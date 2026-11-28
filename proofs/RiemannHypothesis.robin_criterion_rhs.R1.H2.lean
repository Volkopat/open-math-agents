import OMAReductions.R_RiemannHypothesis_robin_criterion_rhs_R1
import Mathlib

/-! Enumerate the divisors supported on the primes at most seventeen. -/
namespace OMA.RobinFinite

open Finset

abbrev Row := ℕ × ℕ × ℕ

def primes : List ℕ := [2,3,5,7,11,13,17]

def geom (p e : ℕ) : ℕ := ∑ i ∈ range (e+1), p^i

def extend (p e : ℕ) (r : Row) : Row :=
  (p^e*r.1, geom p e*r.2.1, (if e=0 then 0 else 1)+r.2.2)

def assemble (e : ℕ → ℕ) : List ℕ → Row
  | [] => (1,1,0)
  | p::ps => extend p (e p) (assemble e ps)

def rows : List ℕ → List Row
  | [] => [(1,1,0)]
  | p::ps => (rows ps).flatMap fun r =>
      ((List.range 17).map fun e => extend p e r).filter fun u => u.1 < 131072

theorem assembled_mem {ps : List ℕ} {e : ℕ→ℕ}
    (primeLower : ∀ p∈ps, 2≤p)
    (powers : ∀ p∈ps, e p<17)
    (fit : (assemble e ps).1<131072) :
    assemble e ps ∈ rows ps := by
  induction ps with
  | nil => simp [assemble,rows]
  | cons p ps ih =>
    have hpos : 0<p^e p := pow_pos (by have := primeLower p (by simp); omega) _
    have htail : (assemble e ps).1<131072 := by
      have h := Nat.le_mul_of_pos_left (assemble e ps).1 hpos
      change p^e p*(assemble e ps).1<131072 at fit
      exact h.trans_lt fit
    have hm := ih (fun q h => primeLower q (List.mem_cons_of_mem _ h))
      (fun q h => powers q (List.mem_cons_of_mem _ h)) htail
    apply List.mem_flatMap.mpr
    refine ⟨assemble e ps,hm,List.mem_filter.mpr ⟨?_,by simpa using fit⟩⟩
    exact List.mem_map.mpr ⟨e p,List.mem_range.mpr (powers p (by simp)),rfl⟩

structure Band where
  lower : ℕ
  upper : ℕ
  num : ℕ
  den : ℕ

def fits (b : Band) (r : Row) (j : ℕ) : Prop :=
  4≤r.2.2+j ∧ r.1*19^j≤b.upper ∧ (j=0 → b.lower≤r.1)

private instance (b : Band) (r : Row) (j : ℕ) : Decidable (fits b r j) := by unfold fits; infer_instance

def boundedBy (b : Band) (r : Row) (j : ℕ) : Prop :=
  b.den*r.2.1*19^j ≤ b.num*r.1*18^j

private instance (b : Band) (r : Row) (j : ℕ) : Decidable (boundedBy b r j) := by unfold boundedBy; infer_instance

def check (b : Band) : Bool :=
  (rows primes).all fun r =>
    (List.range 5).all fun j => decide (fits b r j → boundedBy b r j)

theorem check_correct {b : Band} (h : check b = true) {r : Row} (mem : r ∈ rows primes)
    {j : ℕ} (small : j<5) (hf : fits b r j) : boundedBy b r j := by
  unfold check at h
  have h₁ := List.all_eq_true.mp h _ mem
  have h₂ := List.all_eq_true.mp h₁ _ (List.mem_range.mpr small)
  exact of_decide_eq_true h₂ hf

open scoped ArithmeticFunction.sigma

private theorem assembled_fields (ps : List ℕ) (nd : ps.Nodup) (e : ℕ→ℕ) :
    (assemble e ps).1 = ∏ p ∈ ps.toFinset, p^e p ∧
    (assemble e ps).2.1 = ∏ p ∈ ps.toFinset, geom p (e p) ∧
    (assemble e ps).2.2 = (ps.toFinset.filter fun p => e p ≠ 0).card := by
  induction ps with
  | nil => simp [assemble]
  | cons p ps ih =>
    obtain ⟨hnd, htail⟩ := List.nodup_cons.mp nd
    obtain ⟨hm, hg, hc⟩ := ih htail
    have hp : p ∉ ps.toFinset := by simpa using hnd
    have hf : p ∉ ps.toFinset.filter (fun p => e p ≠ 0) :=
      fun h => hp (Finset.mem_filter.mp h).1
    simp only [assemble, extend, List.toFinset_cons, Finset.prod_insert hp,hm,hg,hc,true_and]
    rw [Finset.filter_insert]
    by_cases h : e p=0 <;> simp [h, Finset.card_insert_of_notMem hf, Nat.add_comm]

private theorem roster_prime : ∀ p ∈ primes, Nat.Prime p := by decide +kernel
private theorem roster_complete : ∀ p : Fin 19, p.val.Prime → p.val ∈ primes := by decide +kernel
private theorem roster_nodup : primes.Nodup := by decide

private theorem big_ge {p : ℕ} (prime : p.Prime) (out : p ∉ primes.toFinset) :
    19 ≤ p := by
  by_contra! h
  exact out (List.mem_toFinset.mpr (roster_complete ⟨p,h⟩ prime))

private theorem bigFactor (p k : ℕ) (h : 19≤p) : geom p k*18 ≤ p^k*19 := by
  have hp : (19:ℝ) ≤ p := by exact_mod_cast h
  have ratio : (p:ℝ)/((p:ℝ)-1) ≤ 19/18 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  have geomReal : (∑ i ∈ range (k+1), (p:ℝ)^i) ≤ (p:ℝ)^k*((p:ℝ)/((p:ℝ)-1)) := by
    rw [← mul_div_assoc,le_div_iff₀ (by linarith),geom_sum_mul,pow_succ]
    linarith
  have hsum := geomReal.trans (mul_le_mul_of_nonneg_left ratio (by positivity : (0:ℝ)≤(p:ℝ)^k))
  have hcast : (↑(geom p k) : ℝ)*18 ≤ (p:ℝ)^k*19 := by
    have h' := (le_div_iff₀ (by norm_num : (0:ℝ)<18)).mp
      (show (↑(geom p k):ℝ) ≤ (p:ℝ)^k*19/18 by
        unfold geom
        push_cast
        simpa only [mul_div_assoc] using hsum)
    exact h'
  exact_mod_cast hcast

private theorem prod_factor_split (F S : Finset ℕ) (f : ℕ→ℕ)
    (neutral : ∀ p, p∉F → f p=1) :
    (∏ p ∈ F, f p) = (∏ p ∈ S, f p)*(∏ p ∈ F \ S, f p) := by
  let A := F ∩ S
  have hA : A ⊆ F := Finset.inter_subset_left
  have hA' : A ⊆ S := Finset.inter_subset_right
  have hs : (∏ p ∈ A, f p) = ∏ p ∈ S, f p := by
    apply Finset.prod_subset hA'
    intro p hs ha
    exact neutral p (fun hf => ha (Finset.mem_inter.mpr ⟨hf,hs⟩))
  have hd : F \ A = F \ S := by
    ext p
    simp only [A, Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have h := Finset.prod_sdiff (f := f) hA
  rw [hd,hs,mul_comm] at h
  exact h.symm

set_option maxHeartbeats 1000000 in
theorem sigma_envelope (b : Band) (pass : check b = true) {n : ℕ}
    (nz : n≠0) (clip : n<131072) (hn₁ : b.lower≤n) (hn₂ : n≤b.upper)
    (many : 4≤n.primeFactors.card) : b.den*(σ 1 n)≤b.num*n := by
  let pset := primes.toFinset
  let e (p : ℕ) := n.factorization p
  let r := assemble e primes
  let big := n.primeFactors \ pset
  let j := big.card
  let q := ∏ p ∈ big, p^e p
  let t := ∏ p ∈ big, geom p (e p)
  have fields := assembled_fields primes roster_nodup e
  have hsmall (p : ℕ) (h : p∉n.primeFactors) : e p=0 := by
    exact Finsupp.notMem_support_iff.mp (by simpa only [Nat.support_factorization] using h)
  have hn : n = r.1*q := by
    rw [fields.1]
    exact (Nat.prod_primeFactors_pow_factorization nz).trans
      (prod_factor_split n.primeFactors pset (fun p => p^e p) (fun p hp => by simp [hsmall p hp]))
  have hs : σ 1 n = r.2.1*t := by
    rw [ArithmeticFunction.sigma_one_apply,Nat.sum_divisors nz,fields.2.1]
    exact prod_factor_split n.primeFactors pset (fun p => geom p (e p))
      (fun p hp => by simp [geom,hsmall p hp])
  have both : (pset.filter fun p => e p≠0)=n.primeFactors∩pset := by
    ext p
    simp only [Finset.mem_filter,Finset.mem_inter]
    have h : e p≠0 ↔ p∈n.primeFactors := by
      change n.factorization p≠0 ↔ p∈n.primeFactors
      rw [← Finsupp.mem_support_iff,Nat.support_factorization]
    rw [h,and_comm]
  have card : r.2.2+j=n.primeFactors.card := by
    rw [fields.2.2,both]
    exact Finset.card_inter_add_card_sdiff n.primeFactors pset
  have exponent : ∀ p∈primes, e p<17 := by
    intro p hp
    have prime := roster_prime p hp
    have hnpos : 0<n := Nat.pos_of_ne_zero nz
    have bound : p^e p≤n :=
      Nat.le_of_dvd hnpos ((prime.pow_dvd_iff_le_factorization nz).mpr (le_refl _))
    by_contra! h
    have lp : 2^17≤p^17 := Nat.pow_le_pow_left prime.two_le _
    have rp : p^17≤p^e p := Nat.pow_le_pow_right (by have := prime.two_le; omega) h
    exact (not_le_of_gt clip) (lp.trans (rp.trans bound))
  have positive : ∀ p∈big, 19≤p ∧ 0<e p := by
    intro p hp
    obtain ⟨hm,out⟩ := Finset.mem_sdiff.mp hp
    exact ⟨big_ge (Nat.prime_of_mem_primeFactors hm) out,
      Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp (by simpa only [Nat.support_factorization] using hm))⟩
  have lowerQ : 19^j≤q := by
    change 19^big.card ≤ ∏ p ∈ big, p^e p
    rw [← Finset.prod_const]
    apply Finset.prod_le_prod'
    intro p hp
    obtain ⟨h1,h2⟩ := positive p hp
    exact h1.trans (by
      calc p = p^1 := by simp
        _ ≤ p^e p := Nat.pow_le_pow_right (by omega) h2)
  have boundBig : t*18^j≤q*19^j := by
    change (∏ p ∈ big, geom p (e p))*18^big.card ≤ (∏ p ∈ big, p^e p)*19^big.card
    rw [← Finset.prod_const (b := 18) (s := big),← Finset.prod_const (b := 19) (s := big),
        ← Finset.prod_mul_distrib,← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod' fun p hp => bigFactor p _ (positive p hp).1
  have qpos : 0<q := (pow_pos (by decide) _).trans_le lowerQ
  have fit : r.1<131072 :=
    (Nat.le_mul_of_pos_right _ qpos).trans_lt (hn.symm ▸ clip)
  have rpos : 0<r.1 := by
    by_contra! h
    rw [Nat.eq_zero_of_le_zero h,zero_mul] at hn
    exact nz hn
  have small : j<5 := by
    by_contra! hl
    have hpow : 19^5≤19^j := Nat.pow_le_pow_right (by decide) hl
    have qn : q≤n := hn.symm ▸ Nat.le_mul_of_pos_left q rpos
    have := hpow.trans (lowerQ.trans qn)
    norm_num at this
    omega
  have mem : r ∈ rows primes := assembled_mem (fun p hp => (roster_prime p hp).two_le) exponent fit
  have hfit : fits b r j := by
    refine ⟨by rw [card]; exact many, ?_, ?_⟩
    · exact (Nat.mul_le_mul_left r.1 lowerQ).trans (hn ▸ hn₂)
    · intro hz
      have empty : big=∅ := Finset.card_eq_zero.mp hz
      have he : q=1 := by simp [q,empty]
      simpa [hn,he] using hn₁
  have hb := check_correct pass mem small hfit
  unfold boundedBy at hb
  have hFull : b.den*(σ 1 n)*18^j≤b.num*n*18^j := by
    calc
      _ = b.den*r.2.1*(t*18^j) := by rw [hs]; ring
      _ ≤ b.den*r.2.1*(q*19^j) := Nat.mul_le_mul_left _ boundBig
      _ = (b.den*r.2.1*19^j)*q := by ring
      _ ≤ (b.num*r.1*18^j)*q := Nat.mul_le_mul_right _ hb
      _ = _ := by rw [hn]; ring
  exact Nat.le_of_mul_le_mul_right hFull (pow_pos (by decide) _)

open Real

private theorem expConstant : (44:ℝ)/25 < exp eulerMascheroniConstant := by
  have hr : (5:ℚ) < harmonic 83 := by norm_num
  have hr' : (5:ℝ) < (harmonic 83:ℝ) := by exact_mod_cast hr
  have hγ : (harmonic 83:ℝ)-log 84 < eulerMascheroniConstant := by
    simpa only [eulerMascheroniSeq,Nat.cast_ofNat,show (83:ℝ)+1=84 by norm_num]
      using eulerMascheroniSeq_lt_eulerMascheroniConstant 83
  have he := exp_lt_exp.mpr ((sub_lt_sub_right hr' (log 84)).trans hγ)
  rw [exp_sub,exp_log (by norm_num : (0:ℝ)<84)] at he
  have hpow : (2.718:ℝ)^5 ≤ exp 5 := by
    rw [show exp 5 = exp 1^5 by simp]
    exact pow_le_pow_left₀ (by norm_num) (by linarith [exp_one_gt_d9]) _
  norm_num at hpow
  linarith

theorem robin_band (b : Band) (checked : check b = true) {u v : ℝ}
    (positiveDen : 0<b.den) (posU : 0<u)
    (expU : exp u < v) (expV : exp v < b.lower)
    (strong : (b.num:ℝ)/b.den ≤ (44:ℝ)/25*u)
    {n : ℕ} (hn : 5040<n) (globalBound : n<131072) (lower : b.lower≤n)
    (upper : n≤b.upper) (many : 4≤n.primeFactors.card) :
    (σ 1 n : ℝ) < exp eulerMascheroniConstant * n * log (log n) := by
  have hp : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hd : (0:ℝ)<b.den := by exact_mod_cast positiveDen
  have envelope := sigma_envelope b checked (by omega : n≠0) globalBound lower upper many
  have hb : (b.den:ℝ)*(σ 1 n:ℝ)≤(b.num:ℝ)*n := by exact_mod_cast envelope
  have lower' : (b.lower:ℝ)≤n := by exact_mod_cast lower
  have hv : v<log (n:ℝ) := (lt_log_iff_exp_lt hp).mpr (expV.trans_le lower')
  have hl : 0<log (n:ℝ) := ((exp_pos u).trans expU).trans hv
  have hu : u<log (log (n:ℝ)) := (lt_log_iff_exp_lt hl).mpr (expU.trans hv)
  have ht := mul_lt_mul'' expConstant hu (by norm_num : (0:ℝ)≤44/25) posU.le
  calc
    (σ 1 n:ℝ) ≤ (b.num:ℝ)/b.den*n := by
      rw [div_mul_eq_mul_div,le_div_iff₀ hd]
      simpa only [mul_comm (b.den:ℝ) (σ 1 n:ℝ)] using hb
    _ < (exp eulerMascheroniConstant * log (log n))*n := mul_lt_mul_of_pos_right (strong.trans_lt ht) hp
    _ = _ := by ring

private def band0 : Band := ⟨5041,7559,127,35⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def checked0 : PLift (check band0 = true) := ⟨by decide +kernel⟩

private theorem apply0 {n : ℕ} (lower : 5041≤n) (upper : n≤7559)
    (many : 4≤n.primeFactors.card) :
    (σ 1 n : ℝ) < Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n) := by
  have e₁ : Real.exp ((17 : ℝ)/8) < (17:ℝ)/2 :=
    OMA.R_RiemannHypothesis_robin_criterion_rhs_R1.RobinSupport.exp_rat_lt (k:=17) (d:=8)
      (by decide) (by norm_num) (by norm_num)
  have e₂ : Real.exp ((17 : ℝ)/2) < (5041:ℝ) :=
    OMA.R_RiemannHypothesis_robin_criterion_rhs_R1.RobinSupport.exp_rat_lt (k:=17) (d:=2)
      (by decide) (by norm_num) (by norm_num)
  exact robin_band band0 checked0.down (by decide) (by norm_num) e₁ e₂
    (by norm_num [band0]) (by omega) (by omega) lower upper many

private def band1 : Band := ⟨7560,10079,80,21⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def checked1 : PLift (check band1 = true) := ⟨by decide +kernel⟩

private theorem apply1 {n : ℕ} (lower : 7560≤n) (upper : n≤10079)
    (many : 4≤n.primeFactors.card) :
    (σ 1 n : ℝ) < Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n) := by
  have e₁ : Real.exp ((13 : ℝ)/6) < (35:ℝ)/4 :=
    OMA.R_RiemannHypothesis_robin_criterion_rhs_R1.RobinSupport.exp_rat_lt (k:=13) (d:=6)
      (by decide) (by norm_num) (by norm_num)
  have e₂ : Real.exp ((35 : ℝ)/4) < (7560:ℝ) :=
    OMA.R_RiemannHypothesis_robin_criterion_rhs_R1.RobinSupport.exp_rat_lt (k:=35) (d:=4)
      (by decide) (by norm_num) (by norm_num)
  exact robin_band band1 checked1.down (by decide) (by norm_num) e₁ e₂
    (by norm_num [band1]) (by omega) (by omega) lower upper many

private def band2 : Band := ⟨10080,15119,39,10⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def checked2 : PLift (check band2 = true) := ⟨by decide +kernel⟩

private theorem apply2 {n : ℕ} (lower : 10080≤n) (upper : n≤15119)
    (many : 4≤n.primeFactors.card) :
    (σ 1 n : ℝ) < Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n) := by
  have e₁ : Real.exp ((71 : ℝ)/32) < (46:ℝ)/5 :=
    OMA.R_RiemannHypothesis_robin_criterion_rhs_R1.RobinSupport.exp_rat_lt (k:=71) (d:=32)
      (by decide) (by norm_num) (by norm_num)
  have e₂ : Real.exp ((46 : ℝ)/5) < (10080:ℝ) :=
    OMA.R_RiemannHypothesis_robin_criterion_rhs_R1.RobinSupport.exp_rat_lt (k:=46) (d:=5)
      (by decide) (by norm_num) (by norm_num)
  exact robin_band band2 checked2.down (by decide) (by norm_num) e₁ e₂
    (by norm_num [band2]) (by omega) (by omega) lower upper many

private def band3 : Band := ⟨15120,27719,12493,3150⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def checked3 : PLift (check band3 = true) := ⟨by decide +kernel⟩

private theorem apply3 {n : ℕ} (lower : 15120≤n) (upper : n≤27719)
    (many : 4≤n.primeFactors.card) :
    (σ 1 n : ℝ) < Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n) := by
  have e₁ : Real.exp ((113 : ℝ)/50) < (48:ℝ)/5 :=
    OMA.R_RiemannHypothesis_robin_criterion_rhs_R1.RobinSupport.exp_rat_lt (k:=113) (d:=50)
      (by decide) (by norm_num) (by norm_num)
  have e₂ : Real.exp ((48 : ℝ)/5) < (15120:ℝ) :=
    OMA.R_RiemannHypothesis_robin_criterion_rhs_R1.RobinSupport.exp_rat_lt (k:=48) (d:=5)
      (by decide) (by norm_num) (by norm_num)
  exact robin_band band3 checked3.down (by decide) (by norm_num) e₁ e₂
    (by norm_num [band3]) (by omega) (by omega) lower upper many

private def band4 : Band := ⟨27720,55439,312,77⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def checked4 : PLift (check band4 = true) := ⟨by decide +kernel⟩

private theorem apply4 {n : ℕ} (lower : 27720≤n) (upper : n≤55439)
    (many : 4≤n.primeFactors.card) :
    (σ 1 n : ℝ) < Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n) := by
  have e₁ : Real.exp ((37 : ℝ)/16) < (51:ℝ)/5 :=
    OMA.R_RiemannHypothesis_robin_criterion_rhs_R1.RobinSupport.exp_rat_lt (k:=37) (d:=16)
      (by decide) (by norm_num) (by norm_num)
  have e₂ : Real.exp ((51 : ℝ)/5) < (27720:ℝ) :=
    OMA.R_RiemannHypothesis_robin_criterion_rhs_R1.RobinSupport.exp_rat_lt (k:=51) (d:=5)
      (by decide) (by norm_num) (by norm_num)
  exact robin_band band4 checked4.down (by decide) (by norm_num) e₁ e₂
    (by norm_num [band4]) (by omega) (by omega) lower upper many

private def band5 : Band := ⟨55440,110879,1612,385⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def checked5 : PLift (check band5 = true) := ⟨by decide +kernel⟩

private theorem apply5 {n : ℕ} (lower : 55440≤n) (upper : n≤110879)
    (many : 4≤n.primeFactors.card) :
    (σ 1 n : ℝ) < Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n) := by
  have e₁ : Real.exp ((119 : ℝ)/50) < (65:ℝ)/6 :=
    OMA.R_RiemannHypothesis_robin_criterion_rhs_R1.RobinSupport.exp_rat_lt (k:=119) (d:=50)
      (by decide) (by norm_num) (by norm_num)
  have e₂ : Real.exp ((65 : ℝ)/6) < (55440:ℝ) :=
    OMA.R_RiemannHypothesis_robin_criterion_rhs_R1.RobinSupport.exp_rat_lt (k:=65) (d:=6)
      (by decide) (by norm_num) (by norm_num)
  exact robin_band band5 checked5.down (by decide) (by norm_num) e₁ e₂
    (by norm_num [band5]) (by omega) (by omega) lower upper many

private def band6 : Band := ⟨110880,131071,234,55⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def checked6 : PLift (check band6 = true) := ⟨by decide +kernel⟩

private theorem apply6 {n : ℕ} (lower : 110880≤n) (upper : n≤131071)
    (many : 4≤n.primeFactors.card) :
    (σ 1 n : ℝ) < Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n) := by
  have e₁ : Real.exp ((39 : ℝ)/16) < (23:ℝ)/2 :=
    OMA.R_RiemannHypothesis_robin_criterion_rhs_R1.RobinSupport.exp_rat_lt (k:=39) (d:=16)
      (by decide) (by norm_num) (by norm_num)
  have e₂ : Real.exp ((23 : ℝ)/2) < (110880:ℝ) :=
    OMA.R_RiemannHypothesis_robin_criterion_rhs_R1.RobinSupport.exp_rat_lt (k:=23) (d:=2)
      (by decide) (by norm_num) (by norm_num)
  exact robin_band band6 checked6.down (by decide) (by norm_num) e₁ e₂
    (by norm_num [band6]) (by omega) (by omega) lower upper many

private theorem allBands (n : ℕ) (low : 5040<n) (high : n<131072) (many : 4≤n.primeFactors.card) :
    (σ 1 n : ℝ) < Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n) := by
  by_cases hi0 : n≤7559
  · exact apply0 (by omega) hi0 many
  · by_cases hi1 : n≤10079
    · exact apply1 (by omega) hi1 many
    ·
      by_cases hi2 : n≤15119
      · exact apply2 (by omega) hi2 many
      ·
        by_cases hi3 : n≤27719
        · exact apply3 (by omega) hi3 many
        ·
          by_cases hi4 : n≤55439
          · exact apply4 (by omega) hi4 many
          ·
            by_cases hi5 : n≤110879
            · exact apply5 (by omega) hi5 many
            ·
              exact apply6 (by omega) (by omega) many

end OMA.RobinFinite

theorem OMA.solution : OMA.R_RiemannHypothesis_robin_criterion_rhs_R1.H2 := by
  intro n low high many
  exact OMA.RobinFinite.allBands n low high many