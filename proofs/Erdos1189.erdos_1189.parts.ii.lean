import FormalConjectures.ErdosProblems.«1189»

/-!
Erdős 1189(ii). For every admissible cardinality k, the largest possible
modulus is 3 times 2 to the power k-3. The digit argument and doubled
constructions follow Jeff Pickhardt and the Omniscience Research Agent,
Irreducible Covering Sets: A Solution of Erdős Problem 1189, Section 4.

The minimum is given by an explicit finite sum. For each threshold t,
enumerate the k-subsets of the integers from 2 through t. Count residue
assignments by removing the points covered by one residue at each step.
A set contributes one precisely when its count is positive and every
single deletion has count zero. The number of thresholds with total weight
zero is the minimum. Simpson's bound supplies the finite summation limit.
The consecutive-integer window theorem of Crittenden and Vanden Eynden and
its application to Simpson's bound are adapted from @marcusbuffett's
accepted proof of the Simpson variant in this repository.
-/

namespace SimpsonBound

open Polynomial

/-- A sum of `s.card` exponential sequences with nonzero bases that vanishes at `s.card`
consecutive integers vanishes at every integer. -/
theorem expsum_vanish {ι : Type*} (s : Finset ι) (b ω : ι → ℂ) (hω : ∀ i ∈ s, ω i ≠ 0) (x : ℤ)
    (h : ∀ z : ℤ, x ≤ z → z < x + s.card → ∑ i ∈ s, b i * ω i ^ z = 0) :
    ∀ z : ℤ, ∑ i ∈ s, b i * ω i ^ z = 0 := by
  classical
  have hdeg : (∏ i ∈ s, (X - C (ω i))).natDegree = s.card := by
    rw [natDegree_prod_of_monic _ _ (fun i _ => monic_X_sub_C _)]
    simp
  have hmonic : (∏ i ∈ s, (X - C (ω i))).Monic := monic_prod_of_monic _ _ (fun i _ => monic_X_sub_C _)
  have hc0 : (∏ i ∈ s, (X - C (ω i))).coeff 0 ≠ 0 := by
    rw [coeff_zero_eq_eval_zero, eval_prod]
    refine Finset.prod_ne_zero_iff.mpr fun i hi => ?_
    simpa using hω i hi
  have hroot : ∀ i ∈ s, (∏ j ∈ s, (X - C (ω j))).eval (ω i) = 0 := by
    intro i hi
    rw [eval_prod]
    exact Finset.prod_eq_zero hi (by simp)
  have hlead : (∏ i ∈ s, (X - C (ω i))).coeff s.card = 1 := by
    have := hmonic.coeff_natDegree
    rwa [hdeg] at this
  have hrec : ∀ z : ℤ, ∑ t ∈ Finset.range (s.card + 1),
      (∏ i ∈ s, (X - C (ω i))).coeff t * ∑ i ∈ s, b i * ω i ^ (z + (t : ℤ)) = 0 := by
    intro z
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro i hi
    have h1 : ∀ t ∈ Finset.range (s.card + 1),
        (∏ j ∈ s, (X - C (ω j))).coeff t * (b i * ω i ^ (z + (t : ℤ)))
          = b i * ω i ^ z * ((∏ j ∈ s, (X - C (ω j))).coeff t * ω i ^ t) := by
      intro t _
      rw [zpow_add₀ (hω i hi), zpow_natCast]
      ring
    rw [Finset.sum_congr rfl h1, ← Finset.mul_sum]
    have h2 : ∑ t ∈ Finset.range (s.card + 1), (∏ j ∈ s, (X - C (ω j))).coeff t * ω i ^ t
        = (∏ j ∈ s, (X - C (ω j))).eval (ω i) := by
      rw [eval_eq_sum_range, hdeg]
    rw [h2, hroot i hi, mul_zero]
  have hfwd : ∀ j : ℕ, ∑ i ∈ s, b i * ω i ^ (x + (j : ℤ)) = 0 := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      by_cases hj : j < s.card
      · exact h _ (by omega) (by omega)
      · rw [not_lt] at hj
        have hr := hrec (x + ((j - s.card : ℕ) : ℤ))
        rw [Finset.sum_range_succ] at hr
        have hz : ∑ t ∈ Finset.range s.card, (∏ i ∈ s, (X - C (ω i))).coeff t *
            ∑ i ∈ s, b i * ω i ^ (x + ((j - s.card : ℕ) : ℤ) + (t : ℤ)) = 0 := by
          apply Finset.sum_eq_zero
          intro t ht
          rw [Finset.mem_range] at ht
          have e : x + ((j - s.card : ℕ) : ℤ) + (t : ℤ) = x + ((j - s.card + t : ℕ) : ℤ) := by
            push_cast; ring
          rw [e, ih _ (by omega), mul_zero]
        rw [hz, zero_add, hlead, one_mul] at hr
        have e : x + ((j - s.card : ℕ) : ℤ) + (s.card : ℤ) = x + (j : ℤ) := by
          rw [Nat.cast_sub hj]; ring
        rwa [e] at hr
  have hall : ∀ j : ℕ, ∀ z : ℤ, x - j ≤ z → ∑ i ∈ s, b i * ω i ^ z = 0 := by
    intro j
    induction j with
    | zero =>
      intro z hz
      have e : z = x + ((z - x).toNat : ℤ) := by
        rw [Int.toNat_of_nonneg (by simpa using hz)]; ring
      rw [e]
      exact hfwd _
    | succ j ih =>
      intro z hz
      by_cases hz' : x - j ≤ z
      · exact ih z hz'
      · have hr := hrec z
        rw [Finset.sum_range_succ'] at hr
        have hz0 : ∑ t ∈ Finset.range s.card, (∏ i ∈ s, (X - C (ω i))).coeff (t + 1) *
            ∑ i ∈ s, b i * ω i ^ (z + ((t + 1 : ℕ) : ℤ)) = 0 := by
          apply Finset.sum_eq_zero
          intro t _
          rw [ih _ (by push_cast at hz ⊢; omega), mul_zero]
        rw [hz0, zero_add] at hr
        simpa [hc0] using hr
  intro z
  refine hall (x - z).toNat z ?_
  have := Int.self_le_toNat (x - z)
  omega

/-- Crittenden--Vanden Eynden: residue classes with moduli in `N` that cover `2 ^ N.card`
consecutive integers cover all the integers. -/
theorem covers_of_covers_window (N : Finset ℕ) (hpos : ∀ m ∈ N, 0 < m) (a : ℕ → ℤ) (x : ℤ)
    (hcov : ∀ z : ℤ, x ≤ z → z < x + 2 ^ N.card → ∃ m ∈ N, z ≡ a m [ZMOD m]) :
    ∀ z : ℤ, ∃ m ∈ N, z ≡ a m [ZMOD m] := by
  classical
  have hne : ∀ m : ℕ, Complex.exp (2 * Real.pi * Complex.I / m) ≠ 0 := fun m => Complex.exp_ne_zero _
  have hiff : ∀ z : ℤ, (∃ m ∈ N, z ≡ a m [ZMOD m]) ↔
      ∏ m ∈ N, (1 - Complex.exp (2 * Real.pi * Complex.I / m) ^ (z - a m)) = 0 := by
    intro z
    rw [Finset.prod_eq_zero_iff]
    refine exists_congr fun m => and_congr_right fun hm => ?_
    rw [sub_eq_zero, eq_comm,
      (Complex.isPrimitiveRoot_exp m (hpos m hm).ne').zpow_eq_one_iff_dvd, Int.modEq_iff_dvd,
      dvd_sub_comm]
  have hexp : ∀ z : ℤ, ∏ m ∈ N, (1 - Complex.exp (2 * Real.pi * Complex.I / m) ^ (z - a m))
      = ∑ t ∈ N.powerset, (∏ m ∈ t, (-(Complex.exp (2 * Real.pi * Complex.I / m) ^ (-a m)))) *
          (∏ m ∈ t, Complex.exp (2 * Real.pi * Complex.I / m)) ^ z := by
    intro z
    have h1 : ∀ m ∈ N, (1 - Complex.exp (2 * Real.pi * Complex.I / m) ^ (z - a m))
        = (-(Complex.exp (2 * Real.pi * Complex.I / m) ^ (-a m)) *
            Complex.exp (2 * Real.pi * Complex.I / m) ^ z) + 1 := by
      intro m _
      rw [sub_eq_add_neg z, zpow_add₀ (hne m)]
      ring
    rw [Finset.prod_congr rfl h1, Finset.prod_add]
    apply Finset.sum_congr rfl
    intro t _
    rw [Finset.prod_const_one, mul_one, Finset.prod_mul_distrib, Finset.prod_zpow]
  have key := expsum_vanish N.powerset
    (fun t => ∏ m ∈ t, (-(Complex.exp (2 * Real.pi * Complex.I / m) ^ (-a m))))
    (fun t => ∏ m ∈ t, Complex.exp (2 * Real.pi * Complex.I / m))
    (fun t _ => Finset.prod_ne_zero_iff.mpr fun m _ => hne m) x (by
      intro z hz1 hz2
      rw [← hexp, ← hiff]
      apply hcov z hz1
      simpa [Finset.card_powerset] using hz2)
  intro z
  rw [hiff, hexp]
  exact key z

end SimpsonBound

theorem CoverExtrema.modulus_bound : ∀ M : Finset ℕ, Erdos1189.IsIrreducibleCoveringSet M →
    ∀ n ∈ M, n ≤ 2^(M.card-1) := by
  intro M hM n hn
  obtain ⟨⟨hgt, a, ha⟩, hirr⟩ := hM
  by_contra hlt
  rw [not_le] at hlt
  apply hirr (M.erase n) (Finset.erase_ssubset hn)
  refine ⟨fun m hm => hgt m (Finset.mem_of_mem_erase hm), a, ?_⟩
  apply SimpsonBound.covers_of_covers_window (M.erase n)
    (fun m hm => by have := hgt m (Finset.mem_of_mem_erase hm); omega) a (a n + 1)
  intro z hz1 hz2
  obtain ⟨m, hm, hmz⟩ := ha z
  refine ⟨m, Finset.mem_erase.mpr ⟨?_, hm⟩, hmz⟩
  rintro rfl
  rw [Finset.card_erase_of_mem hn] at hz2
  have hd : (m : ℤ) ∣ z - a m := Int.modEq_iff_dvd.mp hmz.symm
  have h1 := Int.le_of_dvd (by omega) hd
  have h2 : ((2 : ℤ) ^ (M.card - 1)) < m := by exact_mod_cast hlt
  omega
namespace CoverExtrema

/-- The number of assignments of residues to the listed moduli that cover
the finite list of points. Each summand fixes the residue of one modulus. -/
def ways : List ℕ → List ℕ → ℕ
  | [], xs => if xs.isEmpty then 1 else 0
  | d :: ds, xs => ∑ r ∈ Finset.range d,
      ways ds (xs.filter (fun x => x % d != r))

theorem ways_pos (ds : List ℕ) (hd : ds.Nodup) (xs : List ℕ) :
    0 < ways ds xs ↔ ∃ a : ℕ → ℕ, (∀ d ∈ ds, a d < d) ∧
      ∀ x ∈ xs, ∃ d ∈ ds, x % d = a d := by
  induction ds generalizing xs with
  | nil =>
    cases xs with
    | nil => simp [ways]
    | cons x xs =>
      constructor
      · simp [ways]
      · rintro ⟨a,_,h⟩
        obtain ⟨m,hm,_⟩ := h x List.mem_cons_self
        simp at hm
  | cons d ds ih =>
    obtain ⟨hf, ht⟩ := List.nodup_cons.mp hd
    simp only [ways, Finset.sum_pos_iff_of_nonneg (fun _ _ => Nat.zero_le _),
      Finset.mem_range, ih ht]
    constructor
    · rintro ⟨r,hr,a,hb,ha⟩
      refine ⟨Function.update a d r, ?_, ?_⟩
      · intro m hm
        rcases List.mem_cons.mp hm with rfl | hm
        · simpa using hr
        · have hne : m ≠ d := fun h => hf (h ▸ hm)
          simpa [Function.update_of_ne hne] using hb m hm
      · intro x hx
        by_cases he : x % d = r
        · exact ⟨d,List.mem_cons_self,by simpa using he⟩
        · obtain ⟨m,hm,hxm⟩ := ha x (List.mem_filter.mpr ⟨hx,by simpa using he⟩)
          have hne : m ≠ d := fun h => hf (h ▸ hm)
          exact ⟨m,List.mem_cons_of_mem _ hm,by simpa [Function.update_of_ne hne] using hxm⟩
    · rintro ⟨a,hb,ha⟩
      refine ⟨a d,hb d List.mem_cons_self,a, fun m hm => hb m (List.mem_cons_of_mem _ hm),?_⟩
      intro x hx
      obtain ⟨hx,hne⟩ := List.mem_filter.mp hx
      obtain ⟨m,hm,hxm⟩ := ha x hx
      rcases List.mem_cons.mp hm with rfl|hm
      · simp [hxm] at hne
      · exact ⟨m,hm,hxm⟩

def entries (D : Finset ℕ) := (List.range (D.sup id + 1)).filter (fun i => decide (i ∈ D))

theorem entries_mem {D : Finset ℕ} {d : ℕ} : d ∈ entries D ↔ d ∈ D := by
  simp only [entries,List.mem_filter,List.mem_range,decide_eq_true_eq,and_iff_right_iff_imp]
  intro hd
  have hh := Finset.le_sup (f := id) hd
  simpa using Nat.lt_succ_of_le hh

def window (D : Finset ℕ) := ways (entries D) (List.range (2^D.card))

theorem window_pos (D : Finset ℕ) (hd : ∀ d ∈ D, 1 < d) :
    0 < window D ↔ Erdos1189.IsCoveringSet D := by
  have nd : (entries D).Nodup := List.Nodup.filter _ List.nodup_range
  rw [window, ways_pos (entries D) nd]
  simp only [entries_mem,List.mem_range]
  constructor
  · rintro ⟨a,ha,hcov⟩
    refine ⟨hd,fun d => (a d : ℤ),SimpsonBound.covers_of_covers_window D (fun d h => by have := hd d h; omega) _ 0 ?_⟩
    intro z hz hr
    obtain ⟨d,hm,hh⟩ := hcov z.toNat (by exact_mod_cast (show (z.toNat : ℤ) < (2 : ℤ)^D.card by simpa [Int.toNat_of_nonneg hz] using hr))
    refine ⟨d,hm,?_⟩
    change z % (d : ℤ) = (a d : ℤ) % (d : ℤ)
    rw [Int.emod_eq_of_lt (show (0 : ℤ) ≤ a d by positivity) (show (a d : ℤ) < d by exact_mod_cast ha d hm)]
    have hv := congrArg (fun t : ℕ => (t : ℤ)) hh
    simpa [Int.natCast_mod,Int.toNat_of_nonneg hz] using hv
  · rintro ⟨_,a,ha⟩
    refine ⟨fun d => (a d % d).toNat,?_,?_⟩
    · intro d hm
      have hp : (0:ℤ) < d := by have := hd d hm; omega
      have h0 := Int.emod_nonneg (a d) (ne_of_gt hp)
      have h1 := Int.emod_lt_of_pos (a d) hp
      change (a d % (d : ℤ)).toNat < d
      omega
    · intro x hx
      obtain ⟨d,hm,he⟩ := ha (x : ℤ)
      have eqn : (x : ℤ) % d = a d % d := he
      refine ⟨d,hm,?_⟩
      change x%d = (a d % (d : ℤ)).toNat
      rw [← eqn, ← Int.natCast_mod, Int.toNat_natCast]

def weight (D : Finset ℕ) : ℕ :=
  min 1 (window D) * ∏ d ∈ D, 0 ^ window (D.erase d)

theorem subset_up {D E : Finset ℕ} (hd : Erdos1189.IsCoveringSet D)
    (hs : D ⊆ E) (he : ∀ d ∈ E, 1 < d) : Erdos1189.IsCoveringSet E := by
  obtain ⟨_,a,ha⟩ := hd
  refine ⟨he,a,fun z => ?_⟩
  obtain ⟨m,hm,hc⟩ := ha z
  exact ⟨m,hs hm,hc⟩

theorem weight_pos {D : Finset ℕ} (hd : ∀ d ∈ D, 1 < d) :
    0 < weight D ↔ Erdos1189.IsIrreducibleCoveringSet D := by
  have berase (d : ℕ) : 0 < ((0 : ℕ)^window (D.erase d)) ↔ ¬ Erdos1189.IsCoveringSet (D.erase d) := by
    rw [← window_pos _ (fun m hm => hd m (Finset.mem_of_mem_erase hm))]
    by_cases hz : window (D.erase d)=0 <;> simp [hz, Nat.pos_of_ne_zero]
  have prod_iff : 0 < (∏ d ∈ D, (0 : ℕ)^window (D.erase d)) ↔ ∀ d ∈ D, ¬ Erdos1189.IsCoveringSet (D.erase d) := by
    simp_rw [← berase, Nat.pos_iff_ne_zero]
    exact Finset.prod_ne_zero_iff
  have mpos (x y : ℕ) : 0 < x*y ↔ 0<x ∧ 0<y := by simp [Nat.pos_iff_ne_zero]
  rw [weight, mpos, lt_min_iff, prod_iff, window_pos D hd]
  simp only [Nat.zero_lt_one,true_and,Erdos1189.IsIrreducibleCoveringSet]
  refine and_congr_right fun _ => ⟨?_,fun h d hm => h _ (Finset.erase_ssubset hm)⟩
  intro h N hN hcov
  obtain ⟨d,hm,hn⟩ := Finset.exists_of_ssubset hN
  apply h d hm
  apply subset_up hcov _ (fun m h => hd m (Finset.mem_of_mem_erase h))
  exact Finset.subset_erase.mpr ⟨hN.le,hn⟩

end CoverExtrema
namespace CoverExtrema

def bound (k : ℕ) := 2^(k-1)

def lowCount (k t : ℕ) := ∑ D ∈ (Finset.Icc 2 t).powersetCard k, weight D

/-- The lower endpoint is the number of empty initial thresholds. -/
def lower (k : ℕ) := ∑ t ∈ Finset.range (bound k), 0^(lowCount k t)

private theorem present {D : Finset ℕ} (h : Erdos1189.IsCoveringSet D) : D.Nonempty := by
  obtain ⟨_,a,ha⟩ := h
  obtain ⟨d,hd,_⟩ := ha 0
  exact ⟨d,hd⟩

theorem low_pos (k t : ℕ) :
    0 < lowCount k t ↔ ∃ u ∈ Erdos1189.largestModulus k, u ≤ t := by
  rw [lowCount,Finset.sum_pos_iff_of_nonneg (fun _ _ => Nat.zero_le _)]
  constructor
  · rintro ⟨D,hD,hp⟩
    obtain ⟨sub,hk⟩ := Finset.mem_powersetCard.mp hD
    have irr := (weight_pos fun d hd => (Finset.mem_Icc.mp (sub hd)).1).mp hp
    have ne := present irr.1
    exact ⟨D.max' ne,⟨D,irr,hk,D.isGreatest_max' ne⟩,
      (Finset.mem_Icc.mp (sub (D.max'_mem ne))).2⟩
  · rintro ⟨u,⟨D,hD,hk,hu⟩,ht⟩
    refine ⟨D,Finset.mem_powersetCard.mpr ⟨?_,hk⟩,(weight_pos hD.1.1).mpr hD⟩
    exact fun d hd => Finset.mem_Icc.mpr ⟨hD.1.1 d hd,(hu.2 hd).trans ht⟩

theorem initial_sum {B v : ℕ} (h : v ≤ B) :
    (∑ t ∈ Finset.range B, if t < v then 1 else 0) = v := by
  have e : (Finset.range B).filter (· < v) = Finset.range v := by
    ext i; simp; omega
  simp [e]

theorem lower_least (k : ℕ) (hk : ∃ M : Finset ℕ, Erdos1189.IsIrreducibleCoveringSet M ∧ M.card=k) :
    IsLeast (Erdos1189.largestModulus k) (lower k) := by
  classical
  let vals := (Finset.range (bound k+1)).filter (· ∈ Erdos1189.largestModulus k)
  have hmem (x : ℕ) : x ∈ vals ↔ x ∈ Erdos1189.largestModulus k := by
    simp only [vals,Finset.mem_filter,Finset.mem_range,and_iff_right_iff_imp]
    rintro ⟨D,hd,hc,hx⟩
    have := modulus_bound D hd x hx.1
    simp only [bound,← hc]; omega
  obtain ⟨D,hD,hkD⟩ := hk
  have d := present hD.1
  have nv : vals.Nonempty := ⟨D.max' d,(hmem _).mpr ⟨D,hD,hkD,D.isGreatest_max' d⟩⟩
  have hlo : IsLeast (Erdos1189.largestModulus k) (vals.min' nv) :=
    ⟨(hmem _).mp (vals.min'_mem nv),fun x hx => vals.min'_le _ ((hmem _).mpr hx)⟩
  have upper_bound (v : ℕ) (hv : v ∈ vals) : v ≤ bound k := by
    have := Finset.mem_range.mp (Finset.mem_filter.mp hv).1
    omega
  have el : lower k = vals.min' nv := by
    rw [lower, ← initial_sum (upper_bound _ (vals.min'_mem nv))]
    apply Finset.sum_congr rfl
    intro t ht
    have he : lowCount k t > 0 ↔ vals.min' nv ≤ t :=
      (low_pos k t).trans ⟨fun ⟨u,hu,hut⟩ => (hlo.2 hu).trans hut,fun h => ⟨_,hlo.1,h⟩⟩
    by_cases h : t < vals.min' nv
    · have hz : lowCount k t = 0 := by omega
      simp [h,hz]
    · have hz : lowCount k t ≠ 0 := by omega
      simp [h,hz]
  exact el ▸ hlo

end CoverExtrema
namespace CoverExtrema
open Nat

def shift (L p e j : ℕ) := p^e * ((ordCompl[p] L) * j)

private theorem next_not_dvd {L p e j : ℕ} (hL : L ≠ 0) (hp : p.Prime) (hj : 0 < j) (hlt : j<p) :
    ¬ p^(e+1) ∣ shift L p e j := by
  rw [shift,pow_succ,mul_dvd_mul_iff_left (pow_ne_zero e hp.ne_zero)]
  refine fun h => (hp.dvd_mul.mp h).elim (Nat.not_dvd_ordCompl hp hL) (fun h => ?_)
  exact (not_le.mpr hlt) (Nat.le_of_dvd hj h)

private theorem next_dvd {L d p e j : ℕ} (hd : d ≠ 0) (hp : p.Prime)
    (hdL : d ∣ L) (miss : ¬ d ∣ shift L p e j) : p^(e+1) ∣ d := by
  rw [hp.pow_dvd_iff_le_factorization hd]
  by_contra! h
  apply miss
  have one := pow_dvd_pow p (show d.factorization p ≤ e by omega)
  have two := Nat.ordCompl_dvd_ordCompl_of_dvd hdL p
  have hdiv := Nat.mul_dvd_mul one (two.trans (dvd_mul_right _ j))
  simpa only [shift,Nat.ordProj_mul_ordCompl_eq_self] using hdiv

private theorem other_dvd {L p q e t j : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hne : p ≠ q) (h : p^(e+1) ∣ L) : p^(e+1) ∣ shift L q t j := by
  have nd : ¬ q ∣ p^(e+1) := fun h => hne ((Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow h)).symm
  exact (Nat.dvd_ordCompl_of_dvd_not_dvd h nd).trans
    ((dvd_mul_right _ j).trans (dvd_mul_left _ _))

private theorem same_digit {L p e j b d : ℕ} (hL : L ≠ 0) (hp : p.Prime)
    (hj : j < p) (hb : b < p) (hd : p^(e+1) ∣ d)
    (he : shift L p e j ≡ shift L p e b [MOD d]) : j=b := by
  have hh := he.of_dvd hd
  simp only [shift,pow_succ] at hh
  have hh' := Nat.ModEq.mul_left_cancel' (pow_ne_zero e hp.ne_zero) hh
  have hc := Nat.ModEq.cancel_left_of_coprime (Nat.coprime_ordCompl hp hL) hh'
  simpa [Nat.ModEq, Nat.mod_eq_of_lt hj,Nat.mod_eq_of_lt hb] using hc

abbrev Mark (m : ℕ) := (p : m.primeFactors) × Fin (m.factorization p.val) × Fin (p.val-1)

def markShift {m : ℕ} (L : ℕ) (v : Mark m) := shift L v.1 v.2.1 (v.2.2.val+1)

private theorem mark_inj {L m d : ℕ} (hL : L≠0) (hm : m≠0) (hmL : m ∣ L)
    (v w : Mark m)
    (hv : v.1.val^(v.2.1.val+1) ∣ d) (hw : w.1.val^(w.2.1.val+1) ∣ d)
    (he : markShift L v ≡ markShift L w [MOD d]) : v=w := by
  rcases v with ⟨⟨p,hp⟩,⟨e,helt⟩,⟨j,hj⟩⟩
  rcases w with ⟨⟨q,hq⟩,⟨t,htlt⟩,⟨b,hb⟩⟩
  dsimp only [markShift] at *
  change j < p-1 at hj
  change b < q-1 at hb
  have pp := Nat.prime_of_mem_primeFactors hp
  have pq := Nat.prime_of_mem_primeFactors hq
  have nj : ¬ p^(e+1) ∣ shift L p e (j+1) := next_not_dvd hL pp (by omega) (by omega)
  have nb : ¬ q^(t+1) ∣ shift L q t (b+1) := next_not_dvd hL pq (by omega) (by omega)
  have ep : p=q := by
    by_contra hn
    apply nj
    apply (he.dvd_iff hv).mpr
    apply other_dvd pp pq hn
    exact ((pp.pow_dvd_iff_le_factorization hm).mpr helt).trans hmL
  subst q
  have et : e=t := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with lt|gt
    · apply nj
      exact (he.dvd_iff hv).mpr ((pow_dvd_pow _ lt).trans (dvd_mul_right _ _))
    · apply nb
      exact (he.dvd_iff hw).mp ((pow_dvd_pow _ gt).trans (dvd_mul_right _ _))
  subst t
  have eq := same_digit hL pp (show j+1 < p by omega) (show b+1<p by omega) hv he
  have : j=b := by omega
  subst b
  rfl

def mass (m : ℕ) := ∑ p ∈ m.primeFactors, m.factorization p * (p-1)

theorem mark_card (m : ℕ) : Fintype.card (Mark m) = mass m := by
  simp [Mark,mass,Fintype.card_sigma]
  exact Finset.sum_attach m.primeFactors (fun p => m.factorization p * (p-1))

theorem private_mark {M : Finset ℕ} (irr : Erdos1189.IsIrreducibleCoveringSet M) {m : ℕ} (hm : m ∈ M) :
    mass m ≤ M.card-1 ∧
    ∀ v : Mark m, ∃ d ∈ M.erase m, v.1.val^(v.2.1.val+1) ∣ d := by
  classical
  obtain ⟨⟨gt,a,cover⟩,minimal⟩ := irr
  have privatePt : ∃ z : ℤ, ∀ d ∈ M.erase m, ¬z ≡ a d [ZMOD d] := by
    by_contra! h
    exact minimal _ (Finset.erase_ssubset hm) ⟨fun d hd => gt _ (Finset.mem_of_mem_erase hd),a,h⟩
  obtain ⟨z,hz⟩ := privatePt
  have zm : z ≡ a m [ZMOD m] := by
    obtain ⟨d,hd,he⟩ := cover z
    by_cases eq : d=m
    · simpa [eq] using he
    · exact (hz _ (Finset.mem_erase.mpr ⟨eq,hd⟩) he).elim
  let L := ∏ d ∈ M,d
  have hL : L ≠ 0 := Finset.prod_ne_zero_iff.mpr fun d hd => by have := gt d hd; omega
  have hdiv (d) (hd : d∈M) : d ∣ L := Finset.dvd_prod_of_mem _ hd
  have hm0 : m ≠ 0 := by have := gt m hm; omega
  have hit (v : Mark m) : ∃ d ∈ M.erase m, z + (markShift L v : ℤ) ≡ a d [ZMOD d] ∧
      v.1.val^(v.2.1.val+1) ∣ d := by
    obtain ⟨d,hd,he⟩ := cover (z + (markShift L v : ℤ))
    have pp := Nat.prime_of_mem_primeFactors v.1.property
    have distinct : d ≠ m := by
      rintro rfl
      have dvdI := Int.left_modEq_add_iff.mp (zm.trans he.symm)
      have dvdN : d ∣ markShift L v := by exact_mod_cast dvdI
      have hlt := v.2.2.isLt
      exact next_not_dvd hL pp (by omega) (by omega)
        (((pp.pow_dvd_iff_le_factorization hm0).mpr v.2.1.isLt).trans dvdN)
    have hm' := Finset.mem_erase.mpr ⟨distinct,hd⟩
    refine ⟨d,hm',he,next_dvd (j := v.2.2.val+1) (by have := gt d hd; omega) pp (hdiv d hd) ?_⟩
    intro h
    exact hz d hm' ((Int.left_modEq_add_iff.mpr (by exact_mod_cast h)).trans he)
  choose f hf hz' hdvd using hit
  refine ⟨?_,fun v => ⟨f v,hf v,hdvd v⟩⟩
  let g : Mark m → M.erase m := fun v => ⟨f v,hf v⟩
  have inj : Function.Injective g := by
    intro v w eq
    have he : f v=f w := congrArg Subtype.val eq
    have hx := (hz' v).trans (he ▸ (hz' w).symm)
    apply mark_inj hL hm0 (hdiv m hm) v w (hdvd v) (he ▸ hdvd w)
    exact Int.natCast_modEq_iff.mp (Int.ModEq.add_left_cancel' z hx)
  have hcard := Fintype.card_le_of_injective g inj
  rw [mark_card,Fintype.card_coe,Finset.card_erase_of_mem hm] at hcard
  exact hcard

end CoverExtrema
namespace CoverExtrema
open Nat

private theorem binary_bound (q : ℕ) (hq : 1 ≤ q) : q ≤ 2^(q-1) := by
  induction q,hq using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    have e : n+1-1=(n-1)+1 := by omega
    rw [e,pow_succ]; omega

private theorem odd_saving (q : ℕ) (hq : 3 ≤ q) : 4*q ≤ 3*2^(q-1) := by
  induction q,hq using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    have e : n+1-1=(n-1)+1 := by omega
    rw [e,pow_succ]; omega

private theorem factor_bound (q e : ℕ) (hq : 1 ≤ q) :
    q^e ≤ 2^(e*(q-1)) := by
  rw [Nat.mul_comm e, pow_mul]
  exact Nat.pow_le_pow_left (binary_bound q hq) e

private theorem factor_save (q e : ℕ) (hq : 3 ≤ q) (he : e≠0) :
    4*q^e ≤ 3*2^(e*(q-1)) := by
  obtain ⟨t,rfl⟩ := Nat.exists_eq_succ_of_ne_zero he
  have h := Nat.mul_le_mul (odd_saving q hq) (factor_bound q t (by omega))
  rw [pow_succ,Nat.succ_mul t (q-1),pow_add]
  simpa only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using h

theorem sharp_upper {k m : ℕ} (hk : 3 ≤ k) (h : m ∈ Erdos1189.largestModulus k) :
    m ≤ 3*2^(k-3) := by
  classical
  obtain ⟨M,irr,hcard,hm⟩ := h
  have mem : m ∈ M := hm.1
  have gt := irr.1.1 m mem
  have h0 : m≠0 := by omega
  obtain ⟨budget,another⟩ := private_mark irr mem
  rw [hcard] at budget
  have oddPrime : ∃ q ∈ m.primeFactors, 3 ≤ q := by
    by_contra! hh
    have alltwo : ∀ p ∈ m.primeFactors, p=2 := fun p hp => by
      have := (Nat.prime_of_mem_primeFactors hp).two_le
      have := hh p hp; omega
    have two : 2 ∈ m.primeFactors := by
      have hp := Nat.mem_primeFactors.mpr ⟨Nat.minFac_prime (by omega : m≠1),m.minFac_dvd,h0⟩
      simpa only [alltwo _ hp] using hp
    have decomp : m=2^(m.factorization 2) :=
      (Nat.prod_primeFactors_pow_factorization h0).trans (Finset.prod_eq_single_of_mem 2 two
        (fun p hp ne => (ne (alltwo p hp)).elim))
    have pos := Nat.Prime.factorization_pos_of_dvd Nat.prime_two h0 (Nat.dvd_of_mem_primeFactors two)
    let v : Mark m := ⟨⟨2,two⟩,⟨m.factorization 2-1,by dsimp; omega⟩,⟨0,by change 0 < 2-1;decide⟩⟩
    obtain ⟨b,hb,hdiv⟩ := another v
    change 2^(m.factorization 2-1+1) ∣ b at hdiv
    rw [Nat.sub_add_cancel pos,← decomp] at hdiv
    obtain ⟨ne,hm'⟩ := Finset.mem_erase.mp hb
    exact ne (Nat.le_antisymm (hm.2 hm') (Nat.le_of_dvd (by have := irr.1.1 b hm';omega) hdiv))
  obtain ⟨q,hq,hq3⟩ := oddPrime
  have pos := (Nat.prime_of_mem_primeFactors hq).factorization_pos_of_dvd h0 (Nat.dvd_of_mem_primeFactors hq)
  let R := m.primeFactors.erase q
  let w := fun p => m.factorization p*(p-1)
  have tail : (∏ p ∈ R,p^m.factorization p) ≤ ∏ p ∈ R,2^(w p) := by
    apply Finset.prod_le_prod' (fun p hp => ?_)
    exact factor_bound p _ (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp)).one_lt.le
  have sav := Nat.mul_le_mul (factor_save q _ hq3 pos.ne') tail
  have prod : (∏ p ∈ R,p^m.factorization p)*q^m.factorization q = m :=
    (Finset.prod_erase_mul _ _ hq).trans (Nat.prod_primeFactors_pow_factorization h0).symm
  have sum : (∑ p ∈ R,w p)+w q = mass m := Finset.sum_erase_add _ _ hq
  have e : 4*m ≤ 3*2^(mass m) := by
    rw [Finset.prod_pow_eq_pow_sum] at sav
    calc
      4*m = 4*((∏ p ∈ R,p^m.factorization p)*q^m.factorization q) := congrArg (4*·) prod.symm
      _ ≤ 3*(2^(∑ p ∈ R,w p)*2^(w q)) := by
        simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm,w] using sav
      _ = 3*2^(mass m) := by rw [←pow_add,sum]
  have pbound := Nat.pow_le_pow_right (by decide : 0<2) budget
  have split : k-1=(k-3)+2 := by omega
  rw [split,pow_add] at pbound
  omega

end CoverExtrema
namespace CoverExtrema

def doubled (D : Finset ℕ) := insert 2 (D.image (2*·))

private theorem doubled_gt {D : Finset ℕ} (gt : ∀ d ∈ D, 1 < d) :
    ∀ d ∈ doubled D, 1 < d := by
  intro d hd
  rcases Finset.mem_insert.mp hd with rfl | hh
  · decide
  · obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hh
    have := gt m hm
    omega

theorem doubled_cover {D : Finset ℕ} (h : Erdos1189.IsCoveringSet D) : Erdos1189.IsCoveringSet (doubled D) := by
  obtain ⟨gt,a,ha⟩ := h
  refine ⟨doubled_gt gt, fun q => if q=2 then 0 else 2*a (q/2)+1,?_⟩
  intro z
  by_cases h : z%2=0
  · exact ⟨2,Finset.mem_insert_self .., by simpa [Int.ModEq] using h⟩
  · obtain ⟨m,hm,he⟩ := ha (z/2)
    have hp := gt _ hm
    have nz : 2*m≠2 := by omega
    have hz : 2*(z/2)+1=z := by omega
    refine ⟨2*m,Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hm),?_⟩
    simp only [if_neg nz,Nat.mul_div_cancel_left _ (by decide : 0<2),Nat.cast_mul, Nat.cast_ofNat]
    simpa only [hz] using (Int.ModEq.mul_left' (c := 2) he).add_right 1

theorem doubled_irred {D : Finset ℕ} (irr : Erdos1189.IsIrreducibleCoveringSet D) :
    Erdos1189.IsIrreducibleCoveringSet (doubled D) := by
  refine ⟨doubled_cover irr.1,?_⟩
  rintro N hN ⟨_,a,ha⟩
  let parity (e : ℤ) := D.filter (fun m => 2*m ∈ N ∧ a (2*m)%2=e%2)
  have all (e : ℤ) (avoid : 2 ∈ N → ¬ e ≡ a 2 [ZMOD 2]) : parity e = D := by
    apply Finset.Subset.antisymm (Finset.filter_subset ..)
    by_contra hn
    apply irr.2 (parity e) (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset ..,fun h => hn (Finset.Subset.trans (Finset.Subset.rfl) h.symm.le)⟩)
    refine ⟨fun m hm => irr.1.1 _ (Finset.mem_filter.mp hm).1,fun m => (a (2*m)-e)/2,?_⟩
    intro y
    obtain ⟨d,hd,hz⟩ := ha (2*y+e)
    rcases Finset.mem_insert.mp (hN.le hd : d ∈ doubled D) with rfl | hin
    · apply False.elim (avoid hd _)
      simpa [Int.ModEq,Int.add_emod] using hz
    · obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hin
      have hfull : 2*y+e ≡ a (2*m) [ZMOD (2:ℤ)*m] := by exact_mod_cast hz
      have hpar := hfull.of_dvd (dvd_mul_right _ _)
      have he : e%2=a (2*m)%2 := by simpa [Int.ModEq,Int.add_emod] using hpar
      refine ⟨m,Finset.mem_filter.mpr ⟨hm,hd,he.symm⟩,?_⟩
      have ae : 2*((a (2*m)-e)/2)+e=a (2*m) := by omega
      rw [← ae] at hfull
      exact Int.ModEq.mul_left_cancel' (by decide : (2:ℤ) ≠ 0) (Int.ModEq.add_right_cancel' e hfull)
  by_cases hn : 2 ∈ N
  · have eq := all (a 2+1) (fun _ he => by change (a 2+1)%2=a 2%2 at he; omega)
    apply hN.ne
    apply Finset.Subset.antisymm hN.le
    intro d hd
    rcases Finset.mem_insert.mp hd with rfl|hi
    · exact hn
    · obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hi
      rw [←eq] at hm
      exact (Finset.mem_filter.mp hm).2.1
  · obtain ⟨m,hm⟩ := present irr.1
    have ha₀ : m ∈ parity 0 := (all 0 (fun h => (hn h).elim)).symm ▸ hm
    have ha₁ : m ∈ parity 1 := (all 1 (fun h => (hn h).elim)).symm ▸ hm
    have h₀ := (Finset.mem_filter.mp ha₀).2.2
    have h₁ := (Finset.mem_filter.mp ha₁).2.2
    omega

theorem double_attains {k m : ℕ} (h : m ∈ Erdos1189.largestModulus k) :
    2*m ∈ Erdos1189.largestModulus (k+1) := by
  obtain ⟨D,irr,hk,hm⟩ := h
  have hm' := irr.1.1 m hm.1
  have h2 : 2 ∉ D.image (2*·) := by
    rintro h
    obtain ⟨q,hq,eq⟩ := Finset.mem_image.mp h
    have := irr.1.1 q hq
    omega
  refine ⟨doubled D,doubled_irred irr,?_,Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hm.1),?_⟩
  · rw [doubled,Finset.card_insert_of_notMem h2,Finset.card_image_of_injective _ (fun x y he => by omega),hk]
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl|hi
    · omega
    · obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hi
      have := hm.2 hq
      omega

theorem twelve_attained : 12 ∈ Erdos1189.largestModulus 5 := by
  let seed : Finset ℕ := {2,3,4,6,12}
  have hgt : ∀ d ∈ seed, 1<d := by decide
  have hwt : 0 < weight seed := by decide +kernel
  refine ⟨seed,(weight_pos hgt).mp hwt,by decide,by decide,?_⟩
  intro d hd
  exact (show ∀ d ∈ seed, d ≤ 12 by decide) d hd

theorem sharp_attained (k : ℕ) (hk : 5 ≤ k) : 3*2^(k-3) ∈ Erdos1189.largestModulus k := by
  induction k,hk using Nat.le_induction with
  | base => exact twelve_attained
  | succ k hk ih =>
    have eq : k+1-3 = (k-3)+1 := by omega
    rw [eq,pow_succ]
    simpa only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using double_attains ih

end CoverExtrema
namespace CoverExtrema

private theorem admissible_size {k : ℕ} (hk : ∃ D : Finset ℕ, Erdos1189.IsIrreducibleCoveringSet D ∧ D.card = k) :
    5 ≤ k := by
  by_contra! small
  obtain ⟨D,irr,hcard⟩ := hk
  have ne := present irr.1
  let m := D.max' ne
  have hm : m ∈ Erdos1189.largestModulus k := ⟨D,irr,hcard,D.isGreatest_max' ne⟩
  have hbound := modulus_bound D irr m (D.max'_mem ne)
  rw [hcard] at hbound
  let cap := fun i : ℕ => if i=4 then 6 else bound i
  have table : ∀ i : Fin 5, lowCount i (cap i) = 0 := by decide +kernel
  have hmcap : m ≤ cap k := by
    dsimp [cap]
    split
    · rename_i h
      have hh := sharp_upper (k := k) (by omega) hm
      rw [h] at hh
      norm_num at hh
      exact hh
    · exact hbound
  have yes := (low_pos k (cap k)).mpr ⟨m,hm,hmcap⟩
  have no := table ⟨k,small⟩
  exact (Nat.ne_of_gt yes) no

end CoverExtrema

/-- The first component is a finite sum of zero-count indicators; the second is
the sharp closed form on every admissible cardinality. -/
def OMA.answer (k : ℕ) : ℕ × ℕ := (CoverExtrema.lower k,3*2^(k-3))

theorem OMA.solution : Erdos1189.erdos_1189.parts.ii.answer = OMA.answer →
    type_of% @Erdos1189.erdos_1189.parts.ii := by
  intro heq k hk
  rw [heq]
  have hsize := CoverExtrema.admissible_size hk
  exact ⟨CoverExtrema.lower_least k hk, CoverExtrema.sharp_attained k hsize,
    fun _ hm => CoverExtrema.sharp_upper (by omega) hm⟩
