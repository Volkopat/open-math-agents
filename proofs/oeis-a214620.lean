import OMAStatements.S_oeis_a214620
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Base

-- The signature strategy was outlined by physbuzz in venue note 57766.

open Filter Finset Real
namespace A214620Analytic

theorem small_cutoff :
    ∀ᶠ N : ℕ in atTop,
      64 * (1 + log (((Nat.log 2 N + 2)^4 : ℕ) : ℝ)) ≤ log N := by
  have hsmall := Real.isLittleO_log_id_atTop.bound (show (0:ℝ) < 1/1024 by norm_num)
  obtain ⟨B,hB⟩ := eventually_atTop.1 hsmall
  have grow : Tendsto (fun n : ℕ => log (n:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [grow.eventually_ge_atTop (max B 256)] with N hN
  have hL : 256 ≤ log (N:ℝ) := (le_max_right _ _).trans hN
  have hy : B ≤ 2*log (N:ℝ)+2 := by linarith [(le_max_left B 256).trans hN]
  have bound := hB _ hy
  have hy1 : 1 ≤ 2*log (N:ℝ)+2 := by linarith
  simp only [id_eq, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hy1),
    abs_of_nonneg (by linarith : 0 ≤ 2*log (N:ℝ)+2)] at bound
  have h2 : (1:ℝ)/2 ≤ log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (show (0:ℝ) < 2 by norm_num)
    norm_num at this ⊢
    linarith
  have hk := Real.natLog_le_logb N 2
  simp only [Nat.cast_ofNat, Real.logb] at hk
  have hmul := (le_div_iff₀ (Real.log_pos (show (1:ℝ)<2 by norm_num))).mp hk
  have hk' : ((Nat.log 2 N : ℕ) : ℝ) + 2 ≤ 2 * log N + 2 := by
    nlinarith [mul_nonneg (Nat.cast_nonneg (Nat.log 2 N) (α := ℝ)) (sub_nonneg.mpr h2)]
  have hlog := Real.log_le_log (by positivity : 0 < ((Nat.log 2 N : ℕ) : ℝ)+2) hk'
  push_cast
  rw [Real.log_pow]
  norm_num1
  linarith

theorem prime_sum_bound :
    ∀ᶠ N : ℕ in atTop,
      8 * (∑ j ∈ Finset.Icc 1 ((Nat.log 2 N + 2)^4), Nat.primeCounting (N / j)) ≤ N := by
  obtain ⟨B,hB⟩ := eventually_atTop.1
    (Chebyshev.eventually_primeCounting_le (show (0:ℝ)<1 by norm_num))
  let T : ℝ := max 2 B
  have grow : Tendsto (fun n : ℕ => log (n:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [small_cutoff, grow.eventually_ge_atTop (2 * log T),
    eventually_ge_atTop 2] with N hs hT hN
  let J := (Nat.log 2 N+2)^4
  change 64 * (1 + log (J:ℝ)) ≤ log (N:ℝ) at hs
  have npos : (0:ℝ) < N := by exact_mod_cast (by omega : 0<N)
  have Lpos : 0 < log (N:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1<N))
  have jlog := Real.log_natCast_nonneg J
  have coeff : log 4 + 1 ≤ (4:ℝ) := by
    linarith [Real.log_le_sub_one_of_pos (show (0:ℝ)<4 by norm_num)]
  have term (j : ℕ) (hj : j ∈ Finset.Icc 1 J) :
      (Nat.primeCounting (N/j) : ℝ) ≤ (8*(N:ℝ)/log N) * (j:ℝ)⁻¹ := by
    obtain ⟨hj1,hj2⟩ := Finset.mem_Icc.mp hj
    have jp : (0:ℝ)<j := by exact_mod_cast (by omega : 0<j)
    have logj : log (j:ℝ) ≤ log (J:ℝ) := Real.log_le_log jp (by exact_mod_cast hj2)
    have xr : 0 < (N:ℝ)/j := div_pos npos jp
    have lower : log (N:ℝ)/2 ≤ log ((N:ℝ)/j) := by
      rw [Real.log_div npos.ne' jp.ne']; linarith
    have tp : 0 < T := lt_of_lt_of_le (by norm_num : (0:ℝ)<2) (le_max_left _ _)
    have threshold : B ≤ (N:ℝ)/j :=
      (le_max_right _ _).trans ((Real.log_le_log_iff tp xr).mp (by linarith))
    have count := hB _ threshold
    rw [Nat.floor_div_natCast, Nat.floor_natCast] at count
    have dx : 0 < log ((N:ℝ)/j) := by linarith
    calc
      (Nat.primeCounting (N/j) : ℝ) ≤ _ := count
      _ ≤ 4 * ((N:ℝ)/j) / (log N / 2) := by
        gcongr
      _ = (8*(N:ℝ)/log N) * (j:ℝ)⁻¹ := by ring
  have summed := Finset.sum_le_sum term
  rw [← Finset.mul_sum] at summed
  have harmonic_bound := harmonic_le_one_add_log J
  rw [harmonic_eq_sum_Icc] at harmonic_bound
  push_cast at harmonic_bound
  have combined := summed.trans (mul_le_mul_of_nonneg_left harmonic_bound (by positivity))
  have final : (8:ℝ) * (∑ j ∈ Finset.Icc 1 J, (Nat.primeCounting (N/j):ℝ)) ≤ N := by
    calc
      _ ≤ 8 * ((8*(N:ℝ)/log N) * (1 + log J)) := by linarith
      _ = (N:ℝ) * (64*(1+log J))/(log N) := by ring
      _ ≤ N := (div_le_iff₀ Lpos).mpr (mul_le_mul_of_nonneg_left hs npos.le)
  exact_mod_cast final

end A214620Analytic

namespace A214620Proof

open OMA.S_oeis_a214620
open scoped Finset
open Classical in
theorem signature_bound (N P : ℕ) :
    ((Finset.Icc 1 N).filter (fun n =>
      2 ≤ n ∧ n.minFac ≤ 3 ∧ n.primeFactors.sup id ≤ P ∧ ¬ Occurs n)).card ≤
        4 * (P+1) * (Nat.log 2 N + 2)^2 := by
  classical
  let sig (n : ℕ) := (n.minFac, n.primeFactors.sup id,
    (Nat.digits 2 n).count 0, (Nat.digits 2 n).count 1)
  let D := Nat.log 2 N + 2
  let box := Finset.range 4 ×ˢ (Finset.range (P+1) ×ˢ (Finset.range D ×ˢ Finset.range D))
  have h := Finset.card_le_card_of_injOn (s := (Finset.Icc 1 N).filter (fun n =>
    2 ≤ n ∧ n.minFac ≤ 3 ∧ n.primeFactors.sup id ≤ P ∧ ¬ Occurs n)) (t := box) sig
  apply le_trans (h ?_ ?_)
  · simp [box, D, pow_two, Nat.mul_assoc]
  · intro n hn
    obtain ⟨hi, hn2, hmin, hmax, _⟩ := Finset.mem_filter.mp hn
    have hlen := Nat.length_digits 2 n (by decide) (by omega)
    have hlog := Nat.log_mono_right (b := 2) (Finset.mem_Icc.mp hi).2
    have h0 := List.count_le_length (a := 0) (l := Nat.digits 2 n)
    have h1 := List.count_le_length (a := 1) (l := Nat.digits 2 n)
    simp only [sig, box, SetLike.mem_coe, Finset.mem_product, Finset.mem_range, D]
    omega
  · intro n hn m hm he
    by_contra hne
    obtain ⟨_, hn2, _, _, hno⟩ := Finset.mem_filter.mp hn
    obtain ⟨_, hm2, _, _, _⟩ := Finset.mem_filter.mp hm
    simp only [sig, Prod.mk.injEq] at he
    apply hno
    refine ⟨hn2, m, hm2, Ne.symm hne, he.1, he.2.1, List.perm_iff_count.mpr ?_⟩
    intro a
    rcases a with _|_|a
    · exact he.2.2.1
    · exact he.2.2.2
    · have hx (k : ℕ) : a+2 ∉ Nat.digits 2 k :=
        fun ha => by have := Nat.digits_lt_base (by decide : 1 < 2) ha; omega
      simp [List.count_eq_zero.mpr (hx n), List.count_eq_zero.mpr (hx m)]
end A214620Proof

open Finset OMA.S_oeis_a214620
namespace A214620Proof

def sample (i : ℕ) := 6*(i/4) + (if i%4 = 3 then 6 else i%4+2)

theorem sample_inj : Function.Injective sample := by
  intro a b he
  dsimp [sample] at he
  split_ifs at he <;> omega

theorem small_factors (N : ℕ) :
    4*(N/6) ≤ ((Icc 1 N).filter (fun n => 2 ≤ n ∧ n.minFac ≤ 3)).card := by
  classical
  rw [← card_range (4*(N/6)), ← card_image_of_injective _ sample_inj]
  apply card_le_card
  intro n hn
  obtain ⟨i, hi, rfl⟩ := mem_image.mp hn
  have h := mem_range.mp hi
  have bounds : 2 ≤ sample i ∧ sample i ≤ N := by
    unfold sample
    split <;> omega
  have hd : 2 ∣ sample i ∨ 3 ∣ sample i := by
    unfold sample
    split <;> omega
  refine mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega,bounds.2⟩,bounds.1,?_⟩
  rcases hd with h2|h3
  · exact (Nat.minFac_le_of_dvd (by decide) h2).trans (by decide : 2 ≤ 3)
  · exact Nat.minFac_le_of_dvd (by decide) h3

theorem large_factors (N J : ℕ) (hJ : 0 < J) :
    ((Icc 1 N).filter (fun n => 2 ≤ n ∧ N / J < n.primeFactors.sup id)).card ≤
    ∑ j ∈ Icc 1 J, Nat.primeCounting (N/j) := by
  classical
  let family := fun j : ℕ => ((N/j).primesLE).image (fun p => j*p)
  have cover : ((Icc 1 N).filter (fun n => 2 ≤ n ∧ N / J < n.primeFactors.sup id)) ⊆
      (Icc 1 J).biUnion family := by
    intro n hn
    obtain ⟨hb,h2,hbig⟩ := mem_filter.mp hn
    have hN := (mem_Icc.mp hb).2
    let p := n.primeFactors.sup id
    have hfac : n.primeFactors.Nonempty := by
      by_contra he
      rw [Finset.not_nonempty_iff_eq_empty.mp he] at hbig
      simp at hbig
    have hm : p ∈ n.primeFactors := by
      simpa [p] using (sup_mem_of_nonempty (f:=id) hfac)
    have pp := Nat.prime_of_mem_primeFactors hm
    have dv := Nat.dvd_of_mem_primeFactors hm
    obtain ⟨j,hj⟩ := dv
    have hprod : j*p = n := by rw [hj,Nat.mul_comm]
    have jp : 0 < j := Nat.pos_of_ne_zero (by intro hz; rw [hz, Nat.mul_zero] at hj; omega)
    have hl : j ≤ J := by
      have hh : N < p*J := (Nat.div_lt_iff_lt_mul hJ).mp hbig
      by_contra! h
      have := Nat.mul_le_mul_left p h.le
      omega
    apply mem_biUnion.mpr
    refine ⟨j,mem_Icc.mpr ⟨jp,hl⟩,mem_image.mpr ⟨p,?_,hprod⟩⟩
    apply Nat.mem_primesLE.mpr
    exact ⟨(Nat.le_div_iff_mul_le jp).mpr (by rw [←Nat.mul_comm,hprod]; exact hN),pp⟩
  calc
    _ ≤ _ := card_le_card cover
    _ ≤ ∑ j ∈ Icc 1 J, (family j).card := card_biUnion_le
    _ ≤ _ := by
      apply sum_le_sum
      intro j _
      calc
        _ ≤ ((N/j).primesLE).card := card_image_le
        _ = _ := Nat.primesLE_card_eq_primeCounting _
theorem binary_room (u : ℕ) (h : 32 ≤ u) : 512*(u+2)^2 ≤ 2^u := by
  induction u, h using Nat.le_induction with
  | base => decide
  | succ m hm ih =>
    rw [pow_succ]
    calc
      _ ≤ 2 * (512*(m+2)^2) := by nlinarith [Nat.zero_le ((m-1)^2)]
      _ ≤ _ := by omega

theorem room (N : ℕ) (hn : 2^32 ≤ N) :
    64 * (4 * (N / (Nat.log 2 N + 2)^4 + 1) * (Nat.log 2 N + 2)^2) ≤ N := by
  let t := Nat.log 2 N
  let D := t+2
  let Q := N/D^4
  have ht : 32 ≤ t := Nat.le_log_of_pow_le (by decide) hn
  have hN : 2^t ≤ N := Nat.pow_le_of_le_log (by omega) le_rfl
  have h1 : 512*D^2 ≤ N := (binary_room t ht).trans hN
  have hD : 32 ≤ D := by dsimp [D];omega
  have h2 : 512 ≤ D^2 := by nlinarith [Nat.mul_self_le_mul_self hD]
  have h3 : 512 * D^2 ≤ D^4 := by calc
      _ ≤ D^2 * D^2 := Nat.mul_le_mul_right _ h2
      _ = _ := by ring
  have h4 := (Nat.mul_le_mul_left Q h3).trans (Nat.div_mul_le_self N (D^4))
  change 64*(4*(Q+1)*D^2) ≤ N
  nlinarith only [h4,h1]

open Classical in
theorem combine (N : ℕ) (hn : 2^32 ≤ N)
    (hs : 8 * (∑ j ∈ Icc 1 ((Nat.log 2 N + 2)^4), Nat.primeCounting (N/j)) ≤ N)
    (hb : ∀ P : ℕ, ((Icc 1 N).filter (fun n =>
      2 ≤ n ∧ n.minFac ≤ 3 ∧ n.primeFactors.sup id ≤ P ∧ ¬ Occurs n)).card ≤
        4 * (P+1) * (Nat.log 2 N + 2)^2) :
    N < 2 * count N := by
  classical
  let J := (Nat.log 2 N + 2)^4
  let P := N / J
  let occ := (Icc 1 N).filter Occurs
  let large := (Icc 1 N).filter (fun n => 2 ≤ n ∧ P < n.primeFactors.sup id)
  let bad := (Icc 1 N).filter (fun n =>
      2 ≤ n ∧ n.minFac ≤ 3 ∧ n.primeFactors.sup id ≤ P ∧ ¬ Occurs n)
  have hcover : ((Icc 1 N).filter (fun n => 2 ≤ n ∧ n.minFac ≤ 3)) ⊆
      occ ∪ large ∪ bad := by
    intro n h
    obtain ⟨mem,h2,h3⟩ := mem_filter.mp h
    by_cases h0 : Occurs n
    · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨mem,h0⟩))
    by_cases h1 : P < n.primeFactors.sup id
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨mem,h2,h1⟩))
    exact mem_union_right _ (mem_filter.mpr ⟨mem,h2,h3,by omega,h0⟩)
  have hc := (small_factors N).trans (card_le_card hcover)
  have h1 := Finset.card_union_le (occ ∪ large) bad
  have h2 := Finset.card_union_le occ large
  have hl : 8 * large.card ≤ N :=
    (Nat.mul_le_mul_left 8 (large_factors N J (by dsimp [J];positivity))).trans hs
  have hb' : 64 * bad.card ≤ N := (Nat.mul_le_mul_left 64 (hb P)).trans (room N hn)
  change N < 2*occ.card
  omega
end A214620Proof
theorem OMA.solution : type_of% @OMA.S_oeis_a214620.main := by
  obtain ⟨b,hb⟩ := Filter.eventually_atTop.1 A214620Analytic.prime_sum_bound
  refine ⟨max b (2^32),fun n hn => ?_⟩
  apply A214620Proof.combine n ((le_max_right _ _).trans hn)
    (hb n ((le_max_left _ _).trans hn))
  exact A214620Proof.signature_bound n
