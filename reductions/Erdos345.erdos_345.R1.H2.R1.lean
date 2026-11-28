import OMAReductions.R_Erdos345_erdos_345_R1
import Mathlib

/-! A finite-interval reduction for Erdős 345's upper bound, following the separation of the cosine-polynomial theorem and subset-sum construction in Howe, Huffman, Kohlmeyer and Kruer, "Infinitely many decreases in the thresholds for sums of distinct powers" (2026), and the formalization by the same team at Ghuffy1/erdos345, commit 78012848fd02d20ffd2d2dec70fdc7408483f201. The envelope comparison and the interval extension to arbitrary integers are proved here. -/
open Real Filter
open scoped Topology
namespace Erdos345Envelope

theorem log_envelope :
    ∀ᶠ n : ℕ in atTop, ∀ k : ℕ, n<k → k≤2*(n+1) →
    512*(k:ℝ)*(1+Real.log (2*(k:ℝ)))^8 ≤
      (n+1:ℕ)*((⌊Real.exp ((17/40:ℝ)*Real.log n/Real.log (Real.log n))⌋₊ : ℕ):ℝ)*Real.log 2 := by
  have hL := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hT := Real.tendsto_log_atTop.comp hL
  have expbound := (Real.tendsto_exp_div_pow_atTop 2).comp hT
  filter_upwards [(tendsto_atTop.mp hL) (10^10), (tendsto_atTop.mp hT) 1,
    (tendsto_atTop.mp expbound) 40, eventually_ge_atTop 2] with n hlarge ht he hn
  intro k hnk hk
  let L := Real.log n
  let t := Real.log L
  change (10:ℝ)^10 ≤ L at hlarge
  change 1 ≤ t at ht
  change 40 ≤ Real.exp t / t^2 at he
  have hl : 0<L := by linarith
  have ht' : 0<t := by linarith
  have hLexp : Real.exp t = L := Real.exp_log hl
  rw [hLexp,le_div_iff₀ (sq_pos_of_pos ht')] at he
  have h9 : 9*t ≤ (17/40:ℝ)*L/t := (le_div_iff₀ ht').mpr (by nlinarith)
  have hpow : L^9 ≤ Real.exp ((17/40:ℝ)*L/t) := by
    have := Real.exp_le_exp.mpr h9
    simpa only [show (9:ℝ)*t=(9:ℕ)*t by norm_num,Real.exp_nat_mul,hLexp] using this
  let U := ⌊Real.exp ((17/40:ℝ)*L/t)⌋₊
  have hU : Real.exp ((17/40:ℝ)*L/t)< (U:ℝ)+1 := Nat.lt_floor_add_one _
  have hk' : (k:ℝ)≤2*((n:ℝ)+1) := by exact_mod_cast hk
  have hn' : (2:ℝ)≤n := by exact_mod_cast hn
  have kpos : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have hlog : Real.log (2*(k:ℝ)) ≤ Real.log 8+L := by
    rw [← Real.log_mul (by norm_num : (8:ℝ)≠0) (by positivity : (n:ℝ)≠0)]
    exact Real.log_le_log (by positivity) (by linarith)
  have hb : 1+Real.log (2*(k:ℝ)) ≤ 5*L := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<8)]
  have hb0 : 0 ≤ 1+Real.log (2*(k:ℝ)) := by
    have one : (1:ℝ)≤k := by exact_mod_cast (show 1≤k by omega)
    linarith [Real.log_nonneg (show 1≤2*(k:ℝ) by linarith)]
  have b8 := pow_le_pow_left₀ hb0 hb 8
  have p8 : 1 ≤ L^8 := one_le_pow₀ (by linarith) 
  have coef : 1024*(5*L)^8 ≤ (U:ℝ)*Real.log 2 := by
    have scale := mul_le_mul_of_nonneg_right hlarge (by positivity : 0≤L^8)
    have half : (U:ℝ)/2 ≤ (U:ℝ)*Real.log 2 := by
      nlinarith [mul_le_mul_of_nonneg_left (show (1/2:ℝ)≤Real.log 2 by linarith [Real.log_two_gt_d9]) (Nat.cast_nonneg U : (0:ℝ)≤U)]
    nlinarith only [scale,p8,hU,hpow,half]
  change _ ≤ ((n+1:ℕ):ℝ)*(U:ℝ)*Real.log 2
  push_cast
  calc
    _ ≤ 512*(2*((n:ℝ)+1))*(5*L)^8 := by gcongr
    _ = ((n:ℝ)+1)*(1024*(5*L)^8) := by ring
    _ ≤ ((n:ℝ)+1)*((U:ℝ)*Real.log 2) := mul_le_mul_of_nonneg_left coef (by positivity)
    _ = _ := by ring
end Erdos345Envelope
open Finset Real
namespace Erdos345Envelope

lemma doubling {b k : ℕ} (hb : 0<b) (hk : 2*k≤b) : (b+1)^k ≤ 2*b^k := by
  have bpos : 0<(b:ℝ) := by exact_mod_cast hb
  have ble : 2*(k:ℝ)≤b := by exact_mod_cast hk
  have small : (k:ℝ)*(b:ℝ)⁻¹ ≤ Real.log 2 := by
    rw [← div_eq_mul_inv]
    apply (div_le_iff₀ bpos).mpr
    nlinarith [mul_le_mul_of_nonneg_right (show (1/2:ℝ)≤Real.log 2 by linarith [Real.log_two_gt_d9]) bpos.le]
  have bound : (1+(b:ℝ)⁻¹)^k ≤ 2 := by
    calc
      _ ≤ (Real.exp (b:ℝ)⁻¹)^k := by
        apply pow_le_pow_left₀ (by positivity)
        linarith [Real.add_one_le_exp (b:ℝ)⁻¹]
      _ = Real.exp ((k:ℝ)*(b:ℝ)⁻¹) := (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr small
      _ = 2 := Real.exp_log (by norm_num)
  have h := mul_le_mul_of_nonneg_right bound (pow_nonneg bpos.le k)
  rw [← mul_pow, add_mul, one_mul, inv_mul_cancel₀ bpos.ne'] at h
  exact_mod_cast h

lemma extend {k N a L : ℕ} (hk : 0<k) (hN : 2*k≤N+1) (hL : (N+1)^k≤L)
    (rep : ∀ t ≤ L, ∃ S : Finset ℕ, (∀ i ∈ S, 0 < i ∧ i ≤ N) ∧ ∑ i ∈ S,i^k=a+t) :
    a ∈ IsAddComplete.thresholds (_root_.Erdos345.kthPowers k) := by
  classical
  have ind (j : ℕ) : ∃ length : ℕ, j≤length ∧ (N+j+1)^k≤length ∧
      ∀ t ≤ length, ∃ S : Finset ℕ, (∀ i ∈ S, 0 < i ∧ i ≤ N+j) ∧ ∑ i ∈ S,i^k=a+t := by
    induction j with
    | zero => simpa only [Nat.add_zero] using ⟨L,Nat.zero_le L,hL,rep⟩
    | succ j ih =>
      obtain ⟨len,hj,hnext,old⟩ := ih
      let b := N+j+1
      have bp : 0<b := by dsimp [b]; omega
      have d := doubling bp (show 2*k≤b by dsimp [b]; omega)
      have hb : b^k≤len := hnext
      have hp : 0<b^k := pow_pos bp k
      refine ⟨len+b^k,by omega,?_,?_⟩
      · change (b+1)^k≤len+b^k
        omega
      · intro t ht
        by_cases h : t≤len
        · obtain ⟨S,hs,sum⟩ := old t h
          exact ⟨S,fun i hi => ⟨(hs i hi).1,by have := (hs i hi).2; omega⟩,sum⟩
        · obtain ⟨S,hs,sum⟩ := old (t-b^k) (by omega)
          have fresh : b ∉ S := fun hi => by have := (hs b hi).2; dsimp [b] at this; omega
          refine ⟨insert b S,?_,?_⟩
          · intro i hi
            rcases Finset.mem_insert.mp hi with rfl|hi
            · exact ⟨bp,by dsimp [b]; omega⟩
            · exact ⟨(hs i hi).1,by have := (hs i hi).2; omega⟩
          · rw [Finset.sum_insert fresh,sum]
            omega
  intro m hm
  obtain ⟨len,hl,_,hs⟩ := ind (m-a)
  obtain ⟨S,hS,sum⟩ := hs _ hl
  refine ⟨S.image (fun i => i^k), ?_, ?_⟩
  · intro x hx
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
    exact ⟨i,(hS i hi).1,rfl⟩
  · rw [Finset.sum_image (fun i _ j _ h => Nat.pow_left_injective hk.ne' h),sum]
    omega
end Erdos345Envelope

namespace OMA.R_Erdos345_erdos_345_R1_H2_R1
open Filter Erdos345Envelope

/-- The Belov–Konyagin nonnegative cosine-polynomial input. -/
def H1 : Prop := ∀ J : ℕ, 0<J → ∃ (w : ℕ → ℕ) (a : ℝ),
    AntitoneOn w (Set.Iio J) ∧ (∑ i ∈ Finset.range J, w i) = J ∧
    (∀ θ : ℝ, 0 ≤ a + ∑ i ∈ Finset.range J, (w i : ℝ)*Real.cos (((i+1:ℕ):ℝ)*θ)) ∧
    a ≤ (2:ℝ)^32*(1+Real.log (J:ℝ))^5

/-- The finite subset-sum interval construction at a selected degree in each dyadic interval. -/
def H2 : Prop := (∀ J : ℕ, 0<J → ∃ (w : ℕ → ℕ) (a : ℝ),
    AntitoneOn w (Set.Iio J) ∧ (∑ i ∈ Finset.range J, w i) = J ∧
    (∀ θ : ℝ, 0 ≤ a + ∑ i ∈ Finset.range J, (w i : ℝ)*Real.cos (((i+1:ℕ):ℝ)*θ)) ∧
    a ≤ (2:ℝ)^32*(1+Real.log (J:ℝ))^5) →
  ∀ᶠ Y : ℕ in atTop, ∃ k N a L : ℕ,
    Y≤k ∧ k≤2*Y ∧ 0<k ∧ 2*k≤N+1 ∧ (N+1)^k≤L ∧
    Real.log (max 1 (a:ℝ)) ≤ 512*(k:ℝ)*(1+Real.log (2*(k:ℝ)))^8 ∧
    ∀ t≤L, ∃ S : Finset ℕ, (∀ i∈S, 0 < i ∧ i ≤ N) ∧ ∑ i∈S,i^k=a+t

theorem main : H1 → H2 → OMA.R_Erdos345_erdos_345_R1.H2 := by
  intro cosine finite
  have shift : Filter.Tendsto (fun n : ℕ => n+1) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_succ n) tendsto_id
  filter_upwards [shift.eventually (finite cosine),Erdos345Envelope.log_envelope] with n h he
  obtain ⟨k,N,a,L,hn,hk,hpos,hN,hL,ha,rep⟩ := h
  refine ⟨k,by omega,IsAddComplete.thresholds_mono (Erdos345Envelope.extend hpos hN hL rep) ?_⟩
  let M := (n+1)*⌊Real.exp ((17/40:ℝ)*Real.log n/Real.log (Real.log n))⌋₊
  change a ≤ 2^M
  have bound := ha.trans (he k (by omega) hk)
  have eq : Real.log ((2^M:ℕ):ℝ) = ((n+1:ℕ):ℝ)*
      ((⌊Real.exp ((17/40:ℝ)*Real.log n/Real.log (Real.log n))⌋₊:ℕ):ℝ)*Real.log 2 := by
    simp only [Nat.cast_pow,Nat.cast_ofNat,Real.log_pow,M,Nat.cast_mul]
  rw [←eq] at bound
  have pos : 0 < max 1 (a:ℝ) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have le := (Real.log_le_log_iff pos (by positivity)).mp bound
  exact_mod_cast (le_max_right 1 (a:ℝ)).trans le

end OMA.R_Erdos345_erdos_345_R1_H2_R1
