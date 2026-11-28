import OMAStatements.S_oeis_a181674

/-! Disproof of Charles R. Greathouse IV's average-order conjecture for A181674.
Credit: @cjchaffin.

At N = 2^(2^k) there are O(2^k/k) primorial values up to N. Split each
semiprime by the dyadic interval of its smaller factor. Chebyshev's upper
bound for prime counts, summed across the intervals, bounds the number of
semiprimes by O(N k / 2^k). Thus the summatory count is O(N) along this
subsequence, contradicting the conjectured lower bound.
-/

namespace OeisA181674Primorial

open Finset Filter OMA.S_oeis_a181674

noncomputable def primorialsLE (N : ℕ) : Finset ℕ := by
  classical
  exact (range (N + 1)).filter IsPrimorial

private theorem size_injective {a b : ℕ}
    (h : (Nat.primesLE a).card = (Nat.primesLE b).card) :
    primorial a = primorial b := by
  have he : Nat.primesLE a = Nat.primesLE b := by
    rcases le_total a b with hab | hba
    · exact eq_of_subset_of_card_le (Nat.primesLE_mono hab) h.ge
    · exact (eq_of_subset_of_card_le (Nat.primesLE_mono hba) h.le).symm
  simp only [primorial_eq_prod_primesLE, he]

private theorem size_bound (t h a : ℕ) (hh : 0 < h) (hp : primorial t ≤ 2^a) :
    (Nat.primesLE t).card ≤ 2^h + a/h := by
  classical
  let s := Nat.primesLE t
  let small := s.filter (fun p => p < 2^h)
  let large := s.filter (fun p => ¬p < 2^h)
  have hs : small.card ≤ 2^h := by
    simpa only [card_range] using
      (card_le_card (show small ⊆ range (2^h) from fun p hp => mem_range.mpr (mem_filter.mp hp).2))
  have hpow : (2^h)^large.card ≤ primorial t := by
    calc (2^h)^large.card = ∏ _ ∈ large, 2^h := by simp
         _ ≤ ∏ p ∈ large, p := prod_le_prod' (fun p hp => le_of_not_gt (mem_filter.mp hp).2)
         _ ≤ ∏ p ∈ s, p := prod_le_prod_of_subset_of_one_le' (filter_subset _ _)
           (fun p hp _ => (Nat.one_lt_of_mem_primesLE hp).le)
         _ = primorial t := (primorial_eq_prod_primesLE t).symm
  have hmul : h * large.card ≤ a := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    rw [pow_mul]
    exact hpow.trans hp
  have hl : large.card ≤ a/h := (Nat.le_div_iff_mul_le hh).mpr
    (by simpa only [Nat.mul_comm] using hmul)
  have he : small.card + large.card = s.card :=
    s.card_filter_add_card_filter_not (fun p => p < 2^h)
  change s.card ≤ 2^h + a/h
  omega

theorem card_bound (k : ℕ) (hk : 2 ≤ k) :
    k * (primorialsLE (2^(2^k))).card ≤ 9 * 2^k := by
  classical
  let h := k / 2
  have hh : 0 < h := by dsimp [h]; omega
  let b := 2^h + 2^k/h + 1
  have hc : (primorialsLE (2^(2^k))).card ≤ b := by
    rw [← card_range b]
    apply card_le_card_of_injOn (fun m : ℕ => m.primeFactors.card)
    · intro m hm
      obtain ⟨hmem, t, rfl⟩ := mem_filter.mp hm
      change (primorial t).primeFactors.card ∈ range b
      rw [primeFactors_primorial, mem_range]
      have ht := size_bound t h (2^k) hh (Nat.lt_succ_iff.mp (mem_range.mp hmem))
      dsimp [b]; omega
    · intro m hm v hv he
      obtain ⟨_, t, rfl⟩ := mem_filter.mp hm
      obtain ⟨_, u, rfl⟩ := mem_filter.mp hv
      apply size_injective
      simpa only [primeFactors_primorial] using he
  have h2 : h + h ≤ k := by dsimp [h]; omega
  have hk3 : k ≤ 3*h := by dsimp [h]; omega
  have ha : h * 2^h ≤ 2^k := calc
    h * 2^h ≤ 2^h * 2^h := Nat.mul_le_mul_right _ (Nat.lt_two_pow_self.le)
    _ = 2^(h+h) := (pow_add ..).symm
    _ ≤ 2^k := Nat.pow_le_pow_right (by decide) h2
  have hb : h * (2^k / h) ≤ 2^k := Nat.mul_div_le _ _
  have hh' : h ≤ 2^k := (show h ≤ k by omega).trans (Nat.lt_two_pow_self.le)
  have hB : h*b ≤ 3*2^k := by
    dsimp [b]; rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]; omega
  calc
    k * (primorialsLE (2^(2^k))).card ≤ (3*h)*b := Nat.mul_le_mul hk3 hc
    _ = 3*(h*b) := Nat.mul_assoc ..
    _ ≤ 9*2^k := by omega

theorem eventually_card_bound :
    ∀ᶠ k : ℕ in atTop, ((primorialsLE (2^(2^k))).card : ℝ) ≤ 9 * (2:ℝ)^k / k := by
  filter_upwards [eventually_ge_atTop 2] with k hk
  apply (le_div_iff₀ (by exact_mod_cast (show 0 < k by omega))).mpr
  rw [mul_comm]
  exact_mod_cast card_bound k hk

end OeisA181674Primorial



namespace A181674Blocks

open Finset OMA.S_oeis_a181674

noncomputable def semiprimeCount (N : ℕ) : ℕ := by
  classical
  exact ((range (N+1)).filter IsSemiprime).card

private def primeBlock (m i : ℕ) : Finset ℕ :=
  (((2^(i+1)).primesLE).product ((2^(m-i)).primesLE)).image (fun x : ℕ × ℕ => x.1*x.2)

private theorem block_card (m i : ℕ) :
    (primeBlock m i).card ≤ Nat.primeCounting (2^(i+1)) * Nat.primeCounting (2^(m-i)) := by
  unfold primeBlock
  apply card_image_le.trans
  exact (card_product _ _).le.trans (by simp)

private theorem sorted_factors {x : ℕ} (hx : IsSemiprime x) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≤ q ∧ x = p*q := by
  obtain ⟨p,q,hp,hq,rfl⟩ := hx
  rcases le_total p q with h | h
  · exact ⟨p,q,hp,hq,h,rfl⟩
  · exact ⟨q,p,hq,hp,h,mul_comm _ _⟩

theorem semiprimeCount_even_pow (h : ℕ) :
    semiprimeCount (2^(2*h)) ≤
      ∑ i ∈ range (h+1), Nat.primeCounting (2^(i+1)) * Nat.primeCounting (2^(2*h-i)) := by
  classical
  have cover : ((range (2^(2*h)+1)).filter IsSemiprime) ⊆ (range (h+1)).biUnion (primeBlock (2*h)) := by
    intro x hx
    obtain ⟨hsize,hsem⟩ := mem_filter.mp hx
    obtain ⟨p,q,hp,hq,hpq,rfl⟩ := sorted_factors hsem
    have hprod : p*q ≤ 2^(2*h) := Nat.lt_succ_iff.mp (mem_range.mp hsize)
    let i := p.log2
    have hlow : 2^i ≤ p := Nat.log2_self_le hp.ne_zero
    have hi : i ≤ h := by
      have hxpow : 2^(i+i) ≤ (2:ℕ)^(2*h) := by
        rw [pow_add]
        exact (Nat.mul_le_mul hlow (hlow.trans hpq)).trans hprod
      have := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hxpow
      omega
    have hu : q ≤ 2^(2*h-i) := by
      apply Nat.le_of_mul_le_mul_left (c := 2^i) _ (by positivity)
      rw [← pow_add,Nat.add_sub_of_le (by omega : i ≤ 2*h)]
      exact (Nat.mul_le_mul_right q hlow).trans hprod
    refine mem_biUnion.mpr ⟨i,mem_range.mpr (by omega),?_⟩
    apply mem_image.mpr
    exact ⟨(p,q),mem_product.mpr ⟨Nat.mem_primesLE.mpr ⟨Nat.lt_log2_self.le,hp⟩,
      Nat.mem_primesLE.mpr ⟨hu,hq⟩⟩,rfl⟩
  exact (card_le_card cover).trans (card_biUnion_le.trans
    (sum_le_sum fun i _ => block_card (2*h) i))

theorem semiprimeCount_dyadic (k : ℕ) (hk : 1 ≤ k) :
    semiprimeCount (2^(2^k)) ≤
      ∑ i ∈ range (2^(k-1)+1),
        Nat.primeCounting (2^(i+1)) * Nat.primeCounting (2^(2^k-i)) := by
  obtain ⟨l,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  simpa only [Nat.succ_sub_one,pow_succ' (2:ℕ) l] using semiprimeCount_even_pow (2^l)

end A181674Blocks

namespace A181674Dyadic

open Finset

theorem harmonic_range_dyadic (k : ℕ) :
    (∑ i ∈ range (2 ^ k + 1), (1 : ℝ) / (i + 1)) ≤ (k : ℝ) + 2 := by
  induction k with
  | zero => norm_num [sum_range_succ]
  | succ k ih =>
    let m : ℕ := 2 ^ k
    have hm : (0 : ℝ) < m := by dsimp [m]; positivity
    have hblock : (∑ i ∈ range m, (1 : ℝ) / ((↑(m + 1 + i) : ℝ) + 1)) ≤ 1 := by
      calc
        _ ≤ ∑ _i ∈ range m, (1 : ℝ) / m := by
          refine sum_le_sum fun i _ => one_div_le_one_div_of_le hm ?_
          push_cast
          linarith [Nat.cast_nonneg (α := ℝ) i]
        _ = 1 := by simp [nsmul_eq_mul, hm.ne']
    have hsplit : 2 ^ (k + 1) + 1 = (m + 1) + m := by dsimp [m]; rw [pow_succ]; omega
    rw [hsplit, sum_range_add]
    change (∑ i ∈ range (m + 1), (1 : ℝ) / (i + 1)) ≤ (k : ℝ) + 2 at ih
    rw [Nat.cast_succ]
    linarith

end A181674Dyadic
open Finset Filter Real
open OMA.S_oeis_a181674
namespace A181674

noncomputable def pc (N : ℕ) : Finset ℕ := by classical exact (range (N+1)).filter IsPrimorial
noncomputable def sc (N : ℕ) : Finset ℕ := by classical exact (range (N+1)).filter IsSemiprime

theorem sum_bound (N : ℕ) : summatory N ≤ 2*(pc N).card*(sc N).card := by
  classical
  let s := (pc N) ×ˢ (sc N)
  let t := (sc N) ×ˢ (pc N)
  calc
    _ ≤ (s ∪ t).card := by
      apply card_le_card
      intro z hz
      obtain ⟨hr, _, _, h | h⟩ := mem_filter.mp hz
      · exact mem_union_left _ <| mem_product.mpr ⟨mem_filter.mpr ⟨(mem_product.mp hr).1,h.1⟩,
            mem_filter.mpr ⟨(mem_product.mp hr).2,h.2⟩⟩
      · exact mem_union_right _ <| mem_product.mpr ⟨mem_filter.mpr ⟨(mem_product.mp hr).1,h.1⟩,
            mem_filter.mpr ⟨(mem_product.mp hr).2,h.2⟩⟩
    _ ≤ s.card + t.card := card_union_le _ _
    _ = _ := by simp only [s,t,card_product]; ring

theorem prime_dyadic : ∃ C : ℝ, 0 < C ∧ ∀ j : ℕ,
    (Nat.primeCounting (2^j) : ℝ) * (j+1) ≤ C * 2^j := by
  have hlog : 0 < log 2 := log_pos (by norm_num)
  have ht := (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < (2:ℝ))).eventually
    (Chebyshev.eventually_primeCounting_le (by norm_num : 0 < (1:ℝ)))
  obtain ⟨K,hK⟩ := eventually_atTop.mp ht
  let L := 2*(log 4+1)/log 2
  let D : ℝ := (Nat.primeCounting (2^K))*(K+1)
  have hl : 0 < L := by dsimp [L]; positivity
  refine ⟨max L D, hl.trans_le (le_max_left _ _), fun j => ?_⟩
  by_cases hj : K ≤ j ∧ 1 ≤ j
  · have h := hK j hj.1
    rw [show (2:ℝ)^j=((2^j:ℕ):ℝ) by norm_cast, Nat.floor_natCast] at h
    push_cast at h
    rw [Real.log_pow] at h
    have hpos : 0 < (j:ℝ)*log 2 := mul_pos (by exact_mod_cast hj.2) hlog
    have hπ := (le_div_iff₀ hpos).mp h
    have hπ' : (Nat.primeCounting (2^j):ℝ)*j ≤ (log 4+1)*2^j/log 2 :=
      (le_div_iff₀ hlog).mpr (by simpa [mul_assoc] using hπ)
    calc
      _ ≤ 2*((Nat.primeCounting (2^j):ℝ)*j) := by
        have h1 : (1:ℝ) ≤ j := by exact_mod_cast hj.2
        nlinarith [mul_nonneg (Nat.cast_nonneg (Nat.primeCounting (2^j)) : (0:ℝ) ≤ _) (sub_nonneg.mpr h1)]
      _ ≤ 2*((log 4+1)*2^j/log 2) := by gcongr
      _ = L*2^j := by dsimp [L]; ring
      _ ≤ _ := by gcongr; exact le_max_left _ _
  · have hj' : j ≤ K := by omega
    have hπ : (Nat.primeCounting (2^j):ℝ) ≤ Nat.primeCounting (2^K) :=
      by exact_mod_cast Nat.monotone_primeCounting (Nat.pow_le_pow_right (by decide) hj')
    have h1 : (1:ℝ) ≤ 2^j := one_le_pow₀ (by norm_num)
    have hD : 0 ≤ D := by dsimp [D]; positivity
    calc
      _ ≤ D := by dsimp [D]; gcongr
      _ ≤ D*2^j := by nlinarith [mul_nonneg hD (sub_nonneg.mpr h1)]
      _ ≤ _ := by gcongr; exact le_max_right _ _
end A181674

open Finset Filter Real
open OMA.S_oeis_a181674
namespace A181674

private theorem block_estimate {C : ℝ}
    (hC : ∀ j : ℕ, (Nat.primeCounting (2^j) : ℝ) * (j+1) ≤ C * 2^j)
    (hpos : 0 < C) (m i : ℕ) (hi : i+i ≤ m) :
    (m:ℝ) * ((Nat.primeCounting (2^(i+1)) : ℝ) * Nat.primeCounting (2^(m-i))) ≤
      (4*C^2 * (2:ℝ)^m) * (1/((i:ℝ)+1)) := by
  let a : ℝ := Nat.primeCounting (2^(i+1))
  let b : ℝ := Nat.primeCounting (2^(m-i))
  have a0 : 0 ≤ a := Nat.cast_nonneg _
  have b0 : 0 ≤ b := Nat.cast_nonneg _
  have h1 : a*(i+1) ≤ C*2^(i+1) := by
    have h := hC (i+1)
    dsimp only [a]; push_cast at h; nlinarith
  have h2 : b*m ≤ 2*(C*2^(m-i)) := by
    have h := hC (m-i)
    change b*((m-i:ℕ)+1 : ℝ) ≤ _ at h
    rw [Nat.cast_sub (by omega)] at h
    have hm : (i:ℝ) + i ≤ m := by exact_mod_cast hi
    nlinarith [mul_nonneg b0 (sub_nonneg.mpr hm)]
  change (m:ℝ)*(a*b) ≤ _
  rw [mul_one_div, le_div_iff₀ (by positivity)]
  calc
    _ = (a*(i+1))*(b*m) := by ring
    _ ≤ (C*2^(i+1))*(2*(C*2^(m-i))) := mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = _ := by
      rw [pow_succ]
      have hpow : (2:ℝ)^i*2^(m-i)=2^m := by rw [←pow_add,Nat.add_sub_of_le (by omega)]
      linear_combination (4*C^2)*hpow

theorem contradiction
    (hP : ∀ᶠ k : ℕ in atTop, ((pc (2^(2^k))).card : ℝ) ≤ 9 * (2:ℝ)^k / k)
    (hS : ∀ k : ℕ, 1 ≤ k → (sc (2^(2^k))).card ≤
      ∑ i ∈ range (2^(k-1)+1), Nat.primeCounting (2^(i+1)) * Nat.primeCounting (2^(2^k-i)))
    (hH : ∀ k : ℕ, (∑ i ∈ range (2^k+1), 1/((i:ℝ)+1)) ≤ (k:ℝ)+2) :
    ¬ conjecture := by
  obtain ⟨C,hpos,hC⟩ := prime_dyadic
  have hSum : ∀ᶠ k : ℕ in atTop, ((summatory (2^(2^k)) : ℕ) : ℝ) ≤
      216*C^2*(2:ℝ)^(2^k : ℕ) := by
    filter_upwards [hP,eventually_ge_atTop 1] with k hp hk
    let m : ℕ := 2^k
    have hm : m=2*2^(k-1) := by
      obtain ⟨l,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      simp [m,pow_succ']
    have hmpos : 0 < (m:ℝ) := by dsimp [m]; positivity
    have hkpos : 0 < (k:ℝ) := by exact_mod_cast hk
    have hs : ((sc (2^m)).card : ℝ) ≤
        ∑ i ∈ range (2^(k-1)+1),
          (Nat.primeCounting (2^(i+1)) : ℝ) * Nat.primeCounting (2^(m-i)) := by
      exact_mod_cast hS k hk
    have hbs : (m:ℝ)*(sc (2^m)).card ≤ (4*C^2*2^m)*((k:ℝ)+2) := by
      calc
        _ ≤ (m:ℝ)*_ := mul_le_mul_of_nonneg_left hs hmpos.le
        _ = _ := mul_sum ..
        _ ≤ ∑ i ∈ range (2^(k-1)+1), (4*C^2*(2:ℝ)^m)*(1/((i:ℝ)+1)) := by
          apply sum_le_sum
          intro i hi
          exact block_estimate hC hpos m i (by have := mem_range.mp hi; omega)
        _ = _ := (mul_sum ..).symm
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact (hH (k-1)).trans (by gcongr; exact Nat.sub_le _ _)
    have h1 := (le_div_iff₀ hkpos).mp hp
    have h2 : ((summatory (2^m) : ℕ) : ℝ) ≤ 2*((pc (2^m)).card : ℝ)*(sc (2^m)).card :=
      by exact_mod_cast sum_bound (2^m)
    have h1' : ((pc (2^m)).card : ℝ)*k ≤ 9*(m:ℝ) := by simpa [m] using h1
    have comb := mul_le_mul_of_nonneg_right h1' (Nat.cast_nonneg ((sc (2^m)).card) : (0:ℝ) ≤ _)
    have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk
    have hbs' : (m:ℝ)*(sc (2^m)).card ≤ (4*C^2*2^m)*(3*k) :=
      hbs.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
    change _ ≤ 216*C^2*2^m
    apply (mul_le_mul_iff_left₀ hkpos).mp
    nlinarith [mul_le_mul_of_nonneg_left h2 hkpos.le]
  intro hθ
  obtain ⟨c,hc,hc'⟩ := hθ.2.exists_pos
  have hN : Tendsto (fun k : ℕ => (2:ℕ)^(2^k : ℕ)) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by decide : 1 < (2:ℕ))).comp
      (tendsto_pow_atTop_atTop_of_one_lt (by decide : 1 < (2:ℕ)))
  let N (k : ℕ) : ℕ := 2^(2^k : ℕ)
  have hll : Tendsto (fun k : ℕ => Real.log (Real.log (N k : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hN))
  have ev := (hN.eventually hc'.bound).and (hSum.and (hll.eventually_gt_atTop (c*(216*C^2))))
  obtain ⟨k,hh,hs,hl⟩ := ev.exists
  change ‖(N k : ℝ)*Real.log (Real.log (N k : ℝ))‖ ≤ c*‖(summatory (N k) : ℝ)‖ at hh
  change c*(216*C^2) < Real.log (Real.log (N k : ℝ)) at hl
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (summatory (N k)) : (0:ℝ) ≤ _)] at hh
  have hn0 : 0 < (N k : ℝ) := by dsimp [N]; positivity
  have hs' : (summatory (N k) : ℝ) ≤ (216*C^2)*(N k : ℝ) := by simpa [N] using hs
  nlinarith [le_abs_self ((N k : ℝ)*Real.log (Real.log (N k : ℝ))),
    mul_lt_mul_of_pos_left hl hn0, mul_le_mul_of_nonneg_left hs' hc.le]
end A181674


theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a181674.main) :=
  A181674.contradiction OeisA181674Primorial.eventually_card_bound
    A181674Blocks.semiprimeCount_dyadic A181674Dyadic.harmonic_range_dyadic
