import OMAReductions.R_PartitionParity_bellaiche_nicolas_odd_explicit_R1_H2_R1
import Mathlib

/-! The characteristic-two Euler product bounds the support by odd partition numbers and generalized pentagonal shifts. -/

open PowerSeries PowerSeries.WithPiTopology Finset

namespace PartitionTransfer

-- The inverse-series lemma is from the merged proof of PartitionParity.kolberg by @LordMike.
theorem prod_eq_one :
    (PowerSeries.mk fun n => (Nat.partitionNumber n : ZMod 2)) * pentagonalSeries (ZMod 2) = 1 := by
  let _ : TopologicalSpace (ZMod 2) := ⊥
  have _ : DiscreteTopology (ZMod 2) := ⟨rfl⟩
  have h1 : (PowerSeries.mk fun n => (Nat.partitionNumber n : ZMod 2)) =
      ∏' i, ∑' j : ℕ, (X ^ ((i + 1) * j) : (ZMod 2)⟦X⟧) := by
    have := Nat.Partition.powerSeriesMk_card_restricted_eq_tprod (ZMod 2) (fun _ => True)
    simpa [Nat.Partition.restricted, Nat.partitionNumber] using this
  have hm : Multipliable (fun i : ℕ => ∑' j : ℕ, (X ^ ((i + 1) * j) : (ZMod 2)⟦X⟧)) := by
    simpa using Nat.Partition.multipliable_powerSeriesMk_card_restricted (ZMod 2) (fun _ => True)
  rw [← tprod_one_sub_X_pow, h1, ← hm.tprod_mul (multipliable_one_sub_X_pow _)]
  have h2 : ∀ i : ℕ, (∑' j : ℕ, (X ^ ((i + 1) * j) : (ZMod 2)⟦X⟧)) * (1 - X ^ (i + 1)) = 1 := by
    intro i
    have := tsum_pow_mul_one_sub_of_constantCoeff_eq_zero (R := ZMod 2)
      (f := (X ^ (i+1) : (ZMod 2)⟦X⟧)) (by simp)
    simpa [pow_mul] using this
  simp_rw [h2]
  exact tprod_one


theorem char_two_expand (P : PowerSeries (ZMod 2)) (i : ℕ) :
    P^(2^i) = PowerSeries.expand (2^i) (by positivity) P := by
  have f : iterateFrobenius (ZMod 2) 2 i = RingHom.id _ := by
    apply RingHom.ext
    intro x
    obtain ⟨n, rfl⟩ := ZMod.natCast_zmod_surjective x
    simp
  have g := MvPowerSeries.map_iterateFrobenius_expand 2 (by decide : 2 ≠ 0) P i
  rw [f,MvPowerSeries.map_id] at g
  exact g.symm

theorem support_witness (e n : ℕ) :
    let t := 4^(e+1)
    let k := (t-1)/3
    let E := pentagonalSeries (ZMod 2)
    let Δ := X * E^24
    coeff n (Δ^k) ≠ 0 →
      ∃ a : ℕ, Odd (Nat.partitionNumber a) ∧ ∃ z : ℤ,
        n = k + 8*a + (8*t)*pentagonal z := by
  classical
  intro t k E Δ hn
  let P := PowerSeries.mk fun a => (Nat.partitionNumber a : ZMod 2)
  have hp : P*E=1 := prod_eq_one
  have hmod : t % 3 = 1 := by
    dsimp [t]; rw [Nat.pow_mod]; norm_num
  have ht : 0 < t := by dsimp [t]; positivity
  have hpow : 24*k+8 = 8*t := by dsimp [k]; omega
  have texp : 8*t = 2^(3+2*(e+1)) := by
    dsimp [t]; rw [pow_add 2 3, pow_mul 2 2]; norm_num
  have factor : Δ^k = X^k * (PowerSeries.expand 8 (by decide) P *
      PowerSeries.expand (8*t) (by positivity) E) := by
    have h₈ : P^8 = PowerSeries.expand 8 (by decide) P := char_two_expand P 3
    have ht' : E^(8*t) = PowerSeries.expand (8*t) (by positivity) E := by
      simpa only [texp] using char_two_expand E (3+2*(e+1))
    dsimp [Δ]; rw [mul_pow, ←pow_mul, ←h₈, ←ht', ←hpow, pow_add]
    have hunit : P^8*E^8=1 := by rw [←mul_pow, hp, one_pow]
    rw [show P ^ 8 * (E ^ (24*k) * E ^ 8) = E ^ (24*k) * (P^8*E^8) by ring,hunit,mul_one]
  rw [factor,coeff_X_pow_mul'] at hn
  split at hn
  next hkn =>
    rw [coeff_mul] at hn
    obtain ⟨ij, hij, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
    obtain ⟨u,v⟩ := ij
    have huv : u+v=n-k := by simpa using hij
    obtain ⟨hu,hv⟩ := mul_ne_zero_iff.mp hne
    rw [coeff_expand] at hu hv
    split at hu
    next h8 =>
      split at hv
      next ht8 =>
        have hpodd : Odd (Nat.partitionNumber (u/8)) := by
          simpa [P, ZMod.natCast_eq_zero_iff_even] using hu
        have hz : v/(8*t) ∈ Set.range pentagonal := by
          by_contra hz
          exact hv (coeff_pentagonalSeries_eq_zero _ hz)
        obtain ⟨z,hz⟩ := hz
        refine ⟨u/8,hpodd,z,?_⟩
        rw [hz, Nat.mul_div_cancel' h8, Nat.mul_div_cancel' ht8]
        omega
      next => contradiction
    next => contradiction
  next => contradiction

open Real

theorem parameter_small (x : ℝ) (hx : 2 ≤ x) (hlarge : exp (exp 24) / 8 < x)
    (h : ℕ) (hlog : 4*((h:ℝ)-1) < log (log (8*x))) :
    (h:ℝ) ≤ 2/3 * sqrt x := by
  have xp : 0 < x := by linarith
  have e1 : 2 ≤ exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
  have e24 : 12 ≤ exp 24 := by linarith [Real.add_one_le_exp (24:ℝ)]
  have e12 : (2:ℝ)^12 ≤ exp 12 := by
    calc _ ≤ (exp 1)^12 := by gcongr
         _ = exp 12 := by rw [← Real.exp_nat_mul]; norm_num
  have rx : 12 ≤ sqrt x := Real.le_sqrt_of_sq_le (by linarith [exp_le_exp.mpr e24])
  have hp : 0 < log (8*x) := log_pos (by linarith)
  have l1 := Real.log_le_sub_one_of_pos hp
  have l2 := Real.log_le_sub_one_of_pos (sqrt_pos.2 xp)
  have l3 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  rw [Real.log_sqrt xp.le] at l2
  rw [Real.log_mul (by norm_num) xp.ne',show (8:ℝ)=2^3 by norm_num, Real.log_pow] at l1 hlog
  norm_num at l1 hlog
  linarith

theorem z_square (z : ℤ) : z^2 ≤ (pentagonal z : ℤ) := by
  have hh := two_mul_natCast_pentagonal z
  rcases le_or_gt z 0 with hn|hp
  · nlinarith [mul_nonneg_of_nonpos_of_nonpos hn (show z-1≤0 by omega)]
  · nlinarith [mul_nonneg hp.le (show 0≤z-1 by omega)]

theorem transfer (x : ℝ) (hx : 2 ≤ x) (hlarge : exp (exp 24)/8 < x)
    (e h : ℕ) (he : h+1=2^e) (hlog : 4*((h:ℝ)-1) < log (log (8*x))) :
    let t := 4^(e+1)
    let k := (t-1)/3
    let Δ : PowerSeries (ZMod 2) := X * pentagonalSeries (ZMod 2)^24
    let W := ((Finset.range (⌊8*x⌋₊+1)).filter fun n => coeff n (Δ^k) ≠ 0).card
    (h:ℝ)*W ≤ ({n : ℕ | n ≤ x ∧ Odd (Nat.partitionNumber n)}.ncard:ℝ)*sqrt (3*x) := by
  classical
  intro t k Δ W
  have xp : 0 ≤ x := by linarith
  have teq : t=4*(h+1)^2 := by
    dsimp [t]
    rw [he, ←pow_mul, Nat.mul_comm e 2, pow_mul, pow_succ]
    ring
  let d : ℝ := 2*((h:ℝ)+1)
  have dp : 0 < d := by dsimp [d]; positivity
  have td : (t:ℝ)=d^2 := by rw [teq]; push_cast; dsimp [d]; ring
  let B := ⌊sqrt x / d⌋₊
  let I := Finset.Icc (-(B:ℤ)) (B:ℤ)
  let A := (Finset.range (⌊x⌋₊+1)).filter fun a => Odd (Nat.partitionNumber a)
  let F (az : ℕ × ℤ) := k+8*az.1+8*t*pentagonal az.2
  have cardW : W ≤ A.card * (2*B+1) := by
    have sub : ((Finset.range (⌊8*x⌋₊+1)).filter fun n => coeff n (Δ^k) ≠ 0) ⊆
        (A ×ˢ I).image F := by
      intro n hn
      obtain ⟨hn₁,hn₂⟩ := Finset.mem_filter.mp hn
      have nr : (n:ℝ) ≤ 8*x := (Nat.le_floor_iff (by positivity)).mp (by simpa using hn₁)
      obtain ⟨a,ha,z,hz⟩ := support_witness e n hn₂
      change n=k+8*a+8*t*pentagonal z at hz
      have nr' : (k:ℝ)+8*a+8*t*(pentagonal z:ℝ) ≤ 8*x := by
        rw [hz] at nr; push_cast at nr; exact nr
      have ar : (a:ℝ) ≤ x := by nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) t) (Nat.cast_nonneg (pentagonal z))]
      have zsq : (z:ℝ)^2 ≤ (pentagonal z:ℝ) := by exact_mod_cast z_square z
      have bound : (d * |(z:ℝ)|)^2 ≤ x := by
        rw [mul_pow, sq_abs, ←td]
        nlinarith [mul_le_mul_of_nonneg_left zsq (Nat.cast_nonneg t)]
      have za : (z.natAbs:ℝ) ≤ sqrt x / d := by
        rw [le_div_iff₀ dp, Nat.cast_natAbs, Int.cast_abs, mul_comm]
        exact le_sqrt_of_sq_le bound
      have zb : z.natAbs ≤ B := Nat.le_floor za
      have zi : z ∈ I := by
        change z ∈ Finset.Icc _ _
        rw [Finset.mem_Icc]
        omega
      refine Finset.mem_image.mpr ⟨(a,z), Finset.mem_product.mpr ⟨?_,zi⟩,hz.symm⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have := Nat.le_floor ar; omega),ha⟩
    have ci : I.card = 2*B+1 := by dsimp [I]; rw [Int.card_Icc]; omega
    exact (Finset.card_le_card sub).trans ((Finset.card_image_le).trans (by rw [Finset.card_product,ci]))
  have ca : ({n : ℕ | n ≤ x ∧ Odd (Nat.partitionNumber n)} : Set ℕ) = (A : Set ℕ) := by
    ext n; simp [A, Nat.le_floor_iff xp]
  rw [ca, Set.ncard_coe_finset]
  have bb : (B:ℝ) * d ≤ sqrt x := (le_div_iff₀ dp).mp (Nat.floor_le (by positivity))
  have small := parameter_small x hx hlarge h hlog
  have rad : (5/3:ℝ)*sqrt x ≤ sqrt (3*x) := by
    apply le_sqrt_of_sq_le
    nlinarith [Real.sq_sqrt xp]
  have bound : (h:ℝ)*(2*(B:ℝ)+1) ≤ sqrt (3*x) := by
    dsimp [d] at bb
    apply le_trans _ rad
    nlinarith [Nat.cast_nonneg (α := ℝ) B]
  have cw : (W:ℝ) ≤ (A.card:ℝ)*(2*(B:ℝ)+1) := by exact_mod_cast cardW
  calc (h:ℝ)*W ≤ h*((A.card:ℝ)*(2*(B:ℝ)+1)) := by gcongr
       _ = (A.card:ℝ)*(h*(2*(B:ℝ)+1)) := by ring
       _ ≤ _ := by gcongr

end PartitionTransfer

theorem OMA.solution : OMA.R_PartitionParity_bellaiche_nicolas_odd_explicit_R1_H2_R1.H1 := by
  intro x hx hlarge L e h he _ _ hlog
  exact PartitionTransfer.transfer x hx hlarge e h he hlog
