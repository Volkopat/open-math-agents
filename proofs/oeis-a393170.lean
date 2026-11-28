import OMAStatements.S_oeis_a393170
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace OMA.P_oeis_a393170

open OMA.S_oeis_a393170

private lemma zmod2_ps_two : (2 : PowerSeries (ZMod 2)) = 0 := by
  have h : (2 : ZMod 2) = 0 := by decide
  rw [← map_ofNat (PowerSeries.C (R := ZMod 2)), h, map_zero]

private lemma zmod2_ps_add_self (f : PowerSeries (ZMod 2)) : f + f = 0 := by
  rw [← two_mul, zmod2_ps_two, zero_mul]

private lemma zmod2_ps_sub (f g : PowerSeries (ZMod 2)) : f - g = f + g := by
  rw [sub_eq_add_neg, neg_eq_of_add_eq_zero_right (zmod2_ps_add_self g)]

private lemma coeff_sq_zmod2 (f : PowerSeries (ZMod 2)) (n : ℕ) :
    PowerSeries.coeff n (f ^ 2) = if Even n then PowerSeries.coeff (n / 2) f else 0 := by
  rw [sq, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => PowerSeries.coeff i f * PowerSeries.coeff j f)]
  let t : ℕ → ZMod 2 := fun i => PowerSeries.coeff i f * PowerSeries.coeff (n - i) f
  have hsym : ∀ i ≤ n, t (n - i) = t i := by
    intro i hi; dsimp only [t]; rw [Nat.sub_sub_self hi, mul_comm]
  let L := (Finset.range (n + 1)).filter (fun i => i < n - i)
  let R := (Finset.range (n + 1)).filter (fun i => n - i < i)
  let M := (Finset.range (n + 1)).filter (fun i => i = n - i)
  have hpart : Finset.range (n + 1) = L ∪ (R ∪ M) := by
    ext i; simp only [L, R, M, Finset.mem_union, Finset.mem_filter, Finset.mem_range]
    constructor
    · intro hi
      rcases lt_trichotomy i (n - i) with h | h | h
      · exact Or.inl ⟨hi, h⟩
      · exact Or.inr (Or.inr ⟨hi, h⟩)
      · exact Or.inr (Or.inl ⟨hi, h⟩)
    · rintro (⟨hi, _⟩ | ⟨hi, _⟩ | ⟨hi, _⟩) <;> exact hi
  have hd1 : Disjoint L (R ∪ M) := by
    rw [Finset.disjoint_left]; intro i h1 h2
    simp only [L, R, M, Finset.mem_union, Finset.mem_filter] at h1 h2; omega
  have hd2 : Disjoint R M := by
    rw [Finset.disjoint_left]; intro i h1 h2
    simp only [R, M, Finset.mem_filter] at h1 h2; omega
  have hLR : ∑ i ∈ L, t i = ∑ i ∈ R, t i := by
    refine Finset.sum_bij (fun i _ => n - i) ?_ ?_ ?_ ?_
    · intro i hi; simp only [L, R, Finset.mem_filter, Finset.mem_range] at hi ⊢; omega
    · intro i1 h1 i2 h2 heq; simp only [L, Finset.mem_filter, Finset.mem_range] at h1 h2; omega
    · intro j hj; simp only [L, R, Finset.mem_filter, Finset.mem_range] at hj ⊢
      exact ⟨n - j, ⟨by omega, by omega⟩, by omega⟩
    · intro i hi; simp only [L, Finset.mem_filter, Finset.mem_range] at hi
      exact (hsym i (by omega)).symm
  change ∑ i ∈ Finset.range (n + 1), t i = _
  rw [hpart, Finset.sum_union hd1, Finset.sum_union hd2, hLR, ← add_assoc]
  have hadd2 : ∀ x : ZMod 2, x + x = 0 := by decide
  rw [hadd2, zero_add]
  by_cases hev : Even n
  · rw [if_pos hev]
    have hM : M = {n / 2} := by
      ext i; simp only [M, Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
      rcases hev with ⟨m, rfl⟩; omega
    rw [hM, Finset.sum_singleton]
    dsimp only [t]
    have hsub : n - n / 2 = n / 2 := by rcases hev with ⟨m, rfl⟩; omega
    rw [hsub]
    have hsq : ∀ x : ZMod 2, x * x = x := by decide
    exact hsq _
  · rw [if_neg hev]
    have hM : M = ∅ := by
      ext i; simp only [M, Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false]
      rintro ⟨_, heq⟩; exact hev ⟨i, by omega⟩
    rw [hM, Finset.sum_empty]

private lemma odd_iff_zmod2_eq_one (z : ℤ) : Odd z ↔ (z : ZMod 2) = 1 := by
  constructor
  · rintro ⟨k, rfl⟩; push_cast; have h2 : (2 : ZMod 2) = 0 := by decide
    rw [h2, zero_mul, zero_add]
  · intro h
    rcases Int.even_or_odd z with ⟨k, rfl⟩ | hodd
    · push_cast at h
      have h2 : (k : ZMod 2) + (k : ZMod 2) = 0 := by
        generalize (k : ZMod 2) = x; revert x; decide
      rw [h2] at h; exact absurd h (by decide)
    · exact hodd

/-- General engine: if `a2 : (ZMod 2)⟦X⟧` has `a2(0) = 1`, `a2⁻¹` has zero even coefficients for `n ≥ 2`,
and `(a2 + X)⁻¹` has zero odd coefficients for `n ≥ 1`, then `coeff n a2 = 1 ↔ ∃ k, n = 2^k` for `n ≥ 1`. -/
private lemma parity_from_two_inverses (a2 b d : PowerSeries (ZMod 2))
    (ha0 : PowerSeries.constantCoeff a2 = 1)
    (hb : a2 * b = 1)
    (hd : (a2 + PowerSeries.X) * d = 1)
    (hb_even : ∀ n : ℕ, 1 ≤ n → Even n → PowerSeries.coeff n b = 0)
    (hd_odd : ∀ n : ℕ, Odd n → PowerSeries.coeff n d = 0) :
    ∀ n : ℕ, 1 ≤ n → (PowerSeries.coeff n a2 = 1 ↔ ∃ k : ℕ, n = 2 ^ k) := by
  have hb0 : PowerSeries.constantCoeff b = 1 := by
    have := congrArg PowerSeries.constantCoeff hb
    simp [map_mul, ha0] at this; exact this
  have hd0 : PowerSeries.constantCoeff d = 1 := by
    have := congrArg PowerSeries.constantCoeff hd
    simp [map_mul, map_add, ha0] at this; exact this
  -- Step 1: a2 + X has zero odd coefficients!
  have haX_odd : ∀ n : ℕ, Odd n → PowerSeries.coeff n (a2 + PowerSeries.X) = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hodd
      have hc := congrArg (PowerSeries.coeff n) hd
      have hn0 : n ≠ 0 := by rcases hodd with ⟨k, rfl⟩; omega
      rw [PowerSeries.coeff_one, if_neg hn0, PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (fun i j => PowerSeries.coeff i (a2 + PowerSeries.X) * PowerSeries.coeff j d)] at hc
      rw [Finset.sum_eq_single n] at hc
      · rw [Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff, hd0, mul_one] at hc
        exact hc
      · intro i hi hne
        have hilt : i < n := by have := Finset.mem_range.mp hi; omega
        rcases Nat.even_or_odd (n - i) with hev | hodd_j
        · have hodd_i : Odd i := by
            rcases hodd with ⟨k, rfl⟩; rcases hev with ⟨m, hm⟩
            exact ⟨k - m, by omega⟩
          rw [ih i hilt hodd_i, zero_mul]
        · rw [hd_odd (n - i) hodd_j, mul_zero]
      · intro h; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self n)) h
  have ha1 : PowerSeries.coeff 1 a2 = 1 := by
    have h1 := haX_odd 1 ⟨0, rfl⟩
    rw [map_add, PowerSeries.coeff_X, if_pos rfl] at h1
    generalize PowerSeries.coeff 1 a2 = x at h1 ⊢
    revert x h1; decide
  have ha_odd_ge3 : ∀ n : ℕ, 3 ≤ n → Odd n → PowerSeries.coeff n a2 = 0 := by
    intro n hn hodd
    have h := haX_odd n hodd
    rw [map_add, PowerSeries.coeff_X, if_neg (by omega), add_zero] at h
    exact h
  -- Step 2: define F(t) = ∑ coeff (2k) a2 * t^k and C(t) = ∑ coeff (2k+1) b * t^k
  let F : PowerSeries (ZMod 2) := PowerSeries.mk fun k => PowerSeries.coeff (2 * k) a2
  let C : PowerSeries (ZMod 2) := PowerSeries.mk fun k => PowerSeries.coeff (2 * k + 1) b
  -- F + X * C = 1 from even coefficients of a2 * b = 1!
  have hFXC : F + PowerSeries.X * C = 1 := by
    ext k
    have hc := congrArg (PowerSeries.coeff (2 * k)) hb
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => PowerSeries.coeff i a2 * PowerSeries.coeff j b)] at hc
    rw [map_add, ← pow_one (PowerSeries.X : PowerSeries (ZMod 2)), PowerSeries.coeff_X_pow_mul',
      PowerSeries.coeff_mk, PowerSeries.coeff_mk, PowerSeries.coeff_one]
    have h1eq : PowerSeries.coeff (2 * k) (1 : PowerSeries (ZMod 2)) = if k = 0 then 1 else 0 := by
      rw [PowerSeries.coeff_one]; by_cases hk : k = 0 <;> simp [hk]
    rw [h1eq] at hc
    -- Only i = 2*k (j = 0) and (if k ≥ 1) i = 1 (j = 2*k - 1) survive!
    by_cases hk0 : k = 0
    · subst hk0
      simp only [mul_zero, Finset.range_one, Finset.sum_singleton, Nat.sub_zero,
        PowerSeries.coeff_zero_eq_constantCoeff, hb0, mul_one, ite_true] at hc
      simp [hc]
    · have hk1 : 1 ≤ k := by omega
      rw [if_pos hk1]
      rw [if_neg hk0] at hc ⊢
      have hsum : ∑ i ∈ Finset.range (2 * k + 1), PowerSeries.coeff i a2 * PowerSeries.coeff (2 * k - i) b =
          PowerSeries.coeff (2 * k) a2 + PowerSeries.coeff (2 * (k - 1) + 1) b := by
        have hmem1 : 1 ∈ Finset.range (2 * k + 1) := Finset.mem_range.mpr (by omega)
        have hmem2 : 2 * k ∈ Finset.range (2 * k + 1) := Finset.mem_range.mpr (by omega)
        rw [← Finset.add_sum_erase _ _ hmem2,
          ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨by omega, hmem1⟩)]
        have hrest : ∑ i ∈ ((Finset.range (2 * k + 1)).erase (2 * k)).erase 1,
            PowerSeries.coeff i a2 * PowerSeries.coeff (2 * k - i) b = 0 := by
          apply Finset.sum_eq_zero
          intro i hi
          simp only [Finset.mem_erase, Finset.mem_range] at hi
          rcases Nat.even_or_odd i with hev | hodd
          · have hjeven : Even (2 * k - i) := by rcases hev with ⟨m, rfl⟩; exact ⟨k - m, by omega⟩
            rw [hb_even (2 * k - i) (by omega) hjeven, mul_zero]
          · rcases hodd with ⟨m, rfl⟩; rw [ha_odd_ge3 (2 * m + 1) (by omega) ⟨m, rfl⟩, zero_mul]
        rw [hrest, add_zero, Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff, hb0, mul_one,
          ha1, one_mul, show 2 * k - 1 = 2 * (k - 1) + 1 by omega]
      rw [hsum] at hc
      exact hc
  -- F * C = 1 from odd coefficients of a2 * b = 1!
  have hFC : F * C = 1 := by
    ext k
    have hc := congrArg (PowerSeries.coeff (2 * k + 1)) hb
    rw [PowerSeries.coeff_one, if_neg (by omega), PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => PowerSeries.coeff i a2 * PowerSeries.coeff j b)] at hc
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun p q => PowerSeries.coeff p F * PowerSeries.coeff q C), PowerSeries.coeff_one]
    -- Split i ∈ range (2*k + 2) into even i = 2*p and odd i!
    let Ev := (Finset.range (2 * k + 2)).filter Even
    let Od := (Finset.range (2 * k + 2)).filter (fun i => ¬ Even i)
    have hsplit : Finset.range (2 * k + 2) = Ev ∪ Od := by
      ext i; simp only [Ev, Od, Finset.mem_union, Finset.mem_filter, Finset.mem_range]
      tauto
    have hdisj : Disjoint Ev Od := by
      rw [Finset.disjoint_left]; intro i h1 h2; simp only [Ev, Od, Finset.mem_filter] at h1 h2; exact h2.2 h1.2
    rw [hsplit, Finset.sum_union hdisj] at hc
    have hEv : ∑ i ∈ Ev, PowerSeries.coeff i a2 * PowerSeries.coeff (2 * k + 1 - i) b =
        ∑ p ∈ Finset.range (k + 1), PowerSeries.coeff p F * PowerSeries.coeff (k - p) C := by
      refine (Finset.sum_bij (fun p _ => 2 * p) ?_ ?_ ?_ ?_).symm
      · intro p hp; simp only [Ev, Finset.mem_filter, Finset.mem_range] at hp ⊢
        exact ⟨by omega, ⟨p, by omega⟩⟩
      · intro p1 _ p2 _ h; omega
      · intro i hi; simp only [Ev, Finset.mem_filter, Finset.mem_range] at hi
        rcases hi.2 with ⟨p, rfl⟩
        exact ⟨p, Finset.mem_range.mpr (by omega), by omega⟩
      · intro p hp
        have hpk : p ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hp)
        rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk, show 2 * k + 1 - 2 * p = 2 * (k - p) + 1 by omega]
    have hOd : ∑ i ∈ Od, PowerSeries.coeff i a2 * PowerSeries.coeff (2 * k + 1 - i) b =
        if k = 0 then 1 else 0 := by
      rw [Finset.sum_eq_single 1]
      · rw [ha1, one_mul, show 2 * k + 1 - 1 = 2 * k by omega]
        by_cases hk0 : k = 0
        · subst hk0; simp [PowerSeries.coeff_zero_eq_constantCoeff, hb0]
        · rw [if_neg hk0, hb_even (2 * k) (by omega) ⟨k, by omega⟩]
      · intro i hi hne
        simp only [Od, Finset.mem_filter, Finset.mem_range] at hi
        have hodd_i : Odd i := Nat.not_even_iff_odd.mp hi.2
        have hi3 : 3 ≤ i := by rcases hodd_i with ⟨m, rfl⟩; omega
        rw [ha_odd_ge3 i hi3 hodd_i, zero_mul]
      · intro h1; exfalso; apply h1
        simp only [Od, Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, by decide⟩
    rw [hEv, hOd] at hc
    have hadd0 : ∀ x y : ZMod 2, x + y = 0 → x = y := by decide
    exact hadd0 _ _ hc
  -- Step 3: F^2 + F = X!
  have hFquad : F ^ 2 + F = PowerSeries.X := by
    have hm := congrArg (· * F) hFXC
    rw [add_mul, one_mul, mul_assoc, mul_comm C F, hFC, mul_one, ← sq] at hm
    have := congrArg (· + F + PowerSeries.X) hm
    have hsimp : F ^ 2 + PowerSeries.X + F + PowerSeries.X = F ^ 2 + F := by
      calc F ^ 2 + PowerSeries.X + F + PowerSeries.X
          = F ^ 2 + F + (PowerSeries.X + PowerSeries.X) := by ring
        _ = F ^ 2 + F + 0 := by rw [zmod2_ps_add_self]
        _ = F ^ 2 + F := add_zero _
    have hsimp2 : F + F + PowerSeries.X = PowerSeries.X := by
      rw [zmod2_ps_add_self, zero_add]
    rw [hsimp, hsimp2] at this
    exact this
  -- Step 4: deduce coeff k F = 1 ↔ ∃ m, k = 2^m for k ≥ 1!
  have hFchar : ∀ k : ℕ, 1 ≤ k → (PowerSeries.coeff k F = 1 ↔ ∃ m : ℕ, k = 2 ^ m) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk
      by_cases hk1 : k = 1
      · subst hk1
        have hc := congrArg (PowerSeries.coeff 1) hFquad
        rw [map_add, coeff_sq_zmod2, if_neg (by decide : ¬ Even 1), zero_add,
          PowerSeries.coeff_X, if_pos rfl] at hc
        simp only [hc, true_iff]
        exact ⟨0, by norm_num⟩
      · have hk2 : 2 ≤ k := by omega
        have hc := congrArg (PowerSeries.coeff k) hFquad
        rw [map_add, coeff_sq_zmod2, PowerSeries.coeff_X, if_neg (by omega : ¬ k = 1)] at hc
        by_cases hev : Even k
        · rw [if_pos hev] at hc
          have heq : PowerSeries.coeff k F = PowerSeries.coeff (k / 2) F := by
            have hsum : ∀ x y : ZMod 2, x + y = 0 → y = x := by decide
            exact hsum _ _ hc
          rw [heq, ih (k / 2) (by rcases hev with ⟨m, rfl⟩; omega) (by rcases hev with ⟨m, rfl⟩; omega)]
          constructor
          · rintro ⟨m, hm⟩
            refine ⟨m + 1, ?_⟩
            rcases hev with ⟨t, rfl⟩; rw [pow_succ']; omega
          · rintro ⟨m, hm⟩
            cases m with
            | zero => simp at hm; omega
            | succ m =>
              refine ⟨m, ?_⟩
              rw [hm, pow_succ', Nat.mul_div_cancel_left _ (by norm_num)]
        · rw [if_neg hev, zero_add] at hc
          rw [hc]
          constructor
          · intro h; exact absurd h (by decide)
          · rintro ⟨m, rfl⟩
            cases m with
            | zero => exact absurd rfl hk1
            | succ m => exact absurd ⟨2 ^ m, by rw [pow_succ]; ring⟩ hev
  -- Step 5: finish for all n ≥ 1!
  intro n hn
  by_cases hn1 : n = 1
  · subst hn1; simp only [ha1, true_iff]; exact ⟨0, by norm_num⟩
  · rcases Nat.even_or_odd n with ⟨k, rfl⟩ | hodd
    · have hk1 : 1 ≤ k := by omega
      have hcoeff : PowerSeries.coeff (k + k) a2 = PowerSeries.coeff k F := by
        rw [PowerSeries.coeff_mk, show 2 * k = k + k by omega]
      rw [hcoeff, hFchar k hk1]
      constructor
      · rintro ⟨m, rfl⟩; exact ⟨m + 1, by rw [pow_succ]; ring⟩
      · rintro ⟨m, hm⟩
        cases m with
        | zero => simp at hm; omega
        | succ m => refine ⟨m, ?_⟩; rw [pow_succ] at hm; omega
    · have hn3 : 3 ≤ n := by rcases hodd with ⟨m, rfl⟩; omega
      rw [ha_odd_ge3 n hn3 hodd]
      constructor
      · intro h; exact absurd h (by decide)
      · rintro ⟨m, rfl⟩
        cases m with
        | zero => exact absurd rfl hn1
        | succ m =>
          have hev : Even (2 ^ (m + 1)) := ⟨2 ^ m, by rw [pow_succ]; ring⟩
          exact absurd hev (Nat.not_even_iff_odd.mpr hodd)

private theorem prove_main : type_of% @OMA.S_oeis_a393170.main := by
  intro A hA0 hInv
  let φ := PowerSeries.map (Int.castRingHom (ZMod 2))
  set a2 : PowerSeries (ZMod 2) := φ A
  have ha0 : PowerSeries.constantCoeff a2 = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff, hA0, map_one]
  have hua : IsUnit a2 := PowerSeries.isUnit_iff_constantCoeff.mpr (by rw [ha0]; exact isUnit_one)
  have huax : IsUnit (a2 + PowerSeries.X) :=
    PowerSeries.isUnit_iff_constantCoeff.mpr (by simp [map_add, ha0])
  set b := Ring.inverse a2
  set d := Ring.inverse (a2 + PowerSeries.X)
  have hb : a2 * b = 1 := Ring.mul_inverse_cancel _ hua
  have hd : (a2 + PowerSeries.X) * d = 1 := Ring.mul_inverse_cancel _ huax
  have hinv_map : ∀ n : ℕ,
      φ (Ring.inverse (A - (n : PowerSeries ℤ) * PowerSeries.X)) =
        if Even n then b else d := by
    intro n
    have hun : IsUnit (A - (n : PowerSeries ℤ) * PowerSeries.X) :=
      PowerSeries.isUnit_iff_constantCoeff.mpr (by simp [map_sub, map_mul, hA0])
    have hmul := congrArg φ (Ring.mul_inverse_cancel _ hun)
    rw [map_mul, map_sub, map_mul, map_natCast, PowerSeries.map_X, map_one, zmod2_ps_sub] at hmul
    by_cases hev : Even n
    · rw [if_pos hev]
      have hn0 : (n : PowerSeries (ZMod 2)) = 0 := by
        rcases hev with ⟨m, rfl⟩
        rw [Nat.cast_add, zmod2_ps_add_self]
      rw [hn0, zero_mul, add_zero] at hmul
      exact hua.mul_left_cancel (hmul.trans hb.symm)
    · rw [if_neg hev]
      have hn1 : (n : PowerSeries (ZMod 2)) = 1 := by
        rcases Nat.not_even_iff_odd.mp hev with ⟨m, rfl⟩
        rw [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, zmod2_ps_two, zero_mul, zero_add]
      rw [hn1, one_mul] at hmul
      exact huax.mul_left_cancel (hmul.trans hd.symm)
  have hb_even : ∀ n : ℕ, 1 ≤ n → Even n → PowerSeries.coeff n b = 0 := by
    intro n hn hev
    have h0 := congrArg (Int.cast (R := ZMod 2)) (hInv n hn)
    rw [Int.cast_zero] at h0
    have hmap : ((PowerSeries.coeff n (Ring.inverse (A - (n : PowerSeries ℤ) * PowerSeries.X)) : ℤ) : ZMod 2) =
        PowerSeries.coeff n (φ (Ring.inverse (A - (n : PowerSeries ℤ) * PowerSeries.X))) := by
      rw [PowerSeries.coeff_map]; rfl
    rw [hmap, hinv_map n, if_pos hev] at h0
    exact h0
  have hd_odd : ∀ n : ℕ, Odd n → PowerSeries.coeff n d = 0 := by
    intro n hodd
    have hn : 1 ≤ n := by rcases hodd with ⟨m, rfl⟩; omega
    have h0 := congrArg (Int.cast (R := ZMod 2)) (hInv n hn)
    rw [Int.cast_zero] at h0
    have hmap : ((PowerSeries.coeff n (Ring.inverse (A - (n : PowerSeries ℤ) * PowerSeries.X)) : ℤ) : ZMod 2) =
        PowerSeries.coeff n (φ (Ring.inverse (A - (n : PowerSeries ℤ) * PowerSeries.X))) := by
      rw [PowerSeries.coeff_map]; rfl
    rw [hmap, hinv_map n, if_neg (Nat.not_even_iff_odd.mpr hodd)] at h0
    exact h0
  intro n hn
  rw [odd_iff_zmod2_eq_one]
  have hc : ((PowerSeries.coeff n A : ℤ) : ZMod 2) = PowerSeries.coeff n a2 := by
    rw [PowerSeries.coeff_map]; rfl
  rw [hc]
  exact parity_from_two_inverses a2 b d ha0 hb hd hb_even hd_odd n hn

end OMA.P_oeis_a393170

theorem OMA.solution : type_of% @OMA.S_oeis_a393170.main :=
  OMA.P_oeis_a393170.prove_main
