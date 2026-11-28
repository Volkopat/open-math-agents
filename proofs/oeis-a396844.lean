import OMAStatements.S_oeis_a396844
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace OMA.P_oeis_a396844

open OMA.S_oeis_a396844

/-- Explicit recurrence defining the unique integer sequence `aSeq` with `a(0) = 0`, `a(1) = 1`,
and `A(x * A(x) - 4 * x * A(x)^2) = x^2`. -/
private noncomputable def aSeq : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 =>
    let Atrunc : PowerSeries ℤ := PowerSeries.mk fun j => if _ : j < n + 2 then aSeq j else 0
    let Utrunc : PowerSeries ℤ := PowerSeries.X * Atrunc - 4 * PowerSeries.X * Atrunc ^ 2
    4 * PowerSeries.coeff (n + 2) (Atrunc ^ 2) -
      ∑ k : Fin n, aSeq (k.1 + 2) * PowerSeries.coeff (n + 3) (Utrunc ^ (k.1 + 2))

private lemma coeff_X_mul_eq {R : Type*} [CommRing R] (f : PowerSeries R) (m : ℕ) :
    PowerSeries.coeff (m + 1) (PowerSeries.X * f) = PowerSeries.coeff m f := by
  rw [← pow_one (PowerSeries.X : PowerSeries R), PowerSeries.coeff_X_pow_mul',
    if_pos (by omega), Nat.add_sub_cancel]

private lemma coeff_X_mul_zero {R : Type*} [CommRing R] (f : PowerSeries R) :
    PowerSeries.coeff 0 (PowerSeries.X * f) = 0 := by
  simp [PowerSeries.coeff_zero_eq_constantCoeff]

private lemma coeff_pow_eq_zero_of_lt_two_mul {R : Type*} [CommRing R] {g : PowerSeries R}
    (hg0 : PowerSeries.constantCoeff g = 0) (hg1 : PowerSeries.coeff 1 g = 0)
    {d m : ℕ} (h : m < 2 * d) :
    PowerSeries.coeff m (g ^ d) = 0 := by
  have hgX2 : g = PowerSeries.X ^ 2 * PowerSeries.mk (fun p => PowerSeries.coeff (p + 2) g) := by
    ext k
    rw [PowerSeries.coeff_X_pow_mul']
    by_cases hk : 2 ≤ k
    · rw [if_pos hk, PowerSeries.coeff_mk, show k - 2 + 2 = k by omega]
    · rw [if_neg hk]
      have : k = 0 ∨ k = 1 := by omega
      rcases this with rfl | rfl
      · rwa [PowerSeries.coeff_zero_eq_constantCoeff]
      · exact hg1
  rw [hgX2, mul_pow, ← pow_mul, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]

private lemma coeff_pow_congr_of_ord2 {R : Type*} [CommRing R] {u v : PowerSeries R}
    (_hu0 : PowerSeries.constantCoeff u = 0) (_hu1 : PowerSeries.coeff 1 u = 0)
    (_hv0 : PowerSeries.constantCoeff v = 0) (_hv1 : PowerSeries.coeff 1 v = 0)
    {M : ℕ} (h : ∀ j ≤ M, PowerSeries.coeff j u = PowerSeries.coeff j v) (d : ℕ) :
    ∀ m ≤ M, PowerSeries.coeff m (u ^ d) = PowerSeries.coeff m (v ^ d) := by
  induction d with
  | zero => intro m _; simp
  | succ d ih =>
    intro m hm
    rw [pow_succ, pow_succ, PowerSeries.coeff_mul, PowerSeries.coeff_mul]
    apply Finset.sum_congr rfl
    intro ⟨i, j⟩ hij
    rw [Finset.mem_antidiagonal] at hij
    rw [ih i (by omega), h j (by omega)]

private lemma coeff_mul_congr_of_const0 {R : Type*} [CommRing R] {u v : PowerSeries R}
    (hu0 : PowerSeries.constantCoeff u = 0) (hv0 : PowerSeries.constantCoeff v = 0)
    {M : ℕ} (h : ∀ j < M, PowerSeries.coeff j u = PowerSeries.coeff j v) :
    PowerSeries.coeff M (u ^ 2) = PowerSeries.coeff M (v ^ 2) := by
  rw [pow_two, pow_two, PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro ⟨i, j⟩ hij
  rw [Finset.mem_antidiagonal] at hij
  by_cases hi : i = 0
  · subst hi; simp [PowerSeries.coeff_zero_eq_constantCoeff, hu0, hv0]
  · by_cases hj : j = 0
    · subst hj; simp [PowerSeries.coeff_zero_eq_constantCoeff, hu0, hv0]
    · rw [h i (by omega), h j (by omega)]

private lemma aSeq_satisfies :
    let A : PowerSeries ℤ := PowerSeries.mk aSeq
    PowerSeries.constantCoeff A = 0 ∧
    PowerSeries.coeff 1 A = 1 ∧
    PowerSeries.subst (PowerSeries.X * A - 4 * PowerSeries.X * A ^ 2) A = PowerSeries.X ^ 2 := by
  intro A
  have hA0 : PowerSeries.constantCoeff A = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff]; simp [A, aSeq]
  have hA1 : PowerSeries.coeff 1 A = 1 := by simp [A, aSeq]
  refine ⟨hA0, hA1, ?_⟩
  set U : PowerSeries ℤ := PowerSeries.X * A - 4 * PowerSeries.X * A ^ 2
  have hU0 : PowerSeries.constantCoeff U = 0 := by
    simp [U, map_sub, map_mul]
  have hU1 : PowerSeries.coeff 1 U = 0 := by
    simp only [U, map_sub, mul_assoc, show (4 : PowerSeries ℤ) * (PowerSeries.X * A ^ 2) =
      PowerSeries.C 4 * (PowerSeries.X * A ^ 2) by rfl, PowerSeries.coeff_C_mul,
      coeff_X_mul_eq]
    rw [PowerSeries.coeff_zero_eq_constantCoeff, hA0, map_pow, hA0]
    norm_num
  have hU2 : PowerSeries.coeff 2 U = 1 := by
    simp only [U, map_sub, mul_assoc, show (4 : PowerSeries ℤ) * (PowerSeries.X * A ^ 2) =
      PowerSeries.C 4 * (PowerSeries.X * A ^ 2) by rfl, PowerSeries.coeff_C_mul,
      coeff_X_mul_eq, hA1]
    have hA2_1 : PowerSeries.coeff 1 (A ^ 2) = 0 := by
      rw [pow_two, PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => PowerSeries.coeff i A * PowerSeries.coeff j A)]
      simp [Finset.sum_range_succ, PowerSeries.coeff_zero_eq_constantCoeff, hA0]
    rw [hA2_1]; norm_num
  have hSub : PowerSeries.HasSubst U := PowerSeries.HasSubst.of_constantCoeff_zero hU0
  ext m
  rw [PowerSeries.coeff_subst' hSub, PowerSeries.coeff_X_pow]
  simp only [smul_eq_mul]
  have hfin : ∑ᶠ d : ℕ, PowerSeries.coeff d A * PowerSeries.coeff m (U ^ d) =
      ∑ d ∈ Finset.range (m + 1), aSeq d * PowerSeries.coeff m (U ^ d) := by
    rw [finsum_eq_sum_of_support_subset]
    · refine Finset.sum_congr rfl fun d _ => ?_; simp [A]
    · intro d hd
      simp only [Function.mem_support, ne_eq] at hd
      simp only [Finset.mem_coe, Finset.mem_range]
      by_contra hge
      exact hd (by rw [coeff_pow_eq_zero_of_lt_two_mul hU0 hU1 (by omega), mul_zero])
  rw [hfin]
  have ha0_eq : aSeq 0 = 0 := by unfold aSeq; rfl
  have ha1_eq : aSeq 1 = 1 := by unfold aSeq; rfl
  rcases m with _ | _ | _ | n
  · simp [ha0_eq]
  · simp [Finset.sum_range_succ, ha0_eq, ha1_eq, hU1]
  · simp [Finset.sum_range_succ, ha0_eq, ha1_eq, hU2, coeff_pow_eq_zero_of_lt_two_mul hU0 hU1 (d := 2) (m := 2) (by omega)]
  · -- m = n + 3
    rw [if_neg (by omega)]
    -- Split d = 0, d = 1, 2 ≤ d ≤ n + 1, d ≥ n + 2
    have htrunc : ∑ d ∈ Finset.range (n + 4), aSeq d * PowerSeries.coeff (n + 3) (U ^ d) =
        aSeq 1 * PowerSeries.coeff (n + 3) U +
          ∑ k : Fin n, aSeq (k.1 + 2) * PowerSeries.coeff (n + 3) (U ^ (k.1 + 2)) := by
      have hsub : ∑ d ∈ Finset.range (n + 4), aSeq d * PowerSeries.coeff (n + 3) (U ^ d) =
          ∑ d ∈ Finset.range (n + 2), aSeq d * PowerSeries.coeff (n + 3) (U ^ d) := by
        refine (Finset.sum_subset (Finset.range_mono (by omega)) fun d _ hd => ?_).symm
        rw [Finset.mem_range] at hd
        rw [coeff_pow_eq_zero_of_lt_two_mul hU0 hU1 (by omega), mul_zero]
      rw [hsub, Finset.sum_range_succ', Finset.sum_range_succ']
      simp only [ha0_eq, zero_mul, add_zero, Nat.zero_add, pow_one]
      rw [add_comm]
      congr 1
      rw [Fin.sum_univ_eq_sum_range (fun k => aSeq (k + 2) * PowerSeries.coeff (n + 3) (U ^ (k + 2)))]
    rw [htrunc]
    set Atrunc : PowerSeries ℤ := PowerSeries.mk fun j => if _ : j < n + 2 then aSeq j else 0
    set Utrunc : PowerSeries ℤ := PowerSeries.X * Atrunc - 4 * PowerSeries.X * Atrunc ^ 2
    have hAt0 : PowerSeries.constantCoeff Atrunc = 0 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff]; simp [Atrunc, ha0_eq]
    have hAt_agree : ∀ j < n + 2, PowerSeries.coeff j A = PowerSeries.coeff j Atrunc := by
      intro j hj; simp [A, Atrunc, hj]
    have hUt0 : PowerSeries.constantCoeff Utrunc = 0 := by simp [Utrunc, map_sub, map_mul]
    have hUt1 : PowerSeries.coeff 1 Utrunc = 0 := by
      simp only [Utrunc, map_sub, mul_assoc, show (4 : PowerSeries ℤ) * (PowerSeries.X * Atrunc ^ 2) =
        PowerSeries.C 4 * (PowerSeries.X * Atrunc ^ 2) by rfl, PowerSeries.coeff_C_mul, coeff_X_mul_eq]
      rw [PowerSeries.coeff_zero_eq_constantCoeff, hAt0, map_pow, hAt0]; norm_num
    have hU_agree : ∀ j ≤ n + 1, PowerSeries.coeff j U = PowerSeries.coeff j Utrunc := by
      intro j hj
      cases j with
      | zero => rw [PowerSeries.coeff_zero_eq_constantCoeff, hU0, hUt0]
      | succ j' =>
        simp only [U, Utrunc, map_sub, mul_assoc,
          show (4 : PowerSeries ℤ) * (PowerSeries.X * A ^ 2) = PowerSeries.C 4 * (PowerSeries.X * A ^ 2) by rfl,
          show (4 : PowerSeries ℤ) * (PowerSeries.X * Atrunc ^ 2) = PowerSeries.C 4 * (PowerSeries.X * Atrunc ^ 2) by rfl,
          PowerSeries.coeff_C_mul, coeff_X_mul_eq]
        rw [hAt_agree j' (by omega), coeff_mul_congr_of_const0 hA0 hAt0 (fun r hr => hAt_agree r (by omega))]
    -- For k : Fin n, coeff (n+3) (U^(k+2)) = coeff (n+3) (Utrunc^(k+2)) since U = O(X^2)
    have hUk : ∀ k : Fin n, PowerSeries.coeff (n + 3) (U ^ (k.1 + 2)) =
        PowerSeries.coeff (n + 3) (Utrunc ^ (k.1 + 2)) := by
      intro k
      conv_lhs => rw [pow_succ, PowerSeries.coeff_mul]
      conv_rhs => rw [pow_succ, PowerSeries.coeff_mul]
      apply Finset.sum_congr rfl
      intro ⟨i, j⟩ hij
      rw [Finset.mem_antidiagonal] at hij
      by_cases hi : i < 2 * (k.1 + 1)
      · rw [coeff_pow_eq_zero_of_lt_two_mul hU0 hU1 hi, coeff_pow_eq_zero_of_lt_two_mul hUt0 hUt1 hi,
          zero_mul, zero_mul]
      · by_cases hj : j < 2
        · have hj01 : j = 0 ∨ j = 1 := by omega
          rcases hj01 with rfl | rfl
          · rw [PowerSeries.coeff_zero_eq_constantCoeff, hU0, hUt0, mul_zero, mul_zero]
          · rw [hU1, hUt1, mul_zero, mul_zero]
        · rw [hU_agree j (by omega),
            coeff_pow_congr_of_ord2 hU0 hU1 hUt0 hUt1 hU_agree (k.1 + 1) i (by omega)]
    have hU_n3 : PowerSeries.coeff (n + 3) U = aSeq (n + 2) - 4 * PowerSeries.coeff (n + 2) (Atrunc ^ 2) := by
      simp only [U, map_sub, mul_assoc,
        show (4 : PowerSeries ℤ) * (PowerSeries.X * A ^ 2) = PowerSeries.C 4 * (PowerSeries.X * A ^ 2) by rfl,
        PowerSeries.coeff_C_mul, coeff_X_mul_eq]
      rw [coeff_mul_congr_of_const0 hA0 hAt0 hAt_agree]
      simp [A]
    rw [ha1_eq, one_mul, hU_n3]
    have hsum_eq : ∑ k : Fin n, aSeq (k.1 + 2) * PowerSeries.coeff (n + 3) (U ^ (k.1 + 2)) =
        ∑ k : Fin n, aSeq (k.1 + 2) * PowerSeries.coeff (n + 3) (Utrunc ^ (k.1 + 2)) :=
      Finset.sum_congr rfl fun k _ => by rw [hUk k]
    rw [hsum_eq]
    have ha_n2 : aSeq (n + 2) = 4 * PowerSeries.coeff (n + 2) (Atrunc ^ 2) -
        ∑ k : Fin n, aSeq (k.1 + 2) * PowerSeries.coeff (n + 3) (Utrunc ^ (k.1 + 2)) := by
      conv_lhs => unfold aSeq
    rw [ha_n2]
    ring

open Classical in
/-- Explicit closed-form formula for `aSeq n mod 16`:
`aSeq 0 ≡ 0`, `aSeq 1 ≡ 1`, `aSeq (2^j + 1) ≡ 4 * (-1)^j`, and `0` otherwise. -/
private noncomputable def targetMod16 (n : ℕ) : ZMod 16 :=
  if n = 1 then 1
  else if h : ∃ j : ℕ, n = 2 ^ j + 1 then
    let j := Classical.choose h
    4 * (-1 : ZMod 16) ^ j
  else 0

private lemma targetMod16_eq_of_pow2 {n j : ℕ} (h : n = 2 ^ j + 1) :
    targetMod16 n = 4 * (-1 : ZMod 16) ^ j := by
  have hn1 : n ≠ 1 := by
    have := Nat.one_le_pow j 2 (by norm_num); omega
  unfold targetMod16
  rw [if_neg hn1]
  have hex : ∃ j', n = 2 ^ j' + 1 := ⟨j, h⟩
  rw [dif_pos hex]
  have hj : Classical.choose hex = j := by
    have hch := Classical.choose_spec hex
    have hpow : 2 ^ Classical.choose hex = 2 ^ j := by omega
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) hpow
  rw [hj]

private lemma four_dvd_aSeq_of_ge2 (n : ℕ) :
    (aSeq n : ZMod 16) = targetMod16 n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rcases n with _ | _ | r
    · simp [aSeq, targetMod16]
    · simp [aSeq, targetMod16]
    · -- n = r + 2
      set N := r + 2
      have hN2 : 2 ≤ N := by omega
      -- First: for all j < N, (aSeq j : ZMod 4) = if j = 1 then 1 else 0!
      have hmod4 : ∀ j < N, (aSeq j : ZMod 4) = if j = 1 then 1 else 0 := by
        intro j hj
        have h16 := ih j hj
        have hcast : ((aSeq j : ZMod 16).val : ZMod 4) = (aSeq j : ZMod 4) := by
          have : (aSeq j : ZMod 4) = ZMod.castHom (show 4 ∣ 16 by decide) (ZMod 4) (aSeq j : ZMod 16) := by
            simp
          rw [this, ← ZMod.natCast_zmod_val (aSeq j : ZMod 16)]
          simp
        rw [← hcast, h16]
        unfold targetMod16
        split_ifs with h1 hex
        · decide
        · have hdiv4 : (4 * (-1 : ZMod 16) ^ Classical.choose hex).val % 4 = 0 := by
            generalize Classical.choose hex = t
            have ht : (-1 : ZMod 16) ^ t = 1 ∨ (-1 : ZMod 16) ^ t = -1 := by
              rcases Nat.even_or_odd t with ⟨m, rfl⟩ | ⟨m, rfl⟩
              · left; rw [← two_mul, pow_mul]; simp
              · right; rw [pow_succ, pow_mul]; simp
            rcases ht with h | h <;> rw [h] <;> decide
          rw [← ZMod.natCast_mod, hdiv4]; rfl
        · decide
      -- Define Atrunc and Utrunc and map to ZMod 4!
      set Atrunc : PowerSeries ℤ := PowerSeries.mk fun j => if _ : j < N then aSeq j else 0
      set Utrunc : PowerSeries ℤ := PowerSeries.X * Atrunc - 4 * PowerSeries.X * Atrunc ^ 2
      let φ4 := PowerSeries.map (Int.castRingHom (ZMod 4))
      have hA4 : φ4 Atrunc = (PowerSeries.X : PowerSeries (ZMod 4)) := by
        ext j
        rw [PowerSeries.coeff_map, PowerSeries.coeff_X]
        simp only [Atrunc, PowerSeries.coeff_mk]
        split_ifs with hj hj1
        · have := hmod4 j hj; simpa [hj1] using this
        · have := hmod4 j hj; simpa [hj1] using this
        · omega
        · simp
      have hU4 : φ4 Utrunc = (PowerSeries.X : PowerSeries (ZMod 4)) ^ 2 := by
        have hφ4_4 : φ4 4 = 0 := by
          rw [show (4 : PowerSeries ℤ) = PowerSeries.C 4 by simp, PowerSeries.map_C]
          have h40 : (Int.castRingHom (ZMod 4)) 4 = 0 := by decide
          rw [h40, map_zero]
        simp only [Utrunc, map_sub, map_mul, map_pow, hA4, hφ4_4]
        dsimp only [φ4]
        rw [PowerSeries.map_X]
        ring
      -- Hence 4 * coeff N (Atrunc^2) ≡ (if N = 2 then 4 else 0) (mod 16)!
      have hmul4_zmod16 : ∀ z : ℤ, (z : ZMod 4) = 0 → (4 * z : ZMod 16) = 0 := by
        intro z hz
        obtain ⟨q, hq⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd z 4).mp hz
        rw [hq]; push_cast
        have h16 : (4 : ZMod 16) * 4 = 0 := by decide
        rw [← mul_assoc, h16, zero_mul]
      have h4A2 : ((4 * PowerSeries.coeff N (Atrunc ^ 2) : ℤ) : ZMod 16) =
          if N = 2 then 4 else 0 := by
        have hA2_4 : ((PowerSeries.coeff N (Atrunc ^ 2) : ℤ) : ZMod 4) = if N = 2 then 1 else 0 := by
          have hc := congrArg (PowerSeries.coeff N) (show φ4 (Atrunc ^ 2) = PowerSeries.X ^ 2 by
            rw [map_pow, hA4])
          rw [PowerSeries.coeff_map, PowerSeries.coeff_X_pow] at hc
          exact hc
        by_cases hN_eq2 : N = 2
        · rw [if_pos hN_eq2] at hA2_4 ⊢
          have hz : ((PowerSeries.coeff N (Atrunc ^ 2) - 1 : ℤ) : ZMod 4) = 0 := by
            push_cast; rw [hA2_4, sub_self]
          have h0 := hmul4_zmod16 _ hz
          push_cast at h0 ⊢
          linear_combination h0
        · rw [if_neg hN_eq2] at hA2_4 ⊢
          simpa using hmul4_zmod16 _ hA2_4
      -- And for each k : Fin r, (aSeq (k+2) * coeff (N+1) (Utrunc^(k+2)) : ZMod 16) =
      --   if N + 1 = 2 * (k + 2) then aSeq (k+2) else 0!
      have hsum16 : (∑ k : Fin r, ((aSeq (k.1 + 2) * PowerSeries.coeff (N + 1) (Utrunc ^ (k.1 + 2)) : ℤ) : ZMod 16)) =
          if Even (N + 1) ∧ 4 ≤ N + 1 then (aSeq ((N + 1) / 2) : ZMod 16) else 0 := by
        have hterm : ∀ k : Fin r,
            ((aSeq (k.1 + 2) * PowerSeries.coeff (N + 1) (Utrunc ^ (k.1 + 2)) : ℤ) : ZMod 16) =
            if N + 1 = 2 * (k.1 + 2) then (aSeq (k.1 + 2) : ZMod 16) else 0 := by
          intro k
          have h4a : ((4 : ℕ) : ℤ) ∣ aSeq (k.1 + 2) := by
            rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
            have := hmod4 (k.1 + 2) (by omega)
            simpa [show k.1 + 2 ≠ 1 by omega] using this
          obtain ⟨q, hq⟩ := h4a
          have hU_4 : ((PowerSeries.coeff (N + 1) (Utrunc ^ (k.1 + 2)) : ℤ) : ZMod 4) =
              if N + 1 = 2 * (k.1 + 2) then 1 else 0 := by
            have hc := congrArg (PowerSeries.coeff (N + 1)) (show φ4 (Utrunc ^ (k.1 + 2)) =
                PowerSeries.X ^ (2 * (k.1 + 2)) by rw [map_pow, hU4, ← pow_mul])
            rw [PowerSeries.coeff_map, PowerSeries.coeff_X_pow] at hc
            exact hc
          by_cases heq : N + 1 = 2 * (k.1 + 2)
          · rw [if_pos heq] at hU_4 ⊢
            have hz : ((PowerSeries.coeff (N + 1) (Utrunc ^ (k.1 + 2)) - 1 : ℤ) : ZMod 4) = 0 := by
              push_cast; rw [hU_4, sub_self]
            have h0 := hmul4_zmod16 _ hz
            rw [hq]; push_cast at h0 ⊢
            linear_combination (q : ZMod 16) * h0
          · rw [if_neg heq] at hU_4 ⊢
            have h0 := hmul4_zmod16 _ hU_4
            rw [hq]; push_cast at h0 ⊢
            linear_combination (q : ZMod 16) * h0
        simp_rw [hterm]
        by_cases hcond : Even (N + 1) ∧ 4 ≤ N + 1
        · rw [if_pos hcond]
          rcases hcond.1 with ⟨m, hm⟩
          have hm_ge2 : 2 ≤ m := by omega
          have hm_lt : m - 2 < r := by omega
          rw [Finset.sum_eq_single (⟨m - 2, hm_lt⟩ : Fin r)]
          · dsimp only; rw [if_pos (by omega), show (N + 1) / 2 = m by omega, show m - 2 + 2 = m by omega]
          · intro k _ hk
            rw [if_neg]
            intro h
            apply hk; apply Fin.ext; dsimp only; omega
          · intro h; exact absurd (Finset.mem_univ _) h
        · rw [if_neg hcond]
          refine Finset.sum_eq_zero fun k _ => ?_
          rw [if_neg]
          intro h
          exact hcond ⟨⟨k.1 + 2, by omega⟩, by omega⟩
      -- Combine using aSeq definition
      have ha_rec : (aSeq N : ZMod 16) =
          (if N = 2 then 4 else 0) -
          (if Even (N + 1) ∧ 4 ≤ N + 1 then (aSeq ((N + 1) / 2) : ZMod 16) else 0) := by
        have hdef : aSeq N = 4 * PowerSeries.coeff N (Atrunc ^ 2) -
            ∑ k : Fin r, aSeq (k.1 + 2) * PowerSeries.coeff (N + 1) (Utrunc ^ (k.1 + 2)) := by
          conv_lhs => unfold aSeq
        rw [hdef, Int.cast_sub, h4A2, Int.cast_sum, hsum16]
      rw [ha_rec]
      by_cases hN_eq2 : N = 2
      · rw [hN_eq2]
        have hodd3 : ¬ (Even (2 + 1) ∧ 4 ≤ 2 + 1) := by omega
        rw [if_pos rfl, if_neg hodd3, sub_zero]
        have := targetMod16_eq_of_pow2 (n := 2) (j := 0) (by norm_num)
        simpa using this.symm
      · rw [if_neg hN_eq2, zero_sub]
        by_cases hpar : Even (N + 1)
        · have hge4 : 4 ≤ N + 1 := by omega
          rw [if_pos ⟨hpar, hge4⟩]
          set m := (N + 1) / 2
          have hm_lt : m < N := by omega
          have hm_ge2 : 2 ≤ m := by omega
          have hN_eq : N = 2 * m - 1 := by
            rcases hpar with ⟨t, ht⟩; omega
          rw [ih m hm_lt]
          by_cases hex : ∃ j : ℕ, m = 2 ^ j + 1
          · rcases hex with ⟨j, hj⟩
            rw [targetMod16_eq_of_pow2 hj]
            have hNpow : N = 2 ^ (j + 1) + 1 := by
              rw [hN_eq, hj, pow_succ']; omega
            rw [targetMod16_eq_of_pow2 hNpow, pow_succ]
            ring
          · have htm0 : targetMod16 m = 0 := by
              unfold targetMod16
              rw [if_neg (by omega), dif_neg hex]
            have hnotN : ¬ ∃ j : ℕ, N = 2 ^ j + 1 := by
              rintro ⟨j, hj⟩
              cases j with
              | zero => omega
              | succ j' =>
                exact hex ⟨j', by rw [pow_succ'] at hj; omega⟩
            have htN0 : targetMod16 N = 0 := by
              unfold targetMod16
              rw [if_neg (by omega), dif_neg hnotN]
            rw [htm0, htN0, neg_zero]
        · rw [if_neg (fun h => hpar h.1), neg_zero]
          have hnotN : ¬ ∃ j : ℕ, N = 2 ^ j + 1 := by
            rintro ⟨j, hj⟩
            cases j with
            | zero => omega
            | succ j' =>
              apply hpar
              refine ⟨2 ^ j' + 1, ?_⟩
              rw [pow_succ'] at hj; omega
          unfold targetMod16
          rw [if_neg (by omega), dif_neg hnotN]

private theorem prove_disproof : ¬ type_of% @OMA.S_oeis_a396844.main := by
  intro hMain
  obtain ⟨hA0, hA1, hEq⟩ := aSeq_satisfies
  have h17 := hMain (PowerSeries.mk aSeq) hA0 hA1 hEq 17 (by omega)
  have hnot : ¬ ∃ k : ℕ, 17 = 2 * 4 ^ k + 1 := by
    rintro ⟨k, hk⟩
    have h4k : 4 ^ k = 8 := by omega
    cases k with
    | zero => norm_num at h4k
    | succ k' =>
      cases k' with
      | zero => norm_num at h4k
      | succ k'' =>
        have hge : 16 ≤ 4 ^ (k'' + 2) := by
          calc 16 = 4 ^ 2 := by norm_num
            _ ≤ 4 ^ (k'' + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
  have h17d := h17.2 hnot
  rw [PowerSeries.coeff_mk] at h17d
  have h0 : (aSeq 17 : ZMod 16) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd (aSeq 17) 16).mpr h17d
  have h4 : (aSeq 17 : ZMod 16) = 4 := by
    rw [four_dvd_aSeq_of_ge2 17, targetMod16_eq_of_pow2 (n := 17) (j := 4) (by norm_num)]
    decide
  rw [h4] at h0
  exact absurd h0 (by decide)

end OMA.P_oeis_a396844

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a396844.main) :=
  OMA.P_oeis_a396844.prove_disproof
