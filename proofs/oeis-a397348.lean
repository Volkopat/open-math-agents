import OMAStatements.S_oeis_a397348
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace OMA.P_oeis_a397348

open OMA.S_oeis_a397348

private def isPow2 (m : ℕ) : Prop := ∃ k : ℕ, m = 2 ^ k

private lemma not_isPow2_of_odd_gt_one {m : ℕ} (hm : 1 < m) (hodd : m % 2 = 1) : ¬ isPow2 m := by
  rintro ⟨k, rfl⟩
  cases k with
  | zero => omega
  | succ k =>
    have : 2 ^ (k + 1) % 2 = 0 := by rw [pow_succ]; omega
    omega

private lemma odd_iff_zmod2_eq_one (z : ℤ) : Odd z ↔ (z : ZMod 2) = 1 := by
  constructor
  · rintro ⟨k, rfl⟩
    push_cast
    have h2 : (2 : ZMod 2) = 0 := by decide
    rw [h2, zero_mul, zero_add]
  · intro h
    rcases Int.even_or_odd z with ⟨k, rfl⟩ | hodd
    · push_cast at h
      have h2 : (k : ZMod 2) + (k : ZMod 2) = 0 := by
        generalize (k : ZMod 2) = x; revert x; decide
      rw [h2] at h
      exact absurd h (by decide)
    · exact hodd

/-- Auxiliary integer sequence `b n = a n / n` for `n ≥ 1`, defined via the denominator-free
recurrence for `c = 3`. -/
private def bSeq (a : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 =>
    3 * a (n + 1) +
      ∑ k : Fin n,
        (3 * ((k.1 + 2 : ℕ) : ℤ) ^ 2 - 1) * bSeq a (k.1 + 2) * a (n - k.1)

private lemma bSeq_eq_Ico (a : ℕ → ℤ) (n : ℕ) (hn : 2 ≤ n) :
    bSeq a n = 3 * a (n - 1) +
      ∑ k ∈ Finset.Ico 2 n, (3 * (k : ℤ) ^ 2 - 1) * bSeq a k * a (n - k) := by
  rcases Nat.exists_eq_add_of_le hn with ⟨r, rfl⟩
  rw [show 2 + r = r + 2 by omega]
  rw [show r + 2 - 1 = r + 1 by omega]
  conv_lhs => unfold bSeq
  congr 1
  rw [Fin.sum_univ_eq_sum_range (fun k => (3 * ((k + 2 : ℕ) : ℤ) ^ 2 - 1) * bSeq a (k + 2) * a (r - k))]
  refine Finset.sum_bij (fun k _ => k + 2) ?_ ?_ ?_ ?_
  · intro k hk; rw [Finset.mem_range] at hk; rw [Finset.mem_Ico]; omega
  · intro k1 _ k2 _ h; omega
  · intro j hj; rw [Finset.mem_Ico] at hj; exact ⟨j - 2, Finset.mem_range.mpr (by omega), by omega⟩
  · intro k hk; rw [Finset.mem_range] at hk; rw [show r + 2 - (k + 2) = r - k by omega]

private lemma coeff_mul_range_rev {R : Type*} [CommSemiring R] (f g : PowerSeries R) (m : ℕ) :
    PowerSeries.coeff m (f * g) =
      ∑ j ∈ Finset.range (m + 1), PowerSeries.coeff (m - j) f * PowerSeries.coeff j g := by
  rw [PowerSeries.coeff_mul, ← Finset.sum_range_reflect (fun j => PowerSeries.coeff (m - j) f * PowerSeries.coeff j g) (m + 1)]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun x y => PowerSeries.coeff x f * PowerSeries.coeff y g) m]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  rw [show m + 1 - 1 - j = m - j by omega, show m - (m - j) = j by omega]

open Classical in
private lemma sum_pow2_pairs_mod2 (n : ℕ) (hn : 2 ≤ n) :
    (∑ k ∈ Finset.Ico 2 n,
      if isPow2 k ∧ isPow2 (n + 1 - k) then (1 : ZMod 2) else 0) =
      if isPow2 (n + 1) then 1 else 0 := by
  classical
  set S := (Finset.Ico 2 n).filter (fun k => isPow2 k ∧ isPow2 (n + 1 - k))
  have hsumS : (∑ k ∈ Finset.Ico 2 n, if isPow2 k ∧ isPow2 (n + 1 - k) then (1 : ZMod 2) else 0) =
      ∑ _k ∈ S, (1 : ZMod 2) := by
    rw [Finset.sum_filter]
  rw [hsumS]
  set L := S.filter (fun k => k < n + 1 - k)
  set R := S.filter (fun k => n + 1 - k < k)
  set M := S.filter (fun k => k = n + 1 - k)
  have hpart : S = L ∪ (R ∪ M) := by
    ext k
    simp only [L, R, M, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hk
      rcases lt_trichotomy k (n + 1 - k) with h | h | h
      · exact Or.inl ⟨hk, h⟩
      · exact Or.inr (Or.inr ⟨hk, h⟩)
      · exact Or.inr (Or.inl ⟨hk, h⟩)
    · rintro (⟨hk, _⟩ | ⟨hk, _⟩ | ⟨hk, _⟩) <;> exact hk
  have hd1 : Disjoint L (R ∪ M) := by
    rw [Finset.disjoint_left]
    intro k hkL hkRM
    simp only [L, R, M, Finset.mem_union, Finset.mem_filter] at hkL hkRM
    rcases hkRM with ⟨_, h⟩ | ⟨_, h⟩ <;> omega
  have hd2 : Disjoint R M := by
    rw [Finset.disjoint_left]
    intro k hkR hkM
    simp only [R, M, Finset.mem_filter] at hkR hkM
    omega
  have hLR : ∑ _k ∈ L, (1 : ZMod 2) = ∑ _k ∈ R, (1 : ZMod 2) := by
    refine Finset.sum_bij (fun k _ => n + 1 - k) ?_ ?_ ?_ ?_
    · intro k hk
      simp only [L, S, R, Finset.mem_filter, Finset.mem_Ico] at hk ⊢
      rcases hk with ⟨⟨⟨h2, hlt⟩, hp1, hp2⟩, hkl⟩
      refine ⟨⟨⟨by omega, by omega⟩, hp2, ?_⟩, by omega⟩
      rwa [show n + 1 - (n + 1 - k) = k by omega]
    · intro k1 h1 k2 h2 heq
      simp only [L, S, Finset.mem_filter, Finset.mem_Ico] at h1 h2
      omega
    · intro j hj
      simp only [L, S, R, Finset.mem_filter, Finset.mem_Ico] at hj ⊢
      rcases hj with ⟨⟨⟨h2, hlt⟩, hp1, hp2⟩, hjl⟩
      refine ⟨n + 1 - j, ⟨⟨⟨by omega, by omega⟩, hp2, ?_⟩, by omega⟩, by omega⟩
      rwa [show n + 1 - (n + 1 - j) = j by omega]
    · intro _ _; rfl
  have hadd2 : ∀ x : ZMod 2, x + x = 0 := by decide
  rw [hpart, Finset.sum_union hd1, Finset.sum_union hd2, hLR, ← add_assoc, hadd2, zero_add]
  by_cases hp : isPow2 (n + 1)
  · rw [if_pos hp]
    rcases hp with ⟨m, hm⟩
    have hm2 : 2 ≤ m := by
      by_contra hlt
      have : m = 0 ∨ m = 1 := by omega
      rcases this with rfl | rfl <;> omega
    have hM : M = {2 ^ (m - 1)} := by
      ext k
      simp only [M, S, Finset.mem_filter, Finset.mem_Ico, Finset.mem_singleton]
      have h2m : 2 * 2 ^ (m - 1) = n + 1 := by
        rw [hm, ← pow_succ', show m - 1 + 1 = m by omega]
      constructor
      · rintro ⟨⟨⟨_, _⟩, _, _⟩, hkeq⟩
        omega
      · rintro rfl
        have hge2 : 2 ≤ 2 ^ (m - 1) := by
          have h1 : 1 ≤ m - 1 := by omega
          calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ (m - 1) := Nat.pow_le_pow_right (by norm_num) h1
        refine ⟨⟨⟨hge2, by omega⟩, ⟨m - 1, rfl⟩, ?_⟩, by omega⟩
        rw [show n + 1 - 2 ^ (m - 1) = 2 ^ (m - 1) by omega]
        exact ⟨m - 1, rfl⟩
    rw [hM, Finset.sum_singleton]
  · rw [if_neg hp]
    have hM : M = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro k hk
      simp only [M, S, Finset.mem_filter, Finset.mem_Ico] at hk
      rcases hk with ⟨⟨⟨_, _⟩, ⟨r, rfl⟩, _⟩, hkeq⟩
      exact hp ⟨r + 1, by rw [pow_succ']; omega⟩
    rw [hM, Finset.sum_empty]

private theorem prove_main : type_of% @OMA.S_oeis_a397348.main := by
  classical
  intro a hEq
  set A : PowerSeries ℚ := PowerSeries.mk fun n => (a n : ℚ)
  set F : PowerSeries ℚ := PowerSeries.mk fun n =>
    if n = 0 then (0 : ℚ)
    else if n = 1 then (1 : ℚ)
    else ((3 * (n : ℚ) ^ 2 - 1) / (3 * (n : ℚ) ^ 2)) * (a n : ℚ)
  have hF0 : PowerSeries.constantCoeff F = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff]; simp [F]
  have hSub : PowerSeries.HasSubst F := PowerSeries.HasSubst.of_constantCoeff_zero hF0
  -- Step 1: a 0 = 1
  have ha0 : a 0 = 1 := by
    have hc := congrArg (PowerSeries.coeff 0) hEq
    rw [PowerSeries.coeff_subst' hSub] at hc
    have hfin : ∑ᶠ d : ℕ, PowerSeries.coeff d (PowerSeries.exp ℚ) • PowerSeries.coeff 0 (F ^ d) = 1 := by
      rw [finsum_eq_single _ 0]
      · simp
      · intro d hd
        rw [PowerSeries.coeff_zero_eq_constantCoeff, map_pow, hF0, zero_pow hd, smul_zero]
    rw [hfin] at hc
    simp only [A, PowerSeries.coeff_mk] at hc
    exact_mod_cast hc
  -- Step 2: derivative ℚ A = A * derivative ℚ F
  have hderiv : PowerSeries.derivative ℚ A = A * PowerSeries.derivative ℚ F := by
    conv_lhs => rw [hEq]
    rw [PowerSeries.derivative_subst hSub, PowerSeries.derivative_exp, ← hEq]
  -- Step 3: a 1 = 1
  have ha1 : a 1 = 1 := by
    have hc := congrArg (PowerSeries.coeff 0) hderiv
    rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mul, Finset.Nat.antidiagonal_zero,
      Finset.sum_singleton, PowerSeries.coeff_derivative] at hc
    simp only [A, F, PowerSeries.coeff_mk, ha0] at hc
    norm_num at hc
    exact_mod_cast hc
  -- Step 4: For all n ≥ 1, a n = n * bSeq a n
  have ha_eq_nb : ∀ n : ℕ, 1 ≤ n → a n = (n : ℤ) * bSeq a n := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro hn
      cases n with
      | zero => omega
      | succ m =>
        cases m with
        | zero => simp [bSeq, ha1]
        | succ r =>
          -- n = r + 2
          have hc := congrArg (PowerSeries.coeff (r + 1)) hderiv
          rw [PowerSeries.coeff_derivative, coeff_mul_range_rev] at hc
          simp only [A, PowerSeries.coeff_mk] at hc
          -- Split off j = r + 1 (last) and j = 0 (first) from Finset.range (r + 2)
          rw [Finset.sum_range_succ, Finset.sum_range_succ'] at hc
          simp only [Nat.sub_self, Nat.sub_zero, ha0, Int.cast_one, one_mul,
            PowerSeries.coeff_derivative, F, PowerSeries.coeff_mk, Nat.zero_add,
            show r + 1 + 1 ≠ 0 by omega, show r + 1 + 1 ≠ 1 by omega, ↓reduceIte] at hc
          have h1_term : (if (1 : ℕ) = 0 then (0 : ℚ) else 1) * (((0 : ℕ) : ℚ) + 1) = 1 := by norm_num
          rw [h1_term, mul_one] at hc
          -- Simplify middle sum j ∈ range r (corresponding to k = j + 2)
          have hmid : ∑ j ∈ Finset.range r,
              (a (r + 1 - (j + 1)) : ℚ) *
                ((if j + 1 + 1 = 0 then (0 : ℚ) else if j + 1 + 1 = 1 then 1 else
                  (3 * ((j + 1 + 1 : ℕ) : ℚ) ^ 2 - 1) / (3 * ((j + 1 + 1 : ℕ) : ℚ) ^ 2) * (a (j + 1 + 1) : ℚ)) *
                  (((j + 1 : ℕ) : ℚ) + 1)) =
              (1 / 3 : ℚ) *
                ((∑ k : Fin r, (3 * ((k.1 + 2 : ℕ) : ℤ) ^ 2 - 1) * bSeq a (k.1 + 2) * a (r - k.1) : ℤ) : ℚ) := by
            rw [Fin.sum_univ_eq_sum_range (fun k => (3 * ((k + 2 : ℕ) : ℤ) ^ 2 - 1) * bSeq a (k + 2) * a (r - k))]
            push_cast
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun j hj => ?_
            rw [Finset.mem_range] at hj
            have hih : a (j + 2) = ((j + 2 : ℕ) : ℤ) * bSeq a (j + 2) := ih (j + 2) (by omega) (by omega)
            have hihQ : (a (j + 2) : ℚ) = ((j + 2 : ℕ) : ℚ) * (bSeq a (j + 2) : ℚ) := by exact_mod_cast hih
            rw [show j + 1 + 1 = j + 2 by omega, hihQ]
            have hne : ((j : ℚ) + 2) ≠ 0 := by positivity
            rw [show ((j : ℚ) + 1 + 1) = ((j : ℚ) + 2) by ring]
            push_cast
            field_simp [hne]
          rw [hmid] at hc
          have hnr : ((r + 1 + 1 : ℕ) : ℚ) ≠ 0 := by positivity
          have haQ : (a (r + 2) : ℚ) = ((r + 2 : ℕ) : ℚ) * (bSeq a (r + 2) : ℚ) := by
            conv_rhs => unfold bSeq
            push_cast
            rw [show r + 1 + 1 = r + 2 by omega] at hc hnr
            rw [show ((r + 1 : ℕ) : ℚ) + 1 = ((r + 2 : ℕ) : ℚ) by push_cast; ring] at hc
            have hstep : (a (r + 2) : ℚ) * (1 / (3 * ((r + 2 : ℕ) : ℚ))) =
                (1 / 3 : ℚ) * (∑ x : Fin r, (3 * ((x.1 + 2 : ℕ) : ℚ) ^ 2 - 1) * (bSeq a (x.1 + 2) : ℚ) * (a (r - x.1) : ℚ)) +
                  (a (r + 1) : ℚ) := by
              have hdiff : (a (r + 2) : ℚ) * ((r + 2 : ℕ) : ℚ) -
                  (3 * ((r + 2 : ℕ) : ℚ) ^ 2 - 1) / (3 * ((r + 2 : ℕ) : ℚ) ^ 2) * (a (r + 2) : ℚ) * ((r + 2 : ℕ) : ℚ) =
                  (a (r + 2) : ℚ) * (1 / (3 * ((r + 2 : ℕ) : ℚ))) := by
                field_simp [hnr]; ring
              have hsum_cast : ((∑ k : Fin r, (3 * ((k.1 + 2 : ℕ) : ℤ) ^ 2 - 1) * bSeq a (k.1 + 2) * a (r - k.1) : ℤ) : ℚ) =
                  ∑ x : Fin r, (3 * ((x.1 + 2 : ℕ) : ℚ) ^ 2 - 1) * (bSeq a (x.1 + 2) : ℚ) * (a (r - x.1) : ℚ) := by
                push_cast; rfl
              rw [hsum_cast] at hc
              linarith
            have hmul := congrArg (fun t => t * (3 * ((r + 2 : ℕ) : ℚ))) hstep
            have hcancel : (a (r + 2) : ℚ) * (1 / (3 * ((r + 2 : ℕ) : ℚ))) * (3 * ((r + 2 : ℕ) : ℚ)) = (a (r + 2) : ℚ) := by
              field_simp [hnr]
            rw [hcancel] at hmul
            push_cast at hmul ⊢
            linarith
          exact_mod_cast haQ
  -- Step 5: Mod-2 strong induction on (bSeq a n, a n) for n ≥ 1
  have hmod2 : ∀ n : ℕ, 1 ≤ n →
      ((bSeq a n : ℤ) : ZMod 2) = (if isPow2 n ∨ isPow2 (n + 1) then 1 else 0) ∧
      ((a n : ℤ) : ZMod 2) = (if isPow2 (n + 1) then 1 else 0) := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro hn
      cases n with
      | zero => omega
      | succ m =>
        cases m with
        | zero =>
          have hp1 : isPow2 1 := ⟨0, by norm_num⟩
          have hp2 : isPow2 2 := ⟨1, by norm_num⟩
          simp [bSeq, ha1, hp1, hp2]
        | succ r =>
          set N := r + 2
          have hN2 : 2 ≤ N := by omega
          have hbN : ((bSeq a N : ℤ) : ZMod 2) =
              (if isPow2 N ∨ isPow2 (N + 1) then 1 else 0) := by
            rw [bSeq_eq_Ico a N hN2]
            push_cast
            have h3 : (3 : ZMod 2) = 1 := by decide
            rw [(ih (N - 1) (by omega) (by omega)).2, show N - 1 + 1 = N by omega]
            have hsum : (∑ k ∈ Finset.Ico 2 N,
                ((3 : ZMod 2) * (k : ZMod 2) ^ 2 - 1) * ((bSeq a k : ℤ) : ZMod 2) * ((a (N - k) : ℤ) : ZMod 2)) =
                ∑ k ∈ Finset.Ico 2 N, if isPow2 k ∧ isPow2 (N + 1 - k) then (1 : ZMod 2) else 0 := by
              refine Finset.sum_congr rfl fun k hk => ?_
              rw [Finset.mem_Ico] at hk
              rw [h3, one_mul, (ih k hk.2 (by omega)).1, (ih (N - k) (by omega) (by omega)).2]
              rw [show N - k + 1 = N + 1 - k by omega]
              by_cases hk2 : k % 2 = 0
              · have hkZ : (k : ZMod 2) = 0 := by
                  rw [← ZMod.natCast_mod, hk2]; rfl
                rw [hkZ]
                have hneg1 : ((0 : ZMod 2) ^ 2 - 1) = 1 := by decide
                rw [hneg1, one_mul]
                have hnotk1 : ¬ isPow2 (k + 1) := not_isPow2_of_odd_gt_one (by omega) (by omega)
                simp only [hnotk1, or_false]
                split_ifs <;> simp_all
              · have hkZ : (k : ZMod 2) = 1 := by
                  rw [← ZMod.natCast_mod, show k % 2 = 1 by omega]; rfl
                rw [hkZ]
                have h0 : ((1 : ZMod 2) ^ 2 - 1) = 0 := by decide
                rw [h0, zero_mul, zero_mul]
                have hnotk : ¬ isPow2 k := not_isPow2_of_odd_gt_one (by omega) (by omega)
                simp [hnotk]
            rw [hsum, h3, one_mul, sum_pow2_pairs_mod2 N hN2]
            have hdisj : ¬ (isPow2 N ∧ isPow2 (N + 1)) := by
              rintro ⟨h1, h2⟩
              by_cases hpar : N % 2 = 0
              · exact not_isPow2_of_odd_gt_one (by omega) (by omega) h2
              · exact not_isPow2_of_odd_gt_one (by omega) (by omega) h1
            split_ifs <;> simp_all
          refine ⟨hbN, ?_⟩
          rw [ha_eq_nb N (by omega)]
          push_cast
          rw [hbN]
          by_cases hpar : N % 2 = 0
          · have hNZ : (N : ZMod 2) = 0 := by rw [← ZMod.natCast_mod, hpar]; rfl
            have hnotN1 : ¬ isPow2 (N + 1) := not_isPow2_of_odd_gt_one (by omega) (by omega)
            rw [hNZ, zero_mul, if_neg hnotN1]
          · have hNZ : (N : ZMod 2) = 1 := by rw [← ZMod.natCast_mod, show N % 2 = 1 by omega]; rfl
            have hnotN : ¬ isPow2 N := not_isPow2_of_odd_gt_one (by omega) (by omega)
            rw [hNZ, one_mul]; simp only [hnotN, false_or]
  -- Step 6: Conclude for all n : ℕ
  intro n
  cases n with
  | zero =>
    rw [ha0]
    exact ⟨fun _ => ⟨0, by norm_num⟩, fun _ => ⟨0, by norm_num⟩⟩
  | succ m =>
    rw [odd_iff_zmod2_eq_one, (hmod2 (m + 1) (by omega)).2]
    change (if isPow2 (m + 1 + 1) then (1 : ZMod 2) else 0) = 1 ↔ isPow2 (m + 1 + 1)
    split_ifs with h
    · exact ⟨fun _ => h, fun _ => rfl⟩
    · exact ⟨fun h0 => absurd h0 (by decide), fun h' => absurd h' h⟩

end OMA.P_oeis_a397348

theorem OMA.solution : type_of% @OMA.S_oeis_a397348.main :=
  OMA.P_oeis_a397348.prove_main
