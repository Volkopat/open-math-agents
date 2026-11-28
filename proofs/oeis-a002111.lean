import OMAStatements.S_oeis_a002111
import Mathlib

/-!
# Proof of OEIS A002111: Glaisher's G numbers as unsigned numerators of B(2n+1, 1/3)

We prove that for every integer `n ≥ 1`,
`(-1)^(n+1) * 3^(2n+1) * B(2n+1, 1/3) = |(B(2n+1, 1/3)).num|`.

The proof splits into two parts for `m = 2n + 1 ≥ 3`:
1. **Integrality and coprimality to 3**:
   - Using the von Staudt-Clausen theorem (`Bernoulli.vonStaudt_clausen`), `3 * bernoulli k` is
     3-integral for every `k : ℕ`, which implies `(3^m * B_m(1/3) - 1) / 3` is 3-integral.
   - Letting `D = ∏ k < m, (bernoulli k).den = 3^r * Q` with `Nat.Coprime Q 3`, choosing
     `a : ℕ` with `3 * a ≡ 1 (mod Q)`, and comparing `3^m * B_m(a)` (an integer via
     Faulhaber's formula) with `3^m * B_m(1/3)` shows `Q ∣ D * (3^m * B_m(1/3))`.
   - Combining both gives `3^m * B_m(1/3) = g` for an integer `g` with `3 ∣ g - 1`, hence
     `Nat.Coprime g.natAbs (3^m)` and `(B_m(1/3)).num.natAbs = g.natAbs`.
2. **Positivity / sign**:
   - Lifting `Polynomial.bernoulli m` to `ℝ` and using `B_m'(x) = m * B_{m-1}(x)` and
     `B_m(1 - x) = (-1)^m * B_m(x)`, concavity on `(0, 1/2)` gives
     `(-1)^(n+1) * B_{2n+1}(x) > 0` for all `x ∈ (0, 1/2)` by induction on `n ≥ 1`.
   - Evaluating at `x = 1/3` yields `glaisherG n > 0`, identifying `glaisherG n` with
     `g.natAbs = (B_{2n+1}(1/3)).num.natAbs`.
-/

namespace OEIS_A002111

open Finset

private lemma bernoulliPoly_eq_eval (m : ℕ) (x : ℚ) :
    OMA.S_oeis_a002111.bernoulliPoly m x = (Polynomial.bernoulli m).eval x := by
  simp only [OMA.S_oeis_a002111.bernoulliPoly, Polynomial.bernoulli,
    Polynomial.eval_finsetSum, Polynomial.eval_monomial]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

private def M (m : ℕ) : ℚ :=
  (3 : ℚ) ^ m * OMA.S_oeis_a002111.bernoulliPoly m (1 / 3)

private lemma M_eq_sum (m : ℕ) :
    M m = ∑ k ∈ range (m + 1), (Nat.choose m k : ℚ) * bernoulli k * (3 : ℚ) ^ k := by
  simp only [M, OMA.S_oeis_a002111.bernoulliPoly, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkm : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hpow : (3 : ℚ) ^ m * (1 / 3 : ℚ) ^ (m - k) = (3 : ℚ) ^ k := by
    rw [one_div, inv_pow]
    have hsplit : (3 : ℚ) ^ m = (3 : ℚ) ^ k * (3 : ℚ) ^ (m - k) := by
      rw [← pow_add, Nat.add_sub_of_le hkm]
    rw [hsplit, mul_assoc, mul_inv_cancel₀ (by positivity), mul_one]
  calc
    (3 : ℚ) ^ m * ((Nat.choose m k : ℚ) * bernoulli k * (1 / 3 : ℚ) ^ (m - k))
      = (Nat.choose m k : ℚ) * bernoulli k * ((3 : ℚ) ^ m * (1 / 3 : ℚ) ^ (m - k)) := by ring
    _ = (Nat.choose m k : ℚ) * bernoulli k * (3 : ℚ) ^ k := by rw [hpow]

/-! ### Part 1: 3-adic integrality and congruence mod 3 -/

private lemma padicVal3_le_one_of_not_dvd_den (q : ℚ) (h : ¬ 3 ∣ q.den) :
    have : Fact (Nat.Prime 3) := ⟨by decide⟩
    Rat.padicValuation 3 q ≤ 1 := by
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  exact Rat.padicValuation_le_one_iff.mpr h

private lemma padicVal3_le_one_of_two_mul_int (q : ℚ) (z : ℤ) (hz : q = (z : ℚ) / 2) :
    have : Fact (Nat.Prime 3) := ⟨by decide⟩
    Rat.padicValuation 3 q ≤ 1 := by
  refine padicVal3_le_one_of_not_dvd_den q ?_
  have hdiv : q.den ∣ 2 := by
    have hq : q = Rat.divInt z 2 := by
      rw [hz, Rat.divInt_eq_div]
      norm_cast
    rw [hq]
    exact Int.natCast_dvd_natCast.mp (Rat.den_dvd z 2)
  intro h3
  have : 3 ∣ 2 := h3.trans hdiv
  omega

private lemma padicVal3_three_mul_bernoulli (k : ℕ) :
    have : Fact (Nat.Prime 3) := ⟨by decide⟩
    Rat.padicValuation 3 (3 * bernoulli k) ≤ 1 := by
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  rcases k with _ | _ | k
  · rw [bernoulli_zero, mul_one]
    exact Int.padicValuation_le_one 3 3
  · rw [bernoulli_one]
    exact padicVal3_le_one_of_two_mul_int _ (-3) (by norm_num)
  · rcases Nat.even_or_odd (k + 2) with ⟨j, hj⟩ | hodd
    · have hk_eq : k + 2 = 2 * j := by omega
      rw [hk_eq]
      obtain ⟨z, hz⟩ := Bernoulli.vonStaudt_clausen j
      have hsub : 3 * bernoulli (2 * j) =
          (3 * z : ℤ) - ∑ p ∈ (range (2 * j + 2)).filter
            (fun p => p.Prime ∧ (p - 1) ∣ 2 * j), (3 : ℚ) / p := by
        have hz' : bernoulli (2 * j) = (z : ℚ) - ∑ p ∈ (range (2 * j + 2)).filter
            (fun p => p.Prime ∧ (p - 1) ∣ 2 * j), (1 : ℚ) / p := eq_sub_of_add_eq hz.symm
        rw [hz', mul_sub, Finset.mul_sum]
        push_cast
        congr 1
        refine Finset.sum_congr rfl fun p _ => ?_
        ring
      rw [hsub]
      refine (Rat.padicValuation 3).map_sub_le (Int.padicValuation_le_one 3 (3 * z)) ?_
      refine (Rat.padicValuation 3).map_sum_le fun p hp => ?_
      have hp_prime : p.Prime := (Finset.mem_filter.mp hp).2.1
      by_cases hp3 : p = 3
      · subst hp3
        have h1 : (3 : ℚ) / (3 : ℕ) = (1 : ℤ) := by norm_num
        rw [h1]
        exact Int.padicValuation_le_one 3 1
      · refine padicVal3_le_one_of_not_dvd_den _ ?_
        have hdiv : ((3 : ℚ) / (p : ℕ)).den ∣ p := by
          have hq : (3 : ℚ) / (p : ℕ) = Rat.divInt 3 p := by
            simp [Rat.divInt_eq_div]
          rw [hq]
          exact Int.natCast_dvd_natCast.mp (Rat.den_dvd 3 p)
        intro h3dvd
        have h3p : 3 ∣ p := h3dvd.trans hdiv
        exact hp3 ((Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 3) hp_prime).mp h3p).symm
    · rw [bernoulli_eq_zero_of_odd hodd (by omega), mul_zero]
      simp

private lemma padicVal3_M_sub_one_div_three {m : ℕ} (hm : 1 ≤ m) :
    have : Fact (Nat.Prime 3) := ⟨by decide⟩
    Rat.padicValuation 3 ((M m - 1) / 3) ≤ 1 := by
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hdecomp : (M m - 1) / 3 =
      (m : ℚ) * (-1 / 2) +
        ∑ k ∈ Finset.Ico 2 (m + 1),
          (Nat.choose m k : ℚ) * (3 : ℚ) ^ (k - 2) * (3 * bernoulli k) := by
    rw [M_eq_sum]
    have h0 : ∑ k ∈ range (m + 1), (Nat.choose m k : ℚ) * bernoulli k * (3 : ℚ) ^ k =
        1 + ∑ k ∈ Finset.Ico 1 (m + 1), (Nat.choose m k : ℚ) * bernoulli k * (3 : ℚ) ^ k := by
      rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
      simp
    rw [h0, add_sub_cancel_left]
    by_cases hm1 : m = 1
    · subst hm1
      simp
    · have h1 : ∑ k ∈ Finset.Ico 1 (m + 1), (Nat.choose m k : ℚ) * bernoulli k * (3 : ℚ) ^ k =
          (m : ℚ) * (-1 / 2) * 3 +
            ∑ k ∈ Finset.Ico 2 (m + 1), (Nat.choose m k : ℚ) * bernoulli k * (3 : ℚ) ^ k := by
        rw [Finset.sum_eq_sum_Ico_succ_bot (by omega)]
        simp [Nat.choose_one_right, bernoulli_one]
      rw [h1, add_div, mul_div_cancel_right₀ _ (by norm_num : (3 : ℚ) ≠ 0), Finset.sum_div]
      congr 1
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk2 : 2 ≤ k := (Finset.mem_Ico.mp hk).1
      have hpow : (3 : ℚ) ^ k = (3 : ℚ) ^ (k - 2) * 3 * 3 := by
        have hk_eq : k = k - 2 + 1 + 1 := by omega
        conv_lhs => rw [hk_eq, pow_succ, pow_succ]
      rw [hpow]
      ring
  rw [hdecomp]
  refine (Rat.padicValuation 3).map_add_le ?_ ?_
  · exact ((Rat.padicValuation 3).map_mul _ _).trans_le
      (mul_le_one' (by exact_mod_cast Int.padicValuation_le_one 3 m)
        (padicVal3_le_one_of_two_mul_int _ (-1) (by norm_num)))
  · refine (Rat.padicValuation 3).map_sum_le fun k _ => ?_
    have h1 : Rat.padicValuation 3 ((Nat.choose m k : ℚ) * (3 : ℚ) ^ (k - 2)) ≤ 1 := by
      have : ((Nat.choose m k : ℚ) * (3 : ℚ) ^ (k - 2)) =
          ((Nat.choose m k * 3 ^ (k - 2) : ℤ) : ℚ) := by push_cast; rfl
      rw [this]
      exact Int.padicValuation_le_one 3 _
    exact ((Rat.padicValuation 3).map_mul _ _).trans_le
      (mul_le_one' h1 (padicVal3_three_mul_bernoulli k))

private lemma not_three_dvd_M_den {m : ℕ} (hm : 1 ≤ m) : ¬ 3 ∣ (M m).den := by
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  apply Rat.padicValuation_le_one_iff.mp
  have hM : M m = (1 : ℤ) + (3 : ℤ) * ((M m - 1) / 3) := by push_cast; ring
  rw [hM]
  refine (Rat.padicValuation 3).map_add_le (Int.padicValuation_le_one 3 1) ?_
  exact ((Rat.padicValuation 3).map_mul _ _).trans_le
    (mul_le_one' (Int.padicValuation_le_one 3 3) (padicVal3_M_sub_one_div_three hm))

/-! ### Part 2: Integrality of M(2n + 1) and coprimality to 3 -/

private lemma M_is_int_and_not_dvd_three {n : ℕ} (hn : 1 ≤ n) :
    ∃ g : ℤ, M (2 * n + 1) = (g : ℚ) ∧ ¬ (3 : ℤ) ∣ g := by
  set m := 2 * n + 1 with hm_def
  have hm_ge : 3 ≤ m := by omega
  have hm_odd : Odd m := ⟨n, rfl⟩
  have hBm_zero : bernoulli m = 0 := bernoulli_eq_zero_of_odd hm_odd (by omega)
  set D : ℕ := ∏ k ∈ range m, (bernoulli k).den
  have hD_pos : 0 < D := Finset.prod_pos fun k _ => (bernoulli k).den_pos
  have hD_ne : D ≠ 0 := hD_pos.ne'
  set r : ℕ := D.factorization 3
  set Q : ℕ := D / 3 ^ r
  have hDrQ : 3 ^ r * Q = D := Nat.ordProj_mul_ordCompl_eq_self D 3
  have hQ_pos : 0 < Q := Nat.pos_of_ne_zero fun hQ0 => by
    rw [hQ0, mul_zero] at hDrQ
    exact hD_ne hDrQ.symm
  have h3Q_cop : Nat.Coprime 3 Q := Nat.coprime_ordCompl (by decide : Nat.Prime 3) hD_ne
  -- Find a : ℕ with (Q : ℤ) ∣ 3 * a - 1
  set a : ℕ := ((Nat.gcdA 3 Q) % (Q : ℤ)).toNat
  have ha_cast : (a : ℤ) = (Nat.gcdA 3 Q) % (Q : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by positivity))
  have hQ_dvd_3a : (Q : ℤ) ∣ (3 * (a : ℤ) - 1) := by
    have hbez : (1 : ℤ) = 3 * Nat.gcdA 3 Q + Q * Nat.gcdB 3 Q := by
      have hg := Nat.gcd_eq_gcd_ab 3 Q
      rw [h3Q_cop.gcd_eq_one] at hg
      exact_mod_cast hg
    have hmod : (Nat.gcdA 3 Q) % (Q : ℤ) = Nat.gcdA 3 Q - (Q : ℤ) * ((Nat.gcdA 3 Q) / (Q : ℤ)) := by
      linarith [Int.mul_ediv_add_emod (Nat.gcdA 3 Q) (Q : ℤ)]
    refine ⟨-Nat.gcdB 3 Q - 3 * ((Nat.gcdA 3 Q) / (Q : ℤ)), ?_⟩
    rw [ha_cast, hmod]
    linarith
  -- Integer coefficients c k = D * bernoulli k
  let c : ℕ → ℤ := fun k => (bernoulli k).num * ((D / (bernoulli k).den : ℕ) : ℤ)
  have hc_eq : ∀ k ∈ range m, ((c k : ℤ) : ℚ) = (D : ℚ) * bernoulli k := by
    intro k hk
    have hdvd : (bernoulli k).den ∣ D := Finset.dvd_prod_of_mem _ hk
    have hdiv : ((D / (bernoulli k).den : ℕ) : ℚ) * ((bernoulli k).den : ℚ) = (D : ℚ) := by
      exact_mod_cast Nat.div_mul_cancel hdvd
    have hden_ne : ((bernoulli k).den : ℚ) ≠ 0 := by positivity
    have hnum : ((bernoulli k).num : ℚ) = bernoulli k * ((bernoulli k).den : ℚ) :=
      (div_eq_iff hden_ne).mp (Rat.num_div_den (bernoulli k))
    dsimp [c]
    push_cast
    rw [hnum]
    calc
      bernoulli k * ((bernoulli k).den : ℚ) * ((D / (bernoulli k).den : ℕ) : ℚ)
        = bernoulli k * (((D / (bernoulli k).den : ℕ) : ℚ) * ((bernoulli k).den : ℚ)) := by ring
      _ = (D : ℚ) * bernoulli k := by rw [hdiv]; ring
  -- Express M m and 3^m * B_m(a) via range m (since bernoulli m = 0)
  have hM_range : M m = ∑ k ∈ range m, (Nat.choose m k : ℚ) * bernoulli k * (3 : ℚ) ^ k := by
    rw [M_eq_sum, Finset.sum_range_succ, hBm_zero, mul_zero, zero_mul, add_zero]
  set S_int : ℤ := ∑ k ∈ range m, (Nat.choose m k : ℤ) * c k * (3 : ℤ) ^ k
  have hS_int : (S_int : ℚ) = (D : ℚ) * M m := by
    rw [hM_range, Finset.mul_sum]
    push_cast [S_int]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [hc_eq k hk]
    ring
  set I_int : ℤ := (3 : ℤ) ^ m * ((m : ℤ) * ∑ j ∈ range a, (j : ℤ) ^ (m - 1))
  have hI_int : (I_int : ℚ) =
      ∑ k ∈ range m, (Nat.choose m k : ℚ) * bernoulli k * (3 : ℚ) ^ k * (3 * (a : ℚ)) ^ (m - k) := by
    have hfaul := Polynomial.sum_range_pow_eq_bernoulli_sub a (m - 1)
    have hm_succ : (m - 1).succ = m := by omega
    rw [hm_succ, hBm_zero, sub_zero, ← bernoulliPoly_eq_eval] at hfaul
    have hfaul' : ((m : ℚ) * ∑ j ∈ range a, (j : ℚ) ^ (m - 1)) =
        OMA.S_oeis_a002111.bernoulliPoly m (a : ℚ) := by
      have : ((m - 1 : ℕ) : ℚ) + 1 = (m : ℚ) := by
        exact_mod_cast hm_succ
      rwa [this] at hfaul
    have hcast_I : (I_int : ℚ) = (3 : ℚ) ^ m * ((m : ℚ) * ∑ j ∈ range a, (j : ℚ) ^ (m - 1)) := by
      push_cast [I_int]
      rfl
    rw [hcast_I, hfaul', OMA.S_oeis_a002111.bernoulliPoly, Finset.mul_sum,
      Finset.sum_range_succ, hBm_zero, mul_zero, zero_mul, mul_zero, add_zero]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkm : k ≤ m := (Finset.mem_range.mp hk).le
    have hpow : (3 : ℚ) ^ m * (a : ℚ) ^ (m - k) = (3 : ℚ) ^ k * (3 * (a : ℚ)) ^ (m - k) := by
      rw [mul_pow, ← mul_assoc, ← pow_add, Nat.add_sub_of_le hkm]
    calc
      (3 : ℚ) ^ m * ((Nat.choose m k : ℚ) * bernoulli k * (a : ℚ) ^ (m - k))
        = (Nat.choose m k : ℚ) * bernoulli k * ((3 : ℚ) ^ m * (a : ℚ) ^ (m - k)) := by ring
      _ = (Nat.choose m k : ℚ) * bernoulli k * ((3 : ℚ) ^ k * (3 * (a : ℚ)) ^ (m - k)) := by
          rw [hpow]
      _ = (Nat.choose m k : ℚ) * bernoulli k * (3 : ℚ) ^ k * (3 * (a : ℚ)) ^ (m - k) := by ring
  -- Compare (D : ℤ) * I_int - S_int
  have hdiff_eq : (D : ℤ) * I_int - S_int =
      ∑ k ∈ range m, (Nat.choose m k : ℤ) * c k * (3 : ℤ) ^ k * ((3 * (a : ℤ)) ^ (m - k) - 1) := by
    apply Int.cast_injective (α := ℚ)
    push_cast
    rw [hI_int, hS_int, hM_range, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [hc_eq k hk]
    ring
  have hQ_dvd_diff : (Q : ℤ) ∣ ((D : ℤ) * I_int - S_int) := by
    rw [hdiff_eq]
    refine Finset.dvd_sum fun k _ => ?_
    exact dvd_mul_of_dvd_right (hQ_dvd_3a.trans (sub_one_dvd_pow_sub_one _ _)) _
  have hQ_dvd_D : (Q : ℤ) ∣ (D : ℤ) := by
    refine ⟨(3 : ℤ) ^ r, ?_⟩
    exact_mod_cast hDrQ.symm.trans (mul_comm _ _)
  have hQ_dvd_S : (Q : ℤ) ∣ S_int := by
    have h1 := dvd_sub (dvd_mul_of_dvd_left hQ_dvd_D I_int) hQ_dvd_diff
    rwa [sub_sub_cancel] at h1
  obtain ⟨t, ht⟩ := hQ_dvd_S
  have hM_div : M m = (t : ℚ) / ((3 ^ r : ℕ) : ℚ) := by
    have hQ_ne : (Q : ℚ) ≠ 0 := by positivity
    have h3r_ne : ((3 ^ r : ℕ) : ℚ) ≠ 0 := by positivity
    have hD_eq : (D : ℚ) = ((3 ^ r : ℕ) : ℚ) * (Q : ℚ) := by exact_mod_cast hDrQ.symm
    have hEq : ((3 ^ r : ℕ) : ℚ) * (Q : ℚ) * M m = (Q : ℚ) * (t : ℚ) := by
      rw [← hD_eq, ← hS_int, ht]
      push_cast
      rfl
    have hEq2 : ((3 ^ r : ℕ) : ℚ) * M m = (t : ℚ) := by
      apply mul_left_cancel₀ hQ_ne
      linarith
    exact eq_div_of_mul_eq h3r_ne (by linarith)
  have hden_dvd : (M m).den ∣ 3 ^ r := by
    have hq : M m = Rat.divInt t (3 ^ r : ℕ) := by
      rw [hM_div, Rat.divInt_eq_div]
      norm_cast
    rw [hq]
    exact Int.natCast_dvd_natCast.mp (Rat.den_dvd t (3 ^ r : ℕ))
  have hden_one : (M m).den = 1 := by
    by_contra hne
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
    have hp3 : p = 3 :=
      (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3)).mp
        (hp.dvd_of_dvd_pow (hpdvd.trans hden_dvd))
    subst hp3
    exact not_three_dvd_M_den (by omega) hpdvd
  refine ⟨(M m).num, ?_, ?_⟩
  · exact (Rat.coe_int_num_of_den_eq_one hden_one).symm
  · intro h3dvd
    have : Fact (Nat.Prime 3) := ⟨by decide⟩
    have hval := padicVal3_M_sub_one_div_three (m := m) (by omega)
    have hnotdvd : ¬ 3 ∣ ((M m - 1) / 3).den := Rat.padicValuation_le_one_iff.mp hval
    set g := (M m).num
    have hMq : M m = (g : ℚ) := (Rat.coe_int_num_of_den_eq_one hden_one).symm
    set q := (M m - 1) / 3
    have hq_eq : 3 * q = ((g - 1 : ℤ) : ℚ) := by
      dsimp [q]
      rw [hMq]
      push_cast
      ring
    have hq_num : 3 * (q.num : ℚ) = ((g - 1 : ℤ) : ℚ) * (q.den : ℚ) := by
      have hden_ne : (q.den : ℚ) ≠ 0 := by positivity
      have hnum_q : (q.num : ℚ) = q * (q.den : ℚ) := (div_eq_iff hden_ne).mp (Rat.num_div_den q)
      calc
        3 * (q.num : ℚ) = 3 * (q * (q.den : ℚ)) := by rw [hnum_q]
        _ = (3 * q) * (q.den : ℚ) := by ring
        _ = ((g - 1 : ℤ) : ℚ) * (q.den : ℚ) := by rw [hq_eq]
    have hq_int : (3 : ℤ) * q.num = (g - 1) * (q.den : ℤ) := by
      exact_mod_cast hq_num
    have h3_dvd_prod : (3 : ℤ) ∣ (g - 1) * (q.den : ℤ) := ⟨q.num, hq_int.symm⟩
    have h3_not_den : ¬ (3 : ℤ) ∣ (q.den : ℤ) := by
      intro h
      exact hnotdvd (Int.natCast_dvd_natCast.mp h)
    have h3_prime_int : Prime (3 : ℤ) := Int.prime_iff_natAbs_prime.mpr (by decide)
    have h3_dvd_sub : (3 : ℤ) ∣ (g - 1) :=
      (h3_prime_int.dvd_or_dvd h3_dvd_prod).resolve_right h3_not_den
    have h3_dvd_one : (3 : ℤ) ∣ 1 := by
      have := dvd_sub h3dvd h3_dvd_sub
      rwa [sub_sub_cancel] at this
    omega

/-! ### Part 3: Sign of B(2n + 1, 1/3) via concavity on (0, 1/2) -/

private noncomputable def B_R (m : ℕ) (x : ℝ) : ℝ :=
  ((Polynomial.bernoulli m).map (algebraMap ℚ ℝ)).eval x

private lemma B_R_rat (m : ℕ) (x : ℚ) :
    B_R m (x : ℝ) = (OMA.S_oeis_a002111.bernoulliPoly m x : ℝ) := by
  rw [B_R, bernoulliPoly_eq_eval]
  simpa using Polynomial.eval_map_apply (algebraMap ℚ ℝ) x (p := Polynomial.bernoulli m)

private lemma hasDerivAt_B_R (m : ℕ) (x : ℝ) :
    HasDerivAt (B_R (m + 1)) (((m + 1 : ℕ) : ℝ) * B_R m x) x := by
  have hd := ((Polynomial.bernoulli (m + 1)).map (algebraMap ℚ ℝ)).hasDerivAt x
  have hder : ((Polynomial.bernoulli (m + 1)).map (algebraMap ℚ ℝ)).derivative =
      Polynomial.C (((m + 1 : ℕ) : ℝ)) * (Polynomial.bernoulli m).map (algebraMap ℚ ℝ) := by
    rw [Polynomial.derivative_map, Polynomial.derivative_bernoulli_add_one,
      Polynomial.map_mul, Polynomial.map_add, Polynomial.map_natCast, Polynomial.map_one]
    simp
  rw [hder, Polynomial.eval_mul, Polynomial.eval_C] at hd
  exact hd

private lemma B_R_one_sub (m : ℕ) (x : ℝ) :
    B_R m (1 - x) = (-1 : ℝ) ^ m * B_R m x := by
  have hcomp := congr_arg (Polynomial.map (algebraMap ℚ ℝ)) (Polynomial.bernoulli_comp_one_sub_X m)
  rw [Polynomial.map_comp, Polynomial.map_sub, Polynomial.map_one, Polynomial.map_X,
    Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_neg, Polynomial.map_one] at hcomp
  have hev := congr_arg (Polynomial.eval x) hcomp
  simpa [B_R, Polynomial.eval_comp] using hev

private lemma B_R_odd_zero {n : ℕ} (hn : 1 ≤ n) : B_R (2 * n + 1) 0 = 0 := by
  have h0 := B_R_rat (2 * n + 1) 0
  rw [Rat.cast_zero, bernoulliPoly_eq_eval, Polynomial.bernoulli_eval_zero,
    bernoulli_eq_zero_of_odd ⟨n, rfl⟩ (by omega), Rat.cast_zero] at h0
  exact h0

private lemma B_R_odd_half {n : ℕ} : B_R (2 * n + 1) (1 / 2) = 0 := by
  have h := B_R_one_sub (2 * n + 1) (1 / 2)
  have hpow : (-1 : ℝ) ^ (2 * n + 1) = -1 := Odd.neg_one_pow ⟨n, rfl⟩
  rw [hpow] at h
  linarith

private lemma B_R_three (x : ℝ) :
    B_R 3 x = x * (1 / 2 - x) * (1 - x) := by
  have h3 : Polynomial.bernoulli 3 =
      Polynomial.X ^ 3 - Polynomial.C (3 / 2 : ℚ) * Polynomial.X ^ 2 +
        Polynomial.C (1 / 2 : ℚ) * Polynomial.X := by
    simp only [Polynomial.bernoulli, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    have hb3 : bernoulli 3 = 0 := bernoulli_eq_zero_of_odd ⟨1, rfl⟩ (by decide)
    simp only [bernoulli_zero, bernoulli_one, bernoulli_two, hb3]
    norm_num [Nat.choose]
    ext k
    simp [Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_monomial]
    rcases k with _ | _ | _ | _ | k <;> simp
  rw [B_R, h3]
  simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_C, Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
  norm_num
  ring

private lemma sign_B_R_odd :
    ∀ n : ℕ, 1 ≤ n → ∀ x ∈ Set.Ioo (0 : ℝ) (1 / 2),
      0 < (-1 : ℝ) ^ (n + 1) * B_R (2 * n + 1) x := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    intro x hx
    rw [B_R_three]
    have hx0 : 0 < x := hx.1
    have hx1 : x < 1 / 2 := hx.2
    have hpow : (-1 : ℝ) ^ (1 + 1) = 1 := by norm_num
    rw [hpow, one_mul]
    exact mul_pos (mul_pos hx0 (by linarith)) (by linarith)
  | succ k hk ih =>
    intro x hx
    let f : ℝ → ℝ := fun t => (-1 : ℝ) ^ (k + 2) * B_R (2 * k + 3) t
    let g : ℝ → ℝ := fun t => ((2 * k + 3 : ℕ) : ℝ) * ((-1 : ℝ) ^ (k + 2) * B_R (2 * k + 2) t)
    have hf_deriv : ∀ t : ℝ, HasDerivAt f (g t) t := fun t => by
      have hd := (hasDerivAt_B_R (2 * k + 2) t).const_mul ((-1 : ℝ) ^ (k + 2))
      exact hd.congr_deriv (by dsimp [g]; ring)
    have hg_deriv : ∀ t : ℝ, HasDerivAt g
        (-(((2 * k + 3 : ℕ) : ℝ) * ((2 * k + 2 : ℕ) : ℝ) *
          ((-1 : ℝ) ^ (k + 1) * B_R (2 * k + 1) t))) t := fun t => by
      have hd := ((hasDerivAt_B_R (2 * k + 1) t).const_mul ((-1 : ℝ) ^ (k + 2))).const_mul
        ((2 * k + 3 : ℕ) : ℝ)
      refine hd.congr_deriv ?_
      rw [show k + 2 = (k + 1) + 1 from rfl, pow_succ]
      ring
    have hg_cont : Continuous g :=
      continuous_iff_continuousAt.mpr fun t => (hg_deriv t).continuousAt
    have hf_cont : Continuous f :=
      continuous_iff_continuousAt.mpr fun t => (hf_deriv t).continuousAt
    have hg_anti : StrictAntiOn g (Set.Icc (0 : ℝ) (1 / 2)) := by
      refine strictAntiOn_of_deriv_neg (convex_Icc 0 (1 / 2)) hg_cont.continuousOn ?_
      intro t ht
      rw [interior_Icc] at ht
      rw [(hg_deriv t).deriv]
      have hpos := ih t ht
      have hc1 : (0 : ℝ) < ((2 * k + 3 : ℕ) : ℝ) := by positivity
      have hc2 : (0 : ℝ) < ((2 * k + 2 : ℕ) : ℝ) := by positivity
      exact neg_neg_of_pos (mul_pos (mul_pos hc1 hc2) hpos)
    have hf0 : f 0 = 0 := by
      dsimp [f]
      rw [show 2 * k + 3 = 2 * (k + 1) + 1 by omega, B_R_odd_zero (by omega), mul_zero]
    have hf_half : f (1 / 2) = 0 := by
      dsimp [f]
      rw [show 2 * k + 3 = 2 * (k + 1) + 1 by omega, B_R_odd_half, mul_zero]
    change 0 < (-1 : ℝ) ^ (k + 1 + 1) * B_R (2 * (k + 1) + 1) x
    have hgoal : (-1 : ℝ) ^ (k + 1 + 1) * B_R (2 * (k + 1) + 1) x = f x := by
      dsimp [f]
      congr 2
    rw [hgoal]
    by_contra hle
    have hle' : f x ≤ 0 := not_lt.mp hle
    obtain ⟨c1, hc1, hslope1⟩ := exists_hasDerivAt_eq_slope f g hx.1
      hf_cont.continuousOn (fun t _ => hf_deriv t)
    obtain ⟨c2, hc2, hslope2⟩ := exists_hasDerivAt_eq_slope f g hx.2
      hf_cont.continuousOn (fun t _ => hf_deriv t)
    have hgc1 : g c1 ≤ 0 := by
      rw [hslope1, hf0, sub_zero, sub_zero]
      exact div_nonpos_of_nonpos_of_nonneg hle' hx.1.le
    have hgc2 : 0 ≤ g c2 := by
      rw [hslope2, hf_half, zero_sub]
      exact div_nonneg (neg_nonneg.mpr hle') (sub_nonneg.mpr hx.2.le)
    have hlt : g c2 < g c1 :=
      hg_anti ⟨hc1.1.le, hc1.2.le.trans hx.2.le⟩ ⟨hx.1.le.trans hc2.1.le, hc2.2.le⟩
        (hc1.2.trans hc2.1)
    linarith

private lemma pos_glaisherG {n : ℕ} (hn : 1 ≤ n) :
    0 < OMA.S_oeis_a002111.glaisherG n := by
  have h13 : (1 / 3 : ℝ) ∈ Set.Ioo (0 : ℝ) (1 / 2) := by constructor <;> norm_num
  have hposR : 0 < (-1 : ℝ) ^ (n + 1) * B_R (2 * n + 1) (1 / 3) := sign_B_R_odd n hn (1 / 3) h13
  have hcast : (1 / 3 : ℝ) = ((1 / 3 : ℚ) : ℝ) := by norm_num
  rw [hcast, B_R_rat] at hposR
  have hposQ : 0 < (-1 : ℚ) ^ (n + 1) * OMA.S_oeis_a002111.bernoulliPoly (2 * n + 1) (1 / 3) := by
    have : (0 : ℝ) < (((-1 : ℚ) ^ (n + 1) *
        OMA.S_oeis_a002111.bernoulliPoly (2 * n + 1) (1 / 3) : ℚ) : ℝ) := by
      push_cast
      exact hposR
    exact Rat.cast_pos.mp this
  rw [OMA.S_oeis_a002111.glaisherG, mul_right_comm]
  exact mul_pos hposQ (by positivity)

end OEIS_A002111

theorem OMA.solution : type_of% @OMA.S_oeis_a002111.main := by
  intro n hn
  set m := 2 * n + 1
  set q := OMA.S_oeis_a002111.bernoulliPoly m (1 / 3)
  obtain ⟨g, hg_eq, hg_not_dvd⟩ := OEIS_A002111.M_is_int_and_not_dvd_three hn
  have h3_ne : (3 : ℚ) ^ m ≠ 0 := by positivity
  have hq_mul : (3 : ℚ) ^ m * q = (g : ℚ) := hg_eq
  -- Deduce q.num.natAbs = g.natAbs via coprimality
  have hcross_rat : (q.num : ℚ) * ((3 ^ m : ℕ) : ℚ) = (g : ℚ) * (q.den : ℚ) := by
    have hden_ne : (q.den : ℚ) ≠ 0 := by positivity
    have hnum_q : (q.num : ℚ) = q * (q.den : ℚ) := (div_eq_iff hden_ne).mp (Rat.num_div_den q)
    calc
      (q.num : ℚ) * ((3 ^ m : ℕ) : ℚ) = (q * (q.den : ℚ)) * (3 : ℚ) ^ m := by
        rw [hnum_q]
        norm_cast
      _ = ((3 : ℚ) ^ m * q) * (q.den : ℚ) := by ring
      _ = (g : ℚ) * (q.den : ℚ) := by rw [hq_mul]
  have hcross_int : q.num * ((3 ^ m : ℕ) : ℤ) = g * (q.den : ℤ) := by
    exact_mod_cast hcross_rat
  have hcross_nat : q.num.natAbs * 3 ^ m = g.natAbs * q.den := by
    have := congr_arg Int.natAbs hcross_int
    simpa [Int.natAbs_mul] using this
  have hcop_g3 : Nat.Coprime g.natAbs 3 := by
    refine ((Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 3)).mpr ?_).symm
    intro h3
    exact hg_not_dvd (Int.natCast_dvd.mpr h3)
  have hcop_g3m : Nat.Coprime g.natAbs (3 ^ m) := hcop_g3.pow_right m
  have hden_dvd_3m : q.den ∣ 3 ^ m := by
    have hdvd : q.den ∣ q.num.natAbs * 3 ^ m := ⟨g.natAbs, by linarith⟩
    exact q.reduced.symm.dvd_of_dvd_mul_left hdvd
  have h3m_dvd_den : 3 ^ m ∣ q.den := by
    have hdvd : 3 ^ m ∣ g.natAbs * q.den := ⟨q.num.natAbs, by linarith⟩
    exact hcop_g3m.symm.dvd_of_dvd_mul_left hdvd
  have hden_eq : q.den = 3 ^ m := Nat.dvd_antisymm hden_dvd_3m h3m_dvd_den
  have hnum_abs : q.num.natAbs = g.natAbs := by
    rw [hden_eq] at hcross_nat
    exact Nat.eq_of_mul_eq_mul_right (by positivity) hcross_nat
  -- Combine with positivity of glaisherG n
  have hG_eq : OMA.S_oeis_a002111.glaisherG n = (((-1 : ℤ) ^ (n + 1) * g : ℤ) : ℚ) := by
    rw [OMA.S_oeis_a002111.glaisherG, mul_assoc]
    change (-1 : ℚ) ^ (n + 1) * ((3 : ℚ) ^ m * q) = _
    rw [hq_mul]
    push_cast
    rfl
  have hG_pos : (0 : ℤ) < (-1 : ℤ) ^ (n + 1) * g := by
    have hpos := OEIS_A002111.pos_glaisherG hn
    rw [hG_eq] at hpos
    exact_mod_cast hpos
  have habs_eq : ((-1 : ℤ) ^ (n + 1) * g : ℤ) = (g.natAbs : ℤ) := by
    have hnat : ((-1 : ℤ) ^ (n + 1) * g).natAbs = g.natAbs := by
      rw [Int.natAbs_mul, Int.natAbs_pow, show Int.natAbs (-1 : ℤ) = 1 from rfl, one_pow, one_mul]
    rw [← hnat, Int.natAbs_of_nonneg hG_pos.le]
  rw [hG_eq, habs_eq, ← hnum_abs]
  exact Int.cast_natCast q.num.natAbs
