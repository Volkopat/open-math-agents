import OMAStatements.S_oeis_a370097

-- Problem: A370097: a(n) = Sum_{k=0..n} binomial(3*n,k) * binomial(3*n-k-1,n-k).
-- Upstream: formal-conjectures statements/oeis-a370097.lean:0 (declaration OMA.S_oeis_a370097.main)
-- Credit: @smorshenniygus (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace A370097Proof

open Polynomial Finset

/-! ### Section 1: p-adic divisibility in ℚ -/

private def IsPDvdZ (p K : ℕ) (q : ℚ) : Prop :=
  ∃ N D : ℤ, ¬ (p : ℤ) ∣ D ∧ ((p ^ K : ℕ) : ℤ) ∣ N ∧ q = (N : ℚ) / (D : ℚ)

private lemma int_ne_zero_of_not_dvd {p : ℕ} {D : ℤ} (hD : ¬ (p : ℤ) ∣ D) : D ≠ 0 := by
  intro h0
  exact hD (h0 ▸ dvd_zero _)

private lemma rat_ne_zero_of_not_dvd {p : ℕ} {D : ℤ} (hD : ¬ (p : ℤ) ∣ D) : (D : ℚ) ≠ 0 :=
  Int.cast_ne_zero.mpr (int_ne_zero_of_not_dvd hD)

private lemma not_dvd_one_int {p : ℕ} (hp : p.Prime) : ¬ (p : ℤ) ∣ (1 : ℤ) :=
  fun h => hp.not_dvd_one (Int.ofNat_dvd.mp h)

private lemma isPDvdZ_zero {p K : ℕ} (hp : p.Prime) : IsPDvdZ p K 0 :=
  ⟨0, 1, not_dvd_one_int hp, dvd_zero _, by simp⟩

private lemma isPDvdZ_mono {p K1 K2 : ℕ} {q : ℚ} (hle : K1 ≤ K2) (h : IsPDvdZ p K2 q) :
    IsPDvdZ p K1 q := by
  rcases h with ⟨N, D, hD, hN, hq⟩
  exact ⟨N, D, hD, dvd_trans (Int.ofNat_dvd.mpr (Nat.pow_dvd_pow p hle)) hN, hq⟩

private lemma isPDvdZ_neg {p K : ℕ} {q : ℚ} (h : IsPDvdZ p K q) : IsPDvdZ p K (-q) := by
  rcases h with ⟨N, D, hD, hN, rfl⟩
  refine ⟨-N, D, hD, dvd_neg.mpr hN, ?_⟩
  push_cast
  ring

private lemma isPDvdZ_add {p K : ℕ} (hp : p.Prime) {q1 q2 : ℚ}
    (h1 : IsPDvdZ p K q1) (h2 : IsPDvdZ p K q2) : IsPDvdZ p K (q1 + q2) := by
  rcases h1 with ⟨N1, D1, hD1, hN1, rfl⟩
  rcases h2 with ⟨N2, D2, hD2, hN2, rfl⟩
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hD12 : ¬ (p : ℤ) ∣ D1 * D2 := fun h => (hpZ.dvd_or_dvd h).elim hD1 hD2
  have h1ne : (D1 : ℚ) ≠ 0 := rat_ne_zero_of_not_dvd hD1
  have h2ne : (D2 : ℚ) ≠ 0 := rat_ne_zero_of_not_dvd hD2
  refine ⟨N1 * D2 + N2 * D1, D1 * D2, hD12,
    dvd_add (dvd_mul_of_dvd_left hN1 D2) (dvd_mul_of_dvd_left hN2 D1), ?_⟩
  push_cast
  field_simp

private lemma isPDvdZ_sub {p K : ℕ} (hp : p.Prime) {q1 q2 : ℚ}
    (h1 : IsPDvdZ p K q1) (h2 : IsPDvdZ p K q2) : IsPDvdZ p K (q1 - q2) := by
  rw [sub_eq_add_neg]
  exact isPDvdZ_add hp h1 (isPDvdZ_neg h2)

private lemma isPDvdZ_sum {ι : Type*} {p K : ℕ} (hp : p.Prime) (s : Finset ι) (f : ι → ℚ)
    (hf : ∀ i ∈ s, IsPDvdZ p K (f i)) : IsPDvdZ p K (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isPDvdZ_zero hp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact isPDvdZ_add hp (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

private lemma isPDvdZ_mul {p K1 K2 : ℕ} (hp : p.Prime) {q1 q2 : ℚ}
    (h1 : IsPDvdZ p K1 q1) (h2 : IsPDvdZ p K2 q2) : IsPDvdZ p (K1 + K2) (q1 * q2) := by
  rcases h1 with ⟨N1, D1, hD1, hN1, rfl⟩
  rcases h2 with ⟨N2, D2, hD2, hN2, rfl⟩
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hD12 : ¬ (p : ℤ) ∣ D1 * D2 := fun h => (hpZ.dvd_or_dvd h).elim hD1 hD2
  have hN12 : ((p ^ (K1 + K2) : ℕ) : ℤ) ∣ N1 * N2 := by
    rw [pow_add, Nat.cast_mul]
    exact mul_dvd_mul hN1 hN2
  refine ⟨N1 * N2, D1 * D2, hD12, hN12, ?_⟩
  push_cast
  ring

private lemma isPDvdZ_intCast {p K : ℕ} (hp : p.Prime) (n : ℤ)
    (hn : ((p ^ K : ℕ) : ℤ) ∣ n) : IsPDvdZ p K (n : ℚ) :=
  ⟨n, 1, not_dvd_one_int hp, hn, by simp⟩

private lemma isPDvdZ_intCast_zero {p : ℕ} (hp : p.Prime) (n : ℤ) : IsPDvdZ p 0 (n : ℚ) :=
  isPDvdZ_intCast hp n (by simp)

private lemma isPDvdZ_natCast {p K : ℕ} (hp : p.Prime) (n : ℕ)
    (hn : p ^ K ∣ n) : IsPDvdZ p K (n : ℚ) :=
  ⟨(n : ℤ), 1, not_dvd_one_int hp, Int.ofNat_dvd.mpr hn, by simp⟩

private lemma isPDvdZ_natCast_zero {p : ℕ} (hp : p.Prime) (n : ℕ) : IsPDvdZ p 0 (n : ℚ) :=
  isPDvdZ_natCast hp n (by simp)

private lemma isPDvdZ_pow {p K : ℕ} (hp : p.Prime) {q : ℚ} (h : IsPDvdZ p K q) (m : ℕ) :
    IsPDvdZ p (m * K) (q ^ m) := by
  induction m with
  | zero =>
    simpa using isPDvdZ_natCast_zero hp 1
  | succ m ih =>
    rw [pow_succ, Nat.succ_mul]
    exact isPDvdZ_mul hp ih h

private lemma isPDvdZ_div_nat {p K d : ℕ} (hp : p.Prime) (hd : d ≠ 0) {q : ℚ}
    (hq : IsPDvdZ p (K + padicValNat p d) q) : IsPDvdZ p K (q / (d : ℚ)) := by
  have : Fact p.Prime := ⟨hp⟩
  rcases hq with ⟨N, D, hD, hN, rfl⟩
  set v := padicValNat p d
  have hdv : p ^ v ∣ d := pow_padicValNat_dvd
  rcases hdv with ⟨u, hu⟩
  have hu_ndvd : ¬ p ∣ u := by
    intro hpu
    have hdv1 : p ^ (v + 1) ∣ d := by
      rcases hpu with ⟨w, rfl⟩
      refine ⟨w, ?_⟩
      rw [hu, pow_succ]
      ring
    have hle := (padicValNat_dvd_iff_le hd).mp hdv1
    omega
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hDu : ¬ (p : ℤ) ∣ D * (u : ℤ) := by
    intro h
    rcases hpZ.dvd_or_dvd h with h1 | h2
    · exact hD h1
    · exact hu_ndvd (Int.ofNat_dvd.mp h2)
  rcases hN with ⟨M, hM⟩
  have hN' : ((p ^ K : ℕ) : ℤ) ∣ ((p ^ K : ℕ) : ℤ) * M := dvd_mul_right _ _
  refine ⟨((p ^ K : ℕ) : ℤ) * M, D * (u : ℤ), hDu, hN', ?_⟩
  have hp_ne : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hpv_ne : (p : ℚ) ^ v ≠ 0 := pow_ne_zero v hp_ne
  have hD_ne : (D : ℚ) ≠ 0 := rat_ne_zero_of_not_dvd hD
  have hu_ne : (u : ℚ) ≠ 0 := by
    intro hu0
    have : u = 0 := Nat.cast_eq_zero.mp hu0
    exact hu_ndvd (this ▸ dvd_zero p)
  have hd_eq : (d : ℚ) = (p : ℚ) ^ v * (u : ℚ) := by exact_mod_cast hu
  have hN_eq : (N : ℚ) = (p : ℚ) ^ K * (p : ℚ) ^ v * (M : ℚ) := by
    have : (N : ℤ) = ((p ^ K : ℕ) : ℤ) * ((p ^ v : ℕ) : ℤ) * M := by
      rw [hM, pow_add, Nat.cast_mul, mul_assoc]
    exact_mod_cast this
  rw [hd_eq, hN_eq]
  push_cast
  field_simp

private lemma isPDvdZ_div_coprime_nat {p K d : ℕ} (hp : p.Prime) (hd : ¬ p ∣ d) {q : ℚ}
    (hq : IsPDvdZ p K q) : IsPDvdZ p K (q / (d : ℚ)) := by
  have : Fact p.Prime := ⟨hp⟩
  have hd0 : d ≠ 0 := fun h => hd (h ▸ dvd_zero p)
  have hv : padicValNat p d = 0 := padicValNat.eq_zero_of_not_dvd hd
  exact isPDvdZ_div_nat hp hd0 (by simpa [hv] using hq)

private lemma isPDvdZ_inv_sub_one {p K : ℕ} (_hp : p.Prime) (hK : 1 ≤ K) {u : ℚ}
    (hu : IsPDvdZ p K u) : IsPDvdZ p K ((1 + u)⁻¹ - 1) ∧ 1 + u ≠ 0 := by
  rcases hu with ⟨N, D, hD, hN, rfl⟩
  have hpN : (p : ℤ) ∣ N :=
    dvd_trans (Int.ofNat_dvd.mpr (dvd_pow_self p (by omega : K ≠ 0))) hN
  have hDN : ¬ (p : ℤ) ∣ (D + N) := by
    intro h
    have : (p : ℤ) ∣ D := (dvd_add_left hpN).mp h
    exact hD this
  have hD_ne : (D : ℚ) ≠ 0 := rat_ne_zero_of_not_dvd hD
  have hDN_ne : (D : ℚ) + (N : ℚ) ≠ 0 := by
    have := rat_ne_zero_of_not_dvd hDN
    push_cast at this
    exact this
  have h1u : 1 + (N : ℚ) / (D : ℚ) = ((D : ℚ) + (N : ℚ)) / (D : ℚ) := by
    field_simp
  have h1u_ne : 1 + (N : ℚ) / (D : ℚ) ≠ 0 := by
    rw [h1u]
    exact div_ne_zero hDN_ne hD_ne
  refine ⟨⟨-N, D + N, hDN, dvd_neg.mpr hN, ?_⟩, h1u_ne⟩
  rw [h1u]
  push_cast
  field_simp
  ring

private lemma isPDvdZ_dvd_int {p K : ℕ} (hp : p.Prime) {m : ℤ}
    (h : IsPDvdZ p K (m : ℚ)) : ((p ^ K : ℕ) : ℤ) ∣ m := by
  rcases h with ⟨N, D, hD, hN, hm⟩
  have hD_ne : (D : ℚ) ≠ 0 := rat_ne_zero_of_not_dvd hD
  have hq : (m : ℚ) * (D : ℚ) = (N : ℚ) := (eq_div_iff hD_ne).mp hm
  have hz : m * D = N := by exact_mod_cast hq
  have hpK_dvd : ((p ^ K : ℕ) : ℤ) ∣ m * D := hz ▸ hN
  have hcop : IsCoprime ((p ^ K : ℕ) : ℤ) D := by
    have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    have hcop1 : IsCoprime (p : ℤ) D := hpZ.coprime_iff_not_dvd.mpr hD
    simpa [Nat.cast_pow] using hcop1.pow_left (m := K)
  exact hcop.dvd_of_dvd_mul_right hpK_dvd

/-! ### Section 2: Truncated logarithm modulo p^K -/

private def truncLog (K : ℕ) (u : ℚ) : ℚ :=
  ∑ k ∈ Finset.Icc 1 K, ((-1 : ℚ) ^ (k - 1) / (k : ℚ)) * u ^ k

private lemma truncLog_zero (K : ℕ) : truncLog K 0 = 0 := by
  unfold truncLog
  refine Finset.sum_eq_zero ?_
  intro k hk
  have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  rw [zero_pow (by omega : k ≠ 0), mul_zero]

private lemma poly_geom_sum (K : ℕ) (w : ℚ[X]) :
    (1 + w) * ∑ k ∈ Finset.Icc 1 K, C ((-1 : ℚ) ^ (k - 1)) * w ^ (k - 1) = 1 - (-w) ^ K := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ K + 1), mul_add, ih]
    have h1 : C ((-1 : ℚ) ^ K) * w ^ K = (-w) ^ K := by
      rw [neg_eq_neg_one_mul, mul_pow]
      simp
      ring
    simp only [Nat.add_sub_cancel]
    rw [h1]
    ring

private lemma poly_deriv_truncLog (K : ℕ) (w : ℚ[X]) :
    derivative (∑ k ∈ Finset.Icc 1 K, C ((-1 : ℚ) ^ (k - 1) / (k : ℚ)) * w ^ k) =
      (∑ k ∈ Finset.Icc 1 K, C ((-1 : ℚ) ^ (k - 1)) * w ^ (k - 1)) * derivative w := by
  rw [derivative_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro k hk
  have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  have hk_ne : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [derivative_mul, derivative_C, zero_mul, zero_add, derivative_pow]
  have hC : C ((-1 : ℚ) ^ (k - 1) / (k : ℚ)) * (k : ℚ[X]) = C ((-1 : ℚ) ^ (k - 1)) := by
    rw [← C_eq_natCast, ← map_mul, div_mul_cancel₀ _ hk_ne]
  calc C ((-1 : ℚ) ^ (k - 1) / (k : ℚ)) * ((k : ℚ[X]) * w ^ (k - 1) * derivative w)
      = (C ((-1 : ℚ) ^ (k - 1) / (k : ℚ)) * (k : ℚ[X])) * w ^ (k - 1) * derivative w := by ring
    _ = C ((-1 : ℚ) ^ (k - 1)) * w ^ (k - 1) * derivative w := by rw [hC]

private lemma coeff_eq_zero_of_mul_unit_coeff_zero {A B : ℚ[X]} {K : ℕ}
    (hA0 : A.coeff 0 = 1) (hAB : ∀ j < K, (A * B).coeff j = 0) :
    ∀ j < K, B.coeff j = 0 := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hj
    have h0 := hAB j hj
    rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => A.coeff a * B.coeff b) j] at h0
    rw [Finset.sum_range_succ'] at h0
    simp only [Nat.sub_zero, hA0, one_mul] at h0
    have hrest : ∑ k ∈ Finset.range j, A.coeff (k + 1) * B.coeff (j - (k + 1)) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro k hk
      have hkj : j - (k + 1) < j := by
        have := Finset.mem_range.mp hk
        omega
      rw [ih (j - (k + 1)) hkj (by omega), mul_zero]
    rw [hrest, zero_add] at h0
    exact h0

private lemma poly_isPDvdZ_zero_mul {p : ℕ} (hp : p.Prime) {f g : ℚ[X]}
    (hf : ∀ m, IsPDvdZ p 0 (f.coeff m)) (hg : ∀ m, IsPDvdZ p 0 (g.coeff m)) :
    ∀ m, IsPDvdZ p 0 ((f * g).coeff m) := by
  intro m
  rw [coeff_mul]
  refine isPDvdZ_sum hp _ _ ?_
  intro x _
  simpa using isPDvdZ_mul hp (hf x.1) (hg x.2)

private lemma poly_isPDvdZ_zero_pow {p : ℕ} (hp : p.Prime) {f : ℚ[X]}
    (hf : ∀ m, IsPDvdZ p 0 (f.coeff m)) (k : ℕ) :
    ∀ m, IsPDvdZ p 0 ((f ^ k).coeff m) := by
  induction k with
  | zero =>
    intro m
    rw [pow_zero, coeff_one]
    split_ifs
    · exact isPDvdZ_natCast_zero hp 1
    · exact isPDvdZ_zero hp
  | succ k ih =>
    rw [pow_succ]
    exact poly_isPDvdZ_zero_mul hp ih hf

private lemma padicValNat_le_of_pos {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) :
    padicValNat p k ≤ k := by
  have : Fact p.Prime := ⟨hp⟩
  have h1 : p ^ padicValNat p k ≤ k :=
    Nat.le_of_dvd (by omega) pow_padicValNat_dvd
  have h2 : padicValNat p k ≤ p ^ padicValNat p k :=
    le_trans (Nat.le_of_lt Nat.lt_two_pow_self) (Nat.pow_le_pow_left hp.two_le _)
  exact le_trans h2 h1

private lemma isPDvdZ_neg_one_pow {p : ℕ} (hp : p.Prime) (m : ℕ) :
    IsPDvdZ p 0 ((-1 : ℚ) ^ m) := by
  have h : ((-1 : ℚ) ^ m) = (((-1 : ℤ) ^ m : ℤ) : ℚ) := by push_cast; rfl
  rw [h]
  exact isPDvdZ_intCast_zero hp ((-1 : ℤ) ^ m)

private lemma isPDvdZ_truncLog_add {p K : ℕ} (hp : p.Prime) {u v : ℚ}
    (hu : IsPDvdZ p 2 u) (hv : IsPDvdZ p 2 v) :
    IsPDvdZ p K (truncLog K (u + v + u * v) - truncLog K u - truncLog K v) := by
  have : Fact p.Prime := ⟨hp⟩
  rcases hu with ⟨Nu, Du, hDu, ⟨Mu, hNu⟩, rfl⟩
  rcases hv with ⟨Nv, Dv, hDv, ⟨Mv, hNv⟩, rfl⟩
  set u' : ℚ := (Mu : ℚ) / (Du : ℚ)
  set v' : ℚ := (Mv : ℚ) / (Dv : ℚ)
  have hu_eq : (Nu : ℚ) / (Du : ℚ) = (p ^ 2 : ℚ) * u' := by
    have : (Nu : ℚ) = (p ^ 2 : ℚ) * (Mu : ℚ) := by
      have h1 : (Nu : ℤ) = ((p ^ 2 : ℕ) : ℤ) * Mu := hNu
      exact_mod_cast h1
    rw [this]
    dsimp [u']
    ring
  have hv_eq : (Nv : ℚ) / (Dv : ℚ) = (p ^ 2 : ℚ) * v' := by
    have : (Nv : ℚ) = (p ^ 2 : ℚ) * (Mv : ℚ) := by
      have h1 : (Nv : ℤ) = ((p ^ 2 : ℕ) : ℤ) * Mv := hNv
      exact_mod_cast h1
    rw [this]
    dsimp [v']
    ring
  have hu' : IsPDvdZ p 0 u' := ⟨Mu, Du, hDu, by simp, rfl⟩
  have hv' : IsPDvdZ p 0 v' := ⟨Mv, Dv, hDv, by simp, rfl⟩
  set w1 : ℚ[X] := C u' * X
  set w2 : ℚ[X] := C v' * X
  set w12 : ℚ[X] := C u' * X + C v' * X + C (u' * v') * X ^ 2
  set G : ℚ[X] :=
    ∑ k ∈ Finset.Icc 1 K, C ((-1 : ℚ) ^ (k - 1) / (k : ℚ)) * (w12 ^ k - w1 ^ k - w2 ^ k)
  have hGeval : G.eval (p ^ 2 : ℚ) =
      truncLog K ((p ^ 2 : ℚ) * u' + (p ^ 2 : ℚ) * v' + ((p ^ 2 : ℚ) * u') * ((p ^ 2 : ℚ) * v')) -
      truncLog K ((p ^ 2 : ℚ) * u') - truncLog K ((p ^ 2 : ℚ) * v') := by
    dsimp [G, truncLog]
    rw [eval_finsetSum]
    simp only [eval_mul, eval_sub, eval_pow, eval_C, eval_add, eval_X, w1, w2, w12]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro k _
    ring
  rw [hu_eq, hv_eq, ← hGeval]
  have hG_split : G =
      (∑ k ∈ Finset.Icc 1 K, C ((-1 : ℚ) ^ (k - 1) / (k : ℚ)) * w12 ^ k) -
      (∑ k ∈ Finset.Icc 1 K, C ((-1 : ℚ) ^ (k - 1) / (k : ℚ)) * w1 ^ k) -
      (∑ k ∈ Finset.Icc 1 K, C ((-1 : ℚ) ^ (k - 1) / (k : ℚ)) * w2 ^ k) := by
    dsimp [G]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro k _
    ring
  have hw12_id : 1 + w12 = (1 + w1) * (1 + w2) := by
    dsimp [w1, w2, w12]
    rw [map_mul]
    ring
  have hdw1 : derivative w1 = C u' := by
    dsimp [w1]
    simp
  have hdw2 : derivative w2 = C v' := by
    dsimp [w2]
    simp
  have hdw12 : derivative w12 = C u' * (1 + w2) + C v' * (1 + w1) := by
    dsimp [w12, w1, w2]
    simp only [derivative_add, derivative_mul, derivative_C, derivative_X, derivative_pow,
      Nat.cast_ofNat, zero_mul, zero_add, mul_one, map_mul, map_ofNat]
    ring
  have hderiv_mul : (1 + w1) * (1 + w2) * derivative G =
      -((-w12) ^ K) * derivative w12 +
      ((-w1) ^ K) * derivative w1 * (1 + w2) +
      ((-w2) ^ K) * derivative w2 * (1 + w1) := by
    rw [hG_split, derivative_sub, derivative_sub, poly_deriv_truncLog, poly_deriv_truncLog,
      poly_deriv_truncLog]
    have hA := poly_geom_sum K w12
    have hB := poly_geom_sum K w1
    have hC := poly_geom_sum K w2
    rw [hw12_id] at hA
    calc (1 + w1) * (1 + w2) *
          ((∑ k ∈ Finset.Icc 1 K, C ((-1 : ℚ) ^ (k - 1)) * w12 ^ (k - 1)) * derivative w12 -
           (∑ k ∈ Finset.Icc 1 K, C ((-1 : ℚ) ^ (k - 1)) * w1 ^ (k - 1)) * derivative w1 -
           (∑ k ∈ Finset.Icc 1 K, C ((-1 : ℚ) ^ (k - 1)) * w2 ^ (k - 1)) * derivative w2)
        = ((1 + w1) * (1 + w2) * ∑ k ∈ Finset.Icc 1 K, C ((-1 : ℚ) ^ (k - 1)) * w12 ^ (k - 1)) *
            derivative w12 -
          ((1 + w1) * ∑ k ∈ Finset.Icc 1 K, C ((-1 : ℚ) ^ (k - 1)) * w1 ^ (k - 1)) *
            derivative w1 * (1 + w2) -
          ((1 + w2) * ∑ k ∈ Finset.Icc 1 K, C ((-1 : ℚ) ^ (k - 1)) * w2 ^ (k - 1)) *
            derivative w2 * (1 + w1) := by ring
      _ = (1 - (-w12) ^ K) * derivative w12 - (1 - (-w1) ^ K) * derivative w1 * (1 + w2) -
          (1 - (-w2) ^ K) * derivative w2 * (1 + w1) := by rw [hA, hB, hC]
      _ = (derivative w12 - derivative w1 * (1 + w2) - derivative w2 * (1 + w1)) -
          ((-w12) ^ K) * derivative w12 + ((-w1) ^ K) * derivative w1 * (1 + w2) +
          ((-w2) ^ K) * derivative w2 * (1 + w1) := by ring
      _ = -((-w12) ^ K) * derivative w12 + ((-w1) ^ K) * derivative w1 * (1 + w2) +
          ((-w2) ^ K) * derivative w2 * (1 + w1) := by
          rw [hdw12, hdw1, hdw2]
          ring
  have hX_dvd_w1 : X ∣ w1 := ⟨C u', by dsimp [w1]; ring⟩
  have hX_dvd_w2 : X ∣ w2 := ⟨C v', by dsimp [w2]; ring⟩
  have hX_dvd_w12 : X ∣ w12 := ⟨C u' + C v' + C (u' * v') * X, by dsimp [w12]; ring⟩
  have hXK_dvd : X ^ K ∣ (1 + w1) * (1 + w2) * derivative G := by
    rw [hderiv_mul]
    have h1 : X ^ K ∣ (-w12) ^ K := pow_dvd_pow_of_dvd (dvd_neg.mpr hX_dvd_w12) K
    have h2 : X ^ K ∣ (-w1) ^ K := pow_dvd_pow_of_dvd (dvd_neg.mpr hX_dvd_w1) K
    have h3 : X ^ K ∣ (-w2) ^ K := pow_dvd_pow_of_dvd (dvd_neg.mpr hX_dvd_w2) K
    exact dvd_add (dvd_add (dvd_mul_of_dvd_left (dvd_neg.mpr h1) _)
      (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h2 _) _))
      (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h3 _) _)
  have hprod_coeff : ∀ j < K, ((1 + w1) * (1 + w2) * derivative G).coeff j = 0 := by
    intro j hj
    rcases hXK_dvd with ⟨Q, hQ⟩
    rw [hQ, coeff_X_pow_mul']
    exact if_neg (not_le.mpr hj)
  have hunit0 : ((1 + w1) * (1 + w2)).coeff 0 = 1 := by
    rw [← hw12_id]
    simp [w12]
  have hdG_zero : ∀ j < K, (derivative G).coeff j = 0 :=
    coeff_eq_zero_of_mul_unit_coeff_zero hunit0 hprod_coeff
  have hG_coeff_zero : ∀ m ≤ K, G.coeff m = 0 := by
    intro m hm
    cases m with
    | zero =>
      dsimp [G]
      rw [finsetSum_coeff]
      refine Finset.sum_eq_zero ?_
      intro k hk
      have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
      rw [coeff_C_mul]
      have hsub0 : (w12 ^ k - w1 ^ k - w2 ^ k).coeff 0 = 0 := by
        rw [coeff_sub, coeff_sub, coeff_zero_eq_eval_zero, coeff_zero_eq_eval_zero,
          coeff_zero_eq_eval_zero]
        simp [w1, w2, w12, zero_pow (by omega : k ≠ 0)]
      rw [hsub0, mul_zero]
    | succ m =>
      have hmK : m < K := Nat.lt_of_succ_le hm
      have hdm := hdG_zero m hmK
      rw [coeff_derivative] at hdm
      have hne : ((m : ℚ) + 1) ≠ 0 := by positivity
      exact (mul_eq_zero.mp hdm).resolve_right hne
  rw [eval_eq_sum_range]
  refine isPDvdZ_sum hp _ _ ?_
  intro m _
  by_cases hm : m ≤ K
  · rw [hG_coeff_zero m hm, zero_mul]
    exact isPDvdZ_zero hp
  · have hmK : K + 1 ≤ m := by omega
    have hw1_c : ∀ j, IsPDvdZ p 0 (w1.coeff j) := by
      intro j
      dsimp [w1]
      rw [coeff_C_mul, coeff_X]
      split_ifs
      · simpa using hu'
      · simpa using isPDvdZ_zero hp
    have hw2_c : ∀ j, IsPDvdZ p 0 (w2.coeff j) := by
      intro j
      dsimp [w2]
      rw [coeff_C_mul, coeff_X]
      split_ifs
      · simpa using hv'
      · simpa using isPDvdZ_zero hp
    have hw12_c : ∀ j, IsPDvdZ p 0 (w12.coeff j) := by
      intro j
      have hEq : w12 = w1 + w2 + w1 * w2 := by
        dsimp [w1, w2, w12]
        rw [map_mul]
        ring
      rw [hEq, coeff_add, coeff_add]
      exact isPDvdZ_add hp (isPDvdZ_add hp (hw1_c j) (hw2_c j))
        (poly_isPDvdZ_zero_mul hp hw1_c hw2_c j)
    dsimp [G]
    rw [finsetSum_coeff, Finset.sum_mul]
    refine isPDvdZ_sum hp _ _ ?_
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hkK : k ≤ K := (Finset.mem_Icc.mp hk).2
    rw [coeff_C_mul]
    have hpoly_c : IsPDvdZ p 0 ((w12 ^ k - w1 ^ k - w2 ^ k).coeff m) := by
      rw [coeff_sub, coeff_sub]
      exact isPDvdZ_sub hp (isPDvdZ_sub hp (poly_isPDvdZ_zero_pow hp hw12_c k m)
        (poly_isPDvdZ_zero_pow hp hw1_c k m)) (poly_isPDvdZ_zero_pow hp hw2_c k m)
    have hpow_p : IsPDvdZ p (2 * m) ((p ^ 2 : ℚ) ^ m) := by
      have : ((p ^ 2 : ℚ) ^ m) = ((p ^ (2 * m) : ℕ) : ℚ) := by
        rw [pow_mul]
        push_cast
        ring
      rw [this]
      exact isPDvdZ_natCast hp (p ^ (2 * m)) dvd_rfl
    have hnum : IsPDvdZ p (2 * m)
        (((-1 : ℚ) ^ (k - 1)) * (w12 ^ k - w1 ^ k - w2 ^ k).coeff m * (p ^ 2 : ℚ) ^ m) := by
      have h1 := isPDvdZ_mul hp (isPDvdZ_neg_one_pow hp (k - 1)) hpoly_c
      have h2 := isPDvdZ_mul hp h1 hpow_p
      simpa using h2
    have hle : K + padicValNat p k ≤ 2 * m := by
      have hv := padicValNat_le_of_pos hp hk1
      omega
    have hdiv := isPDvdZ_div_nat hp (by omega : k ≠ 0) (isPDvdZ_mono hle hnum)
    have hrew : ((-1 : ℚ) ^ (k - 1) / (k : ℚ)) * (w12 ^ k - w1 ^ k - w2 ^ k).coeff m *
        (p ^ 2 : ℚ) ^ m =
        ((-1 : ℚ) ^ (k - 1) * (w12 ^ k - w1 ^ k - w2 ^ k).coeff m * (p ^ 2 : ℚ) ^ m) /
          (k : ℚ) := by ring
    rw [hrew]
    exact hdiv

private lemma isPDvdZ_truncLog_prod {ι : Type*} {p K : ℕ} (hp : p.Prime)
    (s : Finset ι) (f : ι → ℚ) (hf : ∀ i ∈ s, IsPDvdZ p 2 (f i)) :
    IsPDvdZ p 2 ((∏ i ∈ s, (1 + f i)) - 1) ∧
    IsPDvdZ p K (truncLog K ((∏ i ∈ s, (1 + f i)) - 1) - ∑ i ∈ s, truncLog K (f i)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, sub_self, Finset.sum_empty, truncLog_zero]
    exact ⟨isPDvdZ_zero hp, isPDvdZ_zero hp⟩
  | @insert a s ha ih =>
    have hfa := hf a (Finset.mem_insert_self a s)
    have hfs : ∀ i ∈ s, IsPDvdZ p 2 (f i) := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    rcases ih hfs with ⟨hprod2, hlog⟩
    set u := f a
    set v := (∏ i ∈ s, (1 + f i)) - 1
    have hprod_eq : (∏ i ∈ insert a s, (1 + f i)) - 1 = u + v + u * v := by
      rw [Finset.prod_insert ha]
      dsimp [u, v]
      ring
    have h2 : IsPDvdZ p 2 (u + v + u * v) := by
      have huv : IsPDvdZ p 2 (u * v) := isPDvdZ_mono (by omega : 2 ≤ 2 + 2) (isPDvdZ_mul hp hfa hprod2)
      exact isPDvdZ_add hp (isPDvdZ_add hp hfa hprod2) huv
    refine ⟨hprod_eq ▸ h2, ?_⟩
    rw [hprod_eq, Finset.sum_insert ha]
    have hstep := isPDvdZ_truncLog_add (K := K) hp hfa hprod2
    have hrew : truncLog K (u + v + u * v) - (truncLog K u + ∑ i ∈ s, truncLog K (f i)) =
        (truncLog K (u + v + u * v) - truncLog K u - truncLog K v) +
        (truncLog K v - ∑ i ∈ s, truncLog K (f i)) := by ring
    rw [hrew]
    exact isPDvdZ_add hp hstep hlog

private lemma isPDvdZ_truncLog_div {p K : ℕ} (hp : p.Prime) {u v : ℚ}
    (hu : IsPDvdZ p 2 u) (hv : IsPDvdZ p 2 v) :
    IsPDvdZ p 2 ((1 + u) / (1 + v) - 1) ∧
    IsPDvdZ p K (truncLog K ((1 + u) / (1 + v) - 1) - (truncLog K u - truncLog K v)) := by
  rcases isPDvdZ_inv_sub_one hp (by omega) hv with ⟨hinv2, h1v_ne⟩
  set w := (1 + v)⁻¹ - 1
  have hvw_eq : v + w + v * w = 0 := by
    dsimp [w]
    field_simp
    ring
  have hlog_inv : IsPDvdZ p K (truncLog K w + truncLog K v) := by
    have h := isPDvdZ_truncLog_add (K := K) hp hv hinv2
    rw [hvw_eq, truncLog_zero] at h
    have hrew : truncLog K w + truncLog K v = -(0 - truncLog K v - truncLog K w) := by ring
    rw [hrew]
    exact isPDvdZ_neg h
  have hdiv_eq : (1 + u) / (1 + v) - 1 = u + w + u * w := by
    dsimp [w]
    field_simp
    ring
  have h2 : IsPDvdZ p 2 (u + w + u * w) :=
    isPDvdZ_add hp (isPDvdZ_add hp hu hinv2)
      (isPDvdZ_mono (by omega : 2 ≤ 2 + 2) (isPDvdZ_mul hp hu hinv2))
  refine ⟨hdiv_eq ▸ h2, ?_⟩
  rw [hdiv_eq]
  have hadd := isPDvdZ_truncLog_add (K := K) hp hu hinv2
  have hrew : truncLog K (u + w + u * w) - (truncLog K u - truncLog K v) =
      (truncLog K (u + w + u * w) - truncLog K u - truncLog K w) +
      (truncLog K w + truncLog K v) := by ring
  rw [hrew]
  exact isPDvdZ_add hp hadd hlog_inv

private lemma three_pow_ge_add_two (t : ℕ) (ht : 1 ≤ t) : t + 2 ≤ 3 ^ t := by
  induction t with
  | zero => omega
  | succ m ih =>
    cases m with
    | zero => norm_num
    | succ m =>
      have h1 : m + 1 + 2 ≤ 3 ^ (m + 1) := ih (by omega)
      have h2 : 3 ^ (m + 2) = 3 * 3 ^ (m + 1) := by ring
      omega

private lemma five_pow_ge_two_mul (t : ℕ) : 2 * t ≤ 5 ^ t := by
  induction t with
  | zero => norm_num
  | succ m ih =>
    have h1 : 5 ^ (m + 1) = 5 * 5 ^ m := by ring
    have h2 : 1 ≤ 5 ^ m := Nat.one_le_pow m 5 (by omega)
    omega

private lemma padicValNat_lt_two_mul_pred {p k : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hk : 2 ≤ k) :
    padicValNat p k + 1 ≤ 2 * (k - 1) := by
  have : Fact p.Prime := ⟨hp⟩
  set t := padicValNat p k
  by_cases ht : t = 0
  · omega
  · have hpow : 3 ^ t ≤ k :=
      le_trans (Nat.pow_le_pow_left hp3 t) (Nat.le_of_dvd (by omega) pow_padicValNat_dvd)
    have h3t := three_pow_ge_add_two t (by omega)
    omega

private lemma isPDvdZ_of_truncLog {p K : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) {u : ℚ}
    (hu2 : IsPDvdZ p 2 u) (hlog : IsPDvdZ p K (truncLog K u)) : IsPDvdZ p K u := by
  by_cases hK2 : K ≤ 2
  · exact isPDvdZ_mono hK2 hu2
  · have hstep : ∀ M : ℕ, 2 ≤ M → M ≤ K → IsPDvdZ p M u := by
      intro M hM2 hMK
      induction M with
      | zero => omega
      | succ M ih =>
        by_cases hM1 : M < 2
        · have : M + 1 = 2 := by omega
          rw [this]
          exact hu2
        · have hMu : IsPDvdZ p M u := ih (by omega) (by omega)
          have hlogM1 : IsPDvdZ p (M + 1) (truncLog K u) := isPDvdZ_mono hMK hlog
          have htail_eq : truncLog K u - u =
              ∑ k ∈ Finset.Icc 2 K, ((-1 : ℚ) ^ (k - 1) / (k : ℚ)) * u ^ k := by
            unfold truncLog
            have h1 : Finset.Icc 1 K = insert 1 (Finset.Icc 2 K) := by
              ext x
              simp only [Finset.mem_Icc, Finset.mem_insert]
              omega
            rw [h1, Finset.sum_insert (by simp)]
            simp
          have htail : IsPDvdZ p (M + 1) (truncLog K u - u) := by
            rw [htail_eq]
            refine isPDvdZ_sum hp _ _ ?_
            intro k hk
            have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
            have hpow : IsPDvdZ p (k * M) (u ^ k) := isPDvdZ_pow hp hMu k
            have hnum : IsPDvdZ p (k * M) (((-1 : ℚ) ^ (k - 1)) * u ^ k) := by
              simpa using isPDvdZ_mul hp (isPDvdZ_neg_one_pow hp (k - 1)) hpow
            have hle : M + 1 + padicValNat p k ≤ k * M := by
              have hv := padicValNat_lt_two_mul_pred hp hp3 hk2
              have hmul : 2 * (k - 1) ≤ (k - 1) * M := by nlinarith
              have hkm : (k - 1) * M + M = k * M := by
                cases k with
                | zero => omega
                | succ k => simp [Nat.succ_mul]
              omega
            have hdiv := isPDvdZ_div_nat hp (by omega : k ≠ 0) (isPDvdZ_mono hle hnum)
            have hrew : ((-1 : ℚ) ^ (k - 1) / (k : ℚ)) * u ^ k =
                (((-1 : ℚ) ^ (k - 1)) * u ^ k) / (k : ℚ) := by ring
            rw [hrew]
            exact hdiv
          have hu_eq : u = truncLog K u - (truncLog K u - u) := by ring
          rw [hu_eq]
          exact isPDvdZ_sub hp hlogM1 htail
    exact hstep K (by omega) le_rfl

/-! ### Section 3: Odd polynomial antidifference for Psi_k -/

private def psi (k n : ℕ) : ℕ :=
  ∑ m ∈ Finset.range n, (m * (m + 1)) ^ k

private lemma three_mul_psi_one (n : ℕ) :
    3 * (psi 1 n : ℤ) = (n : ℤ) ^ 3 - (n : ℤ) := by
  induction n with
  | zero => simp [psi]
  | succ n ih =>
    rw [psi, Finset.sum_range_succ]
    change 3 * ((psi 1 n : ℤ) + ((n * (n + 1)) ^ 1 : ℕ)) = ((n + 1 : ℕ) : ℤ) ^ 3 - ((n + 1 : ℕ) : ℤ)
    push_cast
    linarith

private lemma psi_one_diff (b c : ℕ) :
    (psi 1 (b + c) : ℤ) - (psi 1 b : ℤ) - (psi 1 c : ℤ) =
      (((b + c) * b * c : ℕ) : ℤ) := by
  have h1 := three_mul_psi_one (b + c)
  have h2 := three_mul_psi_one b
  have h3 := three_mul_psi_one c
  push_cast at h1 ⊢
  linarith

private lemma odd_pow_add_sub_dvd (b c : ℤ) (m : ℕ) :
    (b + c) * b * c ∣ (b + c) ^ (2 * m + 1) - b ^ (2 * m + 1) - c ^ (2 * m + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    cases m with
    | zero =>
      refine ⟨3, ?_⟩
      ring
    | succ m =>
      have hodd1 : (b + c) ∣ b ^ (2 * (m + 1) + 1) + c ^ (2 * (m + 1) + 1) :=
        (odd_two_mul_add_one (m + 1)).add_dvd_pow_add_pow b c
      have hodd2 : (b + c) ∣ b ^ (2 * m + 1) + c ^ (2 * m + 1) :=
        (odd_two_mul_add_one m).add_dvd_pow_add_pow b c
      rcases ih with ⟨q0, hq0⟩
      rcases hodd1 with ⟨q1, hq1⟩
      rcases hodd2 with ⟨q2, hq2⟩
      refine ⟨(b + c) ^ 2 * q0 + 2 * q1 + b * c * q2, ?_⟩
      have hstep : (b + c) ^ (2 * (m + 2) + 1) - b ^ (2 * (m + 2) + 1) - c ^ (2 * (m + 2) + 1) =
          (b + c) ^ 2 * ((b + c) ^ (2 * (m + 1) + 1) - b ^ (2 * (m + 1) + 1) - c ^ (2 * (m + 1) + 1)) +
          2 * b * c * (b ^ (2 * (m + 1) + 1) + c ^ (2 * (m + 1) + 1)) +
          (b * c) ^ 2 * (b ^ (2 * m + 1) + c ^ (2 * m + 1)) := by ring
      rw [hstep, hq0, hq1, hq2]
      ring

private lemma descPochhammer_monic_int (d : ℕ) : (descPochhammer ℤ d).Monic := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [descPochhammer_succ_right]
    exact ih.mul (monic_X_sub_C (d : ℤ))

private lemma descPochhammer_antidiff (d : ℕ) :
    (descPochhammer ℚ (d + 1)).comp (X + 1) - descPochhammer ℚ (d + 1) =
      C ((d + 1 : ℕ) : ℚ) * descPochhammer ℚ d := by
  have h1 : (descPochhammer ℚ (d + 1)).comp (X + 1) = (X + 1) * descPochhammer ℚ d := by
    rw [descPochhammer_succ_left, mul_comp, X_comp, comp_assoc]
    have hX : (X - 1 : ℚ[X]).comp (X + 1) = X := by simp
    rw [hX, comp_X]
  rw [h1, descPochhammer_succ_right, C_eq_natCast]
  push_cast
  ring

private lemma exists_antidiff_int (D : ℕ) :
    ∀ Q : ℤ[X], Q.natDegree ≤ D →
      ∃ F : ℚ[X], ∃ G : ℤ[X],
        F.eval 0 = 0 ∧
        F.comp (X + 1) - F = Q.map (Int.castRingHom ℚ) ∧
        G.map (Int.castRingHom ℚ) = C ((D + 1).factorial : ℚ) * F := by
  induction D with
  | zero =>
    intro Q hQ
    have hQeq : Q = C (Q.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero (Nat.le_zero.mp hQ)
    refine ⟨C (Q.coeff 0 : ℚ) * X, C (Q.coeff 0) * X, by simp, ?_, ?_⟩
    · rw [hQeq]
      simp [mul_add]
    · simp
  | succ D ih =>
    intro Q hQ
    set c : ℤ := Q.coeff (D + 1)
    set Q' : ℤ[X] := Q - C c * descPochhammer ℤ (D + 1)
    have hdeg_dp : (descPochhammer ℤ (D + 1)).natDegree = D + 1 := descPochhammer_natDegree ℤ (D + 1)
    have hmonic_dp : (descPochhammer ℤ (D + 1)).Monic := descPochhammer_monic_int (D + 1)
    have hdeg_Q' : Q'.natDegree ≤ D := by
      by_cases hQ0 : Q' = 0
      · simp [hQ0]
      · suffices hlt : Q'.natDegree < D + 1 by omega
        refine lt_of_le_of_ne ?_ ?_
        · refine le_trans (natDegree_sub_le _ _) (max_le hQ ?_)
          refine le_trans natDegree_mul_le ?_
          rw [natDegree_C, zero_add, hdeg_dp]
        · intro heq
          have hlc : Q'.coeff (D + 1) = 0 := by
            dsimp [Q', c]
            rw [coeff_sub, coeff_C_mul]
            have h1 : (descPochhammer ℤ (D + 1)).coeff (D + 1) = 1 := by
              simpa [leadingCoeff, hdeg_dp] using hmonic_dp.leadingCoeff
            rw [h1, mul_one, sub_self]
          have hne : Q'.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hQ0
          rw [leadingCoeff, heq] at hne
          exact hne hlc
    rcases ih Q' hdeg_Q' with ⟨F', G', hF'0, hF'diff, hG'⟩
    set Fd : ℚ[X] := C ((c : ℚ) / ((D + 2 : ℕ) : ℚ)) * descPochhammer ℚ (D + 2)
    set Gd : ℤ[X] := C (c * ((D + 1).factorial : ℤ)) * descPochhammer ℤ (D + 2)
    refine ⟨Fd + F', Gd + C ((D + 2 : ℕ) : ℤ) * G', ?_, ?_, ?_⟩
    · rw [eval_add, hF'0, add_zero]
      dsimp [Fd]
      rw [eval_mul, descPochhammer_eval_zero, if_neg (by omega), mul_zero]
    · rw [add_comp]
      have hFd_diff : Fd.comp (X + 1) - Fd =
          (C c * descPochhammer ℤ (D + 1)).map (Int.castRingHom ℚ) := by
        dsimp [Fd]
        rw [mul_comp, C_comp, ← mul_sub, descPochhammer_antidiff (D + 1)]
        have hne : ((D + 2 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        rw [Polynomial.map_mul, Polynomial.map_C, descPochhammer_map]
        have hC : C ((c : ℚ) / ((D + 2 : ℕ) : ℚ)) * C ((D + 2 : ℕ) : ℚ) = C (c : ℚ) := by
          rw [← map_mul, div_mul_cancel₀ _ hne]
        calc C ((c : ℚ) / ((D + 2 : ℕ) : ℚ)) * (C ((D + 2 : ℕ) : ℚ) * descPochhammer ℚ (D + 1))
            = (C ((c : ℚ) / ((D + 2 : ℕ) : ℚ)) * C ((D + 2 : ℕ) : ℚ)) * descPochhammer ℚ (D + 1) := by ring
          _ = C (c : ℚ) * descPochhammer ℚ (D + 1) := by rw [hC]
          _ = C ((Int.castRingHom ℚ) c) * descPochhammer ℚ (D + 1) := rfl
      have hQ_eq : Q = C c * descPochhammer ℤ (D + 1) + Q' := by
        dsimp [Q']
        ring
      calc (Fd.comp (X + 1) + F'.comp (X + 1)) - (Fd + F')
          = (Fd.comp (X + 1) - Fd) + (F'.comp (X + 1) - F') := by ring
        _ = (C c * descPochhammer ℤ (D + 1)).map (Int.castRingHom ℚ) +
              Q'.map (Int.castRingHom ℚ) := by rw [hFd_diff, hF'diff]
        _ = (C c * descPochhammer ℤ (D + 1) + Q').map (Int.castRingHom ℚ) := by
              rw [Polynomial.map_add]
        _ = Q.map (Int.castRingHom ℚ) := by rw [← hQ_eq]
    · have hfac : ((D + 2).factorial : ℚ) = ((D + 2 : ℕ) : ℚ) * ((D + 1).factorial : ℚ) := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      have hGd : Gd.map (Int.castRingHom ℚ) = C ((D + 2).factorial : ℚ) * Fd := by
        dsimp [Gd, Fd]
        rw [Polynomial.map_mul, Polynomial.map_C, descPochhammer_map]
        have hne : ((D + 2 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        have hC : C ((D + 2).factorial : ℚ) * C ((c : ℚ) / ((D + 2 : ℕ) : ℚ)) =
            C ((Int.castRingHom ℚ) (c * ((D + 1).factorial : ℤ))) := by
          rw [← map_mul, hfac]
          congr 1
          simp only [Int.coe_castRingHom, Int.cast_mul, Int.cast_natCast]
          field_simp
        rw [← mul_assoc, hC]
      have hG2 : (C ((D + 2 : ℕ) : ℤ) * G').map (Int.castRingHom ℚ) =
          C ((D + 2).factorial : ℚ) * F' := by
        rw [Polynomial.map_mul, Polynomial.map_C, hG', ← mul_assoc, ← map_mul, hfac]
        simp
      rw [Polynomial.map_add, hGd, hG2, mul_add]

private lemma poly_eq_zero_of_periodic {H : ℚ[X]} (h0 : H.eval 0 = 0)
    (hper : H.comp (X + 1) = H) : H = 0 := by
  have hnat : ∀ n : ℕ, H.eval (n : ℚ) = 0 := by
    intro n
    induction n with
    | zero => simpa using h0
    | succ n ih =>
      have h1 := congr_arg (fun P : ℚ[X] => P.eval (n : ℚ)) hper
      rw [eval_comp, eval_add, eval_X, eval_one] at h1
      push_cast
      rw [h1, ih]
  by_contra hne
  set N := (H.roots.toFinset).card + 1
  have hsub : (Finset.range N).image (fun n : ℕ => (n : ℚ)) ⊆ H.roots.toFinset := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨n, _, rfl⟩
    rw [Multiset.mem_toFinset, mem_roots hne, IsRoot.def]
    exact hnat n
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range] at hcard
  omega

private lemma coeff_comp_neg_X_int (G : ℤ[X]) (d : ℕ) :
    (G.comp (-X)).coeff d = (-1 : ℤ) ^ d * G.coeff d := by
  induction G using Polynomial.induction_on' with
  | add p q ihp ihq =>
    rw [add_comp, coeff_add, coeff_add, ihp, ihq, mul_add]
  | monomial n a =>
    rw [← C_mul_X_pow_eq_monomial, mul_comp, C_comp, pow_comp, X_comp, neg_eq_neg_one_mul, mul_pow]
    have h1 : C a * ((-1 : ℤ[X]) ^ n * X ^ n) = C (a * (-1 : ℤ) ^ n) * X ^ n := by
      rw [map_mul, map_pow, map_neg, map_one]
      ring
    rw [h1, coeff_C_mul_X_pow, coeff_C_mul_X_pow]
    split_ifs with h
    · subst h; ring
    · ring

private lemma eval_map_int_cast (G : ℤ[X]) (z : ℤ) :
    (G.map (Int.castRingHom ℚ)).eval (z : ℚ) = ((G.eval z : ℤ) : ℚ) := by
  induction G using Polynomial.induction_on' with
  | add p q ihp ihq =>
    simp [ihp, ihq]
  | monomial n a =>
    simp

private lemma dvd_factorial_psi (k b c : ℕ) (_hk : 1 ≤ k) :
    (((b + c) * b * c : ℕ) : ℤ) ∣
      ((2 * k + 1).factorial : ℤ) * ((psi k (b + c) : ℤ) - (psi k b : ℤ) - (psi k c : ℤ)) := by
  set Q : ℤ[X] := (X * (X + 1)) ^ k
  have hdegQ : Q.natDegree ≤ 2 * k := by
    dsimp [Q]
    refine le_trans natDegree_pow_le ?_
    have h1 : (X * (X + 1) : ℤ[X]).natDegree ≤ 2 := by
      refine le_trans natDegree_mul_le ?_
      have hX1 : (X + 1 : ℤ[X]).natDegree ≤ 1 :=
        le_trans (natDegree_add_le _ _) (by simp)
      simp only [natDegree_X]
      omega
    have := Nat.mul_le_mul_left k h1
    omega
  rcases exists_antidiff_int (2 * k) Q hdegQ with ⟨F, G, hF0, hFdiff, hG⟩
  have hFeval : ∀ n : ℕ, F.eval (n : ℚ) = (psi k n : ℚ) := by
    intro n
    induction n with
    | zero => simpa [psi] using hF0
    | succ n ih =>
      have h1 := congr_arg (fun P : ℚ[X] => P.eval (n : ℚ)) hFdiff
      rw [eval_sub, eval_comp, eval_add, eval_X, eval_one, eval_map] at h1
      have hQev : Q.eval₂ (Int.castRingHom ℚ) (n : ℚ) = (((n * (n + 1)) ^ k : ℕ) : ℚ) := by
        dsimp [Q]
        simp [eval₂_pow, eval₂_mul, eval₂_add, eval₂_X, eval₂_one]
      rw [hQev, ih] at h1
      rw [psi, Finset.sum_range_succ]
      push_cast
      have : F.eval ((n : ℚ) + 1) = (psi k n : ℚ) + ((n : ℚ) * ((n : ℚ) + 1)) ^ k := by
        push_cast at h1
        linarith
      simpa [psi] using this
  have hFodd : F.comp (-X) = -F := by
    set H : ℚ[X] := F.comp (-X) + F
    have hH0 : H.eval 0 = 0 := by
      dsimp [H]
      rw [eval_add, eval_comp, eval_neg, eval_X, neg_zero, hF0, add_zero]
    have hHper : H.comp (X + 1) = H := by
      have hcomp1 : (F.comp (-X)).comp (X + 1) = F.comp (-X - 1) := by
        rw [comp_assoc]
        congr 1
        simp only [neg_comp, X_comp]
        ring
      have hcomp2 : (F.comp (X + 1)).comp (-X - 1) = F.comp (-X) := by
        rw [comp_assoc]
        congr 1
        simp only [add_comp, X_comp, one_comp]
        ring
      have hQsym : (Q.map (Int.castRingHom ℚ)).comp (-X - 1) = Q.map (Int.castRingHom ℚ) := by
        dsimp [Q]
        simp only [Polynomial.map_pow, Polynomial.map_mul, Polynomial.map_add, Polynomial.map_X,
          Polynomial.map_one, pow_comp, mul_comp, add_comp, X_comp, one_comp]
        congr 1
        ring
      have h2 := congr_arg (fun P : ℚ[X] => P.comp (-X - 1)) hFdiff
      rw [sub_comp, hcomp2, hQsym, ← hFdiff] at h2
      dsimp [H]
      rw [add_comp, hcomp1]
      linear_combination -h2
    have hHz : H = 0 := poly_eq_zero_of_periodic hH0 hHper
    dsimp [H] at hHz
    exact eq_neg_of_add_eq_zero_left hHz
  have hGodd : G.comp (-X) = -G := by
    apply Polynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
    rw [Polynomial.map_neg, map_comp, Polynomial.map_neg, Polynomial.map_X, hG, mul_comp, C_comp,
      hFodd, mul_neg]
  have hGeven : ∀ d : ℕ, Even d → G.coeff d = 0 := by
    intro d hd
    have h1 := congr_arg (fun P : ℤ[X] => P.coeff d) hGodd
    rw [coeff_neg, coeff_comp_neg_X_int] at h1
    rw [hd.neg_one_pow, one_mul] at h1
    omega
  have hGval : G.eval ((b + c : ℕ) : ℤ) - G.eval (b : ℤ) - G.eval (c : ℤ) =
      ((2 * k + 1).factorial : ℤ) * ((psi k (b + c) : ℤ) - (psi k b : ℤ) - (psi k c : ℤ)) := by
    have hGe : ∀ n : ℕ, ((G.eval (n : ℤ) : ℤ) : ℚ) = ((2 * k + 1).factorial : ℚ) * (psi k n : ℚ) := by
      intro n
      have h1 := congr_arg (fun P : ℚ[X] => P.eval (n : ℚ)) hG
      rw [eval_mul, eval_C, hFeval] at h1
      have h2 := eval_map_int_cast G (n : ℤ)
      simp only [Int.cast_natCast] at h2
      rw [← h2]
      exact h1
    have hq : ((G.eval ((b + c : ℕ) : ℤ) - G.eval (b : ℤ) - G.eval (c : ℤ) : ℤ) : ℚ) =
        (((2 * k + 1).factorial : ℤ) * ((psi k (b + c) : ℤ) - (psi k b : ℤ) - (psi k c : ℤ)) : ℚ) := by
      rw [Int.cast_sub, Int.cast_sub, hGe (b + c), hGe b, hGe c]
      push_cast
      ring
    exact_mod_cast hq
  rw [← hGval]
  rw [eval_eq_sum_range, eval_eq_sum_range, eval_eq_sum_range]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.dvd_sum ?_
  intro d _
  rcases Nat.even_or_odd d with he | ⟨m, rfl⟩
  · rw [hGeven d he]
    simp
  · have hrew : G.coeff (2 * m + 1) * ((b + c : ℕ) : ℤ) ^ (2 * m + 1) -
        G.coeff (2 * m + 1) * (b : ℤ) ^ (2 * m + 1) -
        G.coeff (2 * m + 1) * (c : ℤ) ^ (2 * m + 1) =
        G.coeff (2 * m + 1) * (((b : ℤ) + (c : ℤ)) ^ (2 * m + 1) -
          (b : ℤ) ^ (2 * m + 1) - (c : ℤ) ^ (2 * m + 1)) := by
      push_cast
      ring
    rw [hrew]
    have hdvd := odd_pow_add_sub_dvd (b : ℤ) (c : ℤ) m
    have hcast : (((b + c) * b * c : ℕ) : ℤ) = ((b : ℤ) + (c : ℤ)) * (b : ℤ) * (c : ℤ) := by
      push_cast
      ring
    rw [hcast]
    exact dvd_mul_of_dvd_right hdvd _

/-! ### Section 4: Wolstenholme's theorem for C_1 -/

private lemma zmod_sum_sq_inv_eq_zero {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) :
    ∑ x : ZMod p, (x ^ 2)⁻¹ = 0 := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h0
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h0)
    have hle : p ≤ 2 := Nat.le_of_dvd (by omega) hdvd
    omega
  have h3 : (3 : ZMod p) ≠ 0 := by
    intro h0
    have hdvd : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp (by simpa using h0)
    have hle : p ≤ 3 := Nat.le_of_dvd (by omega) hdvd
    omega
  have hsq : ∑ x : ZMod p, x ^ 2 = 0 := by
    have hbij : ∑ x : ZMod p, ((2 : ZMod p) * x) ^ 2 = ∑ x : ZMod p, x ^ 2 :=
      Equiv.sum_comp (Equiv.mulLeft₀ (2 : ZMod p) h2) (fun x => x ^ 2)
    have h4 : ∑ x : ZMod p, ((2 : ZMod p) * x) ^ 2 = (4 : ZMod p) * ∑ x : ZMod p, x ^ 2 := by
      simp_rw [mul_pow, ← Finset.mul_sum]
      norm_num
    have hmul : (3 : ZMod p) * ∑ x : ZMod p, x ^ 2 = 0 := by
      have hEq : (4 : ZMod p) * ∑ x : ZMod p, x ^ 2 = ∑ x : ZMod p, x ^ 2 := h4.symm.trans hbij
      calc (3 : ZMod p) * ∑ x : ZMod p, x ^ 2
          = (4 : ZMod p) * ∑ x : ZMod p, x ^ 2 - ∑ x : ZMod p, x ^ 2 := by ring
        _ = 0 := sub_eq_zero.mpr hEq
    exact (mul_eq_zero.mp hmul).resolve_left h3
  have hinv_eq : ∑ x : ZMod p, (x ^ 2)⁻¹ = ∑ x : ZMod p, (x⁻¹) ^ 2 := by simp [inv_pow]
  have hinv_bij : ∑ x : ZMod p, (x⁻¹) ^ 2 = ∑ x : ZMod p, x ^ 2 :=
    Equiv.sum_comp (Equiv.inv (ZMod p)) (fun x => x ^ 2)
  rw [hinv_eq, hinv_bij, hsq]

private lemma rat_inv_sum_eq_div {ι : Type*} [DecidableEq ι] {p : ℕ} (hp : p.Prime)
    (s : Finset ι) (b : ι → ℕ) (hb : ∀ i ∈ s, ¬ p ∣ b i) :
    ∃ N D : ℕ, ¬ p ∣ D ∧
      (∑ i ∈ s, ((b i : ℕ) : ℚ)⁻¹) = (N : ℚ) / (D : ℚ) ∧
      (N : ZMod p) = (D : ZMod p) * ∑ i ∈ s, ((b i : ℕ) : ZMod p)⁻¹ := by
  have : Fact p.Prime := ⟨hp⟩
  refine ⟨∑ i ∈ s, ∏ j ∈ s.erase i, b j, ∏ i ∈ s, b i, ?_, ?_, ?_⟩
  · intro h
    rcases (hp.prime.dvd_finsetProd_iff _).mp h with ⟨i, hi, hbi⟩
    exact hb i hi hbi
  · have hD_ne : (∏ i ∈ s, b i : ℕ) ≠ 0 := by
      intro h0
      rcases Finset.prod_eq_zero_iff.mp h0 with ⟨i, hi, hbi⟩
      exact hb i hi (hbi ▸ dvd_zero p)
    rw [eq_div_iff (Nat.cast_ne_zero.mpr hD_ne), Finset.sum_mul]
    push_cast
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hbi_ne : (b i : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (fun h0 => hb i hi (h0 ▸ dvd_zero p))
    rw [← Finset.mul_prod_erase s (fun j => (b j : ℚ)) hi, inv_mul_cancel_left₀ hbi_ne]
  · rw [Finset.mul_sum]
    push_cast
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hbi_ne : ((b i : ℕ) : ZMod p) ≠ 0 := by
      intro h0
      exact hb i hi ((ZMod.natCast_eq_zero_iff (b i) p).mp h0)
    rw [← Finset.mul_prod_erase s (fun j => ((b j : ℕ) : ZMod p)) hi,
      mul_comm ((b i : ℕ) : ZMod p), mul_assoc, mul_inv_cancel₀ hbi_ne, mul_one]

private lemma isPDvdZ_one_C1 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    IsPDvdZ p 1 (∑ t ∈ Finset.Icc 1 ((p - 1) / 2), ((t * (p - t) : ℕ) : ℚ)⁻¹) := by
  have : Fact p.Prime := ⟨hp⟩
  have hp_odd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with rfl | h
    · omega
    · exact h
  set h := (p - 1) / 2
  have hdouble : (2 : ℚ) * ∑ t ∈ Finset.Icc 1 h, ((t * (p - t) : ℕ) : ℚ)⁻¹ =
      ∑ t ∈ Finset.Ico 1 p, ((t * (p - t) : ℕ) : ℚ)⁻¹ := by
    have hsplit : Finset.Ico 1 p = Finset.Icc 1 h ∪ Finset.Icc (h + 1) (p - 1) := by
      ext t
      simp only [Finset.mem_Ico, Finset.mem_union, Finset.mem_Icc]
      omega
    have hdisj : Disjoint (Finset.Icc 1 h) (Finset.Icc (h + 1) (p - 1)) := by
      rw [Finset.disjoint_left]
      intro t ht1 ht2
      rcases Finset.mem_Icc.mp ht1 with ⟨_, _⟩
      rcases Finset.mem_Icc.mp ht2 with ⟨_, _⟩
      omega
    rw [hsplit, Finset.sum_union hdisj]
    have hsym : ∑ t ∈ Finset.Icc (h + 1) (p - 1), ((t * (p - t) : ℕ) : ℚ)⁻¹ =
        ∑ t ∈ Finset.Icc 1 h, ((t * (p - t) : ℕ) : ℚ)⁻¹ := by
      refine Finset.sum_nbij (fun t => p - t) ?_ ?_ ?_ ?_
      · intro t ht
        rcases Finset.mem_Icc.mp ht with ⟨_, _⟩
        exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      · intro t1 ht1 t2 ht2 heq
        dsimp only at heq
        rcases Finset.mem_Icc.mp ht1 with ⟨_, _⟩
        rcases Finset.mem_Icc.mp ht2 with ⟨_, _⟩
        omega
      · intro t ht
        rcases Finset.mem_Icc.mp ht with ⟨_, _⟩
        refine ⟨p - t, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by dsimp; omega⟩
      · intro t ht
        rcases Finset.mem_Icc.mp ht with ⟨_, _⟩
        have hpt : p - (p - t) = t := by omega
        rw [hpt, Nat.mul_comm]
    rw [hsym]
    ring
  have hb : ∀ t ∈ Finset.Ico 1 p, ¬ p ∣ (t * (p - t)) := by
    intro t ht hdvd
    rcases Finset.mem_Ico.mp ht with ⟨h1, h2⟩
    rcases hp.dvd_mul.mp hdvd with ht1 | ht2
    · exact absurd (Nat.le_of_dvd (by omega) ht1) (by omega)
    · exact absurd (Nat.le_of_dvd (by omega) ht2) (by omega)
  rcases rat_inv_sum_eq_div hp (Finset.Ico 1 p) (fun t => t * (p - t)) hb with ⟨N, D, hD, hEq, hZ⟩
  have hsum_z : ∑ t ∈ Finset.Ico 1 p, ((t * (p - t) : ℕ) : ZMod p)⁻¹ = 0 := by
    have hsimp : ∑ t ∈ Finset.Ico 1 p, ((t * (p - t) : ℕ) : ZMod p)⁻¹ =
        - ∑ t ∈ Finset.Ico 1 p, (((t : ℕ) : ZMod p) ^ 2)⁻¹ := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl ?_
      intro t ht
      rcases Finset.mem_Ico.mp ht with ⟨h1, h2⟩
      have hsub : ((p - t : ℕ) : ZMod p) = -((t : ℕ) : ZMod p) := by
        rw [Nat.cast_sub (le_of_lt h2), ZMod.natCast_self, zero_sub]
      rw [Nat.cast_mul, hsub]
      have : ((t : ℕ) : ZMod p) * -((t : ℕ) : ZMod p) = -(((t : ℕ) : ZMod p) ^ 2) := by ring
      rw [this, inv_neg]
    rw [hsimp]
    have hrange : ∑ t ∈ Finset.range p, (((t : ℕ) : ZMod p) ^ 2)⁻¹ =
        ∑ x : ZMod p, (x ^ 2)⁻¹ := by
      refine Finset.sum_nbij (fun t : ℕ => (t : ZMod p)) ?_ ?_ ?_ ?_
      · intro _ _; exact Finset.mem_univ _
      · intro t1 ht1 t2 ht2 heq
        have hval := congr_arg ZMod.val heq
        rwa [ZMod.val_natCast_of_lt (Finset.mem_range.mp ht1),
          ZMod.val_natCast_of_lt (Finset.mem_range.mp ht2)] at hval
      · intro x _
        exact ⟨x.val, Finset.mem_range.mpr (ZMod.val_lt x), ZMod.natCast_zmod_val x⟩
      · intro _ _; rfl
    have hIco : ∑ t ∈ Finset.Ico 1 p, (((t : ℕ) : ZMod p) ^ 2)⁻¹ =
        ∑ t ∈ Finset.range p, (((t : ℕ) : ZMod p) ^ 2)⁻¹ := by
      rw [← Nat.Ico_zero_eq_range, Finset.sum_eq_sum_Ico_succ_bot hp.pos]
      simp
    rw [hIco, hrange, zmod_sum_sq_inv_eq_zero hp5, neg_zero]
  rw [hsum_z, mul_zero] at hZ
  have hpN : p ∣ N := (ZMod.natCast_eq_zero_iff N p).mp hZ
  have h2_ndvd : ¬ p ∣ 2 := fun h => absurd (Nat.le_of_dvd (by omega) h) (by omega)
  have hfull : IsPDvdZ p 1 (∑ t ∈ Finset.Ico 1 p, ((t * (p - t) : ℕ) : ℚ)⁻¹) :=
    ⟨(N : ℤ), (D : ℤ), fun h => hD (Int.ofNat_dvd.mp h),
      Int.ofNat_dvd.mpr (by simpa using hpN), hEq⟩
  have hdiv := isPDvdZ_div_coprime_nat hp h2_ndvd hfull
  have hrew : (∑ t ∈ Finset.Ico 1 p, ((t * (p - t) : ℕ) : ℚ)⁻¹) / ((2 : ℕ) : ℚ) =
      ∑ t ∈ Finset.Icc 1 h, ((t * (p - t) : ℕ) : ℚ)⁻¹ := by
    rw [← hdouble]
    push_cast
    ring
  rw [← hrew]
  exact hdiv

/-! ### Section 5: Kazandzidis's theorem -/

private def epsP (p : ℕ) : ℕ := if p = 3 then 2 else 3

private lemma prod_Ico_pair {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (x : ℕ) :
    (∏ t ∈ Finset.Ico 1 p, ((t + x * p : ℕ) : ℚ) / (t : ℚ)) =
      ∏ t ∈ Finset.Icc 1 ((p - 1) / 2),
        (1 + (p ^ 2 : ℚ) / ((t * (p - t) : ℕ) : ℚ) * ((x * (x + 1) : ℕ) : ℚ)) := by
  have hp_odd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with rfl | h
    · omega
    · exact h
  set h := (p - 1) / 2
  have hsplit : Finset.Ico 1 p = Finset.Icc 1 h ∪ Finset.Icc (h + 1) (p - 1) := by
    ext t
    simp only [Finset.mem_Ico, Finset.mem_union, Finset.mem_Icc]
    omega
  have hdisj : Disjoint (Finset.Icc 1 h) (Finset.Icc (h + 1) (p - 1)) := by
    rw [Finset.disjoint_left]
    intro t ht1 ht2
    rcases Finset.mem_Icc.mp ht1 with ⟨_, _⟩
    rcases Finset.mem_Icc.mp ht2 with ⟨_, _⟩
    omega
  rw [hsplit, Finset.prod_union hdisj]
  have hsym : ∏ t ∈ Finset.Icc (h + 1) (p - 1), ((t + x * p : ℕ) : ℚ) / (t : ℚ) =
      ∏ t ∈ Finset.Icc 1 h, (((p - t) + x * p : ℕ) : ℚ) / ((p - t : ℕ) : ℚ) := by
    refine Finset.prod_nbij (fun t => p - t) ?_ ?_ ?_ ?_
    · intro t ht
      rcases Finset.mem_Icc.mp ht with ⟨_, _⟩
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · intro t1 ht1 t2 ht2 heq
      dsimp only at heq
      rcases Finset.mem_Icc.mp ht1 with ⟨_, _⟩
      rcases Finset.mem_Icc.mp ht2 with ⟨_, _⟩
      omega
    · intro t ht
      rcases Finset.mem_Icc.mp ht with ⟨_, _⟩
      refine ⟨p - t, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by dsimp; omega⟩
    · intro t ht
      rcases Finset.mem_Icc.mp ht with ⟨_, _⟩
      have : p - (p - t) = t := by omega
      rw [this]
  rw [hsym, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl ?_
  intro t ht
  rcases Finset.mem_Icc.mp ht with ⟨ht1, hth⟩
  have ht_lt : t < p := by omega
  have ht_ne : (t : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hpt_ne : ((p - t : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hsub : ((p - t : ℕ) : ℚ) = (p : ℚ) - (t : ℚ) := Nat.cast_sub (le_of_lt ht_lt)
  push_cast
  rw [hsub]
  have hpt_ne' : (p : ℚ) - (t : ℚ) ≠ 0 := by rwa [← hsub]
  field_simp
  ring

private lemma choose_mul_p_ratio_add {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (c b : ℕ) :
    (Nat.choose ((c + b) * p) (b * p) : ℚ) / (Nat.choose (c + b) b : ℚ) =
      ∏ m ∈ Finset.range b,
        (∏ t ∈ Finset.Icc 1 ((p - 1) / 2),
          (1 + (p ^ 2 : ℚ) / ((t * (p - t) : ℕ) : ℚ) * (((c + m) * (c + m + 1) : ℕ) : ℚ))) /
        (∏ t ∈ Finset.Icc 1 ((p - 1) / 2),
          (1 + (p ^ 2 : ℚ) / ((t * (p - t) : ℕ) : ℚ) * ((m * (m + 1) : ℕ) : ℚ))) := by
  induction b with
  | zero => simp
  | succ b ih =>
    have hstep_nat : (b + 1) * Nat.choose (c + (b + 1)) (b + 1) =
        (c + b + 1) * Nat.choose (c + b) b := by
      have h := Nat.add_one_mul_choose_eq (c + b) b
      simpa [Nat.add_assoc, Nat.mul_comm] using h.symm
    have hstep_p : (∏ t ∈ Finset.Ico 1 (p + 1), (b * p + t)) *
        Nat.choose ((c + (b + 1)) * p) ((b + 1) * p) =
        (∏ t ∈ Finset.Ico 1 (p + 1), ((c + b) * p + t)) *
        Nat.choose ((c + b) * p) (b * p) := by
      have hgen : ∀ k : ℕ, (∏ t ∈ Finset.Ico 1 (k + 1), (b * p + t)) *
          Nat.choose ((c + b) * p + k) (b * p + k) =
          (∏ t ∈ Finset.Ico 1 (k + 1), ((c + b) * p + t)) *
          Nat.choose ((c + b) * p) (b * p) := by
        intro k
        induction k with
        | zero => simp
        | succ k ihk =>
          rw [Finset.prod_Ico_succ_top (by omega : 1 ≤ k + 1),
            Finset.prod_Ico_succ_top (by omega : 1 ≤ k + 1)]
          have hch : (b * p + k + 1) * Nat.choose ((c + b) * p + k + 1) (b * p + k + 1) =
              ((c + b) * p + k + 1) * Nat.choose ((c + b) * p + k) (b * p + k) := by
            have h := Nat.add_one_mul_choose_eq ((c + b) * p + k) (b * p + k)
            linarith
          calc (∏ t ∈ Finset.Ico 1 (k + 1), (b * p + t)) * (b * p + (k + 1)) *
                Nat.choose ((c + b) * p + (k + 1)) (b * p + (k + 1))
              = (∏ t ∈ Finset.Ico 1 (k + 1), (b * p + t)) *
                ((b * p + k + 1) * Nat.choose ((c + b) * p + k + 1) (b * p + k + 1)) := by
                  simp only [Nat.add_assoc]; ring
            _ = (∏ t ∈ Finset.Ico 1 (k + 1), (b * p + t)) *
                (((c + b) * p + k + 1) * Nat.choose ((c + b) * p + k) (b * p + k)) := by
                  rw [hch]
            _ = ((c + b) * p + (k + 1)) *
                ((∏ t ∈ Finset.Ico 1 (k + 1), (b * p + t)) *
                  Nat.choose ((c + b) * p + k) (b * p + k)) := by ring
            _ = ((c + b) * p + (k + 1)) *
                ((∏ t ∈ Finset.Ico 1 (k + 1), ((c + b) * p + t)) *
                  Nat.choose ((c + b) * p) (b * p)) := by rw [ihk]
            _ = (∏ t ∈ Finset.Ico 1 (k + 1), ((c + b) * p + t)) * ((c + b) * p + (k + 1)) *
                Nat.choose ((c + b) * p) (b * p) := by ring
      have h1 : (c + (b + 1)) * p = (c + b) * p + p := by ring
      have h2 : (b + 1) * p = b * p + p := by ring
      rw [h1, h2]
      exact hgen p
    have hch_pos1 : (Nat.choose (c + b) b : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.choose_pos (Nat.le_add_left b c)))
    have hch_pos2 : (Nat.choose (c + (b + 1)) (b + 1) : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.choose_pos (Nat.le_add_left (b + 1) c)))
    have hprod_split : ∀ x : ℕ,
        (∏ t ∈ Finset.Ico 1 (p + 1), ((x * p + t : ℕ) : ℚ)) =
          ((x + 1 : ℕ) : ℚ) * (p : ℚ) * (∏ t ∈ Finset.Ico 1 p, ((t + x * p : ℕ) : ℚ)) := by
      intro x
      rw [Finset.prod_Ico_succ_top hp.pos]
      have hlast : ((x * p + p : ℕ) : ℚ) = ((x + 1 : ℕ) : ℚ) * (p : ℚ) := by push_cast; ring
      rw [hlast]
      have hcomm : ∏ t ∈ Finset.Ico 1 p, ((x * p + t : ℕ) : ℚ) =
          ∏ t ∈ Finset.Ico 1 p, ((t + x * p : ℕ) : ℚ) :=
        Finset.prod_congr rfl fun t _ => by rw [Nat.add_comm]
      rw [hcomm]
      ring
    have hIco_ne : ∀ x : ℕ, (∏ t ∈ Finset.Ico 1 p, ((t + x * p : ℕ) : ℚ)) ≠ 0 := by
      intro x
      rw [Finset.prod_ne_zero_iff]
      intro t ht
      have := (Finset.mem_Ico.mp ht).1
      exact Nat.cast_ne_zero.mpr (by omega)
    have hIco_t_ne : (∏ t ∈ Finset.Ico 1 p, (t : ℚ)) ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro t ht
      have := (Finset.mem_Ico.mp ht).1
      exact Nat.cast_ne_zero.mpr (by omega)
    have hp_ne : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
    have hb1_ne : ((b + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hcb1_ne : ((c + b + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hstep_q : (Nat.choose ((c + (b + 1)) * p) ((b + 1) * p) : ℚ) /
        (Nat.choose (c + (b + 1)) (b + 1) : ℚ) =
        ((Nat.choose ((c + b) * p) (b * p) : ℚ) / (Nat.choose (c + b) b : ℚ)) *
        ((∏ t ∈ Finset.Ico 1 p, ((t + (c + b) * p : ℕ) : ℚ) / (t : ℚ)) /
         (∏ t ∈ Finset.Ico 1 p, ((t + b * p : ℕ) : ℚ) / (t : ℚ))) := by
      have h1 : (∏ t ∈ Finset.Ico 1 (p + 1), ((b * p + t : ℕ) : ℚ)) *
          (Nat.choose ((c + (b + 1)) * p) ((b + 1) * p) : ℚ) =
          (∏ t ∈ Finset.Ico 1 (p + 1), (((c + b) * p + t : ℕ) : ℚ)) *
          (Nat.choose ((c + b) * p) (b * p) : ℚ) := by
        exact_mod_cast hstep_p
      have h2 : ((b + 1 : ℕ) : ℚ) * (Nat.choose (c + (b + 1)) (b + 1) : ℚ) =
          ((c + b + 1 : ℕ) : ℚ) * (Nat.choose (c + b) b : ℚ) := by
        exact_mod_cast hstep_nat
      rw [hprod_split b, hprod_split (c + b)] at h1
      have hmain : (Nat.choose ((c + (b + 1)) * p) ((b + 1) * p) : ℚ) *
          (Nat.choose (c + b) b : ℚ) * (∏ t ∈ Finset.Ico 1 p, ((t + b * p : ℕ) : ℚ)) *
          (((b + 1 : ℕ) : ℚ) * (p : ℚ) * ((c + b + 1 : ℕ) : ℚ)) =
          (Nat.choose ((c + b) * p) (b * p) : ℚ) * (Nat.choose (c + (b + 1)) (b + 1) : ℚ) *
          (∏ t ∈ Finset.Ico 1 p, ((t + (c + b) * p : ℕ) : ℚ)) *
          (((b + 1 : ℕ) : ℚ) * (p : ℚ) * ((c + b + 1 : ℕ) : ℚ)) := by
        calc (Nat.choose ((c + (b + 1)) * p) ((b + 1) * p) : ℚ) *
              (Nat.choose (c + b) b : ℚ) * (∏ t ∈ Finset.Ico 1 p, ((t + b * p : ℕ) : ℚ)) *
              (((b + 1 : ℕ) : ℚ) * (p : ℚ) * ((c + b + 1 : ℕ) : ℚ))
            = (((b + 1 : ℕ) : ℚ) * (p : ℚ) * (∏ t ∈ Finset.Ico 1 p, ((t + b * p : ℕ) : ℚ)) *
                (Nat.choose ((c + (b + 1)) * p) ((b + 1) * p) : ℚ)) *
              (((c + b + 1 : ℕ) : ℚ) * (Nat.choose (c + b) b : ℚ)) := by ring
          _ = (((c + b + 1 : ℕ) : ℚ) * (p : ℚ) * (∏ t ∈ Finset.Ico 1 p, ((t + (c + b) * p : ℕ) : ℚ)) *
                (Nat.choose ((c + b) * p) (b * p) : ℚ)) *
              (((b + 1 : ℕ) : ℚ) * (Nat.choose (c + (b + 1)) (b + 1) : ℚ)) := by rw [h1, ← h2]
          _ = (Nat.choose ((c + b) * p) (b * p) : ℚ) * (Nat.choose (c + (b + 1)) (b + 1) : ℚ) *
              (∏ t ∈ Finset.Ico 1 p, ((t + (c + b) * p : ℕ) : ℚ)) *
              (((b + 1 : ℕ) : ℚ) * (p : ℚ) * ((c + b + 1 : ℕ) : ℚ)) := by ring
      have hcancel : ((b + 1 : ℕ) : ℚ) * (p : ℚ) * ((c + b + 1 : ℕ) : ℚ) ≠ 0 :=
        mul_ne_zero (mul_ne_zero hb1_ne hp_ne) hcb1_ne
      have hmain' : (Nat.choose ((c + (b + 1)) * p) ((b + 1) * p) : ℚ) *
          (Nat.choose (c + b) b : ℚ) * (∏ t ∈ Finset.Ico 1 p, ((t + b * p : ℕ) : ℚ)) =
          (Nat.choose ((c + b) * p) (b * p) : ℚ) * (Nat.choose (c + (b + 1)) (b + 1) : ℚ) *
          (∏ t ∈ Finset.Ico 1 p, ((t + (c + b) * p : ℕ) : ℚ)) :=
        mul_right_cancel₀ hcancel hmain
      simp only [Finset.prod_div_distrib]
      have hden1 := hIco_ne b
      have hden2 := hIco_ne (c + b)
      have hdiv_cancel : ((∏ t ∈ Finset.Ico 1 p, ((t + (c + b) * p : ℕ) : ℚ)) /
            ∏ t ∈ Finset.Ico 1 p, (t : ℚ)) /
          ((∏ t ∈ Finset.Ico 1 p, ((t + b * p : ℕ) : ℚ)) /
            ∏ t ∈ Finset.Ico 1 p, (t : ℚ)) =
          (∏ t ∈ Finset.Ico 1 p, ((t + (c + b) * p : ℕ) : ℚ)) /
          (∏ t ∈ Finset.Ico 1 p, ((t + b * p : ℕ) : ℚ)) :=
        div_div_div_cancel_right₀ hIco_t_ne _ _
      rw [hdiv_cancel]
      field_simp
      linarith
    rw [hstep_q, ih, Finset.prod_range_succ, prod_Ico_pair hp hp3 (c + b),
      prod_Ico_pair hp hp3 b]

private lemma legendre_sum_bound {p : ℕ} (hp : p.Prime) (n b : ℕ) :
    (p - 1) * (∑ i ∈ Finset.Ico 1 (b + 1), n / p ^ i) + n / p ^ b ≤ n := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ b + 1), Nat.mul_add]
    have hdiv : p * (n / p ^ (b + 1)) ≤ n / p ^ b := by
      rw [pow_succ, ← Nat.div_div_eq_div_mul]
      exact Nat.mul_div_le (n / p ^ b) p
    have hadd : (p - 1) * (n / p ^ (b + 1)) + n / p ^ (b + 1) = p * (n / p ^ (b + 1)) := by
      cases p with
      | zero => exact absurd hp.ne_zero (by simp)
      | succ p => simp [Nat.succ_mul]
    omega

private lemma legendre_bound {p n : ℕ} (hp : p.Prime) :
    (p - 1) * padicValNat p n.factorial ≤ n := by
  have : Fact p.Prime := ⟨hp⟩
  have hlt : Nat.log p n < n + 1 := Nat.lt_succ_of_le (Nat.log_le_self p n)
  rw [padicValNat_factorial hlt]
  exact le_trans (Nat.le_add_right _ _) (legendre_sum_bound hp n n)

private lemma kazandzidis_exponent_bound {p k : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hk : 2 ≤ k) :
    epsP p + padicValNat p k + padicValNat p (2 * k + 1).factorial ≤ 2 * k := by
  have : Fact p.Prime := ⟨hp⟩
  have hleg := legendre_bound (n := 2 * k + 1) hp
  by_cases hp3eq : p = 3
  · subst hp3eq
    simp only [epsP, ite_true]
    have hfac : padicValNat 3 (2 * k + 1).factorial ≤ k := by omega
    have hvk : padicValNat 3 k ≤ k - 2 := by
      set t := padicValNat 3 k
      by_cases ht : t = 0
      · omega
      · have hpow : 3 ^ t ≤ k := Nat.le_of_dvd (by omega) pow_padicValNat_dvd
        have h3t := three_pow_ge_add_two t (by omega)
        omega
    omega
  · have hp5 : 5 ≤ p := by
      have hp4 : p ≠ 4 := fun h => by subst h; exact absurd hp (by decide)
      omega
    simp only [epsP, if_neg hp3eq]
    have hleg4 : 4 * padicValNat p (2 * k + 1).factorial ≤ 2 * k + 1 :=
      le_trans (Nat.mul_le_mul_right _ (by omega : 4 ≤ p - 1)) hleg
    by_cases hk2 : k = 2
    · subst hk2
      have hvk : padicValNat p 2 = 0 :=
        padicValNat.eq_zero_of_not_dvd (fun h => absurd (Nat.le_of_dvd (by omega) h) (by omega))
      omega
    · have hk3 : 3 ≤ k := by omega
      have hvk : 2 * padicValNat p k ≤ k := by
        set t := padicValNat p k
        have hpow : 5 ^ t ≤ k :=
          le_trans (Nat.pow_le_pow_left hp5 t) (Nat.le_of_dvd (by omega) pow_padicValNat_dvd)
        have h5t := five_pow_ge_two_mul t
        omega
      omega

private lemma psi_shift_eq (k b c : ℕ) :
    (∑ m ∈ Finset.range b, ((c + m) * (c + m + 1)) ^ k) + psi k c = psi k (b + c) := by
  induction b with
  | zero => simp [psi]
  | succ b ih =>
    rw [Finset.sum_range_succ, Nat.succ_add]
    have hpsi : psi k (b + c + 1) = psi k (b + c) + ((b + c) * (b + c + 1)) ^ k := by
      unfold psi
      exact Finset.sum_range_succ _ (b + c)
    rw [hpsi, Nat.add_comm c b]
    linarith

private lemma kazandzidis {p a b : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (_hb : 0 < b) (hba : b < a) :
    padicValNat p (Nat.choose (a * p) (b * p)) = padicValNat p (Nat.choose a b) ∧
    ((p ^ (epsP p + padicValNat p a + padicValNat p b + padicValNat p (a - b) +
        padicValNat p (Nat.choose a b)) : ℕ) : ℤ) ∣
      (Nat.choose (a * p) (b * p) : ℤ) - (Nat.choose a b : ℤ) := by
  have : Fact p.Prime := ⟨hp⟩
  set c := a - b
  have hc : 0 < c := by omega
  have ha : a = c + b := (Nat.sub_add_cancel (le_of_lt hba)).symm
  set h := (p - 1) / 2
  set K := epsP p + padicValNat p a + padicValNat p b + padicValNat p c
  set f : ℕ → ℕ → ℚ := fun x t => (p ^ 2 : ℚ) / ((t * (p - t) : ℕ) : ℚ) * ((x * (x + 1) : ℕ) : ℚ)
  have hf2 : ∀ x : ℕ, ∀ t ∈ Finset.Icc 1 h, IsPDvdZ p 2 (f x t) := by
    intro x t ht
    rcases Finset.mem_Icc.mp ht with ⟨ht1, hth⟩
    have ht_lt : t < p := by omega
    have hndvd : ¬ p ∣ (t * (p - t)) := by
      intro hdvd
      rcases hp.dvd_mul.mp hdvd with h1 | h2
      · exact absurd (Nat.le_of_dvd (by omega) h1) (by omega)
      · exact absurd (Nat.le_of_dvd (by omega) h2) (by omega)
    have hnum : IsPDvdZ p 2 ((p ^ 2 : ℚ) * ((x * (x + 1) : ℕ) : ℚ)) := by
      have h1 : IsPDvdZ p 2 ((p ^ 2 : ℕ) : ℚ) := isPDvdZ_natCast hp (p ^ 2) dvd_rfl
      have h2 := isPDvdZ_natCast_zero hp (x * (x + 1))
      simpa using isPDvdZ_mul hp h1 h2
    have hdiv := isPDvdZ_div_coprime_nat hp hndvd hnum
    have hrew : ((p ^ 2 : ℚ) * ((x * (x + 1) : ℕ) : ℚ)) / ((t * (p - t) : ℕ) : ℚ) = f x t := by
      dsimp [f]; ring
    rwa [hrew] at hdiv
  set g : ℕ → ℚ := fun m =>
    (∏ t ∈ Finset.Icc 1 h, (1 + f (c + m) t)) / (∏ t ∈ Finset.Icc 1 h, (1 + f m t)) - 1
  have hg : ∀ m ∈ Finset.range b, IsPDvdZ p 2 (g m) ∧
      IsPDvdZ p K (truncLog K (g m) -
        (∑ t ∈ Finset.Icc 1 h, truncLog K (f (c + m) t) - ∑ t ∈ Finset.Icc 1 h, truncLog K (f m t))) := by
    intro m _
    rcases isPDvdZ_truncLog_prod (K := K) hp (Finset.Icc 1 h) (f (c + m)) (hf2 (c + m)) with ⟨hu2, hlogu⟩
    rcases isPDvdZ_truncLog_prod (K := K) hp (Finset.Icc 1 h) (f m) (hf2 m) with ⟨hv2, hlogv⟩
    rcases isPDvdZ_truncLog_div (K := K) hp hu2 hv2 with ⟨hdiv2, hlogdiv⟩
    have h1u : 1 + ((∏ t ∈ Finset.Icc 1 h, (1 + f (c + m) t)) - 1) =
        ∏ t ∈ Finset.Icc 1 h, (1 + f (c + m) t) := by ring
    have h1v : 1 + ((∏ t ∈ Finset.Icc 1 h, (1 + f m t)) - 1) =
        ∏ t ∈ Finset.Icc 1 h, (1 + f m t) := by ring
    rw [h1u, h1v] at hdiv2 hlogdiv
    refine ⟨hdiv2, ?_⟩
    have hrew : truncLog K (g m) -
        (∑ t ∈ Finset.Icc 1 h, truncLog K (f (c + m) t) - ∑ t ∈ Finset.Icc 1 h, truncLog K (f m t)) =
        (truncLog K (g m) - (truncLog K ((∏ t ∈ Finset.Icc 1 h, (1 + f (c + m) t)) - 1) -
          truncLog K ((∏ t ∈ Finset.Icc 1 h, (1 + f m t)) - 1))) +
        ((truncLog K ((∏ t ∈ Finset.Icc 1 h, (1 + f (c + m) t)) - 1) -
          ∑ t ∈ Finset.Icc 1 h, truncLog K (f (c + m) t)) -
        (truncLog K ((∏ t ∈ Finset.Icc 1 h, (1 + f m t)) - 1) -
          ∑ t ∈ Finset.Icc 1 h, truncLog K (f m t))) := by
      dsimp [g]; ring
    rw [hrew]
    exact isPDvdZ_add hp hlogdiv (isPDvdZ_sub hp hlogu hlogv)
  set R : ℚ := (Nat.choose (a * p) (b * p) : ℚ) / (Nat.choose a b : ℚ)
  have hR_eq : R = ∏ m ∈ Finset.range b, (1 + g m) := by
    dsimp [R, g, f]
    rw [ha, choose_mul_p_ratio_add hp hp3 c b]
    refine Finset.prod_congr rfl ?_
    intro m _
    ring
  rcases isPDvdZ_truncLog_prod (K := K) hp (Finset.range b) g (fun m hm => (hg m hm).1) with ⟨hR2, hlogR⟩
  rw [← hR_eq] at hR2 hlogR
  -- First conclusion: padicValNat p C(ap,bp) = padicValNat p C(a,b)
  have hval_eq : padicValNat p (Nat.choose (a * p) (b * p)) = padicValNat p (Nat.choose a b) := by
    rcases hR2 with ⟨N, D, hD, hN, hRm1⟩
    have hpN : (p : ℤ) ∣ N := dvd_trans (Int.ofNat_dvd.mpr (dvd_pow_self p (by omega : 2 ≠ 0))) hN
    have hDN : ¬ (p : ℤ) ∣ (D + N) := fun h => hD ((dvd_add_left hpN).mp h)
    have hD_ne : (D : ℚ) ≠ 0 := rat_ne_zero_of_not_dvd hD
    have hch_ne : (Nat.choose a b : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.choose_pos (le_of_lt hba)))
    have hR1 : R = ((D + N : ℤ) : ℚ) / (D : ℚ) := by
      have : R = 1 + (R - 1) := by ring
      rw [this, hRm1]
      push_cast
      field_simp
    have hq_eq : (Nat.choose (a * p) (b * p) : ℚ) * (D : ℚ) =
        (Nat.choose a b : ℚ) * ((D + N : ℤ) : ℚ) := by
      have h1 : (Nat.choose (a * p) (b * p) : ℚ) / (Nat.choose a b : ℚ) =
          ((D + N : ℤ) : ℚ) / (D : ℚ) := hR1
      exact ((div_eq_div_iff hch_ne hD_ne).mp h1).trans (mul_comm _ _)
    have hz_eq : (Nat.choose (a * p) (b * p) : ℤ) * D = (Nat.choose a b : ℤ) * (D + N) := by
      exact_mod_cast hq_eq
    have hnat_eq : Nat.choose (a * p) (b * p) * D.natAbs =
        Nat.choose a b * (D + N).natAbs := by
      have := congr_arg Int.natAbs hz_eq
      simpa [Int.natAbs_mul] using this
    have hch1_ne : Nat.choose (a * p) (b * p) ≠ 0 :=
      Nat.ne_of_gt (Nat.choose_pos (Nat.mul_le_mul_right p (le_of_lt hba)))
    have hch2_ne : Nat.choose a b ≠ 0 := Nat.ne_of_gt (Nat.choose_pos (le_of_lt hba))
    have hD_abs_ndvd : ¬ p ∣ D.natAbs := fun h => hD (Int.natCast_dvd.mpr h)
    have hDN_abs_ndvd : ¬ p ∣ (D + N).natAbs := fun h => hDN (Int.natCast_dvd.mpr h)
    have hD_abs_ne : D.natAbs ≠ 0 := fun h => hD_abs_ndvd (h ▸ dvd_zero p)
    have hDN_abs_ne : (D + N).natAbs ≠ 0 := fun h => hDN_abs_ndvd (h ▸ dvd_zero p)
    have hv := congr_arg (padicValNat p) hnat_eq
    rw [padicValNat.mul hch1_ne hD_abs_ne, padicValNat.mul hch2_ne hDN_abs_ne,
      padicValNat.eq_zero_of_not_dvd hD_abs_ndvd,
      padicValNat.eq_zero_of_not_dvd hDN_abs_ndvd, add_zero, add_zero] at hv
    exact hv
  -- Second conclusion: prove IsPDvdZ p K (truncLog K (R - 1))
  have hsum_diff : IsPDvdZ p K (∑ m ∈ Finset.range b,
      (∑ t ∈ Finset.Icc 1 h, truncLog K (f (c + m) t) -
       ∑ t ∈ Finset.Icc 1 h, truncLog K (f m t))) := by
    have hswap : (∑ m ∈ Finset.range b,
        (∑ t ∈ Finset.Icc 1 h, truncLog K (f (c + m) t) -
         ∑ t ∈ Finset.Icc 1 h, truncLog K (f m t))) =
        ∑ k ∈ Finset.Icc 1 K,
          ((-1 : ℚ) ^ (k - 1) / (k : ℚ)) * ((p ^ (2 * k) : ℕ) : ℚ) *
          (∑ t ∈ Finset.Icc 1 h, (((t * (p - t) : ℕ) : ℚ)⁻¹) ^ k) *
          (((psi k (b + c) : ℤ) - (psi k b : ℤ) - (psi k c : ℤ) : ℤ) : ℚ) := by
      have hterm : ∀ m : ℕ,
          (∑ t ∈ Finset.Icc 1 h, truncLog K (f (c + m) t) -
           ∑ t ∈ Finset.Icc 1 h, truncLog K (f m t)) =
          ∑ k ∈ Finset.Icc 1 K,
            ((-1 : ℚ) ^ (k - 1) / (k : ℚ)) * ((p ^ (2 * k) : ℕ) : ℚ) *
            (∑ t ∈ Finset.Icc 1 h, (((t * (p - t) : ℕ) : ℚ)⁻¹) ^ k) *
            ((((c + m) * (c + m + 1)) ^ k : ℕ) - ((m * (m + 1)) ^ k : ℕ) : ℚ) := by
        intro m
        rw [← Finset.sum_sub_distrib]
        simp only [truncLog]
        simp_rw [← Finset.sum_sub_distrib]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl ?_
        intro k _
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl ?_
        intro t _
        dsimp [f]
        have hp2k : ((p ^ (2 * k) : ℕ) : ℚ) = ((p ^ 2 : ℚ)) ^ k := by
          rw [pow_mul]; push_cast; ring
        rw [hp2k]
        push_cast
        simp only [div_eq_mul_inv, mul_pow]
        ring
      simp_rw [hterm]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro k _
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_sub_distrib]
      have hsh : (∑ m ∈ Finset.range b, ((((c + m) * (c + m + 1)) ^ k : ℕ) : ℚ)) =
          (psi k (b + c) : ℚ) - (psi k c : ℚ) := by
        have h1 : (∑ m ∈ Finset.range b, ((c + m) * (c + m + 1)) ^ k) + psi k c = psi k (b + c) :=
          psi_shift_eq k b c
        have h2 : (∑ m ∈ Finset.range b, ((((c + m) * (c + m + 1)) ^ k : ℕ) : ℚ)) + (psi k c : ℚ) =
            (psi k (b + c) : ℚ) := by exact_mod_cast h1
        linarith
      have hpsib : (∑ m ∈ Finset.range b, (((m * (m + 1)) ^ k : ℕ) : ℚ)) = (psi k b : ℚ) := by
        dsimp [psi]; push_cast; rfl
      rw [hsh, hpsib]
      push_cast
      ring
    rw [hswap]
    refine isPDvdZ_sum hp _ _ ?_
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hCk0 : IsPDvdZ p 0 (∑ t ∈ Finset.Icc 1 h, (((t * (p - t) : ℕ) : ℚ)⁻¹) ^ k) := by
      refine isPDvdZ_sum hp _ _ ?_
      intro t ht
      rcases Finset.mem_Icc.mp ht with ⟨ht1, hth⟩
      have hndvd : ¬ p ∣ (t * (p - t)) := by
        intro hdvd
        rcases hp.dvd_mul.mp hdvd with h1 | h2
        · exact absurd (Nat.le_of_dvd (by omega) h1) (by omega)
        · exact absurd (Nat.le_of_dvd (by omega) h2) (by omega)
      have h1 : IsPDvdZ p 0 (((t * (p - t) : ℕ) : ℚ)⁻¹) := by
        have := isPDvdZ_div_coprime_nat hp hndvd (isPDvdZ_natCast_zero hp 1)
        simpa using this
      simpa using isPDvdZ_pow hp h1 k
    have habc_dvd : p ^ (padicValNat p a + padicValNat p b + padicValNat p c) ∣ a * b * c := by
      have ha1 : p ^ padicValNat p a ∣ a := pow_padicValNat_dvd
      have hb1 : p ^ padicValNat p b ∣ b := pow_padicValNat_dvd
      have hc1 : p ^ padicValNat p c ∣ c := pow_padicValNat_dvd
      rw [pow_add, pow_add]
      exact mul_dvd_mul (mul_dvd_mul ha1 hb1) hc1
    by_cases hk_eq1 : k = 1
    · subst hk_eq1
      rw [psi_one_diff b c]
      have habc_eq : (b + c) * b * c = a * b * c := by rw [ha, Nat.add_comm]
      rw [habc_eq]
      simp only [Nat.sub_self, pow_zero, Nat.cast_one, div_one, one_mul, Nat.mul_one, pow_one]
      have hp2 : IsPDvdZ p 2 ((p ^ 2 : ℕ) : ℚ) := isPDvdZ_natCast hp (p ^ 2) dvd_rfl
      have habc_p : IsPDvdZ p (padicValNat p a + padicValNat p b + padicValNat p c)
          (((a * b * c : ℕ) : ℤ) : ℚ) := by
        simpa using isPDvdZ_natCast hp (a * b * c) habc_dvd
      by_cases hp3eq : p = 3
      · have hKeq : 2 + 0 + (padicValNat p a + padicValNat p b + padicValNat p c) = K := by
          dsimp [K, epsP]; rw [if_pos hp3eq]; omega
        have hmul := isPDvdZ_mul hp (isPDvdZ_mul hp hp2 hCk0) habc_p
        simpa [hKeq] using hmul
      · have hp5 : 5 ≤ p := by
          have hp4 : p ≠ 4 := fun h => by subst h; exact absurd hp (by decide)
          omega
        have hC1 := isPDvdZ_one_C1 hp hp5
        have hKeq : 2 + 1 + (padicValNat p a + padicValNat p b + padicValNat p c) = K := by
          dsimp [K, epsP]; rw [if_neg hp3eq]; omega
        have hmul := isPDvdZ_mul hp (isPDvdZ_mul hp hp2 hC1) habc_p
        simpa [hKeq] using hmul
    · have hk2 : 2 ≤ k := by omega
      have hpsi_dvd : (((a * b * c : ℕ) : ℤ)) ∣
          ((2 * k + 1).factorial : ℤ) * ((psi k (b + c) : ℤ) - (psi k b : ℤ) - (psi k c : ℤ)) := by
        have h1 := dvd_factorial_psi k b c hk1
        have habc_eq : (b + c) * b * c = a * b * c := by rw [ha, Nat.add_comm]
        rwa [habc_eq] at h1
      have hfac_psi : IsPDvdZ p (padicValNat p a + padicValNat p b + padicValNat p c)
          ((((2 * k + 1).factorial : ℤ) * ((psi k (b + c) : ℤ) - (psi k b : ℤ) - (psi k c : ℤ)) : ℤ) : ℚ) :=
        isPDvdZ_intCast hp _ (dvd_trans (Int.ofNat_dvd.mpr habc_dvd) hpsi_dvd)
      have hnum : IsPDvdZ p (2 * k + (padicValNat p a + padicValNat p b + padicValNat p c))
          (((-1 : ℚ) ^ (k - 1)) * ((p ^ (2 * k) : ℕ) : ℚ) *
            (∑ t ∈ Finset.Icc 1 h, (((t * (p - t) : ℕ) : ℚ)⁻¹) ^ k) *
            ((((2 * k + 1).factorial : ℤ) * ((psi k (b + c) : ℤ) - (psi k b : ℤ) - (psi k c : ℤ)) : ℤ) : ℚ)) := by
        have h1 := isPDvdZ_mul hp (isPDvdZ_neg_one_pow hp (k - 1)) (isPDvdZ_natCast hp (p ^ (2 * k)) dvd_rfl)
        have h2 := isPDvdZ_mul hp h1 hCk0
        have h3 := isPDvdZ_mul hp h2 hfac_psi
        simpa [Nat.zero_add, Nat.add_zero] using h3
      have hkd_ne : k * (2 * k + 1).factorial ≠ 0 :=
        mul_ne_zero (by omega) (Nat.factorial_ne_zero _)
      have hval_kd : padicValNat p (k * (2 * k + 1).factorial) =
          padicValNat p k + padicValNat p (2 * k + 1).factorial :=
        padicValNat.mul (by omega) (Nat.factorial_ne_zero _)
      have hle : K + padicValNat p (k * (2 * k + 1).factorial) ≤
          2 * k + (padicValNat p a + padicValNat p b + padicValNat p c) := by
        rw [hval_kd]
        have hkb := kazandzidis_exponent_bound hp hp3 hk2
        dsimp [K]
        omega
      have hdiv := isPDvdZ_div_nat hp hkd_ne (isPDvdZ_mono hle hnum)
      have hfac_ne : ((2 * k + 1).factorial : ℚ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      have hrew : ((-1 : ℚ) ^ (k - 1) * ((p ^ (2 * k) : ℕ) : ℚ) *
            (∑ t ∈ Finset.Icc 1 h, (((t * (p - t) : ℕ) : ℚ)⁻¹) ^ k) *
            ((((2 * k + 1).factorial : ℤ) *
              ((psi k (b + c) : ℤ) - (psi k b : ℤ) - (psi k c : ℤ)) : ℤ) : ℚ)) /
            ((k * (2 * k + 1).factorial : ℕ) : ℚ) =
          ((-1 : ℚ) ^ (k - 1) / (k : ℚ)) * ((p ^ (2 * k) : ℕ) : ℚ) *
            (∑ t ∈ Finset.Icc 1 h, (((t * (p - t) : ℕ) : ℚ)⁻¹) ^ k) *
            (((psi k (b + c) : ℤ) - (psi k b : ℤ) - (psi k c : ℤ) : ℤ) : ℚ) := by
        push_cast
        field_simp
      rwa [hrew] at hdiv
  have hlogR_K : IsPDvdZ p K (truncLog K (R - 1)) := by
    have hsum_g : IsPDvdZ p K (∑ m ∈ Finset.range b, truncLog K (g m) -
        ∑ m ∈ Finset.range b, (∑ t ∈ Finset.Icc 1 h, truncLog K (f (c + m) t) -
          ∑ t ∈ Finset.Icc 1 h, truncLog K (f m t))) := by
      rw [← Finset.sum_sub_distrib]
      exact isPDvdZ_sum hp _ _ fun m hm => (hg m hm).2
    have hrew : truncLog K (R - 1) =
        (truncLog K (R - 1) - ∑ m ∈ Finset.range b, truncLog K (g m)) +
        ((∑ m ∈ Finset.range b, truncLog K (g m) -
          ∑ m ∈ Finset.range b, (∑ t ∈ Finset.Icc 1 h, truncLog K (f (c + m) t) -
            ∑ t ∈ Finset.Icc 1 h, truncLog K (f m t))) +
        ∑ m ∈ Finset.range b, (∑ t ∈ Finset.Icc 1 h, truncLog K (f (c + m) t) -
          ∑ t ∈ Finset.Icc 1 h, truncLog K (f m t))) := by ring
    rw [hrew]
    exact isPDvdZ_add hp hlogR (isPDvdZ_add hp hsum_g hsum_diff)
  have hRm1_K : IsPDvdZ p K (R - 1) := isPDvdZ_of_truncLog hp hp3 hR2 hlogR_K
  have hch_p : IsPDvdZ p (padicValNat p (Nat.choose a b)) (Nat.choose a b : ℚ) :=
    isPDvdZ_natCast hp (Nat.choose a b) pow_padicValNat_dvd
  have hprod_K : IsPDvdZ p (K + padicValNat p (Nat.choose a b)) ((R - 1) * (Nat.choose a b : ℚ)) :=
    isPDvdZ_mul hp hRm1_K hch_p
  have hch_ne : (Nat.choose a b : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.choose_pos (le_of_lt hba)))
  have hprod_eq : (R - 1) * (Nat.choose a b : ℚ) =
      (((Nat.choose (a * p) (b * p) : ℤ) - (Nat.choose a b : ℤ)) : ℚ) := by
    dsimp [R]
    push_cast
    field_simp
  rw [hprod_eq] at hprod_K
  exact ⟨hval_eq, isPDvdZ_dvd_int hp (by push_cast; exact hprod_K)⟩

/-! ### Section 6: Proof of OMA.S_oeis_a370097.main -/

private def T (m k : ℕ) : ℕ :=
  Nat.choose (3 * m) k * Nat.choose (3 * m - k - 1) (m - k)

private lemma choose_three_mul_identity (m k : ℕ) (hm : 1 ≤ m) (hk : k ≤ m) :
    (3 * m - k) * Nat.choose (3 * m - k - 1) (m - k) = 2 * m * Nat.choose (3 * m - k) (m - k) := by
  have h1 : 3 * m - k - 1 = (3 * m - k - 1) := rfl
  have hsub : 3 * m - k - 1 - (m - k) = 2 * m - 1 := by omega
  have hsym1 : Nat.choose (3 * m - k - 1) (m - k) = Nat.choose (3 * m - k - 1) (2 * m - 1) := by
    rw [← Nat.choose_symm (by omega : m - k ≤ 3 * m - k - 1), hsub]
  have hsym2 : Nat.choose (3 * m - k) (m - k) = Nat.choose (3 * m - k) (2 * m) := by
    rw [← Nat.choose_symm (by omega : m - k ≤ 3 * m - k)]
    congr 1; omega
  rw [hsym1, hsym2]
  have h := Nat.add_one_mul_choose_eq (3 * m - k - 1) (2 * m - 1)
  have heq1 : 3 * m - k - 1 + 1 = 3 * m - k := by omega
  have heq2 : 2 * m - 1 + 1 = 2 * m := by omega
  rw [heq1, heq2] at h
  linarith

private lemma choose_mul_choose_eq (m k : ℕ) (hk : k ≤ m) :
    Nat.choose (3 * m) k * Nat.choose (3 * m - k) (m - k) =
      Nat.choose (3 * m) m * Nat.choose m k :=
  (Nat.choose_mul (n := 3 * m) (k := m) (s := k) hk).symm

private lemma T_identity (m k : ℕ) (hm : 1 ≤ m) (hk : k ≤ m) :
    (3 * m - k) * T m k = 2 * m * Nat.choose (3 * m) m * Nat.choose m k := by
  unfold T
  calc (3 * m - k) * (Nat.choose (3 * m) k * Nat.choose (3 * m - k - 1) (m - k))
      = Nat.choose (3 * m) k * ((3 * m - k) * Nat.choose (3 * m - k - 1) (m - k)) := by ring
    _ = Nat.choose (3 * m) k * (2 * m * Nat.choose (3 * m - k) (m - k)) := by
          rw [choose_three_mul_identity m k hm hk]
    _ = 2 * m * (Nat.choose (3 * m) k * Nat.choose (3 * m - k) (m - k)) := by ring
    _ = 2 * m * (Nat.choose (3 * m) m * Nat.choose m k) := by rw [choose_mul_choose_eq m k hk]
    _ = 2 * m * Nat.choose (3 * m) m * Nat.choose m k := by ring

private lemma padicValNat_choose_ge_sub {p n k : ℕ} (hp : p.Prime) (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    padicValNat p n - padicValNat p k ≤ padicValNat p (Nat.choose n k) := by
  have : Fact p.Prime := ⟨hp⟩
  have hn1 : 1 ≤ n := by omega
  have h := Nat.add_one_mul_choose_eq (n - 1) (k - 1)
  have h1 : n - 1 + 1 = n := by omega
  have h2 : k - 1 + 1 = k := by omega
  rw [h1, h2] at h
  have hch1 : Nat.choose (n - 1) (k - 1) ≠ 0 := Nat.ne_of_gt (Nat.choose_pos (by omega))
  have hch2 : Nat.choose n k ≠ 0 := Nat.ne_of_gt (Nat.choose_pos hkn)
  have hv := congr_arg (padicValNat p) h
  rw [padicValNat.mul (by omega) hch1, padicValNat.mul hch2 (by omega)] at hv
  omega

private lemma padicValNat_choose_three_mul {p m : ℕ} (hp : p.Prime) (hm : 1 ≤ m) :
    padicValNat p 3 ≤ padicValNat p (Nat.choose (3 * m) m) := by
  have : Fact p.Prime := ⟨hp⟩
  have h := Nat.add_one_mul_choose_eq (3 * m - 1) (m - 1)
  have h1 : 3 * m - 1 + 1 = 3 * m := by omega
  have h2 : m - 1 + 1 = m := by omega
  rw [h1, h2] at h
  have h3 : Nat.choose (3 * m) m = 3 * Nat.choose (3 * m - 1) (m - 1) := by
    have : 3 * m * Nat.choose (3 * m - 1) (m - 1) = (3 * Nat.choose (3 * m - 1) (m - 1)) * m := by ring
    rw [this] at h
    exact (Nat.mul_right_cancel (by omega : 0 < m) h).symm
  rw [h3, padicValNat.mul (by omega) (Nat.ne_of_gt (Nat.choose_pos (by omega)))]
  omega

private lemma epsP_add_padicValNat_three {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) :
    epsP p + padicValNat p 3 = 3 := by
  have : Fact p.Prime := ⟨hp⟩
  by_cases h3 : p = 3
  · subst h3
    simp [epsP]
  · simp only [epsP, if_neg h3]
    have hndvd : ¬ p ∣ 3 := fun h => by
      have := Nat.le_of_dvd (by omega) h
      omega
    rw [padicValNat.eq_zero_of_not_dvd hndvd]

private lemma S_ndiv_dvd {p M : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hM : 1 ≤ M) :
    IsPDvdZ p (3 * (padicValNat p M + 1))
      (∑ k ∈ (Finset.range (p * M + 1)).filter (fun k => ¬ p ∣ k), (T (p * M) k : ℚ)) := by
  have : Fact p.Prime := ⟨hp⟩
  set N := p * M
  set s := padicValNat p M
  have hN1 : 1 ≤ N := by
    have := hp.pos
    exact Nat.mul_pos this hM
  have hvN : padicValNat p N = s + 1 := by
    dsimp [N, s]
    rw [padicValNat.mul hp.ne_zero (by omega), padicValNat.self hp.one_lt]
    omega
  set S := (Finset.range (N + 1)).filter (fun k => ¬ p ∣ k)
  have hpair_sum : (2 : ℚ) * ∑ k ∈ S, (T N k : ℚ) =
      ∑ k ∈ S, ((T N k : ℚ) + (T N (N - k) : ℚ)) := by
    rw [Finset.sum_add_distrib]
    have hrev : ∑ k ∈ S, (T N (N - k) : ℚ) = ∑ k ∈ S, (T N k : ℚ) := by
      refine Finset.sum_nbij (fun k => N - k) ?_ ?_ ?_ ?_
      · intro k hk
        rcases Finset.mem_filter.mp hk with ⟨hkr, hkp⟩
        have hkle : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hkr)
        refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩
        intro hdvd
        have hN_dvd : p ∣ N := dvd_mul_right p M
        have : p ∣ k := by
          have hadd : (N - k) + k = N := Nat.sub_add_cancel hkle
          exact (Nat.dvd_add_right hdvd).mp (hadd.symm ▸ hN_dvd)
        exact hkp this
      · intro k1 hk1 k2 hk2 heq
        dsimp only at heq
        have h1 : k1 ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hk1).1)
        have h2 : k2 ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hk2).1)
        omega
      · intro k hk
        rcases Finset.mem_filter.mp hk with ⟨hkr, hkp⟩
        have hkle : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hkr)
        refine ⟨N - k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩, by dsimp; omega⟩
        intro hdvd
        have hN_dvd : p ∣ N := dvd_mul_right p M
        have hadd : (N - k) + k = N := Nat.sub_add_cancel hkle
        exact hkp ((Nat.dvd_add_right hdvd).mp (hadd.symm ▸ hN_dvd))
      · intro _ _; rfl
    rw [hrev]
    ring
  have h2_ndvd : ¬ p ∣ 2 := fun h => absurd (Nat.le_of_dvd (by omega) h) (by omega)
  suffices hdouble : IsPDvdZ p (3 * (s + 1)) (∑ k ∈ S, ((T N k : ℚ) + (T N (N - k) : ℚ))) by
    have hdiv := isPDvdZ_div_coprime_nat hp h2_ndvd hdouble
    have hrew : (∑ k ∈ S, ((T N k : ℚ) + (T N (N - k) : ℚ))) / ((2 : ℕ) : ℚ) =
        ∑ k ∈ S, (T N k : ℚ) := by
      rw [← hpair_sum]
      push_cast
      ring
    rwa [hrew] at hdiv
  refine isPDvdZ_sum hp S _ ?_
  intro k hk
  rcases Finset.mem_filter.mp hk with ⟨hkr, hkp⟩
  have hkle : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hkr)
  have hk1 : 1 ≤ k := by
    by_contra h0
    have : k = 0 := by omega
    exact hkp (this ▸ dvd_zero p)
  have h1 := T_identity N k hN1 hkle
  have h2 := T_identity N (N - k) hN1 (Nat.sub_le N k)
  have hsub2 : 3 * N - (N - k) = 2 * N + k := by omega
  rw [hsub2, Nat.choose_symm hkle] at h2
  have h1q : ((3 * N - k : ℕ) : ℚ) * (T N k : ℚ) =
      (2 * N * Nat.choose (3 * N) N * Nat.choose N k : ℕ) := by exact_mod_cast h1
  have h2q : ((2 * N + k : ℕ) : ℚ) * (T N (N - k) : ℚ) =
      (2 * N * Nat.choose (3 * N) N * Nat.choose N k : ℕ) := by exact_mod_cast h2
  have hd1_ne : ((3 * N - k : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hd2_ne : ((2 * N + k : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hsum_eq : (T N k : ℚ) + (T N (N - k) : ℚ) =
      ((10 * N ^ 2 * Nat.choose (3 * N) N * Nat.choose N k : ℕ) : ℚ) /
        (((3 * N - k) * (2 * N + k) : ℕ) : ℚ) := by
    have hT1 : (T N k : ℚ) = ((2 * N * Nat.choose (3 * N) N * Nat.choose N k : ℕ) : ℚ) /
        ((3 * N - k : ℕ) : ℚ) := (eq_div_iff hd1_ne).mpr (by linarith)
    have hT2 : (T N (N - k) : ℚ) = ((2 * N * Nat.choose (3 * N) N * Nat.choose N k : ℕ) : ℚ) /
        ((2 * N + k : ℕ) : ℚ) := (eq_div_iff hd2_ne).mpr (by linarith)
    rw [hT1, hT2]
    have hadd_den : ((3 * N - k : ℕ) : ℚ) + ((2 * N + k : ℕ) : ℚ) = 5 * (N : ℚ) := by
      have : (3 * N - k) + (2 * N + k) = 5 * N := by omega
      exact_mod_cast this
    push_cast
    field_simp
    have hcast1 : ((3 * N - k : ℕ) : ℚ) = 3 * (N : ℚ) - (k : ℚ) := by
      rw [Nat.cast_sub (by omega : k ≤ 3 * N)]
      push_cast; ring
    rw [hcast1]
    ring
  rw [hsum_eq]
  have hden_ndvd : ¬ p ∣ (3 * N - k) * (2 * N + k) := by
    intro hdvd
    have hN_dvd : p ∣ N := dvd_mul_right p M
    rcases hp.dvd_mul.mp hdvd with h1' | h2'
    · have : p ∣ k := (Nat.dvd_add_right h1').mp (by
        have heq : (3 * N - k) + k = 3 * N := by omega
        rw [heq]; exact dvd_mul_of_dvd_right hN_dvd 3)
      exact hkp this
    · have : p ∣ k := (Nat.dvd_add_right (dvd_mul_of_dvd_right hN_dvd 2)).mp h2'
      exact hkp this
  have hv_ch : s + 1 ≤ padicValNat p (Nat.choose N k) := by
    have h := padicValNat_choose_ge_sub hp hk1 hkle
    rw [hvN, padicValNat.eq_zero_of_not_dvd hkp] at h
    omega
  have hnum_dvd : p ^ (3 * (s + 1)) ∣ 10 * N ^ 2 * Nat.choose (3 * N) N * Nat.choose N k := by
    have hN2 : p ^ (2 * (s + 1)) ∣ N ^ 2 := by
      have h1 : p ^ (s + 1) ∣ N := hvN ▸ pow_padicValNat_dvd
      have h2 := pow_dvd_pow_of_dvd h1 2
      rwa [← pow_mul, Nat.mul_comm] at h2
    have hch : p ^ (s + 1) ∣ Nat.choose N k :=
      dvd_trans (Nat.pow_dvd_pow p hv_ch) pow_padicValNat_dvd
    have hmul : p ^ (3 * (s + 1)) ∣ N ^ 2 * Nat.choose N k := by
      have : 3 * (s + 1) = 2 * (s + 1) + (s + 1) := by ring
      rw [this, pow_add]
      exact mul_dvd_mul hN2 hch
    refine dvd_trans hmul ?_
    refine ⟨10 * Nat.choose (3 * N) N, ?_⟩
    ring
  exact isPDvdZ_div_coprime_nat hp hden_ndvd (isPDvdZ_natCast hp _ hnum_dvd)

private lemma S_div_term_dvd {p M j : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hM : 1 ≤ M) (hj : j ≤ M) :
    IsPDvdZ p (3 * (padicValNat p M + 1)) ((T (p * M) (p * j) : ℚ) - (T M j : ℚ)) := by
  have : Fact p.Prime := ⟨hp⟩
  set s := padicValNat p M
  have heps3 := epsP_add_padicValNat_three hp hp3
  have h2_ndvd : ¬ p ∣ 2 := fun h => absurd (Nat.le_of_dvd (by omega) h) (by omega)
  set A1 := Nat.choose (3 * (p * M)) (p * j)
  set A0 := Nat.choose (3 * M) j
  set B1 := Nat.choose (3 * (p * M) - p * j - 1) (p * M - p * j)
  set B0 := Nat.choose (3 * M - j - 1) (M - j)
  have hsplit : (T (p * M) (p * j) : ℚ) - (T M j : ℚ) =
      ((A1 : ℚ) - (A0 : ℚ)) * (B0 : ℚ) + (A1 : ℚ) * ((B1 : ℚ) - (B0 : ℚ)) := by
    dsimp [T, A1, A0, B1, B0]
    push_cast
    ring
  rw [hsplit]
  refine isPDvdZ_add hp ?_ ?_
  · -- Term I: (A1 - A0) * B0
    by_cases hj0 : j = 0
    · subst hj0
      have hA : (A1 : ℚ) - (A0 : ℚ) = 0 := by simp [A1, A0]
      rw [hA, zero_mul]
      exact isPDvdZ_zero hp
    · have hj1 : 1 ≤ j := by omega
      have hkaz := kazandzidis hp hp3 hj1 (by omega : j < 3 * M)
      have hA1_eq : A1 = Nat.choose ((3 * M) * p) (j * p) := by
        dsimp [A1]; congr 1 <;> ring
      have hdiff_A : ((p ^ (epsP p + padicValNat p (3 * M) + padicValNat p j +
          padicValNat p (3 * M - j) + padicValNat p A0) : ℕ) : ℤ) ∣ (A1 : ℤ) - (A0 : ℤ) := by
        rw [hA1_eq]
        exact hkaz.2
      have hv3M : padicValNat p (3 * M) = padicValNat p 3 + s := by
        dsimp [s]
        exact padicValNat.mul (by omega) (by omega)
      have hdiff_Aq : IsPDvdZ p (epsP p + padicValNat p (3 * M) + padicValNat p j +
          padicValNat p (3 * M - j) + padicValNat p A0) ((A1 : ℚ) - (A0 : ℚ)) := by
        simpa using isPDvdZ_intCast hp ((A1 : ℤ) - (A0 : ℤ)) hdiff_A
      have hI_q : IsPDvdZ p (epsP p + padicValNat p (3 * M) + padicValNat p j +
          padicValNat p (3 * M - j) + padicValNat p A0 + padicValNat p B0)
          (((A1 : ℚ) - (A0 : ℚ)) * (B0 : ℚ)) :=
        isPDvdZ_mul hp hdiff_Aq (isPDvdZ_natCast hp B0 pow_padicValNat_dvd)
      refine isPDvdZ_mono ?_ hI_q
      by_cases hjs : s ≤ padicValNat p j
      · have hv3Mj : s ≤ padicValNat p (3 * M - j) := by
          have h1 : p ^ s ∣ 3 * M := dvd_mul_of_dvd_right pow_padicValNat_dvd 3
          have h2 : p ^ s ∣ j := dvd_trans (Nat.pow_dvd_pow p hjs) pow_padicValNat_dvd
          exact (padicValNat_dvd_iff_le (by omega)).mp (Nat.dvd_sub h1 h2)
        omega
      · have hjs_lt : padicValNat p j < s := by omega
        have hv3Mj : padicValNat p (3 * M - j) = padicValNat p j := by
          have h1 : p ^ (padicValNat p j) ∣ 3 * M - j := by
            have hd1 : p ^ (padicValNat p j) ∣ 3 * M :=
              dvd_mul_of_dvd_right (dvd_trans (Nat.pow_dvd_pow p (le_of_lt hjs_lt)) pow_padicValNat_dvd) 3
            exact Nat.dvd_sub hd1 pow_padicValNat_dvd
          have h2 : ¬ p ^ (padicValNat p j + 1) ∣ 3 * M - j := by
            intro hdvd
            have hd1 : p ^ (padicValNat p j + 1) ∣ 3 * M :=
              dvd_mul_of_dvd_right (dvd_trans (Nat.pow_dvd_pow p (by omega)) pow_padicValNat_dvd) 3
            have hdj : p ^ (padicValNat p j + 1) ∣ j := by
              have h := Nat.dvd_sub hd1 hdvd
              have hsub : 3 * M - (3 * M - j) = j := by omega
              rwa [hsub] at h
            have := (padicValNat_dvd_iff_le (by omega)).mp hdj
            omega
          have hle := (padicValNat_dvd_iff_le (by omega)).mp h1
          have hgt : padicValNat p (3 * M - j) < padicValNat p j + 1 := by
            by_contra hge
            exact h2 (dvd_trans (Nat.pow_dvd_pow p (by omega)) pow_padicValNat_dvd)
          omega
        have hvA0 : padicValNat p 3 + s - padicValNat p j ≤ padicValNat p A0 := by
          have := padicValNat_choose_ge_sub hp hj1 (by omega : j ≤ 3 * M)
          rwa [hv3M] at this
        have hvB0 : s - padicValNat p j ≤ padicValNat p B0 := by
          have hB := choose_three_mul_identity M j hM hj
          have hv := congr_arg (padicValNat p) hB
          have hB0_ne : B0 ≠ 0 := Nat.ne_of_gt (Nat.choose_pos (by omega))
          have hch_ne : Nat.choose (3 * M - j) (M - j) ≠ 0 := Nat.ne_of_gt (Nat.choose_pos (by omega))
          rw [padicValNat.mul (by omega) hB0_ne, padicValNat.mul (by omega) hch_ne,
            padicValNat.mul (by omega) (by omega), padicValNat.eq_zero_of_not_dvd h2_ndvd,
            zero_add, hv3Mj] at hv
          omega
        omega
  · -- Term II: A1 * (B1 - B0)
    by_cases hjM : j = M
    · subst hjM
      have hB : (B1 : ℚ) - (B0 : ℚ) = 0 := by simp [B1, B0]
      rw [hB, mul_zero]
      exact isPDvdZ_zero hp
    · have hj_lt : j < M := by omega
      have hB0_eq : ((3 * M - j : ℕ) : ℚ) * (B0 : ℚ) =
          (2 * M : ℚ) * (Nat.choose (3 * M - j) (M - j) : ℚ) := by
        have := choose_three_mul_identity M j hM hj
        exact_mod_cast this
      have hB1_eq : ((3 * (p * M) - p * j : ℕ) : ℚ) * (B1 : ℚ) =
          (2 * (p * M) : ℚ) * (Nat.choose (3 * (p * M) - p * j) (p * M - p * j) : ℚ) := by
        have := choose_three_mul_identity (p * M) (p * j) (Nat.mul_pos hp.pos hM) (Nat.mul_le_mul_left p hj)
        exact_mod_cast this
      have hsub_p1 : 3 * (p * M) - p * j = (3 * M - j) * p := by
        rw [Nat.sub_mul]
        congr 1 <;> ring
      have hsub_p2 : p * M - p * j = (M - j) * p := by
        rw [Nat.sub_mul]
        congr 1 <;> ring
      have hd0_ne : ((3 * M - j : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hp_ne : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
      have hdiff_B_eq : (B1 : ℚ) - (B0 : ℚ) =
          ((2 * M : ℕ) : ℚ) *
            ((Nat.choose ((3 * M - j) * p) ((M - j) * p) : ℚ) -
              (Nat.choose (3 * M - j) (M - j) : ℚ)) /
            ((3 * M - j : ℕ) : ℚ) := by
        rw [hsub_p1, hsub_p2] at hB1_eq
        have hB0' : (B0 : ℚ) = (2 * M : ℚ) * (Nat.choose (3 * M - j) (M - j) : ℚ) /
            ((3 * M - j : ℕ) : ℚ) := (eq_div_iff hd0_ne).mpr (by linarith)
        have hB1' : (B1 : ℚ) = (2 * M : ℚ) * (Nat.choose ((3 * M - j) * p) ((M - j) * p) : ℚ) /
            ((3 * M - j : ℕ) : ℚ) := by
          rw [eq_div_iff hd0_ne]
          have hmul_p : (B1 : ℚ) * ((3 * M - j : ℕ) : ℚ) * (p : ℚ) =
              (2 * M : ℚ) * (Nat.choose ((3 * M - j) * p) ((M - j) * p) : ℚ) * (p : ℚ) := by
            push_cast at hB1_eq
            linarith
          exact mul_right_cancel₀ hp_ne hmul_p
        rw [hB1', hB0']
        push_cast
        ring
      have hkazB := kazandzidis hp hp3 (by omega : 0 < M - j) (by omega : M - j < 3 * M - j)
      have hsub_c : (3 * M - j) - (M - j) = 2 * M := by omega
      rw [hsub_c] at hkazB
      have hv2M : padicValNat p (2 * M) = s := by
        rw [padicValNat.mul (by omega) (by omega), padicValNat.eq_zero_of_not_dvd h2_ndvd, zero_add]
      have hB_diff_dvd : IsPDvdZ p (epsP p + 2 * s + padicValNat p (M - j) +
          padicValNat p (Nat.choose (3 * M - j) (M - j))) ((B1 : ℚ) - (B0 : ℚ)) := by
        rw [hdiff_B_eq]
        have hkazBq : IsPDvdZ p (epsP p + padicValNat p (3 * M - j) + padicValNat p (M - j) +
            padicValNat p (2 * M) + padicValNat p (Nat.choose (3 * M - j) (M - j)))
            ((Nat.choose ((3 * M - j) * p) ((M - j) * p) : ℚ) - (Nat.choose (3 * M - j) (M - j) : ℚ)) := by
          simpa using isPDvdZ_intCast hp _ hkazB.2
        have hnum := isPDvdZ_mul hp (isPDvdZ_natCast hp (2 * M) (hv2M ▸ pow_padicValNat_dvd)) hkazBq
        have hK_eq : epsP p + 2 * s + padicValNat p (M - j) +
            padicValNat p (Nat.choose (3 * M - j) (M - j)) + padicValNat p (3 * M - j) =
            s + (epsP p + padicValNat p (3 * M - j) + padicValNat p (M - j) +
              padicValNat p (2 * M) + padicValNat p (Nat.choose (3 * M - j) (M - j))) := by
          rw [hv2M]; omega
        exact isPDvdZ_div_nat hp (by omega) (hK_eq ▸ hnum)
      have hvA1_eq : padicValNat p A1 = padicValNat p A0 := by
        by_cases hj0 : j = 0
        · subst hj0; simp [A1, A0]
        · have hA1_eq : A1 = Nat.choose ((3 * M) * p) (j * p) := by
            dsimp [A1]; congr 1 <;> ring
          rw [hA1_eq]
          exact (kazandzidis hp hp3 (by omega) (by omega : j < 3 * M)).1
      have hII_q := isPDvdZ_mul hp (isPDvdZ_natCast hp A1 (hvA1_eq ▸ pow_padicValNat_dvd)) hB_diff_dvd
      refine isPDvdZ_mono ?_ hII_q
      by_cases hcase : j = 0 ∨ s ≤ padicValNat p j
      · have hvMj : s ≤ padicValNat p (M - j) := by
          rcases hcase with rfl | hjs
          · simp [s]
          · have h1 : p ^ s ∣ M := pow_padicValNat_dvd
            have h2 : p ^ s ∣ j := dvd_trans (Nat.pow_dvd_pow p hjs) pow_padicValNat_dvd
            exact (padicValNat_dvd_iff_le (by omega)).mp (Nat.dvd_sub h1 h2)
        have hvsum : padicValNat p 3 ≤ padicValNat p A0 + padicValNat p (Nat.choose (3 * M - j) (M - j)) := by
          have hid := choose_mul_choose_eq M j hj
          have hv := congr_arg (padicValNat p) hid
          have h1 : A0 ≠ 0 := Nat.ne_of_gt (Nat.choose_pos (by omega))
          have h2 : Nat.choose (3 * M - j) (M - j) ≠ 0 := Nat.ne_of_gt (Nat.choose_pos (by omega))
          have h3 : Nat.choose (3 * M) M ≠ 0 := Nat.ne_of_gt (Nat.choose_pos (by omega))
          have h4 : Nat.choose M j ≠ 0 := Nat.ne_of_gt (Nat.choose_pos hj)
          rw [padicValNat.mul h1 h2, padicValNat.mul h3 h4] at hv
          have hv3 := padicValNat_choose_three_mul hp hM
          omega
        omega
      · push Not at hcase
        rcases hcase with ⟨hj_ne, hjs_lt⟩
        have hj1 : 1 ≤ j := by omega
        have hvMj : padicValNat p (M - j) = padicValNat p j := by
          have h1 : p ^ padicValNat p j ∣ M - j :=
            Nat.dvd_sub (dvd_trans (Nat.pow_dvd_pow p (le_of_lt hjs_lt)) pow_padicValNat_dvd)
              pow_padicValNat_dvd
          have h2 : ¬ p ^ (padicValNat p j + 1) ∣ M - j := by
            intro hdvd
            have hdM : p ^ (padicValNat p j + 1) ∣ M :=
              dvd_trans (Nat.pow_dvd_pow p (by omega)) pow_padicValNat_dvd
            have hdj : p ^ (padicValNat p j + 1) ∣ j := by
              have h := Nat.dvd_sub hdM hdvd
              have hsub : M - (M - j) = j := by omega
              rwa [hsub] at h
            have := (padicValNat_dvd_iff_le (by omega)).mp hdj
            omega
          have hle := (padicValNat_dvd_iff_le (by omega)).mp h1
          have hgt : padicValNat p (M - j) < padicValNat p j + 1 := by
            by_contra hge
            exact h2 (dvd_trans (Nat.pow_dvd_pow p (by omega)) pow_padicValNat_dvd)
          omega
        have hvA0 : padicValNat p 3 + s - padicValNat p j ≤ padicValNat p A0 := by
          have h := padicValNat_choose_ge_sub hp hj1 (by omega : j ≤ 3 * M)
          rw [padicValNat.mul (by omega) (by omega)] at h
          exact h
        omega

private lemma main_proof :
    ∀ p : ℕ, p.Prime → 3 ≤ p →
      ∀ n r : ℕ, 0 < n → 0 < r →
        Nat.ModEq (p ^ (3 * r)) (OMA.S_oeis_a370097.a (n * p ^ r))
          (OMA.S_oeis_a370097.a (n * p ^ (r - 1))) := by
  intro p hp hp3 n r hn hr
  have : Fact p.Prime := ⟨hp⟩
  set M := n * p ^ (r - 1)
  have hM : 1 ≤ M := Nat.mul_pos hn (pow_pos hp.pos _)
  have hN_eq : n * p ^ r = p * M := by
    dsimp [M]
    have hpow : p ^ r = p * p ^ (r - 1) := by
      cases r with
      | zero => omega
      | succ r => simp [pow_succ']
    rw [hpow]
    ring
  have hs_ge : r - 1 ≤ padicValNat p M := by
    have hdvd : p ^ (r - 1) ∣ M := dvd_mul_left (p ^ (r - 1)) n
    exact (padicValNat_dvd_iff_le (by omega)).mp hdvd
  have h3r_le : 3 * r ≤ 3 * (padicValNat p M + 1) := by omega
  have hsplit_a : (OMA.S_oeis_a370097.a (p * M) : ℚ) - (OMA.S_oeis_a370097.a M : ℚ) =
      (∑ k ∈ (Finset.range (p * M + 1)).filter (fun k => ¬ p ∣ k), (T (p * M) k : ℚ)) +
      (∑ j ∈ Finset.range (M + 1), ((T (p * M) (p * j) : ℚ) - (T M j : ℚ))) := by
    have ha_eq : ∀ m : ℕ, (OMA.S_oeis_a370097.a m : ℚ) = ∑ k ∈ Finset.range (m + 1), (T m k : ℚ) := by
      intro m
      unfold OMA.S_oeis_a370097.a T
      push_cast
      rfl
    rw [ha_eq (p * M), ha_eq M]
    have hpart := (Finset.sum_filter_add_sum_filter_not (Finset.range (p * M + 1))
      (fun k => p ∣ k) (fun k => (T (p * M) k : ℚ))).symm
    have hdiv_sum : ∑ k ∈ (Finset.range (p * M + 1)).filter (fun k => p ∣ k), (T (p * M) k : ℚ) =
        ∑ j ∈ Finset.range (M + 1), (T (p * M) (p * j) : ℚ) := by
      refine (Finset.sum_nbij (fun j => p * j) ?_ ?_ ?_ ?_).symm
      · intro j hj
        have hle : j ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr (by nlinarith), dvd_mul_right p j⟩
      · intro j1 _ j2 _ heq
        exact Nat.mul_left_cancel hp.pos heq
      · intro k hk
        rcases Finset.mem_filter.mp hk with ⟨hkr, ⟨j, rfl⟩⟩
        have hle : p * j ≤ p * M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hkr)
        have hjle : j ≤ M := Nat.le_of_mul_le_mul_left hle hp.pos
        exact ⟨j, Finset.mem_range.mpr (by omega), rfl⟩
      · intro _ _; rfl
    rw [hpart, hdiv_sum, Finset.sum_sub_distrib]
    ring
  have hdiff_q : IsPDvdZ p (3 * r)
      (((OMA.S_oeis_a370097.a (n * p ^ r) : ℤ) - (OMA.S_oeis_a370097.a (n * p ^ (r - 1)) : ℤ) : ℤ) : ℚ) := by
    push_cast
    rw [hN_eq]
    change IsPDvdZ p (3 * r) ((OMA.S_oeis_a370097.a (p * M) : ℚ) - (OMA.S_oeis_a370097.a M : ℚ))
    rw [hsplit_a]
    refine isPDvdZ_mono h3r_le (isPDvdZ_add hp (S_ndiv_dvd hp hp3 hM) ?_)
    refine isPDvdZ_sum hp _ _ ?_
    intro j hj
    exact S_div_term_dvd hp hp3 hM (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
  have hdvd_int : ((p ^ (3 * r) : ℕ) : ℤ) ∣
      (OMA.S_oeis_a370097.a (n * p ^ r) : ℤ) - (OMA.S_oeis_a370097.a (n * p ^ (r - 1)) : ℤ) :=
    isPDvdZ_dvd_int hp hdiff_q
  exact Int.natCast_modEq_iff.mp (Int.modEq_iff_dvd.mpr (by simpa [neg_sub] using dvd_neg.mpr hdvd_int))

end A370097Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a370097.main :=
  A370097Proof.main_proof
