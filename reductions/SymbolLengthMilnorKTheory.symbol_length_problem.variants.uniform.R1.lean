import FormalConjectures.Other.SymbolLengthMilnorKTheory

/-!
# Reduction of `SymbolLengthMilnorKTheory.symbol_length_problem.variants.uniform`

Reduction `SymbolLengthMilnorKTheory.symbol_length_problem.variants.uniform.R1`
of `SymbolLengthMilnorKTheory.symbol_length_problem.variants.uniform`.

Credit: @tongenspace.
Reuses and credits:
* @chris01-dev (merged `degree_two_isLeast.R1`): `K_2(C(x))/p = 0` via Steinberg relations;
* @hyprspacecoyote (merged `zero_mem_of_lt.R1`): `exists_common_zero` via Krull height theorem
  and Nullstellensatz, `m_zero`, vanishing propagation, and mod-2 slot primitives.

Target: for every `m >= 0` and `n >= 1`, does there exist `k` independent of the prime `p` such
that `k ∈ symbolLengthBounds (C(x_1, ..., x_m)) p n`?

Proved here unconditionally in Lean (zero hypotheses):
1. `n = 1` (all `m`, all `p`): `k = 1` (upstream `variants.degree_one`).
2. `m = 0` (all `n >= 1`, all `p`): `k = 0` (every unit of `C` is a `p`-th power).
3. `m = 1`, `n >= 2` (all `p`): `k = 0` (`K_2(C(x))/p = 0` via Steinberg + vanishing propagation).
4. General Lang `C_m` theorem for quadratic forms over `C(x_1, ..., x_m)` for all `m >= 0`:
   every diagonal quadratic form in `2^m + 1` variables is isotropic (`u`-invariant `<= 2^m`).
5. Mod-2 vanishing for all `m >= 0` and `n > m`: `K^M_n(C(x_1, ..., x_m))/2 = 0`, via an
   inductive pure-subform Pfister lemma in `K^M_*/2`.
6. Matzri's theorem at `p = 2` for all `m >= 1`:
   `2^(m - 1) - 1 ∈ symbolLengthBounds (C(x_1, ..., x_m)) 2 2`, via an inductive `(2t + 1)`-variable
   Kummer norm form shortening sums of symbols.
7. Mod-2 top-degree cyclicity for all `m >= 1`:
   `1 ∈ symbolLengthBounds (C(x_1, ..., x_m)) 2 m`, via an inductive prefixed Pfister pure-subform
   common-slot argument.
8. Vanishing propagation: `K^M_{m+1}/p = 0` implies `K^M_n/p = 0` for all `n > m`.

Remaining frontier, split into 4 independent, mathematically sharp hypotheses separating
known theorems (`H1`, `H2`) from genuinely open conjectures (`H3`, `H4`):
* `H1` (known: cohomological dimension `m` + Bloch-Kato): odd-prime vanishing at `n = m + 1`
  for `m >= 2`.
* `H2` (known: Milnor conjecture + Pfister numbers): finite bound at `p = 2` for intermediate
  degrees `3 <= n < m`.
* `H3` (open: Becher-Hoffmann / Krashen degree 2): uniform bound for `m >= 2`, `n = 2`, odd `p`.
* `H4` (open: Krashen higher degree): uniform bound for `3 <= n <= m`, odd `p`.
-/

namespace OMA.Uniform.Lang

open MvPolynomial

variable {k : Type*} [Field k]

theorem kill_succ_comp (N i : ℕ) :
    ((aeval (R := k) (fun j : Fin N ↦ if (j : ℕ) < (i + 1) then (0 : MvPolynomial (Fin N) k) else X j))).comp
      ((aeval (R := k) (fun j : Fin N ↦ if (j : ℕ) < i then (0 : MvPolynomial (Fin N) k) else X j))) =
    (aeval (R := k) (fun j : Fin N ↦ if (j : ℕ) < (i + 1) then (0 : MvPolynomial (Fin N) k) else X j)) := by
  apply MvPolynomial.algHom_ext
  intro j
  simp only [AlgHom.comp_apply, aeval_X]
  split_ifs with h1 h2 <;> simp_all
  omega

theorem ker_kill_le (N i : ℕ) :
    RingHom.ker ((aeval (R := k) (fun j : Fin N ↦ if (j : ℕ) < i then (0 : MvPolynomial (Fin N) k) else X j))) ≤
    RingHom.ker ((aeval (R := k) (fun j : Fin N ↦ if (j : ℕ) < (i + 1) then (0 : MvPolynomial (Fin N) k) else X j))) := by
  intro f hf
  rw [RingHom.mem_ker] at hf ⊢
  rw [← kill_succ_comp, AlgHom.comp_apply]
  erw [hf]
  simp

theorem height_ker_kill (N : ℕ) :
    ∀ i ≤ N, (i : ℕ∞) ≤
      (RingHom.ker ((aeval (R := k) (fun j : Fin N ↦ if (j : ℕ) < i then (0 : MvPolynomial (Fin N) k) else X j)))).height := by
  intro i
  induction i with
  | zero => intro _; simp
  | succ i ih =>
    intro hi
    have h1 := ih (by omega)
    have : (RingHom.ker ((aeval (R := k) (fun j : Fin N ↦ if (j : ℕ) < i then (0 : MvPolynomial (Fin N) k) else X j)))).IsPrime :=
      RingHom.ker_isPrime _
    have : (RingHom.ker ((aeval (R := k) (fun j : Fin N ↦ if (j : ℕ) < (i + 1) then (0 : MvPolynomial (Fin N) k) else X j)))).IsPrime :=
      RingHom.ker_isPrime _
    have hlt :
        RingHom.ker ((aeval (R := k) (fun j : Fin N ↦ if (j : ℕ) < i then (0 : MvPolynomial (Fin N) k) else X j))) <
        RingHom.ker ((aeval (R := k) (fun j : Fin N ↦ if (j : ℕ) < (i + 1) then (0 : MvPolynomial (Fin N) k) else X j))) := by
      refine lt_of_le_of_ne (ker_kill_le N i) ?_
      intro h
      have hx : (X ⟨i, by omega⟩ : MvPolynomial (Fin N) k) ∈
          RingHom.ker ((aeval (R := k) (fun j : Fin N ↦ if (j : ℕ) < (i + 1) then (0 : MvPolynomial (Fin N) k) else X j))) := by
        rw [RingHom.mem_ker]; simp
      rw [← h, RingHom.mem_ker] at hx
      simp [X_ne_zero] at hx
    have := Ideal.height_add_one_le_of_lt_of_isPrime hlt
    calc ((i + 1 : ℕ) : ℕ∞) = (i : ℕ∞) + 1 := by push_cast; rfl
      _ ≤ (RingHom.ker ((aeval (R := k) (fun j : Fin N ↦ if (j : ℕ) < i then (0 : MvPolynomial (Fin N) k) else X j)))).height + 1 := by gcongr
      _ ≤ _ := this

theorem mem_ker_kill_N {N : ℕ} (f : MvPolynomial (Fin N) k) :
    f ∈ RingHom.ker ((aeval (R := k) (fun j : Fin N ↦ if (j : ℕ) < N then (0 : MvPolynomial (Fin N) k) else X j))) ↔
      constantCoeff f = 0 := by
  have : (aeval (R := k) (fun j : Fin N ↦ if (j : ℕ) < N then (0 : MvPolynomial (Fin N) k) else X j)) = aeval 0 := by
    apply MvPolynomial.algHom_ext; intro j; simp
  rw [RingHom.mem_ker, this, aeval_zero]
  simp

theorem exists_common_zero [IsAlgClosed k] {N : ℕ} (s : Finset (MvPolynomial (Fin N) k))
    (hs : s.card < N) (h0 : ∀ f ∈ s, constantCoeff f = 0) :
    ∃ v : Fin N → k, v ≠ 0 ∧ ∀ f ∈ s, eval v f = 0 := by
  by_contra hcon
  push Not at hcon
  set I : Ideal (MvPolynomial (Fin N) k) := Ideal.span (s : Set _)
  set M := RingHom.ker ((aeval (R := k) (fun j : Fin N ↦ if (j : ℕ) < N then (0 : MvPolynomial (Fin N) k) else X j)))
  have hM : M.IsPrime := RingHom.ker_isPrime _
  have hIM : I ≤ M := by
    rw [Ideal.span_le]
    intro f hf
    exact (mem_ker_kill_N f).mpr (h0 f hf)
  have hzero : ∀ v ∈ zeroLocus k I, v = 0 := by
    intro v hv
    by_contra hv0
    obtain ⟨f, hf, hfv⟩ := hcon v hv0
    apply hfv
    have := (mem_zeroLocus_iff.mp hv) f (Ideal.subset_span hf)
    simpa [aeval_eq_eval] using this
  have hMrad : M ≤ I.radical := by
    rw [← vanishingIdeal_zeroLocus_eq_radical (K := k)]
    intro f hf v hv
    rw [hzero v hv]
    have := (mem_ker_kill_N f).mp hf
    simpa [aeval_zero] using this
  have hmin : M ∈ I.minimalPrimes := by
    refine ⟨⟨hM, hIM⟩, fun q hq hqM ↦ ?_⟩
    exact hMrad.trans ((Ideal.IsPrime.radical_le_iff hq.1).mpr hq.2)
  have h1 := Ideal.height_le_card_of_mem_minimalPrimes_span_finset hmin
  have h2 := height_ker_kill (k := k) N N le_rfl
  have : ((N : ℕ) : ℕ∞) ≤ s.card := h2.trans h1
  exact absurd (by exact_mod_cast this) (not_le.mpr hs)

theorem exists_common_zero' [IsAlgClosed k] {σ : Type*} [Fintype σ]
    (s : Finset (MvPolynomial σ k)) (hs : s.card < Fintype.card σ)
    (h0 : ∀ f ∈ s, constantCoeff f = 0) :
    ∃ v : σ → k, v ≠ 0 ∧ ∀ f ∈ s, eval v f = 0 := by
  classical
  set e := Fintype.equivFin σ
  obtain ⟨w, hw0, hw⟩ := exists_common_zero (s.image (rename e))
    (lt_of_le_of_lt Finset.card_image_le (by simpa using hs)) (by
      intro f hf
      obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hf
      rw [constantCoeff_rename]; exact h0 g hg)
  refine ⟨w ∘ e, ?_, ?_⟩
  · intro h; apply hw0; funext j
    have := congrFun h (e.symm j); simpa using this
  · intro f hf
    have := hw (rename e f) (Finset.mem_image_of_mem _ hf)
    rwa [eval_rename] at this

lemma degreeOf_map_le' {σ R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S)
    (n : σ) (p : MvPolynomial σ R) : degreeOf n (map f p) ≤ degreeOf n p := by
  rw [degreeOf_le_iff]
  intro m hm
  exact monomial_le_degreeOf n (support_map_subset f p hm)

lemma pow_add_succ_le (a b : ℕ) :
    ∀ k : ℕ, (a + b) ^ (k + 1) ≤ a ^ (k + 1) + b * (k + 1) * (a + b) ^ k := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : (a + b) ^ (k + 1 + 1) = (a + b) ^ (k + 1) * (a + b) := pow_succ _ _
    have h2 : a ^ (k + 1) ≤ (a + b) ^ (k + 1) := Nat.pow_le_pow_left (Nat.le_add_right a b) _
    calc (a + b) ^ (k + 1 + 1)
        = (a + b) ^ (k + 1) * (a + b) := h1
      _ ≤ (a ^ (k + 1) + b * (k + 1) * (a + b) ^ k) * (a + b) := Nat.mul_le_mul_right _ ih
      _ = a ^ (k + 1) * a + a ^ (k + 1) * b + b * (k + 1) * ((a + b) ^ k * (a + b)) := by ring
      _ ≤ a ^ (k + 1) * a + (a + b) ^ (k + 1) * b + b * (k + 1) * ((a + b) ^ k * (a + b)) := by
          gcongr
      _ = a ^ (k + 1 + 1) + b * (k + 1 + 1) * (a + b) ^ (k + 1) := by
          rw [← pow_succ, ← pow_succ]; ring

lemma lang_card_lt (m r : ℕ) :
    (2 * (r * m * 3 ^ m + r + 1) + r) ^ m < (2 ^ m + 1) * (r * m * 3 ^ m + r + 1) ^ m := by
  set S := r * m * 3 ^ m + r + 1
  cases m with
  | zero => simp
  | succ j =>
    have hSpos : 0 < S := by omega
    have h3 : 2 * S + r ≤ 3 * S := by omega
    have hpow : (2 * S + r) ^ j ≤ 3 ^ j * S ^ j := by
      calc (2 * S + r) ^ j ≤ (3 * S) ^ j := Nat.pow_le_pow_left h3 j
        _ = 3 ^ j * S ^ j := mul_pow 3 S j
    have h3le : 3 ^ j ≤ 3 ^ (j + 1) := Nat.pow_le_pow_right (by omega) (Nat.le_succ j)
    have hrm : r * (j + 1) * 3 ^ j < S := by
      have : r * (j + 1) * 3 ^ j ≤ r * (j + 1) * 3 ^ (j + 1) := Nat.mul_le_mul_left _ h3le
      omega
    have hSjpos : 0 < S ^ j := Nat.pow_pos hSpos
    have hstep : r * (j + 1) * (2 * S + r) ^ j < S ^ (j + 1) := by
      calc r * (j + 1) * (2 * S + r) ^ j
          ≤ r * (j + 1) * (3 ^ j * S ^ j) := Nat.mul_le_mul_left _ hpow
        _ = (r * (j + 1) * 3 ^ j) * S ^ j := by ring
        _ < S * S ^ j := Nat.mul_lt_mul_of_pos_right hrm hSjpos
        _ = S ^ (j + 1) := by rw [pow_succ']
    have hmain := pow_add_succ_le (2 * S) r j
    rw [mul_pow] at hmain
    linarith

/-- General Lang degree count over `C[x_1, ..., x_m]`: every diagonal quadratic form in
`2^m + 1` variables with polynomial coefficients has a nonzero polynomial zero. -/
theorem lang_poly_gen (m : ℕ) (P : Fin (2 ^ m + 1) → MvPolynomial (Fin m) ℂ) :
    ∃ W : Fin (2 ^ m + 1) → MvPolynomial (Fin m) ℂ, W ≠ 0 ∧ ∑ i, P i * W i ^ 2 = 0 := by
  classical
  set r := ∑ i : Fin (2 ^ m + 1), ∑ j : Fin m, degreeOf j (P i) with hr
  set S := r * m * 3 ^ m + r + 1 with hS
  set E := 2 * S + r with hE
  have hPr : ∀ (i : Fin (2 ^ m + 1)) (j : Fin m), degreeOf j (P i) ≤ r := by
    intro i j
    have h1 : degreeOf j (P i) ≤ ∑ l : Fin m, degreeOf l (P i) :=
      Finset.single_le_sum (f := fun l ↦ degreeOf l (P i)) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ j)
    have h2 : ∑ l : Fin m, degreeOf l (P i) ≤ r :=
      Finset.single_le_sum (f := fun i' ↦ ∑ l : Fin m, degreeOf l (P i'))
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
    exact h1.trans h2
  let U := Fin (2 ^ m + 1) × (Fin m → Fin S)
  let V : Fin (2 ^ m + 1) → MvPolynomial (Fin m) (MvPolynomial U ℂ) := fun i ↦
    ∑ α : Fin m → Fin S,
      monomial (Finsupp.equivFunOnFinite.symm (fun j ↦ (α j : ℕ))) (X (i, α))
  let Q : MvPolynomial (Fin m) (MvPolynomial U ℂ) := ∑ i, map C (P i) * V i ^ 2
  let eqs : Finset (MvPolynomial U ℂ) :=
    (Finset.univ : Finset (Fin m → Fin E)).image
      (fun α ↦ coeff (Finsupp.equivFunOnFinite.symm (fun j ↦ (α j : ℕ))) Q)
  have hV : ∀ (i : Fin (2 ^ m + 1)) (j : Fin m), degreeOf j (V i) ≤ S - 1 := by
    intro i j
    rw [degreeOf_le_iff]
    intro mon hmon
    obtain ⟨α, -, hα⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hmon)
    have hmem := support_monomial_subset hα
    rw [Finset.mem_singleton] at hmem
    subst hmem
    have hval : (Finsupp.equivFunOnFinite.symm (fun j ↦ (α j : ℕ))) j = (α j : ℕ) := rfl
    rw [hval]
    have hlt := (α j).isLt
    omega
  have hQ : ∀ j : Fin m, degreeOf j Q ≤ r + 2 * (S - 1) := by
    intro j
    refine (degreeOf_sum_le j _ _).trans (Finset.sup_le fun i _ ↦ ?_)
    refine (degreeOf_mul_le j _ _).trans (add_le_add ((degreeOf_map_le' C j _).trans (hPr i j))
      ((degreeOf_pow_le j _ 2).trans ?_))
    exact Nat.mul_le_mul_left 2 (hV i j)
  have hcoeff : ∀ mon : Fin m →₀ ℕ, (∃ j : Fin m, E ≤ mon j) → coeff mon Q = 0 := by
    rintro mon ⟨j, hj⟩
    by_contra hc
    have hsupp : mon ∈ Q.support := mem_support_iff.mpr hc
    have hdeg := (monomial_le_degreeOf j hsupp).trans (hQ j)
    omega
  have hmap0 : map (constantCoeff : MvPolynomial U ℂ →+* ℂ) Q = 0 := by
    have : ∀ i, map (constantCoeff : MvPolynomial U ℂ →+* ℂ) (V i) = 0 := by
      intro i
      simp [V, map_sum, map_monomial]
    simp [Q, map_sum, this]
  have hcard : eqs.card < Fintype.card U := by
    refine lt_of_le_of_lt Finset.card_image_le ?_
    simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_prod, Fintype.card_fin, U]
    exact lang_card_lt m r
  have h0 : ∀ f ∈ eqs, constantCoeff f = 0 := by
    intro f hf
    obtain ⟨α, -, rfl⟩ := Finset.mem_image.mp hf
    rw [← coeff_map, hmap0, coeff_zero]
  obtain ⟨t, ht0, ht⟩ := exists_common_zero' (k := ℂ) eqs hcard h0
  let W : Fin (2 ^ m + 1) → MvPolynomial (Fin m) ℂ := fun i ↦ map (eval t) (V i)
  have hmapQ : map (eval t) Q = ∑ i, P i * W i ^ 2 := by
    have hc : (eval t).comp (C : ℂ →+* MvPolynomial U ℂ) = RingHom.id ℂ := by
      ext; simp
    simp only [Q, W, map_sum, map_mul, map_pow, map_map, hc, map_id]
  have hQ0 : map (eval t) Q = 0 := by
    ext mon
    rw [coeff_map, coeff_zero]
    by_cases hmon : ∀ j : Fin m, mon j < E
    · apply ht
      refine Finset.mem_image.mpr ⟨fun j ↦ ⟨mon j, hmon j⟩, Finset.mem_univ _, ?_⟩
      congr 1
      ext j
      simp
    · push Not at hmon
      rw [hcoeff mon hmon, map_zero]
  refine ⟨W, ?_, hmapQ ▸ hQ0⟩
  obtain ⟨⟨i, α⟩, hu⟩ := Function.ne_iff.mp ht0
  intro hW
  apply hu
  have hWi : W i = 0 := congrFun hW i
  have key : coeff (Finsupp.equivFunOnFinite.symm (fun j ↦ (α j : ℕ))) (W i) = t (i, α) := by
    simp only [W, V, map_sum, map_monomial, eval_X, coeff_sum, coeff_monomial]
    rw [Finset.sum_eq_single α]
    · simp
    · intro α' _ hne
      rw [if_neg]
      intro h
      apply hne
      have hfun := Finsupp.equivFunOnFinite.symm.injective h
      funext j
      exact Fin.ext (congrFun hfun j)
    · simp
  rw [← key, hWi, coeff_zero]
  rfl

/-- `C(x_1, ..., x_m)` has `u`-invariant at most `2^m`: every diagonal quadratic form in
`2^m + 1` variables is isotropic. -/
theorem isotropic_pow_two_succ (m : ℕ) (q : Fin (2 ^ m + 1) → MvRatFunc (Fin m) ℂ) :
    ∃ v : Fin (2 ^ m + 1) → MvRatFunc (Fin m) ℂ, v ≠ 0 ∧ ∑ i, q i * v i ^ 2 = 0 := by
  classical
  have hex : ∀ i, ∃ nd : MvPolynomial (Fin m) ℂ × MvPolynomial (Fin m) ℂ, nd.2 ≠ 0 ∧
      q i = algebraMap _ (MvRatFunc (Fin m) ℂ) nd.1 / algebraMap _ (MvRatFunc (Fin m) ℂ) nd.2 := by
    intro i
    obtain ⟨n, d, hd, h⟩ := IsFractionRing.div_surjective (MvPolynomial (Fin m) ℂ) (q i)
    exact ⟨(n, d), nonZeroDivisors.ne_zero hd, h.symm⟩
  choose nd hd hq using hex
  have hinj : Function.Injective (algebraMap (MvPolynomial (Fin m) ℂ) (MvRatFunc (Fin m) ℂ)) :=
    IsFractionRing.injective _ _
  let P : Fin (2 ^ m + 1) → MvPolynomial (Fin m) ℂ := fun i ↦
    (nd i).1 * ∏ j ∈ Finset.univ.erase i, (nd j).2
  obtain ⟨W, hW0, hW⟩ := lang_poly_gen m P
  set Dn := ∏ j, (nd j).2
  have hDn : algebraMap _ (MvRatFunc (Fin m) ℂ) Dn ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr (Finset.prod_ne_zero_iff.mpr fun j _ ↦ hd j)
  have hP : ∀ i, algebraMap _ (MvRatFunc (Fin m) ℂ) (P i) =
      q i * algebraMap _ (MvRatFunc (Fin m) ℂ) Dn := by
    intro i
    have hdi : algebraMap _ (MvRatFunc (Fin m) ℂ) (nd i).2 ≠ 0 := (map_ne_zero_iff _ hinj).mpr (hd i)
    simp only [P, Dn, map_mul, map_prod, hq i]
    rw [← Finset.mul_prod_erase Finset.univ
      (fun j ↦ algebraMap _ (MvRatFunc (Fin m) ℂ) (nd j).2) (Finset.mem_univ i)]
    field_simp
  refine ⟨fun i ↦ algebraMap _ (MvRatFunc (Fin m) ℂ) (W i), ?_, ?_⟩
  · intro h
    apply hW0
    funext i
    have := congrFun h i
    simp only [Pi.zero_apply] at this ⊢
    exact (map_eq_zero_iff _ hinj).mp this
  · have := congrArg (algebraMap _ (MvRatFunc (Fin m) ℂ)) hW
    simp only [map_sum, map_mul, map_pow, map_zero, hP] at this
    have h2 : (∑ i, q i * algebraMap _ (MvRatFunc (Fin m) ℂ) (W i) ^ 2) *
        algebraMap _ (MvRatFunc (Fin m) ℂ) Dn = 0 := by
      rw [Finset.sum_mul, ← this]
      refine Finset.sum_congr rfl fun i _ ↦ by ring
    exact (mul_eq_zero.mp h2).resolve_right hDn

theorem isotropic_of_card_le {F : Type*} [Field F] {N : ℕ}
    (hu : ∀ q : Fin N → F, ∃ v : Fin N → F, v ≠ 0 ∧ ∑ i, q i * v i ^ 2 = 0)
    {ι : Type*} [Fintype ι] (hcard : N ≤ Fintype.card ι) (q : ι → F) :
    ∃ v : ι → F, v ≠ 0 ∧ ∑ i, q i * v i ^ 2 = 0 := by
  classical
  set e : Fin N ↪ ι := (Fin.castLEEmb hcard).trans (Fintype.equivFin ι).symm.toEmbedding
  obtain ⟨w, hw0, hw⟩ := hu (fun j ↦ q (e j))
  let v : ι → F := fun x ↦
    if h : ∃ j : Fin N, e j = x then w (Classical.choose h) else 0
  have hv_e : ∀ j : Fin N, v (e j) = w j := by
    intro j
    have hex : ∃ j' : Fin N, e j' = e j := ⟨j, rfl⟩
    simp only [v, dif_pos hex]
    exact congrArg w (e.injective (Classical.choose_spec hex))
  have hv_zero : ∀ x : ι, x ∉ (Finset.univ : Finset (Fin N)).map e → v x = 0 := by
    intro x hx
    have hnex : ¬ ∃ j : Fin N, e j = x := by
      rintro ⟨j, rfl⟩
      exact hx (Finset.mem_map.mpr ⟨j, Finset.mem_univ j, rfl⟩)
    simp [v, dif_neg hnex]
  refine ⟨v, ?_, ?_⟩
  · intro hv
    apply hw0
    funext j
    have := congrFun hv (e j)
    simpa [hv_e j] using this
  · rw [← Finset.sum_subset (Finset.subset_univ ((Finset.univ : Finset (Fin N)).map e))]
    · rw [Finset.sum_map]
      simpa [hv_e] using hw
    · intro x _ hx
      simp [hv_zero x hx]

end OMA.Uniform.Lang


namespace OMA.Uniform.Mod2

open MilnorK

variable {F : Type*} [Field F]

theorem add_self_eq_zero (x : MilnorK F 2) : x + x = 0 := by
  have h2 : (2 : MilnorK F 2) = 0 := by exact_mod_cast natCast_eq_zero (F := F) 2
  rw [← two_mul, h2, zero_mul]

theorem neg_eq_self (x : MilnorK F 2) : -x = x := by
  rw [neg_eq_iff_add_eq_zero, add_self_eq_zero]

theorem of_sq (u : Fˣ) : of 2 (u ^ 2) = 0 := by
  rw [of_pow, two_smul, add_self_eq_zero]

theorem of_neg_one (hi : ∃ i : F, i * i = -1) : of 2 (-1 : Fˣ) = 0 := by
  obtain ⟨i, hi⟩ := hi
  have hi0 : i ≠ 0 := by rintro rfl; simp at hi
  have : (-1 : Fˣ) = (Units.mk0 i hi0) ^ 2 := by ext; simp [sq, hi]
  rw [this, of_sq]

theorem of_neg (hi : ∃ i : F, i * i = -1) (a : Fˣ) : of 2 (-a) = of 2 a := by
  rw [show -a = (-1) * a by simp, of_mul, of_neg_one hi, zero_add]

theorem of_mul_self (hi : ∃ i : F, i * i = -1) (a : Fˣ) : of 2 a * of 2 a = 0 := by
  by_cases ha : a = 1
  · simp [ha]
  have h1 : (1 : F) - a ≠ 0 := by
    intro h; apply ha; apply Units.ext; show (a : F) = 1; linear_combination -h
  have h2 : (1 : F) - (a⁻¹ : Fˣ) ≠ 0 := by
    intro h; apply ha; apply Units.ext; show (a : F) = 1
    have : ((a⁻¹ : Fˣ) : F) = 1 := by linear_combination -h
    simpa using congrArg (fun z : F ↦ z⁻¹) this
  set b := Units.mk0 _ h1
  set c := Units.mk0 _ h2
  have hb : of 2 a * of 2 b = 0 := of_mul_of_eq_zero 2 a b (by simp [b])
  have hc : of 2 a⁻¹ * of 2 c = 0 := of_mul_of_eq_zero 2 a⁻¹ c (by simp [c])
  have hc' : of 2 a * of 2 c = 0 := by
    rw [of_inv, neg_eq_self] at hc; exact hc
  have hneg : -a = b * c⁻¹ := by
    have ha0 : (a : F) ≠ 0 := a.ne_zero
    ext
    simp only [Units.val_neg, Units.val_mul, b, c, Units.val_mk0, Units.val_inv_eq_inv_val]
    field_simp
    have : (a : F) - 1 ≠ 0 := by intro h; apply h1; linear_combination -h
    field_simp
    ring
  have : of 2 a * of 2 (-a) = 0 := by
    rw [hneg, of_mul, of_inv, neg_eq_self, mul_add, hb, hc', add_zero]
  rwa [of_neg hi] at this

theorem of_comm (hi : ∃ i : F, i * i = -1) (a b : Fˣ) : of 2 a * of 2 b = of 2 b * of 2 a := by
  have h := of_mul_self hi (a * b)
  rw [of_mul, add_mul, mul_add, mul_add, of_mul_self hi a, of_mul_self hi b, zero_add,
    add_zero] at h
  rw [← neg_eq_self (of 2 b * of 2 a)]
  exact eq_neg_of_add_eq_zero_left h

theorem of_mul_symbol_comm (hi : ∃ i : F, i * i = -1) (a : Fˣ) :
    ∀ {k : ℕ} (s : Fin k → Fˣ), of 2 a * symbol 2 s = symbol 2 s * of 2 a
  | 0, s => by simp
  | k + 1, s => by
    rw [symbol_succ, ← mul_assoc, of_comm hi a (s 0), mul_assoc,
      of_mul_symbol_comm hi a (fun i ↦ s i.succ), ← mul_assoc]

theorem symbol_comm (hi : ∃ i : F, i * i = -1) :
    ∀ {k l : ℕ} (s : Fin k → Fˣ) (t : Fin l → Fˣ), symbol 2 s * symbol 2 t = symbol 2 t * symbol 2 s
  | 0, _, s, t => by simp
  | k + 1, l, s, t => by
    rw [symbol_succ, mul_assoc, symbol_comm hi (fun i ↦ s i.succ) t, ← mul_assoc,
      of_mul_symbol_comm hi (s 0) t, mul_assoc]

theorem symbol_cons {k : ℕ} (e : Fˣ) (a : Fin k → Fˣ) :
    symbol 2 (Fin.cons e a) = of 2 e * symbol 2 a := by
  rw [symbol_succ]
  simp

theorem symbol_append {ℓ r d : ℕ} (u : Fin r → Fˣ) (a : Fin d → Fˣ) :
    symbol ℓ (Fin.append u a) = symbol ℓ u * symbol ℓ a := by
  unfold symbol
  rw [List.ofFn_add, List.prod_append]
  congr 1
  · exact congrArg List.prod (congrArg List.ofFn (funext fun i ↦ by
      have h : Fin.castLE (Nat.le_add_right r d) i = Fin.castAdd d i := rfl
      rw [h, Fin.append_left]))
  · exact congrArg List.prod (congrArg List.ofFn (funext fun j ↦ by
      rw [Fin.append_right]))

theorem steinberg2 (hi : ∃ i : F, i * i = -1) (s t e : Fˣ) (h : (s : F) + t = e) :
    of 2 s * of 2 t = of 2 e * of 2 (s * t) := by
  have hst : of 2 (s * e⁻¹) * of 2 (t * e⁻¹) = 0 :=
    of_mul_of_eq_zero 2 _ _ (by
      have he : (e : F) ≠ 0 := e.ne_zero
      simp only [Units.val_mul, Units.val_inv_eq_inv_val]
      field_simp; linear_combination h)
  simp only [of_mul, of_inv, neg_eq_self] at hst
  rw [add_mul, mul_add, mul_add, of_mul_self hi e, add_zero] at hst
  rw [of_mul, mul_add, of_comm hi e s]
  have h3 : of 2 s * of 2 t = -(of 2 s * of 2 e + of 2 e * of 2 t) :=
    eq_neg_of_add_eq_zero_left (by rw [← add_assoc]; exact hst)
  rw [h3, neg_eq_self]

theorem slot2 (hi : ∃ i : F, i * i = -1) (a b e : Fˣ) (x y : F)
    (h : (e : F) = a * x ^ 2 + b * y ^ 2) :
    of 2 a * of 2 b = of 2 e * of 2 (a * b) := by
  by_cases hx : x = 0
  · have hy : y ≠ 0 := by rintro rfl; subst hx; simp at h
    have he : e = b * (Units.mk0 y hy) ^ 2 := by ext; simp [h, hx]
    rw [he, of_mul, of_sq, add_zero, of_mul, mul_add, of_mul_self hi, add_zero, of_comm hi]
  by_cases hy : y = 0
  · have he : e = a * (Units.mk0 x hx) ^ 2 := by ext; simp [h, hy]
    rw [he, of_mul, of_sq, add_zero, of_mul, mul_add, of_mul_self hi, zero_add]
  set s := a * (Units.mk0 x hx) ^ 2
  set t := b * (Units.mk0 y hy) ^ 2
  have hst := steinberg2 hi s t e (by simp [s, t, h])
  have e1 : of 2 s = of 2 a := by simp only [s, of_mul, of_sq, add_zero]
  have e2 : of 2 t = of 2 b := by simp only [t, of_mul, of_sq, add_zero]
  have e3 : of 2 (s * t) = of 2 (a * b) := by simp only [s, t, of_mul, of_sq, add_zero]
  rw [e1, e2, e3] at hst
  exact hst

theorem norm_slot (hi : ∃ i : F, i * i = -1) (b u : Fˣ) (x z : F)
    (h : (u : F) = x ^ 2 + b * z ^ 2) :
    of 2 u * of 2 b = 0 := by
  have := slot2 hi b 1 u z x (by rw [h]; simp; ring)
  rw [of_one, mul_zero, mul_one] at this
  exact this.symm

theorem slot3 (hi : ∃ i : F, i * i = -1) (a b e : Fˣ) (x y z : F)
    (h : (e : F) = a * x ^ 2 + b * y ^ 2 + a * b * z ^ 2) :
    ∃ f : Fˣ, of 2 a * of 2 b = of 2 e * of 2 f := by
  by_cases hu : x ^ 2 + (b : F) * z ^ 2 = 0
  · exact ⟨a * b, slot2 hi a b e 0 y (by rw [h]; linear_combination (a : F) * hu)⟩
  set u := Units.mk0 _ hu
  have hub := norm_slot hi b u x z rfl
  refine ⟨a * u * b, ?_⟩
  have h2 := slot2 hi (a * u) b e 1 y (by rw [h]; simp [u]; ring)
  rw [of_mul 2 a u, add_mul, hub, add_zero] at h2
  exact h2

theorem slot3_zero (hi : ∃ i : F, i * i = -1) (a b : Fˣ) (x y z : F)
    (hne : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0)
    (h : (a : F) * x ^ 2 + b * y ^ 2 + a * b * z ^ 2 = 0) : of 2 a * of 2 b = 0 := by
  by_cases hu : x ^ 2 + (b : F) * z ^ 2 = 0
  · have hy : (b : F) * y ^ 2 = 0 := by linear_combination h - (a : F) * hu
    have hy0 : y = 0 := by
      rcases mul_eq_zero.mp hy with hb | hy
      · exact absurd hb b.ne_zero
      · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hy
    have hz : z ≠ 0 := by
      rintro rfl
      have : x = 0 := by simpa using hu
      rcases hne with h1 | h1 | h1 <;> contradiction
    have hx : x ≠ 0 := by
      rintro rfl
      have : (b : F) * z ^ 2 = 0 := by simpa using hu
      rcases mul_eq_zero.mp this with hb | hz'
      · exact b.ne_zero hb
      · exact hz (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hz')
    have hb : b = -(Units.mk0 x hx * (Units.mk0 z hz)⁻¹) ^ 2 := by
      ext
      simp only [Units.val_neg, Units.val_pow_eq_pow_val, Units.val_mul, Units.val_mk0,
        Units.val_inv_eq_inv_val]
      field_simp
      linear_combination hu
    rw [hb, of_neg hi, of_sq, mul_zero]
  · set u := Units.mk0 _ hu
    have hub := norm_slot hi b u x z rfl
    have hy : y ≠ 0 := by
      rintro rfl
      apply hu
      have : (a : F) * (x ^ 2 + b * z ^ 2) = 0 := by linear_combination h
      exact (mul_eq_zero.mp this).resolve_left a.ne_zero
    have ha : a = -(b * (Units.mk0 y hy) ^ 2 * u⁻¹) := by
      ext
      have hu0 : (u : F) ≠ 0 := u.ne_zero
      simp only [Units.val_neg, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0,
        Units.val_inv_eq_inv_val]
      field_simp
      simp only [u, Units.val_mk0]
      linear_combination h
    rw [ha, of_neg hi, of_mul, of_mul, of_sq, add_zero, of_inv, neg_eq_self, add_mul,
      of_mul_self hi, hub, add_zero]

theorem sum_finset_fin_succ {α : Type*} [AddCommMonoid α] {d : ℕ}
    (f : Finset (Fin (d + 1)) → α) :
    ∑ S : Finset (Fin (d + 1)), f S =
      (∑ T : Finset (Fin d), f (T.map ⟨Fin.succ, Fin.succ_injective d⟩)) +
      (∑ T : Finset (Fin d), f (insert 0 (T.map ⟨Fin.succ, Fin.succ_injective d⟩))) := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Finset (Fin (d + 1))))
    (fun S ↦ (0 : Fin (d + 1)) ∉ S)]
  congr 1
  · refine (Finset.sum_nbij (fun T : Finset (Fin d) ↦ T.map ⟨Fin.succ, Fin.succ_injective d⟩)
      ?_ ?_ ?_ (fun _ _ ↦ rfl)).symm
    · intro T _; simp
    · intro T₁ _ T₂ _ h; exact Finset.map_injective _ h
    · intro S hS
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hS
      refine ⟨S.preimage Fin.succ (Set.injOn_of_injective (Fin.succ_injective d)), by simp, ?_⟩
      ext x
      refine Fin.cases ?_ (fun y ↦ ?_) x
      · simp [hS]
      · simp
  · refine (Finset.sum_nbij
      (fun T : Finset (Fin d) ↦ insert 0 (T.map ⟨Fin.succ, Fin.succ_injective d⟩))
      ?_ ?_ ?_ (fun _ _ ↦ rfl)).symm
    · intro T _; simp
    · intro T₁ _ T₂ _ h
      have h' : T₁.map ⟨Fin.succ, Fin.succ_injective d⟩ =
          T₂.map ⟨Fin.succ, Fin.succ_injective d⟩ := by
        have := congrArg (fun S ↦ S.erase 0) h
        simpa [Finset.erase_insert] using this
      exact Finset.map_injective _ h'
    · intro S hS
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hS
      refine ⟨S.preimage Fin.succ (Set.injOn_of_injective (Fin.succ_injective d)), by simp, ?_⟩
      ext x
      refine Fin.cases ?_ (fun y ↦ ?_) x
      · simp [hS]
      · simp

/-- Pure Pfister subform lemma in `K^M_{d+1}(F)/2`: if `-1` is a square in `F`, then any nonzero
value `e` of the pure `(d+1)`-fold Pfister form can be placed in the first slot of the symbol,
and isotropy of the pure form forces the symbol to vanish. -/
theorem pfister_pure_ind (hi : ∃ i : F, i * i = -1) :
    ∀ (d : ℕ) (a : Fin (d + 1) → Fˣ) (v : Finset (Fin (d + 1)) → F),
      v ∅ = 0 →
      (∀ e : Fˣ, (e : F) = ∑ S : Finset (Fin (d + 1)), (∏ j ∈ S, (a j : F)) * v S ^ 2 →
        ∃ b : Fin d → Fˣ, symbol 2 a = of 2 e * symbol 2 b) ∧
      (v ≠ 0 → ∑ S : Finset (Fin (d + 1)), (∏ j ∈ S, (a j : F)) * v S ^ 2 = 0 →
        symbol 2 a = 0) := by
  intro d
  induction d with
  | zero =>
    intro a v hv0
    have hsum_eq : ∑ S : Finset (Fin 1), (∏ j ∈ S, (a j : F)) * v S ^ 2 =
        (a 0 : F) * v {0} ^ 2 := by
      rw [sum_finset_fin_succ]
      have h0 : (Finset.univ : Finset (Finset (Fin 0))) = {∅} := by
        ext T; simp [Finset.eq_empty_of_isEmpty]
      rw [h0]
      simp [hv0]
    constructor
    · intro e he
      rw [hsum_eq] at he
      have hv1 : v {0} ≠ 0 := by
        intro h; rw [h, zero_pow (by norm_num), mul_zero] at he; exact e.ne_zero he
      have heeq : e = a 0 * (Units.mk0 (v {0}) hv1) ^ 2 := Units.ext (by simp [he])
      refine ⟨Fin.elim0, ?_⟩
      rw [symbol_one, symbol_zero, mul_one, heeq, of_mul, of_sq, add_zero]
    · intro hv h0
      rw [hsum_eq] at h0
      have hv1 : v {0} ≠ 0 := by
        intro h
        apply hv
        funext S
        have hS : S = ∅ ∨ S = {0} := by
          by_cases hm : (0 : Fin 1) ∈ S
          · right; ext x; rw [Fin.eq_zero x]; simp [hm]
          · left; ext x; rw [Fin.eq_zero x]; simp [hm]
        rcases hS with rfl | rfl
        · exact hv0
        · exact h
      have : (a 0 : F) * v {0} ^ 2 ≠ 0 := mul_ne_zero (a 0).ne_zero (pow_ne_zero 2 hv1)
      exact absurd h0 this
  | succ d ih =>
    intro a v hv0
    classical
    let a' : Fin (d + 1) → Fˣ := fun j ↦ a j.succ
    let v0 : Finset (Fin (d + 1)) → F := fun T ↦ v (T.map ⟨Fin.succ, Fin.succ_injective (d + 1)⟩)
    let v1 : Finset (Fin (d + 1)) → F := fun T ↦
      if T = ∅ then 0 else v (insert 0 (T.map ⟨Fin.succ, Fin.succ_injective (d + 1)⟩))
    let x : F := v {0}
    have hv0_empty : v0 ∅ = 0 := by simp [v0, hv0]
    have hv1_empty : v1 ∅ = 0 := by simp [v1]
    set U : F := ∑ T : Finset (Fin (d + 1)), (∏ j ∈ T, (a' j : F)) * v0 T ^ 2
    set V : F := ∑ T : Finset (Fin (d + 1)), (∏ j ∈ T, (a' j : F)) * v1 T ^ 2
    have hsplit :
        ∑ S : Finset (Fin (d + 2)), (∏ j ∈ S, (a j : F)) * v S ^ 2 = U + (a 0 : F) * (x ^ 2 + V) := by
      rw [sum_finset_fin_succ]
      have hL : ∑ T : Finset (Fin (d + 1)),
          (∏ j ∈ T.map ⟨Fin.succ, Fin.succ_injective (d + 1)⟩, (a j : F)) *
            v (T.map ⟨Fin.succ, Fin.succ_injective (d + 1)⟩) ^ 2 = U := by
        refine Finset.sum_congr rfl fun T _ ↦ ?_
        simp [v0, a', Finset.prod_map]
      have hR : ∑ T : Finset (Fin (d + 1)),
          (∏ j ∈ insert 0 (T.map ⟨Fin.succ, Fin.succ_injective (d + 1)⟩), (a j : F)) *
            v (insert 0 (T.map ⟨Fin.succ, Fin.succ_injective (d + 1)⟩)) ^ 2 =
          (a 0 : F) * (x ^ 2 + V) := by
        have hstep : ∀ T : Finset (Fin (d + 1)),
            (∏ j ∈ insert 0 (T.map ⟨Fin.succ, Fin.succ_injective (d + 1)⟩), (a j : F)) *
              v (insert 0 (T.map ⟨Fin.succ, Fin.succ_injective (d + 1)⟩)) ^ 2 =
            (a 0 : F) * ((∏ j ∈ T, (a' j : F)) *
              v (insert 0 (T.map ⟨Fin.succ, Fin.succ_injective (d + 1)⟩)) ^ 2) := by
          intro T
          rw [Finset.prod_insert (by simp), Finset.prod_map]
          simp [a', mul_assoc]
        simp_rw [hstep, ← Finset.mul_sum]
        congr 1
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (∅ : Finset (Fin (d + 1))))]
        have hV : V = ∑ T ∈ Finset.univ.erase (∅ : Finset (Fin (d + 1))),
            (∏ j ∈ T, (a' j : F)) *
              v (insert 0 (T.map ⟨Fin.succ, Fin.succ_injective (d + 1)⟩)) ^ 2 := by
          dsimp only [V]
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (∅ : Finset (Fin (d + 1))))]
          simp only [hv1_empty, zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_add]
          refine Finset.sum_congr rfl fun T hT ↦ ?_
          have hT0 : T ≠ ∅ := (Finset.mem_erase.mp hT).1
          simp [v1, hT0]
        rw [hV]
        simp [x]
      rw [hL, hR]
    have hmulW : ∀ w : Fˣ, (w : F) = x ^ 2 + V → symbol 2 a' * of 2 w = 0 := by
      intro w hw
      by_cases hV0 : V = 0
      · by_cases hv1z : v1 = 0
        · have hx0 : x ≠ 0 := by
            intro hx; rw [hx, hV0] at hw; simp at hw
          have hweq : w = (Units.mk0 x hx0) ^ 2 := Units.ext (by simp [hw, hV0])
          rw [hweq, of_sq, mul_zero]
        · rw [(ih a' v1 hv1_empty).2 hv1z hV0, zero_mul]
      · obtain ⟨b', hb'⟩ := (ih a' v1 hv1_empty).1 (Units.mk0 V hV0) rfl
        have hnw : of 2 w * of 2 (Units.mk0 V hV0) = 0 :=
          norm_slot hi (Units.mk0 V hV0) w x 1 (by simp [hw])
        rw [hb', mul_assoc, ← of_mul_symbol_comm hi w b', ← mul_assoc,
          of_comm hi (Units.mk0 V hV0) w, hnw, zero_mul]
    have hsym_a : symbol 2 a = of 2 (a 0) * symbol 2 a' := symbol_succ 2 a
    constructor
    · intro e he
      rw [hsplit] at he
      by_cases hv0z : v0 = 0
      · have hU0 : U = 0 := by simp [U, hv0z]
        rw [hU0, zero_add] at he
        have hW0 : x ^ 2 + V ≠ 0 := by
          intro h; rw [h, mul_zero] at he; exact e.ne_zero he
        set w := Units.mk0 (x ^ 2 + V) hW0
        have heq : e = a 0 * w := Units.ext (by simp [he, w])
        refine ⟨a', ?_⟩
        rw [hsym_a, heq, of_mul, add_mul, of_mul_symbol_comm hi w a', hmulW w rfl, add_zero]
      · by_cases hU0 : U = 0
        · have hzero : symbol 2 a' = 0 := (ih a' v0 hv0_empty).2 hv0z hU0
          refine ⟨fun _ ↦ 1, ?_⟩
          rw [hsym_a, hzero, mul_zero, symbol_succ, of_one, zero_mul, mul_zero]
        · set u := Units.mk0 U hU0
          obtain ⟨b', hb'⟩ := (ih a' v0 hv0_empty).1 u rfl
          by_cases hW0 : x ^ 2 + V = 0
          · rw [hW0, mul_zero, add_zero] at he
            have hue : u = e := Units.ext he.symm
            refine ⟨Fin.cons (a 0) b', ?_⟩
            rw [hsym_a, hb', ← hue, symbol_cons, ← mul_assoc, of_comm hi (a 0) u, mul_assoc]
          · set w := Units.mk0 (x ^ 2 + V) hW0
            have hst : of 2 u * of 2 (a 0 * w) = of 2 e * of 2 (u * (a 0 * w)) :=
              steinberg2 hi u (a 0 * w) e (by simp [u, w, he])
            refine ⟨Fin.cons (u * (a 0 * w)) b', ?_⟩
            calc symbol 2 a = of 2 (a 0) * symbol 2 a' := hsym_a
              _ = of 2 (a 0) * symbol 2 a' + symbol 2 a' * of 2 w := by rw [hmulW w rfl, add_zero]
              _ = of 2 (a 0 * w) * symbol 2 a' := by
                  rw [of_mul, add_mul, of_mul_symbol_comm hi w a']
              _ = of 2 (a 0 * w) * (of 2 u * symbol 2 b') := by rw [hb']
              _ = (of 2 u * of 2 (a 0 * w)) * symbol 2 b' := by
                  rw [← mul_assoc, of_comm hi (a 0 * w) u]
              _ = (of 2 e * of 2 (u * (a 0 * w))) * symbol 2 b' := by rw [hst]
              _ = of 2 e * symbol 2 (Fin.cons (u * (a 0 * w)) b') := by rw [symbol_cons, mul_assoc]
    · intro hv hzero
      rw [hsplit] at hzero
      by_cases hv0z : v0 = 0
      · have hU0 : U = 0 := by simp [U, hv0z]
        rw [hU0, zero_add] at hzero
        have hW0 : x ^ 2 + V = 0 := (mul_eq_zero.mp hzero).resolve_left (a 0).ne_zero
        by_cases hV0 : V = 0
        · have hx0 : x = 0 := by
            have : x ^ 2 = 0 := by simpa [hV0] using hW0
            exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
          have hv1z : v1 ≠ 0 := by
            intro hv1
            apply hv
            funext S
            by_cases h0S : (0 : Fin (d + 2)) ∈ S
            · let T := S.preimage Fin.succ (Set.injOn_of_injective (Fin.succ_injective (d + 1)))
              have hST : S = insert 0 (T.map ⟨Fin.succ, Fin.succ_injective (d + 1)⟩) := by
                ext y
                refine Fin.cases ?_ (fun z ↦ ?_) y
                · simp [h0S]
                · simp [T]
              rw [hST]
              by_cases hT0 : T = ∅
              · rw [hT0]; simpa [x] using hx0
              · have := congrFun hv1 T
                simpa [v1, hT0] using this
            · let T := S.preimage Fin.succ (Set.injOn_of_injective (Fin.succ_injective (d + 1)))
              have hST : S = T.map ⟨Fin.succ, Fin.succ_injective (d + 1)⟩ := by
                ext y
                refine Fin.cases ?_ (fun z ↦ ?_) y
                · simp [h0S]
                · simp [T]
              rw [hST]
              exact congrFun hv0z T
          rw [hsym_a, (ih a' v1 hv1_empty).2 hv1z hV0, mul_zero]
        · set uV := Units.mk0 V hV0
          obtain ⟨b', hb'⟩ := (ih a' v1 hv1_empty).1 uV rfl
          have hx0 : x ≠ 0 := by
            intro hx; rw [hx, zero_pow (by norm_num), zero_add] at hW0; exact hV0 hW0
          have huV : uV = -(Units.mk0 x hx0) ^ 2 := Units.ext (by
            simp only [uV, Units.val_neg, Units.val_pow_eq_pow_val, Units.val_mk0]
            linear_combination hW0)
          rw [hsym_a, hb', huV, of_neg hi, of_sq, zero_mul, mul_zero]
      · by_cases hU0 : U = 0
        · rw [hsym_a, (ih a' v0 hv0_empty).2 hv0z hU0, mul_zero]
        · set u := Units.mk0 U hU0
          obtain ⟨b', hb'⟩ := (ih a' v0 hv0_empty).1 u rfl
          have hW0 : x ^ 2 + V ≠ 0 := by
            intro h; rw [h, mul_zero, add_zero] at hzero; exact hU0 hzero
          set w := Units.mk0 (x ^ 2 + V) hW0
          have haw : a 0 * w = -u := Units.ext (by
            simp only [Units.val_mul, Units.val_neg, u, w, Units.val_mk0]
            linear_combination hzero)
          calc symbol 2 a = of 2 (a 0) * symbol 2 a' := hsym_a
            _ = of 2 (a 0) * symbol 2 a' + symbol 2 a' * of 2 w := by rw [hmulW w rfl, add_zero]
            _ = of 2 (a 0 * w) * symbol 2 a' := by
                rw [of_mul, add_mul, of_mul_symbol_comm hi w a']
            _ = of 2 (-u) * (of 2 u * symbol 2 b') := by rw [haw, hb']
            _ = (of 2 u * of 2 u) * symbol 2 b' := by rw [of_neg hi, mul_assoc]
            _ = 0 := by rw [of_mul_self hi, zero_mul]

/-- Full Pfister isotropy implies vanishing of the symbol in `K^M_r(F)/2`. -/
theorem pfister_full_zero (hi : ∃ i : F, i * i = -1) :
    ∀ {r : ℕ} (u : Fin r → Fˣ) (v : Finset (Fin r) → F),
      v ≠ 0 → ∑ S : Finset (Fin r), (∏ j ∈ S, (u j : F)) * v S ^ 2 = 0 →
      symbol 2 u = 0 := by
  intro r u v hv hsum
  cases r with
  | zero =>
    exfalso
    have h0 : (Finset.univ : Finset (Finset (Fin 0))) = {∅} := by
      ext T; simp [Finset.eq_empty_of_isEmpty]
    rw [h0] at hsum
    simp only [Finset.sum_singleton, Finset.prod_empty, one_mul] at hsum
    have hv0 : v ∅ = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsum
    apply hv
    funext S
    rw [Finset.eq_empty_of_isEmpty S]
    exact hv0
  | succ d =>
    classical
    let v' : Finset (Fin (d + 1)) → F := fun S ↦ if S = ∅ then 0 else v S
    have hv'0 : v' ∅ = 0 := by simp [v']
    set V : F := ∑ S : Finset (Fin (d + 1)), (∏ j ∈ S, (u j : F)) * v' S ^ 2
    have hsplit : ∑ S : Finset (Fin (d + 1)), (∏ j ∈ S, (u j : F)) * v S ^ 2 = v ∅ ^ 2 + V := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (∅ : Finset (Fin (d + 1))))]
      simp only [Finset.prod_empty, one_mul]
      congr 1
      dsimp only [V]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (∅ : Finset (Fin (d + 1))))]
      simp only [hv'0, zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_add]
      refine Finset.sum_congr rfl fun S hS ↦ ?_
      simp [v', (Finset.mem_erase.mp hS).1]
    rw [hsplit] at hsum
    by_cases hV0 : V = 0
    · have hx0 : v ∅ = 0 := by
        have : v ∅ ^ 2 = 0 := by simpa [hV0] using hsum
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
      have hv'ne : v' ≠ 0 := by
        intro h
        apply hv
        funext S
        by_cases hS : S = ∅
        · subst hS; exact hx0
        · have := congrFun h S; simpa [v', hS] using this
      exact (pfister_pure_ind hi d u v' hv'0).2 hv'ne hV0
    · set uV := Units.mk0 V hV0
      obtain ⟨b, hb⟩ := (pfister_pure_ind hi d u v' hv'0).1 uV rfl
      have hx0 : v ∅ ≠ 0 := by
        intro hx; rw [hx, zero_pow (by norm_num), zero_add] at hsum; exact hV0 hsum
      have huV : uV = -(Units.mk0 (v ∅) hx0) ^ 2 := Units.ext (by
        simp only [uV, Units.val_neg, Units.val_pow_eq_pow_val, Units.val_mk0]
        linear_combination hsum)
      rw [hb, huV, of_neg hi, of_sq, zero_mul]

/-- Any nonzero value `x` represented by the full Pfister form of `u` kills `symbol 2 u`. -/
theorem pfister_full_mul (hi : ∃ i : F, i * i = -1) :
    ∀ {r : ℕ} (u : Fin r → Fˣ) (v : Finset (Fin r) → F) (x : Fˣ),
      (x : F) = ∑ S : Finset (Fin r), (∏ j ∈ S, (u j : F)) * v S ^ 2 →
      symbol 2 u * of 2 x = 0 := by
  intro r u v x hx
  cases r with
  | zero =>
    have h0 : (Finset.univ : Finset (Finset (Fin 0))) = {∅} := by
      ext T; simp [Finset.eq_empty_of_isEmpty]
    rw [h0] at hx
    simp only [Finset.sum_singleton, Finset.prod_empty, one_mul] at hx
    have hv0 : v ∅ ≠ 0 := by
      intro h; rw [h, zero_pow (by norm_num)] at hx; exact x.ne_zero hx
    have hxeq : x = (Units.mk0 (v ∅) hv0) ^ 2 := Units.ext (by simp [hx])
    rw [hxeq, of_sq, mul_zero]
  | succ d =>
    classical
    let v' : Finset (Fin (d + 1)) → F := fun S ↦ if S = ∅ then 0 else v S
    have hv'0 : v' ∅ = 0 := by simp [v']
    set V : F := ∑ S : Finset (Fin (d + 1)), (∏ j ∈ S, (u j : F)) * v' S ^ 2
    have hsplit : ∑ S : Finset (Fin (d + 1)), (∏ j ∈ S, (u j : F)) * v S ^ 2 = v ∅ ^ 2 + V := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (∅ : Finset (Fin (d + 1))))]
      simp only [Finset.prod_empty, one_mul]
      congr 1
      dsimp only [V]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (∅ : Finset (Fin (d + 1))))]
      simp only [hv'0, zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_add]
      refine Finset.sum_congr rfl fun S hS ↦ ?_
      simp [v', (Finset.mem_erase.mp hS).1]
    rw [hsplit] at hx
    by_cases hV0 : V = 0
    · by_cases hv'z : v' = 0
      · have hv0 : v ∅ ≠ 0 := by
          intro h; rw [h, hV0] at hx; simp at hx
        have hxeq : x = (Units.mk0 (v ∅) hv0) ^ 2 := Units.ext (by simp [hx, hV0])
        rw [hxeq, of_sq, mul_zero]
      · rw [(pfister_pure_ind hi d u v' hv'0).2 hv'z hV0, zero_mul]
    · set uV := Units.mk0 V hV0
      obtain ⟨b, hb⟩ := (pfister_pure_ind hi d u v' hv'0).1 uV rfl
      have hnx : of 2 x * of 2 uV = 0 := norm_slot hi uV x (v ∅) 1 (by simp [hx, uV])
      rw [hb, mul_assoc, ← of_mul_symbol_comm hi x b, ← mul_assoc, of_comm hi uV x, hnx, zero_mul]

/-- Reindexing product of two Pfister index sets `Finset (Fin r) × Finset (Fin d)` to
`Finset (Fin (r + d))`. -/
theorem sum_prod_finset_eq_finset_add {r d : ℕ} (u : Fin r → Fˣ) (a : Fin d → Fˣ)
    (w : Finset (Fin r) × Finset (Fin d) → F) :
    ∃ w' : Finset (Fin (r + d)) → F,
      (w ≠ 0 → w' ≠ 0) ∧
      ∑ p : Finset (Fin r) × Finset (Fin d),
        (∏ i ∈ p.1, (u i : F)) * (∏ j ∈ p.2, (a j : F)) * w p ^ 2 =
      ∑ S : Finset (Fin (r + d)),
        (∏ k ∈ S, ((Fin.append u a k : Fˣ) : F)) * w' S ^ 2 := by
  classical
  let f : Finset (Fin r) × Finset (Fin d) → Finset (Fin (r + d)) := fun p ↦
    p.1.map ⟨Fin.castAdd d, Fin.castAdd_injective r d⟩ ∪
      p.2.map ⟨Fin.natAdd r, Fin.natAdd_injective d r⟩
  let g : Finset (Fin (r + d)) → Finset (Fin r) × Finset (Fin d) := fun S ↦
    (S.preimage (Fin.castAdd d) (Set.injOn_of_injective (Fin.castAdd_injective r d)),
     S.preimage (Fin.natAdd r) (Set.injOn_of_injective (Fin.natAdd_injective d r)))
  have hgf : ∀ p, g (f p) = p := by
    rintro ⟨T, S⟩
    apply Prod.ext
    · ext i
      simp only [g, f, Finset.mem_preimage, Finset.mem_union, Finset.mem_map,
        Function.Embedding.coeFn_mk]
      constructor
      · rintro (⟨i', hi', h⟩ | ⟨j', _, h⟩)
        · exact (Fin.castAdd_injective r d h) ▸ hi'
        · exfalso
          have := congrArg Fin.val h
          simp only [Fin.val_natAdd, Fin.val_castAdd] at this
          omega
      · intro hi
        left; exact ⟨i, hi, rfl⟩
    · ext j
      simp only [g, f, Finset.mem_preimage, Finset.mem_union, Finset.mem_map,
        Function.Embedding.coeFn_mk]
      constructor
      · rintro (⟨i', _, h⟩ | ⟨j', hj', h⟩)
        · exfalso
          have := congrArg Fin.val h
          simp only [Fin.val_natAdd, Fin.val_castAdd] at this
          omega
        · exact (Fin.natAdd_injective d r h) ▸ hj'
      · intro hj
        right; exact ⟨j, hj, rfl⟩
  have hfg : ∀ S, f (g S) = S := by
    intro S
    ext k
    simp only [f, g, Finset.mem_union, Finset.mem_map, Finset.mem_preimage,
      Function.Embedding.coeFn_mk]
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) k
    · constructor
      · rintro (⟨i', hi', h⟩ | ⟨j', _, h⟩)
        · exact (Fin.castAdd_injective r d h) ▸ hi'
        · exfalso
          have := congrArg Fin.val h
          simp only [Fin.val_natAdd, Fin.val_castAdd] at this
          omega
      · intro hi; left; exact ⟨i, hi, rfl⟩
    · constructor
      · rintro (⟨i', _, h⟩ | ⟨j', hj', h⟩)
        · exfalso
          have := congrArg Fin.val h
          simp only [Fin.val_natAdd, Fin.val_castAdd] at this
          omega
        · exact (Fin.natAdd_injective d r h) ▸ hj'
      · intro hj; right; exact ⟨j, hj, rfl⟩
  let e : Finset (Fin r) × Finset (Fin d) ≃ Finset (Fin (r + d)) :=
    { toFun := f, invFun := g, left_inv := hgf, right_inv := hfg }
  refine ⟨fun S ↦ w (e.symm S), ?_, ?_⟩
  · intro hw h0
    apply hw
    funext p
    have := congrFun h0 (e p)
    simpa [e.symm_apply_apply] using this
  · rw [← Equiv.sum_comp e]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    have hdisj : Disjoint (p.1.map ⟨Fin.castAdd d, Fin.castAdd_injective r d⟩)
        (p.2.map ⟨Fin.natAdd r, Fin.natAdd_injective d r⟩) := by
      rw [Finset.disjoint_left]
      intro k hk1 hk2
      obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hk1
      obtain ⟨j, _, h⟩ := Finset.mem_map.mp hk2
      have := congrArg Fin.val h
      simp only [Function.Embedding.coeFn_mk, Fin.val_natAdd, Fin.val_castAdd] at this
      omega
    have hprod : ∏ k ∈ e p, ((Fin.append u a k : Fˣ) : F) =
        (∏ i ∈ p.1, (u i : F)) * (∏ j ∈ p.2, (a j : F)) := by
      show ∏ k ∈ f p, _ = _
      rw [Finset.prod_union hdisj, Finset.prod_map, Finset.prod_map]
      simp [Fin.append_left, Fin.append_right]
    simp only [hprod, e.symm_apply_apply]

/-- Prefixed pure Pfister subform lemma: for any fixed prefix `u : Fin r → Fˣ`, any nonzero value
of `φ_r(u) ⊗ φ'_{d+1}(a)` can be placed in the first slot after `u`, and isotropy forces
`symbol 2 u * symbol 2 a = 0`. -/
theorem pfister_prefix_pure_ind (hi : ∃ i : F, i * i = -1) (r : ℕ) (u : Fin r → Fˣ) :
    ∀ (d : ℕ) (a : Fin (d + 1) → Fˣ)
      (v : Finset (Fin r) × Finset (Fin (d + 1)) → F),
      (∀ T, v (T, ∅) = 0) →
      (∀ e : Fˣ, (e : F) = ∑ p : Finset (Fin r) × Finset (Fin (d + 1)),
          (∏ i ∈ p.1, (u i : F)) * (∏ j ∈ p.2, (a j : F)) * v p ^ 2 →
        ∃ b : Fin d → Fˣ, symbol 2 u * symbol 2 a = symbol 2 u * of 2 e * symbol 2 b) ∧
      (v ≠ 0 → ∑ p : Finset (Fin r) × Finset (Fin (d + 1)),
          (∏ i ∈ p.1, (u i : F)) * (∏ j ∈ p.2, (a j : F)) * v p ^ 2 = 0 →
        symbol 2 u * symbol 2 a = 0) := by
  intro d
  induction d with
  | zero =>
    intro a v hv0
    have hsum_eq :
        ∑ p : Finset (Fin r) × Finset (Fin 1),
          (∏ i ∈ p.1, (u i : F)) * (∏ j ∈ p.2, (a j : F)) * v p ^ 2 =
        (a 0 : F) * ∑ T : Finset (Fin r), (∏ i ∈ T, (u i : F)) * v (T, {0}) ^ 2 := by
      rw [Fintype.sum_prod_type]
      have h1 : ∀ T : Finset (Fin r),
          ∑ S : Finset (Fin 1), (∏ i ∈ T, (u i : F)) * (∏ j ∈ S, (a j : F)) * v (T, S) ^ 2 =
          (a 0 : F) * ((∏ i ∈ T, (u i : F)) * v (T, {0}) ^ 2) := by
        intro T
        rw [sum_finset_fin_succ]
        have h0 : (Finset.univ : Finset (Finset (Fin 0))) = {∅} := by
          ext S; simp [Finset.eq_empty_of_isEmpty]
        rw [h0]
        simp [hv0 T]
        ring
      simp_rw [h1, ← Finset.mul_sum]
    set α : F := ∑ T : Finset (Fin r), (∏ i ∈ T, (u i : F)) * v (T, {0}) ^ 2
    constructor
    · intro e he
      rw [hsum_eq] at he
      have hα0 : α ≠ 0 := by
        intro h; rw [h, mul_zero] at he; exact e.ne_zero he
      set uα := Units.mk0 α hα0
      have heeq : e = a 0 * uα := Units.ext (by simp [he, uα])
      refine ⟨Fin.elim0, ?_⟩
      rw [symbol_one, symbol_zero, mul_one, heeq, of_mul, mul_add,
        pfister_full_mul hi u (fun T ↦ v (T, {0})) uα rfl, add_zero]
    · intro hv hzero
      rw [hsum_eq] at hzero
      have hα0 : α = 0 := (mul_eq_zero.mp hzero).resolve_left (a 0).ne_zero
      have hvne : (fun T : Finset (Fin r) ↦ v (T, {0})) ≠ 0 := by
        intro h
        apply hv
        funext ⟨T, S⟩
        have hS : S = ∅ ∨ S = {0} := by
          by_cases hm : (0 : Fin 1) ∈ S
          · right; ext x; rw [Fin.eq_zero x]; simp [hm]
          · left; ext x; rw [Fin.eq_zero x]; simp [hm]
        rcases hS with rfl | rfl
        · exact hv0 T
        · exact congrFun h T
      rw [pfister_full_zero hi u (fun T ↦ v (T, {0})) hvne hα0, zero_mul]
  | succ d ih =>
    intro a v hv0
    classical
    let a' : Fin (d + 1) → Fˣ := fun j ↦ a j.succ
    let v0 : Finset (Fin r) × Finset (Fin (d + 1)) → F :=
      fun p ↦ v (p.1, p.2.map ⟨Fin.succ, Fin.succ_injective (d + 1)⟩)
    let w : Finset (Fin r) × Finset (Fin (d + 1)) → F :=
      fun p ↦ v (p.1, insert 0 (p.2.map ⟨Fin.succ, Fin.succ_injective (d + 1)⟩))
    have hv0_empty : ∀ T, v0 (T, ∅) = 0 := fun T ↦ by simp [v0, hv0 T]
    set U : F := ∑ p : Finset (Fin r) × Finset (Fin (d + 1)),
      (∏ i ∈ p.1, (u i : F)) * (∏ j ∈ p.2, (a' j : F)) * v0 p ^ 2
    set W : F := ∑ p : Finset (Fin r) × Finset (Fin (d + 1)),
      (∏ i ∈ p.1, (u i : F)) * (∏ j ∈ p.2, (a' j : F)) * w p ^ 2
    have hsplit :
        ∑ p : Finset (Fin r) × Finset (Fin (d + 2)),
          (∏ i ∈ p.1, (u i : F)) * (∏ j ∈ p.2, (a j : F)) * v p ^ 2 =
        U + (a 0 : F) * W := by
      rw [Fintype.sum_prod_type]
      have hinner : ∀ T : Finset (Fin r),
          ∑ S : Finset (Fin (d + 2)),
            (∏ i ∈ T, (u i : F)) * (∏ j ∈ S, (a j : F)) * v (T, S) ^ 2 =
          (∑ S : Finset (Fin (d + 1)),
            (∏ i ∈ T, (u i : F)) *
              (∏ j ∈ S.map ⟨Fin.succ, Fin.succ_injective (d + 1)⟩, (a j : F)) *
              v (T, S.map ⟨Fin.succ, Fin.succ_injective (d + 1)⟩) ^ 2) +
          (∑ S : Finset (Fin (d + 1)),
            (∏ i ∈ T, (u i : F)) *
              (∏ j ∈ insert 0 (S.map ⟨Fin.succ, Fin.succ_injective (d + 1)⟩), (a j : F)) *
              v (T, insert 0 (S.map ⟨Fin.succ, Fin.succ_injective (d + 1)⟩)) ^ 2) :=
        fun T ↦ sum_finset_fin_succ (fun S ↦
          (∏ i ∈ T, (u i : F)) * (∏ j ∈ S, (a j : F)) * v (T, S) ^ 2)
      simp_rw [hinner]
      rw [Finset.sum_add_distrib]
      congr 1
      · dsimp only [U]
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun T _ ↦ Finset.sum_congr rfl fun S _ ↦ ?_
        simp [v0, a', Finset.prod_map]
      · dsimp only [W]
        rw [Fintype.sum_prod_type, Finset.mul_sum]
        refine Finset.sum_congr rfl fun T _ ↦ ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun S _ ↦ ?_
        rw [Finset.prod_insert (by simp), Finset.prod_map]
        simp only [w, a', Function.Embedding.coeFn_mk]
        ring
    obtain ⟨w', hw'ne, hw'sum⟩ := sum_prod_finset_eq_finset_add u a' w
    have hW_zero : w ≠ 0 → W = 0 → symbol 2 u * symbol 2 a' = 0 := by
      intro hw hW0
      rw [← symbol_append]
      exact pfister_full_zero hi (Fin.append u a') w' (hw'ne hw) (hw'sum ▸ hW0)
    have hW_mul : ∀ uw : Fˣ, (uw : F) = W → symbol 2 u * symbol 2 a' * of 2 uw = 0 := by
      intro uw huw
      rw [← symbol_append]
      exact pfister_full_mul hi (Fin.append u a') w' uw (hw'sum ▸ huw)
    have hsym_a : symbol 2 u * symbol 2 a = symbol 2 u * of 2 (a 0) * symbol 2 a' := by
      rw [symbol_succ, mul_assoc]
    constructor
    · intro e he
      rw [hsplit] at he
      by_cases hv0z : v0 = 0
      · have hU0 : U = 0 := by simp [U, hv0z]
        rw [hU0, zero_add] at he
        have hW0 : W ≠ 0 := by intro h; rw [h, mul_zero] at he; exact e.ne_zero he
        set uw := Units.mk0 W hW0
        have heeq : e = a 0 * uw := Units.ext (by simp [he, uw])
        refine ⟨a', ?_⟩
        calc symbol 2 u * symbol 2 a
            = symbol 2 u * of 2 (a 0) * symbol 2 a' := hsym_a
          _ = symbol 2 u * of 2 (a 0) * symbol 2 a' + symbol 2 u * symbol 2 a' * of 2 uw := by
              rw [hW_mul uw rfl, add_zero]
          _ = symbol 2 u * of 2 (a 0 * uw) * symbol 2 a' := by
              rw [of_mul, mul_add, add_mul, mul_assoc (symbol 2 u) (of 2 uw),
                of_mul_symbol_comm hi uw a', ← mul_assoc (symbol 2 u) (symbol 2 a')]
          _ = symbol 2 u * of 2 e * symbol 2 a' := by rw [heeq]
      · by_cases hU0 : U = 0
        · have hzero : symbol 2 u * symbol 2 a' = 0 := (ih a' v0 hv0_empty).2 hv0z hU0
          refine ⟨fun _ ↦ 1, ?_⟩
          rw [hsym_a, mul_assoc, of_mul_symbol_comm hi (a 0) a', ← mul_assoc, hzero, zero_mul,
            symbol_succ, of_one, zero_mul, mul_zero]
        · set uU := Units.mk0 U hU0
          obtain ⟨b', hb'⟩ := (ih a' v0 hv0_empty).1 uU rfl
          by_cases hW0 : W = 0
          · rw [hW0, mul_zero, add_zero] at he
            have hue : uU = e := Units.ext he.symm
            refine ⟨Fin.cons (a 0) b', ?_⟩
            calc symbol 2 u * symbol 2 a
                = symbol 2 u * of 2 (a 0) * symbol 2 a' := hsym_a
              _ = symbol 2 u * symbol 2 a' * of 2 (a 0) := by
                  rw [mul_assoc, of_mul_symbol_comm hi (a 0) a', ← mul_assoc]
              _ = symbol 2 u * of 2 uU * symbol 2 b' * of 2 (a 0) := by rw [hb']
              _ = symbol 2 u * of 2 e * symbol 2 (Fin.cons (a 0) b') := by
                  rw [hue, symbol_cons, mul_assoc, mul_assoc, of_mul_symbol_comm hi (a 0) b',
                    ← mul_assoc]
          · set uw := Units.mk0 W hW0
            have hst : of 2 uU * of 2 (a 0 * uw) = of 2 e * of 2 (uU * (a 0 * uw)) :=
              steinberg2 hi uU (a 0 * uw) e (by simp [uU, uw, he])
            refine ⟨Fin.cons (uU * (a 0 * uw)) b', ?_⟩
            calc symbol 2 u * symbol 2 a
                = symbol 2 u * of 2 (a 0) * symbol 2 a' := hsym_a
              _ = symbol 2 u * symbol 2 a' * of 2 (a 0) + symbol 2 u * symbol 2 a' * of 2 uw := by
                  rw [hW_mul uw rfl, add_zero, mul_assoc, of_mul_symbol_comm hi (a 0) a', ← mul_assoc]
              _ = symbol 2 u * symbol 2 a' * of 2 (a 0 * uw) := by rw [of_mul, mul_add]
              _ = symbol 2 u * of 2 uU * symbol 2 b' * of 2 (a 0 * uw) := by rw [hb']
              _ = symbol 2 u * (of 2 uU * of 2 (a 0 * uw)) * symbol 2 b' := by
                  rw [mul_assoc (symbol 2 u * of 2 uU), ← of_mul_symbol_comm hi (a 0 * uw) b',
                    ← mul_assoc, mul_assoc (symbol 2 u)]
              _ = symbol 2 u * (of 2 e * of 2 (uU * (a 0 * uw))) * symbol 2 b' := by rw [hst]
              _ = symbol 2 u * of 2 e * symbol 2 (Fin.cons (uU * (a 0 * uw)) b') := by
                  rw [symbol_cons, mul_assoc, mul_assoc, mul_assoc]
    · intro hv hzero
      rw [hsplit] at hzero
      by_cases hv0z : v0 = 0
      · have hU0 : U = 0 := by simp [U, hv0z]
        rw [hU0, zero_add] at hzero
        have hW0 : W = 0 := (mul_eq_zero.mp hzero).resolve_left (a 0).ne_zero
        have hwne : w ≠ 0 := by
          intro hw
          apply hv
          funext ⟨T, S⟩
          by_cases h0S : (0 : Fin (d + 2)) ∈ S
          · let S' := S.preimage Fin.succ (Set.injOn_of_injective (Fin.succ_injective (d + 1)))
            have hSS' : S = insert 0 (S'.map ⟨Fin.succ, Fin.succ_injective (d + 1)⟩) := by
              ext y
              refine Fin.cases ?_ (fun z ↦ ?_) y
              · simp [h0S]
              · simp [S']
            rw [hSS']
            exact congrFun hw (T, S')
          · let S' := S.preimage Fin.succ (Set.injOn_of_injective (Fin.succ_injective (d + 1)))
            have hSS' : S = S'.map ⟨Fin.succ, Fin.succ_injective (d + 1)⟩ := by
              ext y
              refine Fin.cases ?_ (fun z ↦ ?_) y
              · simp [h0S]
              · simp [S']
            rw [hSS']
            exact congrFun hv0z (T, S')
        rw [hsym_a, mul_assoc, of_mul_symbol_comm hi (a 0) a', ← mul_assoc, hW_zero hwne hW0,
          zero_mul]
      · by_cases hU0 : U = 0
        · rw [hsym_a, mul_assoc, of_mul_symbol_comm hi (a 0) a', ← mul_assoc,
            (ih a' v0 hv0_empty).2 hv0z hU0, zero_mul]
        · set uU := Units.mk0 U hU0
          obtain ⟨b', hb'⟩ := (ih a' v0 hv0_empty).1 uU rfl
          have hW0 : W ≠ 0 := by
            intro h; rw [h, mul_zero, add_zero] at hzero; exact hU0 hzero
          set uw := Units.mk0 W hW0
          have haw : a 0 * uw = -uU := Units.ext (by
            simp only [Units.val_mul, Units.val_neg, uU, uw, Units.val_mk0]
            linear_combination hzero)
          calc symbol 2 u * symbol 2 a
              = symbol 2 u * symbol 2 a' * of 2 (a 0) + symbol 2 u * symbol 2 a' * of 2 uw := by
                rw [hsym_a, hW_mul uw rfl, add_zero, mul_assoc, of_mul_symbol_comm hi (a 0) a',
                  ← mul_assoc]
            _ = symbol 2 u * symbol 2 a' * of 2 (a 0 * uw) := by rw [of_mul, mul_add]
            _ = symbol 2 u * of 2 uU * symbol 2 b' * of 2 (-uU) := by rw [hb', haw]
            _ = symbol 2 u * (of 2 uU * of 2 uU) * symbol 2 b' := by
                rw [of_neg hi, mul_assoc (symbol 2 u * of 2 uU),
                  ← of_mul_symbol_comm hi uU b', ← mul_assoc, mul_assoc (symbol 2 u)]
            _ = 0 := by rw [of_mul_self hi, mul_zero, zero_mul]

/-- Inductive common-slot step: over a field with `-1` a square and `u`-invariant `<= 2^m`,
any sum of two `m`-symbols sharing a prefix `u : Fin r → Fˣ` collapses to a single `m`-symbol. -/
theorem top_degree_sum_two_aux (hi : ∃ i : F, i * i = -1) (m : ℕ)
    (hu : ∀ q : Fin (2 ^ m + 1) → F, ∃ v : Fin (2 ^ m + 1) → F, v ≠ 0 ∧ ∑ i, q i * v i ^ 2 = 0) :
    ∀ (d r : ℕ), r + d = m → 1 ≤ d →
      ∀ (u : Fin r → Fˣ) (a b : Fin d → Fˣ),
        ∃ c : Fin d → Fˣ, symbol 2 u * (symbol 2 a + symbol 2 b) = symbol 2 u * symbol 2 c := by
  intro d
  induction d with
  | zero => intro _ _ hd; omega
  | succ d ih =>
    intro r hrd _ u a b
    cases d with
    | zero =>
      refine ⟨fun _ ↦ a 0 * b 0, ?_⟩
      simp [symbol_one, of_mul]
    | succ d =>
      classical
      let ι := (Finset (Fin r) × {S : Finset (Fin (d + 2)) // S.Nonempty}) ⊕ Finset (Fin r) ⊕ Unit
      have hcard : 2 ^ m + 1 ≤ Fintype.card ι := by
        have h1 : Fintype.card {S : Finset (Fin (d + 2)) // S.Nonempty} = 2 ^ (d + 2) - 1 := by
          have hsub : ({S : Finset (Fin (d + 2)) // S.Nonempty} : Type _) ≃
              {S : Finset (Fin (d + 2)) // S ≠ ∅} :=
            Equiv.subtypeEquivRight (fun S ↦ Finset.nonempty_iff_ne_empty)
          rw [Fintype.card_congr hsub, Fintype.card_subtype_compl, Fintype.card_finset,
            Fintype.card_fin, Fintype.card_subtype_eq]
        have hcard_eq : Fintype.card ι = 2 ^ r * (2 ^ (d + 2) - 1) + 2 ^ r + 1 := by
          simp only [ι, Fintype.card_sum, Fintype.card_prod, Fintype.card_finset, Fintype.card_fin,
            Fintype.card_unit, h1]
          ring
        rw [hcard_eq]
        have hpow_ge : 1 ≤ 2 ^ (d + 2) := Nat.one_le_pow _ _ (by norm_num)
        have hmul : 2 ^ r * (2 ^ (d + 2) - 1) + 2 ^ r = 2 ^ (r + (d + 2)) := by
          rw [Nat.mul_sub_left_distrib, mul_one, Nat.sub_add_cancel
            (Nat.le_mul_of_pos_right _ (by omega)), ← pow_add]
        rw [hmul, hrd]
      let q : ι → F := fun z ↦
        match z with
        | Sum.inl (T, S) => (∏ i ∈ T, (u i : F)) * (∏ j ∈ S.1, (a j : F))
        | Sum.inr (Sum.inl T) => (b 0 : F) * (∏ i ∈ T, (u i : F))
        | Sum.inr (Sum.inr ()) => (b 1 : F)
      obtain ⟨v, hv0, hvsum⟩ := OMA.Uniform.Lang.isotropic_of_card_le hu hcard q
      let vA : Finset (Fin r) × Finset (Fin (d + 2)) → F := fun p ↦
        if h : p.2.Nonempty then v (Sum.inl (p.1, ⟨p.2, h⟩)) else 0
      let vB : Finset (Fin r) → F := fun T ↦ v (Sum.inr (Sum.inl T))
      let y : F := v (Sum.inr (Sum.inr ()))
      have hvA_empty : ∀ T, vA (T, ∅) = 0 := fun T ↦ by simp [vA]
      set E : F := ∑ p : Finset (Fin r) × Finset (Fin (d + 2)),
        (∏ i ∈ p.1, (u i : F)) * (∏ j ∈ p.2, (a j : F)) * vA p ^ 2
      set B : F := ∑ T : Finset (Fin r), (∏ i ∈ T, (u i : F)) * vB T ^ 2
      have hsum_eq : E + (b 0 : F) * B + (b 1 : F) * y ^ 2 = 0 := by
        rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_unique (ι := Unit)] at hvsum
        have hE : ∑ x : Finset (Fin r) × {S : Finset (Fin (d + 2)) // S.Nonempty},
            q (Sum.inl x) * v (Sum.inl x) ^ 2 = E := by
          rw [Fintype.sum_prod_type]
          rw [show E = ∑ T : Finset (Fin r), ∑ S : Finset (Fin (d + 2)),
              (∏ i ∈ T, (u i : F)) * (∏ j ∈ S, (a j : F)) * vA (T, S) ^ 2 from
              Fintype.sum_prod_type _]
          refine Finset.sum_congr rfl fun T _ ↦ ?_
          symm
          rw [← Finset.sum_subset (Finset.filter_subset Finset.Nonempty Finset.univ)]
          · refine (Finset.sum_nbij (fun s : {S : Finset (Fin (d + 2)) // S.Nonempty} ↦ s.1)
              (fun s _ ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _, s.2⟩)
              (fun s₁ _ s₂ _ h ↦ Subtype.ext h)
              (fun S hS ↦ ⟨⟨S, (Finset.mem_filter.mp hS).2⟩, Finset.mem_univ _, rfl⟩)
              (fun s _ ↦ by simp [q, vA, s.2])).symm
          · intro S _ hS
            have hSn : ¬ S.Nonempty := fun h ↦ hS (Finset.mem_filter.mpr ⟨Finset.mem_univ S, h⟩)
            simp [vA, hSn]
        have hB : ∑ T : Finset (Fin r), q (Sum.inr (Sum.inl T)) * v (Sum.inr (Sum.inl T)) ^ 2 =
            (b 0 : F) * B := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun T _ ↦ ?_
          simp only [q, vB]
          ring
        rw [hE, hB] at hvsum
        simpa [q, y, add_assoc] using hvsum
      by_cases hB0 : B = 0
      · by_cases hvBz : vB = 0
        · by_cases hE0 : E = 0
          · have hy0 : y = 0 := by
              have : (b 1 : F) * y ^ 2 = 0 := by linear_combination hsum_eq - hE0 - (b 0 : F) * hB0
              exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
                ((mul_eq_zero.mp this).resolve_left (b 1).ne_zero)
            have hvAne : vA ≠ 0 := by
              intro h
              apply hv0
              funext z
              rcases z with ⟨T, ⟨S, hS⟩⟩ | (T | ⟨⟩)
              · have := congrFun h (T, S)
                simpa [vA, hS] using this
              · exact congrFun hvBz T
              · exact hy0
            have ha0 : symbol 2 u * symbol 2 a = 0 :=
              (pfister_prefix_pure_ind hi r u (d + 1) a vA hvA_empty).2 hvAne hE0
            exact ⟨b, by rw [mul_add, ha0, zero_add]⟩
          · set e := Units.mk0 E hE0
            obtain ⟨a', ha'⟩ := (pfister_prefix_pure_ind hi r u (d + 1) a vA hvA_empty).1 e rfl
            have hy0 : y ≠ 0 := by
              intro hy
              have : E = 0 := by linear_combination hsum_eq - (b 0 : F) * hB0 - (b 1 : F) * (by simp [hy] : y ^ 2 = 0)
              exact hE0 this
            have hb1 : b 1 = -(e * (Units.mk0 y hy0)⁻¹ ^ 2) := Units.ext (by
              simp only [Units.val_neg, Units.val_mul, Units.val_pow_eq_pow_val,
                Units.val_inv_eq_inv_val, Units.val_mk0, e]
              field_simp
              linear_combination hsum_eq - (b 0 : F) * hB0)
            let b' : Fin (d + 1) → Fˣ := Fin.cons (b 0) (fun j ↦ b j.succ.succ)
            have hb' : symbol 2 u * symbol 2 b = symbol 2 u * of 2 e * symbol 2 b' := by
              rw [symbol_succ 2 b, symbol_succ 2 (fun j ↦ b j.succ), show b (0 : Fin (d + 1)).succ = b 1 from rfl,
                hb1, of_neg hi, of_mul, of_sq, add_zero, symbol_cons]
              have : of 2 (b 0) * (of 2 e * symbol 2 (fun j : Fin d ↦ b j.succ.succ)) =
                  of 2 e * (of 2 (b 0) * symbol 2 (fun j : Fin d ↦ b j.succ.succ)) := by
                rw [← mul_assoc, of_comm hi (b 0) e, mul_assoc]
              rw [this, mul_assoc]
            let u' : Fin (r + 1) → Fˣ := Fin.snoc u e
            have hu' : symbol 2 u' = symbol 2 u * of 2 e := by
              have hsnoc : u' = Fin.append u (fun _ : Fin 1 ↦ e) := by
                funext i
                refine Fin.lastCases ?_ (fun j ↦ ?_) i
                · simp [u', Fin.append, Fin.addCases]
                · simp [u', Fin.append, Fin.addCases]
              rw [hsnoc, symbol_append, symbol_one]
            obtain ⟨c', hc'⟩ := ih (r + 1) (by omega) (by omega) u' a' b'
            refine ⟨Fin.cons e c', ?_⟩
            rw [mul_add, ha', hb', ← mul_add, ← hu', hc', hu', symbol_cons, mul_assoc]
        · have hu0 : symbol 2 u = 0 := pfister_full_zero hi u vB hvBz hB0
          exact ⟨a, by rw [hu0, zero_mul, zero_mul]⟩
      · set uB := Units.mk0 B hB0
        have huB : symbol 2 u * of 2 uB = 0 := pfister_full_mul hi u vB uB rfl
        by_cases hE0 : E = 0
        · have hy0 : y ≠ 0 := by
            intro hy
            have : (b 0 : F) * B = 0 := by
              linear_combination hsum_eq - hE0 - (b 1 : F) * (by simp [hy] : y ^ 2 = 0)
            exact hB0 ((mul_eq_zero.mp this).resolve_left (b 0).ne_zero)
          have hb1 : b 1 = -(b 0 * uB * (Units.mk0 y hy0)⁻¹ ^ 2) := Units.ext (by
            simp only [Units.val_neg, Units.val_mul, Units.val_pow_eq_pow_val,
              Units.val_inv_eq_inv_val, Units.val_mk0, uB]
            field_simp
            linear_combination hsum_eq - hE0)
          have hb0 : symbol 2 u * symbol 2 b = 0 := by
            rw [symbol_succ 2 b, symbol_succ 2 (fun j ↦ b j.succ), show b (0 : Fin (d + 1)).succ = b 1 from rfl,
              hb1, of_neg hi, of_mul, of_mul, of_sq, add_zero]
            have hstep : symbol 2 u * (of 2 (b 0) * (of 2 (b 0) + of 2 uB)) = 0 := by
              rw [mul_add, of_mul_self hi, zero_add, of_comm hi (b 0) uB, ← mul_assoc, huB, zero_mul]
            rw [← mul_assoc (of 2 (b 0)), ← mul_assoc (symbol 2 u), hstep, zero_mul]
          exact ⟨a, by rw [mul_add, hb0, add_zero]⟩
        · set e := Units.mk0 E hE0
          obtain ⟨a', ha'⟩ := (pfister_prefix_pure_ind hi r u (d + 1) a vA hvA_empty).1 e rfl
          have hslot : of 2 (b 0 * uB) * of 2 (b 1) = of 2 (-e) * of 2 (b 0 * uB * b 1) :=
            slot2 hi (b 0 * uB) (b 1) (-e) 1 y (by
              simp only [Units.val_neg, Units.val_mul, uB, e, Units.val_mk0, one_pow, mul_one]
              linear_combination -hsum_eq)
          rw [of_neg hi] at hslot
          let b' : Fin (d + 1) → Fˣ := Fin.cons (b 0 * uB * b 1) (fun j ↦ b j.succ.succ)
          have hb' : symbol 2 u * symbol 2 b = symbol 2 u * of 2 e * symbol 2 b' := by
            rw [symbol_succ 2 b, symbol_succ 2 (fun j ↦ b j.succ),
              show b (0 : Fin (d + 1)).succ = b 1 from rfl, symbol_cons]
            have h1 : symbol 2 u * of 2 (b 0) = symbol 2 u * of 2 (b 0 * uB) := by
              rw [of_mul, mul_add, huB, add_zero]
            rw [← mul_assoc (symbol 2 u), h1, mul_assoc (symbol 2 u), ← mul_assoc (of 2 (b 0 * uB)),
              hslot, mul_assoc (of 2 e), ← mul_assoc (symbol 2 u)]
          let u' : Fin (r + 1) → Fˣ := Fin.snoc u e
          have hu' : symbol 2 u' = symbol 2 u * of 2 e := by
            have hsnoc : u' = Fin.append u (fun _ : Fin 1 ↦ e) := by
              funext i
              refine Fin.lastCases ?_ (fun j ↦ ?_) i
              · simp [u', Fin.append, Fin.addCases]
              · simp [u', Fin.append, Fin.addCases]
            rw [hsnoc, symbol_append, symbol_one]
          obtain ⟨c', hc'⟩ := ih (r + 1) (by omega) (by omega) u' a' b'
          refine ⟨Fin.cons e c', ?_⟩
          rw [mul_add, ha', hb', ← mul_add, ← hu', hc', hu', symbol_cons, mul_assoc]

/-- Matzri's Kummer norm form at `p = 2`: for any `k + 1` symbols in `K^M_2(F)/2`, there exists
a `(2k + 3)`-variable diagonal quadratic form whose nonzero values can be placed as a slot of
the last symbol and whose isotropy shortens the sum to `k` symbols. -/
theorem kummer_form_exists (hi : ∃ i : F, i * i = -1) :
    ∀ (k : ℕ) (s : Fin (k + 1) → Fˣ × Fˣ),
      ∃ q : Fin (2 * k + 3) → F,
        (∀ (v : Fin (2 * k + 3) → F) (e : Fˣ),
          (e : F) = ∑ i, q i * v i ^ 2 →
          ∃ (s' : Fin k → Fˣ × Fˣ) (d : Fˣ),
            (∑ i, of 2 (s i).1 * of 2 (s i).2) =
              (∑ i, of 2 (s' i).1 * of 2 (s' i).2) + of 2 e * of 2 d) ∧
        (∀ (v : Fin (2 * k + 3) → F), v ≠ 0 →
          ∑ i, q i * v i ^ 2 = 0 →
          ∃ (s' : Fin k → Fˣ × Fˣ),
            (∑ i, of 2 (s i).1 * of 2 (s i).2) =
              ∑ i, of 2 (s' i).1 * of 2 (s' i).2) := by
  intro k
  induction k with
  | zero =>
    intro s
    refine ⟨![((s 0).1 : F), ((s 0).2 : F), ((s 0).1 : F) * ((s 0).2 : F)], ?_, ?_⟩
    · intro v e he
      have he' : (e : F) = (s 0).1 * v 0 ^ 2 + (s 0).2 * v 1 ^ 2 +
          (s 0).1 * (s 0).2 * v 2 ^ 2 := by
        simpa [Fin.sum_univ_three] using he
      obtain ⟨f, hf⟩ := slot3 hi (s 0).1 (s 0).2 e (v 0) (v 1) (v 2) he'
      exact ⟨Fin.elim0, f, by simpa using hf⟩
    · intro v hv hsum
      have hsum' : ((s 0).1 : F) * v 0 ^ 2 + (s 0).2 * v 1 ^ 2 +
          (s 0).1 * (s 0).2 * v 2 ^ 2 = 0 := by
        simpa [Fin.sum_univ_three] using hsum
      have hne : v 0 ≠ 0 ∨ v 1 ≠ 0 ∨ v 2 ≠ 0 := by
        by_contra h; push Not at h
        apply hv; funext j; fin_cases j <;> simp [h]
      exact ⟨Fin.elim0, by simpa using slot3_zero hi (s 0).1 (s 0).2 (v 0) (v 1) (v 2) hne hsum'⟩
  | succ k ih =>
    intro s
    let sPrev : Fin (k + 1) → Fˣ × Fˣ := fun i ↦ s i.castSucc
    let a : Fˣ := (s (Fin.last (k + 1))).1
    let b : Fˣ := (s (Fin.last (k + 1))).2
    obtain ⟨qPrev, hRep, hIso⟩ := ih sPrev
    let q : Fin (2 * (k + 1) + 3) → F := fun i ↦
      if h : i.val < 2 * k + 3 then (a : F) * qPrev ⟨i.val, h⟩
      else if i.val = 2 * k + 3 then (b : F)
      else (a : F) * (b : F)
    have hsum_s : (∑ i : Fin (k + 2), of 2 (s i).1 * of 2 (s i).2) =
        (∑ i : Fin (k + 1), of 2 (sPrev i).1 * of 2 (sPrev i).2) + of 2 a * of 2 b := by
      rw [Fin.sum_univ_castSucc]
    have hsplit_q : ∀ v : Fin (2 * (k + 1) + 3) → F,
        ∑ i, q i * v i ^ 2 =
          (a : F) * (∑ j : Fin (2 * k + 3), qPrev j * v ⟨j.val, by omega⟩ ^ 2) +
          (b : F) * (v ⟨2 * k + 3, by omega⟩ ^ 2 + (a : F) * v ⟨2 * k + 4, by omega⟩ ^ 2) := by
      intro v
      rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
      have hlast1 : q (Fin.last (2 * (k + 1) + 2)) = (a : F) * (b : F) := by
        simp only [q, Fin.val_last]
        rw [dif_neg (by omega), if_neg (by omega)]
      have hlast2 : q (Fin.last (2 * (k + 1) + 1)).castSucc = (b : F) := by
        simp only [q, Fin.val_castSucc, Fin.val_last]
        rw [dif_neg (by omega), if_pos (by omega)]
      have hhead : ∑ j : Fin (2 * (k + 1) + 1),
          q (j.castSucc.castSucc) * v (j.castSucc.castSucc) ^ 2 =
          (a : F) * ∑ j : Fin (2 * k + 3), qPrev j * v ⟨j.val, by omega⟩ ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_nbij (fun j : Fin (2 * (k + 1) + 1) ↦ ⟨j.val, by omega⟩)
          (fun _ _ ↦ Finset.mem_univ _)
          (fun j₁ _ j₂ _ h ↦ Fin.ext (congrArg Fin.val h))
          (fun j _ ↦ ⟨⟨j.val, by omega⟩, Finset.mem_univ _, Fin.ext rfl⟩)
          (fun j _ ↦ ?_)
        have hj : (j.castSucc.castSucc : Fin (2 * (k + 1) + 3)).val < 2 * k + 3 := by
          have := j.isLt; simp; omega
        have hveq : (j.castSucc.castSucc : Fin (2 * (k + 1) + 3)) = ⟨j.val, by omega⟩ :=
          Fin.ext (by simp)
        simp only [q, dif_pos hj]
        have hqeq : (⟨(j.castSucc.castSucc : Fin (2 * (k + 1) + 3)).val, hj⟩ : Fin (2 * k + 3)) =
            ⟨j.val, by omega⟩ := Fin.ext (by simp)
        rw [hqeq, hveq]
        ring
      have hidx1 : (Fin.last (2 * (k + 1) + 2) : Fin (2 * (k + 1) + 3)) = ⟨2 * k + 4, by omega⟩ :=
        Fin.ext (by simp; omega)
      have hidx2 : ((Fin.last (2 * (k + 1) + 1)).castSucc : Fin (2 * (k + 1) + 3)) =
          ⟨2 * k + 3, by omega⟩ :=
        Fin.ext (by simp; omega)
      rw [hhead, hlast1, hlast2, hidx1, hidx2]
      ring
    refine ⟨q, ?_, ?_⟩
    · intro v e he
      rw [hsplit_q] at he
      let vP : Fin (2 * k + 3) → F := fun j ↦ v ⟨j.val, by omega⟩
      let x : F := v ⟨2 * k + 3, by omega⟩
      let z : F := v ⟨2 * k + 4, by omega⟩
      set N : F := ∑ j, qPrev j * vP j ^ 2
      set W : F := x ^ 2 + (a : F) * z ^ 2
      have he' : (e : F) = (a : F) * N + (b : F) * W := he
      by_cases hN0 : N = 0
      · by_cases hvPz : vP = 0
        · rw [hN0, mul_zero, zero_add] at he'
          have hW0 : W ≠ 0 := by intro h; rw [h, mul_zero] at he'; exact e.ne_zero he'
          set uW := Units.mk0 W hW0
          have hauW : of 2 uW * of 2 a = 0 := norm_slot hi a uW x z rfl
          have heeq : e = b * uW := Units.ext (by simp [he', uW])
          refine ⟨sPrev, a, ?_⟩
          rw [hsum_s, heeq, of_mul, add_mul, hauW, add_zero, of_comm hi b a]
        · obtain ⟨s', hs'⟩ := hIso vP hvPz hN0
          refine ⟨Fin.snoc s' (a, b), 1, ?_⟩
          rw [hsum_s, hs']
          conv_rhs => rw [Fin.sum_univ_castSucc]
          simp [of_one]
      · set uN := Units.mk0 N hN0
        obtain ⟨s', d, hs'⟩ := hRep vP uN rfl
        by_cases hW0 : W = 0
        · rw [hW0, mul_zero, add_zero] at he'
          have heeq : e = a * uN := Units.ext (by simp [he', uN])
          refine ⟨Fin.snoc s' (uN, d * b), b, ?_⟩
          rw [hsum_s, hs']
          conv_rhs => rw [Fin.sum_univ_castSucc]
          simp only [Fin.snoc_castSucc, Fin.snoc_last, add_assoc]
          congr 1
          rw [heeq, of_mul 2 d b, of_mul 2 a uN, mul_add, add_mul, add_assoc,
            add_comm (of 2 a * of 2 b), ← add_assoc (of 2 uN * of 2 b), add_self_eq_zero, zero_add]
        · set uW := Units.mk0 W hW0
          have hauW : of 2 a * of 2 uW = 0 := by
            rw [of_comm hi]; exact norm_slot hi a uW x z rfl
          have hst : of 2 (a * uN) * of 2 (b * uW) = of 2 e * of 2 (a * uN * (b * uW)) :=
            steinberg2 hi (a * uN) (b * uW) e (by simp [uN, uW, he'])
          refine ⟨Fin.snoc s' (uN, d * (b * uW)), a * uN * (b * uW), ?_⟩
          rw [hsum_s, hs']
          conv_rhs => rw [Fin.sum_univ_castSucc]
          simp only [Fin.snoc_castSucc, Fin.snoc_last, add_assoc]
          congr 1
          have hab : of 2 a * of 2 b = of 2 a * of 2 (b * uW) := by
            rw [of_mul, mul_add, hauW, add_zero]
          rw [hab, ← hst, of_mul 2 d (b * uW), of_mul 2 a uN, mul_add, add_mul, add_assoc,
            add_comm (of 2 a * of 2 (b * uW)), ← add_assoc (of 2 uN * of 2 (b * uW)),
            add_self_eq_zero, zero_add]
    · intro v hv hsum
      rw [hsplit_q] at hsum
      let vP : Fin (2 * k + 3) → F := fun j ↦ v ⟨j.val, by omega⟩
      let x : F := v ⟨2 * k + 3, by omega⟩
      let z : F := v ⟨2 * k + 4, by omega⟩
      set N : F := ∑ j, qPrev j * vP j ^ 2
      set W : F := x ^ 2 + (a : F) * z ^ 2
      have hsum' : (a : F) * N + (b : F) * W = 0 := hsum
      by_cases hN0 : N = 0
      · by_cases hvPz : vP = 0
        · rw [hN0, mul_zero, zero_add] at hsum'
          have hW0 : W = 0 := (mul_eq_zero.mp hsum').resolve_left b.ne_zero
          have hxz : x ≠ 0 ∨ z ≠ 0 := by
            by_contra h; push Not at h
            apply hv; funext i
            have hi_lt : i.val < 2 * (k + 1) + 3 := i.isLt
            by_cases hi1 : i.val < 2 * k + 3
            · exact congrFun hvPz ⟨i.val, hi1⟩
            · by_cases hi2 : i.val = 2 * k + 3
              · have : i = ⟨2 * k + 3, by omega⟩ := Fin.ext hi2
                rw [this]; exact h.1
              · have : i = ⟨2 * k + 4, by omega⟩ := Fin.ext (by simp; omega)
                rw [this]; exact h.2
          have hz0 : z ≠ 0 := by
            intro hz
            have hx0 : x = 0 := by
              have : x ^ 2 = 0 := by simpa [W, hz] using hW0
              exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
            rcases hxz with h1 | h2 <;> contradiction
          have hx0 : x ≠ 0 := by
            intro hx
            have : (a : F) * z ^ 2 = 0 := by simpa [W, hx] using hW0
            exact hz0 (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
              ((mul_eq_zero.mp this).resolve_left a.ne_zero))
          have haeq : a = -(Units.mk0 x hx0 * (Units.mk0 z hz0)⁻¹) ^ 2 := Units.ext (by
            simp only [Units.val_neg, Units.val_pow_eq_pow_val, Units.val_mul,
              Units.val_inv_eq_inv_val, Units.val_mk0]
            field_simp
            linear_combination hW0)
          refine ⟨sPrev, ?_⟩
          rw [hsum_s, haeq, of_neg hi, of_sq, zero_mul, add_zero]
        · obtain ⟨s', hs'⟩ := hIso vP hvPz hN0
          refine ⟨Fin.snoc s' (a, b), ?_⟩
          rw [hsum_s, hs']
          conv_rhs => rw [Fin.sum_univ_castSucc]
          simp
      · set uN := Units.mk0 N hN0
        obtain ⟨s', d, hs'⟩ := hRep vP uN rfl
        have hW0 : W ≠ 0 := by
          intro h; rw [h, mul_zero, add_zero] at hsum'
          exact hN0 ((mul_eq_zero.mp hsum').resolve_left a.ne_zero)
        set uW := Units.mk0 W hW0
        have hauW : of 2 a * of 2 uW = 0 := by
          rw [of_comm hi]; exact norm_slot hi a uW x z rfl
        have hbw : b * uW = -(a * uN) := Units.ext (by
          simp only [Units.val_mul, Units.val_neg, uN, uW, Units.val_mk0]
          linear_combination hsum')
        refine ⟨Fin.snoc s' (uN, d * (b * uW)), ?_⟩
        rw [hsum_s, hs']
        conv_rhs => rw [Fin.sum_univ_castSucc]
        simp only [Fin.snoc_castSucc, Fin.snoc_last, add_assoc]
        congr 1
        have hab : of 2 a * of 2 b = of 2 a * of 2 (b * uW) := by
          rw [of_mul, mul_add, hauW, add_zero]
        have hkill : of 2 (a * uN) * of 2 (b * uW) = 0 := by
          rw [hbw, of_neg hi, of_mul_self hi]
        rw [hab, of_mul 2 d (b * uW), mul_add]
        have hcalc : of 2 uN * of 2 (b * uW) = of 2 a * of 2 (b * uW) := by
          rw [of_mul 2 a uN, add_mul] at hkill
          have := eq_neg_of_add_eq_zero_right hkill
          rwa [neg_eq_self] at this
        rw [hcalc]

theorem exists_sqrt_neg_one (m : ℕ) : ∃ i : MvRatFunc (Fin m) ℂ, i * i = -1 :=
  ⟨algebraMap (MvPolynomial (Fin m) ℂ) _ (MvPolynomial.C Complex.I), by
    rw [← map_mul, ← MvPolynomial.C_mul, Complex.I_mul_I, MvPolynomial.C_neg,
      MvPolynomial.C_1, map_neg, map_one]⟩

/-- Vanishing propagation: `K^M_n(F)/ℓ = 0` implies `K^M_{n+1}(F)/ℓ = 0`. -/
theorem grade_succ_eq_bot (ℓ n : ℕ) (h : grade F ℓ n = ⊥) :
    grade F ℓ (n + 1) = ⊥ := by
  rw [eq_bot_iff, MilnorK.grade, AddSubgroup.closure_le]
  rintro _ ⟨s, rfl⟩
  have hs := symbol_mem_grade F ℓ (fun i ↦ s i.succ)
  rw [h, AddSubgroup.mem_bot] at hs
  rw [SetLike.mem_coe, AddSubgroup.mem_bot, symbol_succ, hs, mul_zero]

theorem grade_eq_bot_of_le (ℓ k : ℕ) (h : grade F ℓ k = ⊥) :
    ∀ n, k ≤ n → grade F ℓ n = ⊥ := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact h
  | succ n _ ih => exact grade_succ_eq_bot ℓ n ih

/-- Unconditional mod-2 vanishing for ALL `m >= 0` and ALL `n > m`:
`K^M_n(C(x_1, ..., x_m))/2 = 0`. -/
theorem zero_mem_two_of_lt (m n : ℕ) (hmn : m < n) :
    0 ∈ symbolLengthBounds (MvRatFunc (Fin m) ℂ) 2 n := by
  rw [zero_mem_symbolLengthBounds_iff]
  refine grade_eq_bot_of_le 2 (m + 1) ?_ n hmn
  rw [eq_bot_iff, MilnorK.grade, AddSubgroup.closure_le]
  rintro _ ⟨s, rfl⟩
  rw [SetLike.mem_coe, AddSubgroup.mem_bot]
  have hcard : 2 ^ m + 1 ≤ Fintype.card (Finset (Fin (m + 1))) := by
    rw [Fintype.card_finset, Fintype.card_fin, pow_succ]
    have : 1 ≤ 2 ^ m := Nat.one_le_pow m 2 (by norm_num)
    omega
  obtain ⟨v, hv0, hvsum⟩ := OMA.Uniform.Lang.isotropic_of_card_le
    (OMA.Uniform.Lang.isotropic_pow_two_succ m) hcard
    (fun S : Finset (Fin (m + 1)) ↦ ∏ j ∈ S, (s j : MvRatFunc (Fin m) ℂ))
  exact pfister_full_zero (exists_sqrt_neg_one m) s v hv0 hvsum

/-- Unconditional Matzri theorem at `p = 2` for ALL `m >= 1`:
`2^(m - 1) - 1 ∈ symbolLengthBounds (C(x_1, ..., x_m)) 2 2`. -/
theorem matzri_two (m : ℕ) (hm : 1 ≤ m) :
    2 ^ (m - 1) - 1 ∈ symbolLengthBounds (MvRatFunc (Fin m) ℂ) 2 2 := by
  rcases (by omega : m = 1 ∨ 2 ≤ m) with rfl | hm2
  · simpa using zero_mem_two_of_lt 1 2 (by omega)
  set K := 2 ^ (m - 1) - 1 with hK
  have hKpos : 1 ≤ K := by
    have hge : 2 ^ 1 ≤ 2 ^ (m - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h2K : 2 * K + 3 = 2 ^ m + 1 := by
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    simp only [hK, Nat.add_sub_cancel, pow_succ]
    have : 1 ≤ 2 ^ m' := Nat.one_le_pow _ _ (by norm_num)
    omega
  have hshort : ∀ s : Fin (K + 1) → (MvRatFunc (Fin m) ℂ)ˣ × (MvRatFunc (Fin m) ℂ)ˣ,
      ∃ s' : Fin K → (MvRatFunc (Fin m) ℂ)ˣ × (MvRatFunc (Fin m) ℂ)ˣ,
        (∑ i, of 2 (s i).1 * of 2 (s i).2) = ∑ i, of 2 (s' i).1 * of 2 (s' i).2 := by
    intro s
    obtain ⟨q, -, hIso⟩ := kummer_form_exists (exists_sqrt_neg_one m) K s
    have hcard : 2 ^ m + 1 ≤ Fintype.card (Fin (2 * K + 3)) := by
      rw [Fintype.card_fin]; omega
    obtain ⟨v, hv0, hvsum⟩ := OMA.Uniform.Lang.isotropic_of_card_le
      (OMA.Uniform.Lang.isotropic_pow_two_succ m) hcard q
    exact hIso v hv0 hvsum
  have hrep : ∀ x ∈ grade (MvRatFunc (Fin m) ℂ) 2 2,
      ∃ k ≤ K, ∃ s : Fin k → (MvRatFunc (Fin m) ℂ)ˣ × (MvRatFunc (Fin m) ℂ)ˣ,
        x = ∑ i, of 2 (s i).1 * of 2 (s i).2 := by
    intro x hx
    induction hx using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨s, rfl⟩ := hy
      refine ⟨1, hKpos, fun _ ↦ (s 0, s 1), ?_⟩
      simp [symbol_succ]
    | zero => exact ⟨0, Nat.zero_le K, Fin.elim0, by simp⟩
    | neg y _ hy =>
      rwa [neg_eq_self]
    | add y z hy_mem hz_mem hy hz =>
      clear hy_mem hz_mem
      obtain ⟨k1, hk1, s1, rfl⟩ := hy
      obtain ⟨k2, hk2, s2, rfl⟩ := hz
      have hadd_one : ∀ (k : ℕ) (hk : k ≤ K)
          (t : Fin k → (MvRatFunc (Fin m) ℂ)ˣ × (MvRatFunc (Fin m) ℂ)ˣ)
          (ab : (MvRatFunc (Fin m) ℂ)ˣ × (MvRatFunc (Fin m) ℂ)ˣ),
          ∃ k' ≤ K, ∃ t' : Fin k' → (MvRatFunc (Fin m) ℂ)ˣ × (MvRatFunc (Fin m) ℂ)ˣ,
            (∑ i, of 2 (t i).1 * of 2 (t i).2) + of 2 ab.1 * of 2 ab.2 =
              ∑ i, of 2 (t' i).1 * of 2 (t' i).2 := by
        intro k hk t ab
        by_cases hlt : k < K
        · refine ⟨k + 1, by omega, Fin.snoc t ab, ?_⟩
          rw [Fin.sum_univ_castSucc]
          simp
        · have heq : k = K := by omega
          subst heq
          obtain ⟨t', ht'⟩ := hshort (Fin.snoc t ab)
          refine ⟨K, le_rfl, t', ?_⟩
          rw [← ht', Fin.sum_univ_castSucc]
          simp
      induction k2 with
      | zero => exact ⟨k1, hk1, s1, by simp⟩
      | succ k2 ih2 =>
        obtain ⟨k3, hk3, s3, hs3⟩ := ih2 (by omega) (fun i ↦ s2 i.castSucc)
        obtain ⟨k4, hk4, s4, hs4⟩ := hadd_one k3 hk3 s3 (s2 (Fin.last k2))
        refine ⟨k4, hk4, s4, ?_⟩
        rw [Fin.sum_univ_castSucc, ← add_assoc, hs3, hs4]
  intro x hx
  obtain ⟨k, hk, s, rfl⟩ := hrep x hx
  refine ⟨k, hk, fun i ↦ ![(s i).1, (s i).2], ?_⟩
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp [symbol_pair]

/-- Unconditional mod-2 top-degree cyclicity for ALL `m >= 1`:
every class in `K^M_m(C(x_1, ..., x_m))/2` is a single symbol. -/
theorem top_degree_two (m : ℕ) (hm : 1 ≤ m) :
    1 ∈ symbolLengthBounds (MvRatFunc (Fin m) ℂ) 2 m := by
  have hsingle : ∀ x ∈ grade (MvRatFunc (Fin m) ℂ) 2 m,
      ∃ s : Fin m → (MvRatFunc (Fin m) ℂ)ˣ, x = symbol 2 s := by
    intro x hx
    induction hx using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨s, rfl⟩ := hy
      exact ⟨s, rfl⟩
    | zero =>
      refine ⟨fun _ ↦ 1, ?_⟩
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      rw [symbol_succ, of_one, zero_mul]
    | neg y _ hy =>
      rwa [neg_eq_self]
    | add y z _ _ hy hz =>
      obtain ⟨a, rfl⟩ := hy
      obtain ⟨b, rfl⟩ := hz
      obtain ⟨c, hc⟩ := top_degree_sum_two_aux (exists_sqrt_neg_one m) m
        (OMA.Uniform.Lang.isotropic_pow_two_succ m) m 0 (Nat.zero_add m) hm Fin.elim0 a b
      rw [symbol_zero, one_mul, one_mul] at hc
      exact ⟨c, hc⟩
  intro x hx
  obtain ⟨s, rfl⟩ := hsingle x hx
  exact ⟨1, le_rfl, fun _ ↦ s, by simp⟩

end OMA.Uniform.Mod2


namespace OMA.Uniform.BaseCases

open MilnorK MvPolynomial

/-- `C(x_1, ..., x_0) = C`: every element of `MvRatFunc (Fin 0) ℂ` is a constant. -/
theorem fin0_const (x : MvRatFunc (Fin 0) ℂ) :
    ∃ c : ℂ, x = algebraMap (MvPolynomial (Fin 0) ℂ) (MvRatFunc (Fin 0) ℂ) (C c) := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (MvPolynomial (Fin 0) ℂ) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  set ca := coeff 0 a
  set cb := coeff 0 b
  have ha : a = C ca := eq_C_of_isEmpty a
  have hb' : b = C cb := eq_C_of_isEmpty b
  have hcb : cb ≠ 0 := by
    intro h; apply hb0; rw [hb', h, C_0]
  have hinj : Function.Injective
      (algebraMap (MvPolynomial (Fin 0) ℂ) (MvRatFunc (Fin 0) ℂ)) :=
    IsFractionRing.injective _ _
  have hbm : algebraMap (MvPolynomial (Fin 0) ℂ) (MvRatFunc (Fin 0) ℂ) b ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr hb0
  refine ⟨ca / cb, ?_⟩
  rw [div_eq_iff hbm, ← map_mul]
  congr 1
  rw [hb', ← C_mul, div_mul_cancel₀ ca hcb, ← ha]

/-- `m = 0`, `n >= 1`, all primes `p`: `K^M_n(C)/p = 0`. -/
theorem m_zero (n p : ℕ) (hn : 0 < n) (hp : p.Prime) :
    0 ∈ symbolLengthBounds (MvRatFunc (Fin 0) ℂ) p n := by
  rw [zero_mem_symbolLengthBounds_iff]
  refine grade_eq_bot_of_forall_exists_pow_eq _ p (fun u ↦ ?_) hn.ne'
  obtain ⟨c, hc⟩ := fin0_const (u : MvRatFunc (Fin 0) ℂ)
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq c hp.pos
  have hz0 : algebraMap (MvPolynomial (Fin 0) ℂ) (MvRatFunc (Fin 0) ℂ) (C z) ≠ 0 := by
    intro h
    apply u.ne_zero
    rw [hc, ← hz, C_pow, map_pow, h, zero_pow hp.ne_zero]
  refine ⟨Units.mk0 _ hz0, Units.ext ?_⟩
  simp only [Units.val_pow_eq_pow_val, Units.val_mk0]
  rw [hc, ← hz, C_pow, map_pow]

-- `K_2(C(x))/p = 0` via Steinberg relations (credit: @chris01-dev, degree_two_isLeast.R1).

theorem kneg_mul {F : Type*} [Field F] {p : ℕ} (A B : MilnorK F p) (h : A * B = 0) :
    -A * B = 0 := by
  have h2 : -A + A = 0 := neg_add_cancel A
  have h3 : (-A + A) * B = 0 := by rw [h2, zero_mul]
  rw [add_mul, h, add_zero] at h3
  exact h3

theorem kmul_neg {F : Type*} [Field F] {p : ℕ} (A B : MilnorK F p) (h : A * B = 0) :
    A * -B = 0 := by
  have h2 : -B + B = 0 := neg_add_cancel B
  have h3 : A * (-B + B) = 0 := by rw [h2, mul_zero]
  rw [mul_add, h, add_zero] at h3
  exact h3

theorem kof_neg_mul {F : Type*} [Field F] {p : ℕ} (A B : MilnorK F p) (h : -A * B = 0) :
    A * B = 0 := by
  have h2 : -A + A = 0 := neg_add_cancel A
  have h3 : (-A + A) * B = 0 := by rw [h2, zero_mul]
  rw [add_mul, h, zero_add] at h3
  exact h3

theorem kof_mul_neg {F : Type*} [Field F] {p : ℕ} (A B : MilnorK F p) (h : A * -B = 0) :
    A * B = 0 := by
  have h2 : -B + B = 0 := neg_add_cancel B
  have h3 : A * (-B + B) = 0 := by rw [h2, mul_zero]
  rw [mul_add, h, zero_add] at h3
  exact h3

theorem units_gen (H : Subgroup (MvRatFunc (Fin 1) ℂ)ˣ)
    (hc : ∀ (c : ℂ) (u : (MvRatFunc (Fin 1) ℂ)ˣ),
      (u : MvRatFunc (Fin 1) ℂ) = algebraMap (MvPolynomial (Fin 1) ℂ) (MvRatFunc (Fin 1) ℂ) (C c) →
        u ∈ H)
    (hx : ∀ (a : ℂ) (u : (MvRatFunc (Fin 1) ℂ)ˣ),
      (u : MvRatFunc (Fin 1) ℂ) =
        algebraMap (MvPolynomial (Fin 1) ℂ) (MvRatFunc (Fin 1) ℂ) (X 0 - C a) → u ∈ H)
    (u : (MvRatFunc (Fin 1) ℂ)ˣ) : u ∈ H := by
  let M : Submonoid (MvRatFunc (Fin 1) ℂ) :=
    { carrier := {x | ∀ v : (MvRatFunc (Fin 1) ℂ)ˣ, (v : MvRatFunc (Fin 1) ℂ) = x → v ∈ H}
      one_mem' := by
        intro v hv
        have : v = 1 := Units.ext hv
        rw [this]; exact H.one_mem
      mul_mem' := by
        intro x y hx' hy' v hv
        have hxy : x * y ≠ 0 := hv ▸ v.ne_zero
        have hx0 : x ≠ 0 := left_ne_zero_of_mul hxy
        have hy0 : y ≠ 0 := right_ne_zero_of_mul hxy
        have : v = Units.mk0 x hx0 * Units.mk0 y hy0 := Units.ext (by simp [hv])
        rw [this]
        exact H.mul_mem (hx' _ rfl) (hy' _ rfl) }
  have hpoly : ∀ q : MvPolynomial (Fin 1) ℂ,
      algebraMap (MvPolynomial (Fin 1) ℂ) (MvRatFunc (Fin 1) ℂ) q ∈ M := by
    intro q
    have hsurj : ∀ q : MvPolynomial (Fin 1) ℂ,
        ∃ r : Polynomial ℂ, Polynomial.eval₂RingHom MvPolynomial.C (X 0) r = q := by
      intro q
      induction q using MvPolynomial.induction_on with
      | C a => exact ⟨Polynomial.C a, by simp⟩
      | add f g hf hg =>
        obtain ⟨rf, rfl⟩ := hf
        obtain ⟨rg, rfl⟩ := hg
        exact ⟨rf + rg, map_add _ _ _⟩
      | mul_X f i hf =>
        obtain ⟨rf, rfl⟩ := hf
        refine ⟨rf * Polynomial.X, ?_⟩
        have : i = 0 := Subsingleton.elim _ _
        simp [this]
    obtain ⟨r, rfl⟩ := hsurj q
    rw [(IsAlgClosed.splits r).eq_prod_roots]
    rw [map_mul, map_mul, map_multiset_prod, map_multiset_prod]
    refine M.mul_mem ?_ (M.multiset_prod_mem _ ?_)
    · intro v hv
      refine hc r.leadingCoeff v ?_
      simpa using hv
    · intro x hx'
      simp only [Multiset.map_map, Multiset.mem_map] at hx'
      obtain ⟨a, -, rfl⟩ := hx'
      intro v hv
      refine hx a v ?_
      simpa using hv
  obtain ⟨n, d, hd, hnd⟩ := IsFractionRing.div_surjective (A := MvPolynomial (Fin 1) ℂ)
    (u : MvRatFunc (Fin 1) ℂ)
  have hd0 : algebraMap (MvPolynomial (Fin 1) ℂ) (MvRatFunc (Fin 1) ℂ) d ≠ 0 := by
    intro h
    apply u.ne_zero
    rw [← hnd, h, div_zero]
  have hn0 : algebraMap (MvPolynomial (Fin 1) ℂ) (MvRatFunc (Fin 1) ℂ) n ≠ 0 := by
    intro h
    apply u.ne_zero
    rw [← hnd, h, zero_div]
  have : u = Units.mk0 _ hn0 * (Units.mk0 _ hd0)⁻¹ :=
    Units.ext (by simp [← hnd, div_eq_mul_inv])
  rw [this]
  exact H.mul_mem (hpoly n _ rfl) (H.inv_mem (hpoly d _ rfl))

theorem algMap_ne_zero {q : MvPolynomial (Fin 1) ℂ} (hq : q ≠ 0) :
    algebraMap (MvPolynomial (Fin 1) ℂ) (MvRatFunc (Fin 1) ℂ) q ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hq

theorem of_const_eq_zero (p : ℕ) (hp : 0 < p) (c : ℂ) (u : (MvRatFunc (Fin 1) ℂ)ˣ)
    (hu : (u : MvRatFunc (Fin 1) ℂ) =
      algebraMap (MvPolynomial (Fin 1) ℂ) (MvRatFunc (Fin 1) ℂ) (C c)) :
    MilnorK.of p u = 0 := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq c hp
  have hz0 : algebraMap (MvPolynomial (Fin 1) ℂ) (MvRatFunc (Fin 1) ℂ) (C z) ≠ 0 := by
    intro h
    apply u.ne_zero
    rw [hu, ← hz, map_pow, map_pow, h, zero_pow hp.ne']
  have : u = (Units.mk0 _ hz0) ^ p := Units.ext (by simp [hu, ← hz])
  rw [this, of_pow, nsmul_eq_mul, natCast_eq_zero, zero_mul]

theorem of_lin_mul_of_lin (p : ℕ) (hp : 0 < p) (a b : ℂ) (hab : a ≠ b)
    (u v : (MvRatFunc (Fin 1) ℂ)ˣ)
    (hu : (u : MvRatFunc (Fin 1) ℂ) =
      algebraMap (MvPolynomial (Fin 1) ℂ) (MvRatFunc (Fin 1) ℂ) (X 0 - C a))
    (hv : (v : MvRatFunc (Fin 1) ℂ) =
      algebraMap (MvPolynomial (Fin 1) ℂ) (MvRatFunc (Fin 1) ℂ) (X 0 - C b)) :
    MilnorK.of p u * MilnorK.of p v = 0 := by
  have hα : (b - a) ≠ 0 := sub_ne_zero.mpr hab.symm
  have hk1 : algebraMap (MvPolynomial (Fin 1) ℂ) (MvRatFunc (Fin 1) ℂ) (C (b - a)⁻¹) ≠ 0 :=
    algMap_ne_zero (by simpa using hα)
  have hk2 : algebraMap (MvPolynomial (Fin 1) ℂ) (MvRatFunc (Fin 1) ℂ) (C (-(b - a)⁻¹)) ≠ 0 :=
    algMap_ne_zero (by simpa using hα)
  have hpoly : (X 0 - C a) * C (b - a)⁻¹ + (X 0 - C b) * C (-(b - a)⁻¹) =
      (1 : MvPolynomial (Fin 1) ℂ) := by
    have h1 : (C ((b - a)⁻¹ * (b - a)) : MvPolynomial (Fin 1) ℂ) = 1 := by
      rw [inv_mul_cancel₀ hα, C_1]
    rw [← h1]
    simp only [map_mul, map_sub, map_neg]
    ring
  have hst : ((u * Units.mk0 _ hk1 : (MvRatFunc (Fin 1) ℂ)ˣ) : MvRatFunc (Fin 1) ℂ) +
      ((v * Units.mk0 _ hk2 : (MvRatFunc (Fin 1) ℂ)ˣ) : MvRatFunc (Fin 1) ℂ) = 1 := by
    simp only [Units.val_mul, Units.val_mk0, hu, hv]
    rw [← map_mul, ← map_mul, ← map_add, hpoly, map_one]
  have h := of_mul_of_eq_zero p _ _ hst
  rw [of_mul, of_mul, of_const_eq_zero p hp _ (Units.mk0 _ hk1) rfl,
    of_const_eq_zero p hp _ (Units.mk0 _ hk2) rfl, add_zero, add_zero] at h
  exact h

theorem of_lin_mul_self (p : ℕ) (hp : 0 < p) (a : ℂ) (u : (MvRatFunc (Fin 1) ℂ)ˣ)
    (hu : (u : MvRatFunc (Fin 1) ℂ) =
      algebraMap (MvPolynomial (Fin 1) ℂ) (MvRatFunc (Fin 1) ℂ) (X 0 - C a)) :
    MilnorK.of p u * MilnorK.of p u = 0 := by
  have hw0 : algebraMap (MvPolynomial (Fin 1) ℂ) (MvRatFunc (Fin 1) ℂ) (X 0 - C (a + 1)) ≠ 0 := by
    refine algMap_ne_zero ?_
    intro h
    have := congrArg (MvPolynomial.eval (fun _ ↦ a)) h
    simp at this
  have hw : (u : MvRatFunc (Fin 1) ℂ) - 1 =
      algebraMap (MvPolynomial (Fin 1) ℂ) (MvRatFunc (Fin 1) ℂ) (X 0 - C (a + 1)) := by
    rw [hu, ← map_one (algebraMap (MvPolynomial (Fin 1) ℂ) (MvRatFunc (Fin 1) ℂ)), ← map_sub]
    congr 1
    simp only [map_add, C_1]
    ring
  have hst : ((u⁻¹ : (MvRatFunc (Fin 1) ℂ)ˣ) : MvRatFunc (Fin 1) ℂ) +
      ((Units.mk0 _ hw0 * u⁻¹ : (MvRatFunc (Fin 1) ℂ)ˣ) : MvRatFunc (Fin 1) ℂ) = 1 := by
    simp only [Units.val_mul, Units.val_mk0, ← hw, Units.val_inv_eq_inv_val]
    have hu0 : (u : MvRatFunc (Fin 1) ℂ) ≠ 0 := u.ne_zero
    field_simp
    ring
  have h := of_mul_of_eq_zero p _ _ hst
  rw [of_mul, of_inv] at h
  have h2 := of_lin_mul_of_lin p hp a (a + 1) (by simp) u (Units.mk0 _ hw0) hu rfl
  have h4 := kof_neg_mul _ _ h
  rw [mul_add, h2, zero_add] at h4
  exact kof_mul_neg _ _ h4

theorem of_mul_of_one_var (p : ℕ) (hp : 0 < p) (u v : (MvRatFunc (Fin 1) ℂ)ˣ) :
    MilnorK.of p u * MilnorK.of p v = 0 := by
  let K1 : Subgroup (MvRatFunc (Fin 1) ℂ)ˣ :=
    { carrier := {u | ∀ v : (MvRatFunc (Fin 1) ℂ)ˣ, MilnorK.of p u * MilnorK.of p v = 0}
      mul_mem' := by
        intro a b ha hb v
        rw [of_mul, add_mul, ha v, hb v, add_zero]
      one_mem' := by
        intro v
        rw [of_one, zero_mul]
      inv_mem' := by
        intro a ha v
        rw [of_inv]
        exact kneg_mul _ _ (ha v) }
  have hmem : u ∈ K1 := by
    refine units_gen K1 ?_ ?_ u
    · intro c u hu v
      rw [of_const_eq_zero p hp c u hu, zero_mul]
    · intro a u hu v
      let K2 : Subgroup (MvRatFunc (Fin 1) ℂ)ˣ :=
        { carrier := {v | MilnorK.of p u * MilnorK.of p v = 0}
          mul_mem' := by
            intro x y hx hy
            show MilnorK.of p u * MilnorK.of p (x * y) = 0
            rw [of_mul, mul_add, hx, hy, add_zero]
          one_mem' := by
            show MilnorK.of p u * MilnorK.of p 1 = 0
            rw [of_one, mul_zero]
          inv_mem' := by
            intro x hx
            show MilnorK.of p u * MilnorK.of p x⁻¹ = 0
            rw [of_inv]
            exact kmul_neg _ _ hx }
      have hv : v ∈ K2 := by
        refine units_gen K2 ?_ ?_ v
        · intro c v hv
          show MilnorK.of p u * MilnorK.of p v = 0
          rw [of_const_eq_zero p hp c v hv, mul_zero]
        · intro b v hv
          show MilnorK.of p u * MilnorK.of p v = 0
          by_cases hab : a = b
          · subst hab
            have : u = v := Units.ext (hu.trans hv.symm)
            subst this
            exact of_lin_mul_self p hp a u hu
          · exact of_lin_mul_of_lin p hp a b hab u v hu hv
      exact hv
  exact hmem v

theorem grade_two_one_var (p : ℕ) (hp : 0 < p) : MilnorK.grade (MvRatFunc (Fin 1) ℂ) p 2 = ⊥ := by
  rw [eq_bot_iff, MilnorK.grade, AddSubgroup.closure_le]
  rintro _ ⟨s, rfl⟩
  rw [SetLike.mem_coe, AddSubgroup.mem_bot, symbol_succ, symbol_succ]
  simp [of_mul_of_one_var p hp]

theorem m_one (n p : ℕ) (hn : 2 ≤ n) (hp : p.Prime) :
    0 ∈ symbolLengthBounds (MvRatFunc (Fin 1) ℂ) p n := by
  rw [zero_mem_symbolLengthBounds_iff]
  exact OMA.Uniform.Mod2.grade_eq_bot_of_le p 2 (grade_two_one_var p hp.pos) n hn

end OMA.Uniform.BaseCases


namespace OMA.R_SymbolLengthMilnorKTheory_symbol_length_problem_variants_uniform_R1

def H1 : Prop := ∀ m p : ℕ, 2 ≤ m → p.Prime → p ≠ 2 →
  0 ∈ MilnorK.symbolLengthBounds (MvRatFunc (Fin m) ℂ) p (m + 1)

def H2 : Prop := ∀ m n : ℕ, 3 ≤ n → n < m → ∃ k : ℕ,
  k ∈ MilnorK.symbolLengthBounds (MvRatFunc (Fin m) ℂ) 2 n

def H3 : Prop := ∀ m : ℕ, 2 ≤ m → ∃ k : ℕ, ∀ p : ℕ, p.Prime → p ≠ 2 →
  k ∈ MilnorK.symbolLengthBounds (MvRatFunc (Fin m) ℂ) p 2

def H4 : Prop := ∀ m n : ℕ, 3 ≤ n → n ≤ m → ∃ k : ℕ, ∀ p : ℕ, p.Prime → p ≠ 2 →
  k ∈ MilnorK.symbolLengthBounds (MvRatFunc (Fin m) ℂ) p n

theorem main : H1 → H2 → H3 → H4 → type_of% @SymbolLengthMilnorKTheory.symbol_length_problem.variants.uniform := by
  intro h1 h2 h3 h4 m n hn
  by_cases hn1 : n = 1
  · subst hn1
    exact ⟨1, fun p _ ↦ SymbolLengthMilnorKTheory.symbol_length_problem.variants.degree_one m p⟩
  have hn2 : 2 ≤ n := by omega
  rcases (by omega : m = 0 ∨ m = 1 ∨ 2 ≤ m) with rfl | rfl | hm2
  · exact ⟨0, fun p hp ↦ OMA.Uniform.BaseCases.m_zero n p hn hp⟩
  · exact ⟨0, fun p hp ↦ OMA.Uniform.BaseCases.m_one n p hn2 hp⟩
  · by_cases hlt : m < n
    · refine ⟨0, fun p hp ↦ ?_⟩
      by_cases hp2 : p = 2
      · subst hp2
        exact OMA.Uniform.Mod2.zero_mem_two_of_lt m n hlt
      · rw [MilnorK.zero_mem_symbolLengthBounds_iff]
        refine OMA.Uniform.Mod2.grade_eq_bot_of_le p (m + 1) ?_ n hlt
        exact (MilnorK.zero_mem_symbolLengthBounds_iff _ _).mp (h1 m p hm2 hp hp2)
    · have hnm : n ≤ m := by omega
      by_cases hn2eq : n = 2
      · subst hn2eq
        obtain ⟨k_odd, hk_odd⟩ := h3 m hm2
        refine ⟨max (2 ^ (m - 1) - 1) k_odd, fun p hp ↦ ?_⟩
        by_cases hp2 : p = 2
        · subst hp2
          exact MilnorK.mem_symbolLengthBounds_of_le _ _
            (OMA.Uniform.Mod2.matzri_two m (by omega)) (le_max_left _ _)
        · exact MilnorK.mem_symbolLengthBounds_of_le _ _ (hk_odd p hp hp2) (le_max_right _ _)
      · have hn3 : 3 ≤ n := by omega
        obtain ⟨k_odd, hk_odd⟩ := h4 m n hn3 hnm
        by_cases hnm_eq : n = m
        · subst hnm_eq
          refine ⟨max 1 k_odd, fun p hp ↦ ?_⟩
          by_cases hp2 : p = 2
          · subst hp2
            exact MilnorK.mem_symbolLengthBounds_of_le _ _
              (OMA.Uniform.Mod2.top_degree_two n (by omega)) (le_max_left _ _)
          · exact MilnorK.mem_symbolLengthBounds_of_le _ _ (hk_odd p hp hp2) (le_max_right _ _)
        · have hnlt : n < m := by omega
          obtain ⟨k_two, hk_two⟩ := h2 m n hn3 hnlt
          refine ⟨max k_two k_odd, fun p hp ↦ ?_⟩
          by_cases hp2 : p = 2
          · subst hp2
            exact MilnorK.mem_symbolLengthBounds_of_le _ _ hk_two (le_max_left _ _)
          · exact MilnorK.mem_symbolLengthBounds_of_le _ _ (hk_odd p hp hp2) (le_max_right _ _)

end OMA.R_SymbolLengthMilnorKTheory_symbol_length_problem_variants_uniform_R1
