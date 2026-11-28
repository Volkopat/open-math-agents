import OMAReductions.R_Green93_green_93_variants_bskk_small_R1

/-!
Reduction of `Green93.green_93.variants.bskk_small.R1.H1` (small-degree divisor bound
`1 <= deg g <= sqrt n` for random monic polynomials of degree `n` with coefficients in
`{0, ..., M}`, `1 <= M <= 33`, and nonzero constant term) to two decoupled, unconditionally true
Mahler-measure regimes for non-cyclotomic irreducible monic divisors of degree `2 <= deg q <= sqrt n`:

- `H1`: Breuillard-Varju (2019, *Acta Math.*, Proposition 38) small Mahler measure non-cyclotomic
  divisors (`M(q) <= 101 / 100`, where `log M(q) < 1 / 100 < tau / 10 = 1 / 20` for every uniform
  distribution on `{0, ..., M}` with `M >= 1`).
- `H2`: Bary-Soroker-Koukoulopoulos-Kozma (2023, *Invent. Math.* 233, Section 3) / Konyagin (1999)
  large Mahler measure small-degree non-cyclotomic divisors (`101 / 100 < M(q)` and
  `2 <= deg q <= sqrt n`).

In `main` and the private lemmas below, we prove completely from scratch in Lean 4:
1. Exact constant-term identity and exact denominator sample-space cardinality
   `|{a : Fin n -> Fin (M + 1) | (monicPoly a).coeff 0 != 0}| = M * (M + 1)^(n - 1)` for `n >= 1`,
   plus positivity at positive integers (`eval c >= 1` for `c >= 1`, ruling out `X - 1 = Phi_1`).
2. Irreducible monic factor extraction in `Z[X]` preserving `1 <= deg q <= deg g`.
3. Complete elimination of all linear non-cyclotomic divisors (`deg q = 1`, `q != X + 1`) via a
   modular quotient injection into `Fin n -> Fin (M / 2 + 1)`, proving an exponential bound
   `<= M * (2 / 3)^n * (M + 1)^n`.
4. Complete elimination of all cyclotomic divisors `Phi_m | monicPoly a` (`1 <= m`, `phi(m)^2 <= n`)
   via the elementary totient inequality `2 * m^2 <= 9 * phi(m)^3`, the uniform slice
   anti-concentration bound `p_max(L, M) <= 4 / sqrt L` (central binomial induction, parity-pair
   splitting for even `M + 1`, and integer second-moment Chebyshev bound plus conditioning for odd
   `M + 1`), monic polynomial remainder fiber decomposition modulo `Phi_m`, and an explicit
   asymptotic union bound over `2 <= m <= 31` and `32 <= m < 6 * u^6` (`u^8 <= n < (u + 1)^8`).
5. Assembly of the four-part union bound (`linear + cyclotomic + H1 + H2 <= epsilon`).
-/

namespace OMA.R_Green93_green_93_variants_bskk_small_R1_H1_R1

open Polynomial

/- Breuillard-Varju (2019, Acta Math., Prop. 38): vanishing probability of having a non-cyclotomic
irreducible monic divisor of degree 2 <= deg q <= sqrt n and small Mahler measure M(q) <= 101/100. -/
def H1 : Prop :=
  ∀ M : ℕ, 1 ≤ M → M ≤ 33 → ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    (({a : Fin n → Fin (M + 1) |
        (Green93.monicPoly fun j ↦ (a j : ℕ)).coeff 0 ≠ 0 ∧
        ∃ q : ℤ[X], q.Monic ∧ Irreducible q ∧ 2 ≤ q.natDegree ∧ q.natDegree ^ 2 ≤ n ∧
          (∀ m : ℕ, 1 ≤ m → q ≠ Polynomial.cyclotomic m ℤ) ∧
          (((q.map (Int.castRingHom ℂ)).roots.map fun z : ℂ => max (1 : ℝ) ‖z‖).prod ≤
            (101 : ℝ) / 100) ∧
          q ∣ Green93.monicPoly fun j ↦ (a j : ℕ)}.ncard : ℝ) ≤
      ε * ((M * (M + 1) ^ (n - 1) : ℕ) : ℝ))

/- BSKK23 (Invent. Math. 2023, Section 3) / Konyagin (1999): vanishing probability of having a
non-cyclotomic irreducible monic divisor of degree 2 <= deg q <= sqrt n and Mahler measure
M(q) > 101/100. -/
def H2 : Prop :=
  ∀ M : ℕ, 1 ≤ M → M ≤ 33 → ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    (({a : Fin n → Fin (M + 1) |
        (Green93.monicPoly fun j ↦ (a j : ℕ)).coeff 0 ≠ 0 ∧
        ∃ q : ℤ[X], q.Monic ∧ Irreducible q ∧ 2 ≤ q.natDegree ∧ q.natDegree ^ 2 ≤ n ∧
          (∀ m : ℕ, 1 ≤ m → q ≠ Polynomial.cyclotomic m ℤ) ∧
          ((101 : ℝ) / 100 <
            ((q.map (Int.castRingHom ℂ)).roots.map fun z : ℂ => max (1 : ℝ) ‖z‖).prod) ∧
          q ∣ Green93.monicPoly fun j ↦ (a j : ℕ)}.ncard : ℝ) ≤
      ε * ((M * (M + 1) ^ (n - 1) : ℕ) : ℝ))

section

/- ### Part 1: Basic properties of `Green93.monicPoly` and exact sample-space cardinality -/

private lemma monicPoly_coeff_zero {n : ℕ} (hn : 1 ≤ n) (a : Fin n → ℕ) :
    (Green93.monicPoly a).coeff 0 = (a ⟨0, by omega⟩ : ℤ) := by
  unfold Green93.monicPoly
  rw [coeff_add, coeff_X_pow, if_neg (by omega), zero_add, finsetSum_coeff]
  rw [Finset.sum_eq_single (⟨0, by omega⟩ : Fin n)]
  · simp
  · intro j _ hj
    rw [coeff_C_mul_X_pow, if_neg]
    intro h0
    exact hj (Fin.ext h0.symm)
  · intro h
    exact False.elim (h (Finset.mem_univ _))

private lemma card_nonzero_constTerm (M n : ℕ) (hn : 1 ≤ n) :
    {a : Fin n → Fin (M + 1) |
      (Green93.monicPoly fun j ↦ (a j : ℕ)).coeff 0 ≠ 0}.ncard = M * (M + 1) ^ (n - 1) := by
  let S : Set (Fin n → Fin (M + 1)) :=
    {a : Fin n → Fin (M + 1) | (Green93.monicPoly fun j ↦ (a j : ℕ)).coeff 0 ≠ 0}
  have heq_mem : ∀ a : Fin n → Fin (M + 1), a ∈ S ↔ (a ⟨0, by omega⟩).1 ≠ 0 := by
    intro a
    dsimp only [S]
    rw [Set.mem_ofPred_eq, monicPoly_coeff_zero hn]
    exact Int.natCast_ne_zero
  let e : S ≃ Fin M × (Fin (n - 1) → Fin (M + 1)) :=
    { toFun := fun ⟨a, ha⟩ =>
        have hpos : 1 ≤ (a ⟨0, by omega⟩).1 := by
          have hne := (heq_mem a).mp ha
          omega
        (⟨(a ⟨0, by omega⟩).1 - 1, by have := (a ⟨0, by omega⟩).2; omega⟩,
         fun i => a ⟨i.1 + 1, by have := i.2; omega⟩)
      invFun := fun ⟨x, b⟩ =>
        ⟨fun j => if h0 : j.1 = 0 then ⟨x.1 + 1, by have := x.2; omega⟩
                  else b ⟨j.1 - 1, by have := j.2; omega⟩,
         (heq_mem _).mpr (by simp)⟩
      left_inv := by
        rintro ⟨a, ha⟩
        apply Subtype.ext
        ext j
        dsimp only
        by_cases h0 : j.1 = 0
        · rw [dif_pos h0]
          dsimp only
          have hj : j = ⟨0, by omega⟩ := Fin.ext h0
          have hne := (heq_mem a).mp ha
          rw [hj]
          omega
        · rw [dif_neg h0]
          have hidx : (⟨j.1 - 1 + 1, by have := j.2; omega⟩ : Fin n) = j := Fin.ext (by dsimp only; omega)
          rw [hidx]
      right_inv := by
        rintro ⟨x, b⟩
        ext
        · simp
        · simp }
  rw [Set.ncard_eq_toFinset_card']
  have hcard : S.toFinset.card = Fintype.card S := by
    rw [← Fintype.card_coe]
    refine Fintype.card_congr ?_
    exact
      { toFun := fun ⟨a, ha⟩ => ⟨a, Set.mem_toFinset.mp ha⟩
        invFun := fun ⟨a, ha⟩ => ⟨a, Set.mem_toFinset.mpr ha⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [hcard, Fintype.card_congr e, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_fin, Fintype.card_fin]

private lemma monicPoly_eval_pos {n : ℕ} (a : Fin n → ℕ) {c : ℤ} (hc : 1 ≤ c) :
    1 ≤ (Green93.monicPoly a).eval c := by
  unfold Green93.monicPoly
  simp only [eval_add, eval_pow, eval_X, eval_finsetSum, eval_mul, eval_C]
  have hpow : (1 : ℤ) ≤ c ^ n := one_le_pow₀ hc
  have hsum : (0 : ℤ) ≤ ∑ j : Fin n, (a j : ℤ) * c ^ j.1 := by
    refine Finset.sum_nonneg fun j _ => ?_
    have hc0 : (0 : ℤ) ≤ c := by omega
    exact mul_nonneg (Int.natCast_nonneg _) (pow_nonneg hc0 _)
  linarith

private lemma X_sub_C_not_dvd_monicPoly {n : ℕ} (a : Fin n → ℕ) {c : ℤ} (hc : 1 ≤ c) :
    ¬ (X - C c ∣ Green93.monicPoly a) := by
  intro hdvd
  have hev : (Green93.monicPoly a).eval c = 0 := by
    obtain ⟨h, hh⟩ := hdvd
    rw [hh, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul]
  have hpos := monicPoly_eval_pos a hc
  omega

private lemma cyclotomic_one_not_dvd_monicPoly {n : ℕ} (a : Fin n → ℕ) :
    ¬ (Polynomial.cyclotomic 1 ℤ ∣ Green93.monicPoly a) := by
  rw [Polynomial.cyclotomic_one, ← map_one C]
  exact X_sub_C_not_dvd_monicPoly a le_rfl

private lemma ncard_biUnion_finset_le {α β : Type*} [Finite α] (s : Finset β) (f : β → Set α) :
    (⋃ b ∈ s, f b).ncard ≤ ∑ b ∈ s, (f b).ncard := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp
  | insert b t hbt ih =>
    rw [Finset.sum_insert hbt]
    have hunion : (⋃ x ∈ insert b t, f x) = f b ∪ ⋃ x ∈ t, f x := by
      ext y
      simp
    rw [hunion]
    exact (Set.ncard_union_le _ _).trans (Nat.add_le_add_left ih _)

private lemma pow_le_two_mul_denom {M n : ℕ} (hM : 1 ≤ M) (hn : 1 ≤ n) :
    ((M + 1) ^ n : ℝ) ≤ 2 * ((M * (M + 1) ^ (n - 1) : ℕ) : ℝ) := by
  have hnat : (M + 1) ^ n ≤ 2 * (M * (M + 1) ^ (n - 1)) := by
    have hsplit : (M + 1) ^ n = (M + 1) * (M + 1) ^ (n - 1) := by
      cases n with
      | zero => omega
      | succ k => simp [pow_succ, mul_comm]
    rw [hsplit]
    have hM2 : M + 1 ≤ 2 * M := by omega
    calc (M + 1) * (M + 1) ^ (n - 1)
        ≤ (2 * M) * (M + 1) ^ (n - 1) := Nat.mul_le_mul_right _ hM2
      _ = 2 * (M * (M + 1) ^ (n - 1)) := by ring
  exact_mod_cast hnat

/- ### Part 2: Irreducible monic factor extraction in `ℤ[X]` -/

private lemma exists_irreducible_monic_dvd_aux :
    ∀ d : ℕ, ∀ g : ℤ[X], g.Monic → 1 ≤ g.natDegree → g.natDegree ≤ d →
      ∃ q : ℤ[X], q.Monic ∧ Irreducible q ∧ 1 ≤ q.natDegree ∧ q.natDegree ≤ g.natDegree ∧ q ∣ g := by
  intro d
  induction d with
  | zero =>
    intro g _ h1 h0
    omega
  | succ d ih =>
    intro g hg h1 hd
    by_cases hirr : Irreducible g
    · exact ⟨g, hg, hirr, h1, le_rfl, dvd_rfl⟩
    · have hnu : ¬ IsUnit g := by
        rw [hg.isUnit_iff]
        intro h1g
        rw [h1g, natDegree_one] at h1
        omega
      have hfac : ∃ u v : ℤ[X], g = u * v ∧ ¬ IsUnit u ∧ ¬ IsUnit v := by
        rw [irreducible_iff] at hirr
        push Not at hirr
        exact hirr hnu
      obtain ⟨u, v, huv, hnu_u, hnu_v⟩ := hfac
      have hg0 : g ≠ 0 := hg.ne_zero
      have hu0 : u ≠ 0 := by intro h; rw [h, zero_mul] at huv; exact hg0 huv
      have hv0 : v ≠ 0 := by intro h; rw [h, mul_zero] at huv; exact hg0 huv
      have hlc : u.leadingCoeff * v.leadingCoeff = 1 := by
        rw [← leadingCoeff_mul, ← huv, hg.leadingCoeff]
      have hu_unit : IsUnit u.leadingCoeff := isUnit_iff_exists_inv.mpr ⟨v.leadingCoeff, hlc⟩
      have hv_unit : IsUnit v.leadingCoeff :=
        isUnit_iff_exists_inv.mpr ⟨u.leadingCoeff, mul_comm u.leadingCoeff v.leadingCoeff ▸ hlc⟩
      have hu_sq : u.leadingCoeff * u.leadingCoeff = 1 := by
        rcases Int.isUnit_iff.mp hu_unit with h | h <;> simp [h]
      have hv_sq : v.leadingCoeff * v.leadingCoeff = 1 := by
        rcases Int.isUnit_iff.mp hv_unit with h | h <;> simp [h]
      let u' : ℤ[X] := C u.leadingCoeff * u
      let v' : ℤ[X] := C v.leadingCoeff * v
      have hu'_monic : u'.Monic := by
        dsimp only [u']
        rw [Monic.def, leadingCoeff_mul, leadingCoeff_C, hu_sq]
      have hv'_monic : v'.Monic := by
        dsimp only [v']
        rw [Monic.def, leadingCoeff_mul, leadingCoeff_C, hv_sq]
      have hmul' : g = u' * v' := by
        dsimp only [u', v']
        calc g = u * v := huv
          _ = C 1 * (u * v) := by simp
          _ = C (u.leadingCoeff * v.leadingCoeff) * (u * v) := by rw [hlc]
          _ = (C u.leadingCoeff * u) * (C v.leadingCoeff * v) := by rw [map_mul]; ring
      have hu'_deg1 : 1 ≤ u'.natDegree := by
        by_contra h0
        have hdeg0 : u'.natDegree = 0 := by omega
        have hu'1 : u' = 1 := by
          rw [eq_C_of_natDegree_eq_zero hdeg0]
          have hcoeff : u'.coeff 0 = 1 := by
            have := hu'_monic.leadingCoeff
            rw [leadingCoeff, hdeg0] at this
            exact this
          rw [hcoeff, map_one]
        exact hnu_u (isUnit_iff_exists_inv.mpr ⟨C u.leadingCoeff, by rw [mul_comm]; exact hu'1⟩)
      have hv'_deg1 : 1 ≤ v'.natDegree := by
        by_contra h0
        have hdeg0 : v'.natDegree = 0 := by omega
        have hv'1 : v' = 1 := by
          rw [eq_C_of_natDegree_eq_zero hdeg0]
          have hcoeff : v'.coeff 0 = 1 := by
            have := hv'_monic.leadingCoeff
            rw [leadingCoeff, hdeg0] at this
            exact this
          rw [hcoeff, map_one]
        exact hnu_v (isUnit_iff_exists_inv.mpr ⟨C v.leadingCoeff, by rw [mul_comm]; exact hv'1⟩)
      have hdeg_add : g.natDegree = u'.natDegree + v'.natDegree := by
        rw [hmul', natDegree_mul hu'_monic.ne_zero hv'_monic.ne_zero]
      have hu'_led : u'.natDegree ≤ d := by omega
      obtain ⟨q, hq_m, hq_i, hq_1, hq_le, hq_dvd⟩ := ih u' hu'_monic hu'_deg1 hu'_led
      exact ⟨q, hq_m, hq_i, hq_1, by omega, dvd_trans hq_dvd ⟨v', hmul'⟩⟩

private lemma exists_irreducible_monic_dvd (g : ℤ[X]) (hg : g.Monic) (h1 : 1 ≤ g.natDegree) :
    ∃ q : ℤ[X], q.Monic ∧ Irreducible q ∧ 1 ≤ q.natDegree ∧ q.natDegree ≤ g.natDegree ∧ q ∣ g :=
  exists_irreducible_monic_dvd_aux g.natDegree g hg h1 le_rfl

/- ### Part 3: Complete elimination of all linear non-cyclotomic divisors -/

private lemma monic_natDegree_one_eq_X_add_C (q : ℤ[X]) (hq : q.Monic) (hdeg : q.natDegree = 1) :
    q = X + C (q.coeff 0) := by
  have hdle : q.degree ≤ 1 := by
    calc q.degree ≤ (q.natDegree : WithBot ℕ) := degree_le_natDegree
      _ = 1 := by rw [hdeg]; rfl
  have heq := eq_X_add_C_of_degree_le_one hdle
  have hcoeff1 : q.coeff 1 = 1 := by
    have := hq.leadingCoeff
    rw [leadingCoeff, hdeg] at this
    exact this
  rw [hcoeff1, map_one, one_mul] at heq
  exact heq

private lemma linear_neg_eval_card_le (M n k : ℕ) (hk : 2 ≤ k) :
    {a : Fin n → Fin (M + 1) |
      (Green93.monicPoly fun j ↦ (a j : ℕ)).eval (-(k : ℤ)) = 0}.ncard ≤ (M / 2 + 1) ^ n := by
  let S : Set (Fin n → Fin (M + 1)) :=
    {a : Fin n → Fin (M + 1) | (Green93.monicPoly fun j ↦ (a j : ℕ)).eval (-(k : ℤ)) = 0}
  let φ : S → (Fin n → Fin (M / 2 + 1)) := fun ⟨a, _⟩ j =>
    ⟨(a j).1 / k, by
      have h1 : (a j).1 ≤ M := by have := (a j).2; omega
      have h2 : (a j).1 / k ≤ M / k := Nat.div_le_div_right h1
      have h3 : M / k ≤ M / 2 := Nat.div_le_div_left hk (by omega)
      omega⟩
  have hinj : Function.Injective φ := by
    rintro ⟨a, ha⟩ ⟨a', ha'⟩ hφ
    apply Subtype.ext
    have hcoord : ∀ m : ℕ, ∀ (hm : m < n), a ⟨m, hm⟩ = a' ⟨m, hm⟩ := by
      intro m
      induction m using Nat.strong_induction_on with
      | _ m ih =>
        intro hm
        have hsum_zero : ∑ j : Fin n, (((a j).1 : ℤ) - ((a' j).1 : ℤ)) * (-(k : ℤ)) ^ j.1 = 0 := by
          have ha0 : (-(k : ℤ)) ^ n + ∑ j : Fin n, ((a j).1 : ℤ) * (-(k : ℤ)) ^ j.1 = 0 := by
            have ha_ev : (Green93.monicPoly fun j ↦ (a j : ℕ)).eval (-(k : ℤ)) = 0 := ha
            unfold Green93.monicPoly at ha_ev
            simpa [eval_add, eval_pow, eval_X, eval_finsetSum, eval_mul, eval_C] using ha_ev
          have ha'0 : (-(k : ℤ)) ^ n + ∑ j : Fin n, ((a' j).1 : ℤ) * (-(k : ℤ)) ^ j.1 = 0 := by
            have ha'_ev : (Green93.monicPoly fun j ↦ (a' j : ℕ)).eval (-(k : ℤ)) = 0 := ha'
            unfold Green93.monicPoly at ha'_ev
            simpa [eval_add, eval_pow, eval_X, eval_finsetSum, eval_mul, eval_C] using ha'_ev
          have hsub : (∑ j : Fin n, ((a j).1 : ℤ) * (-(k : ℤ)) ^ j.1) -
              (∑ j : Fin n, ((a' j).1 : ℤ) * (-(k : ℤ)) ^ j.1) = 0 := by linarith
          rw [← Finset.sum_sub_distrib] at hsub
          convert hsub using 2 with j
          ring
        let jm : Fin n := ⟨m, hm⟩
        have hsplit : ∑ j : Fin n, (((a j).1 : ℤ) - ((a' j).1 : ℤ)) * (-(k : ℤ)) ^ j.1 =
            ((((a jm).1 : ℤ) - ((a' jm).1 : ℤ)) +
              (-(k : ℤ)) * ∑ j ∈ Finset.univ.filter (fun j : Fin n => m < j.1),
                (((a j).1 : ℤ) - ((a' j).1 : ℤ)) * (-(k : ℤ)) ^ (j.1 - (m + 1))) *
              (-(k : ℤ)) ^ m := by
          have hge : ∑ j : Fin n, (((a j).1 : ℤ) - ((a' j).1 : ℤ)) * (-(k : ℤ)) ^ j.1 =
              ∑ j ∈ Finset.univ.filter (fun j : Fin n => m ≤ j.1),
                (((a j).1 : ℤ) - ((a' j).1 : ℤ)) * (-(k : ℤ)) ^ j.1 := by
            symm
            refine Finset.sum_subset (Finset.filter_subset _ _) fun j _ hj => ?_
            have hlt : j.1 < m := by
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
              omega
            have heq := ih j.1 hlt j.2
            have hj_eq : (⟨j.1, j.2⟩ : Fin n) = j := Fin.eta j j.2
            rw [hj_eq] at heq
            rw [heq, sub_self, zero_mul]
          rw [hge]
          have hpart : Finset.univ.filter (fun j : Fin n => m ≤ j.1) =
              insert jm (Finset.univ.filter (fun j : Fin n => m < j.1)) := by
            ext j
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff, jm]
            omega
          have hnot : jm ∉ Finset.univ.filter (fun j : Fin n => m < j.1) := by
            simp [jm]
          rw [hpart, Finset.sum_insert hnot, add_mul, Finset.mul_sum, Finset.sum_mul]
          congr 1
          refine Finset.sum_congr rfl fun j hj => ?_
          have hgt : m < j.1 := (Finset.mem_filter.mp hj).2
          have hexp : j.1 = (j.1 - (m + 1)) + 1 + m := by omega
          conv_lhs => rw [hexp]
          rw [pow_add, pow_add, pow_one]
          ring
        rw [hsplit] at hsum_zero
        have hpow_ne : (-(k : ℤ)) ^ m ≠ 0 := pow_ne_zero m (by omega)
        have hfac0 : (((a jm).1 : ℤ) - ((a' jm).1 : ℤ)) +
            (-(k : ℤ)) * ∑ j ∈ Finset.univ.filter (fun j : Fin n => m < j.1),
              (((a j).1 : ℤ) - ((a' j).1 : ℤ)) * (-(k : ℤ)) ^ (j.1 - (m + 1)) = 0 :=
          (mul_eq_zero.mp hsum_zero).resolve_right hpow_ne
        have hdvd : (k : ℤ) ∣ ((a jm).1 : ℤ) - ((a' jm).1 : ℤ) := by
          refine ⟨∑ j ∈ Finset.univ.filter (fun j : Fin n => m < j.1),
            (((a j).1 : ℤ) - ((a' j).1 : ℤ)) * (-(k : ℤ)) ^ (j.1 - (m + 1)), ?_⟩
          linarith
        have hq_eq : (a jm).1 / k = (a' jm).1 / k := by
          have := congrArg (fun f => (f jm).1) hφ
          exact this
        have hrem_eq : (a jm).1 % k = (a' jm).1 % k := by
          have hda := Nat.div_add_mod (a jm).1 k
          have hda' := Nat.div_add_mod (a' jm).1 k
          have hma : (a jm).1 % k < k := Nat.mod_lt _ (by omega)
          have hma' : (a' jm).1 % k < k := Nat.mod_lt _ (by omega)
          obtain ⟨t, ht⟩ := hdvd
          have hdiff : (((a jm).1 % k : ℕ) : ℤ) - (((a' jm).1 % k : ℕ) : ℤ) = (k : ℤ) * t := by
            have h1 : ((a jm).1 : ℤ) = (k : ℤ) * (((a jm).1 / k : ℕ) : ℤ) + (((a jm).1 % k : ℕ) : ℤ) := by
              exact_mod_cast hda.symm
            have h2 : ((a' jm).1 : ℤ) = (k : ℤ) * (((a' jm).1 / k : ℕ) : ℤ) + (((a' jm).1 % k : ℕ) : ℤ) := by
              exact_mod_cast hda'.symm
            rw [hq_eq] at h1
            linarith
          have hmaZ : (((a jm).1 % k : ℕ) : ℤ) < (k : ℤ) := by exact_mod_cast hma
          have hma'Z : (((a' jm).1 % k : ℕ) : ℤ) < (k : ℤ) := by exact_mod_cast hma'
          have ht0 : t = 0 := by
            by_contra hne
            rcases lt_or_gt_of_ne hne with hlt | hgt <;> nlinarith
          rw [ht0, mul_zero] at hdiff
          omega
        apply Fin.ext
        change (a jm).1 = (a' jm).1
        have hda := Nat.div_add_mod (a jm).1 k
        have hda' := Nat.div_add_mod (a' jm).1 k
        rw [hq_eq, hrem_eq] at hda
        omega
    ext j
    have := hcoord j.1 j.2
    exact congrArg Fin.val this
  rw [Set.ncard_eq_toFinset_card']
  have hcard : S.toFinset.card = Fintype.card S := by
    rw [← Fintype.card_coe]
    refine Fintype.card_congr ?_
    exact
      { toFun := fun ⟨a, ha⟩ => ⟨a, Set.mem_toFinset.mp ha⟩
        invFun := fun ⟨a, ha⟩ => ⟨a, Set.mem_toFinset.mpr ha⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [hcard]
  calc Fintype.card S ≤ Fintype.card (Fin n → Fin (M / 2 + 1)) := Fintype.card_le_of_injective φ hinj
    _ = (M / 2 + 1) ^ n := by rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

private lemma linear_noncyc_divisors_small (M : ℕ) (hM : 1 ≤ M) (ε : ℝ) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      (({a : Fin n → Fin (M + 1) |
          (Green93.monicPoly fun j ↦ (a j : ℕ)).coeff 0 ≠ 0 ∧
          ∃ q : ℤ[X], q.Monic ∧ q.natDegree = 1 ∧ q ≠ Polynomial.cyclotomic 2 ℤ ∧
            q ∣ Green93.monicPoly fun j ↦ (a j : ℕ)}.ncard : ℝ) ≤
        ε * ((M * (M + 1) ^ (n - 1) : ℕ) : ℝ)) := by
  have htend : Filter.Tendsto (fun n : ℕ => (2 * (M : ℝ)) * ((2 : ℝ) / 3) ^ n) Filter.atTop (nhds 0) := by
    have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2 / 3) (by norm_num : (2 : ℝ) / 3 < 1)
    simpa using hpow.const_mul (2 * (M : ℝ))
  obtain ⟨n₁, hn₁⟩ := Metric.tendsto_atTop.mp htend ε hε
  refine ⟨max 1 n₁, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_left _ _) hn
  have hnn₁ : n₁ ≤ n := le_trans (le_max_right _ _) hn
  have hsub : {a : Fin n → Fin (M + 1) |
      (Green93.monicPoly fun j ↦ (a j : ℕ)).coeff 0 ≠ 0 ∧
      ∃ q : ℤ[X], q.Monic ∧ q.natDegree = 1 ∧ q ≠ Polynomial.cyclotomic 2 ℤ ∧
        q ∣ Green93.monicPoly fun j ↦ (a j : ℕ)} ⊆
      ⋃ k ∈ Finset.Icc 2 M,
        {a : Fin n → Fin (M + 1) |
          (Green93.monicPoly fun j ↦ (a j : ℕ)).eval (-(k : ℤ)) = 0} := by
    intro a ⟨ha0, q, hq_m, hq_deg, hq_ne2, hq_dvd⟩
    have hq_eq : q = X + C (q.coeff 0) := monic_natDegree_one_eq_X_add_C q hq_m hq_deg
    have hc_ne0 : q.coeff 0 ≠ 0 := by
      intro h0
      obtain ⟨h, hh⟩ := hq_dvd
      have hc0 : (Green93.monicPoly fun j ↦ (a j : ℕ)).coeff 0 = q.coeff 0 * h.coeff 0 := by
        rw [hh, mul_coeff_zero]
      rw [h0, zero_mul] at hc0
      exact ha0 hc0
    have hc_pos : 0 < q.coeff 0 := by
      by_contra hle
      have hneg : 1 ≤ -(q.coeff 0) := by omega
      have hq_sub : q = X - C (-(q.coeff 0)) := by
        rw [map_neg, sub_neg_eq_add]
        exact hq_eq
      rw [hq_sub] at hq_dvd
      exact X_sub_C_not_dvd_monicPoly _ hneg hq_dvd
    have hc_ne1 : q.coeff 0 ≠ 1 := by
      intro h1
      rw [h1, map_one] at hq_eq
      exact hq_ne2 (by rw [hq_eq, Polynomial.cyclotomic_two])
    have hc_ge2 : 2 ≤ q.coeff 0 := by omega
    let k : ℕ := (q.coeff 0).toNat
    have hk_eq : (k : ℤ) = q.coeff 0 := Int.toNat_of_nonneg (by omega)
    have hk_ge2 : 2 ≤ k := by omega
    have hk_leM : k ≤ M := by
      obtain ⟨h, hh⟩ := hq_dvd
      have hc0 : (Green93.monicPoly fun j ↦ (a j : ℕ)).coeff 0 = (k : ℤ) * h.coeff 0 := by
        rw [hh, mul_coeff_zero, hk_eq]
      rw [monicPoly_coeff_zero hn1] at hc0
      have hdvd_nat : k ∣ (a ⟨0, by omega⟩).1 := by
        have hpos_a0 : 0 < ((a ⟨0, by omega⟩).1 : ℤ) := by
          have hne := ha0
          rw [monicPoly_coeff_zero hn1] at hne
          omega
        have hh_pos : 0 < h.coeff 0 := by nlinarith
        refine ⟨(h.coeff 0).toNat, ?_⟩
        have h1 : ((h.coeff 0).toNat : ℤ) = h.coeff 0 := Int.toNat_of_nonneg (by omega)
        rw [← h1] at hc0
        exact_mod_cast hc0
      have hpos_a : 0 < (a ⟨0, by omega⟩).1 := by
        have hne := ha0
        rw [monicPoly_coeff_zero hn1] at hne
        omega
      have hle_a := Nat.le_of_dvd hpos_a hdvd_nat
      have hlt_M := (a ⟨0, by omega⟩).2
      omega
    refine Set.mem_iUnion₂.mpr ⟨k, Finset.mem_Icc.mpr ⟨hk_ge2, hk_leM⟩, ?_⟩
    obtain ⟨h, hh⟩ := hq_dvd
    rw [Set.mem_ofPred_eq, hh, eval_mul, hq_eq, ← hk_eq, eval_add, eval_X, eval_C, neg_add_cancel, zero_mul]
  have hncard_nat : {a : Fin n → Fin (M + 1) |
      (Green93.monicPoly fun j ↦ (a j : ℕ)).coeff 0 ≠ 0 ∧
      ∃ q : ℤ[X], q.Monic ∧ q.natDegree = 1 ∧ q ≠ Polynomial.cyclotomic 2 ℤ ∧
        q ∣ Green93.monicPoly fun j ↦ (a j : ℕ)}.ncard ≤ M * (M / 2 + 1) ^ n := by
    calc _ ≤ (⋃ k ∈ Finset.Icc 2 M,
          {a : Fin n → Fin (M + 1) |
            (Green93.monicPoly fun j ↦ (a j : ℕ)).eval (-(k : ℤ)) = 0}).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ ∑ k ∈ Finset.Icc 2 M,
          {a : Fin n → Fin (M + 1) |
            (Green93.monicPoly fun j ↦ (a j : ℕ)).eval (-(k : ℤ)) = 0}.ncard :=
          ncard_biUnion_finset_le _ _
      _ ≤ ∑ _k ∈ Finset.Icc 2 M, (M / 2 + 1) ^ n :=
          Finset.sum_le_sum fun k hk => linear_neg_eval_card_le M n k (Finset.mem_Icc.mp hk).1
      _ = (Finset.Icc 2 M).card * (M / 2 + 1) ^ n := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ M * (M / 2 + 1) ^ n := by
          refine Nat.mul_le_mul_right _ ?_
          rw [Nat.card_Icc]
          omega
  have hratio : ((M / 2 + 1 : ℕ) : ℝ) ≤ (2 / 3 : ℝ) * ((M + 1 : ℕ) : ℝ) := by
    have hnat : 3 * (M / 2 + 1) ≤ 2 * (M + 1) := by omega
    have hreal : (3 : ℝ) * ((M / 2 + 1 : ℕ) : ℝ) ≤ 2 * ((M + 1 : ℕ) : ℝ) := by exact_mod_cast hnat
    linarith
  have hpow_le : (((M / 2 + 1 : ℕ) : ℝ)) ^ n ≤ ((2 : ℝ) / 3) ^ n * ((M + 1 : ℕ) : ℝ) ^ n := by
    calc (((M / 2 + 1 : ℕ) : ℝ)) ^ n
        ≤ ((2 / 3 : ℝ) * ((M + 1 : ℕ) : ℝ)) ^ n := pow_le_pow_left₀ (by positivity) hratio n
      _ = ((2 : ℝ) / 3) ^ n * ((M + 1 : ℕ) : ℝ) ^ n := mul_pow _ _ n
  have hsmall : (2 * (M : ℝ)) * ((2 : ℝ) / 3) ^ n ≤ ε := by
    have hdist := hn₁ n hnn₁
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hdist
    exact le_of_lt hdist
  have hden := pow_le_two_mul_denom hM hn1
  calc (({a : Fin n → Fin (M + 1) |
          (Green93.monicPoly fun j ↦ (a j : ℕ)).coeff 0 ≠ 0 ∧
          ∃ q : ℤ[X], q.Monic ∧ q.natDegree = 1 ∧ q ≠ Polynomial.cyclotomic 2 ℤ ∧
            q ∣ Green93.monicPoly fun j ↦ (a j : ℕ)}.ncard : ℝ))
      ≤ ((M * (M / 2 + 1) ^ n : ℕ) : ℝ) := by exact_mod_cast hncard_nat
    _ = (M : ℝ) * (((M / 2 + 1 : ℕ) : ℝ)) ^ n := by push_cast; rfl
    _ ≤ (M : ℝ) * (((2 : ℝ) / 3) ^ n * ((M + 1 : ℕ) : ℝ) ^ n) :=
        mul_le_mul_of_nonneg_left hpow_le (by positivity)
    _ ≤ (M : ℝ) * (((2 : ℝ) / 3) ^ n * (2 * ((M * (M + 1) ^ (n - 1) : ℕ) : ℝ))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity)) (by positivity)
        simpa [Nat.cast_add, Nat.cast_one] using hden
    _ = ((2 * (M : ℝ)) * ((2 : ℝ) / 3) ^ n) * ((M * (M + 1) ^ (n - 1) : ℕ) : ℝ) := by ring
    _ ≤ ε * ((M * (M + 1) ^ (n - 1) : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right hsmall (by positivity)

/- ### Part 4: Complete elimination of all cyclotomic divisors up to degree `sqrt n` -/

private lemma strip_prime (p : ℕ) (hp : p.Prime) :
    ∀ r : ℕ, 1 ≤ r → ∃ k r' : ℕ, 1 ≤ r' ∧ ¬ p ∣ r' ∧ r = p ^ k * r' := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro hr
    by_cases hdvd : p ∣ r
    · have hlt : r / p < r := Nat.div_lt_self (by omega) hp.one_lt
      have hpos : 1 ≤ r / p := Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) hp.pos
      obtain ⟨k, r', hr', hndvd, heq⟩ := ih (r / p) hlt hpos
      refine ⟨k + 1, r', hr', hndvd, ?_⟩
      have hmul : r = p * (r / p) := (Nat.mul_div_cancel' hdvd).symm
      rw [hmul, heq, pow_succ]
      ring
    · exact ⟨0, r, hr, hdvd, by simp⟩

private lemma prime_pow_sq_le_totient_cube {p k : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 1 ≤ k) :
    (p ^ k) ^ 2 ≤ (Nat.totient (p ^ k)) ^ 3 := by
  rw [Nat.totient_prime_pow hp (by omega)]
  have h1 : p ^ 2 ≤ (p - 1) ^ 3 := by
    have hZ : ((p : ℤ)) ^ 2 ≤ ((p : ℤ) - 1) ^ 3 := by nlinarith
    have hcast : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by omega
    rw [← hcast] at hZ
    exact_mod_cast hZ
  have h2 : p ^ (2 * k - 2) ≤ p ^ (3 * (k - 1)) :=
    Nat.pow_le_pow_right hp.pos (by omega)
  have hlhs : (p ^ k) ^ 2 = p ^ (2 * k - 2) * p ^ 2 := by
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  have hrhs : (p ^ (k - 1) * (p - 1)) ^ 3 = p ^ (3 * (k - 1)) * (p - 1) ^ 3 := by
    rw [mul_pow, ← pow_mul, mul_comm (k - 1) 3]
  rw [hlhs, hrhs]
  exact Nat.mul_le_mul h2 h1

private lemma coprime_two_three_sq_le_totient_cube :
    ∀ r : ℕ, 1 ≤ r → ¬ 2 ∣ r → ¬ 3 ∣ r → r ^ 2 ≤ (Nat.totient r) ^ 3 := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro hr h2 h3
    by_cases hr1 : r = 1
    · subst hr1; simp
    · let p := r.minFac
      have hp : p.Prime := Nat.minFac_prime hr1
      have hpdvd : p ∣ r := Nat.minFac_dvd r
      have hp5 : 5 ≤ p := by
        have h2p : p ≠ 2 := by intro h; rw [h] at hpdvd; exact h2 hpdvd
        have h3p : p ≠ 3 := by intro h; rw [h] at hpdvd; exact h3 hpdvd
        have h4p : p ≠ 4 := by intro h; rw [h] at hp; exact (by norm_num : ¬ Nat.Prime 4) hp
        have hge2 := hp.two_le
        omega
      obtain ⟨k, r', hr', hndvd, heq⟩ := strip_prime p hp r hr
      have hk : 1 ≤ k := by
        by_contra hk0
        have hk' : k = 0 := by omega
        rw [hk', pow_zero, one_mul] at heq
        rw [heq] at hpdvd
        exact hndvd hpdvd
      have hcop : Nat.Coprime (p ^ k) r' := (hp.coprime_iff_not_dvd.mpr hndvd).pow_left k
      have hr'lt : r' < r := by
        have hpk : 1 < p ^ k := one_lt_pow₀ hp.one_lt (by omega)
        calc r' = 1 * r' := (one_mul _).symm
          _ < p ^ k * r' := Nat.mul_lt_mul_of_pos_right hpk (by omega)
          _ = r := heq.symm
      have hr'2 : ¬ 2 ∣ r' := fun hd => h2 (dvd_trans hd ⟨p ^ k, by rw [heq, mul_comm]⟩)
      have hr'3 : ¬ 3 ∣ r' := fun hd => h3 (dvd_trans hd ⟨p ^ k, by rw [heq, mul_comm]⟩)
      have hih := ih r' hr'lt hr' hr'2 hr'3
      have hpk := prime_pow_sq_le_totient_cube hp hp5 hk
      rw [heq, mul_pow, Nat.totient_mul hcop, mul_pow]
      exact Nat.mul_le_mul hpk hih

private lemma two_mul_sq_le_nine_mul_totient_cube (m : ℕ) (hm : 1 ≤ m) :
    2 * m ^ 2 ≤ 9 * (Nat.totient m) ^ 3 := by
  obtain ⟨a, m₁, hm₁, hndvd2, hm_eq⟩ := strip_prime 2 Nat.prime_two m hm
  obtain ⟨b, r, hr, hndvd3, hm₁_eq⟩ := strip_prime 3 Nat.prime_three m₁ hm₁
  have hr2 : ¬ 2 ∣ r := fun hd => hndvd2 (dvd_trans hd ⟨3 ^ b, by rw [hm₁_eq, mul_comm]⟩)
  have h2a : (2 ^ a) ^ 2 ≤ 4 * (Nat.totient (2 ^ a)) ^ 3 := by
    cases a with
    | zero => norm_num
    | succ a' =>
      rw [Nat.totient_prime_pow Nat.prime_two (Nat.succ_pos a'), Nat.succ_sub_one]
      simp only [show 2 - 1 = 1 from rfl, mul_one]
      have hlhs : (2 ^ (a' + 1)) ^ 2 = 4 * 2 ^ (2 * a') := by
        rw [← pow_mul, show (a' + 1) * 2 = 2 * a' + 2 by omega, pow_add]
        ring
      have hrhs : 4 * (2 ^ a') ^ 3 = 4 * 2 ^ (3 * a') := by
        rw [← pow_mul, mul_comm a' 3]
      rw [hlhs, hrhs]
      exact Nat.mul_le_mul_left 4 (Nat.pow_le_pow_right (by omega) (by omega))
  have h3b : 8 * (3 ^ b) ^ 2 ≤ 9 * (Nat.totient (3 ^ b)) ^ 3 := by
    cases b with
    | zero => norm_num
    | succ b' =>
      rw [Nat.totient_prime_pow Nat.prime_three (Nat.succ_pos b'), Nat.succ_sub_one]
      simp only [show 3 - 1 = 2 from rfl]
      have hlhs : 8 * (3 ^ (b' + 1)) ^ 2 = 72 * 3 ^ (2 * b') := by
        rw [← pow_mul, show (b' + 1) * 2 = 2 * b' + 2 by omega, pow_add]
        ring
      have hrhs : 9 * (3 ^ b' * 2) ^ 3 = 72 * 3 ^ (3 * b') := by
        rw [mul_pow, ← pow_mul, mul_comm b' 3]
        ring
      rw [hlhs, hrhs]
      exact Nat.mul_le_mul_left 72 (Nat.pow_le_pow_right (by omega) (by omega))
  have hr_le := coprime_two_three_sq_le_totient_cube r hr hr2 hndvd3
  have hcop2 : Nat.Coprime (2 ^ a) m₁ := (Nat.prime_two.coprime_iff_not_dvd.mpr hndvd2).pow_left a
  have hcop3 : Nat.Coprime (3 ^ b) r := (Nat.prime_three.coprime_iff_not_dvd.mpr hndvd3).pow_left b
  have htot : Nat.totient m = Nat.totient (2 ^ a) * Nat.totient (3 ^ b) * Nat.totient r := by
    rw [hm_eq, Nat.totient_mul hcop2, hm₁_eq, Nat.totient_mul hcop3, mul_assoc]
  have hmul8 : 8 * m ^ 2 ≤ 36 * (Nat.totient m) ^ 3 := by
    calc 8 * m ^ 2 = (2 ^ a) ^ 2 * (8 * (3 ^ b) ^ 2) * r ^ 2 := by
          rw [hm_eq, hm₁_eq]; ring
      _ ≤ (4 * (Nat.totient (2 ^ a)) ^ 3) * (9 * (Nat.totient (3 ^ b)) ^ 3) * (Nat.totient r) ^ 3 :=
          Nat.mul_le_mul (Nat.mul_le_mul h2a h3b) hr_le
      _ = 36 * (Nat.totient m) ^ 3 := by rw [htot]; ring
  omega

private lemma add_one_mul_choose_eq :
    ∀ n k : ℕ, (n + 1) * n.choose k = (n + 1).choose (k + 1) * (k + 1) := by
  intro n
  induction n with
  | zero =>
    intro k
    cases k with
    | zero => norm_num
    | succ k =>
      have h0 : Nat.choose 1 (k + 1 + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp [h0]
  | succ n ih =>
    intro k
    cases k with
    | zero => simp [Nat.choose_one_right]
    | succ k =>
      have h1 := ih k
      have h2 := ih (k + 1)
      have h3 : (n + 1).choose (k + 1) = n.choose k + n.choose (k + 1) := Nat.choose_succ_succ n k
      rw [Nat.choose_succ_succ (n + 1) (k + 1), Nat.choose_succ_succ n k]
      simp only [Nat.succ_eq_add_one] at h1 h2 h3 ⊢
      calc (n + 1 + 1) * (n.choose k + n.choose (k + 1))
          = (n + 1) * n.choose k + (n + 1) * n.choose (k + 1) + (n.choose k + n.choose (k + 1)) := by ring
        _ = (n + 1).choose (k + 1) * (k + 1) + (n + 1).choose (k + 1 + 1) * (k + 1 + 1) +
            (n + 1).choose (k + 1) := by rw [h1, h2, ← h3]
        _ = (n + 1).choose (k + 1) * (k + 1 + 1) + (n + 1).choose (k + 1 + 1) * (k + 1 + 1) := by ring
        _ = (n.choose k + n.choose (k + 1) + (n + 1).choose (k + 1 + 1)) * (k + 1 + 1) := by
            rw [h3]; ring

private lemma central_binom_sq_le (k : ℕ) :
    (Nat.choose (2 * k) k) ^ 2 * (2 * k + 1) ≤ 4 ^ (2 * k) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    have hrec : (k + 1) * Nat.choose (2 * (k + 1)) (k + 1) =
        2 * (2 * k + 1) * Nat.choose (2 * k) k := by
      have h1 := add_one_mul_choose_eq (2 * k + 1) k
      have h2 := add_one_mul_choose_eq (2 * k) k
      have hsym : (2 * k + 1).choose k = (2 * k + 1).choose (k + 1) := by
        have := Nat.choose_symm (show k ≤ 2 * k + 1 by omega)
        simpa [show 2 * k + 1 - k = k + 1 by omega] using this.symm
      rw [hsym] at h1
      have hmul : (k + 1) * ((2 * k + 2).choose (k + 1) * (k + 1)) =
          (k + 1) * (2 * (2 * k + 1) * (2 * k).choose k) := by
        calc (k + 1) * ((2 * k + 2).choose (k + 1) * (k + 1))
            = (k + 1) * ((2 * k + 2) * (2 * k + 1).choose (k + 1)) := by rw [← h1]
          _ = (2 * k + 2) * ((2 * k + 1).choose (k + 1) * (k + 1)) := by ring
          _ = (2 * k + 2) * ((2 * k + 1) * (2 * k).choose k) := by rw [← h2]
          _ = (k + 1) * (2 * (2 * k + 1) * (2 * k).choose k) := by ring
      have hcancel := Nat.eq_of_mul_eq_mul_left (Nat.succ_pos k) hmul
      rw [show 2 * (k + 1) = 2 * k + 2 by omega]
      linarith [hcancel]
    have hstep : (k + 1) ^ 2 * ((Nat.choose (2 * (k + 1)) (k + 1)) ^ 2 * (2 * (k + 1) + 1)) ≤
        (k + 1) ^ 2 * 4 ^ (2 * (k + 1)) := by
      have hlhs : (k + 1) ^ 2 * ((Nat.choose (2 * (k + 1)) (k + 1)) ^ 2 * (2 * (k + 1) + 1)) =
          (4 * (2 * k + 1) * (2 * k + 3)) * ((Nat.choose (2 * k) k) ^ 2 * (2 * k + 1)) := by
        calc _ = ((k + 1) * Nat.choose (2 * (k + 1)) (k + 1)) ^ 2 * (2 * k + 3) := by ring
          _ = (2 * (2 * k + 1) * Nat.choose (2 * k) k) ^ 2 * (2 * k + 3) := by rw [hrec]
          _ = (4 * (2 * k + 1) * (2 * k + 3)) * ((Nat.choose (2 * k) k) ^ 2 * (2 * k + 1)) := by ring
      have hquad : 4 * (2 * k + 1) * (2 * k + 3) ≤ 16 * (k + 1) ^ 2 := by nlinarith
      rw [hlhs]
      calc (4 * (2 * k + 1) * (2 * k + 3)) * ((Nat.choose (2 * k) k) ^ 2 * (2 * k + 1))
          ≤ (16 * (k + 1) ^ 2) * 4 ^ (2 * k) := Nat.mul_le_mul hquad ih
        _ = (k + 1) ^ 2 * 4 ^ (2 * (k + 1)) := by
            rw [show 2 * (k + 1) = 2 * k + 2 by omega, pow_add]
            ring
    exact Nat.le_of_mul_le_mul_left hstep (by positivity)

private lemma choose_sq_mul_le_four_pow (L t : ℕ) (_hL : 1 ≤ L) :
    (Nat.choose L t) ^ 2 * L ≤ 4 ^ L := by
  have hmid : L.choose t ≤ L.choose (L / 2) := Nat.choose_le_middle t L
  have hle1 : (L.choose t) ^ 2 * L ≤ (L.choose (L / 2)) ^ 2 * L :=
    Nat.mul_le_mul_right L (Nat.pow_le_pow_left hmid 2)
  refine le_trans hle1 ?_
  rcases Nat.even_or_odd L with ⟨k, hk⟩ | ⟨k, hk⟩
  · have hL2 : L = 2 * k := by omega
    rw [hL2, show 2 * k / 2 = k by omega]
    exact le_trans (Nat.mul_le_mul_left _ (by omega : 2 * k ≤ 2 * k + 1)) (central_binom_sq_le k)
  · rw [hk, show (2 * k + 1) / 2 = k by omega]
    cases k with
    | zero => norm_num
    | succ k' =>
      have hadd : (2 * (k' + 1) + 1).choose (k' + 1) ≤ 2 * (2 * (k' + 1)).choose (k' + 1) := by
        rw [Nat.choose_succ_succ, Nat.succ_eq_add_one]
        have hle := Nat.choose_le_middle k' (2 * (k' + 1))
        rw [show 2 * (k' + 1) / 2 = k' + 1 by omega] at hle
        omega
      calc ((2 * (k' + 1) + 1).choose (k' + 1)) ^ 2 * (2 * (k' + 1) + 1)
          ≤ (2 * (2 * (k' + 1)).choose (k' + 1)) ^ 2 * (2 * (k' + 1) + 1) :=
            Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hadd 2)
        _ = 4 * (((2 * (k' + 1)).choose (k' + 1)) ^ 2 * (2 * (k' + 1) + 1)) := by ring
        _ ≤ 4 * 4 ^ (2 * (k' + 1)) := Nat.mul_le_mul_left 4 (central_binom_sq_le (k' + 1))
        _ = 4 ^ (2 * (k' + 1) + 1) := by rw [pow_succ, mul_comm]

private lemma slice_card_binary_le (L : ℕ) (hL : 1 ≤ L) (t : ℤ) :
    ({v : Fin L → Fin 2 | ∑ i : Fin L, ((v i).1 : ℤ) = t}.ncard : ℝ) ≤
      (2 : ℝ) ^ L / Real.sqrt (L : ℝ) := by
  by_cases ht : 0 ≤ t
  · let k : ℕ := t.toNat
    have hk : (k : ℤ) = t := Int.toNat_of_nonneg ht
    let S : Set (Fin L → Fin 2) := {v : Fin L → Fin 2 | ∑ i : Fin L, ((v i).1 : ℤ) = t}
    let φ : S → (Finset.univ : Finset (Fin L)).powersetCard k := fun ⟨v, hv⟩ =>
      ⟨Finset.univ.filter (fun i : Fin L => (v i).1 = 1), by
        rw [Finset.mem_powersetCard]
        refine ⟨Finset.subset_univ _, ?_⟩
        have hsum_nat : ∑ i : Fin L, (v i).1 = (Finset.univ.filter (fun i : Fin L => (v i).1 = 1)).card := by
          rw [Finset.card_eq_sum_ones, ← Finset.sum_filter_add_sum_filter_not Finset.univ
            (fun i : Fin L => (v i).1 = 1)]
          have h1 : ∑ i ∈ Finset.univ.filter (fun i : Fin L => (v i).1 = 1), (v i).1 =
              ∑ _i ∈ Finset.univ.filter (fun i : Fin L => (v i).1 = 1), 1 :=
            Finset.sum_congr rfl fun i hi => (Finset.mem_filter.mp hi).2
          have h2 : ∑ i ∈ Finset.univ.filter (fun i : Fin L => ¬ (v i).1 = 1), (v i).1 = 0 := by
            refine Finset.sum_eq_zero fun i hi => ?_
            have hne := (Finset.mem_filter.mp hi).2
            have hlt := (v i).2
            omega
          rw [h1, h2, add_zero]
        have hv' : (∑ i : Fin L, (v i).1 : ℤ) = (k : ℤ) := by
          have := hv
          rw [Set.mem_ofPred_eq, ← hk] at this
          simpa using this
        have hnat : ∑ i : Fin L, (v i).1 = k := by exact_mod_cast hv'
        omega⟩
    have hinj : Function.Injective φ := by
      rintro ⟨v₁, hv₁⟩ ⟨v₂, hv₂⟩ hφ
      apply Subtype.ext
      ext i
      dsimp only
      have hset : Finset.univ.filter (fun j : Fin L => (v₁ j).1 = 1) =
          Finset.univ.filter (fun j : Fin L => (v₂ j).1 = 1) := congrArg Subtype.val hφ
      have hiff : (v₁ i).1 = 1 ↔ (v₂ i).1 = 1 := by
        have := Finset.ext_iff.mp hset i
        simpa using this
      have h1 := (v₁ i).2
      have h2 := (v₂ i).2
      omega
    have hcard_le : S.ncard ≤ Nat.choose L k := by
      rw [Set.ncard_eq_toFinset_card']
      have hcoe : S.toFinset.card = Fintype.card S := by
        rw [← Fintype.card_coe]
        refine Fintype.card_congr ?_
        exact
          { toFun := fun ⟨x, hx⟩ => ⟨x, Set.mem_toFinset.mp hx⟩
            invFun := fun ⟨x, hx⟩ => ⟨x, Set.mem_toFinset.mpr hx⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
      rw [hcoe]
      calc Fintype.card S
          ≤ Fintype.card ((Finset.univ : Finset (Fin L)).powersetCard k) :=
            Fintype.card_le_of_injective φ hinj
        _ = ((Finset.univ : Finset (Fin L)).powersetCard k).card := Fintype.card_coe _
        _ = Nat.choose L k := by rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
    have hsq_nat := choose_sq_mul_le_four_pow L k hL
    have hsq_real : (S.ncard : ℝ) ^ 2 * (L : ℝ) ≤ ((2 : ℝ) ^ L) ^ 2 := by
      have h1 : (S.ncard : ℝ) ^ 2 * (L : ℝ) ≤ ((Nat.choose L k : ℝ)) ^ 2 * (L : ℝ) := by
        gcongr
      have h2 : ((Nat.choose L k : ℝ)) ^ 2 * (L : ℝ) ≤ (4 : ℝ) ^ L := by exact_mod_cast hsq_nat
      have h4 : (4 : ℝ) ^ L = ((2 : ℝ) ^ L) ^ 2 := by
        rw [← pow_mul, mul_comm, pow_mul]
        norm_num
      linarith
    have hsqrt_pos : 0 < Real.sqrt (L : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < L))
    rw [le_div_iff₀ hsqrt_pos]
    have hsq2 : ((S.ncard : ℝ) * Real.sqrt (L : ℝ)) ^ 2 ≤ ((2 : ℝ) ^ L) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      exact hsq_real
    nlinarith [mul_nonneg (Nat.cast_nonneg S.ncard) (le_of_lt hsqrt_pos), pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) L]
  · have hemp : {v : Fin L → Fin 2 | ∑ i : Fin L, ((v i).1 : ℤ) = t} = ∅ := by
      ext v
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      have hnn : (0 : ℤ) ≤ ∑ i : Fin L, ((v i).1 : ℤ) :=
        Finset.sum_nonneg fun i _ => Int.natCast_nonneg _
      omega
    rw [hemp, Set.ncard_empty, Nat.cast_zero]
    positivity

private lemma slice_card_even_le (r L : ℕ) (_hr : 1 ≤ r) (hL : 1 ≤ L) (t : ℤ) :
    ({v : Fin L → Fin (2 * r) | ∑ i : Fin L, ((v i).1 : ℤ) = t}.ncard : ℝ) ≤
      ((2 * r : ℕ) : ℝ) ^ L / Real.sqrt (L : ℝ) := by
  let S : Set (Fin L → Fin (2 * r)) := {v : Fin L → Fin (2 * r) | ∑ i : Fin L, ((v i).1 : ℤ) = t}
  let qOf : (Fin L → Fin (2 * r)) → (Fin L → Fin r) :=
    fun v i => ⟨(v i).1 / 2, by have := (v i).2; omega⟩
  let bOf : (Fin L → Fin (2 * r)) → (Fin L → Fin 2) :=
    fun v i => ⟨(v i).1 % 2, Nat.mod_lt _ (by omega)⟩
  have hsub : S ⊆ ⋃ q ∈ (Finset.univ : Finset (Fin L → Fin r)), {v | v ∈ S ∧ qOf v = q} := by
    intro v hv
    exact Set.mem_iUnion₂.mpr ⟨qOf v, Finset.mem_univ _, hv, rfl⟩
  have hfiber : ∀ q : Fin L → Fin r,
      ({v | v ∈ S ∧ qOf v = q}.ncard : ℝ) ≤ (2 : ℝ) ^ L / Real.sqrt (L : ℝ) := by
    intro q
    let t' : ℤ := t - 2 * ∑ i : Fin L, ((q i).1 : ℤ)
    let Fq : Set (Fin L → Fin (2 * r)) := {v | v ∈ S ∧ qOf v = q}
    let T : Set (Fin L → Fin 2) := {b : Fin L → Fin 2 | ∑ i : Fin L, ((b i).1 : ℤ) = t'}
    let ψ : Fq → T := fun ⟨v, hv, hq⟩ =>
      ⟨bOf v, by
        rw [Set.mem_ofPred_eq]
        have hsum_v : ∑ i : Fin L, ((v i).1 : ℤ) = t := hv
        have hsplit : ∑ i : Fin L, ((v i).1 : ℤ) =
            2 * (∑ i : Fin L, ((q i).1 : ℤ)) + ∑ i : Fin L, ((bOf v i).1 : ℤ) := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          have hqi : (q i).1 = (v i).1 / 2 := by
            have := congrArg (fun f => (f i).1) hq.symm
            exact this
          have hdm := Nat.div_add_mod (v i).1 2
          have hdmZ : (2 : ℤ) * (((v i).1 / 2 : ℕ) : ℤ) + (((v i).1 % 2 : ℕ) : ℤ) = ((v i).1 : ℤ) := by
            exact_mod_cast hdm
          dsimp only [bOf]
          rw [hqi]
          linarith
        dsimp only [t']
        linarith⟩
    have hψ_inj : Function.Injective ψ := by
      rintro ⟨v₁, hv₁, hq₁⟩ ⟨v₂, hv₂, hq₂⟩ hψ
      apply Subtype.ext
      ext i
      dsimp only
      have hqeq : (v₁ i).1 / 2 = (v₂ i).1 / 2 := by
        have h1 : (qOf v₁ i).1 = (q i).1 := congrArg (fun f => (f i).1) hq₁
        have h2 : (qOf v₂ i).1 = (q i).1 := congrArg (fun f => (f i).1) hq₂
        exact h1.trans h2.symm
      have hbeq : (v₁ i).1 % 2 = (v₂ i).1 % 2 := congrArg (fun x => (x.1 i).1) hψ
      have h1 := Nat.div_add_mod (v₁ i).1 2
      have h2 := Nat.div_add_mod (v₂ i).1 2
      omega
    have hle_nat : Fq.ncard ≤ T.ncard := by
      rw [Set.ncard_eq_toFinset_card', Set.ncard_eq_toFinset_card']
      have h1 : Fq.toFinset.card = Fintype.card Fq := by
        rw [← Fintype.card_coe]
        refine Fintype.card_congr ?_
        exact
          { toFun := fun ⟨x, hx⟩ => ⟨x, Set.mem_toFinset.mp hx⟩
            invFun := fun ⟨x, hx⟩ => ⟨x, Set.mem_toFinset.mpr hx⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
      have h2 : T.toFinset.card = Fintype.card T := by
        rw [← Fintype.card_coe]
        refine Fintype.card_congr ?_
        exact
          { toFun := fun ⟨x, hx⟩ => ⟨x, Set.mem_toFinset.mp hx⟩
            invFun := fun ⟨x, hx⟩ => ⟨x, Set.mem_toFinset.mpr hx⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
      rw [h1, h2]
      exact Fintype.card_le_of_injective ψ hψ_inj
    have hle_R : (Fq.ncard : ℝ) ≤ (T.ncard : ℝ) := by exact_mod_cast hle_nat
    exact le_trans hle_R (slice_card_binary_le L hL t')
  have hnc : S.ncard ≤ ∑ q ∈ (Finset.univ : Finset (Fin L → Fin r)), {v | v ∈ S ∧ qOf v = q}.ncard :=
    (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (ncard_biUnion_finset_le _ _)
  calc (S.ncard : ℝ)
      ≤ ∑ q ∈ (Finset.univ : Finset (Fin L → Fin r)), ({v | v ∈ S ∧ qOf v = q}.ncard : ℝ) := by
        exact_mod_cast hnc
    _ ≤ ∑ _q ∈ (Finset.univ : Finset (Fin L → Fin r)), ((2 : ℝ) ^ L / Real.sqrt (L : ℝ)) :=
        Finset.sum_le_sum fun q _ => hfiber q
    _ = ((Finset.univ : Finset (Fin L → Fin r)).card : ℝ) * ((2 : ℝ) ^ L / Real.sqrt (L : ℝ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = ((r : ℝ) ^ L) * ((2 : ℝ) ^ L / Real.sqrt (L : ℝ)) := by
        rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
        push_cast; rfl
    _ = ((2 * r : ℕ) : ℝ) ^ L / Real.sqrt (L : ℝ) := by
        rw [Nat.cast_mul, Nat.cast_ofNat, mul_pow]
        ring

private lemma sum_sq_zero_mean (M : ℕ) :
    ∀ L : ℕ,
      ∑ v : Fin L → Fin (M + 1),
        (∑ i : Fin L, (if (v i).1 = M then (M : ℝ) else (-1 : ℝ))) ^ 2 =
        (L : ℝ) * (M : ℝ) * ((M + 1 : ℕ) : ℝ) ^ L := by
  let valX : Fin (M + 1) → ℝ := fun x => if x.1 = M then (M : ℝ) else (-1 : ℝ)
  have hmean : ∑ x : Fin (M + 1), valX x = 0 := by
    rw [Fin.sum_univ_castSucc]
    have h1 : ∑ x : Fin M, valX x.castSucc = ∑ _x : Fin M, (-1 : ℝ) := by
      refine Finset.sum_congr rfl fun x _ => ?_
      dsimp only [valX]
      rw [if_neg (by have := x.2; simp; omega)]
    have h2 : valX (Fin.last M) = (M : ℝ) := by
      dsimp only [valX]
      simp
    rw [h1, h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hsq : ∑ x : Fin (M + 1), (valX x) ^ 2 = (M : ℝ) * ((M + 1 : ℕ) : ℝ) := by
    rw [Fin.sum_univ_castSucc]
    have h1 : ∑ x : Fin M, (valX x.castSucc) ^ 2 = ∑ _x : Fin M, (1 : ℝ) := by
      refine Finset.sum_congr rfl fun x _ => ?_
      dsimp only [valX]
      rw [if_neg (by have := x.2; simp; omega)]
      norm_num
    have h2 : (valX (Fin.last M)) ^ 2 = (M : ℝ) ^ 2 := by
      dsimp only [valX]
      simp
    rw [h1, h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    push_cast
    ring
  intro L
  induction L with
  | zero =>
    simp
  | succ L ih =>
    let e : (Fin (M + 1) × (Fin L → Fin (M + 1))) ≃ (Fin (L + 1) → Fin (M + 1)) :=
      Fin.consEquiv (fun _ => Fin (M + 1))
    rw [← Fintype.sum_equiv e
      (fun p => (valX p.1 + ∑ i : Fin L, valX (p.2 i)) ^ 2)
      (fun v => (∑ i : Fin (L + 1), valX (v i)) ^ 2)
      (by
        rintro ⟨x, w⟩
        dsimp only [e]
        rw [Fin.sum_univ_succ]
        rfl)]
    rw [Fintype.sum_prod_type]
    have hexp : ∀ x : Fin (M + 1), ∀ w : Fin L → Fin (M + 1),
        (valX x + ∑ i : Fin L, valX (w i)) ^ 2 =
          (valX x) ^ 2 + 2 * valX x * (∑ i : Fin L, valX (w i)) + (∑ i : Fin L, valX (w i)) ^ 2 :=
      fun _ _ => by ring
    simp_rw [hexp, Finset.sum_add_distrib]
    have hterm1 : ∑ x : Fin (M + 1), ∑ _w : Fin L → Fin (M + 1), (valX x) ^ 2 =
        (M : ℝ) * ((M + 1 : ℕ) : ℝ) ^ (L + 1) := by
      simp_rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
      rw [← Finset.mul_sum, hsq]
      push_cast
      rw [pow_succ]
      ring
    have hterm2 : ∑ x : Fin (M + 1), ∑ w : Fin L → Fin (M + 1),
        2 * valX x * (∑ i : Fin L, valX (w i)) = 0 := by
      simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
      have hfactor : ∑ x : Fin (M + 1), 2 * valX x = 0 := by
        rw [← Finset.mul_sum, hmean, mul_zero]
      rw [hfactor, zero_mul]
    have hterm3 : ∑ _x : Fin (M + 1), ∑ w : Fin L → Fin (M + 1), (∑ i : Fin L, valX (w i)) ^ 2 =
        (L : ℝ) * (M : ℝ) * ((M + 1 : ℕ) : ℝ) ^ (L + 1) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ih]
      rw [pow_succ]
      ring
    rw [hterm1, hterm2, add_zero, hterm3]
    push_cast
    ring

private lemma chebyshev_top_digit_le (M L : ℕ) (hM : 2 ≤ M) (hL : 1 ≤ L) :
    ({v : Fin L → Fin (M + 1) |
      3 * (Finset.univ.filter (fun i : Fin L => (v i).1 < M)).card < L}.ncard : ℝ) ≤
      (9 / (4 * (L : ℝ))) * ((M + 1 : ℕ) : ℝ) ^ L := by
  let E : Set (Fin L → Fin (M + 1)) :=
    {v : Fin L → Fin (M + 1) | 3 * (Finset.univ.filter (fun i : Fin L => (v i).1 < M)).card < L}
  let valX : Fin (M + 1) → ℝ := fun x => if x.1 = M then (M : ℝ) else (-1 : ℝ)
  have hpt : ∀ v ∈ E.toFinset,
      ((L : ℝ) * ((M + 1 : ℕ) : ℝ)) ^ 2 ≤ 9 * (∑ i : Fin L, valX (v i)) ^ 2 := by
    intro v hv
    have hvE_mem : v ∈ E := Set.mem_toFinset.mp hv
    have hvE : 3 * (Finset.univ.filter (fun i : Fin L => (v i).1 < M)).card < L := hvE_mem
    let Slt := Finset.univ.filter (fun i : Fin L => (v i).1 < M)
    let Seq := Finset.univ.filter (fun i : Fin L => ¬ (v i).1 < M)
    have hsum_val : ∑ i : Fin L, valX (v i) = (Seq.card : ℝ) * (M : ℝ) - (Slt.card : ℝ) := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin L => (v i).1 < M)]
      have h1 : ∑ i ∈ Slt, valX (v i) = -(Slt.card : ℝ) := by
        have : ∑ i ∈ Slt, valX (v i) = ∑ _i ∈ Slt, (-1 : ℝ) := by
          refine Finset.sum_congr rfl fun i hi => ?_
          have hlt := (Finset.mem_filter.mp hi).2
          dsimp only [valX]
          rw [if_neg (by omega)]
        rw [this, Finset.sum_const, nsmul_eq_mul]
        ring
      have h2 : ∑ i ∈ Seq, valX (v i) = (Seq.card : ℝ) * (M : ℝ) := by
        have : ∑ i ∈ Seq, valX (v i) = ∑ _i ∈ Seq, (M : ℝ) := by
          refine Finset.sum_congr rfl fun i hi => ?_
          have hge := (Finset.mem_filter.mp hi).2
          have hlt := (v i).2
          dsimp only [valX]
          rw [if_pos (by omega)]
        rw [this, Finset.sum_const, nsmul_eq_mul]
      rw [h1, h2]
      ring
    have hcards : Slt.card + Seq.card = L := by
      dsimp only [Slt, Seq]
      rw [Finset.card_eq_sum_ones, Finset.card_eq_sum_ones, Finset.sum_filter_add_sum_filter_not,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
    have hcardsR : (Slt.card : ℝ) + (Seq.card : ℝ) = (L : ℝ) := by exact_mod_cast hcards
    have h3c : 3 * (Slt.card : ℝ) ≤ (L : ℝ) := by exact_mod_cast (le_of_lt hvE)
    have hM2 : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    have hL0 : (0 : ℝ) ≤ (L : ℝ) := by positivity
    have hlin : (L : ℝ) * ((M + 1 : ℕ) : ℝ) ≤ 3 * (∑ i : Fin L, valX (v i)) := by
      rw [hsum_val]
      push_cast
      nlinarith
    have hsq : ((L : ℝ) * ((M + 1 : ℕ) : ℝ)) ^ 2 ≤ (3 * (∑ i : Fin L, valX (v i))) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hlin 2
    linarith
  have hsum_le : (E.toFinset.card : ℝ) * ((L : ℝ) * ((M + 1 : ℕ) : ℝ)) ^ 2 ≤
      9 * ((L : ℝ) * (M : ℝ) * ((M + 1 : ℕ) : ℝ) ^ L) := by
    calc (E.toFinset.card : ℝ) * ((L : ℝ) * ((M + 1 : ℕ) : ℝ)) ^ 2
        = ∑ _v ∈ E.toFinset, ((L : ℝ) * ((M + 1 : ℕ) : ℝ)) ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ v ∈ E.toFinset, 9 * (∑ i : Fin L, valX (v i)) ^ 2 := Finset.sum_le_sum hpt
      _ ≤ ∑ v ∈ (Finset.univ : Finset (Fin L → Fin (M + 1))), 9 * (∑ i : Fin L, valX (v i)) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => by positivity
      _ = 9 * ∑ v : Fin L → Fin (M + 1), (∑ i : Fin L, valX (v i)) ^ 2 := by rw [← Finset.mul_sum]
      _ = 9 * ((L : ℝ) * (M : ℝ) * ((M + 1 : ℕ) : ℝ) ^ L) := by rw [sum_sq_zero_mean M L]
  rw [Set.ncard_eq_toFinset_card']
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (by omega : 0 < L)
  have hMpos : (0 : ℝ) < ((M + 1 : ℕ) : ℝ) := by positivity
  have h4M : 4 * (M : ℝ) ≤ ((M + 1 : ℕ) : ℝ) ^ 2 := by
    push_cast
    nlinarith [sq_nonneg ((M : ℝ) - 1)]
  have hden_pos : (0 : ℝ) < (L : ℝ) ^ 2 * ((M + 1 : ℕ) : ℝ) ^ 2 := by positivity
  rw [show (9 / (4 * (L : ℝ))) * ((M + 1 : ℕ) : ℝ) ^ L =
      (9 * ((M + 1 : ℕ) : ℝ) ^ L) / (4 * (L : ℝ)) by ring, le_div_iff₀ (by positivity)]
  have hstep1 : (E.toFinset.card : ℝ) * (4 * (L : ℝ)) * ((L : ℝ) * ((M + 1 : ℕ) : ℝ) ^ 2) ≤
      (9 * ((M + 1 : ℕ) : ℝ) ^ L) * ((L : ℝ) * ((M + 1 : ℕ) : ℝ) ^ 2) := by
    calc (E.toFinset.card : ℝ) * (4 * (L : ℝ)) * ((L : ℝ) * ((M + 1 : ℕ) : ℝ) ^ 2)
        = 4 * ((E.toFinset.card : ℝ) * ((L : ℝ) * ((M + 1 : ℕ) : ℝ)) ^ 2) := by ring
      _ ≤ 4 * (9 * ((L : ℝ) * (M : ℝ) * ((M + 1 : ℕ) : ℝ) ^ L)) := by linarith
      _ = 9 * (4 * (M : ℝ)) * (L : ℝ) * ((M + 1 : ℕ) : ℝ) ^ L := by ring
      _ ≤ 9 * (((M + 1 : ℕ) : ℝ) ^ 2) * (L : ℝ) * ((M + 1 : ℕ) : ℝ) ^ L := by
          gcongr
      _ = (9 * ((M + 1 : ℕ) : ℝ) ^ L) * ((L : ℝ) * ((M + 1 : ℕ) : ℝ) ^ 2) := by ring
  exact le_of_mul_le_mul_right hstep1 (by positivity)

private lemma sum_pow_card_finset (M L : ℕ) :
    ∑ S : Finset (Fin L), ((M : ℕ) : ℝ) ^ S.card = ((M + 1 : ℕ) : ℝ) ^ L := by
  have hnat : ∑ S : Finset (Fin L), M ^ S.card = (M + 1) ^ L := by
    have hcard := Fintype.card_fun (α := Fin L) (β := Fin (M + 1))
    rw [Fintype.card_fin, Fintype.card_fin] at hcard
    rw [← hcard, ← Finset.card_univ]
    rw [Finset.card_eq_sum_card_fiberwise (f := fun v : Fin L → Fin (M + 1) =>
        Finset.univ.filter (fun i : Fin L => (v i).1 < M))
      (t := (Finset.univ : Finset (Finset (Fin L)))) (fun _ _ => Finset.mem_univ _)]
    refine Finset.sum_congr rfl fun S _ => ?_
    let e : {v : Fin L → Fin (M + 1) // Finset.univ.filter (fun i : Fin L => (v i).1 < M) = S} ≃
        (S → Fin M) :=
      { toFun := fun ⟨v, hv⟩ i =>
          ⟨(v i.1).1, by
            have hi : i.1 ∈ Finset.univ.filter (fun j : Fin L => (v j).1 < M) := by
              rw [hv]; exact i.2
            exact (Finset.mem_filter.mp hi).2⟩
        invFun := fun w =>
          ⟨fun i => if hi : i ∈ S then ⟨(w ⟨i, hi⟩).1, by have := (w ⟨i, hi⟩).2; omega⟩
                    else ⟨M, by omega⟩, by
            ext i
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            by_cases hi : i ∈ S
            · simp only [hi, ↓reduceDIte, iff_true]
              exact (w ⟨i, hi⟩).2
            · simp [hi]⟩
        left_inv := by
          rintro ⟨v, hv⟩
          apply Subtype.ext
          ext i
          by_cases hi : i ∈ S
          · simp [hi]
          · simp only [hi, ↓reduceDIte]
            have hnot : ¬ (v i).1 < M := by
              intro hlt
              apply hi
              rw [← hv]
              exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩
            have hlt := (v i).2
            omega
        right_inv := by
          intro w
          ext i
          simp [i.2] }
    have hcoe : (Finset.univ.filter (fun v : Fin L → Fin (M + 1) =>
        Finset.univ.filter (fun i : Fin L => (v i).1 < M) = S)).card =
        Fintype.card {v : Fin L → Fin (M + 1) // Finset.univ.filter (fun i : Fin L => (v i).1 < M) = S} := by
      rw [← Fintype.card_coe]
      refine Fintype.card_congr ?_
      exact
        { toFun := fun ⟨v, hv⟩ => ⟨v, (Finset.mem_filter.mp hv).2⟩
          invFun := fun ⟨v, hv⟩ => ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    rw [hcoe, Fintype.card_congr e, Fintype.card_fun, Fintype.card_coe, Fintype.card_fin]
  exact_mod_cast hnat

private lemma slice_card_le (M L : ℕ) (hM : 1 ≤ M) (hL : 1 ≤ L) (t : ℤ) :
    ({v : Fin L → Fin (M + 1) | ∑ i : Fin L, ((v i).1 : ℤ) = t}.ncard : ℝ) ≤
      (4 / Real.sqrt (L : ℝ)) * ((M + 1 : ℕ) : ℝ) ^ L := by
  rcases Nat.even_or_odd (M + 1) with ⟨r, hr⟩ | ⟨r, hr⟩
  · have h2r : M + 1 = 2 * r := by omega
    have hr1 : 1 ≤ r := by omega
    have heven_gen : ∀ N : ℕ, N = 2 * r →
        ({v : Fin L → Fin N | ∑ i : Fin L, ((v i).1 : ℤ) = t}.ncard : ℝ) ≤
          (4 / Real.sqrt (L : ℝ)) * ((N : ℕ) : ℝ) ^ L := by
      rintro N rfl
      have hle := slice_card_even_le r L hr1 hL t
      have h1 : ((2 * r : ℕ) : ℝ) ^ L / Real.sqrt (L : ℝ) =
          (1 / Real.sqrt (L : ℝ)) * ((2 * r : ℕ) : ℝ) ^ L := by ring
      rw [h1] at hle
      have h4 : (1 / Real.sqrt (L : ℝ)) ≤ 4 / Real.sqrt (L : ℝ) := by
        gcongr
        norm_num
      exact le_trans hle (mul_le_mul_of_nonneg_right h4 (by positivity))
    exact heven_gen (M + 1) h2r
  · have hM2 : 2 ≤ M := by omega
    have hM2r : M = 2 * r := by omega
    have hr1 : 1 ≤ r := by omega
    let Ebad : Set (Fin L → Fin (M + 1)) :=
      {v : Fin L → Fin (M + 1) | 3 * (Finset.univ.filter (fun i : Fin L => (v i).1 < M)).card < L}
    let Egood : Set (Fin L → Fin (M + 1)) :=
      {v : Fin L → Fin (M + 1) |
        ∑ i : Fin L, ((v i).1 : ℤ) = t ∧
        L ≤ 3 * (Finset.univ.filter (fun i : Fin L => (v i).1 < M)).card}
    have hsplit : {v : Fin L → Fin (M + 1) | ∑ i : Fin L, ((v i).1 : ℤ) = t} ⊆ Ebad ∪ Egood := by
      intro v hv
      by_cases hlt : 3 * (Finset.univ.filter (fun i : Fin L => (v i).1 < M)).card < L
      · exact Or.inl hlt
      · exact Or.inr ⟨hv, by omega⟩
    have hgood_sub : Egood ⊆
        ⋃ S ∈ (Finset.univ : Finset (Finset (Fin L))).filter (fun S => L ≤ 3 * S.card),
          {v : Fin L → Fin (M + 1) |
            ∑ i : Fin L, ((v i).1 : ℤ) = t ∧
            Finset.univ.filter (fun i : Fin L => (v i).1 < M) = S} := by
      intro v ⟨hvsum, hvcard⟩
      exact Set.mem_iUnion₂.mpr ⟨Finset.univ.filter (fun i : Fin L => (v i).1 < M),
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvcard⟩, hvsum, rfl⟩
    have hgood_fiber : ∀ S : Finset (Fin L), L ≤ 3 * S.card →
        ({v : Fin L → Fin (M + 1) |
            ∑ i : Fin L, ((v i).1 : ℤ) = t ∧
            Finset.univ.filter (fun i : Fin L => (v i).1 < M) = S}.ncard : ℝ) ≤
          (Real.sqrt 3 / Real.sqrt (L : ℝ)) * ((M : ℕ) : ℝ) ^ S.card := by
      intro S hS
      have hS1 : 1 ≤ S.card := by omega
      have hcard_S : Fintype.card S = S.card := Fintype.card_coe S
      let eS' : Fin S.card ≃ S := (Fintype.equivFinOfCardEq hcard_S).symm
      let tS : ℤ := t - ((L - S.card : ℕ) : ℤ) * (M : ℤ)
      let TS : Set (Fin S.card → Fin (2 * r)) :=
        {w : Fin S.card → Fin (2 * r) | ∑ j : Fin S.card, ((w j).1 : ℤ) = tS}
      let FS : Set (Fin L → Fin (M + 1)) :=
        {v : Fin L → Fin (M + 1) |
          ∑ i : Fin L, ((v i).1 : ℤ) = t ∧
          Finset.univ.filter (fun i : Fin L => (v i).1 < M) = S}
      let ψ : FS → TS := fun ⟨v, hvsum, hvS⟩ =>
        ⟨fun j => ⟨(v (eS' j).1).1, by
            have hmem : (eS' j).1 ∈ Finset.univ.filter (fun i : Fin L => (v i).1 < M) := by
              rw [hvS]; exact (eS' j).2
            have hlt := (Finset.mem_filter.mp hmem).2
            omega⟩, by
          rw [Set.mem_ofPred_eq]
          have hsum_all : ∑ i : Fin L, ((v i).1 : ℤ) =
              (∑ i ∈ S, ((v i).1 : ℤ)) + ∑ i ∈ Finset.univ \ S, ((v i).1 : ℤ) := by
            rw [← Finset.sum_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset (Finset.subset_univ S)]
          have houtside : ∑ i ∈ Finset.univ \ S, ((v i).1 : ℤ) = ((L - S.card : ℕ) : ℤ) * (M : ℤ) := by
            have hconst : ∑ i ∈ Finset.univ \ S, ((v i).1 : ℤ) = ∑ _i ∈ Finset.univ \ S, (M : ℤ) := by
              refine Finset.sum_congr rfl fun i hi => ?_
              have hnot : i ∉ S := (Finset.mem_sdiff.mp hi).2
              have hge : ¬ (v i).1 < M := by
                intro hlt
                apply hnot
                rw [← hvS]
                exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩
              have hlt := (v i).2
              omega
            rw [hconst, Finset.sum_const, Finset.card_sdiff, Finset.inter_univ,
              Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          have hinside : ∑ j : Fin S.card, ((v (eS' j).1).1 : ℤ) = ∑ i ∈ S, ((v i).1 : ℤ) := by
            rw [Fintype.sum_equiv eS' _ (fun i : S => ((v i.1).1 : ℤ)) (fun _ => rfl)]
            exact Finset.sum_coe_sort S (fun i => ((v i).1 : ℤ))
          dsimp only [tS]
          linarith⟩
      have hψ_inj : Function.Injective ψ := by
        rintro ⟨v₁, hv₁sum, hv₁S⟩ ⟨v₂, hv₂sum, hv₂S⟩ hψ
        apply Subtype.ext
        ext i
        dsimp only
        by_cases hi : i ∈ S
        · let j : Fin S.card := eS'.symm ⟨i, hi⟩
          have hj : (eS' j).1 = i := by simp [j]
          have hval : (v₁ (eS' j).1).1 = (v₂ (eS' j).1).1 := congrArg (fun x => (x.1 j).1) hψ
          rw [hj] at hval
          exact hval
        · have h1 : ¬ (v₁ i).1 < M := by
            intro hlt; apply hi; rw [← hv₁S]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩
          have h2 : ¬ (v₂ i).1 < M := by
            intro hlt; apply hi; rw [← hv₂S]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩
          have hlt1 := (v₁ i).2
          have hlt2 := (v₂ i).2
          omega
      have hcard_le : FS.ncard ≤ TS.ncard := by
        rw [Set.ncard_eq_toFinset_card', Set.ncard_eq_toFinset_card']
        have h1 : FS.toFinset.card = Fintype.card FS := by
          rw [← Fintype.card_coe]
          refine Fintype.card_congr ?_
          exact
            { toFun := fun ⟨x, hx⟩ => ⟨x, Set.mem_toFinset.mp hx⟩
              invFun := fun ⟨x, hx⟩ => ⟨x, Set.mem_toFinset.mpr hx⟩
              left_inv := fun _ => rfl
              right_inv := fun _ => rfl }
        have h2 : TS.toFinset.card = Fintype.card TS := by
          rw [← Fintype.card_coe]
          refine Fintype.card_congr ?_
          exact
            { toFun := fun ⟨x, hx⟩ => ⟨x, Set.mem_toFinset.mp hx⟩
              invFun := fun ⟨x, hx⟩ => ⟨x, Set.mem_toFinset.mpr hx⟩
              left_inv := fun _ => rfl
              right_inv := fun _ => rfl }
        rw [h1, h2]
        exact Fintype.card_le_of_injective ψ hψ_inj
      have heven := slice_card_even_le r S.card hr1 hS1 tS
      have hsqrt_cmp : 1 / Real.sqrt (S.card : ℝ) ≤ Real.sqrt 3 / Real.sqrt (L : ℝ) := by
        have hSpos : 0 < Real.sqrt (S.card : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < S.card))
        have hLpos : 0 < Real.sqrt (L : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < L))
        rw [div_le_div_iff₀ hSpos hLpos, one_mul, ← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
        exact Real.sqrt_le_sqrt (by exact_mod_cast hS)
      calc (FS.ncard : ℝ)
          ≤ (TS.ncard : ℝ) := by exact_mod_cast hcard_le
        _ ≤ ((2 * r : ℕ) : ℝ) ^ S.card / Real.sqrt (S.card : ℝ) := heven
        _ = (1 / Real.sqrt (S.card : ℝ)) * ((M : ℕ) : ℝ) ^ S.card := by rw [← hM2r]; ring
        _ ≤ (Real.sqrt 3 / Real.sqrt (L : ℝ)) * ((M : ℕ) : ℝ) ^ S.card :=
            mul_le_mul_of_nonneg_right hsqrt_cmp (by positivity)
    have hgood_le : (Egood.ncard : ℝ) ≤ (Real.sqrt 3 / Real.sqrt (L : ℝ)) * ((M + 1 : ℕ) : ℝ) ^ L := by
      have hnc := (Set.ncard_le_ncard hgood_sub (Set.toFinite _)).trans (ncard_biUnion_finset_le _ _)
      calc (Egood.ncard : ℝ)
          ≤ ∑ S ∈ (Finset.univ : Finset (Finset (Fin L))).filter (fun S => L ≤ 3 * S.card),
              ({v : Fin L → Fin (M + 1) |
                ∑ i : Fin L, ((v i).1 : ℤ) = t ∧
                Finset.univ.filter (fun i : Fin L => (v i).1 < M) = S}.ncard : ℝ) := by
            exact_mod_cast hnc
        _ ≤ ∑ S ∈ (Finset.univ : Finset (Finset (Fin L))).filter (fun S => L ≤ 3 * S.card),
              (Real.sqrt 3 / Real.sqrt (L : ℝ)) * ((M : ℕ) : ℝ) ^ S.card :=
            Finset.sum_le_sum fun S hS => hgood_fiber S (Finset.mem_filter.mp hS).2
        _ ≤ ∑ S : Finset (Fin L), (Real.sqrt 3 / Real.sqrt (L : ℝ)) * ((M : ℕ) : ℝ) ^ S.card :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => by positivity
        _ = (Real.sqrt 3 / Real.sqrt (L : ℝ)) * ∑ S : Finset (Fin L), ((M : ℕ) : ℝ) ^ S.card := by
            rw [← Finset.mul_sum]
        _ = (Real.sqrt 3 / Real.sqrt (L : ℝ)) * ((M + 1 : ℕ) : ℝ) ^ L := by
            rw [sum_pow_card_finset M L]
    have hbad_le := chebyshev_top_digit_le M L hM2 hL
    have hunion : ({v : Fin L → Fin (M + 1) | ∑ i : Fin L, ((v i).1 : ℤ) = t}.ncard : ℝ) ≤
        (Ebad.ncard : ℝ) + (Egood.ncard : ℝ) := by
      have hnat := (Set.ncard_le_ncard hsplit (Set.toFinite _)).trans (Set.ncard_union_le Ebad Egood)
      exact_mod_cast hnat
    have hL_ge_sqrt : Real.sqrt (L : ℝ) ≤ (L : ℝ) := by
      have h1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
      have hsq : (L : ℝ) ≤ (L : ℝ) ^ 2 := by nlinarith
      calc Real.sqrt (L : ℝ) ≤ Real.sqrt ((L : ℝ) ^ 2) := Real.sqrt_le_sqrt hsq
        _ = (L : ℝ) := Real.sqrt_sq (by positivity)
    have hsqrt_pos : 0 < Real.sqrt (L : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < L))
    have hinv_le : 9 / (4 * (L : ℝ)) ≤ (9 / 4 : ℝ) / Real.sqrt (L : ℝ) := by
      rw [div_div]
      exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
    have hsqrt3 : Real.sqrt 3 ≤ 7 / 4 := by
      rw [Real.sqrt_le_left (by norm_num)]
      norm_num
    have hconst_le : 9 / (4 * (L : ℝ)) + Real.sqrt 3 / Real.sqrt (L : ℝ) ≤ 4 / Real.sqrt (L : ℝ) := by
      calc 9 / (4 * (L : ℝ)) + Real.sqrt 3 / Real.sqrt (L : ℝ)
          ≤ (9 / 4 : ℝ) / Real.sqrt (L : ℝ) + (7 / 4 : ℝ) / Real.sqrt (L : ℝ) :=
            add_le_add hinv_le (div_le_div_of_nonneg_right hsqrt3 (le_of_lt hsqrt_pos))
        _ = 4 / Real.sqrt (L : ℝ) := by ring
    calc ({v : Fin L → Fin (M + 1) | ∑ i : Fin L, ((v i).1 : ℤ) = t}.ncard : ℝ)
        ≤ (Ebad.ncard : ℝ) + (Egood.ncard : ℝ) := hunion
      _ ≤ (9 / (4 * (L : ℝ))) * ((M + 1 : ℕ) : ℝ) ^ L +
          (Real.sqrt 3 / Real.sqrt (L : ℝ)) * ((M + 1 : ℕ) : ℝ) ^ L := add_le_add hbad_le hgood_le
      _ = (9 / (4 * (L : ℝ)) + Real.sqrt 3 / Real.sqrt (L : ℝ)) * ((M + 1 : ℕ) : ℝ) ^ L := by ring
      _ ≤ (4 / Real.sqrt (L : ℝ)) * ((M + 1 : ℕ) : ℝ) ^ L :=
          mul_le_mul_of_nonneg_right hconst_le (by positivity)

private lemma X_pow_sub_X_pow_mod_dvd (m j : ℕ) :
    (X ^ m - 1 : ℤ[X]) ∣ X ^ j - X ^ (j % m) := by
  have hdiv : j = j % m + m * (j / m) := by
    have := Nat.div_add_mod j m
    omega
  conv_lhs => skip
  have hfac : (X ^ j - X ^ (j % m) : ℤ[X]) = X ^ (j % m) * ((X ^ m) ^ (j / m) - 1 ^ (j / m)) := by
    rw [one_pow, mul_sub, mul_one, ← pow_mul, ← pow_add, ← hdiv]
  rw [hfac]
  exact dvd_mul_of_dvd_right (sub_dvd_pow_sub_pow (X ^ m : ℤ[X]) 1 (j / m)) _

private lemma cyclotomic_dvd_X_pow_sub_one {m : ℕ} (hm : 1 ≤ m) :
    Polynomial.cyclotomic m ℤ ∣ X ^ m - 1 := by
  rw [← Polynomial.prod_cyclotomic_eq_X_pow_sub_one (by omega : 0 < m) ℤ]
  exact Finset.dvd_prod_of_mem _ (Nat.mem_divisors_self m (by omega))

private lemma cyclotomic_dvd_card_le (M n m : ℕ) (hM : 1 ≤ M) (hm : 2 ≤ m) (hmn : m ≤ n) :
    ({a : Fin n → Fin (M + 1) |
      Polynomial.cyclotomic m ℤ ∣ Green93.monicPoly fun j ↦ (a j : ℕ)}.ncard : ℝ) ≤
      (4 / Real.sqrt ((n / m : ℕ) : ℝ)) ^ (Nat.totient m) * ((M + 1 : ℕ) : ℝ) ^ n := by
  let Φ : ℤ[X] := Polynomial.cyclotomic m ℤ
  let d : ℕ := Nat.totient m
  have hΦ_monic : Φ.Monic := Polynomial.cyclotomic.monic m ℤ
  have hΦ_deg : Φ.natDegree = d := Polynomial.natDegree_cyclotomic m ℤ
  have hd_pos : 1 ≤ d := Nat.totient_pos.mpr (by omega)
  have hd_lt : d < m := Nat.totient_lt m (by omega)
  have hΦ_dvd_Xm : Φ ∣ X ^ m - 1 := cyclotomic_dvd_X_pow_sub_one (by omega)
  let B_rest := {j : Fin n // d ≤ j.1 % m}
  let B_mod : Fin d → Type := fun r => {j : Fin n // j.1 % m = r.1}
  let splitEquiv : (Fin n → Fin (M + 1)) ≃
      (B_rest → Fin (M + 1)) × (∀ r : Fin d, B_mod r → Fin (M + 1)) :=
    { toFun := fun a => (fun j => a j.1, fun r j => a j.1)
      invFun := fun ⟨a_rest, a_mod⟩ j =>
        if h : d ≤ j.1 % m then a_rest ⟨j, h⟩
        else a_mod ⟨j.1 % m, by omega⟩ ⟨j, rfl⟩
      left_inv := by
        intro a
        ext j
        by_cases h : d ≤ j.1 % m <;> simp [h]
      right_inv := by
        rintro ⟨a_rest, a_mod⟩
        refine Prod.ext (funext fun j => by dsimp only; rw [dif_pos j.2])
          (funext fun r => funext fun j => ?_)
        rcases r with ⟨rv, hrlt⟩
        rcases j with ⟨j0, hj0⟩
        dsimp only at hj0 ⊢
        have hnot : ¬ d ≤ j0.1 % m := by omega
        rw [dif_neg hnot]
        subst hj0
        rfl }
  let P_hi_of : (B_rest → Fin (M + 1)) → ℤ[X] := fun a_rest =>
    ∑ r ∈ Finset.Ico d m,
      C ((∑ j ∈ Finset.univ.filter (fun j : B_rest => j.1.1 % m = r), ((a_rest j).1 : ℤ)) +
        (if n % m = r then (1 : ℤ) else 0)) * X ^ r
  let target_of : (B_rest → Fin (M + 1)) → Fin d → ℤ := fun a_rest r =>
    -((P_hi_of a_rest %ₘ Φ).coeff r.1) - (if n % m = r.1 then (1 : ℤ) else 0)
  have hdvd_imp : ∀ a : Fin n → Fin (M + 1),
      Φ ∣ Green93.monicPoly (fun j ↦ (a j : ℕ)) →
      ∀ r : Fin d,
        ∑ j : B_mod r, ((a j.1).1 : ℤ) = target_of (splitEquiv a).1 r := by
    intro a hdvd
    let S_sum : ℕ → ℤ := fun r =>
      (∑ j ∈ Finset.univ.filter (fun j : Fin n => j.1 % m = r), ((a j).1 : ℤ)) +
        (if n % m = r then (1 : ℤ) else 0)
    let P_lo : ℤ[X] := ∑ r ∈ Finset.range d, C (S_sum r) * X ^ r
    let P_hi : ℤ[X] := ∑ r ∈ Finset.Ico d m, C (S_sum r) * X ^ r
    have hP_hi_eq : P_hi = P_hi_of (splitEquiv a).1 := by
      dsimp only [P_hi, P_hi_of, S_sum, splitEquiv]
      refine Finset.sum_congr rfl fun r hr => ?_
      have hrd : d ≤ r := (Finset.mem_Ico.mp hr).1
      refine congrArg (fun c => C (c + if n % m = r then (1 : ℤ) else 0) * X ^ r) ?_
      symm
      refine Finset.sum_nbij (fun j : B_rest => j.1) ?_ ?_ ?_ ?_
      · intro j hj
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2⟩
      · intro j₁ _ j₂ _ heq
        exact Subtype.ext heq
      · intro j hj
        have hjr : j.1 % m = r := (Finset.mem_filter.mp (Finset.mem_coe.mp hj)).2
        refine ⟨⟨j, by omega⟩, Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjr⟩), rfl⟩
      · intro _ _; rfl
    have hcong : Φ ∣ Green93.monicPoly (fun j ↦ (a j : ℕ)) - (P_lo + P_hi) := by
      have hP_tot : P_lo + P_hi = ∑ r ∈ Finset.range m, C (S_sum r) * X ^ r := by
        dsimp only [P_lo, P_hi]
        have hunion : Finset.range m = Finset.range d ∪ Finset.Ico d m := by
          ext r; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
        have hdisj : Disjoint (Finset.range d) (Finset.Ico d m) := by
          rw [Finset.disjoint_left]; intro r h1 h2
          simp only [Finset.mem_range, Finset.mem_Ico] at h1 h2; omega
        rw [hunion, Finset.sum_union hdisj]
      have hdecomp : P_lo + P_hi =
          X ^ (n % m) + ∑ j : Fin n, C ((a j).1 : ℤ) * X ^ (j.1 % m) := by
        rw [hP_tot]
        have hterm1 : ∑ r ∈ Finset.range m, C (if n % m = r then (1 : ℤ) else 0) * X ^ r =
            X ^ (n % m) := by
          rw [Finset.sum_eq_single (n % m)]
          · simp
          · intro r _ hne; simp [Ne.symm hne]
          · intro hnot; exact False.elim (hnot (Finset.mem_range.mpr (Nat.mod_lt n (by omega))))
        have hterm2 : ∑ r ∈ Finset.range m,
            C (∑ j ∈ Finset.univ.filter (fun j : Fin n => j.1 % m = r), ((a j).1 : ℤ)) * X ^ r =
            ∑ j : Fin n, C ((a j).1 : ℤ) * X ^ (j.1 % m) := by
          have hfiber := Finset.sum_fiberwise_of_maps_to
            (s := (Finset.univ : Finset (Fin n))) (t := Finset.range m)
            (g := fun j : Fin n => j.1 % m)
            (fun j _ => Finset.mem_range.mpr (Nat.mod_lt j.1 (by omega)))
            (fun j => C ((a j).1 : ℤ) * X ^ (j.1 % m))
          rw [← hfiber]
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [map_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun j hj => ?_
          rw [(Finset.mem_filter.mp hj).2]
        have hsum_add : ∑ r ∈ Finset.range m, C (S_sum r) * X ^ r =
            (∑ r ∈ Finset.range m,
              C (∑ j ∈ Finset.univ.filter (fun j : Fin n => j.1 % m = r), ((a j).1 : ℤ)) * X ^ r) +
            (∑ r ∈ Finset.range m, C (if n % m = r then (1 : ℤ) else 0) * X ^ r) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun r _ => ?_
          dsimp only [S_sum]
          rw [map_add, add_mul]
        rw [hsum_add, hterm1, hterm2, add_comm]
      rw [hdecomp]
      unfold Green93.monicPoly
      have hdiff_eq : (X ^ n + ∑ j : Fin n, C ((a j).1 : ℤ) * X ^ j.1) -
          (X ^ (n % m) + ∑ j : Fin n, C ((a j).1 : ℤ) * X ^ (j.1 % m)) =
          (X ^ n - X ^ (n % m)) +
            ∑ j : Fin n, C ((a j).1 : ℤ) * (X ^ j.1 - X ^ (j.1 % m)) := by
        have hsub : (∑ j : Fin n, C ((a j).1 : ℤ) * X ^ j.1) -
            (∑ j : Fin n, C ((a j).1 : ℤ) * X ^ (j.1 % m)) =
            ∑ j : Fin n, C ((a j).1 : ℤ) * (X ^ j.1 - X ^ (j.1 % m)) := by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
        rw [← hsub]
        abel
      rw [hdiff_eq]
      refine dvd_add (dvd_trans hΦ_dvd_Xm (X_pow_sub_X_pow_mod_dvd m n)) ?_
      refine Finset.dvd_sum fun j _ => ?_
      exact dvd_mul_of_dvd_right (dvd_trans hΦ_dvd_Xm (X_pow_sub_X_pow_mod_dvd m j.1)) _
    have hΦ_dvd_sum : Φ ∣ P_lo + P_hi := by
      have hsub := dvd_sub hdvd hcong
      simpa using hsub
    have hΦ_dvd_rem : Φ ∣ P_lo - (-(P_hi %ₘ Φ)) := by
      have hrem : P_hi - P_hi %ₘ Φ = Φ * (P_hi /ₘ Φ) := by
        have := Polynomial.modByMonic_add_div P_hi Φ
        linear_combination -this
      have h1 : Φ ∣ P_hi - P_hi %ₘ Φ := ⟨P_hi /ₘ Φ, hrem⟩
      have h2 := dvd_sub hΦ_dvd_sum h1
      convert h2 using 1
      ring
    have hPlo_deg : P_lo.degree < Φ.degree := by
      have hΦ_deg_eq : Φ.degree = (d : WithBot ℕ) := by
        rw [degree_eq_natDegree hΦ_monic.ne_zero, hΦ_deg]
      rw [hΦ_deg_eq]
      refine lt_of_le_of_lt (degree_sum_le _ _) ?_
      refine (Finset.sup_lt_iff (WithBot.bot_lt_coe d)).mpr fun r hr => ?_
      have hrd : r < d := Finset.mem_range.mp hr
      calc (C (S_sum r) * X ^ r).degree
          ≤ (C (S_sum r)).degree + (X ^ r).degree := degree_mul_le _ _
        _ ≤ 0 + (r : WithBot ℕ) := add_le_add degree_C_le (by rw [degree_X_pow])
        _ = (r : WithBot ℕ) := zero_add _
        _ < (d : WithBot ℕ) := WithBot.coe_lt_coe.mpr hrd
    have hrem_deg : (-(P_hi %ₘ Φ)).degree < Φ.degree := by
      rw [degree_neg]
      exact Polynomial.degree_modByMonic_lt P_hi hΦ_monic
    have hdiff_deg : (P_lo - (-(P_hi %ₘ Φ))).degree < Φ.degree :=
      lt_of_le_of_lt (degree_sub_le _ _) (max_lt hPlo_deg hrem_deg)
    have hPlo_eq : P_lo = -(P_hi %ₘ Φ) := by
      have hmod0 : (P_lo - (-(P_hi %ₘ Φ))) %ₘ Φ = 0 :=
        (Polynomial.modByMonic_eq_zero_iff_dvd hΦ_monic).mpr hΦ_dvd_rem
      have hmodself : (P_lo - (-(P_hi %ₘ Φ))) %ₘ Φ = P_lo - (-(P_hi %ₘ Φ)) :=
        (Polynomial.modByMonic_eq_self_iff hΦ_monic).mpr hdiff_deg
      have h0 : P_lo - (-(P_hi %ₘ Φ)) = 0 := hmodself.symm.trans hmod0
      exact sub_eq_zero.mp h0
    intro r
    have hcoeff_lo : P_lo.coeff r.1 = S_sum r.1 := by
      dsimp only [P_lo]
      rw [finsetSum_coeff, Finset.sum_eq_single r.1]
      · simp
      · intro k _ hne; rw [coeff_C_mul_X_pow, if_neg (Ne.symm hne)]
      · intro hnot; exact False.elim (hnot (Finset.mem_range.mpr r.2))
    have hcoeff_eq : S_sum r.1 = -((P_hi_of (splitEquiv a).1 %ₘ Φ).coeff r.1) := by
      rw [← hcoeff_lo, hPlo_eq, coeff_neg, hP_hi_eq]
    have hsum_mod : ∑ j : B_mod r, ((a j.1).1 : ℤ) =
        ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.1 % m = r.1), ((a j).1 : ℤ) := by
      refine Finset.sum_nbij (fun j : B_mod r => j.1) ?_ ?_ ?_ ?_
      · intro j _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, j.2⟩
      · intro j₁ _ j₂ _ heq; exact Subtype.ext heq
      · intro j hj
        have hjr := (Finset.mem_filter.mp (Finset.mem_coe.mp hj)).2
        exact ⟨⟨j, hjr⟩, Finset.mem_coe.mpr (Finset.mem_univ _), rfl⟩
      · intro _ _; rfl
    rw [hsum_mod]
    dsimp only [S_sum, target_of] at hcoeff_eq ⊢
    linarith
  have hB_ge : ∀ r : Fin d, n / m ≤ Fintype.card (B_mod r) := by
    intro r
    let ι : Fin (n / m) → B_mod r := fun q =>
      ⟨⟨q.1 * m + r.1, by
        have hq : q.1 + 1 ≤ n / m := q.2
        have hr : r.1 < m := lt_trans r.2 hd_lt
        have hmul : (q.1 + 1) * m ≤ (n / m) * m := Nat.mul_le_mul_right m hq
        have hle : (n / m) * m ≤ n := Nat.div_mul_le_self n m
        calc q.1 * m + r.1 < q.1 * m + m := Nat.add_lt_add_left hr _
          _ = (q.1 + 1) * m := by ring
          _ ≤ n := le_trans hmul hle⟩, by
        simp only [Nat.mul_add_mod_self_right]
        exact Nat.mod_eq_of_lt (lt_trans r.2 hd_lt)⟩
    have hι_inj : Function.Injective ι := by
      intro q₁ q₂ h
      have hval : q₁.1 * m + r.1 = q₂.1 * m + r.1 := congrArg (fun x => x.1.1) h
      have hmul : q₁.1 * m = q₂.1 * m := Nat.add_right_cancel hval
      exact Fin.ext (Nat.eq_of_mul_eq_mul_right (by omega : 0 < m) hmul)
    calc n / m = Fintype.card (Fin (n / m)) := (Fintype.card_fin _).symm
      _ ≤ Fintype.card (B_mod r) := Fintype.card_le_of_injective ι hι_inj
  have hcard_sum_eq : Fintype.card B_rest + ∑ r : Fin d, Fintype.card (B_mod r) = n := by
    let e_idx : Fin n ≃ Sum B_rest (Σ r : Fin d, B_mod r) :=
      { toFun := fun j => if h : d ≤ j.1 % m then Sum.inl ⟨j, h⟩
                          else Sum.inr ⟨⟨j.1 % m, by omega⟩, ⟨j, rfl⟩⟩
        invFun := fun x => match x with
          | Sum.inl j => j.1
          | Sum.inr ⟨_, j⟩ => j.1
        left_inv := fun j => by by_cases h : d ≤ j.1 % m <;> simp [h]
        right_inv := by
          rintro (j | ⟨⟨rv, hrlt⟩, ⟨j0, hj0⟩⟩)
          · simp [j.2]
          · dsimp only at hj0 ⊢
            have hnot : ¬ d ≤ j0.1 % m := by omega
            rw [dif_neg hnot]
            subst hj0
            rfl }
    have h := Fintype.card_congr e_idx
    rw [Fintype.card_fin, Fintype.card_sum, Fintype.card_sigma] at h
    exact h.symm
  let Target : Set ((B_rest → Fin (M + 1)) × (∀ r : Fin d, B_mod r → Fin (M + 1))) :=
    {p | ∀ r : Fin d, ∑ j : B_mod r, ((p.2 r j).1 : ℤ) = target_of p.1 r}
  have hcard_le_target :
      {a : Fin n → Fin (M + 1) | Φ ∣ Green93.monicPoly fun j ↦ (a j : ℕ)}.ncard ≤ Target.ncard := by
    classical
    let S := {a : Fin n → Fin (M + 1) | Φ ∣ Green93.monicPoly fun j ↦ (a j : ℕ)}
    let ψ : S → Target := fun ⟨a, ha⟩ => ⟨splitEquiv a, hdvd_imp a ha⟩
    have hψ_inj : Function.Injective ψ := by
      rintro ⟨a₁, _⟩ ⟨a₂, _⟩ h
      exact Subtype.ext (splitEquiv.injective (congrArg Subtype.val h))
    rw [Set.ncard_eq_toFinset_card', Set.ncard_eq_toFinset_card']
    have h1 : S.toFinset.card = Fintype.card S := by
      rw [← Fintype.card_coe]
      refine Fintype.card_congr ?_
      exact
        { toFun := fun ⟨x, hx⟩ => ⟨x, Set.mem_toFinset.mp hx⟩
          invFun := fun ⟨x, hx⟩ => ⟨x, Set.mem_toFinset.mpr hx⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    have h2 : Target.toFinset.card = Fintype.card Target := by
      rw [← Fintype.card_coe]
      refine Fintype.card_congr ?_
      exact
        { toFun := fun ⟨x, hx⟩ => ⟨x, Set.mem_toFinset.mp hx⟩
          invFun := fun ⟨x, hx⟩ => ⟨x, Set.mem_toFinset.mpr hx⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    rw [h1, h2]
    exact Fintype.card_le_of_injective ψ hψ_inj
  have hTarget_card : (Target.ncard : ℝ) ≤
      (4 / Real.sqrt ((n / m : ℕ) : ℝ)) ^ d * ((M + 1 : ℕ) : ℝ) ^ n := by
    have hfiber_nat : Target.ncard =
        ∑ a_rest : B_rest → Fin (M + 1),
          ∏ r : Fin d,
            {w : B_mod r → Fin (M + 1) |
              ∑ j : B_mod r, ((w j).1 : ℤ) = target_of a_rest r}.ncard := by
      classical
      rw [Set.ncard_eq_toFinset_card']
      rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst)
        (t := (Finset.univ : Finset (B_rest → Fin (M + 1)))) (fun _ _ => Finset.mem_univ _)]
      refine Finset.sum_congr rfl fun a_rest _ => ?_
      let F_r : ∀ r : Fin d, Set (B_mod r → Fin (M + 1)) := fun r =>
        {w : B_mod r → Fin (M + 1) | ∑ j : B_mod r, ((w j).1 : ℤ) = target_of a_rest r}
      let T_fib := Target.toFinset.filter (fun p => p.1 = a_rest)
      let e_fib : T_fib ≃ ∀ r : Fin d, F_r r :=
        { toFun := fun ⟨p, hp⟩ r =>
            ⟨p.2 r, by
              have hmem := Finset.mem_filter.mp hp
              have hT : ∀ r' : Fin d, ∑ j : B_mod r', ((p.2 r' j).1 : ℤ) = target_of p.1 r' :=
                Set.mem_toFinset.mp hmem.1
              rw [hmem.2] at hT
              exact hT r⟩
          invFun := fun w =>
            ⟨(a_rest, fun r => (w r).1),
             Finset.mem_filter.mpr ⟨Set.mem_toFinset.mpr (fun r => (w r).2), rfl⟩⟩
          left_inv := by
            rintro ⟨⟨p1, p2⟩, hp⟩
            have hp1 : p1 = a_rest := (Finset.mem_filter.mp hp).2
            subst hp1
            rfl
          right_inv := fun _ => rfl }
      have h1 : T_fib.card = Fintype.card T_fib := (Fintype.card_coe T_fib).symm
      change T_fib.card = _
      rw [h1, Fintype.card_congr e_fib, Fintype.card_pi]
      refine Finset.prod_congr rfl fun r _ => ?_
      rw [Set.ncard_eq_toFinset_card']
      rw [← Fintype.card_coe]
      refine Fintype.card_congr ?_
      exact
        { toFun := fun ⟨x, hx⟩ => ⟨x, Set.mem_toFinset.mpr hx⟩
          invFun := fun ⟨x, hx⟩ => ⟨x, Set.mem_toFinset.mp hx⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    have hslice_r : ∀ (a_rest : B_rest → Fin (M + 1)) (r : Fin d),
        ({w : B_mod r → Fin (M + 1) |
          ∑ j : B_mod r, ((w j).1 : ℤ) = target_of a_rest r}.ncard : ℝ) ≤
          (4 / Real.sqrt ((n / m : ℕ) : ℝ)) * ((M + 1 : ℕ) : ℝ) ^ Fintype.card (B_mod r) := by
      intro a_rest r
      let eB : B_mod r ≃ Fin (Fintype.card (B_mod r)) := Fintype.equivFin (B_mod r)
      have hcard_eq : {w : B_mod r → Fin (M + 1) |
          ∑ j : B_mod r, ((w j).1 : ℤ) = target_of a_rest r}.ncard =
          {v : Fin (Fintype.card (B_mod r)) → Fin (M + 1) |
            ∑ i : Fin (Fintype.card (B_mod r)), ((v i).1 : ℤ) = target_of a_rest r}.ncard := by
        let S1 := {w : B_mod r → Fin (M + 1) | ∑ j : B_mod r, ((w j).1 : ℤ) = target_of a_rest r}
        let S2 := {v : Fin (Fintype.card (B_mod r)) → Fin (M + 1) |
          ∑ i : Fin (Fintype.card (B_mod r)), ((v i).1 : ℤ) = target_of a_rest r}
        let eS : S1 ≃ S2 :=
          { toFun := fun ⟨w, hw⟩ =>
              ⟨fun i => w (eB.symm i), by
                rw [Set.mem_ofPred_eq, ← hw]
                exact Fintype.sum_equiv eB.symm _ _ (fun _ => rfl)⟩
            invFun := fun ⟨v, hv⟩ =>
              ⟨fun j => v (eB j), by
                rw [Set.mem_ofPred_eq, ← hv]
                exact Fintype.sum_equiv eB _ _ (fun _ => rfl)⟩
            left_inv := fun ⟨w, _⟩ => by apply Subtype.ext; ext j; simp
            right_inv := fun ⟨v, _⟩ => by apply Subtype.ext; ext i; simp }
        rw [Set.ncard_eq_toFinset_card', Set.ncard_eq_toFinset_card']
        have h1 : S1.toFinset.card = Fintype.card S1 := by
          rw [← Fintype.card_coe]
          refine Fintype.card_congr ?_
          exact
            { toFun := fun ⟨x, hx⟩ => ⟨x, Set.mem_toFinset.mp hx⟩
              invFun := fun ⟨x, hx⟩ => ⟨x, Set.mem_toFinset.mpr hx⟩
              left_inv := fun _ => rfl
              right_inv := fun _ => rfl }
        have h2 : S2.toFinset.card = Fintype.card S2 := by
          rw [← Fintype.card_coe]
          refine Fintype.card_congr ?_
          exact
            { toFun := fun ⟨x, hx⟩ => ⟨x, Set.mem_toFinset.mp hx⟩
              invFun := fun ⟨x, hx⟩ => ⟨x, Set.mem_toFinset.mpr hx⟩
              left_inv := fun _ => rfl
              right_inv := fun _ => rfl }
        rw [h1, h2]
        exact Fintype.card_congr eS
      rw [hcard_eq]
      have hnm1 : 1 ≤ n / m := Nat.div_pos hmn (by omega)
      have hBr1 : 1 ≤ Fintype.card (B_mod r) := le_trans hnm1 (hB_ge r)
      have hle := slice_card_le M (Fintype.card (B_mod r)) hM hBr1 (target_of a_rest r)
      have hsqrt_le : Real.sqrt ((n / m : ℕ) : ℝ) ≤ Real.sqrt ((Fintype.card (B_mod r) : ℕ) : ℝ) :=
        Real.sqrt_le_sqrt (by exact_mod_cast hB_ge r)
      have hsqrt_pos : 0 < Real.sqrt ((n / m : ℕ) : ℝ) :=
        Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n / m))
      have hdiv_le : 4 / Real.sqrt ((Fintype.card (B_mod r) : ℕ) : ℝ) ≤
          4 / Real.sqrt ((n / m : ℕ) : ℝ) :=
        div_le_div_of_nonneg_left (by norm_num) hsqrt_pos hsqrt_le
      exact le_trans hle (mul_le_mul_of_nonneg_right hdiv_le (by positivity))
    rw [hfiber_nat]
    push_cast
    calc ∑ a_rest : B_rest → Fin (M + 1),
          ∏ r : Fin d,
            ({w : B_mod r → Fin (M + 1) |
              ∑ j : B_mod r, ((w j).1 : ℤ) = target_of a_rest r}.ncard : ℝ)
        ≤ ∑ _a_rest : B_rest → Fin (M + 1),
          ∏ r : Fin d,
            ((4 / Real.sqrt ((n / m : ℕ) : ℝ)) * ((M + 1 : ℕ) : ℝ) ^ Fintype.card (B_mod r)) := by
          refine Finset.sum_le_sum fun a_rest _ => ?_
          refine Finset.prod_le_prod (fun _ _ => by positivity) fun r _ => hslice_r a_rest r
      _ = ((M + 1 : ℕ) : ℝ) ^ Fintype.card B_rest *
          ((4 / Real.sqrt ((n / m : ℕ) : ℝ)) ^ d *
            ((M + 1 : ℕ) : ℝ) ^ (∑ r : Fin d, Fintype.card (B_mod r))) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul,
            Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
            Finset.prod_pow_eq_pow_sum]
          push_cast
          rfl
      _ = (4 / Real.sqrt ((n / m : ℕ) : ℝ)) ^ d * ((M + 1 : ℕ) : ℝ) ^ n := by
          rw [← mul_assoc, mul_comm (((M + 1 : ℕ) : ℝ) ^ Fintype.card B_rest), mul_assoc,
            ← pow_add, hcard_sum_eq]
      _ = (4 / Real.sqrt ((n / m : ℕ) : ℝ)) ^ d * ((M : ℝ) + 1) ^ n := by
          push_cast
          rfl
  exact le_trans (by exact_mod_cast hcard_le_target) hTarget_card

private lemma eighth_root_bounds (n : ℕ) :
    let u := Nat.sqrt (Nat.sqrt (Nat.sqrt n))
    u ^ 8 ≤ n ∧ n < (u + 1) ^ 8 := by
  let a := Nat.sqrt n
  let b := Nat.sqrt a
  let u := Nat.sqrt b
  have hu1 : u * u ≤ b := Nat.sqrt_le b
  have hu2 : b < (u + 1) * (u + 1) := Nat.lt_succ_sqrt b
  have hb1 : b * b ≤ a := Nat.sqrt_le a
  have hb2 : a < (b + 1) * (b + 1) := Nat.lt_succ_sqrt a
  have ha1 : a * a ≤ n := Nat.sqrt_le n
  have ha2 : n < (a + 1) * (a + 1) := Nat.lt_succ_sqrt n
  have h1 : u ^ 4 ≤ a := by
    calc u ^ 4 = (u * u) * (u * u) := by ring
      _ ≤ b * b := Nat.mul_le_mul hu1 hu1
      _ ≤ a := hb1
  have h2 : a < (u + 1) ^ 4 := by
    have hb_le : b + 1 ≤ (u + 1) * (u + 1) := hu2
    calc a < (b + 1) * (b + 1) := hb2
      _ ≤ ((u + 1) * (u + 1)) * ((u + 1) * (u + 1)) := Nat.mul_le_mul hb_le hb_le
      _ = (u + 1) ^ 4 := by ring
  refine ⟨?_, ?_⟩
  · calc u ^ 8 = u ^ 4 * u ^ 4 := by ring
      _ ≤ a * a := Nat.mul_le_mul h1 h1
      _ ≤ n := ha1
  · have ha_le : a + 1 ≤ (u + 1) ^ 4 := h2
    calc n < (a + 1) * (a + 1) := ha2
      _ ≤ (u + 1) ^ 4 * (u + 1) ^ 4 := Nat.mul_le_mul ha_le ha_le
      _ = (u + 1) ^ 8 := by ring

private lemma cyclotomic_divisors_small (M : ℕ) (hM : 1 ≤ M) (ε : ℝ) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      (({a : Fin n → Fin (M + 1) |
          (Green93.monicPoly fun j ↦ (a j : ℕ)).coeff 0 ≠ 0 ∧
          ∃ m : ℕ, 1 ≤ m ∧ (Nat.totient m) ^ 2 ≤ n ∧
            Polynomial.cyclotomic m ℤ ∣ Green93.monicPoly fun j ↦ (a j : ℕ)}.ncard : ℝ) ≤
        ε * ((M * (M + 1) ^ (n - 1) : ℕ) : ℝ)) := by
  let C : ℝ := 2 * (120 + 6 * (16 : ℝ) ^ 7)
  let u₀ : ℕ := max 20 (Nat.ceil (C / ε) + 1)
  refine ⟨u₀ ^ 8, fun n hn => ?_⟩
  have hu₀20 : 20 ≤ u₀ := le_max_left _ _
  have hn1 : 1 ≤ n := by
    have : 1 ≤ u₀ ^ 8 := one_le_pow₀ (by omega)
    omega
  let u : ℕ := Nat.sqrt (Nat.sqrt (Nat.sqrt n))
  have hub := eighth_root_bounds n
  have hub1 : u ^ 8 ≤ n := hub.1
  have hub2 : n < (u + 1) ^ 8 := hub.2
  have hu_ge : u₀ ≤ u := by
    by_contra hlt
    have hle : u + 1 ≤ u₀ := by omega
    have hpow : (u + 1) ^ 8 ≤ u₀ ^ 8 := Nat.pow_le_pow_left hle 8
    omega
  have hu20 : 20 ≤ u := le_trans hu₀20 hu_ge
  have hu1_6 : (u + 1) ^ 6 ≤ 2 * u ^ 6 := by
    have hZ : ((u : ℤ) + 1) ^ 6 ≤ 2 * (u : ℤ) ^ 6 := by
      have hu20Z : (20 : ℤ) ≤ (u : ℤ) := by exact_mod_cast hu20
      have h1 : ((u : ℤ) + 1) ^ 6 = (u : ℤ) ^ 6 + 6 * (u : ℤ) ^ 5 + 15 * (u : ℤ) ^ 4 +
          20 * (u : ℤ) ^ 3 + 15 * (u : ℤ) ^ 2 + 6 * (u : ℤ) + 1 := by ring
      have hp1 : 20 * (u : ℤ) ^ 5 ≤ (u : ℤ) ^ 6 := by nlinarith [pow_nonneg (by omega : (0 : ℤ) ≤ u) 5]
      have hp2 : 400 * (u : ℤ) ^ 4 ≤ (u : ℤ) ^ 6 := by nlinarith [pow_nonneg (by omega : (0 : ℤ) ≤ u) 4]
      have hp3 : 8000 * (u : ℤ) ^ 3 ≤ (u : ℤ) ^ 6 := by nlinarith [pow_nonneg (by omega : (0 : ℤ) ≤ u) 3]
      have hp4 : 160000 * (u : ℤ) ^ 2 ≤ (u : ℤ) ^ 6 := by nlinarith [pow_nonneg (by omega : (0 : ℤ) ≤ u) 2]
      have hp5 : 3200000 * (u : ℤ) ≤ (u : ℤ) ^ 6 := by nlinarith
      have hp6 : (64000000 : ℤ) ≤ (u : ℤ) ^ 6 := by nlinarith
      nlinarith
    exact_mod_cast hZ
  have hm_lt : ∀ m : ℕ, 1 ≤ m → (Nat.totient m) ^ 2 ≤ n → m < 6 * u ^ 6 := by
    intro m hm hφn
    have htot := two_mul_sq_le_nine_mul_totient_cube m hm
    have h4 : 4 * m ^ 4 ≤ 81 * n ^ 3 := by
      calc 4 * m ^ 4 = (2 * m ^ 2) ^ 2 := by ring
        _ ≤ (9 * (Nat.totient m) ^ 3) ^ 2 := Nat.pow_le_pow_left htot 2
        _ = 81 * ((Nat.totient m) ^ 2) ^ 3 := by ring
        _ ≤ 81 * n ^ 3 := Nat.mul_le_mul_left 81 (Nat.pow_le_pow_left hφn 3)
    have hlt3 : n ^ 3 < ((u + 1) ^ 8) ^ 3 := Nat.pow_lt_pow_left hub.2 (by omega)
    have h4lt : 4 * m ^ 4 < 4 * (3 * (u + 1) ^ 6) ^ 4 := by
      calc 4 * m ^ 4 ≤ 81 * n ^ 3 := h4
        _ < 81 * ((u + 1) ^ 8) ^ 3 := Nat.mul_lt_mul_of_pos_left hlt3 (by omega)
        _ = 81 * (u + 1) ^ 24 := by rw [← pow_mul]
        _ < 324 * (u + 1) ^ 24 := Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)
        _ = 4 * (3 * (u + 1) ^ 6) ^ 4 := by ring
    have hmlt3 : m < 3 * (u + 1) ^ 6 := by
      by_contra hge
      have hpow : (3 * (u + 1) ^ 6) ^ 4 ≤ m ^ 4 := Nat.pow_le_pow_left (by omega) 4
      omega
    omega
  let SmallM : Finset ℕ := (Finset.Icc 2 31).filter (fun m => (Nat.totient m) ^ 2 ≤ n)
  let LargeM : Finset ℕ := (Finset.Icc 2 (6 * u ^ 6)).filter
    (fun m => 7 ≤ Nat.totient m ∧ (Nat.totient m) ^ 2 ≤ n)
  have hsub : {a : Fin n → Fin (M + 1) |
      (Green93.monicPoly fun j ↦ (a j : ℕ)).coeff 0 ≠ 0 ∧
      ∃ m : ℕ, 1 ≤ m ∧ (Nat.totient m) ^ 2 ≤ n ∧
        Polynomial.cyclotomic m ℤ ∣ Green93.monicPoly fun j ↦ (a j : ℕ)} ⊆
      (⋃ m ∈ SmallM, {a : Fin n → Fin (M + 1) |
          Polynomial.cyclotomic m ℤ ∣ Green93.monicPoly fun j ↦ (a j : ℕ)}) ∪
      (⋃ m ∈ LargeM, {a : Fin n → Fin (M + 1) |
          Polynomial.cyclotomic m ℤ ∣ Green93.monicPoly fun j ↦ (a j : ℕ)}) := by
    intro a ⟨_, m, hm1, hφn, hdvd⟩
    have hm2 : 2 ≤ m := by
      by_contra hlt
      have hm_eq : m = 1 := by omega
      rw [hm_eq] at hdvd
      exact cyclotomic_one_not_dvd_monicPoly _ hdvd
    by_cases hφ7 : 7 ≤ Nat.totient m
    · refine Or.inr (Set.mem_iUnion₂.mpr ⟨m, ?_, hdvd⟩)
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hm2, le_of_lt (hm_lt m hm1 hφn)⟩, hφ7, hφn⟩
    · refine Or.inl (Set.mem_iUnion₂.mpr ⟨m, ?_, hdvd⟩)
      have hφ6 : Nat.totient m ≤ 6 := by omega
      have htot := two_mul_sq_le_nine_mul_totient_cube m hm1
      have h2m : 2 * m ^ 2 ≤ 9 * 6 ^ 3 := le_trans htot (Nat.mul_le_mul_left 9 (Nat.pow_le_pow_left hφ6 3))
      have hm31 : m ≤ 31 := by nlinarith
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hm2, hm31⟩, hφn⟩
  have hSmall_bound :
      ((⋃ m ∈ SmallM, {a : Fin n → Fin (M + 1) |
          Polynomial.cyclotomic m ℤ ∣ Green93.monicPoly fun j ↦ (a j : ℕ)}).ncard : ℝ) ≤
        (120 / (u : ℝ)) * ((M + 1 : ℕ) : ℝ) ^ n := by
    have hnc := ncard_biUnion_finset_le SmallM (fun m =>
      {a : Fin n → Fin (M + 1) | Polynomial.cyclotomic m ℤ ∣ Green93.monicPoly fun j ↦ (a j : ℕ)})
    calc ((⋃ m ∈ SmallM, _).ncard : ℝ)
        ≤ ∑ m ∈ SmallM, ({a : Fin n → Fin (M + 1) |
            Polynomial.cyclotomic m ℤ ∣ Green93.monicPoly fun j ↦ (a j : ℕ)}.ncard : ℝ) := by
          exact_mod_cast hnc
      _ ≤ ∑ _m ∈ SmallM, ((4 / (u : ℝ)) * ((M + 1 : ℕ) : ℝ) ^ n) := by
          refine Finset.sum_le_sum fun m hm => ?_
          have hmIcc := (Finset.mem_filter.mp hm).1
          have hm2 : 2 ≤ m := (Finset.mem_Icc.mp hmIcc).1
          have hm31 : m ≤ 31 := (Finset.mem_Icc.mp hmIcc).2
          have hu2_le : u ^ 2 ≤ n / m := by
            refine (Nat.le_div_iff_mul_le (by omega : 0 < m)).mpr ?_
            have h31 : 31 ≤ u ^ 6 := by
              have : 20 ^ 6 ≤ u ^ 6 := Nat.pow_le_pow_left hu20 6
              omega
            calc u ^ 2 * m ≤ u ^ 2 * 31 := Nat.mul_le_mul_left _ hm31
              _ ≤ u ^ 2 * u ^ 6 := Nat.mul_le_mul_left _ h31
              _ = u ^ 8 := by ring
              _ ≤ n := hub.1
          have hmn : m ≤ n := by
            have : 31 ≤ u ^ 8 := le_trans (by norm_num : 31 ≤ 20 ^ 8) (Nat.pow_le_pow_left hu20 8)
            omega
          have hcyc := cyclotomic_dvd_card_le M n m hM hm2 hmn
          have hsqrt : (u : ℝ) ≤ Real.sqrt ((n / m : ℕ) : ℝ) := by
            rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ u)]
            exact Real.sqrt_le_sqrt (by exact_mod_cast hu2_le)
          have hratio : 4 / Real.sqrt ((n / m : ℕ) : ℝ) ≤ 4 / (u : ℝ) :=
            div_le_div_of_nonneg_left (by norm_num) (by positivity) hsqrt
          have h4u_le1 : 4 / (u : ℝ) ≤ 1 := by
            rw [div_le_one (by positivity)]
            exact_mod_cast (by omega : 4 ≤ u)
          have hφ1 : 1 ≤ Nat.totient m := Nat.totient_pos.mpr (by omega)
          have hpow_le : (4 / Real.sqrt ((n / m : ℕ) : ℝ)) ^ (Nat.totient m) ≤ 4 / (u : ℝ) := by
            calc (4 / Real.sqrt ((n / m : ℕ) : ℝ)) ^ (Nat.totient m)
                ≤ (4 / (u : ℝ)) ^ (Nat.totient m) := pow_le_pow_left₀ (by positivity) hratio _
              _ ≤ (4 / (u : ℝ)) ^ 1 := pow_le_pow_of_le_one (by positivity) h4u_le1 hφ1
              _ = 4 / (u : ℝ) := pow_one _
          exact le_trans hcyc (mul_le_mul_of_nonneg_right hpow_le (by positivity))
      _ = (SmallM.card : ℝ) * ((4 / (u : ℝ)) * ((M + 1 : ℕ) : ℝ) ^ n) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 30 * ((4 / (u : ℝ)) * ((M + 1 : ℕ) : ℝ) ^ n) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          have hcard : SmallM.card ≤ 30 := by
            calc SmallM.card ≤ (Finset.Icc 2 31).card := Finset.card_filter_le _ _
              _ = 30 := by rw [Nat.card_Icc]
          exact_mod_cast hcard
      _ = (120 / (u : ℝ)) * ((M + 1 : ℕ) : ℝ) ^ n := by ring
  have hLarge_bound :
      ((⋃ m ∈ LargeM, {a : Fin n → Fin (M + 1) |
          Polynomial.cyclotomic m ℤ ∣ Green93.monicPoly fun j ↦ (a j : ℕ)}).ncard : ℝ) ≤
        ((6 * (16 : ℝ) ^ 7) / (u : ℝ)) * ((M + 1 : ℕ) : ℝ) ^ n := by
    have hnc := ncard_biUnion_finset_le LargeM (fun m =>
      {a : Fin n → Fin (M + 1) | Polynomial.cyclotomic m ℤ ∣ Green93.monicPoly fun j ↦ (a j : ℕ)})
    calc ((⋃ m ∈ LargeM, _).ncard : ℝ)
        ≤ ∑ m ∈ LargeM, ({a : Fin n → Fin (M + 1) |
            Polynomial.cyclotomic m ℤ ∣ Green93.monicPoly fun j ↦ (a j : ℕ)}.ncard : ℝ) := by
          exact_mod_cast hnc
      _ ≤ ∑ _m ∈ LargeM, (((16 : ℝ) / (u : ℝ)) ^ 7 * ((M + 1 : ℕ) : ℝ) ^ n) := by
          refine Finset.sum_le_sum fun m hm => ?_
          have hmF := Finset.mem_filter.mp hm
          have hm2 : 2 ≤ m := (Finset.mem_Icc.mp hmF.1).1
          have hm_ub : m ≤ 6 * u ^ 6 := (Finset.mem_Icc.mp hmF.1).2
          have hφ7 : 7 ≤ Nat.totient m := hmF.2.1
          have hmn : m ≤ n := by
            have h6 : 6 ≤ u ^ 2 := by nlinarith
            calc m ≤ 6 * u ^ 6 := hm_ub
              _ ≤ u ^ 2 * u ^ 6 := Nat.mul_le_mul_right _ h6
              _ = u ^ 8 := by ring
              _ ≤ n := hub.1
          have hdiv_ge : u ^ 2 / 8 ≤ n / m := by
            refine (Nat.le_div_iff_mul_le (by omega : 0 < m)).mpr ?_
            have h8 : 8 * (u ^ 2 / 8) ≤ u ^ 2 := Nat.mul_div_le (u ^ 2) 8
            have h6 : 6 * (u ^ 2 / 8) ≤ u ^ 2 := by omega
            calc (u ^ 2 / 8) * m ≤ (u ^ 2 / 8) * (6 * u ^ 6) := Nat.mul_le_mul_left _ hm_ub
              _ = (6 * (u ^ 2 / 8)) * u ^ 6 := by ring
              _ ≤ u ^ 2 * u ^ 6 := Nat.mul_le_mul_right _ h6
              _ = u ^ 8 := by ring
              _ ≤ n := hub.1
          have h16_ge : u ^ 2 ≤ 16 * (n / m) := by
            have h8 : u ^ 2 ≤ 8 * (u ^ 2 / 8) + 7 := by omega
            have h400 : 400 ≤ u ^ 2 := by nlinarith
            omega
          have hsqrt : (u : ℝ) / 4 ≤ Real.sqrt ((n / m : ℕ) : ℝ) := by
            rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ (u : ℝ) / 4)]
            refine Real.sqrt_le_sqrt ?_
            have hR : ((u : ℝ) ^ 2) ≤ 16 * ((n / m : ℕ) : ℝ) := by exact_mod_cast h16_ge
            linarith
          have hratio : 4 / Real.sqrt ((n / m : ℕ) : ℝ) ≤ 16 / (u : ℝ) := by
            have h1 := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 4) (by positivity : (0 : ℝ) < (u : ℝ) / 4) hsqrt
            calc 4 / Real.sqrt ((n / m : ℕ) : ℝ) ≤ 4 / ((u : ℝ) / 4) := h1
              _ = 16 / (u : ℝ) := by ring
          have h16u_le1 : 16 / (u : ℝ) ≤ 1 := by
            rw [div_le_one (by positivity)]
            exact_mod_cast (by omega : 16 ≤ u)
          have hpow_le : (4 / Real.sqrt ((n / m : ℕ) : ℝ)) ^ (Nat.totient m) ≤ (16 / (u : ℝ)) ^ 7 := by
            calc (4 / Real.sqrt ((n / m : ℕ) : ℝ)) ^ (Nat.totient m)
                ≤ (16 / (u : ℝ)) ^ (Nat.totient m) := pow_le_pow_left₀ (by positivity) hratio _
              _ ≤ (16 / (u : ℝ)) ^ 7 := pow_le_pow_of_le_one (by positivity) h16u_le1 hφ7
          exact le_trans (cyclotomic_dvd_card_le M n m hM hm2 hmn)
            (mul_le_mul_of_nonneg_right hpow_le (by positivity))
      _ = (LargeM.card : ℝ) * (((16 : ℝ) / (u : ℝ)) ^ 7 * ((M + 1 : ℕ) : ℝ) ^ n) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (6 * (u : ℝ) ^ 6) * (((16 : ℝ) / (u : ℝ)) ^ 7 * ((M + 1 : ℕ) : ℝ) ^ n) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          have hcard : LargeM.card ≤ 6 * u ^ 6 := by
            calc LargeM.card ≤ (Finset.Icc 2 (6 * u ^ 6)).card := Finset.card_filter_le _ _
              _ ≤ 6 * u ^ 6 := by rw [Nat.card_Icc]; omega
          exact_mod_cast hcard
      _ = ((6 * (16 : ℝ) ^ 7) / (u : ℝ)) * ((M + 1 : ℕ) : ℝ) ^ n := by
          have hu_ne : (u : ℝ) ≠ 0 := by positivity
          rw [div_pow]
          field_simp [hu_ne]
  have hunion : (({a : Fin n → Fin (M + 1) |
        (Green93.monicPoly fun j ↦ (a j : ℕ)).coeff 0 ≠ 0 ∧
        ∃ m : ℕ, 1 ≤ m ∧ (Nat.totient m) ^ 2 ≤ n ∧
          Polynomial.cyclotomic m ℤ ∣ Green93.monicPoly fun j ↦ (a j : ℕ)}.ncard : ℝ)) ≤
      ((120 / (u : ℝ)) + (6 * (16 : ℝ) ^ 7) / (u : ℝ)) * ((M + 1 : ℕ) : ℝ) ^ n := by
    have hnat := (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (Set.ncard_union_le _ _)
    have hR : (({a : Fin n → Fin (M + 1) |
        (Green93.monicPoly fun j ↦ (a j : ℕ)).coeff 0 ≠ 0 ∧
        ∃ m : ℕ, 1 ≤ m ∧ (Nat.totient m) ^ 2 ≤ n ∧
          Polynomial.cyclotomic m ℤ ∣ Green93.monicPoly fun j ↦ (a j : ℕ)}.ncard : ℝ)) ≤
        ((⋃ m ∈ SmallM, {a : Fin n → Fin (M + 1) |
          Polynomial.cyclotomic m ℤ ∣ Green93.monicPoly fun j ↦ (a j : ℕ)}).ncard : ℝ) +
        ((⋃ m ∈ LargeM, {a : Fin n → Fin (M + 1) |
          Polynomial.cyclotomic m ℤ ∣ Green93.monicPoly fun j ↦ (a j : ℕ)}).ncard : ℝ) := by
      exact_mod_cast hnat
    linarith
  have hCu : C / (u : ℝ) ≤ ε := by
    have h1 : C / ε ≤ (u₀ : ℝ) := by
      have hceil : C / ε ≤ (Nat.ceil (C / ε) : ℝ) := Nat.le_ceil _
      have hle : Nat.ceil (C / ε) ≤ u₀ := le_trans (Nat.le_succ _) (le_max_right _ _)
      exact le_trans hceil (by exact_mod_cast hle)
    have h2 : C / ε ≤ (u : ℝ) := le_trans h1 (by exact_mod_cast hu_ge)
    rw [div_le_iff₀ (by positivity)]
    have h3 : C ≤ (u : ℝ) * ε := by
      have := (div_le_iff₀ hε).mp h2
      linarith
    linarith
  have hden := pow_le_two_mul_denom hM hn1
  calc (({a : Fin n → Fin (M + 1) |
          (Green93.monicPoly fun j ↦ (a j : ℕ)).coeff 0 ≠ 0 ∧
          ∃ m : ℕ, 1 ≤ m ∧ (Nat.totient m) ^ 2 ≤ n ∧
            Polynomial.cyclotomic m ℤ ∣ Green93.monicPoly fun j ↦ (a j : ℕ)}.ncard : ℝ))
      ≤ ((120 / (u : ℝ)) + (6 * (16 : ℝ) ^ 7) / (u : ℝ)) * ((M + 1 : ℕ) : ℝ) ^ n := hunion
    _ ≤ ((120 / (u : ℝ)) + (6 * (16 : ℝ) ^ 7) / (u : ℝ)) *
          (2 * ((M * (M + 1) ^ (n - 1) : ℕ) : ℝ)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        simpa [Nat.cast_add, Nat.cast_one] using hden
    _ = (C / (u : ℝ)) * ((M * (M + 1) ^ (n - 1) : ℕ) : ℝ) := by dsimp only [C]; ring
    _ ≤ ε * ((M * (M + 1) ^ (n - 1) : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right hCu (by positivity)

end

/- ### Part 5: Main reduction theorem -/

theorem main : H1 → H2 → OMA.R_Green93_green_93_variants_bskk_small_R1.H1 := by
  intro hH1 hH2 M hM1 hM33 ε hε
  have hε4 : 0 < ε / 4 := by linarith
  obtain ⟨n₁, hn₁⟩ := linear_noncyc_divisors_small M hM1 (ε / 4) hε4
  obtain ⟨n₂, hn₂⟩ := cyclotomic_divisors_small M hM1 (ε / 4) hε4
  obtain ⟨n₃, hn₃⟩ := hH1 M hM1 hM33 (ε / 4) hε4
  obtain ⟨n₄, hn₄⟩ := hH2 M hM1 hM33 (ε / 4) hε4
  refine ⟨max 1 (max n₁ (max n₂ (max n₃ n₄))), fun n hn => ?_⟩
  have hn_ge1 : 1 ≤ n := le_trans (le_max_left _ _) hn
  have h_n1 : n₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have h_n2 : n₂ ≤ n :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hn
  have h_n3 : n₃ ≤ n :=
    le_trans (le_trans (le_max_left _ _)
      (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))) hn
  have h_n4 : n₄ ≤ n :=
    le_trans (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))) hn
  have hsample := card_nonzero_constTerm M n hn_ge1
  let S_lin : Set (Fin n → Fin (M + 1)) :=
    {a | (Green93.monicPoly fun j ↦ (a j : ℕ)).coeff 0 ≠ 0 ∧
      ∃ q : ℤ[X], q.Monic ∧ q.natDegree = 1 ∧ q ≠ Polynomial.cyclotomic 2 ℤ ∧
        q ∣ Green93.monicPoly fun j ↦ (a j : ℕ)}
  let S_cyc : Set (Fin n → Fin (M + 1)) :=
    {a | (Green93.monicPoly fun j ↦ (a j : ℕ)).coeff 0 ≠ 0 ∧
      ∃ m : ℕ, 1 ≤ m ∧ (Nat.totient m) ^ 2 ≤ n ∧
        Polynomial.cyclotomic m ℤ ∣ Green93.monicPoly fun j ↦ (a j : ℕ)}
  let S_smallM : Set (Fin n → Fin (M + 1)) :=
    {a | (Green93.monicPoly fun j ↦ (a j : ℕ)).coeff 0 ≠ 0 ∧
      ∃ q : ℤ[X], q.Monic ∧ Irreducible q ∧ 2 ≤ q.natDegree ∧ q.natDegree ^ 2 ≤ n ∧
        (∀ m : ℕ, 1 ≤ m → q ≠ Polynomial.cyclotomic m ℤ) ∧
        (((q.map (Int.castRingHom ℂ)).roots.map fun z : ℂ => max (1 : ℝ) ‖z‖).prod ≤
          (101 : ℝ) / 100) ∧
        q ∣ Green93.monicPoly fun j ↦ (a j : ℕ)}
  let S_largeM : Set (Fin n → Fin (M + 1)) :=
    {a | (Green93.monicPoly fun j ↦ (a j : ℕ)).coeff 0 ≠ 0 ∧
      ∃ q : ℤ[X], q.Monic ∧ Irreducible q ∧ 2 ≤ q.natDegree ∧ q.natDegree ^ 2 ≤ n ∧
        (∀ m : ℕ, 1 ≤ m → q ≠ Polynomial.cyclotomic m ℤ) ∧
        ((101 : ℝ) / 100 <
          ((q.map (Int.castRingHom ℂ)).roots.map fun z : ℂ => max (1 : ℝ) ‖z‖).prod) ∧
        q ∣ Green93.monicPoly fun j ↦ (a j : ℕ)}
  have hcover : {a : Fin n → Fin (M + 1) |
      (Green93.monicPoly fun j ↦ (a j : ℕ)).coeff 0 ≠ 0 ∧
      ∃ g : ℤ[X], g.Monic ∧ 1 ≤ g.natDegree ∧ g.natDegree ^ 2 ≤ n ∧
        g ∣ Green93.monicPoly fun j ↦ (a j : ℕ)} ⊆
      S_lin ∪ (S_cyc ∪ (S_smallM ∪ S_largeM)) := by
    intro a ⟨ha0, g, hg_m, hg_1, hg_sq, hg_dvd⟩
    obtain ⟨q, hq_m, hq_irr, hq_1, hq_le, hq_dvd_g⟩ := exists_irreducible_monic_dvd g hg_m hg_1
    have hq_dvd : q ∣ Green93.monicPoly fun j ↦ (a j : ℕ) := dvd_trans hq_dvd_g hg_dvd
    have hq_sq : q.natDegree ^ 2 ≤ n := le_trans (Nat.pow_le_pow_left hq_le 2) hg_sq
    by_cases hcyc : ∃ m : ℕ, 1 ≤ m ∧ q = Polynomial.cyclotomic m ℤ
    · obtain ⟨m, hm1, hqm⟩ := hcyc
      refine Or.inr (Or.inl ⟨ha0, m, hm1, ?_, hqm ▸ hq_dvd⟩)
      have hdeg_m : q.natDegree = Nat.totient m := by
        rw [hqm, Polynomial.natDegree_cyclotomic m ℤ]
      rwa [← hdeg_m]
    · push Not at hcyc
      by_cases hdeg1 : q.natDegree = 1
      · exact Or.inl ⟨ha0, q, hq_m, hdeg1, hcyc 2 (by omega), hq_dvd⟩
      · have hdeg2 : 2 ≤ q.natDegree := by omega
        rcases le_or_gt (((q.map (Int.castRingHom ℂ)).roots.map fun z : ℂ => max (1 : ℝ) ‖z‖).prod)
            ((101 : ℝ) / 100) with hle | hgt
        · exact Or.inr (Or.inr (Or.inl ⟨ha0, q, hq_m, hq_irr, hdeg2, hq_sq, hcyc, hle, hq_dvd⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨ha0, q, hq_m, hq_irr, hdeg2, hq_sq, hcyc, hgt, hq_dvd⟩))
  have hnc_nat : {a : Fin n → Fin (M + 1) |
      (Green93.monicPoly fun j ↦ (a j : ℕ)).coeff 0 ≠ 0 ∧
      ∃ g : ℤ[X], g.Monic ∧ 1 ≤ g.natDegree ∧ g.natDegree ^ 2 ≤ n ∧
        g ∣ Green93.monicPoly fun j ↦ (a j : ℕ)}.ncard ≤
      S_lin.ncard + S_cyc.ncard + S_smallM.ncard + S_largeM.ncard := by
    have h1 := Set.ncard_le_ncard hcover (Set.toFinite _)
    have h2 := Set.ncard_union_le S_lin (S_cyc ∪ (S_smallM ∪ S_largeM))
    have h3 := Set.ncard_union_le S_cyc (S_smallM ∪ S_largeM)
    have h4 := Set.ncard_union_le S_smallM S_largeM
    omega
  have hnc_real : (({a : Fin n → Fin (M + 1) |
      (Green93.monicPoly fun j ↦ (a j : ℕ)).coeff 0 ≠ 0 ∧
      ∃ g : ℤ[X], g.Monic ∧ 1 ≤ g.natDegree ∧ g.natDegree ^ 2 ≤ n ∧
        g ∣ Green93.monicPoly fun j ↦ (a j : ℕ)}.ncard : ℝ)) ≤
      (S_lin.ncard : ℝ) + (S_cyc.ncard : ℝ) + (S_smallM.ncard : ℝ) + (S_largeM.ncard : ℝ) := by
    exact_mod_cast hnc_nat
  have hb1 : (S_lin.ncard : ℝ) ≤ (ε / 4) * ((M * (M + 1) ^ (n - 1) : ℕ) : ℝ) := hn₁ n h_n1
  have hb2 : (S_cyc.ncard : ℝ) ≤ (ε / 4) * ((M * (M + 1) ^ (n - 1) : ℕ) : ℝ) := hn₂ n h_n2
  have hb3 : (S_smallM.ncard : ℝ) ≤ (ε / 4) * ((M * (M + 1) ^ (n - 1) : ℕ) : ℝ) := hn₃ n h_n3
  have hb4 : (S_largeM.ncard : ℝ) ≤ (ε / 4) * ((M * (M + 1) ^ (n - 1) : ℕ) : ℝ) := hn₄ n h_n4
  have _ : {a : Fin n → Fin (M + 1) |
      (Green93.monicPoly fun j ↦ (a j : ℕ)).coeff 0 ≠ 0}.ncard = M * (M + 1) ^ (n - 1) := hsample
  linarith

end OMA.R_Green93_green_93_variants_bskk_small_R1_H1_R1
