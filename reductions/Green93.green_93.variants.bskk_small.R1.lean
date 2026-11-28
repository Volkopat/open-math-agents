import FormalConjectures.GreensOpenProblems.«93»

/-!
Reduction of `Green93.green_93.variants.bskk_small` (Bary-Soroker, Koukoulopoulos, and Kozma,
Invent. Math. 233 (2023), 1041-1120, Theorem 1(b)) to the small-divisor and intermediate-divisor
regimes of Theorem 2 (`H1`, `H2`), proved via Gauss's lower bound on monic irreducibles over
`GaloisField p d`, injective product factorization modulo `p = Nat.minFac (M + 1)`, exact fiber
lifting, proper monic factorization in `ℤ[X]`, and uniformization over `1 ≤ M ≤ 33`.
-/

namespace OMA.R_Green93_green_93_variants_bskk_small_R1

open Polynomial

/- Small-degree divisor bound (BSKK23 Theorem 2, regime 1 <= deg g <= sqrt n):
for every 1 <= M <= 33 and every epsilon > 0, eventually the fraction of degree-n monic
polynomials over {0, ..., M} with nonzero constant term having a monic integer divisor of
degree 1 <= d <= sqrt n is at most epsilon. -/
def H1 : Prop :=
  ∀ M : ℕ, 1 ≤ M → M ≤ 33 → ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    (({a : Fin n → Fin (M + 1) |
        (Green93.monicPoly fun j ↦ (a j : ℕ)).coeff 0 ≠ 0 ∧
        ∃ g : ℤ[X], g.Monic ∧ 1 ≤ g.natDegree ∧ g.natDegree ^ 2 ≤ n ∧
          g ∣ Green93.monicPoly fun j ↦ (a j : ℕ)}.ncard : ℝ) ≤
      ε * ((M * (M + 1) ^ (n - 1) : ℕ) : ℝ))

/- Intermediate-degree divisor bound (BSKK23 Theorem 2, regime sqrt n < deg g < theta * n):
for every 1 <= M <= 33, there exists theta in (0, 1/2) such that for every epsilon > 0,
eventually the fraction of degree-n monic polynomials over {0, ..., M} with nonzero constant
term having a monic integer divisor of degree sqrt n < d < theta * n is at most epsilon. -/
def H2 : Prop :=
  ∀ M : ℕ, 1 ≤ M → M ≤ 33 → ∃ θ : ℝ, 0 < θ ∧ θ < 1 / 2 ∧
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      (({a : Fin n → Fin (M + 1) |
          (Green93.monicPoly fun j ↦ (a j : ℕ)).coeff 0 ≠ 0 ∧
          ∃ g : ℤ[X], g.Monic ∧ n < g.natDegree ^ 2 ∧ (g.natDegree : ℝ) < θ * (n : ℝ) ∧
            g ∣ Green93.monicPoly fun j ↦ (a j : ℕ)}.ncard : ℝ) ≤
        ε * ((M * (M + 1) ^ (n - 1) : ℕ) : ℝ))

/- Finite-parameter uniformization over 1 <= M <= 33: reduces uniform (delta, n0) to pointwise
eventual positive lower bounds by taking the minimum delta and maximum n0 over Fin 33. -/
lemma uniformize_bounded_M (P : ℕ → ℕ → ℝ)
    (h : ∀ M : ℕ, 1 ≤ M → M ≤ 33 →
      ∃ δ : ℝ, 0 < δ ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → δ ≤ P M n) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ n₀ : ℕ, ∀ M n : ℕ, 1 ≤ M → M ≤ 33 → n₀ ≤ n → δ ≤ P M n := by
  have hfin : ∀ k : Fin 33,
      ∃ δ : ℝ, 0 < δ ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → δ ≤ P (k.val + 1) n :=
    fun k => h (k.val + 1) (by omega) (by omega)
  choose δf hδf using hfin
  choose nf hnf using fun k : Fin 33 => (hδf k).2
  let δ : ℝ := Finset.univ.inf' Finset.univ_nonempty δf
  let n₀ : ℕ := Finset.univ.sup nf
  refine ⟨δ, ?_, n₀, ?_⟩
  · rw [Finset.lt_inf'_iff]
    intro k _
    exact (hδf k).1
  · intro M n hM1 hM33 hn
    let k : Fin 33 := ⟨M - 1, by omega⟩
    have hkM : k.val + 1 = M := by
      change M - 1 + 1 = M
      omega
    have hδ_le : δ ≤ δf k := Finset.inf'_le δf (Finset.mem_univ k)
    have hn_le : nf k ≤ n := le_trans (Finset.le_sup (f := nf) (Finset.mem_univ k)) hn
    have hP : δf k ≤ P (k.val + 1) n := hnf k n hn_le
    rw [hkM] at hP
    exact le_trans hδ_le hP

/- Coefficient formula for X^n + sum_{j < n} c_j X^j over any commutative ring. -/
lemma coeff_monic_of_coeffs {R : Type*} [CommRing R] {n : ℕ} (c : Fin n → R) (k : ℕ) :
    (X ^ n + ∑ j : Fin n, C (c j) * X ^ (j : ℕ)).coeff k =
      if h : k < n then c ⟨k, h⟩ else if k = n then 1 else 0 := by
  rw [coeff_add, coeff_X_pow, finsetSum_coeff]
  by_cases hk : k < n
  · have hne : k ≠ n := by omega
    simp only [hne, ↓reduceIte, zero_add]
    have hsum : (∑ j : Fin n, (C (c j) * X ^ (j : ℕ)).coeff k) = c ⟨k, hk⟩ := by
      rw [Finset.sum_eq_single ⟨k, hk⟩]
      · simp
      · intro j _ hj
        rw [coeff_C_mul, coeff_X_pow]
        have hjk : k ≠ (j : ℕ) := fun h => hj (Fin.ext h.symm)
        simp only [hjk, ↓reduceIte, mul_zero]
      · intro h
        exact absurd (Finset.mem_univ _) h
    rw [hsum]
    simp [hk]
  · have hsum : (∑ j : Fin n, (C (c j) * X ^ (j : ℕ)).coeff k) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      rw [coeff_C_mul, coeff_X_pow]
      have hjk : k ≠ (j : ℕ) := by omega
      simp only [hjk, ↓reduceIte, mul_zero]
    rw [hsum, add_zero]
    by_cases hkn : k = n
    · subst hkn
      simp
    · simp [hk, hkn]

/- Degree upper bound for the lower-order sum sum_{j < n} c_j X^j. -/
lemma degree_lower_sum_lt {R : Type*} [CommRing R] {n : ℕ} (c : Fin n → R) :
    (∑ j : Fin n, C (c j) * X ^ (j : ℕ)).degree < (n : WithBot ℕ) := by
  have haux : ∀ s : Finset (Fin n),
      (∑ j ∈ s, C (c j) * X ^ (j : ℕ)).degree < (n : WithBot ℕ) := by
    intro s
    classical
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty, degree_zero]
      exact WithBot.bot_lt_coe n
    | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      refine (degree_add_le _ _).trans_lt (max_lt ?_ ih)
      calc
        (C (c a) * X ^ (a : ℕ)).degree ≤ (C (c a)).degree + (X ^ (a : ℕ) : R[X]).degree :=
          degree_mul_le _ _
        _ ≤ (0 : WithBot ℕ) + (a : ℕ) := add_le_add degree_C_le (degree_X_pow_le (a : ℕ))
        _ = ((a : ℕ) : WithBot ℕ) := by simp
        _ < (n : WithBot ℕ) := WithBot.coe_lt_coe.mpr a.isLt
  exact haux Finset.univ

/- X^n + sum_{j < n} c_j X^j is always monic. -/
lemma monic_of_coeffs {R : Type*} [CommRing R] {n : ℕ} (c : Fin n → R) :
    (X ^ n + ∑ j : Fin n, C (c j) * X ^ (j : ℕ)).Monic := by
  nontriviality R
  apply (monic_X_pow n).add_of_left
  rw [degree_X_pow]
  exact degree_lower_sum_lt c

/- Over a nontrivial commutative ring, X^n + sum_{j < n} c_j X^j has natDegree n. -/
lemma natDegree_of_coeffs {R : Type*} [CommRing R] [Nontrivial R] {n : ℕ} (c : Fin n → R) :
    (X ^ n + ∑ j : Fin n, C (c j) * X ^ (j : ℕ)).natDegree = n := by
  have hlt : (∑ j : Fin n, C (c j) * X ^ (j : ℕ)).degree < (X ^ n : R[X]).degree := by
    rw [degree_X_pow]
    exact degree_lower_sum_lt c
  have hdeg : (X ^ n + ∑ j : Fin n, C (c j) * X ^ (j : ℕ)).degree = (n : WithBot ℕ) := by
    rw [degree_add_eq_left_of_degree_lt hlt, degree_X_pow]
  exact natDegree_eq_of_degree_eq_some hdeg

/- Every monic polynomial of natDegree n is recovered from its lower n coefficients. -/
lemma eq_monic_of_coeffs {R : Type*} [CommRing R] {n : ℕ} {f : R[X]}
    (hf : f.Monic) (hdeg : f.natDegree = n) :
    f = X ^ n + ∑ j : Fin n, C (f.coeff (j : ℕ)) * X ^ (j : ℕ) := by
  ext k
  rw [coeff_monic_of_coeffs]
  by_cases hk : k < n
  · simp [hk]
  · by_cases hkn : k = n
    · subst hkn
      simp [← hdeg, hf.leadingCoeff]
    · have hgt : f.natDegree < k := by omega
      simp [hk, hkn, coeff_eq_zero_of_natDegree_lt hgt]

/- Ring homomorphism image of X^n + sum_{j < n} c_j X^j maps coefficients entrywise. -/
lemma map_monic_of_coeffs {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {n : ℕ}
    (c : Fin n → R) :
    (X ^ n + ∑ j : Fin n, C (c j) * X ^ (j : ℕ)).map φ =
      X ^ n + ∑ j : Fin n, C (φ (c j)) * X ^ (j : ℕ) := by
  simp [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C]

/- Exact cardinality of tuples in Fin (m + 1) -> alpha with coordinate 0 distinct from z. -/
lemma card_nonzero_zero_coord {α : Type*} [Fintype α] [DecidableEq α] (z : α) (m : ℕ) :
    (Finset.univ.filter fun a : Fin (m + 1) → α => a 0 ≠ z).card =
      (Fintype.card α - 1) * Fintype.card α ^ m := by
  let S := Finset.univ.filter fun a : Fin (m + 1) → α => a 0 ≠ z
  let T := (Finset.univ.erase z) ×ˢ (Finset.univ : Finset (Fin m → α))
  have hbij : S.card = T.card := by
    refine Finset.card_bij (fun a _ => (a 0, fun j : Fin m => a j.succ)) ?_ ?_ ?_
    · intro a ha
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at ha
      simp only [T, Finset.mem_product, Finset.mem_erase, Finset.mem_univ, and_true]
      exact ha
    · intro a₁ _ a₂ _ h
      have h0 : a₁ 0 = a₂ 0 := congrArg Prod.fst h
      have htail : (fun j : Fin m => a₁ j.succ) = (fun j : Fin m => a₂ j.succ) :=
        congrArg Prod.snd h
      funext i
      refine Fin.cases h0 (fun j => congrFun htail j) i
    · intro p hp
      simp only [T, Finset.mem_product, Finset.mem_erase, Finset.mem_univ, and_true] at hp
      refine ⟨Fin.cons p.1 p.2, ?_, ?_⟩
      · simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Fin.cons_zero]
        exact hp
      · ext
        · simp
        · simp
  rw [hbij, Finset.card_product, Finset.card_erase_of_mem (Finset.mem_univ z),
    Finset.card_univ, Finset.card_univ, Fintype.card_fun, Fintype.card_fin]

/- Exact cardinality of the sample space {a : Fin n -> Fin (M + 1) | (monicPoly a).coeff 0 != 0}. -/
lemma card_nonzero_const_sample (M n : ℕ) (hn : 1 ≤ n) :
    (Finset.univ.filter fun a : Fin n → Fin (M + 1) =>
      (Green93.monicPoly fun j => (a j : ℕ)).coeff 0 ≠ 0).card =
      M * (M + 1) ^ (n - 1) := by
  classical
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hfilt :
      (Finset.univ.filter fun a : Fin (m + 1) → Fin (M + 1) =>
        (Green93.monicPoly fun j => (a j : ℕ)).coeff 0 ≠ 0) =
      (Finset.univ.filter fun a : Fin (m + 1) → Fin (M + 1) => a 0 ≠ (0 : Fin (M + 1))) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Green93.monicPoly]
    rw [coeff_monic_of_coeffs (c := fun j : Fin (m + 1) => ((a j : ℕ) : ℤ)) 0]
    have h0lt : 0 < m + 1 := Nat.succ_pos m
    simp only [h0lt, dite_true]
    constructor
    · intro h ha0
      apply h
      have hv : (a 0 : ℕ) = 0 := by rw [ha0]; rfl
      exact_mod_cast hv
    · intro h h0
      apply h
      have hv : (a 0 : ℕ) = 0 := by exact_mod_cast h0
      exact Fin.ext hv
  rw [hfilt, card_nonzero_zero_coord (0 : Fin (M + 1)) m]
  simp

/- Proper monic factorization equivalence in Z[X] for a monic polynomial of positive degree. -/
lemma not_irreducible_monic_int_iff {f : ℤ[X]} (hf : f.Monic) (hdeg : 1 ≤ f.natDegree) :
    ¬ Irreducible f ↔
      ∃ g h : ℤ[X], g.Monic ∧ h.Monic ∧ 1 ≤ g.natDegree ∧ 1 ≤ h.natDegree ∧ g * h = f := by
  have hfu : ¬ IsUnit f := by
    intro hu
    rcases Polynomial.isUnit_iff.mp hu with ⟨r, _, rfl⟩
    rw [natDegree_C] at hdeg
    omega
  constructor
  · intro hnirr
    rw [irreducible_iff] at hnirr
    push Not at hnirr
    obtain ⟨g, h, hfg, hgu, hhu⟩ := hnirr hfu
    have hlc : g.leadingCoeff * h.leadingCoeff = 1 := by
      rw [← leadingCoeff_mul, ← hfg, hf.leadingCoeff]
    have hg_unit : IsUnit g.leadingCoeff :=
      ⟨⟨g.leadingCoeff, h.leadingCoeff, hlc, by rw [mul_comm]; exact hlc⟩, rfl⟩
    rcases Int.isUnit_iff.mp hg_unit with hgl1 | hgln1
    · have hhl1 : h.leadingCoeff = 1 := by
        rw [hgl1, one_mul] at hlc
        exact hlc
      have hgm : g.Monic := hgl1
      have hhm : h.Monic := hhl1
      have hgdeg : 1 ≤ g.natDegree := by
        by_contra h0
        have hd0 : g.natDegree = 0 := by omega
        have hg1 : g = 1 := by
          rw [eq_C_of_natDegree_eq_zero hd0]
          have hc0 : g.coeff 0 = 1 := by rw [← hd0]; exact hgm.leadingCoeff
          rw [hc0, map_one]
        exact hgu (hg1 ▸ isUnit_one)
      have hhdeg : 1 ≤ h.natDegree := by
        by_contra h0
        have hd0 : h.natDegree = 0 := by omega
        have hh1 : h = 1 := by
          rw [eq_C_of_natDegree_eq_zero hd0]
          have hc0 : h.coeff 0 = 1 := by rw [← hd0]; exact hhm.leadingCoeff
          rw [hc0, map_one]
        exact hhu (hh1 ▸ isUnit_one)
      exact ⟨g, h, hgm, hhm, hgdeg, hhdeg, hfg.symm⟩
    · have hhln1 : h.leadingCoeff = -1 := by
        rw [hgln1, neg_one_mul] at hlc
        linarith
      have hgm : (-g).Monic := by
        show (-g).leadingCoeff = 1
        rw [leadingCoeff_neg, hgln1, neg_neg]
      have hhm : (-h).Monic := by
        show (-h).leadingCoeff = 1
        rw [leadingCoeff_neg, hhln1, neg_neg]
      have hngu : ¬ IsUnit (-g) := fun hu => hgu (by simpa using hu.neg)
      have hnhu : ¬ IsUnit (-h) := fun hu => hhu (by simpa using hu.neg)
      have hgdeg : 1 ≤ (-g).natDegree := by
        by_contra h0
        have hd0 : (-g).natDegree = 0 := by omega
        have hg1 : -g = 1 := by
          rw [eq_C_of_natDegree_eq_zero hd0]
          have hc0 : (-g).coeff 0 = 1 := by rw [← hd0]; exact hgm.leadingCoeff
          rw [hc0, map_one]
        exact hngu (hg1 ▸ isUnit_one)
      have hhdeg : 1 ≤ (-h).natDegree := by
        by_contra h0
        have hd0 : (-h).natDegree = 0 := by omega
        have hh1 : -h = 1 := by
          rw [eq_C_of_natDegree_eq_zero hd0]
          have hc0 : (-h).coeff 0 = 1 := by rw [← hd0]; exact hhm.leadingCoeff
          rw [hc0, map_one]
        exact hnhu (hh1 ▸ isUnit_one)
      exact ⟨-g, -h, hgm, hhm, hgdeg, hhdeg, by rw [neg_mul_neg, hfg]⟩
  · rintro ⟨g, h, _, _, hg1, hh1, hgh⟩ hirr
    have hgu : ¬ IsUnit g := by
      intro hu
      rcases Polynomial.isUnit_iff.mp hu with ⟨r, _, rfl⟩
      rw [natDegree_C] at hg1
      omega
    have hhu : ¬ IsUnit h := by
      intro hu
      rcases Polynomial.isUnit_iff.mp hu with ⟨r, _, rfl⟩
      rw [natDegree_C] at hh1
      omega
    rcases hirr.isUnit_or_isUnit hgh.symm with h1 | h2
    · exact hgu h1
    · exact hhu h2

/- Local-to-global irreducibility criterion modulo a prime p: if f mod p has an irreducible
divisor of degree > (1 - theta) * deg f and f has no monic integer divisor of degree in
[1, theta * deg f), then f is irreducible in Z[X]. -/
lemma irreducible_of_mod_prime_large_factor_and_no_small_div
    (p : ℕ) [Fact p.Prime] {f : ℤ[X]} (hf : f.Monic) (hdeg : 1 ≤ f.natDegree)
    {θ : ℝ}
    (hbig : ∃ q : (ZMod p)[X], Irreducible q ∧
      q ∣ f.map (Int.castRingHom (ZMod p)) ∧
      (1 - θ) * (f.natDegree : ℝ) < (q.natDegree : ℝ))
    (hno : ∀ g : ℤ[X], g.Monic → 1 ≤ g.natDegree →
      (g.natDegree : ℝ) < θ * (f.natDegree : ℝ) → ¬ g ∣ f) :
    Irreducible f := by
  by_contra hnirr
  obtain ⟨g, h, hg, hh, hg1, hh1, hgh⟩ := (not_irreducible_monic_int_iff hf hdeg).mp hnirr
  have hsum_deg : g.natDegree + h.natDegree = f.natDegree := by
    rw [← hgh, hg.natDegree_mul hh]
  obtain ⟨q, hq_irr, hq_dvd, hq_deg⟩ := hbig
  let φ : ℤ →+* ZMod p := Int.castRingHom (ZMod p)
  have hq_prime : Prime q := UniqueFactorizationMonoid.irreducible_iff_prime.mp hq_irr
  have hq_dvd_prod : q ∣ g.map φ * h.map φ := by
    rw [← Polynomial.map_mul, hgh]
    exact hq_dvd
  rcases hq_prime.dvd_or_dvd hq_dvd_prod with hqg | hqh
  · have hgm_ne : g.map φ ≠ 0 := (hg.map φ).ne_zero
    have hq_le_g : q.natDegree ≤ g.natDegree := by
      calc
        q.natDegree ≤ (g.map φ).natDegree := Polynomial.natDegree_le_of_dvd hqg hgm_ne
        _ = g.natDegree := hg.natDegree_map φ
    have hq_le_gR : (q.natDegree : ℝ) ≤ (g.natDegree : ℝ) := Nat.cast_le.mpr hq_le_g
    have hsumR : (g.natDegree : ℝ) + (h.natDegree : ℝ) = (f.natDegree : ℝ) := by
      exact_mod_cast hsum_deg
    have hh_lt : (h.natDegree : ℝ) < θ * (f.natDegree : ℝ) := by linarith
    exact hno h hh hh1 hh_lt ⟨g, by rw [mul_comm, hgh]⟩
  · have hhm_ne : h.map φ ≠ 0 := (hh.map φ).ne_zero
    have hq_le_h : q.natDegree ≤ h.natDegree := by
      calc
        q.natDegree ≤ (h.map φ).natDegree := Polynomial.natDegree_le_of_dvd hqh hhm_ne
        _ = h.natDegree := hh.natDegree_map φ
    have hq_le_hR : (q.natDegree : ℝ) ≤ (h.natDegree : ℝ) := Nat.cast_le.mpr hq_le_h
    have hsumR : (g.natDegree : ℝ) + (h.natDegree : ℝ) = (f.natDegree : ℝ) := by
      exact_mod_cast hsum_deg
    have hg_lt : (g.natDegree : ℝ) < θ * (f.natDegree : ℝ) := by linarith
    exact hno g hg hg1 hg_lt ⟨h, hgh.symm⟩

/- Elementary geometric sum bound: for p >= 2, sum_{e <= m} p^e <= 2 * p^m. -/
lemma sum_pow_le_two_mul_pow {p : ℕ} (hp : 2 ≤ p) (m : ℕ) :
    (∑ e ∈ Finset.range (m + 1), p ^ e) ≤ 2 * p ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have hstep : 2 * p ^ m ≤ p * p ^ m := Nat.mul_le_mul_right (p ^ m) hp
    have hpow : p ^ (m + 1) = p * p ^ m := by rw [pow_succ, mul_comm]
    omega

/- Gauss-type lower bound on monic irreducible polynomials of degree d >= 4 over ZMod p,
proved via minimal polynomials of elements of GaloisField p d and subfield root bounds. -/
lemma card_irred_monic_zmod_lower_bound (p : ℕ) [hp_fact : Fact p.Prime] {d : ℕ} (hd : 4 ≤ d) :
    p ^ d ≤ 2 * d * {c : Fin d → ZMod p |
      Irreducible (X ^ d + ∑ j : Fin d, C (c j) * X ^ (j : ℕ))}.ncard := by
  classical
  have hp2 : 2 ≤ p := hp_fact.out.two_le
  have hd0 : d ≠ 0 := by omega
  let K := GaloisField p d
  let _ : Fintype K := Fintype.ofFinite K
  have hcardK : Fintype.card K = p ^ d := by
    rw [Fintype.card_eq_nat_card, GaloisField.card p d hd0]
  have hfinK : Module.finrank (ZMod p) K = d := GaloisField.finrank p hd0
  have hmin_dvd : ∀ α : K, (minpoly (ZMod p) α).natDegree ∣ d := by
    intro α
    have hint : IsIntegral (ZMod p) α := Algebra.IsIntegral.isIntegral α
    let E := IntermediateField.adjoin (ZMod p) ({α} : Set K)
    have hfinE : Module.finrank (ZMod p) E = (minpoly (ZMod p) α).natDegree :=
      IntermediateField.adjoin.finrank hint
    have hmul : Module.finrank (ZMod p) E * Module.finrank E K = Module.finrank (ZMod p) K :=
      Module.finrank_mul_finrank (ZMod p) E K
    rw [hfinE, hfinK] at hmul
    exact ⟨Module.finrank E K, hmul.symm⟩
  have hmin_pos : ∀ α : K, 1 ≤ (minpoly (ZMod p) α).natDegree := by
    intro α
    exact minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral α)
  have hpow_min : ∀ α : K, α ^ (p ^ (minpoly (ZMod p) α).natDegree) = α := by
    intro α
    have hint : IsIntegral (ZMod p) α := Algebra.IsIntegral.isIntegral α
    let E := IntermediateField.adjoin (ZMod p) ({α} : Set K)
    have _ : Finite E := Finite.of_injective Subtype.val Subtype.val_injective
    let _ : Fintype E := Fintype.ofFinite E
    have hcardE : Fintype.card E = p ^ (minpoly (ZMod p) α).natDegree := by
      rw [← FiniteField.pow_finrank_eq_card p E, IntermediateField.adjoin.finrank hint]
    let x : E := ⟨α, IntermediateField.mem_adjoin_simple_self (ZMod p) α⟩
    have hx : x ^ Fintype.card E = x := FiniteField.pow_card x
    rw [hcardE] at hx
    have hval : (x ^ (p ^ (minpoly (ZMod p) α).natDegree) : K) = (x : K) :=
      congrArg Subtype.val hx
    simpa [x] using hval
  let S : Finset K := Finset.univ.filter fun α : K => (minpoly (ZMod p) α).natDegree = d
  let Bad : Finset K := Finset.univ.filter fun α : K => (minpoly (ZMod p) α).natDegree < d
  have huniv_sub : (Finset.univ : Finset K) ⊆ S ∪ Bad := by
    intro α _
    have hle : (minpoly (ZMod p) α).natDegree ≤ d :=
      Nat.le_of_dvd (by omega) (hmin_dvd α)
    rw [Finset.mem_union]
    by_cases heq : (minpoly (ZMod p) α).natDegree = d
    · left
      simp [S, heq]
    · right
      simp [Bad]
      omega
  have hcard_split : p ^ d ≤ S.card + Bad.card := by
    calc
      p ^ d = (Finset.univ : Finset K).card := by rw [Finset.card_univ, hcardK]
      _ ≤ (S ∪ Bad).card := Finset.card_le_card huniv_sub
      _ ≤ S.card + Bad.card := Finset.card_union_le S Bad
  have hBad_sub : Bad ⊆ (Finset.Ico 1 (d / 2 + 1)).biUnion
      (fun e => ((X ^ (p ^ e) - X : K[X]).roots).toFinset) := by
    intro α hα
    simp only [Bad, Finset.mem_filter, Finset.mem_univ, true_and] at hα
    set e := (minpoly (ZMod p) α).natDegree
    have he1 : 1 ≤ e := hmin_pos α
    have hedvd : e ∣ d := hmin_dvd α
    rcases hedvd with ⟨m, hm⟩
    have hm2 : 2 ≤ m := by nlinarith
    have h2e : 2 * e ≤ d := by nlinarith
    have he_le : e ≤ d / 2 := by omega
    rw [Finset.mem_biUnion]
    refine ⟨e, Finset.mem_Ico.mpr ⟨he1, by omega⟩, ?_⟩
    rw [Multiset.mem_toFinset, mem_roots]
    · simp only [IsRoot.def, eval_sub, eval_pow, eval_X, sub_eq_zero]
      exact hpow_min α
    · intro h0
      have hpe : 2 ≤ p ^ e := by
        calc
          2 ≤ p := hp2
          _ = p ^ 1 := (pow_one p).symm
          _ ≤ p ^ e := Nat.pow_le_pow_right (by omega) he1
      have hcoeff : ((X ^ (p ^ e) - X : K[X]).coeff (p ^ e)) = 1 := by
        rw [coeff_sub, coeff_X_pow_self, coeff_X]
        have hne : 1 ≠ p ^ e := by omega
        simp [hne]
      rw [h0, coeff_zero] at hcoeff
      exact zero_ne_one hcoeff
  have hBad_card : Bad.card ≤ 2 * p ^ (d / 2) := by
    calc
      Bad.card ≤ ((Finset.Ico 1 (d / 2 + 1)).biUnion
          (fun e => ((X ^ (p ^ e) - X : K[X]).roots).toFinset)).card :=
        Finset.card_le_card hBad_sub
      _ ≤ ∑ e ∈ Finset.Ico 1 (d / 2 + 1), (((X ^ (p ^ e) - X : K[X]).roots).toFinset).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ e ∈ Finset.Ico 1 (d / 2 + 1), p ^ e := by
        apply Finset.sum_le_sum
        intro e he
        have he1 : 1 ≤ e := (Finset.mem_Ico.mp he).1
        have hpe : 2 ≤ p ^ e := by
          calc
            2 ≤ p := hp2
            _ = p ^ 1 := (pow_one p).symm
            _ ≤ p ^ e := Nat.pow_le_pow_right (by omega) he1
        have hnd : (X ^ (p ^ e) - X : K[X]).natDegree = p ^ e := by
          rw [natDegree_sub_eq_left_of_natDegree_lt]
          · exact natDegree_X_pow (p ^ e)
          · rw [natDegree_X, natDegree_X_pow]
            omega
        calc
          (((X ^ (p ^ e) - X : K[X]).roots).toFinset).card ≤
              Multiset.card (X ^ (p ^ e) - X : K[X]).roots := Multiset.toFinset_card_le _
          _ ≤ (X ^ (p ^ e) - X : K[X]).natDegree := Polynomial.card_roots' _
          _ = p ^ e := hnd
      _ ≤ ∑ e ∈ Finset.range (d / 2 + 1), p ^ e := by
        apply Finset.sum_le_sum_of_subset
        intro e he
        rw [Finset.mem_Ico] at he
        rw [Finset.mem_range]
        exact he.2
      _ ≤ 2 * p ^ (d / 2) := sum_pow_le_two_mul_pow hp2 (d / 2)
  have h2Bad : 2 * Bad.card ≤ p ^ d := by
    have h4 : 4 ≤ p ^ 2 := by nlinarith
    calc
      2 * Bad.card ≤ 2 * (2 * p ^ (d / 2)) := Nat.mul_le_mul_left 2 hBad_card
      _ = 4 * p ^ (d / 2) := by ring
      _ ≤ p ^ 2 * p ^ (d / 2) := Nat.mul_le_mul_right _ h4
      _ = p ^ (2 + d / 2) := (pow_add p 2 (d / 2)).symm
      _ ≤ p ^ d := Nat.pow_le_pow_right (by omega) (by omega)
  have hS_lower : p ^ d ≤ 2 * S.card := by omega
  let I_set : Finset (Fin d → ZMod p) :=
    Finset.univ.filter fun c : Fin d → ZMod p =>
      Irreducible (X ^ d + ∑ j : Fin d, C (c j) * X ^ (j : ℕ))
  let f : K → (Fin d → ZMod p) := fun α j => (minpoly (ZMod p) α).coeff (j : ℕ)
  have hf_maps : ∀ α ∈ S, f α ∈ I_set := by
    intro α hα
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hα
    have hint : IsIntegral (ZMod p) α := Algebra.IsIntegral.isIntegral α
    have hrec : minpoly (ZMod p) α = X ^ d + ∑ j : Fin d, C (f α j) * X ^ (j : ℕ) :=
      eq_monic_of_coeffs (minpoly.monic hint) hα
    simp only [I_set, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← hrec]
    exact minpoly.irreducible hint
  have hS_le : S.card ≤ d * I_set.card := by
    rw [Finset.card_eq_sum_card_fiberwise hf_maps]
    calc
      (∑ c ∈ I_set, (S.filter fun α => f α = c).card) ≤ ∑ _c ∈ I_set, d := by
        apply Finset.sum_le_sum
        intro c _
        let q : (ZMod p)[X] := X ^ d + ∑ j : Fin d, C (c j) * X ^ (j : ℕ)
        let qK : K[X] := q.map (algebraMap (ZMod p) K)
        have hqK_monic : qK.Monic := (monic_of_coeffs c).map (algebraMap (ZMod p) K)
        have hqK_deg : qK.natDegree = d := by
          rw [(monic_of_coeffs c).natDegree_map, natDegree_of_coeffs]
        have hsub : (S.filter fun α => f α = c) ⊆ qK.roots.toFinset := by
          intro α hα
          simp only [Finset.mem_filter] at hα
          rcases hα with ⟨hαS, hfc⟩
          simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hαS
          have hint : IsIntegral (ZMod p) α := Algebra.IsIntegral.isIntegral α
          have hmin_eq : minpoly (ZMod p) α = q := by
            have h1 := eq_monic_of_coeffs (minpoly.monic hint) hαS
            simpa only [q, ← hfc, f] using h1
          rw [Multiset.mem_toFinset, mem_roots hqK_monic.ne_zero, IsRoot.def]
          change (q.map (algebraMap (ZMod p) K)).eval α = 0
          rw [← eval₂_eq_eval_map]
          change aeval α q = 0
          rw [← hmin_eq]
          exact minpoly.aeval (ZMod p) α
        calc
          (S.filter fun α => f α = c).card ≤ qK.roots.toFinset.card := Finset.card_le_card hsub
          _ ≤ Multiset.card qK.roots := Multiset.toFinset_card_le _
          _ ≤ qK.natDegree := Polynomial.card_roots' qK
          _ = d := hqK_deg
      _ = I_set.card * d := by simp
      _ = d * I_set.card := mul_comm _ _
  have hI_ncard : I_set.card = {c : Fin d → ZMod p |
      Irreducible (X ^ d + ∑ j : Fin d, C (c j) * X ^ (j : ℕ))}.ncard := by
    rw [← Set.ncard_coe_finset I_set]
    congr 1
    ext c
    simp [I_set]
  rw [← hI_ncard]
  calc
    p ^ d ≤ 2 * S.card := hS_lower
    _ ≤ 2 * (d * I_set.card) := Nat.mul_le_mul_left 2 hS_le
    _ = 2 * d * I_set.card := by ring

/- Uniqueness of the large monic irreducible factor of degree > n/2 in (ZMod p)[X]. -/
lemma eq_large_monic_irred_factor (p : ℕ) [Fact p.Prime] {q₁ q₂ r₁ r₂ : (ZMod p)[X]}
    (hq₁m : q₁.Monic) (hq₂m : q₂.Monic) (hr₂m : r₂.Monic)
    (hq₁i : Irreducible q₁) (hq₂i : Irreducible q₂)
    (hdeg : r₂.natDegree < q₁.natDegree)
    (heq : q₁ * r₁ = q₂ * r₂) : q₁ = q₂ ∧ r₁ = r₂ := by
  have hq₁p : Prime q₁ := UniqueFactorizationMonoid.irreducible_iff_prime.mp hq₁i
  have hdvd : q₁ ∣ q₂ * r₂ := ⟨r₁, heq.symm⟩
  rcases hq₁p.dvd_or_dvd hdvd with hq12 | hq1r2
  · have hassoc : Associated q₁ q₂ := by
      rcases hq12 with ⟨u, hu⟩
      rcases hq₂i.isUnit_or_isUnit hu with hq1u | huu
      · exact absurd hq1u hq₁i.not_isUnit
      · exact ⟨huu.unit, hu.symm⟩
    have hqq : q₁ = q₂ := Polynomial.eq_of_monic_of_associated hq₁m hq₂m hassoc
    have hrr : r₁ = r₂ := mul_left_cancel₀ hq₁m.ne_zero (by rwa [← hqq] at heq)
    exact ⟨hqq, hrr⟩
  · have hle : q₁.natDegree ≤ r₂.natDegree :=
      Polynomial.natDegree_le_of_dvd hq1r2 hr₂m.ne_zero
    omega

/- Lower bound on the count of monic degree-n polynomials in (ZMod p)[X] with nonzero constant
term and an irreducible divisor of degree >= n - k + 1, via injective factorization (q, r) |-> q * r. -/
lemma card_mod_prime_large_irred_factor (p : ℕ) [hp_fact : Fact p.Prime] {n k : ℕ}
    (hk : 4 ≤ k) (hkn : 2 * k < n) :
    (k - 1) * p ^ n ≤ 4 * n *
      {c : Fin n → ZMod p |
        c ⟨0, by omega⟩ ≠ 0 ∧
        ∃ q : (ZMod p)[X], Irreducible q ∧
          q ∣ (X ^ n + ∑ j : Fin n, C (c j) * X ^ (j : ℕ)) ∧
          n - k + 1 ≤ q.natDegree}.ncard := by
  classical
  have hp2 : 2 ≤ p := hp_fact.out.two_le
  let A_mod : Finset (Fin n → ZMod p) :=
    Finset.univ.filter fun c : Fin n → ZMod p =>
      c ⟨0, by omega⟩ ≠ 0 ∧
      ∃ q : (ZMod p)[X], Irreducible q ∧
        q ∣ (X ^ n + ∑ j : Fin n, C (c j) * X ^ (j : ℕ)) ∧
        n - k + 1 ≤ q.natDegree
  let I_d : ∀ d : ℕ, Finset (Fin d → ZMod p) := fun d =>
    Finset.univ.filter fun u : Fin d → ZMod p =>
      Irreducible (X ^ d + ∑ j : Fin d, C (u j) * X ^ (j : ℕ))
  let R_d : ∀ d : ℕ, Finset (Fin (n - d) → ZMod p) := fun d =>
    Finset.univ.filter fun v : Fin (n - d) → ZMod p =>
      (X ^ (n - d) + ∑ j : Fin (n - d), C (v j) * X ^ (j : ℕ)).coeff 0 ≠ 0
  let prodCoeffs : ∀ d : ℕ, (Fin d → ZMod p) × (Fin (n - d) → ZMod p) → (Fin n → ZMod p) :=
    fun d uv j =>
      ((X ^ d + ∑ i : Fin d, C (uv.1 i) * X ^ (i : ℕ)) *
        (X ^ (n - d) + ∑ i : Fin (n - d), C (uv.2 i) * X ^ (i : ℕ))).coeff (j : ℕ)
  let Img : ℕ → Finset (Fin n → ZMod p) := fun d =>
    (I_d d ×ˢ R_d d).image (prodCoeffs d)
  have hprod_rec : ∀ {d : ℕ} (hdn : d ≤ n) (u : Fin d → ZMod p) (v : Fin (n - d) → ZMod p),
      X ^ n + ∑ j : Fin n, C (prodCoeffs d (u, v) j) * X ^ (j : ℕ) =
        (X ^ d + ∑ i : Fin d, C (u i) * X ^ (i : ℕ)) *
          (X ^ (n - d) + ∑ i : Fin (n - d), C (v i) * X ^ (i : ℕ)) := by
    intro d hdn u v
    let q := X ^ d + ∑ i : Fin d, C (u i) * X ^ (i : ℕ)
    let r := X ^ (n - d) + ∑ i : Fin (n - d), C (v i) * X ^ (i : ℕ)
    have hqr_m : (q * r).Monic := (monic_of_coeffs u).mul (monic_of_coeffs v)
    have hqr_deg : (q * r).natDegree = n := by
      rw [(monic_of_coeffs u).natDegree_mul (monic_of_coeffs v),
        natDegree_of_coeffs u, natDegree_of_coeffs v]
      omega
    exact (eq_monic_of_coeffs hqr_m hqr_deg).symm
  have hImg_sub : ∀ d ∈ Finset.Ico (n - k + 1) n, Img d ⊆ A_mod := by
    intro d hd c hc
    rw [Finset.mem_Ico] at hd
    rw [Finset.mem_image] at hc
    rcases hc with ⟨⟨u, v⟩, huv, rfl⟩
    rw [Finset.mem_product] at huv
    rcases huv with ⟨hu, hv⟩
    simp only [I_d, R_d, Finset.mem_filter, Finset.mem_univ, true_and] at hu hv
    let q := X ^ d + ∑ i : Fin d, C (u i) * X ^ (i : ℕ)
    let r := X ^ (n - d) + ∑ i : Fin (n - d), C (v i) * X ^ (i : ℕ)
    have hq_deg : q.natDegree = d := natDegree_of_coeffs u
    have hq0 : q.coeff 0 ≠ 0 := by
      intro h0
      have hXdvd : X ∣ q := Polynomial.X_dvd_iff.mpr h0
      rcases hXdvd with ⟨s, hs⟩
      rcases hu.isUnit_or_isUnit hs with hXu | hsu
      · exact Polynomial.not_isUnit_X hXu
      · rcases Polynomial.isUnit_iff.mp hsu with ⟨a, _, ha⟩
        have hs0 : s.natDegree = 0 := by rw [← ha, natDegree_C]
        have hq1 : q.natDegree ≤ 1 := by
          rw [hs]
          calc
            (X * s).natDegree ≤ (X : (ZMod p)[X]).natDegree + s.natDegree := natDegree_mul_le
            _ = 1 := by rw [natDegree_X, hs0, add_zero]
        omega
    simp only [A_mod, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨?_, q, hu, ?_, ?_⟩
    · change (q * r).coeff 0 ≠ 0
      rw [Polynomial.mul_coeff_zero]
      exact mul_ne_zero hq0 hv
    · rw [hprod_rec (by omega : d ≤ n) u v]
      exact ⟨r, rfl⟩
    · rw [hq_deg]
      exact hd.1
  have hImg_card : ∀ d ∈ Finset.Ico (n - k + 1) n, (Img d).card = (I_d d).card * (R_d d).card := by
    intro d hd
    rw [Finset.mem_Ico] at hd
    rw [Finset.card_image_of_injOn, Finset.card_product]
    intro uv₁ huv₁ uv₂ huv₂ hpeq
    rw [Finset.mem_coe, Finset.mem_product] at huv₁ huv₂
    have hu₁ := (Finset.mem_filter.mp huv₁.1).2
    have hu₂ := (Finset.mem_filter.mp huv₂.1).2
    have hpoly :
        (X ^ d + ∑ i : Fin d, C (uv₁.1 i) * X ^ (i : ℕ)) *
          (X ^ (n - d) + ∑ i : Fin (n - d), C (uv₁.2 i) * X ^ (i : ℕ)) =
        (X ^ d + ∑ i : Fin d, C (uv₂.1 i) * X ^ (i : ℕ)) *
          (X ^ (n - d) + ∑ i : Fin (n - d), C (uv₂.2 i) * X ^ (i : ℕ)) := by
      rw [← hprod_rec (by omega : d ≤ n) uv₁.1 uv₁.2,
        ← hprod_rec (by omega : d ≤ n) uv₂.1 uv₂.2, hpeq]
    have hlt : (X ^ (n - d) + ∑ i : Fin (n - d), C (uv₂.2 i) * X ^ (i : ℕ)).natDegree <
        (X ^ d + ∑ i : Fin d, C (uv₁.1 i) * X ^ (i : ℕ)).natDegree := by
      rw [natDegree_of_coeffs, natDegree_of_coeffs]
      omega
    obtain ⟨hqeq, hreq⟩ := eq_large_monic_irred_factor p
      (monic_of_coeffs uv₁.1) (monic_of_coeffs uv₂.1) (monic_of_coeffs uv₂.2)
      hu₁ hu₂ hlt hpoly
    apply Prod.ext
    · funext i
      have hi := congrArg (fun P => P.coeff (i : ℕ)) hqeq
      rw [coeff_monic_of_coeffs, coeff_monic_of_coeffs] at hi
      simpa only [i.isLt, dite_true] using hi
    · funext i
      have hi := congrArg (fun P => P.coeff (i : ℕ)) hreq
      rw [coeff_monic_of_coeffs, coeff_monic_of_coeffs] at hi
      simpa only [i.isLt, dite_true] using hi
  have hImg_disj : Set.PairwiseDisjoint (↑(Finset.Ico (n - k + 1) n) : Set ℕ) Img := by
    intro d₁ hd₁ d₂ hd₂ hne
    rw [Finset.mem_coe, Finset.mem_Ico] at hd₁ hd₂
    change Disjoint (Img d₁) (Img d₂)
    rw [Finset.disjoint_left]
    intro c hc₁ hc₂
    rw [Finset.mem_image] at hc₁ hc₂
    rcases hc₁ with ⟨⟨u₁, v₁⟩, huv₁, rfl⟩
    rcases hc₂ with ⟨⟨u₂, v₂⟩, huv₂, heq⟩
    rw [Finset.mem_product] at huv₁ huv₂
    have hu₁ := (Finset.mem_filter.mp huv₁.1).2
    have hu₂ := (Finset.mem_filter.mp huv₂.1).2
    have hpoly :
        (X ^ d₁ + ∑ i : Fin d₁, C (u₁ i) * X ^ (i : ℕ)) *
          (X ^ (n - d₁) + ∑ i : Fin (n - d₁), C (v₁ i) * X ^ (i : ℕ)) =
        (X ^ d₂ + ∑ i : Fin d₂, C (u₂ i) * X ^ (i : ℕ)) *
          (X ^ (n - d₂) + ∑ i : Fin (n - d₂), C (v₂ i) * X ^ (i : ℕ)) := by
      rw [← hprod_rec (by omega : d₁ ≤ n) u₁ v₁,
        ← hprod_rec (by omega : d₂ ≤ n) u₂ v₂, heq]
    have hlt : (X ^ (n - d₂) + ∑ i : Fin (n - d₂), C (v₂ i) * X ^ (i : ℕ)).natDegree <
        (X ^ d₁ + ∑ i : Fin d₁, C (u₁ i) * X ^ (i : ℕ)).natDegree := by
      rw [natDegree_of_coeffs, natDegree_of_coeffs]
      omega
    obtain ⟨hqeq, _⟩ := eq_large_monic_irred_factor p
      (monic_of_coeffs u₁) (monic_of_coeffs u₂) (monic_of_coeffs v₂)
      hu₁ hu₂ hlt hpoly
    have hdeq : d₁ = d₂ := by
      have := congrArg Polynomial.natDegree hqeq
      simpa [natDegree_of_coeffs] using this
    exact hne hdeq
  have hsum_le_A : (∑ d ∈ Finset.Ico (n - k + 1) n, (I_d d).card * (R_d d).card) ≤ A_mod.card := by
    calc
      (∑ d ∈ Finset.Ico (n - k + 1) n, (I_d d).card * (R_d d).card)
          = ∑ d ∈ Finset.Ico (n - k + 1) n, (Img d).card := by
            apply Finset.sum_congr rfl
            intro d hd
            exact (hImg_card d hd).symm
      _ = ((Finset.Ico (n - k + 1) n).biUnion Img).card :=
        (Finset.card_biUnion hImg_disj).symm
      _ ≤ A_mod.card := Finset.card_le_card (Finset.biUnion_subset.mpr hImg_sub)
  have hR_card : ∀ d ∈ Finset.Ico (n - k + 1) n, (R_d d).card = (p - 1) * p ^ (n - d - 1) := by
    intro d hd
    rw [Finset.mem_Ico] at hd
    have hm1 : 1 ≤ n - d := by omega
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n - d ≠ 0)
    have hcast :
        (Finset.univ.filter fun v : Fin (m + 1) → ZMod p =>
          (X ^ (m + 1) + ∑ j : Fin (m + 1), C (v j) * X ^ (j : ℕ)).coeff 0 ≠ 0).card =
        (p - 1) * p ^ m := by
      have hfilt :
          (Finset.univ.filter fun v : Fin (m + 1) → ZMod p =>
            (X ^ (m + 1) + ∑ j : Fin (m + 1), C (v j) * X ^ (j : ℕ)).coeff 0 ≠ 0) =
          (Finset.univ.filter fun v : Fin (m + 1) → ZMod p => v 0 ≠ 0) := by
        ext v
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [coeff_monic_of_coeffs v 0]
        simp
      rw [hfilt, card_nonzero_zero_coord (0 : ZMod p) m, ZMod.card]
    have hsub : n - d - 1 = m := by omega
    rw [hsub]
    dsimp only [R_d]
    rw [hm]
    exact hcast
  have hterm : ∀ d ∈ Finset.Ico (n - k + 1) n, p ^ n ≤ 4 * n * ((I_d d).card * (R_d d).card) := by
    intro d hd
    have hd_ico := Finset.mem_Ico.mp hd
    have hd4 : 4 ≤ d := by omega
    have hI_ncard : (I_d d).card = {u : Fin d → ZMod p |
        Irreducible (X ^ d + ∑ j : Fin d, C (u j) * X ^ (j : ℕ))}.ncard := by
      rw [← Set.ncard_coe_finset (I_d d)]
      congr 1
      ext u
      simp [I_d]
    have hI : p ^ d ≤ 2 * d * (I_d d).card := by
      rw [hI_ncard]
      exact card_irred_monic_zmod_lower_bound p hd4
    have hR := hR_card d hd
    have hp_le : p ≤ 2 * (p - 1) := by omega
    have hexp : d + (1 + (n - d - 1)) = n := by omega
    calc
      p ^ n = p ^ (d + (1 + (n - d - 1))) := by rw [hexp]
      _ = p ^ d * (p * p ^ (n - d - 1)) := by rw [pow_add, pow_add, pow_one]
      _ ≤ (2 * d * (I_d d).card) * (2 * (p - 1) * p ^ (n - d - 1)) := by
        apply Nat.mul_le_mul hI
        calc
          p * p ^ (n - d - 1) ≤ (2 * (p - 1)) * p ^ (n - d - 1) :=
            Nat.mul_le_mul_right _ hp_le
          _ = 2 * (p - 1) * p ^ (n - d - 1) := by ring
      _ = 4 * d * ((I_d d).card * ((p - 1) * p ^ (n - d - 1))) := by ring
      _ = 4 * d * ((I_d d).card * (R_d d).card) := by rw [← hR]
      _ ≤ 4 * n * ((I_d d).card * (R_d d).card) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 4 (by omega))
  have hcard_ico : (Finset.Ico (n - k + 1) n).card = k - 1 := by
    rw [Nat.card_Ico]
    omega
  have hA_ncard : A_mod.card = {c : Fin n → ZMod p |
      c ⟨0, by omega⟩ ≠ 0 ∧
      ∃ q : (ZMod p)[X], Irreducible q ∧
        q ∣ (X ^ n + ∑ j : Fin n, C (c j) * X ^ (j : ℕ)) ∧
        n - k + 1 ≤ q.natDegree}.ncard := by
    rw [← Set.ncard_coe_finset A_mod]
    congr 1
    ext c
    simp [A_mod]
  rw [← hA_ncard]
  calc
    (k - 1) * p ^ n = ∑ _d ∈ Finset.Ico (n - k + 1) n, p ^ n := by
      rw [Finset.sum_const, hcard_ico, smul_eq_mul]
    _ ≤ ∑ d ∈ Finset.Ico (n - k + 1) n, 4 * n * ((I_d d).card * (R_d d).card) :=
      Finset.sum_le_sum hterm
    _ = 4 * n * ∑ d ∈ Finset.Ico (n - k + 1) n, (I_d d).card * (R_d d).card := by
      rw [Finset.mul_sum]
    _ ≤ 4 * n * A_mod.card := Nat.mul_le_mul_left (4 * n) hsum_le_A

/- Exact fiber lifting from ZMod p to Fin (M + 1) when M + 1 = k_M * p: every tuple c in S
with c 0 != 0 lifts to k_M^n distinct coefficient vectors in Fin (M + 1) with nonzero constant term. -/
lemma card_lift_mod_prime_fibers {M p k_M n : ℕ} [hp_fact : Fact p.Prime]
    (hMp : M + 1 = k_M * p) (hn : 1 ≤ n) (S : Finset (Fin n → ZMod p))
    (hS : ∀ c ∈ S, c ⟨0, by omega⟩ ≠ 0) :
    S.card * k_M ^ n ≤
      (Finset.univ.filter fun a : Fin n → Fin (M + 1) =>
        (Green93.monicPoly fun j => (a j : ℕ)).coeff 0 ≠ 0 ∧
        (fun j : Fin n => ((a j : ℕ) : ZMod p)) ∈ S).card := by
  classical
  have hp0 : 0 < p := hp_fact.out.pos
  let lift : (Fin n → ZMod p) × (Fin n → Fin k_M) → (Fin n → Fin (M + 1)) :=
    fun ct j => ⟨(ct.1 j).val + (ct.2 j).val * p, by
      have hc : (ct.1 j).val < p := ZMod.val_lt (ct.1 j)
      have ht : (ct.2 j).val < k_M := (ct.2 j).isLt
      have hle : (ct.2 j).val + 1 ≤ k_M := ht
      have hmul : ((ct.2 j).val + 1) * p ≤ k_M * p := Nat.mul_le_mul_right p hle
      nlinarith⟩
  let Dom : Finset ((Fin n → ZMod p) × (Fin n → Fin k_M)) := S ×ˢ Finset.univ
  let Tgt : Finset (Fin n → Fin (M + 1)) :=
    Finset.univ.filter fun a : Fin n → Fin (M + 1) =>
      (Green93.monicPoly fun j => (a j : ℕ)).coeff 0 ≠ 0 ∧
      (fun j : Fin n => ((a j : ℕ) : ZMod p)) ∈ S
  have hred : ∀ ct (j : Fin n), ((lift ct j : ℕ) : ZMod p) = ct.1 j := by
    intro ct j
    change (((ct.1 j).val + (ct.2 j).val * p : ℕ) : ZMod p) = ct.1 j
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_self, mul_zero, add_zero]
  have himg_sub : Dom.image lift ⊆ Tgt := by
    intro a ha
    rw [Finset.mem_image] at ha
    rcases ha with ⟨ct, hct, rfl⟩
    rw [Finset.mem_product] at hct
    have hcS : ct.1 ∈ S := hct.1
    simp only [Tgt, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨?_, ?_⟩
    · unfold Green93.monicPoly
      rw [coeff_monic_of_coeffs (c := fun j : Fin n => ((lift ct j : ℕ) : ℤ)) 0]
      have h0lt : 0 < n := by omega
      simp only [h0lt, dite_true]
      intro h0
      have hnat0 : (lift ct ⟨0, h0lt⟩ : ℕ) = 0 := by exact_mod_cast h0
      have hval0 : (ct.1 ⟨0, h0lt⟩).val = 0 := by
        change (ct.1 ⟨0, h0lt⟩).val + (ct.2 ⟨0, h0lt⟩).val * p = 0 at hnat0
        omega
      have hc0 : ct.1 ⟨0, h0lt⟩ = 0 := by
        rw [← ZMod.natCast_zmod_val (ct.1 ⟨0, h0lt⟩), hval0, Nat.cast_zero]
      exact hS ct.1 hcS hc0
    · have hfun : (fun j : Fin n => ((lift ct j : ℕ) : ZMod p)) = ct.1 :=
        funext (hred ct)
      rw [hfun]
      exact hcS
  have hinj : Set.InjOn lift (Dom : Set ((Fin n → ZMod p) × (Fin n → Fin k_M))) := by
    intro ct₁ _ ct₂ _ heq
    apply Prod.ext
    · funext j
      rw [← hred ct₁ j, ← hred ct₂ j, heq]
    · funext j
      have hj := congrArg (fun f => (f j).val) heq
      change (ct₁.1 j).val + (ct₁.2 j).val * p = (ct₂.1 j).val + (ct₂.2 j).val * p at hj
      have hc₁ : (ct₁.1 j).val < p := ZMod.val_lt (ct₁.1 j)
      have hc₂ : (ct₂.1 j).val < p := ZMod.val_lt (ct₂.1 j)
      have ht_eq : (ct₁.2 j).val = (ct₂.2 j).val := by
        have h1 : ((ct₁.1 j).val + (ct₁.2 j).val * p) / p = (ct₁.2 j).val := by
          rw [Nat.add_mul_div_right _ _ hp0, Nat.div_eq_of_lt hc₁, zero_add]
        have h2 : ((ct₂.1 j).val + (ct₂.2 j).val * p) / p = (ct₂.2 j).val := by
          rw [Nat.add_mul_div_right _ _ hp0, Nat.div_eq_of_lt hc₂, zero_add]
        rw [← h1, ← h2, hj]
      exact Fin.ext ht_eq
  calc
    S.card * k_M ^ n = Dom.card := by
      rw [Finset.card_product, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    _ = (Dom.image lift).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ Tgt.card := Finset.card_le_card himg_sub

/- Pointwise-in-M reduction from H1 (small divisors) and H2 (intermediate divisors) to an
eventual positive lower bound on Green93.irreducibleProb M n for fixed 1 <= M <= 33. -/
lemma pointwise_bskk_small_of_H1_H2 (hH1 : H1) (hH2 : H2) {M : ℕ} (hM1 : 1 ≤ M) (hM33 : M ≤ 33) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → δ ≤ Green93.irreducibleProb M n := by
  classical
  obtain ⟨θ, hθ0, hθhalf, hH2M⟩ := hH2 M hM1 hM33
  have hθ32 : 0 < θ / 32 := by linarith
  obtain ⟨n₁, hn₁⟩ := hH1 M hM1 hM33 (θ / 32) hθ32
  obtain ⟨n₂, hn₂⟩ := hH2M (θ / 32) hθ32
  let n₀ : ℕ := max (max n₁ n₂) (Nat.ceil (4 / θ) + 10)
  refine ⟨θ / 16, by linarith, n₀, ?_⟩
  intro n hn
  have hn₁_le : n₁ ≤ n := le_trans (le_trans (le_max_left n₁ n₂) (le_max_left _ _)) hn
  have hn₂_le : n₂ ≤ n := le_trans (le_trans (le_max_right n₁ n₂) (le_max_left _ _)) hn
  have hn_ceil : Nat.ceil (4 / θ) + 10 ≤ n := le_trans (le_max_right _ _) hn
  have hn1 : 1 ≤ n := by omega
  have h4_le_θn : 4 ≤ θ * (n : ℝ) := by
    have h1 : 4 / θ ≤ (Nat.ceil (4 / θ) : ℝ) := Nat.le_ceil (4 / θ)
    have h2 : (Nat.ceil (4 / θ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : Nat.ceil (4 / θ) ≤ n)
    have h3 : 4 / θ ≤ (n : ℝ) := le_trans h1 h2
    have h4 := mul_le_mul_of_nonneg_left h3 (le_of_lt hθ0)
    have h5 : θ * (4 / θ) = 4 := by field_simp
    linarith
  let k : ℕ := Nat.floor (θ * (n : ℝ))
  have hk4 : 4 ≤ k := Nat.le_floor h4_le_θn
  have hk_le_θn : (k : ℝ) ≤ θ * (n : ℝ) := Nat.floor_le (by positivity)
  have hθn_lt_k1 : θ * (n : ℝ) < (k : ℝ) + 1 := Nat.lt_floor_add_one (θ * (n : ℝ))
  have h2k_lt_n : 2 * k < n := by
    have hR : (2 * k : ℝ) < (n : ℝ) := by
      calc
        (2 * k : ℝ) = 2 * (k : ℝ) := by ring
        _ ≤ 2 * (θ * (n : ℝ)) := by linarith
        _ < 2 * ((1 / 2 : ℝ) * (n : ℝ)) := by
          have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
          nlinarith
        _ = (n : ℝ) := by ring
    exact_mod_cast hR
  let p : ℕ := Nat.minFac (M + 1)
  have hp_prime : p.Prime := Nat.minFac_prime (by omega)
  have : Fact p.Prime := ⟨hp_prime⟩
  obtain ⟨k_M, hk_M⟩ := Nat.minFac_dvd (M + 1)
  have hMp : M + 1 = k_M * p := by rw [hk_M, mul_comm]
  let S_mod : Finset (Fin n → ZMod p) :=
    Finset.univ.filter fun c : Fin n → ZMod p =>
      c ⟨0, by omega⟩ ≠ 0 ∧
      ∃ q : (ZMod p)[X], Irreducible q ∧
        q ∣ (X ^ n + ∑ j : Fin n, C (c j) * X ^ (j : ℕ)) ∧
        n - k + 1 ≤ q.natDegree
  have hS_mod_nz : ∀ c ∈ S_mod, c ⟨0, by omega⟩ ≠ 0 := by
    intro c hc
    exact (Finset.mem_filter.mp hc).2.1
  let A_set : Finset (Fin n → Fin (M + 1)) :=
    Finset.univ.filter fun a : Fin n → Fin (M + 1) =>
      (Green93.monicPoly fun j => (a j : ℕ)).coeff 0 ≠ 0 ∧
      (fun j : Fin n => ((a j : ℕ) : ZMod p)) ∈ S_mod
  have hS_ncard : S_mod.card = {c : Fin n → ZMod p |
      c ⟨0, by omega⟩ ≠ 0 ∧
      ∃ q : (ZMod p)[X], Irreducible q ∧
        q ∣ (X ^ n + ∑ j : Fin n, C (c j) * X ^ (j : ℕ)) ∧
        n - k + 1 ≤ q.natDegree}.ncard := by
    rw [← Set.ncard_coe_finset S_mod]
    congr 1
    ext c
    simp [S_mod]
  have hmod_bound : (k - 1) * p ^ n ≤ 4 * n * S_mod.card := by
    rw [hS_ncard]
    exact card_mod_prime_large_irred_factor p hk4 h2k_lt_n
  have hlift_bound := card_lift_mod_prime_fibers hMp hn1 S_mod hS_mod_nz
  let D : ℕ := M * (M + 1) ^ (n - 1)
  have hD_le_pow : D ≤ (M + 1) ^ n := by
    have hpow : (M + 1) ^ n = (M + 1) * (M + 1) ^ (n - 1) := by
      cases n with
      | zero => omega
      | succ m => simp [pow_succ, mul_comm]
    rw [hpow]
    exact Nat.mul_le_mul_right _ (Nat.le_succ M)
  have hA_nat : (k - 1) * D ≤ 4 * n * A_set.card := by
    calc
      (k - 1) * D ≤ (k - 1) * (M + 1) ^ n := Nat.mul_le_mul_left (k - 1) hD_le_pow
      _ = (k - 1) * (k_M * p) ^ n := by rw [hMp]
      _ = k_M ^ n * ((k - 1) * p ^ n) := by rw [mul_pow]; ring
      _ ≤ k_M ^ n * (4 * n * S_mod.card) := Nat.mul_le_mul_left (k_M ^ n) hmod_bound
      _ = 4 * n * (S_mod.card * k_M ^ n) := by ring
      _ ≤ 4 * n * A_set.card := Nat.mul_le_mul_left (4 * n) hlift_bound
  have hA_real : (θ / 8) * (D : ℝ) ≤ (A_set.card : ℝ) := by
    have hk1_ge : (θ / 2) * (n : ℝ) ≤ ((k - 1 : ℕ) : ℝ) := by
      have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
      linarith
    have hA_R : ((k - 1 : ℕ) : ℝ) * (D : ℝ) ≤ 4 * (n : ℝ) * (A_set.card : ℝ) := by
      exact_mod_cast hA_nat
    have h1 : (θ / 2) * (n : ℝ) * (D : ℝ) ≤ 4 * (n : ℝ) * (A_set.card : ℝ) :=
      le_trans (mul_le_mul_of_nonneg_right hk1_ge (Nat.cast_nonneg D)) hA_R
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    nlinarith
  let Good : Finset (Fin n → Fin (M + 1)) :=
    Finset.univ.filter fun a : Fin n → Fin (M + 1) =>
      (Green93.monicPoly fun j => (a j : ℕ)).coeff 0 ≠ 0 ∧
      Irreducible (Green93.monicPoly fun j => (a j : ℕ))
  let Bad1 : Finset (Fin n → Fin (M + 1)) :=
    Finset.univ.filter fun a : Fin n → Fin (M + 1) =>
      (Green93.monicPoly fun j => (a j : ℕ)).coeff 0 ≠ 0 ∧
      ∃ g : ℤ[X], g.Monic ∧ 1 ≤ g.natDegree ∧ g.natDegree ^ 2 ≤ n ∧
        g ∣ Green93.monicPoly fun j => (a j : ℕ)
  let Bad2 : Finset (Fin n → Fin (M + 1)) :=
    Finset.univ.filter fun a : Fin n → Fin (M + 1) =>
      (Green93.monicPoly fun j => (a j : ℕ)).coeff 0 ≠ 0 ∧
      ∃ g : ℤ[X], g.Monic ∧ n < g.natDegree ^ 2 ∧ (g.natDegree : ℝ) < θ * (n : ℝ) ∧
        g ∣ Green93.monicPoly fun j => (a j : ℕ)
  have hA_sub : A_set ⊆ Good ∪ Bad1 ∪ Bad2 := by
    intro a ha
    simp only [A_set, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    rcases ha with ⟨ha0, haS⟩
    by_cases h1 : a ∈ Bad1
    · exact Finset.mem_union_left Bad2 (Finset.mem_union_right Good h1)
    · by_cases h2 : a ∈ Bad2
      · exact Finset.mem_union_right (Good ∪ Bad1) h2
      · apply Finset.mem_union_left Bad2
        apply Finset.mem_union_left Bad1
        simp only [Good, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨ha0, ?_⟩
        let f : ℤ[X] := Green93.monicPoly fun j => (a j : ℕ)
        have hf_monic : f.Monic := monic_of_coeffs (fun j : Fin n => ((a j : ℕ) : ℤ))
        have hf_deg : f.natDegree = n := natDegree_of_coeffs (fun j : Fin n => ((a j : ℕ) : ℤ))
        have hf_map : f.map (Int.castRingHom (ZMod p)) =
            X ^ n + ∑ j : Fin n, C (((a j : ℕ) : ZMod p)) * X ^ (j : ℕ) := by
          unfold f Green93.monicPoly
          rw [map_monic_of_coeffs]
          simp
        simp only [S_mod, Finset.mem_filter, Finset.mem_univ, true_and] at haS
        obtain ⟨_, q, hq_irr, hq_dvd, hq_deg⟩ := haS
        refine irreducible_of_mod_prime_large_factor_and_no_small_div p hf_monic
          (by rw [hf_deg]; exact hn1) (θ := θ) ?_ ?_
        · refine ⟨q, hq_irr, by rw [hf_map]; exact hq_dvd, ?_⟩
          rw [hf_deg]
          have hqR : ((n - k + 1 : ℕ) : ℝ) ≤ (q.natDegree : ℝ) := Nat.cast_le.mpr hq_deg
          have hnkR : ((n - k + 1 : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) + 1 := by
            rw [Nat.cast_add, Nat.cast_sub (by omega : k ≤ n), Nat.cast_one]
          linarith
        · intro g hg hg1 hg_lt hgdvd
          rw [hf_deg] at hg_lt
          by_cases hsq : g.natDegree ^ 2 ≤ n
          · apply h1
            simp only [Bad1, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨ha0, g, hg, hg1, hsq, hgdvd⟩
          · apply h2
            simp only [Bad2, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨ha0, g, hg, by omega, hg_lt, hgdvd⟩
  have hcard_union : A_set.card ≤ Good.card + Bad1.card + Bad2.card := by
    calc
      A_set.card ≤ (Good ∪ Bad1 ∪ Bad2).card := Finset.card_le_card hA_sub
      _ ≤ (Good ∪ Bad1).card + Bad2.card := Finset.card_union_le _ _
      _ ≤ Good.card + Bad1.card + Bad2.card :=
        Nat.add_le_add_right (Finset.card_union_le _ _) _
  have hBad1_eq : (Bad1.card : ℝ) =
      ({a : Fin n → Fin (M + 1) |
        (Green93.monicPoly fun j => (a j : ℕ)).coeff 0 ≠ 0 ∧
        ∃ g : ℤ[X], g.Monic ∧ 1 ≤ g.natDegree ∧ g.natDegree ^ 2 ≤ n ∧
          g ∣ Green93.monicPoly fun j => (a j : ℕ)}.ncard : ℝ) := by
    congr 1
    rw [← Set.ncard_coe_finset Bad1]
    congr 1
    ext a
    simp [Bad1]
  have hBad2_eq : (Bad2.card : ℝ) =
      ({a : Fin n → Fin (M + 1) |
        (Green93.monicPoly fun j => (a j : ℕ)).coeff 0 ≠ 0 ∧
        ∃ g : ℤ[X], g.Monic ∧ n < g.natDegree ^ 2 ∧ (g.natDegree : ℝ) < θ * (n : ℝ) ∧
          g ∣ Green93.monicPoly fun j => (a j : ℕ)}.ncard : ℝ) := by
    congr 1
    rw [← Set.ncard_coe_finset Bad2]
    congr 1
    ext a
    simp [Bad2]
  have hBad1_bound : (Bad1.card : ℝ) ≤ (θ / 32) * (D : ℝ) := by
    rw [hBad1_eq]
    exact hn₁ n hn₁_le
  have hBad2_bound : (Bad2.card : ℝ) ≤ (θ / 32) * (D : ℝ) := by
    rw [hBad2_eq]
    exact hn₂ n hn₂_le
  have hcard_unionR : (A_set.card : ℝ) ≤ (Good.card : ℝ) + (Bad1.card : ℝ) + (Bad2.card : ℝ) := by
    exact_mod_cast hcard_union
  have hGood_lower : (θ / 16) * (D : ℝ) ≤ (Good.card : ℝ) := by linarith
  have hD_pos : (0 : ℝ) < (D : ℝ) := by
    have hDn : 0 < D := Nat.mul_pos (by omega) (Nat.pow_pos (by omega))
    exact_mod_cast hDn
  unfold Green93.irreducibleProb
  have hden :
      ((Finset.univ.filter fun a : Fin n → Fin (M + 1) =>
        (Green93.monicPoly fun j => (a j : ℕ)).coeff 0 ≠ 0).card : ℝ) = (D : ℝ) := by
    exact_mod_cast card_nonzero_const_sample M n hn1
  have hnum :
      ((Finset.univ.filter fun a : Fin n → Fin (M + 1) =>
        (Green93.monicPoly fun j => (a j : ℕ)).coeff 0 ≠ 0 ∧
        Irreducible (Green93.monicPoly fun j => (a j : ℕ))).card : ℝ) = (Good.card : ℝ) := by
    congr 1
  rw [hden, hnum, le_div_iff₀ hD_pos]
  exact hGood_lower

theorem main : H1 → H2 → type_of% @Green93.green_93.variants.bskk_small := by
  intro hH1 hH2
  exact uniformize_bounded_M Green93.irreducibleProb
    (fun M hM1 hM33 => pointwise_bskk_small_of_H1_H2 hH1 hH2 hM1 hM33)

end OMA.R_Green93_green_93_variants_bskk_small_R1
