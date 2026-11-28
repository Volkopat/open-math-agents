import OMAReductions.R_Arxiv_2610_08796_exists_isPolyTime_bayesNash_R2_H3_R1

-- Step H2 of reduction R2.H3.R1: polynomial bit-bound, exact rational threshold,
-- and monotone cutoff characterization for unconstrained fixed-threshold equilibria.

/-!
# Rational Threshold Bound and Coverage Monotonicity (`R2.H3.R1.H2`)

We prove the pure mathematical structure hypothesis `H2` of reduction `R2.H3.R1` without any
Turing machine machinery or topological fixed-point theorems:

1. **Fourier–Motzkin elimination** over any strictly ordered field `K` (`ℚ` or `ℝ`), yielding:
   - Rational feasibility from real feasibility for rational linear inequality systems;
   - Farkas' lemma and Hall's bipartite supply-demand theorem (via finite layer-cake induction);
   - Exact strong LP duality for bipartite flow programs with lower bounds or equalities.
2. **Strictly positive LTU game structure** (`a_{θ,t} > 0`, `d_t > 0`):
   - The lower-feasible coverage set `LowerSet G lam` is nonempty, compact, and closed under
     coordinatewise `max`, hence has a unique maximum `c*(lam)`.
   - Using LP duality on the log-slope weights `-Real.log (a_{θ,t})`, we show `c*(lam)` also
     satisfies the upper defender best-response condition, hence is a fixed-`lam` equilibrium.
   - Using the same log-slope LP duality between any ordered equilibrium pair `cLo ≤ cHi` at fixed
     `lam`, we prove an intermediate value property for total coverage `∑ t, c t`.
3. **General games via utility-preserving perturbation**:
   - Perturbing `b_{θ,t} ↦ b_{θ,t} + ε c_t`, `a_{θ,t} ↦ a_{θ,t} + ε`, `d_t ↦ d_t + ε` preserves
     attacker utilities identically at `c` while making slopes strictly positive.
   - Taking `ε ↓ 0` proves equilibrium existence for all `lam ≥ 0`, coordinatewise monotonicity
     in `lam`, and exact attainment `∑ t, c t = g.1` at the supremum threshold `q`.
4. **Cramer's rule vertex bound & `BitstringEncoding` length bounds**:
   - Every bounded integer polytope attains its coordinate maximum at a rational vertex whose
     denominator divides a `k × k` submatrix determinant (bounded by `k! * B^k` via Leibniz).
   - Decoupling active sets `(B_θ, T₀, T₁)` gives `q ∈ ℚ` with `0 ≤ q ≤ M` and `q.den ≤ M`
     for `M = 2 ^ p.eval (BitstringEncoding.bitEncode g).length`, closing `H2`.
-/

open ComplexityTheory Arxiv.«2610.08796» BigOperators

namespace OMA.R2H3R1H2

private lemma sum_subtype_ite {α : Type*} [Fintype α] (P : α → Prop) [DecidablePred P]
    (f : {x : α // P x} → ℝ) :
    ∑ x : {x : α // P x}, f x = ∑ x : α, if h : P x then f ⟨x, h⟩ else 0 := by
  classical
  calc ∑ x : {x : α // P x}, f x
      = ∑ x ∈ Finset.univ.filter P, if h : P x then f ⟨x, h⟩ else 0 := by
          refine Finset.sum_bij (fun x _ => x.1) ?_ ?_ ?_ ?_
          · intro x _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.2⟩
          · intro x1 _ x2 _ h; exact Subtype.ext h
          · intro x hx; exact ⟨⟨x, (Finset.mem_filter.mp hx).2⟩, Finset.mem_univ _, rfl⟩
          · intro x _; simp [x.2]
    _ = ∑ x : α, if h : P x then f ⟨x, h⟩ else 0 := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun x _ => by by_cases h : P x <;> simp [h]

private lemma natAbs_finset_prod {ι : Type*} (s : Finset ι) (f : ι → ℤ) :
    (∏ i ∈ s, f i).natAbs = ∏ i ∈ s, (f i).natAbs := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, Int.natAbs_mul, ih]

private lemma sum_fin_get_eq_list_sum {α : Type*} (l : List α) (f : α → ℕ) :
    ∑ i : Fin l.length, f (l.get i) = (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.length_cons, Fin.sum_univ_succ, List.get_eq_getElem, List.map_cons,
      List.sum_cons] at ih ⊢
    exact congrArg (f a + ·) ih


/- ## Section 1: Fourier–Motzkin Elimination, Farkas, Hall, and Bipartite LP Duality -/

section FourierMotzkin

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Fourier–Motzkin elimination / Farkas alternative for finite linear inequality systems
`∑ j, a i j * x j ≤ b i` over any strictly ordered field `K`. -/
theorem fourier_motzkin :
    ∀ (n : ℕ) {m : ℕ} (a : Fin m → Fin n → K) (b : Fin m → K),
      (∃ x : Fin n → K, ∀ i : Fin m, ∑ j : Fin n, a i j * x j ≤ b i) ∨
      (∃ w : Fin m → K,
        (∀ i, 0 ≤ w i) ∧
        (∀ j : Fin n, ∑ i : Fin m, w i * a i j = 0) ∧
        ∑ i : Fin m, w i * b i < 0)
  | 0, m, a, b => by
    by_cases h : ∀ i : Fin m, 0 ≤ b i
    · left
      refine ⟨Fin.elim0, fun i => ?_⟩
      simpa using h i
    · right
      push Not at h
      obtain ⟨i₀, hi₀⟩ := h
      refine ⟨Pi.single i₀ (1 : K), ?_, fun j => Fin.elim0 j, ?_⟩
      · intro i
        by_cases hi : i = i₀
        · subst hi; simp
        · simp [Pi.single_eq_of_ne hi]
      · rw [Finset.sum_eq_single i₀]
        · simp [hi₀]
        · intro i _ hi; simp [Pi.single_eq_of_ne hi]
        · intro habs; exact absurd (Finset.mem_univ _) habs
  | n + 1, m, a, b => by
    classical
    let Z : Finset (Fin m) := Finset.univ.filter fun i => a i 0 = 0
    let P : Finset (Fin m) := Finset.univ.filter fun i => 0 < a i 0
    let N : Finset (Fin m) := Finset.univ.filter fun i => a i 0 < 0
    let Idx := {i : Fin m // i ∈ Z} ⊕ ({i : Fin m // i ∈ P} × {k : Fin m // k ∈ N})
    let e := Fintype.equivFin Idx
    let a' : Fin (Fintype.card Idx) → Fin n → K := fun r j =>
      match e.symm r with
      | Sum.inl i => a i.1 j.succ
      | Sum.inr (i, k) => (-a k.1 0) * a i.1 j.succ + a i.1 0 * a k.1 j.succ
    let b' : Fin (Fintype.card Idx) → K := fun r =>
      match e.symm r with
      | Sum.inl i => b i.1
      | Sum.inr (i, k) => (-a k.1 0) * b i.1 + a i.1 0 * b k.1
    rcases fourier_motzkin n a' b' with ⟨y, hy⟩ | ⟨w', hw'_nn, hw'_eq, hw'_lt⟩
    · left
      have hZ : ∀ i ∈ Z, ∑ j : Fin n, a i j.succ * y j ≤ b i := by
        intro i hi
        have := hy (e (Sum.inl ⟨i, hi⟩))
        simpa [a', b'] using this
      have hPN' : ∀ i ∈ P, ∀ k ∈ N,
          (b k - ∑ j : Fin n, a k j.succ * y j) / a k 0 ≤
          (b i - ∑ j : Fin n, a i j.succ * y j) / a i 0 := by
        intro i hi k hk
        have hi0 : 0 < a i 0 := (Finset.mem_filter.mp hi).2
        have hk0 : a k 0 < 0 := (Finset.mem_filter.mp hk).2
        have hkneg : 0 < -a k 0 := neg_pos.mpr hk0
        have hcomb := hy (e (Sum.inr (⟨i, hi⟩, ⟨k, hk⟩)))
        simp only [a', b', Equiv.symm_apply_apply] at hcomb
        have hrew :
            ∑ j : Fin n, ((-a k 0) * a i j.succ + a i 0 * a k j.succ) * y j =
            (-a k 0) * (∑ j : Fin n, a i j.succ * y j) +
            a i 0 * (∑ j : Fin n, a k j.succ * y j) := by
          simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
        rw [hrew] at hcomb
        have hmul : 0 < a i 0 * (-a k 0) := mul_pos hi0 hkneg
        have hdiff : 0 ≤ (b i - ∑ j : Fin n, a i j.succ * y j) / a i 0 -
            (b k - ∑ j : Fin n, a k j.succ * y j) / a k 0 := by
          have hcalc : (a i 0 * (-a k 0)) *
              ((b i - ∑ j : Fin n, a i j.succ * y j) / a i 0 -
               (b k - ∑ j : Fin n, a k j.succ * y j) / a k 0) =
              (-a k 0) * (b i - ∑ j : Fin n, a i j.succ * y j) +
              a i 0 * (b k - ∑ j : Fin n, a k j.succ * y j) := by
            field_simp [ne_of_gt hi0, ne_of_lt hk0]
            ring
          have hrhs : 0 ≤ (-a k 0) * (b i - ∑ j : Fin n, a i j.succ * y j) +
              a i 0 * (b k - ∑ j : Fin n, a k j.succ * y j) := by linarith
          nlinarith
        linarith
      let U : Fin m → K := fun i => (b i - ∑ j : Fin n, a i j.succ * y j) / a i 0
      let x0 : K :=
        if hP : P.Nonempty then P.inf' hP U
        else if hN : N.Nonempty then N.sup' hN U
        else 0
      have hx0_P : ∀ i ∈ P, x0 ≤ U i := by
        intro i hi
        have hP : P.Nonempty := ⟨i, hi⟩
        simp only [x0, dif_pos hP]
        exact Finset.inf'_le U hi
      have hx0_N : ∀ k ∈ N, U k ≤ x0 := by
        intro k hk
        by_cases hP : P.Nonempty
        · simp only [x0, dif_pos hP]
          exact Finset.le_inf' hP U (fun i hi => hPN' i hi k hk)
        · have hN : N.Nonempty := ⟨k, hk⟩
          simp only [x0, dif_neg hP, dif_pos hN]
          exact Finset.le_sup' U hk
      refine ⟨Fin.cons x0 y, fun i => ?_⟩
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rcases lt_trichotomy (a i 0) 0 with hlt | heq | hgt
      · have hiN : i ∈ N := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩
        have hle := hx0_N i hiN
        have hneg : 0 < -a i 0 := neg_pos.mpr hlt
        have hcalc : (-a i 0) * U i = -(b i - ∑ j : Fin n, a i j.succ * y j) := by
          simp only [U]
          field_simp [ne_of_lt hlt]
        have : (-a i 0) * U i ≤ (-a i 0) * x0 := mul_le_mul_of_nonneg_left hle (le_of_lt hneg)
        linarith
      · have hiZ : i ∈ Z := Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq⟩
        rw [heq, zero_mul, zero_add]
        exact hZ i hiZ
      · have hiP : i ∈ P := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt⟩
        have hle := hx0_P i hiP
        have hcalc : a i 0 * U i = b i - ∑ j : Fin n, a i j.succ * y j := by
          simp only [U]
          field_simp [ne_of_gt hgt]
        have : a i 0 * x0 ≤ a i 0 * U i := mul_le_mul_of_nonneg_left hle (le_of_lt hgt)
        linarith
    · right
      let wZ : {i : Fin m // i ∈ Z} → K := fun i => w' (e (Sum.inl i))
      let wPN : {i : Fin m // i ∈ P} → {k : Fin m // k ∈ N} → K :=
        fun i k => w' (e (Sum.inr (i, k)))
      let w : Fin m → K := fun r =>
        if hZ : r ∈ Z then wZ ⟨r, hZ⟩
        else if hP : r ∈ P then ∑ k : {k : Fin m // k ∈ N}, wPN ⟨r, hP⟩ k * (-a k.1 0)
        else if hN : r ∈ N then ∑ i : {i : Fin m // i ∈ P}, wPN i ⟨r, hN⟩ * a i.1 0
        else 0
      have hw_nn : ∀ r, 0 ≤ w r := by
        intro r
        dsimp only [w]
        split_ifs with hZ hP hN
        · exact hw'_nn _
        · exact Finset.sum_nonneg fun k _ => mul_nonneg (hw'_nn _)
            (le_of_lt (neg_pos.mpr (Finset.mem_filter.mp k.2).2))
        · exact Finset.sum_nonneg fun i _ => mul_nonneg (hw'_nn _)
            (le_of_lt (Finset.mem_filter.mp i.2).2)
        · exact le_rfl
      have hsum_split : ∀ f : Fin m → K,
          ∑ r : Fin m, w r * f r =
          (∑ i : {i : Fin m // i ∈ Z}, wZ i * f i.1) +
          ∑ i : {i : Fin m // i ∈ P}, ∑ k : {k : Fin m // k ∈ N},
            wPN i k * ((-a k.1 0) * f i.1 + a i.1 0 * f k.1) := by
        intro f
        have hpart : (Finset.univ : Finset (Fin m)) = Z ∪ (P ∪ N) := by
          ext r
          simp only [Finset.mem_univ, Finset.mem_union, Z, P, N, Finset.mem_filter, true_and,
            true_iff]
          rcases lt_trichotomy (a r 0) 0 with h | h | h
          · exact Or.inr (Or.inr h)
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
        have hdisjPN : Disjoint P N := by
          rw [Finset.disjoint_left]
          intro r hrP hrN
          have h1 := (Finset.mem_filter.mp hrP).2
          have h2 := (Finset.mem_filter.mp hrN).2
          linarith
        have hdisjZ : Disjoint Z (P ∪ N) := by
          rw [Finset.disjoint_left]
          intro r hrZ hrPN
          have h0 := (Finset.mem_filter.mp hrZ).2
          rcases Finset.mem_union.mp hrPN with hrP | hrN
          · linarith [(Finset.mem_filter.mp hrP).2]
          · linarith [(Finset.mem_filter.mp hrN).2]
        rw [hpart, Finset.sum_union hdisjZ, Finset.sum_union hdisjPN]
        have h1 : ∑ r ∈ Z, w r * f r = ∑ i : {i : Fin m // i ∈ Z}, wZ i * f i.1 := by
          rw [← Finset.sum_coe_sort Z]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [w, dif_pos i.2]
        have h2 : ∑ r ∈ P, w r * f r =
            ∑ i : {i : Fin m // i ∈ P}, ∑ k : {k : Fin m // k ∈ N},
              wPN i k * ((-a k.1 0) * f i.1) := by
          rw [← Finset.sum_coe_sort P]
          refine Finset.sum_congr rfl fun i _ => ?_
          have hniZ : i.1 ∉ Z := fun h => by
            linarith [(Finset.mem_filter.mp h).2, (Finset.mem_filter.mp i.2).2]
          simp only [w, dif_neg hniZ, dif_pos i.2, Finset.sum_mul, mul_assoc]
        have h3 : ∑ r ∈ N, w r * f r =
            ∑ i : {i : Fin m // i ∈ P}, ∑ k : {k : Fin m // k ∈ N},
              wPN i k * (a i.1 0 * f k.1) := by
          rw [← Finset.sum_coe_sort N, Finset.sum_comm]
          refine Finset.sum_congr rfl fun k _ => ?_
          have hnkZ : k.1 ∉ Z := fun h => by
            linarith [(Finset.mem_filter.mp h).2, (Finset.mem_filter.mp k.2).2]
          have hnkP : k.1 ∉ P := fun h => by
            linarith [(Finset.mem_filter.mp h).2, (Finset.mem_filter.mp k.2).2]
          simp only [w, dif_neg hnkZ, dif_neg hnkP, dif_pos k.2, Finset.sum_mul, mul_assoc]
        rw [h1, h2, h3]
        congr 1
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        ring
      have hsum_e : ∀ (gZ : {i : Fin m // i ∈ Z} → K)
          (gPN : {i : Fin m // i ∈ P} × {k : Fin m // k ∈ N} → K),
          (∑ i : {i : Fin m // i ∈ Z}, wZ i * gZ i) +
          (∑ i : {i : Fin m // i ∈ P}, ∑ k : {k : Fin m // k ∈ N}, wPN i k * gPN (i, k)) =
          ∑ r : Fin (Fintype.card Idx), w' r *
            (match e.symm r with | Sum.inl i => gZ i | Sum.inr p => gPN p) := by
        intro gZ gPN
        rw [← e.sum_comp]
        dsimp only [Idx]
        simp only [Equiv.symm_apply_apply, Fintype.sum_sum_type, Fintype.sum_prod_type]
        rfl
      refine ⟨w, hw_nn, ?_, ?_⟩
      · intro j
        refine Fin.cases ?_ ?_ j
        · rw [hsum_split (fun r => a r 0)]
          have hZ0 : ∑ i : {i : Fin m // i ∈ Z}, wZ i * a i.1 0 = 0 :=
            Finset.sum_eq_zero fun i _ => by rw [(Finset.mem_filter.mp i.2).2, mul_zero]
          have hPN0 : ∑ i : {i : Fin m // i ∈ P}, ∑ k : {k : Fin m // k ∈ N},
              wPN i k * ((-a k.1 0) * a i.1 0 + a i.1 0 * a k.1 0) = 0 :=
            Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun k _ => by ring
          rw [hZ0, hPN0, add_zero]
        · intro j'
          rw [hsum_split (fun r => a r j'.succ)]
          rw [hsum_e (fun i => a i.1 j'.succ)
            (fun p => (-a p.2.1 0) * a p.1.1 j'.succ + a p.1.1 0 * a p.2.1 j'.succ)]
          convert hw'_eq j' using 1
          refine Finset.sum_congr rfl fun r _ => by cases h : e.symm r <;> simp [a', h]
      · rw [hsum_split b]
        rw [hsum_e (fun i => b i.1) (fun p => (-a p.2.1 0) * b p.1.1 + a p.1.1 0 * b p.2.1)]
        convert hw'_lt using 1
        refine Finset.sum_congr rfl fun r _ => by cases h : e.symm r <;> simp [b', h]

end FourierMotzkin

/-- A finite rational linear inequality system feasible over `ℝ` is feasible over `ℚ`. -/
theorem rat_of_real_feasible {m n : ℕ} (a : Fin m → Fin n → ℚ) (b : Fin m → ℚ)
    (hreal : ∃ x : Fin n → ℝ, ∀ i : Fin m, ∑ j : Fin n, (a i j : ℝ) * x j ≤ (b i : ℝ)) :
    ∃ q : Fin n → ℚ, ∀ i : Fin m, ∑ j : Fin n, a i j * q j ≤ b i := by
  rcases fourier_motzkin n a b with hq | ⟨w, hw_nn, hw_eq, hw_lt⟩
  · exact hq
  · exfalso
    obtain ⟨x, hx⟩ := hreal
    have h1 : ∑ i : Fin m, (w i : ℝ) * (∑ j : Fin n, (a i j : ℝ) * x j) ≤
        ∑ i : Fin m, (w i : ℝ) * (b i : ℝ) := by
      refine Finset.sum_le_sum fun i _ => ?_
      exact mul_le_mul_of_nonneg_left (hx i) (Rat.cast_nonneg.mpr (hw_nn i))
    have h0 : ∑ i : Fin m, (w i : ℝ) * (∑ j : Fin n, (a i j : ℝ) * x j) = 0 := by
      calc ∑ i : Fin m, (w i : ℝ) * (∑ j : Fin n, (a i j : ℝ) * x j)
          = ∑ i : Fin m, ∑ j : Fin n, ((w i * a i j : ℚ) : ℝ) * x j := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun j _ => by push_cast; ring
        _ = ∑ j : Fin n, (∑ i : Fin m, ((w i * a i j : ℚ) : ℝ)) * x j := by
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun j _ => by rw [Finset.sum_mul]
        _ = ∑ j : Fin n, ((∑ i : Fin m, w i * a i j : ℚ) : ℝ) * x j := by
              refine Finset.sum_congr rfl fun j _ => by push_cast; rfl
        _ = 0 := by
              refine Finset.sum_eq_zero fun j _ => by rw [hw_eq j]; simp
    have hlt : ∑ i : Fin m, (w i : ℝ) * (b i : ℝ) < 0 := by
      have : ∑ i : Fin m, (w i : ℝ) * (b i : ℝ) = ((∑ i : Fin m, w i * b i : ℚ) : ℝ) := by
        push_cast; rfl
      rw [this]
      exact_mod_cast hw_lt
    linarith

/-- Finite layer-cake lemma: if `u ≥ 0`, `v ≥ 0`, `E θ t → v t ≤ u θ`, and
`∑ θ, π θ * u θ < ∑ t, s t * v t`, then some subset `R` violates Hall's condition. -/
theorem layer_cake_hall {m n : ℕ} (π : Fin m → ℝ) (s : Fin n → ℝ) (E : Fin m → Fin n → Prop)
    [DecidableRel E] (hπ : ∀ θ, 0 ≤ π θ) :
    ∀ (k : ℕ) (u : Fin m → ℝ) (v : Fin n → ℝ),
      ((Finset.univ.image v).filter fun x => 0 < x).card ≤ k →
      (∀ θ, 0 ≤ u θ) → (∀ t, 0 ≤ v t) → (∀ θ t, E θ t → v t ≤ u θ) →
      ∑ θ : Fin m, π θ * u θ < ∑ t : Fin n, s t * v t →
      ∃ R : Finset (Fin n),
        ∑ θ ∈ Finset.univ.filter (fun θ => ∃ t ∈ R, E θ t), π θ < ∑ t ∈ R, s t
  | 0, u, v, hcard, hu, hv, _, hlt => by
    exfalso
    have hv0 : ∀ t, v t = 0 := by
      intro t
      by_contra hne
      have hpos : 0 < v t := lt_of_le_of_ne (hv t) (Ne.symm hne)
      have hmem : v t ∈ (Finset.univ.image v).filter fun x => 0 < x :=
        Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem v (Finset.mem_univ t), hpos⟩
      have := Finset.card_pos.mpr ⟨v t, hmem⟩
      omega
    have hsumv : ∑ t : Fin n, s t * v t = 0 :=
      Finset.sum_eq_zero fun t _ => by rw [hv0 t, mul_zero]
    have hsumu : 0 ≤ ∑ θ : Fin m, π θ * u θ :=
      Finset.sum_nonneg fun θ _ => mul_nonneg (hπ θ) (hu θ)
    linarith
  | k + 1, u, v, hcard, hu, hv, hE, hlt => by
    classical
    let V := (Finset.univ.image v).filter fun x => 0 < x
    by_cases hV : V.Nonempty
    · let δ := V.min' hV
      have hδ_pos : 0 < δ := (Finset.mem_filter.mp (Finset.min'_mem V hV)).2
      let R : Finset (Fin n) := Finset.univ.filter fun t => δ ≤ v t
      let NR : Finset (Fin m) := Finset.univ.filter fun θ => ∃ t ∈ R, E θ t
      by_cases hR : ∑ θ ∈ NR, π θ < ∑ t ∈ R, s t
      · exact ⟨R, hR⟩
      · push Not at hR
        let v' : Fin n → ℝ := fun t => if t ∈ R then v t - δ else 0
        let u' : Fin m → ℝ := fun θ => if θ ∈ NR then u θ - δ else u θ
        have hv'_nn : ∀ t, 0 ≤ v' t := by
          intro t; dsimp only [v']; split_ifs with ht
          · linarith [(Finset.mem_filter.mp ht).2]
          · exact le_rfl
        have hu'_nn : ∀ θ, 0 ≤ u' θ := by
          intro θ; dsimp only [u']; split_ifs with hθ
          · obtain ⟨t, htR, hEt⟩ := (Finset.mem_filter.mp hθ).2
            linarith [(Finset.mem_filter.mp htR).2, hE θ t hEt]
          · exact hu θ
        have hE' : ∀ θ t, E θ t → v' t ≤ u' θ := by
          intro θ t hEt
          by_cases ht : t ∈ R
          · have hθ : θ ∈ NR := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨t, ht, hEt⟩⟩
            simp only [v', u', if_pos ht, if_pos hθ]
            linarith [hE θ t hEt]
          · simp only [v', if_neg ht]
            exact hu'_nn θ
        have hv_eq : ∀ t, v t = v' t + if t ∈ R then δ else 0 := by
          intro t
          dsimp only [v']
          split_ifs with ht
          · ring
          · simp only [zero_add]
            by_contra hne
            have hpos : 0 < v t := lt_of_le_of_ne (hv t) (Ne.symm hne)
            have hmem : v t ∈ V :=
              Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem v (Finset.mem_univ t), hpos⟩
            have hle : δ ≤ v t := Finset.min'_le V (v t) hmem
            exact ht (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hle⟩)
        have hu_eq : ∀ θ, u θ = u' θ + if θ ∈ NR then δ else 0 := by
          intro θ; dsimp only [u']; split_ifs <;> ring
        have hsum_v : ∑ t : Fin n, s t * v t =
            (∑ t : Fin n, s t * v' t) + δ * ∑ t ∈ R, s t := by
          calc ∑ t : Fin n, s t * v t
              = ∑ t : Fin n, (s t * v' t + if t ∈ R then s t * δ else 0) := by
                  refine Finset.sum_congr rfl fun t _ => ?_
                  rw [hv_eq t]; split_ifs <;> ring
            _ = (∑ t : Fin n, s t * v' t) + ∑ t ∈ R, s t * δ := by
                  rw [Finset.sum_add_distrib, ← Finset.sum_filter]
                  congr 1; simp
            _ = (∑ t : Fin n, s t * v' t) + δ * ∑ t ∈ R, s t := by
                  rw [Finset.mul_sum]; congr 1
                  refine Finset.sum_congr rfl fun t _ => by ring
        have hsum_u : ∑ θ : Fin m, π θ * u θ =
            (∑ θ : Fin m, π θ * u' θ) + δ * ∑ θ ∈ NR, π θ := by
          calc ∑ θ : Fin m, π θ * u θ
              = ∑ θ : Fin m, (π θ * u' θ + if θ ∈ NR then π θ * δ else 0) := by
                  refine Finset.sum_congr rfl fun θ _ => ?_
                  rw [hu_eq θ]; split_ifs <;> ring
            _ = (∑ θ : Fin m, π θ * u' θ) + ∑ θ ∈ NR, π θ * δ := by
                  rw [Finset.sum_add_distrib, ← Finset.sum_filter]
                  congr 1; simp
            _ = (∑ θ : Fin m, π θ * u' θ) + δ * ∑ θ ∈ NR, π θ := by
                  rw [Finset.mul_sum]; congr 1
                  refine Finset.sum_congr rfl fun θ _ => by ring
        have hlt' : ∑ θ : Fin m, π θ * u' θ < ∑ t : Fin n, s t * v' t := by nlinarith
        have hcard' : ((Finset.univ.image v').filter fun x => 0 < x).card ≤ k := by
          let V' := (Finset.univ.image v').filter fun x => 0 < x
          have hsub : V'.image (· + δ) ⊆ V.erase δ := by
            intro y hy
            obtain ⟨x, hxV', rfl⟩ := Finset.mem_image.mp hy
            obtain ⟨hximg, hxpos⟩ := Finset.mem_filter.mp hxV'
            obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hximg
            have htR : t ∈ R := by
              by_contra hnt
              simp only [v', if_neg hnt] at hxpos
              linarith
            have hvt : v' t + δ = v t := by simp [v', if_pos htR]
            rw [hvt]
            refine Finset.mem_erase.mpr ⟨by linarith, Finset.mem_filter.mpr
              ⟨Finset.mem_image_of_mem v (Finset.mem_univ t), by linarith⟩⟩
          have h1 : V'.card = (V'.image (· + δ)).card :=
            (Finset.card_image_of_injective V' (add_left_injective δ)).symm
          have h2 : (V'.image (· + δ)).card ≤ (V.erase δ).card := Finset.card_le_card hsub
          have h3 : (V.erase δ).card = V.card - 1 := Finset.card_erase_of_mem (Finset.min'_mem V hV)
          have h4 : 1 ≤ V.card := Finset.one_le_card.mpr hV
          have hVle : V.card ≤ k + 1 := hcard
          change V'.card ≤ k
          omega
        exact layer_cake_hall π s E hπ k u' v' hcard' hu'_nn hv'_nn hE' hlt'
    · exfalso
      -- Actually if V is empty, v = 0 identically, contradicting hlt directly:
      have hv0 : ∀ t, v t = 0 := by
        intro t
        by_contra hne
        have hpos : 0 < v t := lt_of_le_of_ne (hv t) (Ne.symm hne)
        exact hV ⟨v t, Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem v (Finset.mem_univ t), hpos⟩⟩
      have hsumv : ∑ t : Fin n, s t * v t = 0 :=
        Finset.sum_eq_zero fun t _ => by rw [hv0 t, mul_zero]
      have hsumu : 0 ≤ ∑ θ : Fin m, π θ * u θ :=
        Finset.sum_nonneg fun θ _ => mul_nonneg (hπ θ) (hu θ)
      linarith

/-- Hall's bipartite supply-demand theorem via Fourier–Motzkin + finite layer-cake. -/
theorem farkas_hall_flow {m n : ℕ} (π : Fin m → ℝ) (s : Fin n → ℝ) (E : Fin m → Fin n → Prop)
    [DecidableRel E] (hπ : ∀ θ, 0 ≤ π θ) (hE_nonempty : ∀ θ, ∃ t, E θ t)
    (hhall : ∀ R : Finset (Fin n),
      ∑ t ∈ R, s t ≤ ∑ θ ∈ Finset.univ.filter (fun θ => ∃ t ∈ R, E θ t), π θ) :
    ∃ f : Fin m → Fin n → ℝ,
      (∀ θ t, 0 ≤ f θ t) ∧ (∀ θ t, ¬ E θ t → f θ t = 0) ∧
      (∀ θ, ∑ t : Fin n, f θ t = π θ) ∧ (∀ t, s t ≤ ∑ θ : Fin m, f θ t) := by
  classical
  -- First obtain a flow with `∑_t f θ t ≤ π θ` and `s t ≤ ∑_θ f θ t`
  let Edge := {p : Fin m × Fin n // E p.1 p.2}
  let eV := Fintype.equivFin Edge
  let Row := Edge ⊕ (Fin m ⊕ Fin n)
  let eR := Fintype.equivFin Row
  let a : Fin (Fintype.card Row) → Fin (Fintype.card Edge) → ℝ := fun r c =>
    let p := eV.symm c
    match eR.symm r with
    | Sum.inl q => if p = q then -1 else 0
    | Sum.inr (Sum.inl θ) => if p.1.1 = θ then 1 else 0
    | Sum.inr (Sum.inr t) => if p.1.2 = t then -1 else 0
  let b : Fin (Fintype.card Row) → ℝ := fun r =>
    match eR.symm r with
    | Sum.inl _ => 0
    | Sum.inr (Sum.inl θ) => π θ
    | Sum.inr (Sum.inr t) => -s t
  rcases fourier_motzkin (Fintype.card Edge) a b with ⟨x, hx⟩ | ⟨w, hw_nn, hw_eq, hw_lt⟩
  · let f0 : Fin m → Fin n → ℝ := fun θ t =>
      if h : E θ t then x (eV ⟨(θ, t), h⟩) else 0
    have hf0_nn : ∀ θ t, 0 ≤ f0 θ t := by
      intro θ t; dsimp only [f0]; split_ifs with h
      · have := hx (eR (Sum.inl ⟨(θ, t), h⟩))
        simp only [a, b, Equiv.symm_apply_apply] at this
        have hsum : ∑ c : Fin (Fintype.card Edge),
            (if eV.symm c = ⟨(θ, t), h⟩ then (-1 : ℝ) else 0) * x c = -x (eV ⟨(θ, t), h⟩) := by
          rw [Finset.sum_eq_single (eV ⟨(θ, t), h⟩)]
          · simp
          · intro c _ hc
            have : eV.symm c ≠ ⟨(θ, t), h⟩ := fun heq => hc (by rw [← heq]; simp)
            simp [this]
          · intro habs; exact absurd (Finset.mem_univ _) habs
        linarith
      · exact le_rfl
    have hf0_row : ∀ θ, ∑ t : Fin n, f0 θ t ≤ π θ := by
      intro θ
      have := hx (eR (Sum.inr (Sum.inl θ)))
      simp only [a, b, Equiv.symm_apply_apply] at this
      have hsum : ∑ c : Fin (Fintype.card Edge),
          (if (eV.symm c).1.1 = θ then (1 : ℝ) else 0) * x c = ∑ t : Fin n, f0 θ t := by
        rw [← eV.sum_comp]
        simp only [Equiv.symm_apply_apply]
        calc ∑ p : Edge, (if p.1.1 = θ then (1 : ℝ) else 0) * x (eV p)
            = ∑ p : Fin m × Fin n, if h : E p.1 p.2 then
                (if p.1 = θ then (1 : ℝ) else 0) * x (eV ⟨p, h⟩) else 0 := by
                exact sum_subtype_ite _ _
          _ = ∑ θ' : Fin m, ∑ t : Fin n, if h : E θ' t then
                (if θ' = θ then (1 : ℝ) else 0) * x (eV ⟨(θ', t), h⟩) else 0 :=
                Fintype.sum_prod_type _
          _ = ∑ t : Fin n, f0 θ t := by
                rw [Finset.sum_eq_single θ]
                · refine Finset.sum_congr rfl fun t _ => by dsimp only [f0]; by_cases hE : E θ t <;> simp [hE]
                · intro θ' _ hne; refine Finset.sum_eq_zero fun t _ => by split_ifs <;> simp
                · intro habs; exact absurd (Finset.mem_univ _) habs
      linarith
    have hf0_col : ∀ t, s t ≤ ∑ θ : Fin m, f0 θ t := by
      intro t
      have := hx (eR (Sum.inr (Sum.inr t)))
      simp only [a, b, Equiv.symm_apply_apply] at this
      have hsum : ∑ c : Fin (Fintype.card Edge),
          (if (eV.symm c).1.2 = t then (-1 : ℝ) else 0) * x c = -∑ θ : Fin m, f0 θ t := by
        rw [← eV.sum_comp]
        simp only [Equiv.symm_apply_apply]
        calc ∑ p : Edge, (if p.1.2 = t then (-1 : ℝ) else 0) * x (eV p)
            = ∑ p : Fin m × Fin n, if h : E p.1 p.2 then
                (if p.2 = t then (-1 : ℝ) else 0) * x (eV ⟨p, h⟩) else 0 := by
                exact sum_subtype_ite _ _
          _ = ∑ θ : Fin m, ∑ t' : Fin n, if h : E θ t' then
                (if t' = t then (-1 : ℝ) else 0) * x (eV ⟨(θ, t'), h⟩) else 0 :=
                Fintype.sum_prod_type _
          _ = ∑ θ : Fin m, -f0 θ t := by
                refine Finset.sum_congr rfl fun θ _ => ?_
                rw [Finset.sum_eq_single t]
                · dsimp only [f0]; by_cases hE : E θ t <;> simp [hE]
                · intro t' _ hne; split_ifs <;> simp
                · intro habs; exact absurd (Finset.mem_univ _) habs
          _ = -∑ θ : Fin m, f0 θ t := by rw [Finset.sum_neg_distrib]
      linarith
    -- Top up each type θ onto an arbitrary valid edge `t_θ`
    choose t0 ht0 using hE_nonempty
    let f : Fin m → Fin n → ℝ := fun θ t =>
      f0 θ t + if t = t0 θ then π θ - ∑ t' : Fin n, f0 θ t' else 0
    refine ⟨f, ?_, ?_, ?_, ?_⟩
    · intro θ t; dsimp only [f]; split_ifs
      · linarith [hf0_nn θ t, hf0_row θ]
      · linarith [hf0_nn θ t]
    · intro θ t hnE; dsimp only [f]
      have hne : t ≠ t0 θ := fun h => hnE (h ▸ ht0 θ)
      simp [f0, hnE, hne]
    · intro θ
      dsimp only [f]
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ (t0 θ)]
      simp
    · intro t
      have : ∑ θ : Fin m, f0 θ t ≤ ∑ θ : Fin m, f θ t := by
        refine Finset.sum_le_sum fun θ _ => ?_
        dsimp only [f]; split_ifs
        · linarith [hf0_row θ]
        · linarith
      linarith [hf0_col t]
  · exfalso
    let u : Fin m → ℝ := fun θ => w (eR (Sum.inr (Sum.inl θ)))
    let v : Fin n → ℝ := fun t => w (eR (Sum.inr (Sum.inr t)))
    have hu_nn : ∀ θ, 0 ≤ u θ := fun θ => hw_nn _
    have hv_nn : ∀ t, 0 ≤ v t := fun t => hw_nn _
    have hE_le : ∀ θ t, E θ t → v t ≤ u θ := by
      intro θ t hEt
      have hq := hw_eq (eV ⟨(θ, t), hEt⟩)
      rw [← eR.sum_comp] at hq
      dsimp only [Row] at hq
      simp only [a, Equiv.symm_apply_apply, Fintype.sum_sum_type] at hq
      have h1 : ∑ q : Edge, w (eR (Sum.inl q)) *
          (if (⟨(θ, t), hEt⟩ : Edge) = q then (-1 : ℝ) else 0) =
          -w (eR (Sum.inl ⟨(θ, t), hEt⟩)) := by
        rw [Finset.sum_eq_single ⟨(θ, t), hEt⟩]
        · simp
        · intro q _ hne; simp [Ne.symm hne]
        · intro habs; exact absurd (Finset.mem_univ _) habs
      have h2 : ∑ θ' : Fin m, w (eR (Sum.inr (Sum.inl θ'))) *
          (if θ = θ' then (1 : ℝ) else 0) = u θ := by
        rw [Finset.sum_eq_single θ]
        · simp [u]
        · intro θ' _ hne; simp [Ne.symm hne]
        · intro habs; exact absurd (Finset.mem_univ _) habs
      have h3 : ∑ t' : Fin n, w (eR (Sum.inr (Sum.inr t'))) *
          (if t = t' then (-1 : ℝ) else 0) = -v t := by
        rw [Finset.sum_eq_single t]
        · simp [v]
        · intro t' _ hne; simp [Ne.symm hne]
        · intro habs; exact absurd (Finset.mem_univ _) habs
      rw [h1, h2, h3] at hq
      linarith [hw_nn (eR (Sum.inl ⟨(θ, t), hEt⟩))]
    have hlt_uv : ∑ θ : Fin m, π θ * u θ < ∑ t : Fin n, s t * v t := by
      rw [← eR.sum_comp] at hw_lt
      dsimp only [Row] at hw_lt
      simp only [b, Equiv.symm_apply_apply, Fintype.sum_sum_type, mul_zero,
        Finset.sum_const_zero, zero_add, mul_neg, Finset.sum_neg_distrib] at hw_lt
      have h1 : ∑ θ : Fin m, π θ * u θ = ∑ θ : Fin m, w (eR (Sum.inr (Sum.inl θ))) * π θ :=
        Finset.sum_congr rfl fun θ _ => by ring
      have h2 : ∑ t : Fin n, s t * v t = ∑ t : Fin n, w (eR (Sum.inr (Sum.inr t))) * s t :=
        Finset.sum_congr rfl fun t _ => by ring
      linarith
    obtain ⟨R, hR⟩ := layer_cake_hall π s E hπ _ u v le_rfl hu_nn hv_nn hE_le hlt_uv
    linarith [hhall R]

/-- Exact strong LP duality for bipartite flow maximization with lower-bound (`eqMode = false`)
or exact-equality (`eqMode = true`) target constraints. -/
theorem lp_duality_flow {m n : ℕ} (eqMode : Bool) (π : Fin m → ℝ) (s : Fin n → ℝ)
    (E : Fin m → Fin n → Prop) [DecidableRel E] (α : Fin m → Fin n → ℝ)
    (hπ : ∀ θ, 0 ≤ π θ)
    (hfeas : ∃ f : Fin m → Fin n → ℝ,
      (∀ θ t, 0 ≤ f θ t) ∧ (∀ θ t, ¬ E θ t → f θ t = 0) ∧
      (∀ θ, ∑ t : Fin n, f θ t = π θ) ∧
      (∀ t, if eqMode then ∑ θ : Fin m, f θ t = s t else s t ≤ ∑ θ : Fin m, f θ t)) :
    ∃ (f : Fin m → Fin n → ℝ) (u : Fin m → ℝ) (z : Fin n → ℝ),
      (∀ θ t, 0 ≤ f θ t) ∧ (∀ θ t, ¬ E θ t → f θ t = 0) ∧
      (∀ θ, ∑ t : Fin n, f θ t = π θ) ∧
      (∀ t, if eqMode then ∑ θ : Fin m, f θ t = s t else s t ≤ ∑ θ : Fin m, f θ t) ∧
      (∀ θ t, E θ t → α θ t + z t ≤ u θ) ∧
      (∀ θ t, 0 < f θ t → α θ t + z t = u θ) := by
  classical
  let P : Set (Fin m → Fin n → ℝ) :=
    {f | (∀ θ t, 0 ≤ f θ t) ∧ (∀ θ t, ¬ E θ t → f θ t = 0) ∧
      (∀ θ, ∑ t : Fin n, f θ t = π θ) ∧
      (∀ t, if eqMode then ∑ θ : Fin m, f θ t = s t else s t ≤ ∑ θ : Fin m, f θ t)}
  have hP_nonempty : P.Nonempty := hfeas
  have hP_compact : IsCompact P := by
    let B : ℝ := ∑ θ : Fin m, π θ
    let Box : Set (Fin m → Fin n → ℝ) :=
      Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Set.Icc 0 B
    have hBox : IsCompact Box := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
    have hsub : P ⊆ Box := by
      intro f hf θ _ t _
      refine ⟨hf.1 θ t, ?_⟩
      have h1 : f θ t ≤ ∑ t' : Fin n, f θ t' :=
        Finset.single_le_sum (fun t' _ => hf.1 θ t') (Finset.mem_univ t)
      have h2 : π θ ≤ B := Finset.single_le_sum (fun θ' _ => hπ θ') (Finset.mem_univ θ)
      linarith [hf.2.2.1 θ]
    have hclosed : IsClosed P := by
      have h1 : IsClosed {f : Fin m → Fin n → ℝ | ∀ θ t, 0 ≤ f θ t} := by
        have heq : {f : Fin m → Fin n → ℝ | ∀ θ t, 0 ≤ f θ t} =
            ⋂ θ : Fin m, ⋂ t : Fin n, {f | (0 : ℝ) ≤ f θ t} := by ext f; simp
        rw [heq]
        exact isClosed_iInter fun θ => isClosed_iInter fun t =>
          isClosed_le continuous_const ((continuous_apply t).comp (continuous_apply θ))
      have h2 : IsClosed {f : Fin m → Fin n → ℝ | ∀ θ t, ¬ E θ t → f θ t = 0} := by
        have heq : {f : Fin m → Fin n → ℝ | ∀ θ t, ¬ E θ t → f θ t = 0} =
            ⋂ θ : Fin m, ⋂ t : Fin n, ⋂ _ : ¬ E θ t, {f | f θ t = (0 : ℝ)} := by ext f; simp
        rw [heq]
        exact isClosed_iInter fun θ => isClosed_iInter fun t => isClosed_iInter fun _ =>
          isClosed_eq ((continuous_apply t).comp (continuous_apply θ)) continuous_const
      have h3 : IsClosed {f : Fin m → Fin n → ℝ | ∀ θ, ∑ t : Fin n, f θ t = π θ} := by
        have heq : {f : Fin m → Fin n → ℝ | ∀ θ, ∑ t : Fin n, f θ t = π θ} =
            ⋂ θ : Fin m, {f | ∑ t : Fin n, f θ t = π θ} := by ext f; simp
        rw [heq]
        exact isClosed_iInter fun θ =>
          isClosed_eq (continuous_finsetSum Finset.univ fun t _ =>
            (continuous_apply t).comp (continuous_apply θ)) continuous_const
      have h4 : IsClosed {f : Fin m → Fin n → ℝ |
          ∀ t, if eqMode then ∑ θ : Fin m, f θ t = s t else s t ≤ ∑ θ : Fin m, f θ t} := by
        have heq : {f : Fin m → Fin n → ℝ |
            ∀ t, if eqMode then ∑ θ : Fin m, f θ t = s t else s t ≤ ∑ θ : Fin m, f θ t} =
            ⋂ t : Fin n, {f | if eqMode then ∑ θ : Fin m, f θ t = s t else s t ≤ ∑ θ : Fin m, f θ t} := by
          ext f; simp
        rw [heq]
        refine isClosed_iInter fun t => ?_
        cases eqMode
        · simpa using isClosed_le continuous_const (continuous_finsetSum Finset.univ fun θ _ =>
            (continuous_apply t).comp (continuous_apply θ))
        · simpa using isClosed_eq (continuous_finsetSum Finset.univ fun θ _ =>
            (continuous_apply t).comp (continuous_apply θ)) continuous_const
      have hP_eq : P = ({f | ∀ θ t, 0 ≤ f θ t} ∩ {f | ∀ θ t, ¬ E θ t → f θ t = 0}) ∩ {f | ∀ θ, ∑ t : Fin n, f θ t = π θ} ∩ {f | ∀ t, if eqMode then ∑ θ : Fin m, f θ t = s t else s t ≤ ∑ θ : Fin m, f θ t} := by ext f; simp [P, and_assoc]
      rw [hP_eq]
      exact ((h1.inter h2).inter h3).inter h4
    exact hBox.of_isClosed_subset hclosed hsub
  let obj : (Fin m → Fin n → ℝ) → ℝ := fun f => ∑ θ : Fin m, ∑ t : Fin n, α θ t * f θ t
  have hobj_cont : Continuous obj :=
    continuous_finsetSum _ fun θ _ => continuous_finsetSum _ fun t _ =>
      continuous_const.mul ((continuous_apply t).comp (continuous_apply θ))
  obtain ⟨f, hfP, hfmax⟩ := hP_compact.exists_isMaxOn hP_nonempty hobj_cont.continuousOn
  let M : ℝ := obj f
  -- Dual system in variables `(u : Fin m → ℝ, z : Fin n → ℝ)`:
  -- (1) for each edge `(θ, t)` with `E θ t`: `-u θ + z t ≤ -α θ t`
  -- (2) if `!eqMode`, for each `t`: `-z t ≤ 0`
  -- (3) objective: `∑ θ, π θ * u θ - ∑ t, s t * z t ≤ M`
  let Edge := {p : Fin m × Fin n // E p.1 p.2}
  let eVar := Fintype.equivFin (Fin m ⊕ Fin n)
  let DualRow := Edge ⊕ (Fin n ⊕ Unit)
  let eDR := Fintype.equivFin DualRow
  let aD : Fin (Fintype.card DualRow) → Fin (Fintype.card (Fin m ⊕ Fin n)) → ℝ := fun r c =>
    match eDR.symm r, eVar.symm c with
    | Sum.inl q, Sum.inl θ => if q.1.1 = θ then -1 else 0
    | Sum.inl q, Sum.inr t => if q.1.2 = t then 1 else 0
    | Sum.inr (Sum.inl t), Sum.inl _ => 0
    | Sum.inr (Sum.inl t), Sum.inr t' => if !eqMode ∧ t = t' then -1 else 0
    | Sum.inr (Sum.inr ()), Sum.inl θ => π θ
    | Sum.inr (Sum.inr ()), Sum.inr t => -s t
  let bD : Fin (Fintype.card DualRow) → ℝ := fun r =>
    match eDR.symm r with
    | Sum.inl q => -α q.1.1 q.1.2
    | Sum.inr (Sum.inl _) => 0
    | Sum.inr (Sum.inr ()) => M
  rcases fourier_motzkin (Fintype.card (Fin m ⊕ Fin n)) aD bD with ⟨y, hy⟩ | ⟨w, hw_nn, hw_eq, hw_lt⟩
  · let u : Fin m → ℝ := fun θ => y (eVar (Sum.inl θ))
    let z : Fin n → ℝ := fun t => y (eVar (Sum.inr t))
    have hEdge : ∀ θ t, E θ t → α θ t + z t ≤ u θ := by
      intro θ t hEt
      have h := hy (eDR (Sum.inl ⟨(θ, t), hEt⟩))
      rw [← eVar.sum_comp] at h
      simp only [aD, bD, Equiv.symm_apply_apply, Fintype.sum_sum_type] at h
      have h1 : ∑ θ' : Fin m, (if θ = θ' then (-1 : ℝ) else 0) * y (eVar (Sum.inl θ')) = -u θ := by
        rw [Finset.sum_eq_single θ]
        · simp [u]
        · intro θ' _ hne; simp [Ne.symm hne]
        · intro habs; exact absurd (Finset.mem_univ _) habs
      have h2 : ∑ t' : Fin n, (if t = t' then (1 : ℝ) else 0) * y (eVar (Sum.inr t')) = z t := by
        rw [Finset.sum_eq_single t]
        · simp [z]
        · intro t' _ hne; simp [Ne.symm hne]
        · intro habs; exact absurd (Finset.mem_univ _) habs
      rw [h1, h2] at h
      linarith
    have hz_nn : ∀ t, eqMode = false → 0 ≤ z t := by
      intro t heq
      have h := hy (eDR (Sum.inr (Sum.inl t)))
      rw [← eVar.sum_comp] at h
      simp only [aD, bD, Equiv.symm_apply_apply, Fintype.sum_sum_type, zero_mul,
        Finset.sum_const_zero, zero_add, heq, Bool.not_false, true_and] at h
      have h1 : ∑ t' : Fin n, (if t = t' then (-1 : ℝ) else 0) * y (eVar (Sum.inr t')) = -z t := by
        rw [Finset.sum_eq_single t]
        · simp [z]
        · intro t' _ hne; simp [Ne.symm hne]
        · intro habs; exact absurd (Finset.mem_univ _) habs
      rw [h1] at h
      linarith
    have hDualObj : ∑ θ : Fin m, π θ * u θ - ∑ t : Fin n, s t * z t ≤ M := by
      have h := hy (eDR (Sum.inr (Sum.inr ())))
      rw [← eVar.sum_comp] at h
      simp only [aD, bD, Equiv.symm_apply_apply, Fintype.sum_sum_type, neg_mul,
        Finset.sum_neg_distrib] at h
      simpa [u, z, sub_eq_add_neg] using h
    -- Complementary slackness
    have hslack_nonneg : ∀ θ t, 0 ≤ (u θ - z t - α θ t) * f θ t := by
      intro θ t
      by_cases hEt : E θ t
      · exact mul_nonneg (by linarith [hEdge θ t hEt]) (hfP.1 θ t)
      · rw [hfP.2.1 θ t hEt, mul_zero]
    have hzslack_nonneg : ∀ t, 0 ≤ z t * ((∑ θ : Fin m, f θ t) - s t) := by
      intro t
      cases hmode : eqMode
      · have hge := hfP.2.2.2 t
        simp only [hmode, Bool.false_eq_true, ↓reduceIte] at hge
        exact mul_nonneg (hz_nn t hmode) (by linarith)
      · have heq := hfP.2.2.2 t
        simp only [hmode, ↓reduceIte] at heq
        rw [heq, sub_self, mul_zero]
    have htotal : (∑ θ : Fin m, ∑ t : Fin n, (u θ - z t - α θ t) * f θ t) +
        (∑ t : Fin n, z t * ((∑ θ : Fin m, f θ t) - s t)) ≤ 0 := by
      have hcalc : (∑ θ : Fin m, ∑ t : Fin n, (u θ - z t - α θ t) * f θ t) +
          (∑ t : Fin n, z t * ((∑ θ : Fin m, f θ t) - s t)) =
          (∑ θ : Fin m, π θ * u θ - ∑ t : Fin n, s t * z t) - M := by
        have h1 : ∑ θ : Fin m, ∑ t : Fin n, (u θ - z t - α θ t) * f θ t =
            (∑ θ : Fin m, u θ * ∑ t : Fin n, f θ t) -
            (∑ t : Fin n, z t * ∑ θ : Fin m, f θ t) - M := by
          simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, obj, M]
          congr 2
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun t _ => by rw [Finset.mul_sum]
        have h2 : ∑ θ : Fin m, u θ * ∑ t : Fin n, f θ t = ∑ θ : Fin m, π θ * u θ :=
          Finset.sum_congr rfl fun θ _ => by rw [hfP.2.2.1 θ]; ring
        have h3 : ∑ t : Fin n, z t * ((∑ θ : Fin m, f θ t) - s t) =
            (∑ t : Fin n, z t * ∑ θ : Fin m, f θ t) - ∑ t : Fin n, s t * z t := by
          simp only [mul_sub, Finset.sum_sub_distrib]
          congr 1; refine Finset.sum_congr rfl fun t _ => by ring
        linarith
      linarith
    have hsum_zero : ∑ θ : Fin m, ∑ t : Fin n, (u θ - z t - α θ t) * f θ t = 0 := by
      have ha : 0 ≤ ∑ θ : Fin m, ∑ t : Fin n, (u θ - z t - α θ t) * f θ t :=
        Finset.sum_nonneg fun θ _ => Finset.sum_nonneg fun t _ => hslack_nonneg θ t
      have hb : 0 ≤ ∑ t : Fin n, z t * ((∑ θ : Fin m, f θ t) - s t) :=
        Finset.sum_nonneg fun t _ => hzslack_nonneg t
      linarith
    refine ⟨f, u, z, hfP.1, hfP.2.1, hfP.2.2.1, hfP.2.2.2, hEdge, ?_⟩
    intro θ t hfpos
    have hEt : E θ t := by
      by_contra hnE; linarith [hfP.2.1 θ t hnE]
    have hzero : (u θ - z t - α θ t) * f θ t = 0 := by
      have houter := (Finset.sum_eq_zero_iff_of_nonneg (fun θ' _ =>
        Finset.sum_nonneg fun t' _ => hslack_nonneg θ' t')).mp hsum_zero θ (Finset.mem_univ θ)
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun t' _ => hslack_nonneg θ t')).mp houter t
        (Finset.mem_univ t)
    have hfac : u θ - z t - α θ t = 0 := (mul_eq_zero.mp hzero).resolve_right (ne_of_gt hfpos)
    linarith
  · exfalso
    -- Farkas certificate gives a primal flow beating `M`!
    let g : Fin m → Fin n → ℝ := fun θ t =>
      if h : E θ t then w (eDR (Sum.inl ⟨(θ, t), h⟩)) else 0
    let γ : ℝ := w (eDR (Sum.inr (Sum.inr ())))
    have hg_nn : ∀ θ t, 0 ≤ g θ t := by
      intro θ t; dsimp only [g]; split_ifs; exact hw_nn _; exact le_rfl
    have hγ_nn : 0 ≤ γ := hw_nn _
    have hg_row : ∀ θ, ∑ t : Fin n, g θ t = γ * π θ := by
      intro θ
      have h := hw_eq (eVar (Sum.inl θ))
      rw [← eDR.sum_comp] at h
      dsimp only [DualRow] at h
      simp only [aD, Equiv.symm_apply_apply, Fintype.sum_sum_type, mul_zero,
        Finset.sum_const_zero, zero_add, Fintype.sum_unique] at h
      have h1 : ∑ q : Edge, w (eDR (Sum.inl q)) * (if q.1.1 = θ then (-1 : ℝ) else 0) =
          -∑ t : Fin n, g θ t := by
        calc ∑ q : Edge, w (eDR (Sum.inl q)) * (if q.1.1 = θ then (-1 : ℝ) else 0)
            = ∑ p : Fin m × Fin n, if hE : E p.1 p.2 then
                w (eDR (Sum.inl ⟨p, hE⟩)) * (if p.1 = θ then (-1 : ℝ) else 0) else 0 := by
                exact sum_subtype_ite _ _
          _ = ∑ θ' : Fin m, ∑ t : Fin n, if hE : E θ' t then
                w (eDR (Sum.inl ⟨(θ', t), hE⟩)) * (if θ' = θ then (-1 : ℝ) else 0) else 0 :=
                Fintype.sum_prod_type _
          _ = ∑ t : Fin n, -g θ t := by
                rw [Finset.sum_eq_single θ]
                · refine Finset.sum_congr rfl fun t _ => by dsimp only [g]; by_cases hE : E θ t <;> simp [hE]
                · intro θ' _ hne; refine Finset.sum_eq_zero fun t _ => by split_ifs <;> simp
                · intro habs; exact absurd (Finset.mem_univ _) habs
          _ = -∑ t : Fin n, g θ t := by rw [Finset.sum_neg_distrib]
      rw [h1] at h
      linarith
    have hg_col : ∀ t, if eqMode then ∑ θ : Fin m, g θ t = γ * s t
        else γ * s t ≤ ∑ θ : Fin m, g θ t := by
      intro t
      have h := hw_eq (eVar (Sum.inr t))
      rw [← eDR.sum_comp] at h
      dsimp only [DualRow] at h
      simp only [aD, Equiv.symm_apply_apply, Fintype.sum_sum_type, Fintype.sum_unique] at h
      have h1 : ∑ q : Edge, w (eDR (Sum.inl q)) * (if q.1.2 = t then (1 : ℝ) else 0) =
          ∑ θ : Fin m, g θ t := by
        calc ∑ q : Edge, w (eDR (Sum.inl q)) * (if q.1.2 = t then (1 : ℝ) else 0)
            = ∑ p : Fin m × Fin n, if hE : E p.1 p.2 then
                w (eDR (Sum.inl ⟨p, hE⟩)) * (if p.2 = t then (1 : ℝ) else 0) else 0 := by
                exact sum_subtype_ite _ _
          _ = ∑ θ : Fin m, ∑ t' : Fin n, if hE : E θ t' then
                w (eDR (Sum.inl ⟨(θ, t'), hE⟩)) * (if t' = t then (1 : ℝ) else 0) else 0 :=
                Fintype.sum_prod_type _
          _ = ∑ θ : Fin m, g θ t := by
                refine Finset.sum_congr rfl fun θ _ => ?_
                rw [Finset.sum_eq_single t]
                · dsimp only [g]; by_cases hE : E θ t <;> simp [hE]
                · intro t' _ hne; split_ifs <;> simp
                · intro habs; exact absurd (Finset.mem_univ _) habs
      rw [h1] at h
      cases hmode : eqMode
      · simp only [hmode, Bool.not_false, true_and, Bool.false_eq_true, ↓reduceIte] at h ⊢
        have h2 : ∑ t' : Fin n, w (eDR (Sum.inr (Sum.inl t'))) *
            (if t' = t then (-1 : ℝ) else 0) = -w (eDR (Sum.inr (Sum.inl t))) := by
          rw [Finset.sum_eq_single t]
          · simp
          · intro t' _ hne; simp [hne]
          · intro habs; exact absurd (Finset.mem_univ _) habs
        rw [h2] at h
        linarith [hw_nn (eDR (Sum.inr (Sum.inl t)))]
      · simp only [hmode, Bool.not_true, ↓reduceIte, mul_neg] at h ⊢
        have h0 : ∑ t' : Fin n, w (eDR (Sum.inr (Sum.inl t'))) *
            (if false = true ∧ t' = t then (-1 : ℝ) else 0) = 0 := by simp
        rw [h0, zero_add] at h
        dsimp only [γ]
        linarith
    have hobj_gt : γ * M < obj g := by
      rw [← eDR.sum_comp] at hw_lt
      dsimp only [DualRow] at hw_lt
      simp only [bD, Equiv.symm_apply_apply, Fintype.sum_sum_type, mul_zero,
        Finset.sum_const_zero, zero_add, Fintype.sum_unique] at hw_lt
      have h1 : ∑ q : Edge, w (eDR (Sum.inl q)) * (-α q.1.1 q.1.2) = -obj g := by
        calc ∑ q : Edge, w (eDR (Sum.inl q)) * (-α q.1.1 q.1.2)
            = ∑ p : Fin m × Fin n, if hE : E p.1 p.2 then
                w (eDR (Sum.inl ⟨p, hE⟩)) * (-α p.1 p.2) else 0 := by
                exact sum_subtype_ite _ _
          _ = ∑ θ : Fin m, ∑ t : Fin n, if hE : E θ t then
                w (eDR (Sum.inl ⟨(θ, t), hE⟩)) * (-α θ t) else 0 := Fintype.sum_prod_type _
          _ = ∑ θ : Fin m, ∑ t : Fin n, -(α θ t * g θ t) := by
                refine Finset.sum_congr rfl fun θ _ => Finset.sum_congr rfl fun t _ => ?_
                dsimp only [g]; split_ifs <;> ring
          _ = -obj g := by simp only [obj, Finset.sum_neg_distrib]
      rw [h1] at hw_lt
      linarith
    rcases lt_or_eq_of_le hγ_nn with hγ_pos | hγ_zero
    · let g' : Fin m → Fin n → ℝ := fun θ t => g θ t / γ
      have hg'P : g' ∈ P := by
        refine ⟨fun θ t => div_nonneg (hg_nn θ t) (le_of_lt hγ_pos),
          fun θ t hnE => by simp [g', g, hnE], fun θ => ?_, fun t => ?_⟩
        · simp only [g', ← Finset.sum_div, hg_row θ]
          exact mul_div_cancel_left₀ (π θ) (ne_of_gt hγ_pos)
        · have ht := hg_col t
          cases hmode : eqMode
          · simp only [hmode, Bool.false_eq_true, ↓reduceIte] at ht ⊢
            simp only [g', ← Finset.sum_div]
            exact (le_div_iff₀ hγ_pos).mpr (by linarith)
          · simp only [hmode, ↓reduceIte] at ht ⊢
            simp only [g', ← Finset.sum_div, ht]
            exact mul_div_cancel_left₀ (s t) (ne_of_gt hγ_pos)
      have hleM : obj g' ≤ M := hfmax hg'P
      have hobj_div : obj g' = obj g / γ := by
        calc obj g' = ∑ θ : Fin m, ∑ t : Fin n, (α θ t * g θ t) / γ := by
              simp only [obj, g']
              exact Finset.sum_congr rfl fun θ _ => Finset.sum_congr rfl fun t _ => by ring
          _ = obj g / γ := by simp only [obj, ← Finset.sum_div]
      rw [hobj_div, div_le_iff₀ hγ_pos] at hleM
      linarith
    · have hg0 : ∀ θ t, g θ t = 0 := by
        intro θ t
        have hsum : ∑ t' : Fin n, g θ t' = 0 := by rw [hg_row θ, ← hγ_zero, zero_mul]
        exact (Finset.sum_eq_zero_iff_of_nonneg (fun t' _ => hg_nn θ t')).mp hsum t
          (Finset.mem_univ t)
      have hobj0 : obj g = 0 :=
        Finset.sum_eq_zero fun θ _ => Finset.sum_eq_zero fun t _ => by rw [hg0 θ t, mul_zero]
      rw [← hγ_zero, zero_mul, hobj0] at hobj_gt
      linarith

/- ## Section 2: Strictly Positive LTU Games (`RealGame`) -/

/-- A real-valued Bayesian simple security game with `m` attacker types and `n` targets. -/
structure RealGame (m n : ℕ) where
  π : Fin m → ℝ
  b : Fin m → Fin n → ℝ
  a : Fin m → Fin n → ℝ
  d : Fin n → ℝ
  hn : 0 < n
  hπ_nn : ∀ θ, 0 ≤ π θ
  hπ_sum : ∑ θ : Fin m, π θ = 1
  ha_nn : ∀ θ t, 0 ≤ a θ t
  hd_nn : ∀ t, 0 ≤ d t

namespace RealGame

variable {m n : ℕ} (G : RealGame m n)

def uA (c : Fin n → ℝ) (θ : Fin m) (t : Fin n) : ℝ := G.b θ t - G.a θ t * c t

def gain (p : Fin m → Fin n → ℝ) (t : Fin n) : ℝ := (∑ θ : Fin m, G.π θ * p θ t) * G.d t

def IsAtkProfile (G : RealGame m n) (p : Fin m → Fin n → ℝ) : Prop :=
  let _ := G
  ∀ θ, (∑ t : Fin n, p θ t) = 1 ∧ ∀ t, 0 ≤ p θ t

def IsAtkBR (c : Fin n → ℝ) (p : Fin m → Fin n → ℝ) : Prop :=
  ∀ θ t s, 0 < p θ t → G.uA c θ s ≤ G.uA c θ t

def IsLower (lam : ℝ) (c : Fin n → ℝ) (p : Fin m → Fin n → ℝ) : Prop :=
  (∀ t, 0 ≤ c t ∧ c t ≤ 1) ∧ G.IsAtkProfile p ∧ G.IsAtkBR c p ∧
  ∀ t, 0 < c t → lam ≤ G.gain p t

def IsEq (lam : ℝ) (c : Fin n → ℝ) (p : Fin m → Fin n → ℝ) : Prop :=
  G.IsLower lam c p ∧ ∀ t, c t < 1 → G.gain p t ≤ lam

def LowerSet (lam : ℝ) : Set (Fin n → ℝ) := {c | ∃ p, G.IsLower lam c p}

noncomputable def maxUtil (c : Fin n → ℝ) (θ : Fin m) : ℝ :=
  Finset.univ.sup' (Finset.univ_nonempty_iff.mpr ⟨⟨0, G.hn⟩⟩) (fun t => G.uA c θ t)

lemma le_maxUtil (c : Fin n → ℝ) (θ : Fin m) (t : Fin n) :
    G.uA c θ t ≤ G.maxUtil c θ :=
  Finset.le_sup' (fun t => G.uA c θ t) (Finset.mem_univ t)

lemma exists_argmax (c : Fin n → ℝ) (θ : Fin m) :
    ∃ t : Fin n, G.uA c θ t = G.maxUtil c θ := by
  obtain ⟨t, _, ht⟩ := Finset.exists_mem_eq_sup'
    (Finset.univ_nonempty_iff.mpr ⟨⟨0, G.hn⟩⟩) (fun t => G.uA c θ t)
  exact ⟨t, ht.symm⟩

lemma isAtkBR_iff_maxUtil (c : Fin n → ℝ) (p : Fin m → Fin n → ℝ) :
    G.IsAtkBR c p ↔ ∀ θ t, 0 < p θ t → G.uA c θ t = G.maxUtil c θ := by
  constructor
  · intro h θ t hpos
    exact le_antisymm (G.le_maxUtil c θ t)
      (Finset.sup'_le _ _ fun s _ => h θ t s hpos)
  · intro h θ t s hpos
    rw [h θ t hpos]
    exact G.le_maxUtil c θ s

lemma uA_anti {c₁ c₂ : Fin n → ℝ} (hle : ∀ t, c₁ t ≤ c₂ t) (θ : Fin m) (t : Fin n) :
    G.uA c₂ θ t ≤ G.uA c₁ θ t := by
  simp only [uA]
  have := mul_le_mul_of_nonneg_left (hle t) (G.ha_nn θ t)
  linarith

lemma maxUtil_anti {c₁ c₂ : Fin n → ℝ} (hle : ∀ t, c₁ t ≤ c₂ t) (θ : Fin m) :
    G.maxUtil c₂ θ ≤ G.maxUtil c₁ θ := by
  refine Finset.sup'_le _ _ fun t _ => le_trans (G.uA_anti hle θ t) (G.le_maxUtil c₁ θ t)

/-- Existence of a trivial pure attacker best response for any coverage `c`. -/
lemma exists_pure_atkBR (c : Fin n → ℝ) :
    ∃ p : Fin m → Fin n → ℝ, G.IsAtkProfile p ∧ G.IsAtkBR c p := by
  classical
  choose t0 ht0 using fun θ => G.exists_argmax c θ
  refine ⟨fun θ t => if t = t0 θ then 1 else 0, ?_, ?_⟩
  · intro θ
    refine ⟨by simp, fun t => by dsimp only; split_ifs <;> linarith⟩
  · intro θ t s hpos
    have ht : t = t0 θ := by by_contra hne; simp [hne] at hpos
    rw [ht, ht0 θ]
    exact G.le_maxUtil c θ s

/-- `0` is always in `LowerSet G lam`. -/
lemma zero_mem_lowerSet (lam : ℝ) : (fun _ : Fin n => (0 : ℝ)) ∈ G.LowerSet lam := by
  obtain ⟨p, hp, hbr⟩ := G.exists_pure_atkBR (fun _ => 0)
  exact ⟨p, fun _ => ⟨le_rfl, zero_le_one⟩, hp, hbr, fun _ h => absurd h (lt_irrefl 0)⟩

/-- `1` is always an equilibrium at `lam = 0`. -/
lemma one_isEq_zero : ∃ p, G.IsEq 0 (fun _ : Fin n => (1 : ℝ)) p := by
  obtain ⟨p, hp, hbr⟩ := G.exists_pure_atkBR (fun _ => 1)
  refine ⟨p, ⟨fun _ => ⟨zero_le_one, le_rfl⟩, hp, hbr, fun t _ => ?_⟩,
    fun _ h => absurd h (lt_irrefl 1)⟩
  exact mul_nonneg (Finset.sum_nonneg fun θ _ => mul_nonneg (G.hπ_nn θ) ((hp θ).2 t)) (G.hd_nn t)

/-- Compactness of the joint set `{(c, p) | IsLower G lam c p}`. -/
lemma isCompact_lowerPairs (lam : ℝ) :
    IsCompact {x : (Fin n → ℝ) × (Fin m → Fin n → ℝ) | G.IsLower lam x.1 x.2} := by
  let BoxC : Set (Fin n → ℝ) := Set.pi Set.univ fun _ => Set.Icc 0 1
  let BoxP : Set (Fin m → Fin n → ℝ) :=
    Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Set.Icc 0 1
  have hBox : IsCompact (BoxC ×ˢ BoxP) :=
    (isCompact_univ_pi fun _ => isCompact_Icc).prod
      (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc)
  have hsub : {x : (Fin n → ℝ) × (Fin m → Fin n → ℝ) | G.IsLower lam x.1 x.2} ⊆ BoxC ×ˢ BoxP := by
    rintro ⟨c, p⟩ ⟨hc, hp, _, _⟩
    refine ⟨fun t _ => hc t, fun θ _ t _ => ⟨(hp θ).2 t, ?_⟩⟩
    have := Finset.single_le_sum (f := fun t' : Fin n => p θ t') (fun t' _ => (hp θ).2 t') (Finset.mem_univ t)
    linarith [(hp θ).1]
  have hclosed : IsClosed {x : (Fin n → ℝ) × (Fin m → Fin n → ℝ) | G.IsLower lam x.1 x.2} := by
    have hc1 : IsClosed {x : (Fin n → ℝ) × (Fin m → Fin n → ℝ) | ∀ t, 0 ≤ x.1 t ∧ x.1 t ≤ 1} := by
      have heq : {x : (Fin n → ℝ) × (Fin m → Fin n → ℝ) | ∀ t, 0 ≤ x.1 t ∧ x.1 t ≤ 1} =
          ⋂ t : Fin n, ({x | (0 : ℝ) ≤ x.1 t} ∩ {x | x.1 t ≤ 1}) := by ext x; simp
      rw [heq]
      exact isClosed_iInter fun t =>
        (isClosed_le continuous_const ((continuous_apply t).comp continuous_fst)).inter
        (isClosed_le ((continuous_apply t).comp continuous_fst) continuous_const)
    have hc2 : IsClosed {x : (Fin n → ℝ) × (Fin m → Fin n → ℝ) | G.IsAtkProfile x.2} := by
      have heq : {x : (Fin n → ℝ) × (Fin m → Fin n → ℝ) | G.IsAtkProfile x.2} =
          ⋂ θ : Fin m, ({x | ∑ t : Fin n, x.2 θ t = 1} ∩ ⋂ t : Fin n, {x | (0 : ℝ) ≤ x.2 θ t}) := by
        ext x; simp [IsAtkProfile]
      rw [heq]
      exact isClosed_iInter fun θ =>
        (isClosed_eq (continuous_finsetSum Finset.univ fun t _ =>
          (continuous_apply t).comp ((continuous_apply θ).comp continuous_snd)) continuous_const).inter
        (isClosed_iInter fun t =>
          isClosed_le continuous_const ((continuous_apply t).comp ((continuous_apply θ).comp continuous_snd)))
    have hc3 : IsClosed {x : (Fin n → ℝ) × (Fin m → Fin n → ℝ) | G.IsAtkBR x.1 x.2} := by
      have heq : {x : (Fin n → ℝ) × (Fin m → Fin n → ℝ) | G.IsAtkBR x.1 x.2} =
          ⋂ θ, ⋂ t, ⋂ s, ({x | x.2 θ t ≤ 0} ∪ {x | G.uA x.1 θ s ≤ G.uA x.1 θ t}) := by
        ext ⟨c, p⟩
        simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_union, IsAtkBR]
        constructor
        · intro h θ t s
          by_cases hpos : 0 < p θ t
          · exact Or.inr (h θ t s hpos)
          · exact Or.inl (not_lt.mp hpos)
        · intro h θ t s hpos
          exact (h θ t s).resolve_left (not_le.mpr hpos)
      rw [heq]
      refine isClosed_iInter fun θ => isClosed_iInter fun t => isClosed_iInter fun s =>
        IsClosed.union
          (isClosed_le ((continuous_apply t).comp ((continuous_apply θ).comp continuous_snd))
            continuous_const)
          (isClosed_le
            (continuous_const.sub (continuous_const.mul ((continuous_apply s).comp continuous_fst)))
            (continuous_const.sub (continuous_const.mul ((continuous_apply t).comp continuous_fst))))
    have hc4 : IsClosed {x : (Fin n → ℝ) × (Fin m → Fin n → ℝ) |
        ∀ t, 0 < x.1 t → lam ≤ G.gain x.2 t} := by
      have heq : {x : (Fin n → ℝ) × (Fin m → Fin n → ℝ) | ∀ t, 0 < x.1 t → lam ≤ G.gain x.2 t} =
          ⋂ t, ({x | x.1 t ≤ 0} ∪ {x | lam ≤ G.gain x.2 t}) := by
        ext ⟨c, p⟩
        simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_union]
        constructor
        · intro h t
          by_cases hpos : 0 < c t
          · exact Or.inr (h t hpos)
          · exact Or.inl (not_lt.mp hpos)
        · intro h t hpos
          exact (h t).resolve_left (not_le.mpr hpos)
      rw [heq]
      refine isClosed_iInter fun t => IsClosed.union
        (isClosed_le ((continuous_apply t).comp continuous_fst) continuous_const)
        (isClosed_le continuous_const ((continuous_finsetSum _ fun θ _ =>
          continuous_const.mul ((continuous_apply t).comp ((continuous_apply θ).comp continuous_snd))).mul
          continuous_const))
    have h_eq : {x : (Fin n → ℝ) × (Fin m → Fin n → ℝ) | G.IsLower lam x.1 x.2} =
        ({x | ∀ t, 0 ≤ x.1 t ∧ x.1 t ≤ 1} ∩ {x | G.IsAtkProfile x.2}) ∩
        {x | G.IsAtkBR x.1 x.2} ∩ {x | ∀ t, 0 < x.1 t → lam ≤ G.gain x.2 t} := by
      ext x; simp [IsLower, and_assoc]
    rw [h_eq]
    exact ((hc1.inter hc2).inter hc3).inter hc4
  exact hBox.of_isClosed_subset hclosed hsub

lemma isCompact_lowerSet (lam : ℝ) : IsCompact (G.LowerSet lam) := by
  have heq : G.LowerSet lam = Prod.fst '' {x : (Fin n → ℝ) × (Fin m → Fin n → ℝ) |
      G.IsLower lam x.1 x.2} := by
    ext c; simp [LowerSet]
  rw [heq]
  exact (G.isCompact_lowerPairs lam).image continuous_fst

/-- Compactness of the joint equilibrium set `{(c, p) | IsEq G lam c p}`. -/
lemma isCompact_eqPairs (lam : ℝ) :
    IsCompact {x : (Fin n → ℝ) × (Fin m → Fin n → ℝ) | G.IsEq lam x.1 x.2} := by
  have hc5 : IsClosed {x : (Fin n → ℝ) × (Fin m → Fin n → ℝ) |
      ∀ t, x.1 t < 1 → G.gain x.2 t ≤ lam} := by
    have heq : {x : (Fin n → ℝ) × (Fin m → Fin n → ℝ) | ∀ t, x.1 t < 1 → G.gain x.2 t ≤ lam} =
        ⋂ t, ({x | 1 ≤ x.1 t} ∪ {x | G.gain x.2 t ≤ lam}) := by
      ext ⟨c, p⟩
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_union]
      constructor
      · intro h t
        by_cases hlt : c t < 1
        · exact Or.inr (h t hlt)
        · exact Or.inl (not_lt.mp hlt)
      · intro h t hlt
        exact (h t).resolve_left (not_le.mpr hlt)
    rw [heq]
    refine isClosed_iInter fun t => IsClosed.union
      (isClosed_le continuous_const ((continuous_apply t).comp continuous_fst))
      (isClosed_le ((continuous_finsetSum _ fun θ _ =>
        continuous_const.mul ((continuous_apply t).comp ((continuous_apply θ).comp continuous_snd))).mul
        continuous_const) continuous_const)
  exact (G.isCompact_lowerPairs lam).inter_right hc5

/-- Key gross-substitutes lattice property: when `a_{θ,t} > 0` strictly, `LowerSet G lam` is
closed under pairwise coordinatewise `max`. -/
lemma lowerSet_max_closed (ha_pos : ∀ θ t, 0 < G.a θ t) (lam : ℝ)
    {c₁ c₂ : Fin n → ℝ} (h₁ : c₁ ∈ G.LowerSet lam) (h₂ : c₂ ∈ G.LowerSet lam) :
    (fun t => max (c₁ t) (c₂ t)) ∈ G.LowerSet lam := by
  classical
  obtain ⟨p₁, hc₁, hp₁, hbr₁, hlo₁⟩ := h₁
  obtain ⟨p₂, hc₂, hp₂, hbr₂, hlo₂⟩ := h₂
  let cbar : Fin n → ℝ := fun t => max (c₁ t) (c₂ t)
  have hle₁ : ∀ t, c₁ t ≤ cbar t := fun t => le_max_left _ _
  have hle₂ : ∀ t, c₂ t ≤ cbar t := fun t => le_max_right _ _
  choose tstar htstar using fun θ => G.exists_argmax cbar θ
  let α : Fin m → ℝ := fun θ => ∑ t ∈ Finset.univ.filter (fun t => c₂ t ≤ c₁ t), p₁ θ t
  let β : Fin m → ℝ := fun θ => ∑ t ∈ Finset.univ.filter (fun t => c₁ t < c₂ t), p₂ θ t
  have hα_nn : ∀ θ, 0 ≤ α θ := fun θ => Finset.sum_nonneg fun t _ => (hp₁ θ).2 t
  have hβ_nn : ∀ θ, 0 ≤ β θ := fun θ => Finset.sum_nonneg fun t _ => (hp₂ θ).2 t
  have hα_le : ∀ θ, α θ ≤ 1 := fun θ => by
    calc α θ ≤ ∑ t : Fin n, p₁ θ t :=
          Finset.sum_le_univ_sum_of_nonneg fun t => (hp₁ θ).2 t
      _ = 1 := (hp₁ θ).1
  have hβ_le : ∀ θ, β θ ≤ 1 := fun θ => by
    calc β θ ≤ ∑ t : Fin n, p₂ θ t :=
          Finset.sum_le_univ_sum_of_nonneg fun t => (hp₂ θ).2 t
      _ = 1 := (hp₂ θ).1
  -- Crucial: for every θ, at least one of α θ and β θ is 0!
  have hαβ_zero : ∀ θ, α θ = 0 ∨ β θ = 0 := by
    intro θ
    rcases lt_or_ge (G.maxUtil c₂ θ) (G.maxUtil c₁ θ) with hlt | hge
    · left
      refine Finset.sum_eq_zero fun t ht => ?_
      have hct : c₂ t ≤ c₁ t := (Finset.mem_filter.mp ht).2
      by_contra hne
      have hpos : 0 < p₁ θ t := lt_of_le_of_ne ((hp₁ θ).2 t) (Ne.symm hne)
      have heq1 : G.uA c₁ θ t = G.maxUtil c₁ θ := (G.isAtkBR_iff_maxUtil c₁ p₁).mp hbr₁ θ t hpos
      have hle2 : G.uA c₁ θ t ≤ G.uA c₂ θ t := by
        simp only [uA]; nlinarith [G.ha_nn θ t]
      linarith [G.le_maxUtil c₂ θ t]
    · right
      refine Finset.sum_eq_zero fun t ht => ?_
      have hct : c₁ t < c₂ t := (Finset.mem_filter.mp ht).2
      by_contra hne
      have hpos : 0 < p₂ θ t := lt_of_le_of_ne ((hp₂ θ).2 t) (Ne.symm hne)
      have heq2 : G.uA c₂ θ t = G.maxUtil c₂ θ := (G.isAtkBR_iff_maxUtil c₂ p₂).mp hbr₂ θ t hpos
      have hlt1 : G.uA c₂ θ t < G.uA c₁ θ t := by
        simp only [uA]; nlinarith [ha_pos θ t]
      linarith [G.le_maxUtil c₁ θ t]
  have hαβ_le : ∀ θ, α θ + β θ ≤ 1 := by
    intro θ
    rcases hαβ_zero θ with h0 | h0
    · linarith [hβ_le θ]
    · linarith [hα_le θ]
  let pbar : Fin m → Fin n → ℝ := fun θ t =>
    (if c₂ t ≤ c₁ t then p₁ θ t else p₂ θ t) +
    (if t = tstar θ then 1 - α θ - β θ else 0)
  refine ⟨pbar, ?_, ?_, ?_, ?_⟩
  · intro t
    exact ⟨le_trans (hc₁ t).1 (le_max_left _ _), max_le (hc₁ t).2 (hc₂ t).2⟩
  · intro θ
    refine ⟨?_, ?_⟩
    · dsimp only [pbar]
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ (tstar θ)]
      simp only [Finset.mem_univ, ↓reduceIte]
      have hsplit : ∑ t : Fin n, (if c₂ t ≤ c₁ t then p₁ θ t else p₂ θ t) = α θ + β θ := by
        rw [Finset.sum_ite]
        congr 1
        refine Finset.sum_congr ?_ fun _ _ => rfl
        ext t; simp [not_le]
      rw [hsplit]; ring
    · intro t
      dsimp only [pbar]
      have h1 : 0 ≤ if c₂ t ≤ c₁ t then p₁ θ t else p₂ θ t := by
        split_ifs; exact (hp₁ θ).2 t; exact (hp₂ θ).2 t
      have h2 : 0 ≤ if t = tstar θ then 1 - α θ - β θ else 0 := by
        split_ifs; linarith [hαβ_le θ]; exact le_rfl
      linarith
  · rw [G.isAtkBR_iff_maxUtil]
    intro θ t hpos
    dsimp only [pbar] at hpos
    by_cases hts : t = tstar θ
    · rw [hts]; exact htstar θ
    · simp only [hts, ↓reduceIte, add_zero] at hpos
      split_ifs at hpos with hct
      · have hbar_eq : cbar t = c₁ t := max_eq_left hct
        have heq1 : G.uA c₁ θ t = G.maxUtil c₁ θ := (G.isAtkBR_iff_maxUtil c₁ p₁).mp hbr₁ θ t hpos
        have hu_eq : G.uA cbar θ t = G.uA c₁ θ t := by simp [uA, hbar_eq]
        exact le_antisymm (G.le_maxUtil cbar θ t)
          (le_trans (G.maxUtil_anti hle₁ θ) (by linarith))
      · have hlt : c₁ t < c₂ t := not_le.mp hct
        have hbar_eq : cbar t = c₂ t := max_eq_right (le_of_lt hlt)
        have heq2 : G.uA c₂ θ t = G.maxUtil c₂ θ := (G.isAtkBR_iff_maxUtil c₂ p₂).mp hbr₂ θ t hpos
        have hu_eq : G.uA cbar θ t = G.uA c₂ θ t := by simp [uA, hbar_eq]
        exact le_antisymm (G.le_maxUtil cbar θ t)
          (le_trans (G.maxUtil_anti hle₂ θ) (by linarith))
  · intro t htpos
    by_cases hct : c₂ t ≤ c₁ t
    · have hbar_eq : cbar t = c₁ t := max_eq_left hct
      have hc1_pos : 0 < c₁ t := by linarith
      have hge : G.gain p₁ t ≤ G.gain pbar t := by
        refine mul_le_mul_of_nonneg_right (Finset.sum_le_sum fun θ _ => ?_) (G.hd_nn t)
        refine mul_le_mul_of_nonneg_left ?_ (G.hπ_nn θ)
        dsimp only [pbar]; rw [if_pos hct]
        split_ifs; linarith [hαβ_le θ]; linarith
      linarith [hlo₁ t hc1_pos]
    · have hlt : c₁ t < c₂ t := not_le.mp hct
      have hbar_eq : cbar t = c₂ t := max_eq_right (le_of_lt hlt)
      have hc2_pos : 0 < c₂ t := by linarith
      have hge : G.gain p₂ t ≤ G.gain pbar t := by
        refine mul_le_mul_of_nonneg_right (Finset.sum_le_sum fun θ _ => ?_) (G.hd_nn t)
        refine mul_le_mul_of_nonneg_left ?_ (G.hπ_nn θ)
        dsimp only [pbar]; rw [if_neg hct]
        split_ifs; linarith [hαβ_le θ]; linarith
      linarith [hlo₂ t hc2_pos]

/-- When `a_{θ,t} > 0` strictly, `LowerSet G lam` has a unique coordinatewise maximum element. -/
lemma exists_max_lowerSet (ha_pos : ∀ θ t, 0 < G.a θ t) (lam : ℝ) :
    ∃ cstar ∈ G.LowerSet lam, ∀ c ∈ G.LowerSet lam, ∀ t, c t ≤ cstar t := by
  have hcomp := G.isCompact_lowerSet lam
  have hne : (G.LowerSet lam).Nonempty := ⟨fun _ => 0, G.zero_mem_lowerSet lam⟩
  have hcoord : ∀ t : Fin n, ∃ ct ∈ G.LowerSet lam, ∀ c ∈ G.LowerSet lam, c t ≤ ct t := by
    intro t
    obtain ⟨ct, hct, hmax⟩ := hcomp.exists_isMaxOn hne (continuous_apply t).continuousOn
    exact ⟨ct, hct, fun c hc => hmax hc⟩
  choose ct hct_mem hct_max using hcoord
  -- Take finite coordinatewise max over `Finset.univ`
  have hfin : ∀ S : Finset (Fin n),
      ∃ cS ∈ G.LowerSet lam, ∀ t ∈ S, ∀ c ∈ G.LowerSet lam, c t ≤ cS t := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨fun _ => 0, G.zero_mem_lowerSet lam, fun _ ht => absurd ht (by simp)⟩
    | @insert t0 S' ht0 ih =>
      obtain ⟨cS', hcS'_mem, hcS'_max⟩ := ih
      refine ⟨fun t => max (cS' t) (ct t0 t),
        G.lowerSet_max_closed ha_pos lam hcS'_mem (hct_mem t0), ?_⟩
      intro t ht c hc
      rcases Finset.mem_insert.mp ht with rfl | htS'
      · exact le_trans (hct_max t c hc) (le_max_right _ _)
      · exact le_trans (hcS'_max t htS' c hc) (le_max_left _ _)
  obtain ⟨cstar, hcstar_mem, hcstar_max⟩ := hfin Finset.univ
  exact ⟨cstar, hcstar_mem, fun c hc t => hcstar_max t (Finset.mem_univ t) c hc⟩

/-- Core theorem for strictly positive games: the maximum element `c*` of `LowerSet G lam`
automatically satisfies the upper condition too, hence is a fixed-`lam` equilibrium. -/
lemma max_lowerSet_isEq (ha_pos : ∀ θ t, 0 < G.a θ t) (hd_pos : ∀ t, 0 < G.d t)
    {lam : ℝ} (hlam : 0 < lam)
    {cstar : Fin n → ℝ} (hcstar_mem : cstar ∈ G.LowerSet lam)
    (hcstar_max : ∀ c ∈ G.LowerSet lam, ∀ t, c t ≤ cstar t) :
    ∃ pstar, G.IsEq lam cstar pstar := by
  classical
  obtain ⟨p0, hc0, hp0, hbr0, hlo0⟩ := hcstar_mem
  let s : Fin n → ℝ := fun t => lam / G.d t
  let B : Fin m → Finset (Fin n) := fun θ =>
    Finset.univ.filter fun t => G.uA cstar θ t = G.maxUtil cstar θ
  have hB_ne : ∀ θ, (B θ).Nonempty := fun θ => by
    obtain ⟨t, ht⟩ := G.exists_argmax cstar θ
    exact ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ t, ht⟩⟩
  let Tlt1 : Finset (Fin n) := Finset.univ.filter fun t => cstar t < 1
  -- Claim: no subset `S ⊆ Tlt1` is strictly over-demanded
  have hno_over : ∀ S ⊆ Tlt1,
      ∑ θ ∈ Finset.univ.filter (fun θ => B θ ⊆ S), G.π θ ≤ ∑ t ∈ S, s t := by
    by_contra hbad
    push Not at hbad
    -- Pick `S ⊆ Tlt1` maximizing excess `Φ S`, and of minimum cardinality among maximizers
    let Φ : Finset (Fin n) → ℝ := fun S =>
      (∑ θ ∈ Finset.univ.filter (fun θ => B θ ⊆ S), G.π θ) - ∑ t ∈ S, s t
    let Subs := Tlt1.powerset
    have hSubs_ne : Subs.Nonempty := ⟨∅, Finset.empty_mem_powerset _⟩
    obtain ⟨Smax, hSmax_mem, hSmax_ge⟩ := Subs.exists_max_image Φ hSubs_ne
    let MaxSubs := Subs.filter fun S => Φ S = Φ Smax
    have hMax_ne : MaxSubs.Nonempty := ⟨Smax, Finset.mem_filter.mpr ⟨hSmax_mem, rfl⟩⟩
    obtain ⟨S, hS_mem, hS_mincard⟩ := MaxSubs.exists_min_image Finset.card hMax_ne
    have hS_sub : S ⊆ Tlt1 := Finset.mem_powerset.mp (Finset.mem_filter.mp hS_mem).1
    have hS_eq : Φ S = Φ Smax := (Finset.mem_filter.mp hS_mem).2
    obtain ⟨Sbad, hSbad_sub, hSbad_gt⟩ := hbad
    have hΦ_pos : 0 < Φ S := by
      have := hSmax_ge Sbad (Finset.mem_powerset.mpr hSbad_sub)
      dsimp only [Φ] at this hS_eq ⊢
      linarith
    have hS_ne : S.Nonempty := by
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty.mp hempty] at hΦ_pos
      have h0 : (Finset.univ.filter (fun θ : Fin m => B θ ⊆ ∅)) = ∅ := by
        ext θ; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.subset_empty,
          Finset.notMem_empty, iff_false]
        exact (hB_ne θ).ne_empty
      simp only [Φ, h0, Finset.sum_empty, sub_self] at hΦ_pos
      linarith
    -- Define `Θ_S` and check strict Hall condition on `(Θ_S, S)`
    let ΘS : Finset (Fin m) := Finset.univ.filter fun θ => B θ ⊆ S
    let eΘ := Fintype.equivFin {θ : Fin m // θ ∈ ΘS}
    let eS := Fintype.equivFin {t : Fin n // t ∈ S}
    let π' : Fin (Fintype.card {θ : Fin m // θ ∈ ΘS}) → ℝ := fun i => G.π (eΘ.symm i).1
    let s' : Fin (Fintype.card {t : Fin n // t ∈ S}) → ℝ := fun j => s (eS.symm j).1
    let E' : Fin (Fintype.card {θ : Fin m // θ ∈ ΘS}) →
        Fin (Fintype.card {t : Fin n // t ∈ S}) → Prop :=
      fun i j => (eS.symm j).1 ∈ B (eΘ.symm i).1
    have hhall : ∀ R' : Finset (Fin (Fintype.card {t : Fin n // t ∈ S})),
        ∑ j ∈ R', s' j ≤
        ∑ i ∈ Finset.univ.filter (fun i => ∃ j ∈ R', E' i j), π' i := by
      intro R'
      by_cases hR'_ne : R'.Nonempty
      · let R : Finset (Fin n) := R'.image fun j => (eS.symm j).1
        have hR_sub : R ⊆ S := by
          intro t ht; obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp ht; exact (eS.symm j).2
        have hR_ne : R.Nonempty := hR'_ne.image _
        let S' : Finset (Fin n) := S \ R
        have hS'_sub : S' ⊆ Tlt1 := Finset.Subset.trans Finset.sdiff_subset hS_sub
        have hS'_card : S'.card < S.card := by
          have h1 := Finset.card_sdiff_add_card_eq_card hR_sub
          have h2 := Finset.card_pos.mpr hR_ne
          dsimp only [S']
          omega
        have hΦ_lt : Φ S' < Φ S := by
          have hle := hSmax_ge S' (Finset.mem_powerset.mpr hS'_sub)
          by_contra hnot
          have heq : Φ S' = Φ Smax := by linarith
          have hmem : S' ∈ MaxSubs := Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hS'_sub, heq⟩
          have := hS_mincard S' hmem
          omega
        -- Rewrite sums in terms of `R` and `S'`
        have hsum_s : ∑ j ∈ R', s' j = ∑ t ∈ R, s t := by
          rw [Finset.sum_image]
          intro j1 _ j2 _ heq
          exact eS.symm.injective (Subtype.ext heq)
        have hsum_s_diff : ∑ t ∈ S, s t - ∑ t ∈ S', s t = ∑ t ∈ R, s t := by
          have := Finset.sum_sdiff hR_sub (f := s)
          linarith
        have hΘ_part : ΘS = (Finset.univ.filter fun θ => B θ ⊆ S') ∪
            (ΘS.filter fun θ => ∃ t ∈ R, t ∈ B θ) := by
          ext θ
          simp only [ΘS, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
          constructor
          · intro hsub
            by_cases hex : ∃ t ∈ R, t ∈ B θ
            · exact Or.inr ⟨hsub, hex⟩
            · left; intro t ht; exact Finset.mem_sdiff.mpr ⟨hsub ht, fun htR => hex ⟨t, htR, ht⟩⟩
          · rintro (hsub | ⟨hsub, _⟩)
            · exact Finset.Subset.trans hsub Finset.sdiff_subset
            · exact hsub
        have hΘ_disj : Disjoint (Finset.univ.filter fun θ => B θ ⊆ S')
            (ΘS.filter fun θ => ∃ t ∈ R, t ∈ B θ) := by
          rw [Finset.disjoint_left]
          intro θ h1 h2
          have hsub := (Finset.mem_filter.mp h1).2
          obtain ⟨t, htR, htB⟩ := (Finset.mem_filter.mp h2).2
          exact (Finset.mem_sdiff.mp (hsub htB)).2 htR
        have hsum_π_eq : ∑ i ∈ Finset.univ.filter (fun i => ∃ j ∈ R', E' i j), π' i =
            ∑ θ ∈ ΘS.filter (fun θ => ∃ t ∈ R, t ∈ B θ), G.π θ := by
          refine Finset.sum_bij (fun i _ => (eΘ.symm i).1) ?_ ?_ ?_ ?_
          · intro i hi
            obtain ⟨j, hjR', hEij⟩ := (Finset.mem_filter.mp hi).2
            exact Finset.mem_filter.mpr ⟨(eΘ.symm i).2,
              ⟨(eS.symm j).1, Finset.mem_image_of_mem _ hjR', hEij⟩⟩
          · intro i1 _ i2 _ heq; exact eΘ.symm.injective (Subtype.ext heq)
          · intro θ hθ
            obtain ⟨hθS, t, htR, htB⟩ := Finset.mem_filter.mp hθ
            obtain ⟨j, hjR', rfl⟩ := Finset.mem_image.mp htR
            exact ⟨eΘ ⟨θ, hθS⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
              ⟨j, hjR', by simpa [E'] using htB⟩⟩, by simp⟩
          · intro i _; rfl
        have hsum_Θ : ∑ θ ∈ ΘS, G.π θ =
            (∑ θ ∈ Finset.univ.filter (fun θ => B θ ⊆ S'), G.π θ) +
            ∑ θ ∈ ΘS.filter (fun θ => ∃ t ∈ R, t ∈ B θ), G.π θ := by
          conv_lhs => rw [hΘ_part]
          exact Finset.sum_union hΘ_disj
        rw [hsum_s, hsum_π_eq]
        dsimp only [Φ] at hΦ_lt
        linarith
      · rw [Finset.not_nonempty_iff_eq_empty.mp hR'_ne]
        simp only [Finset.sum_empty]
        exact Finset.sum_nonneg fun i _ => G.hπ_nn _
    have hE'_ne : ∀ i, ∃ j, E' i j := by
      intro i
      obtain ⟨t, htB⟩ := hB_ne (eΘ.symm i).1
      have htS : t ∈ S := (Finset.mem_filter.mp (eΘ.symm i).2).2 htB
      exact ⟨eS ⟨t, htS⟩, by simpa [E'] using htB⟩
    have hflow := farkas_hall_flow π' s' E' (fun i => G.hπ_nn _) hE'_ne hhall
    -- Apply log-slope LP duality on `(ΘS, S)` with `α' i j = -Real.log (G.a θ t)`
    let α' : Fin (Fintype.card {θ : Fin m // θ ∈ ΘS}) →
        Fin (Fintype.card {t : Fin n // t ∈ S}) → ℝ :=
      fun i j => -Real.log (G.a (eΘ.symm i).1 (eS.symm j).1)
    obtain ⟨fstar, u, z, hf_nn, hf_supp, hf_row, hf_col, hdual, hcs⟩ :=
      lp_duality_flow false π' s' E' α' (fun i => G.hπ_nn _) hflow
    let w : Fin n → ℝ := fun t => if ht : t ∈ S then Real.exp (-z (eS ⟨t, ht⟩)) else 0
    have hw_pos : ∀ t ∈ S, 0 < w t := fun t ht => by simp [w, ht, Real.exp_pos]
    have hw_nn : ∀ t, 0 ≤ w t := fun t => by
      dsimp only [w]; split_ifs; exact le_of_lt (Real.exp_pos _); exact le_rfl
    -- Choose tiny `δ > 0` so `c' = cstar + δ * w` stays ≤ 1 and preserves strict suboptimal gaps
    let gapCap : Finset ℝ :=
      S.image (fun t => (1 - cstar t) / w t) ∪
      (((Finset.univ.product (Finset.univ.product Finset.univ)).filter
        (fun p : Fin m × Fin n × Fin n => p.1 ∈ ΘS ∧ p.2.1 ∈ B p.1 ∧ p.2.2 ∉ B p.1)).image
        (fun p => (G.uA cstar p.1 p.2.1 - G.uA cstar p.1 p.2.2) / (G.a p.1 p.2.1 * w p.2.1)))
    have hgapCap_ne : gapCap.Nonempty := by
      obtain ⟨t0, ht0⟩ := hS_ne
      exact ⟨(1 - cstar t0) / w t0, Finset.mem_union_left _ (Finset.mem_image_of_mem _ ht0)⟩
    have hgapCap_pos : ∀ x ∈ gapCap, 0 < x := by
      intro x hx
      rcases Finset.mem_union.mp hx with hx1 | hx2
      · obtain ⟨t, htS, rfl⟩ := Finset.mem_image.mp hx1
        have hlt1 : cstar t < 1 := (Finset.mem_filter.mp (hS_sub htS)).2
        exact div_pos (by linarith) (hw_pos t htS)
      · obtain ⟨⟨θ, t, r⟩, hp, rfl⟩ := Finset.mem_image.mp hx2
        obtain ⟨_, hθS, htB, hrB⟩ := Finset.mem_filter.mp hp
        have htS : t ∈ S := (Finset.mem_filter.mp hθS).2 htB
        have hgt : G.uA cstar θ r < G.uA cstar θ t := by
          have h1 : G.uA cstar θ t = G.maxUtil cstar θ := (Finset.mem_filter.mp htB).2
          have h2 : G.uA cstar θ r ≤ G.maxUtil cstar θ := G.le_maxUtil cstar θ r
          have hne : G.uA cstar θ r ≠ G.maxUtil cstar θ :=
            fun heq => hrB (Finset.mem_filter.mpr ⟨Finset.mem_univ r, heq⟩)
          exact lt_of_le_of_ne (by linarith) (fun h => hne (by linarith))
        exact div_pos (by linarith) (mul_pos (ha_pos θ t) (hw_pos t htS))
    let δ : ℝ := gapCap.min' hgapCap_ne
    have hδ_pos : 0 < δ := hgapCap_pos δ (Finset.min'_mem gapCap hgapCap_ne)
    let c' : Fin n → ℝ := fun t => cstar t + δ * w t
    have hc'_ge : ∀ t, cstar t ≤ c' t := fun t => by
      dsimp only [c']; nlinarith [hw_nn t]
    have hc'_le1 : ∀ t, c' t ≤ 1 := by
      intro t; dsimp only [c']
      by_cases htS : t ∈ S
      · have hle : δ ≤ (1 - cstar t) / w t :=
          Finset.min'_le gapCap _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ htS))
        have := (le_div_iff₀ (hw_pos t htS)).mp hle
        linarith
      · simp only [w, dif_neg htS, mul_zero, add_zero]
        exact (hc0 t).2
    -- Construct attacker strategy `p'` for `c'`
    choose argmax' hargmax' using fun θ => G.exists_argmax c' θ
    have hout_ex : ∀ θ, θ ∉ ΘS → ∃ t, t ∈ B θ ∧ t ∉ S := by
      intro θ hnot
      have : ¬ B θ ⊆ S := fun h => hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      exact Finset.not_subset.mp this
    let p' : Fin m → Fin n → ℝ := fun θ t =>
      if hθ : θ ∈ ΘS then
        if hπpos : 0 < G.π θ then
          if ht : t ∈ S then fstar (eΘ ⟨θ, hθ⟩) (eS ⟨t, ht⟩) / G.π θ else 0
        else if t = argmax' θ then 1 else 0
      else
        if t ∈ S then 0
        else p0 θ t + if t = Classical.choose (hout_ex θ hθ) then ∑ r ∈ S, p0 θ r else 0
    have hc'_mem : c' ∈ G.LowerSet lam := by
      refine ⟨p', fun t => ⟨le_trans (hc0 t).1 (hc'_ge t), hc'_le1 t⟩, ?_, ?_, ?_⟩
      · -- IsAtkProfile p'
        intro θ
        by_cases hθ : θ ∈ ΘS
        · by_cases hπpos : 0 < G.π θ
          · refine ⟨?_, ?_⟩
            · dsimp only [p']
              simp only [dif_pos hθ, dif_pos hπpos]
              have hsum : ∑ t : Fin n,
                  (if ht : t ∈ S then fstar (eΘ ⟨θ, hθ⟩) (eS ⟨t, ht⟩) / G.π θ else 0) =
                  (∑ j : Fin (Fintype.card {t : Fin n // t ∈ S}),
                    fstar (eΘ ⟨θ, hθ⟩) j) / G.π θ := by
                rw [Finset.sum_div, ← eS.sum_comp]
                convert (sum_subtype_ite (fun t : Fin n => t ∈ S)
                  (fun t => fstar (eΘ ⟨θ, hθ⟩) (eS t) / G.π θ)).symm
              rw [hsum, hf_row (eΘ ⟨θ, hθ⟩)]
              simp only [π', Equiv.symm_apply_apply]
              exact div_self (ne_of_gt hπpos)
            · intro t; dsimp only [p']; simp only [dif_pos hθ, dif_pos hπpos]
              split_ifs; exact div_nonneg (hf_nn _ _) (le_of_lt hπpos); exact le_rfl
          · refine ⟨by simp [p', hθ, hπpos], fun t => by simp only [p', dif_pos hθ, dif_neg hπpos]; split_ifs <;> linarith⟩
        · have hs_notS : Classical.choose (hout_ex θ hθ) ∉ S := (Classical.choose_spec (hout_ex θ hθ)).2
          refine ⟨?_, ?_⟩
          · dsimp only [p']; simp only [dif_neg hθ]
            have h1 : ∑ t : Fin n, (if t ∈ S then (0 : ℝ) else
                p0 θ t + if t = Classical.choose (hout_ex θ hθ) then ∑ r ∈ S, p0 θ r else 0) =
                (∑ t ∈ Finset.univ \ S, p0 θ t) + ∑ r ∈ S, p0 θ r := by
              rw [Finset.sum_ite, Finset.sum_const_zero, zero_add]
              have hfilt : Finset.univ.filter (fun t : Fin n => t ∉ S) = Finset.univ \ S := by
                ext t; simp
              rw [hfilt, Finset.sum_add_distrib, Finset.sum_ite_eq']
              simp [hs_notS]
            rw [h1, Finset.sum_sdiff (Finset.subset_univ S)]
            exact (hp0 θ).1
          · intro t; dsimp only [p']; simp only [dif_neg hθ]
            split_ifs
            · exact le_rfl
            · linarith [(hp0 θ).2 t, Finset.sum_nonneg (s := S) fun r _ => (hp0 θ).2 r]
            · linarith [(hp0 θ).2 t]
      · -- IsAtkBR c' p'
        intro θ t r hpos
        by_cases hθ : θ ∈ ΘS
        · by_cases hπpos : 0 < G.π θ
          · dsimp only [p'] at hpos; simp only [dif_pos hθ, dif_pos hπpos] at hpos
            have htS : t ∈ S := by by_contra h; simp [h] at hpos
            simp only [dif_pos htS] at hpos
            have hfpos : 0 < fstar (eΘ ⟨θ, hθ⟩) (eS ⟨t, htS⟩) := (div_pos_iff_of_pos_right hπpos).mp hpos
            have htB : t ∈ B θ := by
              by_contra hnB
              have : ¬ E' (eΘ ⟨θ, hθ⟩) (eS ⟨t, htS⟩) := by simpa [E'] using hnB
              linarith [hf_supp _ _ this]
            have hcs_eq := hcs (eΘ ⟨θ, hθ⟩) (eS ⟨t, htS⟩) hfpos
            simp only [α', Equiv.symm_apply_apply] at hcs_eq
            by_cases hrB : r ∈ B θ
            · have hrS : r ∈ S := (Finset.mem_filter.mp hθ).2 hrB
              have hdu := hdual (eΘ ⟨θ, hθ⟩) (eS ⟨r, hrS⟩) (by simpa [E'] using hrB)
              simp only [α', Equiv.symm_apply_apply] at hdu
              have hlog_le : Real.log (G.a θ t * w t) ≤ Real.log (G.a θ r * w r) := by
                have h1 : Real.log (G.a θ t * w t) = Real.log (G.a θ t) - z (eS ⟨t, htS⟩) := by
                  rw [Real.log_mul (ne_of_gt (ha_pos θ t)) (ne_of_gt (hw_pos t htS))]
                  simp [w, htS, Real.log_exp]; ring
                have h2 : Real.log (G.a θ r * w r) = Real.log (G.a θ r) - z (eS ⟨r, hrS⟩) := by
                  rw [Real.log_mul (ne_of_gt (ha_pos θ r)) (ne_of_gt (hw_pos r hrS))]
                  simp [w, hrS, Real.log_exp]; ring
                linarith
              have haw_le : G.a θ t * w t ≤ G.a θ r * w r := by
                have := Real.exp_le_exp.mpr hlog_le
                rwa [Real.exp_log (mul_pos (ha_pos θ t) (hw_pos t htS)),
                  Real.exp_log (mul_pos (ha_pos θ r) (hw_pos r hrS))] at this
              have hu_eq : G.uA cstar θ t = G.uA cstar θ r := by
                rw [(Finset.mem_filter.mp htB).2, (Finset.mem_filter.mp hrB).2]
              have h1 : G.uA c' θ t = G.uA cstar θ t - δ * (G.a θ t * w t) := by
                simp only [uA, c']; ring
              have h2 : G.uA c' θ r = G.uA cstar θ r - δ * (G.a θ r * w r) := by
                simp only [uA, c']; ring
              nlinarith
            · have hleδ : δ ≤ (G.uA cstar θ t - G.uA cstar θ r) / (G.a θ t * w t) := by
                refine Finset.min'_le gapCap _ (Finset.mem_union_right _ ?_)
                refine Finset.mem_image.mpr ⟨(θ, t, r), ?_, rfl⟩
                exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hθ, htB, hrB⟩
              have h1 : δ * (G.a θ t * w t) ≤ G.uA cstar θ t - G.uA cstar θ r :=
                (le_div_iff₀ (mul_pos (ha_pos θ t) (hw_pos t htS))).mp hleδ
              have h2 : G.uA c' θ t = G.uA cstar θ t - δ * (G.a θ t * w t) := by
                simp only [uA, c']; ring
              have h3 : G.uA c' θ r ≤ G.uA cstar θ r := G.uA_anti hc'_ge θ r
              linarith
          · dsimp only [p'] at hpos; simp only [dif_pos hθ, dif_neg hπpos] at hpos
            have ht : t = argmax' θ := by by_contra hne; simp [hne] at hpos
            rw [ht, hargmax' θ]; exact G.le_maxUtil c' θ r
        · dsimp only [p'] at hpos; simp only [dif_neg hθ] at hpos
          have htS : t ∉ S := fun h => by simp [h] at hpos
          simp only [if_neg htS] at hpos
          have htB : t ∈ B θ := by
            by_cases hteq : t = Classical.choose (hout_ex θ hθ)
            · rw [hteq]; exact (Classical.choose_spec (hout_ex θ hθ)).1
            · simp only [if_neg hteq, add_zero] at hpos
              exact Finset.mem_filter.mpr ⟨Finset.mem_univ t,
                (G.isAtkBR_iff_maxUtil cstar p0).mp hbr0 θ t hpos⟩
          have hc't : c' t = cstar t := by simp [c', w, htS]
          have hut : G.uA c' θ t = G.maxUtil cstar θ := by
            rw [show G.uA c' θ t = G.uA cstar θ t by simp [uA, hc't]]
            exact (Finset.mem_filter.mp htB).2
          exact le_trans (G.uA_anti hc'_ge θ r) (by linarith [G.le_maxUtil cstar θ r])
      · -- Lower defender BR: `0 < c' t → lam ≤ G.gain p' t`
        intro t htpos
        by_cases htS : t ∈ S
        · have hsum_ge : s t ≤ ∑ θ : Fin m, G.π θ * p' θ t := by
            have hcol := hf_col (eS ⟨t, htS⟩)
            simp only [Bool.false_eq_true, ↓reduceIte, s', Equiv.symm_apply_apply] at hcol
            calc s t ≤ ∑ i : Fin (Fintype.card {θ : Fin m // θ ∈ ΘS}),
                  fstar i (eS ⟨t, htS⟩) := hcol
              _ = ∑ θ ∈ ΘS, G.π θ * p' θ t := by
                  rw [← eΘ.sum_comp, ← Finset.sum_coe_sort ΘS]
                  refine Finset.sum_congr rfl fun θ _ => ?_
                  by_cases hπpos : 0 < G.π θ.1
                  · simp only [p', dif_pos θ.2, dif_pos hπpos, dif_pos htS]
                    exact (mul_div_cancel₀ _ (ne_of_gt hπpos)).symm
                  · have hπ0 : G.π θ.1 = 0 := le_antisymm (not_lt.mp hπpos) (G.hπ_nn θ.1)
                    have hrow := hf_row (eΘ θ)
                    simp only [π', Equiv.symm_apply_apply, hπ0] at hrow
                    have hf0 : fstar (eΘ θ) (eS ⟨t, htS⟩) = 0 :=
                      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hf_nn _ j)).mp hrow _
                        (Finset.mem_univ _)
                    rw [hf0, hπ0, zero_mul]
              _ ≤ ∑ θ : Fin m, G.π θ * p' θ t := by
                  refine Finset.sum_le_univ_sum_of_nonneg fun θ => mul_nonneg (G.hπ_nn θ) ?_
                  by_cases hθ : θ ∈ ΘS
                  · by_cases hπpos : 0 < G.π θ
                    · simp only [p', dif_pos hθ, dif_pos hπpos, dif_pos htS]
                      exact div_nonneg (hf_nn _ _) (le_of_lt hπpos)
                    · simp only [p', dif_pos hθ, dif_neg hπpos]; split_ifs <;> linarith
                  · simp [p', hθ, htS]
          have := mul_le_mul_of_nonneg_right hsum_ge (le_of_lt (hd_pos t))
          simpa [gain, s, div_mul_cancel₀ _ (ne_of_gt (hd_pos t))] using this
        · have hc't : c' t = cstar t := by simp [c', w, htS]
          have hctpos : 0 < cstar t := by linarith
          have hgain_ge : G.gain p0 t ≤ G.gain p' t := by
            refine mul_le_mul_of_nonneg_right (Finset.sum_le_sum fun θ _ => ?_) (G.hd_nn t)
            by_cases hθ : θ ∈ ΘS
            · have hp0_zero : p0 θ t = 0 := by
                by_contra hne
                have hpos : 0 < p0 θ t := lt_of_le_of_ne ((hp0 θ).2 t) (Ne.symm hne)
                have htB : t ∈ B θ := Finset.mem_filter.mpr
                  ⟨Finset.mem_univ t, (G.isAtkBR_iff_maxUtil cstar p0).mp hbr0 θ t hpos⟩
                exact htS ((Finset.mem_filter.mp hθ).2 htB)
              rw [hp0_zero, mul_zero]
              refine mul_nonneg (G.hπ_nn θ) ?_
              by_cases hπpos : 0 < G.π θ
              · simp [p', hθ, hπpos, htS]
              · simp only [p', dif_pos hθ, dif_neg hπpos]; split_ifs <;> linarith
            · refine mul_le_mul_of_nonneg_left ?_ (G.hπ_nn θ)
              simp only [p', dif_neg hθ, if_neg htS]
              split_ifs
              · linarith [Finset.sum_nonneg (s := S) fun r _ => (hp0 θ).2 r]
              · linarith
          linarith [hlo0 t hctpos]
    -- Contradiction: `c' ∈ LowerSet G lam`, yet `c' t0 > cstar t0`!
    obtain ⟨t0, ht0S⟩ := hS_ne
    have hle := hcstar_max c' hc'_mem t0
    have hgt : cstar t0 < c' t0 := by
      dsimp only [c']; nlinarith [hw_pos t0 ht0S]
    linarith
  -- Now `hno_over` holds for all `S ⊆ Tlt1`, AND `p0` satisfies all lower bounds on `{t | cstar t > 0}`!
  -- Construct a flow `pstar` supported on `B θ` satisfying BOTH lower and upper bounds via `fourier_motzkin`!
  let Edge := {p : Fin m × Fin n // p.2 ∈ B p.1}
  let eV := Fintype.equivFin Edge
  let Row := Edge ⊕ (Fin m ⊕ (Fin m ⊕ (Fin n ⊕ Fin n)))
  let eR := Fintype.equivFin Row
  let aF : Fin (Fintype.card Row) → Fin (Fintype.card Edge) → ℝ := fun r c =>
    let q := eV.symm c
    match eR.symm r with
    | Sum.inl q' => if q = q' then -1 else 0
    | Sum.inr (Sum.inl θ) => if q.1.1 = θ then 1 else 0
    | Sum.inr (Sum.inr (Sum.inl θ)) => if q.1.1 = θ then -1 else 0
    | Sum.inr (Sum.inr (Sum.inr (Sum.inl t))) => if 0 < cstar t ∧ q.1.2 = t then -1 else 0
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr t))) => if cstar t < 1 ∧ q.1.2 = t then 1 else 0
  let bF : Fin (Fintype.card Row) → ℝ := fun r =>
    match eR.symm r with
    | Sum.inl _ => 0
    | Sum.inr (Sum.inl θ) => G.π θ
    | Sum.inr (Sum.inr (Sum.inl θ)) => -G.π θ
    | Sum.inr (Sum.inr (Sum.inr (Sum.inl t))) => if 0 < cstar t then -s t else 0
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr t))) => if cstar t < 1 then s t else 0
  rcases fourier_motzkin (Fintype.card Edge) aF bF with ⟨x, hx⟩ | ⟨w, hw_nn, hw_eq, hw_lt⟩
  · let f : Fin m → Fin n → ℝ := fun θ t =>
      if h : t ∈ B θ then x (eV ⟨(θ, t), h⟩) else 0
    have hf_nn : ∀ θ t, 0 ≤ f θ t := by
      intro θ t; dsimp only [f]; split_ifs with h
      · have := hx (eR (Sum.inl ⟨(θ, t), h⟩))
        simp only [aF, bF, Equiv.symm_apply_apply] at this
        have hsum : ∑ c : Fin (Fintype.card Edge),
            (if eV.symm c = ⟨(θ, t), h⟩ then (-1 : ℝ) else 0) * x c = -x (eV ⟨(θ, t), h⟩) := by
          rw [Finset.sum_eq_single (eV ⟨(θ, t), h⟩)]
          · simp
          · intro c _ hne; simp [show eV.symm c ≠ ⟨(θ, t), h⟩ from fun heq => hne (by rw [← heq]; simp)]
          · intro habs; exact absurd (Finset.mem_univ _) habs
        linarith
      · exact le_rfl
    have hf_row : ∀ θ, ∑ t : Fin n, f θ t = G.π θ := by
      intro θ
      have hle := hx (eR (Sum.inr (Sum.inl θ)))
      have hge := hx (eR (Sum.inr (Sum.inr (Sum.inl θ))))
      simp only [aF, bF, Equiv.symm_apply_apply] at hle hge
      have h1 : ∑ c : Fin (Fintype.card Edge),
          (if (eV.symm c).1.1 = θ then (1 : ℝ) else 0) * x c = ∑ t : Fin n, f θ t := by
        rw [← eV.sum_comp]; simp only [Equiv.symm_apply_apply]
        calc ∑ q : Edge, (if q.1.1 = θ then (1 : ℝ) else 0) * x (eV q)
            = ∑ q : Fin m × Fin n, if h : q.2 ∈ B q.1 then
                (if q.1 = θ then (1 : ℝ) else 0) * x (eV ⟨q, h⟩) else 0 := by
                exact sum_subtype_ite _ _
          _ = ∑ θ' : Fin m, ∑ t : Fin n, if h : t ∈ B θ' then
                (if θ' = θ then (1 : ℝ) else 0) * x (eV ⟨(θ', t), h⟩) else 0 := Fintype.sum_prod_type _
          _ = ∑ t : Fin n, f θ t := by
                rw [Finset.sum_eq_single θ]
                · refine Finset.sum_congr rfl fun t _ => by dsimp only [f]; by_cases hB : t ∈ B θ <;> simp [hB]
                · intro θ' _ hne; refine Finset.sum_eq_zero fun t _ => by split_ifs <;> simp
                · intro habs; exact absurd (Finset.mem_univ _) habs
      have h2 : ∑ c : Fin (Fintype.card Edge),
          (if (eV.symm c).1.1 = θ then (-1 : ℝ) else 0) * x c = -∑ t : Fin n, f θ t := by
        have : ∀ c, (if (eV.symm c).1.1 = θ then (-1 : ℝ) else 0) * x c =
            -((if (eV.symm c).1.1 = θ then (1 : ℝ) else 0) * x c) := fun c => by split_ifs <;> ring
        simp only [this, Finset.sum_neg_distrib, h1]
      linarith
    have hf_col_lo : ∀ t, 0 < cstar t → s t ≤ ∑ θ : Fin m, f θ t := by
      intro t htpos
      have h := hx (eR (Sum.inr (Sum.inr (Sum.inr (Sum.inl t)))))
      simp only [aF, bF, Equiv.symm_apply_apply, htpos, true_and, ↓reduceIte] at h
      have hsum : ∑ c : Fin (Fintype.card Edge),
          (if (eV.symm c).1.2 = t then (-1 : ℝ) else 0) * x c = -∑ θ : Fin m, f θ t := by
        rw [← eV.sum_comp]; simp only [Equiv.symm_apply_apply]
        calc ∑ q : Edge, (if q.1.2 = t then (-1 : ℝ) else 0) * x (eV q)
            = ∑ q : Fin m × Fin n, if hB : q.2 ∈ B q.1 then
                (if q.2 = t then (-1 : ℝ) else 0) * x (eV ⟨q, hB⟩) else 0 := by
                exact sum_subtype_ite _ _
          _ = ∑ θ : Fin m, ∑ t' : Fin n, if hB : t' ∈ B θ then
                (if t' = t then (-1 : ℝ) else 0) * x (eV ⟨(θ, t'), hB⟩) else 0 := Fintype.sum_prod_type _
          _ = ∑ θ : Fin m, -f θ t := by
                refine Finset.sum_congr rfl fun θ _ => ?_
                rw [Finset.sum_eq_single t]
                · dsimp only [f]; by_cases hB : t ∈ B θ <;> simp [hB]
                · intro t' _ hne; split_ifs <;> simp
                · intro habs; exact absurd (Finset.mem_univ _) habs
          _ = -∑ θ : Fin m, f θ t := by rw [Finset.sum_neg_distrib]
      linarith
    have hf_col_hi : ∀ t, cstar t < 1 → ∑ θ : Fin m, f θ t ≤ s t := by
      intro t htlt
      have h := hx (eR (Sum.inr (Sum.inr (Sum.inr (Sum.inr t)))))
      simp only [aF, bF, Equiv.symm_apply_apply, htlt, true_and, ↓reduceIte] at h
      have hsum : ∑ c : Fin (Fintype.card Edge),
          (if (eV.symm c).1.2 = t then (1 : ℝ) else 0) * x c = ∑ θ : Fin m, f θ t := by
        rw [← eV.sum_comp]; simp only [Equiv.symm_apply_apply]
        calc ∑ q : Edge, (if q.1.2 = t then (1 : ℝ) else 0) * x (eV q)
            = ∑ q : Fin m × Fin n, if hB : q.2 ∈ B q.1 then
                (if q.2 = t then (1 : ℝ) else 0) * x (eV ⟨q, hB⟩) else 0 := by
                exact sum_subtype_ite _ _
          _ = ∑ θ : Fin m, ∑ t' : Fin n, if hB : t' ∈ B θ then
                (if t' = t then (1 : ℝ) else 0) * x (eV ⟨(θ, t'), hB⟩) else 0 := Fintype.sum_prod_type _
          _ = ∑ θ : Fin m, f θ t := by
                refine Finset.sum_congr rfl fun θ _ => ?_
                rw [Finset.sum_eq_single t]
                · dsimp only [f]; by_cases hB : t ∈ B θ <;> simp [hB]
                · intro t' _ hne; split_ifs <;> simp
                · intro habs; exact absurd (Finset.mem_univ _) habs
      linarith
    choose tB htB using hB_ne
    let pstar : Fin m → Fin n → ℝ := fun θ t =>
      if hπ : 0 < G.π θ then f θ t / G.π θ else if t = tB θ then 1 else 0
    have hπp : ∀ θ t, G.π θ * pstar θ t = f θ t := by
      intro θ t; dsimp only [pstar]; split_ifs with hπ
      · exact mul_div_cancel₀ _ (ne_of_gt hπ)
      · have hπ0 : G.π θ = 0 := le_antisymm (not_lt.mp hπ) (G.hπ_nn θ)
        have hf0 : f θ t = 0 :=
          (Finset.sum_eq_zero_iff_of_nonneg (fun t' _ => hf_nn θ t')).mp
            (by rw [hf_row θ, hπ0]) t (Finset.mem_univ t)
        rw [hπ0, zero_mul, hf0]
      · have hπ0 : G.π θ = 0 := le_antisymm (not_lt.mp hπ) (G.hπ_nn θ)
        have hf0 : f θ t = 0 :=
          (Finset.sum_eq_zero_iff_of_nonneg (fun t' _ => hf_nn θ t')).mp
            (by rw [hf_row θ, hπ0]) t (Finset.mem_univ t)
        rw [hπ0, zero_mul, hf0]
    refine ⟨pstar, ⟨hc0, ?_, ?_, ?_⟩, ?_⟩
    · intro θ; dsimp only [pstar]; split_ifs with hπ
      · refine ⟨by rw [← Finset.sum_div, hf_row θ, div_self (ne_of_gt hπ)],
          fun t => div_nonneg (hf_nn θ t) (le_of_lt hπ)⟩
      · refine ⟨by simp, fun t => by split_ifs <;> linarith⟩
    · rw [G.isAtkBR_iff_maxUtil]
      intro θ t hpos
      by_cases hπ : 0 < G.π θ
      · simp only [pstar, dif_pos hπ] at hpos
        have hfpos : 0 < f θ t := (div_pos_iff_of_pos_right hπ).mp hpos
        have htB' : t ∈ B θ := by by_contra h; simp [f, h] at hfpos
        exact (Finset.mem_filter.mp htB').2
      · simp only [pstar, dif_neg hπ] at hpos
        have ht : t = tB θ := by by_contra hne; simp [hne] at hpos
        rw [ht]; exact (Finset.mem_filter.mp (htB θ)).2
    · intro t htpos
      simp only [gain, hπp]
      have := mul_le_mul_of_nonneg_right (hf_col_lo t htpos) (le_of_lt (hd_pos t))
      simpa [s, div_mul_cancel₀ _ (ne_of_gt (hd_pos t))] using this
    · intro t htlt
      simp only [gain, hπp]
      have := mul_le_mul_of_nonneg_right (hf_col_hi t htlt) (le_of_lt (hd_pos t))
      simpa [s, div_mul_cancel₀ _ (ne_of_gt (hd_pos t))] using this
  · -- Farkas certificate contradicts `p0` (lower feasibility) + `hno_over` (upper feasibility)!
    exfalso
    let u : Fin m → ℝ := fun θ =>
      w (eR (Sum.inr (Sum.inl θ))) - w (eR (Sum.inr (Sum.inr (Sum.inl θ))))
    let vL : Fin n → ℝ := fun t =>
      if 0 < cstar t then w (eR (Sum.inr (Sum.inr (Sum.inr (Sum.inl t))))) else 0
    let vU : Fin n → ℝ := fun t =>
      if cstar t < 1 then w (eR (Sum.inr (Sum.inr (Sum.inr (Sum.inr t))))) else 0
    have hvL_nn : ∀ t, 0 ≤ vL t := fun t => by dsimp only [vL]; split_ifs; exact hw_nn _; exact le_rfl
    have hvU_nn : ∀ t, 0 ≤ vU t := fun t => by dsimp only [vU]; split_ifs; exact hw_nn _; exact le_rfl
    have hEdge_ineq : ∀ θ t, t ∈ B θ → vL t - vU t ≤ u θ := by
      intro θ t htB
      have h := hw_eq (eV ⟨(θ, t), htB⟩)
      rw [← eR.sum_comp] at h
      dsimp only [Row] at h
      simp only [aF, Equiv.symm_apply_apply, Fintype.sum_sum_type] at h
      have h1 : ∑ q : Edge, w (eR (Sum.inl q)) *
          (if (⟨(θ, t), htB⟩ : Edge) = q then (-1 : ℝ) else 0) =
          -w (eR (Sum.inl ⟨(θ, t), htB⟩)) := by
        rw [Finset.sum_eq_single ⟨(θ, t), htB⟩]
        · simp
        · intro q _ hne; simp [Ne.symm hne]
        · intro habs; exact absurd (Finset.mem_univ _) habs
      have h2 : ∑ θ' : Fin m, w (eR (Sum.inr (Sum.inl θ'))) *
          (if θ = θ' then (1 : ℝ) else 0) = w (eR (Sum.inr (Sum.inl θ))) := by
        rw [Finset.sum_eq_single θ]
        · simp
        · intro θ' _ hne; simp [Ne.symm hne]
        · intro habs; exact absurd (Finset.mem_univ _) habs
      have h3 : ∑ θ' : Fin m, w (eR (Sum.inr (Sum.inr (Sum.inl θ')))) *
          (if θ = θ' then (-1 : ℝ) else 0) = -w (eR (Sum.inr (Sum.inr (Sum.inl θ)))) := by
        rw [Finset.sum_eq_single θ]
        · simp
        · intro θ' _ hne; simp [Ne.symm hne]
        · intro habs; exact absurd (Finset.mem_univ _) habs
      have h4 : ∑ t' : Fin n, w (eR (Sum.inr (Sum.inr (Sum.inr (Sum.inl t'))))) *
          (if 0 < cstar t' ∧ t = t' then (-1 : ℝ) else 0) = -vL t := by
        rw [Finset.sum_eq_single t]
        · dsimp only [vL]; by_cases hpos : 0 < cstar t <;> simp [hpos]
        · intro t' _ hne; simp [Ne.symm hne]
        · intro habs; exact absurd (Finset.mem_univ _) habs
      have h5 : ∑ t' : Fin n, w (eR (Sum.inr (Sum.inr (Sum.inr (Sum.inr t'))))) *
          (if cstar t' < 1 ∧ t = t' then (1 : ℝ) else 0) = vU t := by
        rw [Finset.sum_eq_single t]
        · dsimp only [vU]; by_cases hlt : cstar t < 1 <;> simp [hlt]
        · intro t' _ hne; simp [Ne.symm hne]
        · intro habs; exact absurd (Finset.mem_univ _) habs
      rw [h1, h2, h3, h4, h5] at h
      have hwnn := hw_nn (eR (Sum.inl ⟨(θ, t), htB⟩))
      dsimp only [u]
      linarith
    have hlt_w : ∑ θ : Fin m, G.π θ * u θ + ∑ t : Fin n, s t * (vU t - vL t) < 0 := by
      rw [← eR.sum_comp] at hw_lt
      dsimp only [Row] at hw_lt
      simp only [bF, Equiv.symm_apply_apply, Fintype.sum_sum_type, mul_zero,
        Finset.sum_const_zero, zero_add] at hw_lt
      have h1 : ∑ θ : Fin m, G.π θ * u θ =
          (∑ θ : Fin m, w (eR (Sum.inr (Sum.inl θ))) * G.π θ) +
          (∑ θ : Fin m, w (eR (Sum.inr (Sum.inr (Sum.inl θ)))) * -G.π θ) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun θ _ => by dsimp only [u]; ring
      have h2 : ∑ t : Fin n, s t * (vU t - vL t) =
          (∑ t : Fin n, w (eR (Sum.inr (Sum.inr (Sum.inr (Sum.inl t))))) *
            if 0 < cstar t then -s t else 0) +
          (∑ t : Fin n, w (eR (Sum.inr (Sum.inr (Sum.inr (Sum.inr t))))) *
            if cstar t < 1 then s t else 0) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun t _ => by dsimp only [vU, vL]; split_ifs <;> ring
      linarith
    -- Split `u` and `vU - vL` via positive and negative parts!
    -- Wait: let `z t = vL t - vU t`, so `z t ≤ u θ` on `B θ` and `∑ π θ * u θ < ∑ s t * z t`!
    -- Split into `z⁺ t = max (z t) 0 ≤ vL t` and `z⁻ t = max (-z t) 0 ≤ vU t`:
    -- Notice `u θ = u⁺ θ - u⁻ θ`? Even simpler:
    -- Since `z t ≤ u θ` on `B θ`, we have `max (z t) 0 ≤ max (u θ) 0` AND `max (-u θ) 0 ≤ max (-z t) 0`!
    -- Check `∑ π θ * u θ - ∑ s t * z t = (∑ π θ * max (u θ) 0 - ∑ s t * max (z t) 0) + (∑ s t * max (-z t) 0 - ∑ π θ * max (-u θ) 0)`!
    let z : Fin n → ℝ := fun t => vL t - vU t
    have hsplit_ineq :
        (∑ θ : Fin m, G.π θ * max (u θ) 0 - ∑ t : Fin n, s t * max (z t) 0) +
        (∑ t : Fin n, s t * max (-z t) 0 - ∑ θ : Fin m, G.π θ * max (-u θ) 0) < 0 := by
      have hident :
          (∑ θ : Fin m, G.π θ * max (u θ) 0 - ∑ t : Fin n, s t * max (z t) 0) +
          (∑ t : Fin n, s t * max (-z t) 0 - ∑ θ : Fin m, G.π θ * max (-u θ) 0) =
          ∑ θ : Fin m, G.π θ * u θ + ∑ t : Fin n, s t * (vU t - vL t) := by
        have hu_id : ∀ θ, max (u θ) 0 - max (-u θ) 0 = u θ := fun θ => by
          rcases le_or_gt 0 (u θ) with h | h
          · rw [max_eq_left h, max_eq_right (by linarith)]; ring
          · rw [max_eq_right (le_of_lt h), max_eq_left (by linarith)]; ring
        have hz_id : ∀ t, max (-z t) 0 - max (z t) 0 = vU t - vL t := fun t => by
          dsimp only [z]
          rcases le_or_gt 0 (vL t - vU t) with h | h
          · rw [max_eq_left h, max_eq_right (by linarith)]; ring
          · rw [max_eq_right (le_of_lt h), max_eq_left (by linarith)]; ring
        calc (∑ θ : Fin m, G.π θ * max (u θ) 0 - ∑ t : Fin n, s t * max (z t) 0) +
              (∑ t : Fin n, s t * max (-z t) 0 - ∑ θ : Fin m, G.π θ * max (-u θ) 0)
            = (∑ θ : Fin m, G.π θ * (max (u θ) 0 - max (-u θ) 0)) +
              (∑ t : Fin n, s t * (max (-z t) 0 - max (z t) 0)) := by
                simp only [mul_sub, Finset.sum_sub_distrib]; ring
          _ = ∑ θ : Fin m, G.π θ * u θ + ∑ t : Fin n, s t * (vU t - vL t) := by
                simp only [hu_id, hz_id]
      linarith
    -- First bracket is `≥ 0` because of `p0`!
    have hbr1 : 0 ≤ ∑ θ : Fin m, G.π θ * max (u θ) 0 - ∑ t : Fin n, s t * max (z t) 0 := by
      have h1 : ∑ t : Fin n, s t * max (z t) 0 ≤
          ∑ t : Fin n, (∑ θ : Fin m, G.π θ * p0 θ t) * max (z t) 0 := by
        refine Finset.sum_le_sum fun t _ => ?_
        by_cases hpos : 0 < cstar t
        · have hgain := hlo0 t hpos
          have hsle : s t ≤ ∑ θ : Fin m, G.π θ * p0 θ t :=
            (div_le_iff₀ (hd_pos t)).mpr hgain
          exact mul_le_mul_of_nonneg_right hsle (le_max_right _ _)
        · have hvL0 : vL t = 0 := by simp [vL, hpos]
          have hz0 : max (z t) 0 = 0 := max_eq_right (by dsimp only [z]; linarith [hvU_nn t])
          rw [hz0, mul_zero, mul_zero]
      have h2 : ∑ t : Fin n, (∑ θ : Fin m, G.π θ * p0 θ t) * max (z t) 0 ≤
          ∑ θ : Fin m, G.π θ * max (u θ) 0 := by
        calc ∑ t : Fin n, (∑ θ : Fin m, G.π θ * p0 θ t) * max (z t) 0
            = ∑ θ : Fin m, ∑ t : Fin n, G.π θ * p0 θ t * max (z t) 0 := by
                simp only [Finset.sum_mul]; rw [Finset.sum_comm]
          _ ≤ ∑ θ : Fin m, ∑ t : Fin n, G.π θ * p0 θ t * max (u θ) 0 := by
                refine Finset.sum_le_sum fun θ _ => Finset.sum_le_sum fun t _ => ?_
                by_cases hppos : 0 < p0 θ t
                · have htB : t ∈ B θ := Finset.mem_filter.mpr
                    ⟨Finset.mem_univ t, (G.isAtkBR_iff_maxUtil cstar p0).mp hbr0 θ t hppos⟩
                  exact mul_le_mul_of_nonneg_left (max_le_max_right 0 (hEdge_ineq θ t htB))
                    (mul_nonneg (G.hπ_nn θ) (le_of_lt hppos))
                · have hpzero : p0 θ t = 0 := le_antisymm (not_lt.mp hppos) ((hp0 θ).2 t)
                  simp [hpzero]
          _ = ∑ θ : Fin m, G.π θ * max (u θ) 0 := by
                refine Finset.sum_congr rfl fun θ _ => ?_
                calc ∑ t : Fin n, G.π θ * p0 θ t * max (u θ) 0
                    = (G.π θ * ∑ t : Fin n, p0 θ t) * max (u θ) 0 := by
                        rw [← Finset.sum_mul, ← Finset.mul_sum]
                  _ = G.π θ * max (u θ) 0 := by rw [(hp0 θ).1, mul_one]
      linarith
    -- Therefore the second bracket MUST be `< 0`, contradicting `hno_over` via layer-cake!
    have hbr2 : ∑ t : Fin n, s t * max (-z t) 0 < ∑ θ : Fin m, G.π θ * max (-u θ) 0 := by linarith
    -- Dual layer-cake: flip `(θ, t)` roles with `u_new t = max (-z t) 0`, `v_new θ = max (-u θ) 0`!
    -- For every `θ` and `t ∈ B θ`, `max (-u θ) 0 ≤ max (-z t) 0`, and if `cstar t = 1` then `vU t = 0` so `max (-z t) 0 = 0`!
    have h_lc := layer_cake_hall (m := n) (n := m) s G.π (fun t θ => t ∈ B θ)
      (fun t => div_nonneg (le_of_lt hlam) (le_of_lt (hd_pos t)))
      _ (fun t => max (-z t) 0) (fun θ => max (-u θ) 0) le_rfl
      (fun t => le_max_right _ _) (fun θ => le_max_right _ _)
      (fun t θ htB => max_le_max_right 0 (by linarith [hEdge_ineq θ t htB]))
      hbr2
    obtain ⟨ΘR, hΘR⟩ := h_lc
    -- Look at `S := {t | ∃ θ ∈ ΘR, t ∈ B θ}`! Wait: check if `S ⊆ Tlt1`!
    -- Actually in `h_lc`, the LHS sums `s t` over `S = {t | ∃ θ ∈ ΘR, t ∈ B θ}`, and RHS sums `π θ` over `ΘR`!
    -- Wait: what if `S` contains a target `t` with `cstar t = 1`?!
    -- If `cstar t = 1`, then `vU t = 0`, so `-z t = -vL t ≤ 0`, so `max (-z t) 0 = 0`, so `max (-u θ) 0 = 0` for all `θ` with `t ∈ B θ`!
    -- Better: restrict `v_new θ` by filtering out `θ` with `B θ ⊄ Tlt1` (for such `θ`, `max (-u θ) 0 = 0` anyway!)
    let S_bad : Finset (Fin n) := Finset.univ.filter fun t => ∃ θ ∈ ΘR, t ∈ B θ
    -- Wait: if `cstar t = 1` and `t ∈ S_bad`, could `t` be in `S_bad` even though `u_new t = 0`?
    -- Yes, if `ΘR` included some `θ` with `v_new θ = 0`! Wait: `layer_cake_hall` ONLY puts `θ` with `v_new θ ≥ δ > 0` into `ΘR`!
    -- Even cleaner: filter `ΘR` to `ΘR' := ΘR.filter (fun θ => B θ ⊆ Tlt1)` — NO, `s t` is nonnegative,
    -- instead just check directly: apply `layer_cake_hall` with `s_eff t := if cstar t < 1 then s t else 0`!
    have hbr2' : ∑ t : Fin n, (if cstar t < 1 then s t else 0) * max (-z t) 0 <
        ∑ θ : Fin m, G.π θ * max (-u θ) 0 := by
      have heq : ∀ t, (if cstar t < 1 then s t else 0) * max (-z t) 0 = s t * max (-z t) 0 := by
        intro t; split_ifs with hlt
        · rfl
        · have hvU0 : vU t = 0 := by simp [vU, hlt]
          have hmz0 : max (-z t) 0 = 0 := max_eq_right (by dsimp only [z]; linarith [hvL_nn t])
          rw [hmz0, mul_zero, mul_zero]
      simpa only [heq] using hbr2
    -- For `θ` with `¬ B θ ⊆ Tlt1`, pick `t ∈ B θ` with `¬ cstar t < 1`, then `max (-z t) 0 = 0`, so `max (-u θ) 0 = 0`!
    have hθ_out_zero : ∀ θ, ¬ B θ ⊆ Tlt1 → max (-u θ) 0 = 0 := by
      intro θ hnot
      obtain ⟨t, htB, htnot⟩ := Finset.not_subset.mp hnot
      have hlt : ¬ cstar t < 1 := fun h => htnot (Finset.mem_filter.mpr ⟨Finset.mem_univ t, h⟩)
      have hvU0 : vU t = 0 := by simp [vU, hlt]
      have hmz0 : max (-z t) 0 = 0 := max_eq_right (by dsimp only [z]; linarith [hvL_nn t])
      have hle : max (-u θ) 0 ≤ max (-z t) 0 := max_le_max_right 0 (by linarith [hEdge_ineq θ t htB])
      exact le_antisymm (by linarith) (le_max_right _ _)
    have hbr2'' : ∑ t : Fin n, (if cstar t < 1 then s t else 0) * max (-z t) 0 <
        ∑ θ : Fin m, (if B θ ⊆ Tlt1 then G.π θ else 0) * max (-u θ) 0 := by
      have heq : ∀ θ, (if B θ ⊆ Tlt1 then G.π θ else 0) * max (-u θ) 0 =
          G.π θ * max (-u θ) 0 := by
        intro θ; split_ifs with hsub
        · rfl
        · rw [hθ_out_zero θ hsub, mul_zero, mul_zero]
      simpa only [heq] using hbr2'
    obtain ⟨ΘR2, hΘR2⟩ := layer_cake_hall (m := n) (n := m)
      (fun t => if cstar t < 1 then s t else 0)
      (fun θ => if B θ ⊆ Tlt1 then G.π θ else 0)
      (fun t θ => t ∈ B θ)
      (fun t => by split_ifs; exact div_nonneg (le_of_lt hlam) (le_of_lt (hd_pos t)); exact le_rfl)
      _ (fun t => max (-z t) 0) (fun θ => max (-u θ) 0) le_rfl
      (fun t => le_max_right _ _) (fun θ => le_max_right _ _)
      (fun t θ htB => max_le_max_right 0 (by linarith [hEdge_ineq θ t htB]))
      hbr2''
    let S2 : Finset (Fin n) := Tlt1.filter fun t => ∃ θ ∈ ΘR2, t ∈ B θ
    have hS2_sub : S2 ⊆ Tlt1 := Finset.filter_subset _ _
    have hLHS_eq : ∑ t ∈ Finset.univ.filter (fun t => ∃ θ ∈ ΘR2, t ∈ B θ),
        (if cstar t < 1 then s t else 0) = ∑ t ∈ S2, s t := by
      rw [← Finset.sum_filter]
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext t; simp [S2, Tlt1, and_comm]
    have hRHS_le : ∑ θ ∈ ΘR2, (if B θ ⊆ Tlt1 then G.π θ else 0) ≤
        ∑ θ ∈ Finset.univ.filter (fun θ => B θ ⊆ S2), G.π θ := by
      rw [← Finset.sum_filter]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun θ _ _ => G.hπ_nn θ)
      intro θ hθ
      obtain ⟨hθR2, hθTlt1⟩ := Finset.mem_filter.mp hθ
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ θ, fun t htB => ?_⟩
      exact Finset.mem_filter.mpr ⟨hθTlt1 htB, ⟨θ, hθR2, htB⟩⟩
    linarith [hno_over S2 hS2_sub]

/-- Intermediate value property for total coverage at fixed `lam > 0` in a strictly positive game:
given ordered equilibria `cLo ≤ cHi` with `∑ cLo ≤ R ≤ ∑ cHi`, there is an equilibrium with `∑ c = R`. -/
lemma strict_eq_ivt (ha_pos : ∀ θ t, 0 < G.a θ t) (hd_pos : ∀ t, 0 < G.d t)
    {lam R : ℝ} (_hlam : 0 < lam)
    {cLo cHi : Fin n → ℝ} {pLo pHi : Fin m → Fin n → ℝ}
    (hLo : G.IsEq lam cLo pLo) (hHi : G.IsEq lam cHi pHi)
    (hle : ∀ t, cLo t ≤ cHi t) (hRlo : ∑ t, cLo t ≤ R) (hRhi : R ≤ ∑ t, cHi t) :
    ∃ c p, G.IsEq lam c p ∧ ∑ t, c t = R := by
  classical
  let K : Set ((Fin n → ℝ) × (Fin m → Fin n → ℝ)) :=
    {x | G.IsEq lam x.1 x.2 ∧ (∀ t, cLo t ≤ x.1 t ∧ x.1 t ≤ cHi t) ∧ ∑ t, x.1 t ≤ R}
  have hK_ne : K.Nonempty := ⟨(cLo, pLo), hLo, fun t => ⟨le_rfl, hle t⟩, hRlo⟩
  have hK_comp : IsCompact K := by
    have hc1 : IsClosed {x : (Fin n → ℝ) × (Fin m → Fin n → ℝ) |
        ∀ t, cLo t ≤ x.1 t ∧ x.1 t ≤ cHi t} := by
      have heq : {x : (Fin n → ℝ) × (Fin m → Fin n → ℝ) |
          ∀ t, cLo t ≤ x.1 t ∧ x.1 t ≤ cHi t} =
          ⋂ t : Fin n, ({x | cLo t ≤ x.1 t} ∩ {x | x.1 t ≤ cHi t}) := by ext x; simp
      rw [heq]
      exact isClosed_iInter fun t =>
        (isClosed_le continuous_const ((continuous_apply t).comp continuous_fst)).inter
        (isClosed_le ((continuous_apply t).comp continuous_fst) continuous_const)
    have hc2 : IsClosed {x : (Fin n → ℝ) × (Fin m → Fin n → ℝ) | ∑ t, x.1 t ≤ R} :=
      isClosed_le (continuous_finsetSum _ fun t _ => (continuous_apply t).comp continuous_fst)
        continuous_const
    exact (G.isCompact_eqPairs lam).inter_right (hc1.inter hc2)
  let sumObj : (Fin n → ℝ) × (Fin m → Fin n → ℝ) → ℝ := fun x => ∑ t, x.1 t
  have hsumCont : Continuous sumObj :=
    continuous_finsetSum _ fun t _ => (continuous_apply t).comp continuous_fst
  obtain ⟨⟨cB, pB⟩, ⟨hB_eq, hB_box, hB_leR⟩, hB_max⟩ :=
    hK_comp.exists_isMaxOn hK_ne hsumCont.continuousOn
  by_cases hhit : ∑ t, cB t = R
  · exact ⟨cB, pB, hB_eq, hhit⟩
  · exfalso
    have hB_ltR : ∑ t, cB t < R := lt_of_le_of_ne hB_leR hhit
    let J : Finset (Fin n) := Finset.univ.filter fun t => cB t < cHi t
    have hJ_ne : J.Nonempty := by
      by_contra hempty
      have heq : ∀ t, cB t = cHi t := fun t => by
        have hnot : ¬ cB t < cHi t := fun h =>
          hempty ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ t, h⟩⟩
        exact le_antisymm (hB_box t).2 (not_lt.mp hnot)
      have : ∑ t, cB t = ∑ t, cHi t := Finset.sum_congr rfl fun t _ => heq t
      linarith
    let B : Fin m → Finset (Fin n) := fun θ =>
      Finset.univ.filter fun t => G.uA cB θ t = G.maxUtil cB θ
    let ΘJ : Finset (Fin m) := Finset.univ.filter fun θ => B θ ⊆ J
    let s : Fin n → ℝ := fun t => lam / G.d t
    -- For `θ ∉ ΘJ`, `pHi θ t = 0` on `J`!
    have hpHi_out : ∀ θ, θ ∉ ΘJ → ∀ t ∈ J, pHi θ t = 0 := by
      intro θ hnot t htJ
      have : ¬ B θ ⊆ J := fun h => hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      obtain ⟨r, hrB, hrJ⟩ := Finset.not_subset.mp this
      have hcr : cB r = cHi r := le_antisymm (hB_box r).2 (not_lt.mp fun h =>
        hrJ (Finset.mem_filter.mpr ⟨Finset.mem_univ r, h⟩))
      have hct : cB t < cHi t := (Finset.mem_filter.mp htJ).2
      have hlt : G.uA cHi θ t < G.uA cHi θ r := by
        have h1 : G.uA cHi θ t < G.uA cB θ t := by simp only [uA]; nlinarith [ha_pos θ t]
        have h2 : G.uA cB θ t ≤ G.uA cB θ r := by
          rw [(Finset.mem_filter.mp hrB).2]; exact G.le_maxUtil cB θ t
        have h3 : G.uA cB θ r = G.uA cHi θ r := by simp [uA, hcr]
        linarith
      by_contra hne
      have hpos : 0 < pHi θ t := lt_of_le_of_ne ((hHi.1.2.1 θ).2 t) (Ne.symm hne)
      linarith [hHi.1.2.2.1 θ t r hpos]
    -- Sandwich chain on `J`:
    -- `∑_{t ∈ J} s t ≤ ∑_{t ∈ J} x_t(pHi) ≤ ∑_{θ ∈ ΘJ} π θ ≤ ∑_{t ∈ J} x_t(pB) ≤ ∑_{t ∈ J} s t`
    have h1 : ∑ t ∈ J, s t ≤ ∑ t ∈ J, ∑ θ : Fin m, G.π θ * pHi θ t := by
      refine Finset.sum_le_sum fun t htJ => ?_
      have htpos : 0 < cHi t := lt_of_le_of_lt (hB_eq.1.1 t).1 (Finset.mem_filter.mp htJ).2
      exact (div_le_iff₀ (hd_pos t)).mpr (hHi.1.2.2.2 t htpos)
    have h2 : ∑ t ∈ J, ∑ θ : Fin m, G.π θ * pHi θ t ≤ ∑ θ ∈ ΘJ, G.π θ := by
      rw [Finset.sum_comm]
      calc ∑ θ : Fin m, ∑ t ∈ J, G.π θ * pHi θ t
          = ∑ θ ∈ ΘJ, ∑ t ∈ J, G.π θ * pHi θ t := by
              rw [← Finset.sum_subset (Finset.subset_univ ΘJ)]
              intro θ _ hnot
              exact Finset.sum_eq_zero fun t htJ => by rw [hpHi_out θ hnot t htJ, mul_zero]
        _ ≤ ∑ θ ∈ ΘJ, G.π θ := by
              refine Finset.sum_le_sum fun θ _ => ?_
              rw [← Finset.mul_sum]
              calc G.π θ * ∑ t ∈ J, pHi θ t
                  ≤ G.π θ * ∑ t : Fin n, pHi θ t := mul_le_mul_of_nonneg_left
                      (Finset.sum_le_univ_sum_of_nonneg fun t => (hHi.1.2.1 θ).2 t) (G.hπ_nn θ)
                _ = G.π θ := by rw [(hHi.1.2.1 θ).1, mul_one]
    have h3_in : ∀ θ ∈ ΘJ, ∑ t ∈ J, G.π θ * pB θ t = G.π θ := by
      intro θ hθ
      rw [← Finset.mul_sum]
      have hsumJ : ∑ t ∈ J, pB θ t = 1 := by
        rw [← (hB_eq.1.2.1 θ).1]
        refine Finset.sum_subset (Finset.subset_univ J) fun t _ htJ => ?_
        by_contra hne
        have hpos : 0 < pB θ t := lt_of_le_of_ne ((hB_eq.1.2.1 θ).2 t) (Ne.symm hne)
        have htB : t ∈ B θ := Finset.mem_filter.mpr
          ⟨Finset.mem_univ t, (G.isAtkBR_iff_maxUtil cB pB).mp hB_eq.1.2.2.1 θ t hpos⟩
        exact htJ ((Finset.mem_filter.mp hθ).2 htB)
      rw [hsumJ, mul_one]
    have h3 : ∑ θ ∈ ΘJ, G.π θ ≤ ∑ t ∈ J, ∑ θ : Fin m, G.π θ * pB θ t := by
      rw [Finset.sum_comm]
      calc ∑ θ ∈ ΘJ, G.π θ
          = ∑ θ ∈ ΘJ, ∑ t ∈ J, G.π θ * pB θ t :=
              Finset.sum_congr rfl fun θ hθ => (h3_in θ hθ).symm
        _ ≤ ∑ θ : Fin m, ∑ t ∈ J, G.π θ * pB θ t :=
              Finset.sum_le_univ_sum_of_nonneg fun θ =>
                Finset.sum_nonneg fun t _ => mul_nonneg (G.hπ_nn θ) ((hB_eq.1.2.1 θ).2 t)
    have h4 : ∑ t ∈ J, ∑ θ : Fin m, G.π θ * pB θ t ≤ ∑ t ∈ J, s t := by
      refine Finset.sum_le_sum fun t htJ => ?_
      have htlt1 : cB t < 1 := lt_of_lt_of_le (Finset.mem_filter.mp htJ).2 (hHi.1.1 t).2
      exact (le_div_iff₀ (hd_pos t)).mpr (hB_eq.2 t htlt1)
    -- Every inequality is an equality!
    have hcol_eq : ∀ t ∈ J, ∑ θ : Fin m, G.π θ * pB θ t = s t := by
      intro t htJ
      have hle_each : ∀ t' ∈ J, ∑ θ : Fin m, G.π θ * pB θ t' ≤ s t' := fun t' ht' =>
        (le_div_iff₀ (hd_pos t')).mpr
          (hB_eq.2 t' (lt_of_lt_of_le (Finset.mem_filter.mp ht').2 (hHi.1.1 t').2))
      have hsum_eq : ∑ t' ∈ J, (s t' - ∑ θ : Fin m, G.π θ * pB θ t') = 0 := by
        rw [Finset.sum_sub_distrib]; linarith
      have := (Finset.sum_eq_zero_iff_of_nonneg fun t' ht' =>
        by linarith [hle_each t' ht']).mp hsum_eq t htJ
      linarith
    have hout_zero : ∀ θ, θ ∉ ΘJ → ∀ t ∈ J, G.π θ * pB θ t = 0 := by
      have hsum_out : ∑ θ ∈ Finset.univ \ ΘJ, ∑ t ∈ J, G.π θ * pB θ t = 0 := by
        have hadd := Finset.sum_sdiff (Finset.subset_univ ΘJ)
          (f := fun θ => ∑ t ∈ J, G.π θ * pB θ t)
        have hΘ_eq : ∑ θ ∈ ΘJ, ∑ t ∈ J, G.π θ * pB θ t = ∑ θ ∈ ΘJ, G.π θ :=
          Finset.sum_congr rfl fun θ hθ => h3_in θ hθ
        rw [Finset.sum_comm] at h1 h2 h3 h4
        linarith
      intro θ hnot t htJ
      have houter := (Finset.sum_eq_zero_iff_of_nonneg fun θ' _ =>
        Finset.sum_nonneg fun t' _ => mul_nonneg (G.hπ_nn θ') ((hB_eq.1.2.1 θ').2 t')).mp
        hsum_out θ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ θ, hnot⟩)
      exact (Finset.sum_eq_zero_iff_of_nonneg fun t' _ =>
        mul_nonneg (G.hπ_nn θ) ((hB_eq.1.2.1 θ).2 t')).mp houter t htJ
    -- Apply equality-mode log-slope LP duality on `(ΘJ, J)`!
    let eΘ := Fintype.equivFin {θ : Fin m // θ ∈ ΘJ}
    let eJ := Fintype.equivFin {t : Fin n // t ∈ J}
    let π' : Fin (Fintype.card {θ : Fin m // θ ∈ ΘJ}) → ℝ := fun i => G.π (eΘ.symm i).1
    let s' : Fin (Fintype.card {t : Fin n // t ∈ J}) → ℝ := fun j => s (eJ.symm j).1
    let E' : Fin (Fintype.card {θ : Fin m // θ ∈ ΘJ}) →
        Fin (Fintype.card {t : Fin n // t ∈ J}) → Prop :=
      fun i j => (eJ.symm j).1 ∈ B (eΘ.symm i).1
    let α' : Fin (Fintype.card {θ : Fin m // θ ∈ ΘJ}) →
        Fin (Fintype.card {t : Fin n // t ∈ J}) → ℝ :=
      fun i j => -Real.log (G.a (eΘ.symm i).1 (eJ.symm j).1)
    have hfeas_eq : ∃ f : Fin (Fintype.card {θ : Fin m // θ ∈ ΘJ}) →
        Fin (Fintype.card {t : Fin n // t ∈ J}) → ℝ,
        (∀ i j, 0 ≤ f i j) ∧ (∀ i j, ¬ E' i j → f i j = 0) ∧
        (∀ i, ∑ j, f i j = π' i) ∧
        (∀ j, if true then ∑ i, f i j = s' j else s' j ≤ ∑ i, f i j) := by
      refine ⟨fun i j => G.π (eΘ.symm i).1 * pB (eΘ.symm i).1 (eJ.symm j).1,
        fun i j => mul_nonneg (G.hπ_nn _) ((hB_eq.1.2.1 _).2 _), ?_, ?_, ?_⟩
      · intro i j hnE
        by_cases hpos : 0 < pB (eΘ.symm i).1 (eJ.symm j).1
        · exfalso; exact hnE (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            (G.isAtkBR_iff_maxUtil cB pB).mp hB_eq.1.2.2.1 _ _ hpos⟩)
        · have h0 : pB (eΘ.symm i).1 (eJ.symm j).1 = 0 :=
            le_antisymm (not_lt.mp hpos) ((hB_eq.1.2.1 _).2 _)
          dsimp only; rw [h0, mul_zero]
      · intro i
        dsimp only [π']
        rw [← eJ.sum_comp]
        simp only [Equiv.symm_apply_apply]
        rw [Finset.sum_coe_sort J (fun t => G.π (eΘ.symm i).1 * pB (eΘ.symm i).1 t)]
        exact h3_in (eΘ.symm i).1 (eΘ.symm i).2
      · intro j
        simp only [↓reduceIte, s']
        rw [← eΘ.sum_comp]
        simp only [Equiv.symm_apply_apply]
        rw [Finset.sum_coe_sort ΘJ (fun θ => G.π θ * pB θ (eJ.symm j).1)]
        rw [← hcol_eq (eJ.symm j).1 (eJ.symm j).2]
        refine Finset.sum_subset (Finset.subset_univ ΘJ) fun θ _ hnot => ?_
        exact hout_zero θ hnot (eJ.symm j).1 (eJ.symm j).2
    obtain ⟨fstar, u, z, hf_nn, hf_supp, hf_row, hf_col, hdual, hcs⟩ :=
      lp_duality_flow true π' s' E' α' (fun i => G.hπ_nn _) hfeas_eq
    let w : Fin n → ℝ := fun t => if ht : t ∈ J then Real.exp (-z (eJ ⟨t, ht⟩)) else 0
    have hw_pos : ∀ t ∈ J, 0 < w t := fun t ht => by simp [w, ht, Real.exp_pos]
    have hw_nn : ∀ t, 0 ≤ w t := fun t => by
      dsimp only [w]; split_ifs; exact le_of_lt (Real.exp_pos _); exact le_rfl
    have hsumw_pos : 0 < ∑ t ∈ J, w t :=
      Finset.sum_pos (fun t ht => hw_pos t ht) hJ_ne
    let gapCap : Finset ℝ :=
      insert ((R - ∑ t, cB t) / ∑ t ∈ J, w t)
      (J.image (fun t => (cHi t - cB t) / w t) ∪
       ((Finset.univ.product (Finset.univ.product Finset.univ)).filter
         (fun p : Fin m × Fin n × Fin n => p.1 ∈ ΘJ ∧ p.2.1 ∈ B p.1 ∧ p.2.2 ∉ B p.1)).image
         (fun p => (G.uA cB p.1 p.2.1 - G.uA cB p.1 p.2.2) / (G.a p.1 p.2.1 * w p.2.1)))
    have hgapCap_ne : gapCap.Nonempty := ⟨_, Finset.mem_insert_self _ _⟩
    have hgapCap_pos : ∀ x ∈ gapCap, 0 < x := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx'
      · exact div_pos (by linarith) hsumw_pos
      · rcases Finset.mem_union.mp hx' with hx1 | hx2
        · obtain ⟨t, htJ, rfl⟩ := Finset.mem_image.mp hx1
          exact div_pos (by linarith [(Finset.mem_filter.mp htJ).2]) (hw_pos t htJ)
        · obtain ⟨⟨θ, t, r⟩, hp, rfl⟩ := Finset.mem_image.mp hx2
          obtain ⟨_, hθJ, htB, hrB⟩ := Finset.mem_filter.mp hp
          have htJ : t ∈ J := (Finset.mem_filter.mp hθJ).2 htB
          have hgt : G.uA cB θ r < G.uA cB θ t := by
            have h1 : G.uA cB θ t = G.maxUtil cB θ := (Finset.mem_filter.mp htB).2
            have h2 : G.uA cB θ r ≤ G.maxUtil cB θ := G.le_maxUtil cB θ r
            have hne : G.uA cB θ r ≠ G.maxUtil cB θ :=
              fun heq => hrB (Finset.mem_filter.mpr ⟨Finset.mem_univ r, heq⟩)
            exact lt_of_le_of_ne (by linarith) (fun h => hne (by linarith))
          exact div_pos (by linarith) (mul_pos (ha_pos θ t) (hw_pos t htJ))
    let δ : ℝ := gapCap.min' hgapCap_ne
    have hδ_pos : 0 < δ := hgapCap_pos δ (Finset.min'_mem gapCap hgapCap_ne)
    let c' : Fin n → ℝ := fun t => cB t + δ * w t
    have hc'_ge : ∀ t, cB t ≤ c' t := fun t => by dsimp only [c']; nlinarith [hw_nn t]
    have hc'_le : ∀ t, c' t ≤ cHi t := by
      intro t; dsimp only [c']
      by_cases htJ : t ∈ J
      · have hle : δ ≤ (cHi t - cB t) / w t :=
          Finset.min'_le gapCap _ (Finset.mem_insert_of_mem
            (Finset.mem_union_left _ (Finset.mem_image_of_mem _ htJ)))
        have := (le_div_iff₀ (hw_pos t htJ)).mp hle
        linarith
      · simp only [w, dif_neg htJ, mul_zero, add_zero]
        exact (hB_box t).2
    have hc'_sum : ∑ t, c' t = (∑ t, cB t) + δ * ∑ t ∈ J, w t := by
      dsimp only [c']
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      congr 2
      rw [← Finset.sum_subset (Finset.subset_univ J)]
      intro t _ htJ; simp [w, htJ]
    have hc'_sum_leR : ∑ t, c' t ≤ R := by
      have hle : δ ≤ (R - ∑ t, cB t) / ∑ t ∈ J, w t :=
        Finset.min'_le gapCap _ (Finset.mem_insert_self _ _)
      have := (le_div_iff₀ hsumw_pos).mp hle
      linarith
    -- Construct `p'` for `c'`
    choose argmax' hargmax' using fun θ => G.exists_argmax c' θ
    have hout_ex : ∀ θ, θ ∉ ΘJ → ∃ t, t ∈ B θ ∧ t ∉ J := by
      intro θ hnot
      exact Finset.not_subset.mp fun h => hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    let p' : Fin m → Fin n → ℝ := fun θ t =>
      if hθ : θ ∈ ΘJ then
        if hπpos : 0 < G.π θ then
          if ht : t ∈ J then fstar (eΘ ⟨θ, hθ⟩) (eJ ⟨t, ht⟩) / G.π θ else 0
        else if t = argmax' θ then 1 else 0
      else
        if t ∈ J then 0
        else pB θ t + if t = Classical.choose (hout_ex θ hθ) then ∑ r ∈ J, pB θ r else 0
    have hgain_in : ∀ t ∈ J, G.gain p' t = lam := by
      intro t htJ
      have hsum : ∑ θ : Fin m, G.π θ * p' θ t = s t := by
        calc ∑ θ : Fin m, G.π θ * p' θ t
            = ∑ θ ∈ ΘJ, G.π θ * p' θ t := by
                rw [← Finset.sum_subset (Finset.subset_univ ΘJ)]
                intro θ _ hnot; simp [p', hnot, htJ]
          _ = ∑ i : Fin (Fintype.card {θ : Fin m // θ ∈ ΘJ}), fstar i (eJ ⟨t, htJ⟩) := by
                rw [← eΘ.sum_comp, ← Finset.sum_coe_sort ΘJ]
                refine Finset.sum_congr rfl fun θ _ => ?_
                by_cases hπpos : 0 < G.π θ.1
                · simp only [p', dif_pos θ.2, dif_pos hπpos, dif_pos htJ]
                  exact mul_div_cancel₀ _ (ne_of_gt hπpos)
                · have hπ0 : G.π θ.1 = 0 := le_antisymm (not_lt.mp hπpos) (G.hπ_nn θ.1)
                  have hrow := hf_row (eΘ θ)
                  simp only [π', Equiv.symm_apply_apply, hπ0] at hrow
                  have hf0 : fstar (eΘ θ) (eJ ⟨t, htJ⟩) = 0 :=
                    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hf_nn _ j)).mp hrow _
                      (Finset.mem_univ _)
                  rw [hπ0, zero_mul, hf0]
          _ = s t := by simpa [s'] using hf_col (eJ ⟨t, htJ⟩)
      simp only [gain, hsum, s, div_mul_cancel₀ _ (ne_of_gt (hd_pos t))]
    have hgain_out : ∀ t, t ∉ J → G.gain p' t = G.gain pB t := by
      intro t htJ
      simp only [gain]
      congr 1
      refine Finset.sum_congr rfl fun θ _ => ?_
      by_cases hθ : θ ∈ ΘJ
      · have hpB0 : pB θ t = 0 := by
          by_contra hne
          have hpos : 0 < pB θ t := lt_of_le_of_ne ((hB_eq.1.2.1 θ).2 t) (Ne.symm hne)
          have htB : t ∈ B θ := Finset.mem_filter.mpr
            ⟨Finset.mem_univ t, (G.isAtkBR_iff_maxUtil cB pB).mp hB_eq.1.2.2.1 θ t hpos⟩
          exact htJ ((Finset.mem_filter.mp hθ).2 htB)
        rw [hpB0, mul_zero]
        by_cases hπpos : 0 < G.π θ
        · simp [p', hθ, hπpos, htJ]
        · have hπ0 : G.π θ = 0 := le_antisymm (not_lt.mp hπpos) (G.hπ_nn θ)
          rw [hπ0, zero_mul]
      · simp only [p', dif_neg hθ, if_neg htJ]
        split_ifs
        · rw [mul_add, Finset.mul_sum]
          have hzero : ∑ r ∈ J, G.π θ * pB θ r = 0 :=
            Finset.sum_eq_zero fun r hrJ => hout_zero θ hθ r hrJ
          linarith
        · simp
    have hc'_inK : (c', p') ∈ K := by
      refine ⟨⟨⟨fun t => ⟨le_trans (hB_eq.1.1 t).1 (hc'_ge t),
        le_trans (hc'_le t) (hHi.1.1 t).2⟩, ?_, ?_, ?_⟩, ?_⟩,
        fun t => ⟨le_trans (hB_box t).1 (hc'_ge t), hc'_le t⟩, hc'_sum_leR⟩
      · -- IsAtkProfile p'
        intro θ
        by_cases hθ : θ ∈ ΘJ
        · by_cases hπpos : 0 < G.π θ
          · refine ⟨?_, fun t => by
              simp only [p', dif_pos hθ, dif_pos hπpos]
              split_ifs; exact div_nonneg (hf_nn _ _) (le_of_lt hπpos); exact le_rfl⟩
            simp only [p', dif_pos hθ, dif_pos hπpos]
            have hsum : ∑ t : Fin n,
                (if ht : t ∈ J then fstar (eΘ ⟨θ, hθ⟩) (eJ ⟨t, ht⟩) / G.π θ else 0) =
                (∑ j : Fin (Fintype.card {t : Fin n // t ∈ J}),
                  fstar (eΘ ⟨θ, hθ⟩) j) / G.π θ := by
              rw [Finset.sum_div, ← eJ.sum_comp]
              convert (sum_subtype_ite (fun t : Fin n => t ∈ J)
                (fun t => fstar (eΘ ⟨θ, hθ⟩) (eJ t) / G.π θ)).symm
            rw [hsum, hf_row (eΘ ⟨θ, hθ⟩)]
            simp only [π', Equiv.symm_apply_apply]
            exact div_self (ne_of_gt hπpos)
          · refine ⟨by simp [p', hθ, hπpos], fun t => by
              simp only [p', dif_pos hθ, dif_neg hπpos]; split_ifs <;> linarith⟩
        · have hs_notJ : Classical.choose (hout_ex θ hθ) ∉ J := (Classical.choose_spec (hout_ex θ hθ)).2
          refine ⟨?_, fun t => by
            simp only [p', dif_neg hθ]; split_ifs
            · exact le_rfl
            · linarith [(hB_eq.1.2.1 θ).2 t, Finset.sum_nonneg (s := J) fun r _ => (hB_eq.1.2.1 θ).2 r]
            · linarith [(hB_eq.1.2.1 θ).2 t]⟩
          simp only [p', dif_neg hθ]
          have h1 : ∑ t : Fin n, (if t ∈ J then (0 : ℝ) else
              pB θ t + if t = Classical.choose (hout_ex θ hθ) then ∑ r ∈ J, pB θ r else 0) =
              (∑ t ∈ Finset.univ \ J, pB θ t) + ∑ r ∈ J, pB θ r := by
            rw [Finset.sum_ite, Finset.sum_const_zero, zero_add]
            have hfilt : Finset.univ.filter (fun t : Fin n => t ∉ J) = Finset.univ \ J := by
              ext t; simp
            rw [hfilt, Finset.sum_add_distrib, Finset.sum_ite_eq']
            simp [hs_notJ]
          rw [h1, Finset.sum_sdiff (Finset.subset_univ J)]
          exact (hB_eq.1.2.1 θ).1
      · -- IsAtkBR c' p'
        intro θ t r hpos
        by_cases hθ : θ ∈ ΘJ
        · by_cases hπpos : 0 < G.π θ
          · dsimp only [p'] at hpos; simp only [dif_pos hθ, dif_pos hπpos] at hpos
            have htJ : t ∈ J := by by_contra h; simp [h] at hpos
            simp only [dif_pos htJ] at hpos
            have hfpos : 0 < fstar (eΘ ⟨θ, hθ⟩) (eJ ⟨t, htJ⟩) :=
              (div_pos_iff_of_pos_right hπpos).mp hpos
            have htB : t ∈ B θ := by
              by_contra hnB
              have : ¬ E' (eΘ ⟨θ, hθ⟩) (eJ ⟨t, htJ⟩) := by simpa [E'] using hnB
              linarith [hf_supp _ _ this]
            have hcs_eq := hcs (eΘ ⟨θ, hθ⟩) (eJ ⟨t, htJ⟩) hfpos
            simp only [α', Equiv.symm_apply_apply] at hcs_eq
            by_cases hrB : r ∈ B θ
            · have hrJ : r ∈ J := (Finset.mem_filter.mp hθ).2 hrB
              have hdu := hdual (eΘ ⟨θ, hθ⟩) (eJ ⟨r, hrJ⟩) (by simpa [E'] using hrB)
              simp only [α', Equiv.symm_apply_apply] at hdu
              have hlog_le : Real.log (G.a θ t * w t) ≤ Real.log (G.a θ r * w r) := by
                have h1 : Real.log (G.a θ t * w t) = Real.log (G.a θ t) - z (eJ ⟨t, htJ⟩) := by
                  rw [Real.log_mul (ne_of_gt (ha_pos θ t)) (ne_of_gt (hw_pos t htJ))]
                  simp [w, htJ, Real.log_exp]; ring
                have h2 : Real.log (G.a θ r * w r) = Real.log (G.a θ r) - z (eJ ⟨r, hrJ⟩) := by
                  rw [Real.log_mul (ne_of_gt (ha_pos θ r)) (ne_of_gt (hw_pos r hrJ))]
                  simp [w, hrJ, Real.log_exp]; ring
                linarith
              have haw_le : G.a θ t * w t ≤ G.a θ r * w r := by
                have := Real.exp_le_exp.mpr hlog_le
                rwa [Real.exp_log (mul_pos (ha_pos θ t) (hw_pos t htJ)),
                  Real.exp_log (mul_pos (ha_pos θ r) (hw_pos r hrJ))] at this
              have hu_eq : G.uA cB θ t = G.uA cB θ r := by
                rw [(Finset.mem_filter.mp htB).2, (Finset.mem_filter.mp hrB).2]
              have h1 : G.uA c' θ t = G.uA cB θ t - δ * (G.a θ t * w t) := by
                simp only [uA, c']; ring
              have h2 : G.uA c' θ r = G.uA cB θ r - δ * (G.a θ r * w r) := by
                simp only [uA, c']; ring
              nlinarith
            · have hleδ : δ ≤ (G.uA cB θ t - G.uA cB θ r) / (G.a θ t * w t) := by
                refine Finset.min'_le gapCap _ (Finset.mem_insert_of_mem
                  (Finset.mem_union_right _ ?_))
                refine Finset.mem_image.mpr ⟨(θ, t, r), ?_, rfl⟩
                exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hθ, htB, hrB⟩
              have h1 : δ * (G.a θ t * w t) ≤ G.uA cB θ t - G.uA cB θ r :=
                (le_div_iff₀ (mul_pos (ha_pos θ t) (hw_pos t htJ))).mp hleδ
              have h2 : G.uA c' θ t = G.uA cB θ t - δ * (G.a θ t * w t) := by
                simp only [uA, c']; ring
              have h3 : G.uA c' θ r ≤ G.uA cB θ r := G.uA_anti hc'_ge θ r
              linarith
          · dsimp only [p'] at hpos; simp only [dif_pos hθ, dif_neg hπpos] at hpos
            have ht : t = argmax' θ := by by_contra hne; simp [hne] at hpos
            rw [ht, hargmax' θ]; exact G.le_maxUtil c' θ r
        · dsimp only [p'] at hpos; simp only [dif_neg hθ] at hpos
          have htJ : t ∉ J := fun h => by simp [h] at hpos
          simp only [if_neg htJ] at hpos
          have htB : t ∈ B θ := by
            by_cases hteq : t = Classical.choose (hout_ex θ hθ)
            · rw [hteq]; exact (Classical.choose_spec (hout_ex θ hθ)).1
            · simp only [if_neg hteq, add_zero] at hpos
              exact Finset.mem_filter.mpr ⟨Finset.mem_univ t,
                (G.isAtkBR_iff_maxUtil cB pB).mp hB_eq.1.2.2.1 θ t hpos⟩
          have hc't : c' t = cB t := by simp [c', w, htJ]
          have hut : G.uA c' θ t = G.maxUtil cB θ := by
            rw [show G.uA c' θ t = G.uA cB θ t by simp [uA, hc't]]
            exact (Finset.mem_filter.mp htB).2
          exact le_trans (G.uA_anti hc'_ge θ r) (by linarith [G.le_maxUtil cB θ r])
      · -- Lower defender BR
        intro t htpos
        by_cases htJ : t ∈ J
        · rw [hgain_in t htJ]
        · rw [hgain_out t htJ]
          have hc't : c' t = cB t := by simp [c', w, htJ]
          exact hB_eq.1.2.2.2 t (by linarith)
      · -- Upper defender BR
        intro t htlt
        by_cases htJ : t ∈ J
        · rw [hgain_in t htJ]
        · rw [hgain_out t htJ]
          have hc't : c' t = cB t := by simp [c', w, htJ]
          exact hB_eq.2 t (by linarith)
    have hle : ∑ t, c' t ≤ ∑ t, cB t := hB_max hc'_inK
    have hgt : ∑ t, cB t < ∑ t, c' t := by rw [hc'_sum]; nlinarith [hδ_pos, hsumw_pos]
    linarith

/-- Intermediate value property at `lam = 0` when `d_t > 0` strictly. -/
lemma strict_eq_ivt_zero (hd_pos : ∀ t, 0 < G.d t) {R : ℝ}
    {cLo : Fin n → ℝ} {pLo : Fin m → Fin n → ℝ} (hLo : G.IsEq 0 cLo pLo)
    (hRlo : ∑ t, cLo t ≤ R) (hRhi : R ≤ (n : ℝ)) :
    ∃ c p, G.IsEq 0 c p ∧ ∑ t, c t = R := by
  by_cases hsum_eq : ∑ t, cLo t = (n : ℝ)
  · exact ⟨cLo, pLo, hLo, le_antisymm hRlo (by linarith)⟩
  · have hsum_lt : ∑ t, cLo t < (n : ℝ) := by
      have hle : ∑ t : Fin n, cLo t ≤ (n : ℝ) := by
        calc ∑ t : Fin n, cLo t ≤ ∑ _ : Fin n, (1 : ℝ) :=
              Finset.sum_le_sum fun t _ => (hLo.1.1 t).2
          _ = (n : ℝ) := by simp
      exact lt_of_le_of_ne hle hsum_eq
    let τ : ℝ := (R - ∑ t, cLo t) / ((n : ℝ) - ∑ t, cLo t)
    have hτ0 : 0 ≤ τ := div_nonneg (by linarith) (by linarith)
    have hτ1 : τ ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
    let c : Fin n → ℝ := fun t => (1 - τ) * cLo t + τ
    have hc_ge : ∀ t, cLo t ≤ c t := fun t => by
      dsimp only [c]; nlinarith [(hLo.1.1 t).2]
    have hc_bnds : ∀ t, 0 ≤ c t ∧ c t ≤ 1 := fun t => by
      dsimp only [c]; constructor <;> nlinarith [(hLo.1.1 t).1, (hLo.1.1 t).2]
    have hc_eq1 : ∀ t, cLo t = 1 → c t = 1 := fun t ht => by
      dsimp only [c]; rw [ht]; ring
    -- Note: if `cLo t < 1`, then `gain pLo t ≤ 0`, so `∑ θ, π θ * pLo θ t = 0`, so `∀ θ, π θ * pLo θ t = 0`!
    -- Even better: if `cLo t < 1` AND `pLo θ t > 0` for some `π θ = 0`, replace `pLo θ` by pure BR to `c`!
    choose argmaxC hargmaxC using fun θ => G.exists_argmax c θ
    let p : Fin m → Fin n → ℝ := fun θ t =>
      if 0 < G.π θ then pLo θ t else if t = argmaxC θ then 1 else 0
    have hgain_eq : ∀ t, G.gain p t = G.gain pLo t := by
      intro t
      simp only [gain]
      congr 1
      refine Finset.sum_congr rfl fun θ _ => ?_
      dsimp only [p]; split_ifs with hπ
      · rfl
      · have hπ0 : G.π θ = 0 := le_antisymm (not_lt.mp hπ) (G.hπ_nn θ)
        rw [hπ0, zero_mul, zero_mul]
      · have hπ0 : G.π θ = 0 := le_antisymm (not_lt.mp hπ) (G.hπ_nn θ)
        rw [hπ0, zero_mul, zero_mul]
    refine ⟨c, p, ⟨⟨hc_bnds, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
    · intro θ; dsimp only [p]; split_ifs
      · exact hLo.1.2.1 θ
      · refine ⟨by simp, fun t => by split_ifs <;> linarith⟩
    · intro θ t s hpos
      by_cases hπ : 0 < G.π θ
      · simp only [p, if_pos hπ] at hpos
        have hct1 : cLo t = 1 := by
          by_contra hne
          have hlt1 : cLo t < 1 := lt_of_le_of_ne (hLo.1.1 t).2 hne
          have hgle := hLo.2 t hlt1
          have hsum0 : ∑ θ' : Fin m, G.π θ' * pLo θ' t = 0 := by
            have hge : 0 ≤ ∑ θ' : Fin m, G.π θ' * pLo θ' t :=
              Finset.sum_nonneg fun θ' _ => mul_nonneg (G.hπ_nn θ') ((hLo.1.2.1 θ').2 t)
            have hle : ∑ θ' : Fin m, G.π θ' * pLo θ' t ≤ 0 := by
              nlinarith [hd_pos t, show G.gain pLo t = (∑ θ', G.π θ' * pLo θ' t) * G.d t from rfl]
            linarith
          have hterm0 := (Finset.sum_eq_zero_iff_of_nonneg fun θ' _ =>
            mul_nonneg (G.hπ_nn θ') ((hLo.1.2.1 θ').2 t)).mp hsum0 θ (Finset.mem_univ θ)
          nlinarith
        have hct : c t = cLo t := by rw [hc_eq1 t hct1, hct1]
        have hu_eq : G.uA c θ t = G.uA cLo θ t := by simp [uA, hct]
        exact le_trans (G.uA_anti hc_ge θ s) (by linarith [hLo.1.2.2.1 θ t s hpos])
      · simp only [p, if_neg hπ] at hpos
        have ht : t = argmaxC θ := by by_contra hne; simp [hne] at hpos
        rw [ht, hargmaxC θ]; exact G.le_maxUtil c θ s
    · intro t _
      rw [hgain_eq t]
      exact mul_nonneg (Finset.sum_nonneg fun θ _ =>
        mul_nonneg (G.hπ_nn θ) ((hLo.1.2.1 θ).2 t)) (G.hd_nn t)
    · intro t htlt
      rw [hgain_eq t]
      have hctlt : cLo t < 1 := lt_of_le_of_lt (hc_ge t) htlt
      exact hLo.2 t hctlt
    · simp only [c, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hne : (n : ℝ) - ∑ t, cLo t ≠ 0 := by linarith
      dsimp only [τ]
      field_simp [hne]
      ring

/- ## Section 3: General `RealGame` via Utility-Preserving Perturbation -/

/-- Perturbed strictly-positive game anchored at a reference coverage vector `c₀`. -/
def perturb (c₀ : Fin n → ℝ) (ε : ℝ) (hε : 0 < ε) : RealGame m n where
  π := G.π
  b := fun θ t => G.b θ t + ε * c₀ t
  a := fun θ t => G.a θ t + ε
  d := fun t => G.d t + ε
  hn := G.hn
  hπ_nn := G.hπ_nn
  hπ_sum := G.hπ_sum
  ha_nn := fun θ t => by linarith [G.ha_nn θ t]
  hd_nn := fun t => by linarith [G.hd_nn t]

lemma perturb_a_pos (c₀ : Fin n → ℝ) {ε : ℝ} (hε : 0 < ε) (θ : Fin m) (t : Fin n) :
    0 < (G.perturb c₀ ε hε).a θ t := by
  simp only [perturb]; linarith [G.ha_nn θ t]

lemma perturb_d_pos (c₀ : Fin n → ℝ) {ε : ℝ} (hε : 0 < ε) (t : Fin n) :
    0 < (G.perturb c₀ ε hε).d t := by
  simp only [perturb]; linarith [G.hd_nn t]

lemma perturb_uA_at_anchor (c₀ : Fin n → ℝ) {ε : ℝ} (hε : 0 < ε) (θ : Fin m) (t : Fin n) :
    (G.perturb c₀ ε hε).uA c₀ θ t = G.uA c₀ θ t := by
  simp only [uA, perturb]; ring

/-- Closedness under simultaneous limit `ε_k → 0`, `lam_k → lam`, `(c_k, p_k) → (c, p)`. -/
lemma isEq_of_perturb_tendsto (c₀ : Fin n → ℝ)
    {ε : ℕ → ℝ} (hε_pos : ∀ k, 0 < ε k) (hε_lim : Filter.Tendsto ε Filter.atTop (nhds 0))
    {lam_seq : ℕ → ℝ} {lam : ℝ} (hlam_lim : Filter.Tendsto lam_seq Filter.atTop (nhds lam))
    {c_seq : ℕ → Fin n → ℝ} {p_seq : ℕ → Fin m → Fin n → ℝ}
    {c : Fin n → ℝ} {p : Fin m → Fin n → ℝ}
    (hc_lim : Filter.Tendsto c_seq Filter.atTop (nhds c))
    (hp_lim : Filter.Tendsto p_seq Filter.atTop (nhds p))
    (heq : ∀ k, (G.perturb c₀ (ε k) (hε_pos k)).IsEq (lam_seq k) (c_seq k) (p_seq k)) :
    G.IsEq lam c p := by
  have hc_coord : ∀ t, Filter.Tendsto (fun k => c_seq k t) Filter.atTop (nhds (c t)) :=
    fun t => (continuous_apply t).continuousAt.tendsto.comp hc_lim
  have hp_coord : ∀ θ t, Filter.Tendsto (fun k => p_seq k θ t) Filter.atTop (nhds (p θ t)) := fun θ t =>
    ((continuous_apply t).continuousAt.tendsto.comp ((continuous_apply θ).continuousAt.tendsto.comp hp_lim))
  have huA_lim : ∀ θ t, Filter.Tendsto (fun k => (G.perturb c₀ (ε k) (hε_pos k)).uA (c_seq k) θ t)
      Filter.atTop (nhds (G.uA c θ t)) := by
    intro θ t
    have h1 : Filter.Tendsto (fun k => (G.b θ t + ε k * c₀ t) - (G.a θ t + ε k) * c_seq k t)
        Filter.atTop (nhds ((G.b θ t + 0 * c₀ t) - (G.a θ t + 0) * c t)) :=
      (tendsto_const_nhds.add (hε_lim.mul tendsto_const_nhds)).sub
        ((tendsto_const_nhds.add hε_lim).mul (hc_coord t))
    simpa [uA, perturb] using h1
  have hgain_lim : ∀ t, Filter.Tendsto (fun k => (G.perturb c₀ (ε k) (hε_pos k)).gain (p_seq k) t)
      Filter.atTop (nhds (G.gain p t)) := by
    intro t
    have h1 : Filter.Tendsto (fun k => (∑ θ : Fin m, G.π θ * p_seq k θ t) * (G.d t + ε k))
        Filter.atTop (nhds ((∑ θ : Fin m, G.π θ * p θ t) * (G.d t + 0))) :=
      (tendsto_finsetSum _ fun θ _ => tendsto_const_nhds.mul (hp_coord θ t)).mul
        (tendsto_const_nhds.add hε_lim)
    simpa [gain, perturb] using h1
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro t
    exact ⟨ge_of_tendsto (hc_coord t) (Filter.Eventually.of_forall fun k => ((heq k).1.1 t).1),
      le_of_tendsto (hc_coord t) (Filter.Eventually.of_forall fun k => ((heq k).1.1 t).2)⟩
  · intro θ
    refine ⟨?_, fun t => ge_of_tendsto (hp_coord θ t)
      (Filter.Eventually.of_forall fun k => ((heq k).1.2.1 θ).2 t)⟩
    have hsum : Filter.Tendsto (fun k => ∑ t : Fin n, p_seq k θ t)
        Filter.atTop (nhds (∑ t : Fin n, p θ t)) :=
      tendsto_finsetSum _ fun t _ => hp_coord θ t
    have hconst : (fun k => ∑ t : Fin n, p_seq k θ t) = fun _ => (1 : ℝ) :=
      funext fun k => ((heq k).1.2.1 θ).1
    rw [hconst] at hsum
    exact tendsto_nhds_unique hsum tendsto_const_nhds
  · intro θ t s hpos
    have hev : ∀ᶠ k in Filter.atTop, 0 < p_seq k θ t :=
      (hc_coord t |> fun _ => (hp_coord θ t).eventually (lt_mem_nhds hpos))
    exact le_of_tendsto_of_tendsto (huA_lim θ s) (huA_lim θ t)
      (hev.mono fun k hk => (heq k).1.2.2.1 θ t s hk)
  · intro t hpos
    have hev : ∀ᶠ k in Filter.atTop, 0 < c_seq k t := (hc_coord t).eventually (lt_mem_nhds hpos)
    exact le_of_tendsto_of_tendsto hlam_lim (hgain_lim t)
      (hev.mono fun k hk => (heq k).1.2.2.2 t hk)
  · intro t hlt
    have hev : ∀ᶠ k in Filter.atTop, c_seq k t < 1 := (hc_coord t).eventually (gt_mem_nhds hlt)
    exact le_of_tendsto_of_tendsto (hgain_lim t) hlam_lim
      (hev.mono fun k hk => (heq k).2 t hk)

/-- Existence of a real fixed-`lam` equilibrium for EVERY `lam ≥ 0` in ANY `RealGame`. -/
lemma exists_real_eq {lam : ℝ} (hlam : 0 ≤ lam) : ∃ c p, G.IsEq lam c p := by
  rcases eq_or_lt_of_le hlam with rfl | hlam_pos
  · obtain ⟨p, hp⟩ := G.one_isEq_zero
    exact ⟨fun _ => 1, p, hp⟩
  · let ε : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
    have hε_pos : ∀ k, 0 < ε k := fun k => by positivity
    have hε_lim : Filter.Tendsto ε Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hex : ∀ k, ∃ cp : (Fin n → ℝ) × (Fin m → Fin n → ℝ),
        (G.perturb (fun _ => 0) (ε k) (hε_pos k)).IsEq lam cp.1 cp.2 := by
      intro k
      let Gk := G.perturb (fun _ => 0) (ε k) (hε_pos k)
      obtain ⟨cstar, hmem, hmax⟩ := Gk.exists_max_lowerSet (G.perturb_a_pos _ (hε_pos k)) lam
      obtain ⟨pstar, heq⟩ := Gk.max_lowerSet_isEq (G.perturb_a_pos _ (hε_pos k))
        (G.perturb_d_pos _ (hε_pos k)) hlam_pos hmem hmax
      exact ⟨(cstar, pstar), heq⟩
    choose seq hseq using hex
    let Box : Set ((Fin n → ℝ) × (Fin m → Fin n → ℝ)) :=
      (Set.pi Set.univ fun _ => Set.Icc 0 1) ×ˢ
      (Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Set.Icc 0 1)
    have hBox : IsCompact Box :=
      (isCompact_univ_pi fun _ => isCompact_Icc).prod
        (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc)
    have hmemBox : ∀ k, seq k ∈ Box := fun k =>
      ⟨fun t _ => (hseq k).1.1 t, fun θ _ t _ =>
        ⟨((hseq k).1.2.1 θ).2 t, by
          have := Finset.single_le_sum (f := fun t' : Fin n => (seq k).2 θ t') (fun t' _ => ((hseq k).1.2.1 θ).2 t') (Finset.mem_univ t)
          linarith [((hseq k).1.2.1 θ).1]⟩⟩
    obtain ⟨⟨c, p⟩, _, φ, hφ_mono, hφ_lim⟩ := hBox.tendsto_subseq hmemBox
    refine ⟨c, p, G.isEq_of_perturb_tendsto (fun _ => 0)
      (fun k => hε_pos (φ k)) (hε_lim.comp hφ_mono.tendsto_atTop)
      tendsto_const_nhds
      (continuous_fst.continuousAt.tendsto.comp hφ_lim)
      (continuous_snd.continuousAt.tendsto.comp hφ_lim)
      (fun k => hseq (φ k))⟩

/-- Coordinatewise monotonicity in `lam` for ANY `RealGame`: if `0 ≤ lam₁ ≤ lam₂` and
`(c₂, p₂)` is a `lam₂`-equilibrium, then there is a `lam₁`-equilibrium `(c₁, p₁)` with `c₂ ≤ c₁`. -/
lemma real_eq_monotone {lam₁ lam₂ : ℝ} (hlam₁ : 0 ≤ lam₁) (hle : lam₁ ≤ lam₂)
    {c₂ : Fin n → ℝ} {p₂ : Fin m → Fin n → ℝ} (h₂ : G.IsEq lam₂ c₂ p₂) :
    ∃ c₁ p₁, G.IsEq lam₁ c₁ p₁ ∧ ∀ t, c₂ t ≤ c₁ t := by
  rcases eq_or_lt_of_le hlam₁ with rfl | hlam₁_pos
  · obtain ⟨p₁, hp₁⟩ := G.one_isEq_zero
    exact ⟨fun _ => 1, p₁, hp₁, fun t => (h₂.1.1 t).2⟩
  · let ε : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
    have hε_pos : ∀ k, 0 < ε k := fun k => by positivity
    have hε_lim : Filter.Tendsto ε Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hex : ∀ k, ∃ cp : (Fin n → ℝ) × (Fin m → Fin n → ℝ),
        (G.perturb c₂ (ε k) (hε_pos k)).IsEq lam₁ cp.1 cp.2 ∧ ∀ t, c₂ t ≤ cp.1 t := by
      intro k
      let Gk := G.perturb c₂ (ε k) (hε_pos k)
      have hc2_mem : c₂ ∈ Gk.LowerSet lam₁ := by
        refine ⟨p₂, h₂.1.1, h₂.1.2.1, ?_, ?_⟩
        · intro θ t s hpos
          rw [G.perturb_uA_at_anchor c₂ (hε_pos k) θ s, G.perturb_uA_at_anchor c₂ (hε_pos k) θ t]
          exact h₂.1.2.2.1 θ t s hpos
        · intro t htpos
          have h1 : G.gain p₂ t ≤ Gk.gain p₂ t := by
            simp only [gain, Gk, perturb]
            have hsum_nn : 0 ≤ ∑ θ : Fin m, G.π θ * p₂ θ t :=
              Finset.sum_nonneg fun θ _ => mul_nonneg (G.hπ_nn θ) ((h₂.1.2.1 θ).2 t)
            nlinarith [hε_pos k]
          linarith [h₂.1.2.2.2 t htpos]
      obtain ⟨cstar, hmem, hmax⟩ := Gk.exists_max_lowerSet (G.perturb_a_pos c₂ (hε_pos k)) lam₁
      obtain ⟨pstar, heq⟩ := Gk.max_lowerSet_isEq (G.perturb_a_pos c₂ (hε_pos k))
        (G.perturb_d_pos c₂ (hε_pos k)) hlam₁_pos hmem hmax
      exact ⟨(cstar, pstar), heq, hmax c₂ hc2_mem⟩
    choose seq hseq hseq_ge using hex
    let Box : Set ((Fin n → ℝ) × (Fin m → Fin n → ℝ)) :=
      (Set.pi Set.univ fun _ => Set.Icc 0 1) ×ˢ
      (Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Set.Icc 0 1)
    have hBox : IsCompact Box :=
      (isCompact_univ_pi fun _ => isCompact_Icc).prod
        (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc)
    have hmemBox : ∀ k, seq k ∈ Box := fun k =>
      ⟨fun t _ => (hseq k).1.1 t, fun θ _ t _ =>
        ⟨((hseq k).1.2.1 θ).2 t, by
          have := Finset.single_le_sum (f := fun t' : Fin n => (seq k).2 θ t') (fun t' _ => ((hseq k).1.2.1 θ).2 t') (Finset.mem_univ t)
          linarith [((hseq k).1.2.1 θ).1]⟩⟩
    obtain ⟨⟨c₁, p₁⟩, _, φ, hφ_mono, hφ_lim⟩ := hBox.tendsto_subseq hmemBox
    have hc_lim := continuous_fst.continuousAt.tendsto.comp hφ_lim
    refine ⟨c₁, p₁, G.isEq_of_perturb_tendsto c₂
      (fun k => hε_pos (φ k)) (hε_lim.comp hφ_mono.tendsto_atTop)
      tendsto_const_nhds hc_lim (continuous_snd.continuousAt.tendsto.comp hφ_lim)
      (fun k => hseq (φ k)), fun t => ?_⟩
    exact ge_of_tendsto ((continuous_apply t).continuousAt.tendsto.comp hc_lim)
      (Filter.Eventually.of_forall fun k => hseq_ge (φ k) t)

/-- Helper: in any `RealGame`, if `0 < R`, any `lam` with `∃ c p, IsEq G lam c p ∧ R ≤ ∑ c`
satisfies `lam ≤ ∑ t, G.d t`. -/
lemma lam_le_sum_d {lam R : ℝ} (hR : 0 < R) {c : Fin n → ℝ} {p : Fin m → Fin n → ℝ}
    (heq : G.IsEq lam c p) (hsum : R ≤ ∑ t, c t) : lam ≤ ∑ t, G.d t := by
  have hex : ∃ t, 0 < c t := by
    by_contra h
    push Not at h
    have : ∑ t, c t ≤ 0 := Finset.sum_nonpos fun t _ => h t
    linarith
  obtain ⟨t, htpos⟩ := hex
  have h1 : lam ≤ G.gain p t := heq.1.2.2.2 t htpos
  have h2 : ∑ θ : Fin m, G.π θ * p θ t ≤ 1 := by
    calc ∑ θ : Fin m, G.π θ * p θ t
        ≤ ∑ θ : Fin m, G.π θ * 1 := Finset.sum_le_sum fun θ _ =>
            mul_le_mul_of_nonneg_left (by
              have := Finset.single_le_sum (f := fun t' : Fin n => p θ t') (fun t' _ => (heq.1.2.1 θ).2 t') (Finset.mem_univ t)
              linarith [(heq.1.2.1 θ).1]) (G.hπ_nn θ)
      _ = 1 := by simp [G.hπ_sum]
  have h3 : G.gain p t ≤ G.d t := by
    dsimp only [gain]; nlinarith [G.hd_nn t]
  have h4 : G.d t ≤ ∑ t', G.d t' := Finset.single_le_sum (fun t' _ => G.hd_nn t') (Finset.mem_univ t)
  linarith

/-- Exact total coverage at the supremum threshold `q` for ANY `RealGame`. -/
lemma exists_real_eq_exact_at_sup {R q : ℝ} (hRpos : 0 < R) (hRle : R ≤ (n : ℝ)) (hq0 : 0 ≤ q)
    (hq_att : ∃ cHi pHi, G.IsEq q cHi pHi ∧ R ≤ ∑ t, cHi t)
    (hq_max : ∀ lam, q < lam → ∀ c p, G.IsEq lam c p → ∑ t, c t < R) :
    ∃ c p, G.IsEq q c p ∧ ∑ t, c t = R := by
  obtain ⟨cHi, pHi, hHi, hHisum⟩ := hq_att
  let ε : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hε_pos : ∀ k, 0 < ε k := fun k => by positivity
  have hε_lim : Filter.Tendsto ε Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  let Dmax : ℝ := (∑ t, G.d t) + (n : ℝ)
  have hstep : ∀ k : ℕ, ∃ qk : ℝ, ∃ c : Fin n → ℝ, ∃ p : Fin m → Fin n → ℝ,
      q ≤ qk ∧ qk ≤ Dmax ∧ (G.perturb cHi (ε k) (hε_pos k)).IsEq qk c p ∧ ∑ t, c t = R := by
    intro k
    let Gk := G.perturb cHi (ε k) (hε_pos k)
    let Λk : Set ℝ := {lam | 0 ≤ lam ∧ ∃ c p, Gk.IsEq lam c p ∧ R ≤ ∑ t, c t}
    have h0_mem : (0 : ℝ) ∈ Λk := by
      obtain ⟨p0, hp0⟩ := Gk.one_isEq_zero
      refine ⟨le_rfl, fun _ => 1, p0, hp0, ?_⟩
      simpa using hRle
    have hq_mem : q ∈ Λk := by
      rcases eq_or_lt_of_le hq0 with rfl | hq_pos
      · exact h0_mem
      · have hcHi_mem : cHi ∈ Gk.LowerSet q := by
          refine ⟨pHi, hHi.1.1, hHi.1.2.1, ?_, ?_⟩
          · intro θ t s hpos
            rw [G.perturb_uA_at_anchor cHi (hε_pos k) θ s, G.perturb_uA_at_anchor cHi (hε_pos k) θ t]
            exact hHi.1.2.2.1 θ t s hpos
          · intro t htpos
            have h1 : G.gain pHi t ≤ Gk.gain pHi t := by
              simp only [gain, Gk, perturb]
              have hsum_nn : 0 ≤ ∑ θ : Fin m, G.π θ * pHi θ t :=
                Finset.sum_nonneg fun θ _ => mul_nonneg (G.hπ_nn θ) ((hHi.1.2.1 θ).2 t)
              nlinarith [hε_pos k]
            linarith [hHi.1.2.2.2 t htpos]
        obtain ⟨cstar, hmem, hmax⟩ := Gk.exists_max_lowerSet (G.perturb_a_pos cHi (hε_pos k)) q
        obtain ⟨pstar, heq⟩ := Gk.max_lowerSet_isEq (G.perturb_a_pos cHi (hε_pos k))
          (G.perturb_d_pos cHi (hε_pos k)) hq_pos hmem hmax
        refine ⟨hq0, cstar, pstar, heq, le_trans hHisum (Finset.sum_le_sum fun t _ => hmax cHi hcHi_mem t)⟩
    have hbdd : BddAbove Λk := by
      refine ⟨Dmax, ?_⟩
      rintro lam ⟨_, c, p, heq, hsum⟩
      have h1 := Gk.lam_le_sum_d hRpos heq hsum
      have hε_le1 : ε k ≤ 1 := by
        dsimp only [ε]
        exact (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) k])
      have h2 : ∑ t, Gk.d t ≤ Dmax := by
        simp only [Gk, perturb, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul, Dmax]
        have : (n : ℝ) * ε k ≤ (n : ℝ) * 1 := mul_le_mul_of_nonneg_left hε_le1 (Nat.cast_nonneg n)
        linarith
      linarith
    let qk : ℝ := sSup Λk
    have hqk_ge_q : q ≤ qk := le_csSup hbdd hq_mem
    have hqk_ge_0 : 0 ≤ qk := le_trans hq0 hqk_ge_q
    have hqk_le : qk ≤ Dmax := csSup_le ⟨0, h0_mem⟩ (by
      rintro lam ⟨_, c, p, heq, hsum⟩
      have h1 := Gk.lam_le_sum_d hRpos heq hsum
      have hε_le1 : ε k ≤ 1 := by dsimp only [ε]; exact (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) k])
      have h2 : ∑ t, Gk.d t ≤ Dmax := by
        simp only [Gk, perturb, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul, Dmax]
        have : (n : ℝ) * ε k ≤ (n : ℝ) * 1 := mul_le_mul_of_nonneg_left hε_le1 (Nat.cast_nonneg n)
        linarith
      linarith)
    -- Extract a lower limit `(cLo, pLo)` at `qk` from `lam_j = qk + 1/(j+1) ↓ qk`
    let Box : Set ((Fin n → ℝ) × (Fin m → Fin n → ℝ)) :=
      (Set.pi Set.univ fun _ => Set.Icc 0 1) ×ˢ
      (Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Set.Icc 0 1)
    have hBox : IsCompact Box :=
      (isCompact_univ_pi fun _ => isCompact_Icc).prod
        (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc)
    have hhi_seq : ∀ j : ℕ, ∃ cp : (Fin n → ℝ) × (Fin m → Fin n → ℝ),
        Gk.IsEq (qk + 1 / ((j : ℝ) + 1)) cp.1 cp.2 ∧
        (∀ c ∈ Gk.LowerSet (qk + 1 / ((j : ℝ) + 1)), ∀ t, c t ≤ cp.1 t) ∧
        ∑ t, cp.1 t < R := by
      intro j
      have hlj_pos : 0 < qk + 1 / ((j : ℝ) + 1) := by positivity
      obtain ⟨cs, hmem, hmax⟩ := Gk.exists_max_lowerSet (G.perturb_a_pos cHi (hε_pos k)) _
      obtain ⟨ps, heq⟩ := Gk.max_lowerSet_isEq (G.perturb_a_pos cHi (hε_pos k))
        (G.perturb_d_pos cHi (hε_pos k)) hlj_pos hmem hmax
      have hlt : ∑ t, cs t < R := by
        by_contra hnot
        have hmemΛ : qk + 1 / ((j : ℝ) + 1) ∈ Λk := ⟨le_of_lt hlj_pos, cs, ps, heq, not_lt.mp hnot⟩
        have := le_csSup hbdd hmemΛ
        have hpos : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
        linarith
      exact ⟨(cs, ps), heq, hmax, hlt⟩
    choose seqM hseqM_eq hseqM_max hseqM_lt using hhi_seq
    have hmemBoxM : ∀ j, seqM j ∈ Box := fun j =>
      ⟨fun t _ => (hseqM_eq j).1.1 t, fun θ _ t _ =>
        ⟨((hseqM_eq j).1.2.1 θ).2 t, by
          have := Finset.single_le_sum (f := fun t' : Fin n => (seqM j).2 θ t') (fun t' _ => ((hseqM_eq j).1.2.1 θ).2 t') (Finset.mem_univ t)
          linarith [((hseqM_eq j).1.2.1 θ).1]⟩⟩
    obtain ⟨⟨cLo, pLo⟩, _, φ, hφ_mono, hφ_lim⟩ := hBox.tendsto_subseq hmemBoxM
    have hlamM_lim : Filter.Tendsto (fun j => qk + 1 / (((φ j : ℕ) : ℝ) + 1))
        Filter.atTop (nhds qk) := by
      have h1 : Filter.Tendsto (fun j => qk + 1 / (((φ j : ℕ) : ℝ) + 1))
          Filter.atTop (nhds (qk + 0)) :=
        tendsto_const_nhds.add
          (tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ_mono.tendsto_atTop)
      simpa using h1
    have hLo_eq : Gk.IsEq qk cLo pLo := by
      -- Constant game limit as `lam_j → qk`
      have hc_coord : ∀ t, Filter.Tendsto (fun j => (seqM (φ j)).1 t) Filter.atTop (nhds (cLo t)) :=
        fun t => (continuous_apply t).continuousAt.tendsto.comp
          (continuous_fst.continuousAt.tendsto.comp hφ_lim)
      have hp_coord : ∀ θ t, Filter.Tendsto (fun j => (seqM (φ j)).2 θ t) Filter.atTop (nhds (pLo θ t)) :=
        fun θ t => (continuous_apply t).continuousAt.tendsto.comp ((continuous_apply θ).continuousAt.tendsto.comp (continuous_snd.continuousAt.tendsto.comp hφ_lim))
      have huA_lim : ∀ θ t, Filter.Tendsto (fun j => Gk.uA (seqM (φ j)).1 θ t)
          Filter.atTop (nhds (Gk.uA cLo θ t)) := fun θ t =>
        tendsto_const_nhds.sub (tendsto_const_nhds.mul (hc_coord t))
      have hgain_lim : ∀ t, Filter.Tendsto (fun j => Gk.gain (seqM (φ j)).2 t)
          Filter.atTop (nhds (Gk.gain pLo t)) := fun t =>
        (tendsto_finsetSum _ fun θ _ => tendsto_const_nhds.mul (hp_coord θ t)).mul tendsto_const_nhds
      refine ⟨⟨fun t => ⟨ge_of_tendsto (hc_coord t) (Filter.Eventually.of_forall fun j => ((hseqM_eq (φ j)).1.1 t).1),
        le_of_tendsto (hc_coord t) (Filter.Eventually.of_forall fun j => ((hseqM_eq (φ j)).1.1 t).2)⟩,
        fun θ => ⟨by
          have hsum := tendsto_finsetSum Finset.univ fun t _ => hp_coord θ t
          have hconst : (fun j => ∑ t, (seqM (φ j)).2 θ t) = fun _ => 1 :=
            funext fun j => ((hseqM_eq (φ j)).1.2.1 θ).1
          rw [hconst] at hsum; exact tendsto_nhds_unique hsum tendsto_const_nhds,
          fun t => ge_of_tendsto (hp_coord θ t) (Filter.Eventually.of_forall fun j => ((hseqM_eq (φ j)).1.2.1 θ).2 t)⟩,
        fun θ t s hpos => le_of_tendsto_of_tendsto (huA_lim θ s) (huA_lim θ t)
          (((hp_coord θ t).eventually (lt_mem_nhds hpos)).mono fun j hj => (hseqM_eq (φ j)).1.2.2.1 θ t s hj),
        fun t hpos => le_of_tendsto_of_tendsto hlamM_lim (hgain_lim t)
          (((hc_coord t).eventually (lt_mem_nhds hpos)).mono fun j hj => (hseqM_eq (φ j)).1.2.2.2 t hj)⟩,
        fun t hlt => le_of_tendsto_of_tendsto (hgain_lim t) hlamM_lim
          (((hc_coord t).eventually (gt_mem_nhds hlt)).mono fun j hj => (hseqM_eq (φ j)).2 t hj)⟩
    have hcLo_sum_le : ∑ t, cLo t ≤ R := by
      have hsum := tendsto_finsetSum Finset.univ fun t _ =>
        (continuous_apply t).continuousAt.tendsto.comp
          (continuous_fst.continuousAt.tendsto.comp hφ_lim)
      exact le_of_tendsto hsum (Filter.Eventually.of_forall fun j => le_of_lt (hseqM_lt (φ j)))
    rcases eq_or_lt_of_le hqk_ge_0 with hqk0 | hqk_pos
    · rw [← hqk0] at hLo_eq
      obtain ⟨c, p, heq, hsum⟩ := Gk.strict_eq_ivt_zero (G.perturb_d_pos cHi (hε_pos k)) hLo_eq
        hcLo_sum_le hRle
      exact ⟨qk, c, p, hqk_ge_q, hqk_le, hqk0 ▸ heq, hsum⟩
    · -- For `qk > 0`, `cstar = max LowerSet Gk qk` satisfies `cLo ≤ cstar` AND `R ≤ ∑ cstar`!
      obtain ⟨cstar, hcs_mem, hcs_max⟩ := Gk.exists_max_lowerSet (G.perturb_a_pos cHi (hε_pos k)) qk
      obtain ⟨pstar, hcs_eq⟩ := Gk.max_lowerSet_isEq (G.perturb_a_pos cHi (hε_pos k))
        (G.perturb_d_pos cHi (hε_pos k)) hqk_pos hcs_mem hcs_max
      have hcLo_le_cstar : ∀ t, cLo t ≤ cstar t := hcs_max cLo ⟨pLo, hLo_eq.1⟩
      -- Also `R ≤ ∑ cstar`: pick `lam_j ∈ Λk` with `lam_j > qk - 1/(j+1)`!
      have hcs_sum_ge : R ≤ ∑ t, cstar t := by
        by_contra hlt
        push Not at hlt
        -- Actually pick a sequence `lam_j ∈ Λk` converging to `qk`, extract `(c_j, p_j) → (c_∞, p_∞) ∈ LowerSet Gk qk`,
        -- then `c_∞ ≤ cstar` and `R ≤ ∑ c_∞ ≤ ∑ cstar`, contradiction!
        have hlo_seq : ∀ j : ℕ, ∃ lam ∈ Λk, qk - 1 / ((j : ℝ) + 1) < lam := by
          intro j
          have hpos : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
          exact exists_lt_of_lt_csSup ⟨0, h0_mem⟩ (by linarith)
        choose lamLo hlamLo_mem hlamLo_gt using hlo_seq
        have hlo_cp : ∀ j, ∃ cp : (Fin n → ℝ) × (Fin m → Fin n → ℝ),
            Gk.IsEq (lamLo j) cp.1 cp.2 ∧ R ≤ ∑ t, cp.1 t := fun j => by
          obtain ⟨_, c, p, heq, hsum⟩ := hlamLo_mem j
          exact ⟨(c, p), heq, hsum⟩
        choose seqL hseqL_eq hseqL_sum using hlo_cp
        have hmemBoxL : ∀ j, seqL j ∈ Box := fun j =>
          ⟨fun t _ => (hseqL_eq j).1.1 t, fun θ _ t _ =>
            ⟨((hseqL_eq j).1.2.1 θ).2 t, by
              have := Finset.single_le_sum (f := fun t' : Fin n => (seqL j).2 θ t') (fun t' _ => ((hseqL_eq j).1.2.1 θ).2 t') (Finset.mem_univ t)
              linarith [((hseqL_eq j).1.2.1 θ).1]⟩⟩
        obtain ⟨⟨cL, pL⟩, _, ψ, hψ_mono, hψ_lim⟩ := hBox.tendsto_subseq hmemBoxL
        have hlamL_lim : Filter.Tendsto (lamLo ∘ ψ) Filter.atTop (nhds qk) := by
          have hsub_lim : Filter.Tendsto (fun j => qk - 1 / (((ψ j : ℕ) : ℝ) + 1))
              Filter.atTop (nhds qk) := by
            have h1 : Filter.Tendsto (fun j => qk - 1 / (((ψ j : ℕ) : ℝ) + 1))
                Filter.atTop (nhds (qk - 0)) :=
              tendsto_const_nhds.sub
                (tendsto_one_div_add_atTop_nhds_zero_nat.comp hψ_mono.tendsto_atTop)
            simpa using h1
          refine tendsto_of_tendsto_of_tendsto_of_le_of_le hsub_lim tendsto_const_nhds
            (fun j => le_of_lt (hlamLo_gt (ψ j)))
            (fun j => le_csSup hbdd (hlamLo_mem (ψ j)))
        have hcL_lower : cL ∈ Gk.LowerSet qk := by
          have hc_coord : ∀ t, Filter.Tendsto (fun j => (seqL (ψ j)).1 t) Filter.atTop (nhds (cL t)) :=
            fun t => (continuous_apply t).continuousAt.tendsto.comp
              (continuous_fst.continuousAt.tendsto.comp hψ_lim)
          have hp_coord : ∀ θ t, Filter.Tendsto (fun j => (seqL (ψ j)).2 θ t) Filter.atTop (nhds (pL θ t)) :=
            fun θ t => (continuous_apply t).continuousAt.tendsto.comp ((continuous_apply θ).continuousAt.tendsto.comp (continuous_snd.continuousAt.tendsto.comp hψ_lim))
          have huA_lim : ∀ θ t, Filter.Tendsto (fun j => Gk.uA (seqL (ψ j)).1 θ t)
              Filter.atTop (nhds (Gk.uA cL θ t)) := fun θ t =>
            tendsto_const_nhds.sub (tendsto_const_nhds.mul (hc_coord t))
          have hgain_lim : ∀ t, Filter.Tendsto (fun j => Gk.gain (seqL (ψ j)).2 t)
              Filter.atTop (nhds (Gk.gain pL t)) := fun t =>
            (tendsto_finsetSum _ fun θ _ => tendsto_const_nhds.mul (hp_coord θ t)).mul tendsto_const_nhds
          exact ⟨pL, fun t => ⟨ge_of_tendsto (hc_coord t) (Filter.Eventually.of_forall fun j => ((hseqL_eq (ψ j)).1.1 t).1),
            le_of_tendsto (hc_coord t) (Filter.Eventually.of_forall fun j => ((hseqL_eq (ψ j)).1.1 t).2)⟩,
            fun θ => ⟨by
              have hsum := tendsto_finsetSum Finset.univ fun t _ => hp_coord θ t
              have hconst : (fun j => ∑ t, (seqL (ψ j)).2 θ t) = fun _ => 1 :=
                funext fun j => ((hseqL_eq (ψ j)).1.2.1 θ).1
              rw [hconst] at hsum; exact tendsto_nhds_unique hsum tendsto_const_nhds,
              fun t => ge_of_tendsto (hp_coord θ t) (Filter.Eventually.of_forall fun j => ((hseqL_eq (ψ j)).1.2.1 θ).2 t)⟩,
            fun θ t s hpos => le_of_tendsto_of_tendsto (huA_lim θ s) (huA_lim θ t)
              (((hp_coord θ t).eventually (lt_mem_nhds hpos)).mono fun j hj => (hseqL_eq (ψ j)).1.2.2.1 θ t s hj),
            fun t hpos => le_of_tendsto_of_tendsto hlamL_lim (hgain_lim t)
              (((hc_coord t).eventually (lt_mem_nhds hpos)).mono fun j hj => (hseqL_eq (ψ j)).1.2.2.2 t hj)⟩
        have hcL_sum : R ≤ ∑ t, cL t := by
          have hsum := tendsto_finsetSum Finset.univ fun t _ =>
            (continuous_apply t).continuousAt.tendsto.comp
              (continuous_fst.continuousAt.tendsto.comp hψ_lim)
          exact ge_of_tendsto hsum (Filter.Eventually.of_forall fun j => hseqL_sum (ψ j))
        have hcL_le : ∑ t, cL t ≤ ∑ t, cstar t := Finset.sum_le_sum fun t _ => hcs_max cL hcL_lower t
        linarith
      obtain ⟨c, p, heq, hsum⟩ := Gk.strict_eq_ivt (G.perturb_a_pos cHi (hε_pos k))
        (G.perturb_d_pos cHi (hε_pos k)) hqk_pos hLo_eq hcs_eq hcLo_le_cstar hcLo_sum_le hcs_sum_ge
      exact ⟨qk, c, p, hqk_ge_q, hqk_le, heq, hsum⟩
  choose qseq cseq pseq hq_ge hq_le heq_seq hsum_seq using hstep
  let BigBox : Set (ℝ × (Fin n → ℝ) × (Fin m → Fin n → ℝ)) :=
    Set.Icc q Dmax ×ˢ
    ((Set.pi Set.univ fun _ => Set.Icc 0 1) ×ˢ
     (Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Set.Icc 0 1))
  have hBigBox : IsCompact BigBox :=
    isCompact_Icc.prod ((isCompact_univ_pi fun _ => isCompact_Icc).prod
      (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc))
  have hmemBig : ∀ k, (qseq k, cseq k, pseq k) ∈ BigBox := fun k =>
    ⟨⟨hq_ge k, hq_le k⟩, fun t _ => (heq_seq k).1.1 t, fun θ _ t _ =>
      ⟨((heq_seq k).1.2.1 θ).2 t, by
        have := Finset.single_le_sum (f := fun t' : Fin n => pseq k θ t') (fun t' _ => ((heq_seq k).1.2.1 θ).2 t') (Finset.mem_univ t)
        linarith [((heq_seq k).1.2.1 θ).1]⟩⟩
  obtain ⟨⟨qinf, cinf, pinf⟩, ⟨⟨hqinf_ge, _⟩, _, _⟩, φ, hφ_mono, hφ_lim⟩ :=
    hBigBox.tendsto_subseq hmemBig
  have hq_lim : Filter.Tendsto (fun k => qseq (φ k)) Filter.atTop (nhds qinf) :=
    continuous_fst.continuousAt.tendsto.comp hφ_lim
  have hc_lim : Filter.Tendsto (fun k => cseq (φ k)) Filter.atTop (nhds cinf) :=
    (continuous_fst.comp continuous_snd).continuousAt.tendsto.comp hφ_lim
  have hp_lim : Filter.Tendsto (fun k => pseq (φ k)) Filter.atTop (nhds pinf) :=
    (continuous_snd.comp continuous_snd).continuousAt.tendsto.comp hφ_lim
  have hinf_eq : G.IsEq qinf cinf pinf :=
    G.isEq_of_perturb_tendsto cHi (fun k => hε_pos (φ k))
      (hε_lim.comp hφ_mono.tendsto_atTop) hq_lim hc_lim hp_lim (fun k => heq_seq (φ k))
  have hinf_sum : ∑ t, cinf t = R := by
    have hsum : Filter.Tendsto (fun k => ∑ t, cseq (φ k) t) Filter.atTop (nhds (∑ t, cinf t)) :=
      tendsto_finsetSum Finset.univ fun t _ =>
        (continuous_apply t).continuousAt.tendsto.comp hc_lim
    have hconst : (fun k => ∑ t, cseq (φ k) t) = fun _ => R := funext fun k => hsum_seq (φ k)
    rw [hconst] at hsum
    exact tendsto_nhds_unique hsum tendsto_const_nhds
  have hqinf_eq : qinf = q := by
    by_contra hne
    have hgt : q < qinf := lt_of_le_of_ne hqinf_ge (Ne.symm hne)
    linarith [hq_max qinf hgt cinf pinf hinf_eq]
  rw [hqinf_eq] at hinf_eq
  exact ⟨cinf, pinf, hinf_eq, hinf_sum⟩

end RealGame

/- ## Section 4: Cramer Vertex Bound for Bounded Integer Polytopes -/

/-- Every nonempty bounded integer-coefficient polytope `P ⊆ ℝ^k` attains its maximum of a
coordinate `coord : Fin k` at a rational number `q : ℚ` whose denominator is at most
`k! * B^k` (where `B` bounds all entries `|A i j|`). -/
theorem polytope_max_cramer {m k : ℕ} (A : Matrix (Fin m) (Fin k) ℤ) (b : Fin m → ℤ)
    (coord : Fin k) (B : ℕ) (hA_bd : ∀ i j, (A i j).natAbs ≤ B)
    (R : ℝ)
    (hP_ne : ∃ x : Fin k → ℝ, ∀ i, ∑ j, (A i j : ℝ) * x j ≤ (b i : ℝ))
    (hP_bdd : ∀ x : Fin k → ℝ, (∀ i, ∑ j, (A i j : ℝ) * x j ≤ (b i : ℝ)) → ∀ j, |x j| ≤ R) :
    ∃ q : ℚ,
      (∃ x : Fin k → ℝ, (∀ i, ∑ j, (A i j : ℝ) * x j ≤ (b i : ℝ)) ∧ x coord = (q : ℝ)) ∧
      (∀ x : Fin k → ℝ, (∀ i, ∑ j, (A i j : ℝ) * x j ≤ (b i : ℝ)) → x coord ≤ (q : ℝ)) ∧
      q.den ≤ Nat.factorial k * B ^ k := by
  classical
  let P : Set (Fin k → ℝ) := {x | ∀ i, ∑ j, (A i j : ℝ) * x j ≤ (b i : ℝ)}
  have hP_comp : IsCompact P := by
    let Box : Set (Fin k → ℝ) := Set.pi Set.univ fun _ => Set.Icc (-R) R
    have hBox : IsCompact Box := isCompact_univ_pi fun _ => isCompact_Icc
    have hsub : P ⊆ Box := fun x hx j _ => abs_le.mp (hP_bdd x hx j)
    have hclosed : IsClosed P := by
      have heq : P = ⋂ i : Fin m, {x : Fin k → ℝ | ∑ j : Fin k, (A i j : ℝ) * x j ≤ (b i : ℝ)} := by
        ext x; simp [P]
      rw [heq]
      exact isClosed_iInter fun i =>
        isClosed_le (continuous_finsetSum Finset.univ fun j _ => continuous_const.mul (continuous_apply j))
          continuous_const
    exact hBox.of_isClosed_subset hclosed hsub
  obtain ⟨x0, hx0P, hx0max⟩ := hP_comp.exists_isMaxOn hP_ne (continuous_apply coord).continuousOn
  let Mval : ℝ := x0 coord
  let F : Set (Fin k → ℝ) := {x ∈ P | x coord = Mval}
  have hF_ne : F.Nonempty := ⟨x0, hx0P, rfl⟩
  let Arow : Fin m → (Fin k → ℝ) := fun i j => (A i j : ℝ)
  let tight (x : Fin k → ℝ) : Finset (Fin m) :=
    Finset.univ.filter fun i => ∑ j, (A i j : ℝ) * x j = (b i : ℝ)
  let rk (x : Fin k → ℝ) : ℕ :=
    Module.finrank ℝ (Submodule.span ℝ (Arow '' (tight x : Set (Fin m))))
  have hrk_le : ∀ x, rk x ≤ k := fun x => by
    have := Submodule.finrank_le (Submodule.span ℝ (Arow '' (tight x : Set (Fin m))))
    simpa [Module.finrank_fin_fun] using this
  -- Choose `x* ∈ F` maximizing `rk x` (over a finite range `≤ k`)
  let rkSet : Finset ℕ := (Finset.range (k + 1)).filter fun r => ∃ x ∈ F, rk x = r
  have hrkSet_ne : rkSet.Nonempty :=
    ⟨rk x0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (hrk_le x0)), x0, ⟨hx0P, rfl⟩, rfl⟩⟩
  let rmax := rkSet.max' hrkSet_ne
  obtain ⟨xstar, hxstarF, hxstar_rk⟩ := (Finset.mem_filter.mp (Finset.max'_mem rkSet hrkSet_ne)).2
  have hxstar_maxrk : ∀ x ∈ F, rk x ≤ rk xstar := by
    intro x hxF
    rw [hxstar_rk]
    exact Finset.le_max' rkSet (rk x)
      (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (hrk_le x)), x, hxF, rfl⟩)
  -- Show `rk xstar = k`!
  have hrk_full : rk xstar = k := by
    by_contra hne
    have hlt : rk xstar < k := lt_of_le_of_ne (hrk_le xstar) hne
    let S := Submodule.span ℝ (Arow '' (tight xstar : Set (Fin m)))
    let L' : (Fin k → ℝ) →ₗ[ℝ] (S →ₗ[ℝ] ℝ) :=
      { toFun := fun d =>
          { toFun := fun v => ∑ j, v.1 j * d j
            map_add' := fun v1 v2 => by simp only [Submodule.coe_add, Pi.add_apply, add_mul, Finset.sum_add_distrib]
            map_smul' := fun c v => by
              simp only [SetLike.val_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc, ← Finset.mul_sum] }
        map_add' := fun d1 d2 => by ext v; simp [mul_add, Finset.sum_add_distrib]
        map_smul' := fun c d => by
          ext v
          simp only [LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply, smul_eq_mul,
            LinearMap.smul_apply, RingHom.id_apply]
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => by ring }
    have hker_pos : 0 < Module.finrank ℝ (LinearMap.ker L') := by
      have h1 := LinearMap.finrank_range_add_finrank_ker L'
      have h2 : Module.finrank ℝ (LinearMap.range L') ≤ Module.finrank ℝ (S →ₗ[ℝ] ℝ) :=
        Submodule.finrank_le _
      have h3 : Module.finrank ℝ (S →ₗ[ℝ] ℝ) = Module.finrank ℝ S := by
        rw [Module.finrank_linearMap, Module.finrank_self, mul_one]
      have h4 : Module.finrank ℝ (Fin k → ℝ) = k := Module.finrank_fin_fun ℝ
      have hltS : Module.finrank ℝ S < k := hlt
      omega
    have hker_ne : LinearMap.ker L' ≠ ⊥ := by
      intro hbot
      rw [hbot, finrank_bot] at hker_pos
      omega
    obtain ⟨d, hd_ker, hd_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker_ne
    have hd_orth : ∀ v ∈ S, ∑ j, v j * d j = 0 := fun v hv => by
      have := LinearMap.congr_fun (LinearMap.mem_ker.mp hd_ker) ⟨v, hv⟩
      simpa [L'] using this
    have hd_tight : ∀ i ∈ tight xstar, ∑ j, (A i j : ℝ) * d j = 0 := fun i hi =>
      hd_orth (Arow i) (Submodule.subset_span ⟨i, hi, rfl⟩)
    -- Show `d coord = 0` (otherwise small `±t • d` beats `Mval`!)
    have hd_coord : d coord = 0 := by
      by_contra hne0
      let Slack := (Finset.univ \ tight xstar).filter fun i => ∑ j, (A i j : ℝ) * d j ≠ 0
      let t0 : ℝ := if hSl : Slack.Nonempty then
          (Slack.image fun i => ((b i : ℝ) - ∑ j, (A i j : ℝ) * xstar j) / |∑ j, (A i j : ℝ) * d j|).min'
            (hSl.image _)
        else 1
      have ht0_pos : 0 < t0 := by
        by_cases hSl : Slack.Nonempty
        · have hmem : t0 ∈ Slack.image fun i =>
              ((b i : ℝ) - ∑ j, (A i j : ℝ) * xstar j) / |∑ j, (A i j : ℝ) * d j| := by
            simp only [t0, dif_pos hSl]; exact Finset.min'_mem _ _
          obtain ⟨i, hi, hi_eq⟩ := Finset.mem_image.mp hmem
          have hnt : i ∉ tight xstar := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hi).1).2
          have hne_ad : ∑ j, (A i j : ℝ) * d j ≠ 0 := (Finset.mem_filter.mp hi).2
          have hlt_i : ∑ j, (A i j : ℝ) * xstar j < (b i : ℝ) :=
            lt_of_le_of_ne (hxstarF.1 i) fun h => hnt (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩)
          rw [← hi_eq]
          exact div_pos (by linarith) (abs_pos.mpr hne_ad)
        · simp only [t0, dif_neg hSl]; exact zero_lt_one
      let sgn : ℝ := if 0 < d coord then 1 else -1
      let xnew : Fin k → ℝ := fun j => xstar j + (sgn * t0) * d j
      have hxnewP : xnew ∈ P := by
        intro i
        have hcalc : ∑ j, (A i j : ℝ) * xnew j =
            (∑ j, (A i j : ℝ) * xstar j) + (sgn * t0) * ∑ j, (A i j : ℝ) * d j := by
          simp only [xnew, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
          congr 1; refine Finset.sum_congr rfl fun j _ => by ring
        rw [hcalc]
        by_cases hit : i ∈ tight xstar
        · rw [hd_tight i hit, mul_zero, add_zero]; exact hxstarF.1 i
        · by_cases had : ∑ j, (A i j : ℝ) * d j = 0
          · rw [had, mul_zero, add_zero]; exact hxstarF.1 i
          · have hiSl : i ∈ Slack :=
              Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hit⟩, had⟩
            have hle_t0 : t0 ≤ ((b i : ℝ) - ∑ j, (A i j : ℝ) * xstar j) / |∑ j, (A i j : ℝ) * d j| := by
              have hSl : Slack.Nonempty := ⟨i, hiSl⟩
              simp only [t0, dif_pos hSl]
              exact Finset.min'_le _ _ (Finset.mem_image_of_mem _ hiSl)
            have h1 : t0 * |∑ j, (A i j : ℝ) * d j| ≤ (b i : ℝ) - ∑ j, (A i j : ℝ) * xstar j :=
              (le_div_iff₀ (abs_pos.mpr had)).mp hle_t0
            have h2 : (sgn * t0) * ∑ j, (A i j : ℝ) * d j ≤ t0 * |∑ j, (A i j : ℝ) * d j| := by
              have hsgn : |sgn| = 1 := by dsimp only [sgn]; split_ifs <;> simp
              calc (sgn * t0) * ∑ j, (A i j : ℝ) * d j
                  ≤ |(sgn * t0) * ∑ j, (A i j : ℝ) * d j| := le_abs_self _
                _ = |sgn| * |t0| * |∑ j, (A i j : ℝ) * d j| := by simp [abs_mul]
                _ = t0 * |∑ j, (A i j : ℝ) * d j| := by rw [hsgn, abs_of_pos ht0_pos, one_mul]
            linarith
      have hgt_M : Mval < xnew coord := by
        have hpos_prod : 0 < sgn * d coord := by
          dsimp only [sgn]; split_ifs with h
          · linarith
          · have : d coord < 0 := lt_of_le_of_ne (not_lt.mp h) hne0
            linarith
        dsimp only [xnew]
        rw [hxstarF.2]
        have : 0 < (sgn * t0) * d coord := by
          have : (sgn * t0) * d coord = t0 * (sgn * d coord) := by ring
          rw [this]; exact mul_pos ht0_pos hpos_prod
        linarith
      have hle_M : xnew coord ≤ Mval := hx0max hxnewP
      linarith
    -- Since `d ≠ 0` and `P` is bounded, some `i ∉ tight xstar` has `A_i · d > 0`
    let PosRows := (Finset.univ \ tight xstar).filter fun i => 0 < ∑ j, (A i j : ℝ) * d j
    have hPos_ne : PosRows.Nonempty := by
      by_contra hempty
      have hle0 : ∀ i, ∑ j, (A i j : ℝ) * d j ≤ 0 := by
        intro i
        by_cases hit : i ∈ tight xstar
        · rw [hd_tight i hit]
        · by_contra hgt
          push Not at hgt
          exact hempty ⟨i, Finset.mem_filter.mpr
            ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hit⟩, hgt⟩⟩
      obtain ⟨j0, hj0⟩ : ∃ j0, d j0 ≠ 0 := by
        by_contra h; push Not at h; exact hd_ne (funext h)
      let T : ℝ := (R + |xstar j0| + 1) / |d j0|
      have hT_nn : 0 ≤ T := by
        have hR0 : 0 ≤ R := le_trans (abs_nonneg (xstar j0)) (hP_bdd xstar hxstarF.1 j0)
        exact div_nonneg (by linarith [abs_nonneg (xstar j0)]) (abs_nonneg (d j0))
      let xT : Fin k → ℝ := fun j => xstar j + T * d j
      have hxTP : xT ∈ P := by
        intro i
        have hcalc : ∑ j, (A i j : ℝ) * xT j =
            (∑ j, (A i j : ℝ) * xstar j) + T * ∑ j, (A i j : ℝ) * d j := by
          simp only [xT, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
          congr 1; refine Finset.sum_congr rfl fun j _ => by ring
        rw [hcalc]
        have : T * ∑ j, (A i j : ℝ) * d j ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hT_nn (hle0 i)
        linarith [hxstarF.1 i]
      have hbddT := hP_bdd xT hxTP j0
      have hcalcT : T * |d j0| = R + |xstar j0| + 1 :=
        div_mul_cancel₀ _ (abs_ne_zero.mpr hj0)
      have htri : T * |d j0| ≤ |xT j0| + |xstar j0| := by
        have : T * d j0 = xT j0 - xstar j0 := by simp [xT]
        calc T * |d j0| = |T * d j0| := by rw [abs_mul, abs_of_nonneg hT_nn]
          _ = |xT j0 - xstar j0| := by rw [this]
          _ ≤ |xT j0| + |xstar j0| := abs_sub _ _
      linarith
    -- Step along `d` until hitting the first row `i_hit ∈ PosRows`
    let stepLen : Fin m → ℝ := fun i =>
      ((b i : ℝ) - ∑ j, (A i j : ℝ) * xstar j) / (∑ j, (A i j : ℝ) * d j)
    obtain ⟨ihit, hihit_mem, hihit_min⟩ := PosRows.exists_min_image stepLen hPos_ne
    have hihit_nt : ihit ∉ tight xstar := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hihit_mem).1).2
    have hihit_pos : 0 < ∑ j, (A ihit j : ℝ) * d j := (Finset.mem_filter.mp hihit_mem).2
    let tstar : ℝ := stepLen ihit
    have htstar_pos : 0 < tstar := by
      have hlt_i : ∑ j, (A ihit j : ℝ) * xstar j < (b ihit : ℝ) :=
        lt_of_le_of_ne (hxstarF.1 ihit) fun h =>
          hihit_nt (Finset.mem_filter.mpr ⟨Finset.mem_univ ihit, h⟩)
      exact div_pos (by linarith) hihit_pos
    let x' : Fin k → ℝ := fun j => xstar j + tstar * d j
    have hx'P : x' ∈ P := by
      intro i
      have hcalc : ∑ j, (A i j : ℝ) * x' j =
          (∑ j, (A i j : ℝ) * xstar j) + tstar * ∑ j, (A i j : ℝ) * d j := by
        simp only [x', mul_add, Finset.sum_add_distrib, Finset.mul_sum]
        congr 1; refine Finset.sum_congr rfl fun j _ => by ring
      rw [hcalc]
      by_cases hit : i ∈ tight xstar
      · rw [hd_tight i hit, mul_zero, add_zero]; exact hxstarF.1 i
      · by_cases hpos : 0 < ∑ j, (A i j : ℝ) * d j
        · have hiPos : i ∈ PosRows :=
            Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hit⟩, hpos⟩
          have hle := hihit_min i hiPos
          have := (le_div_iff₀ hpos).mp hle
          linarith
        · have hle0 : ∑ j, (A i j : ℝ) * d j ≤ 0 := not_lt.mp hpos
          have : tstar * ∑ j, (A i j : ℝ) * d j ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos (le_of_lt htstar_pos) hle0
          linarith [hxstarF.1 i]
    have hx'F : x' ∈ F := ⟨hx'P, by simp [x', hd_coord, hxstarF.2]⟩
    have htight_sub : tight xstar ⊆ tight x' := by
      intro i hi
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ i, ?_⟩
      have hcalc : ∑ j, (A i j : ℝ) * x' j =
          (∑ j, (A i j : ℝ) * xstar j) + tstar * ∑ j, (A i j : ℝ) * d j := by
        simp only [x', mul_add, Finset.sum_add_distrib, Finset.mul_sum]
        congr 1; refine Finset.sum_congr rfl fun j _ => by ring
      rw [hcalc, hd_tight i hi, mul_zero, add_zero]
      exact (Finset.mem_filter.mp hi).2
    have hihit_tight' : ihit ∈ tight x' := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ ihit, ?_⟩
      have hcalc : ∑ j, (A ihit j : ℝ) * x' j =
          (∑ j, (A ihit j : ℝ) * xstar j) + tstar * ∑ j, (A ihit j : ℝ) * d j := by
        simp only [x', mul_add, Finset.sum_add_distrib, Finset.mul_sum]
        congr 1; refine Finset.sum_congr rfl fun j _ => by ring
      rw [hcalc]
      have hmul : tstar * ∑ j, (A ihit j : ℝ) * d j = (b ihit : ℝ) - ∑ j, (A ihit j : ℝ) * xstar j :=
        div_mul_cancel₀ _ (ne_of_gt hihit_pos)
      linarith
    have hS_lt : S < Submodule.span ℝ (Arow '' (tight x' : Set (Fin m))) := by
      refine lt_of_le_of_ne (Submodule.span_mono (Set.image_mono (Finset.coe_subset.mpr htight_sub))) ?_
      intro heq
      have hmemS : Arow ihit ∈ S := heq ▸ Submodule.subset_span ⟨ihit, hihit_tight', rfl⟩
      linarith [hd_orth (Arow ihit) hmemS]
    have hrk_lt : rk xstar < rk x' := Submodule.finrank_lt_finrank_of_lt hS_lt
    linarith [hxstar_maxrk x' hx'F]
  -- Extract a basis of `k` linearly independent tight rows!
  have hspan_top : Submodule.span ℝ (Arow '' (tight xstar : Set (Fin m))) = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by rw [Module.finrank_fin_fun]; exact hrk_full)
  obtain ⟨s_sub, hs_sub, hs_basis⟩ :=
    exists_linearIndependent ℝ (Arow '' (tight xstar : Set (Fin m)))
  have hs_span : Submodule.span ℝ s_sub = ⊤ := by rw [hs_basis.1, hspan_top]
  have hs_fin : s_sub.Finite := ((tight xstar).finite_toSet.image Arow).subset hs_sub
  let _ : Fintype s_sub := hs_fin.fintype
  let bas : Module.Basis s_sub ℝ (Fin k → ℝ) :=
    Module.Basis.mk hs_basis.2 (by rw [Subtype.range_coe_subtype, Set.ofPred_mem_eq, hs_span])
  have hs_card : Fintype.card s_sub = k := by
    have := Module.finrank_eq_card_basis bas
    rw [Module.finrank_fin_fun] at this
    exact this.symm
  let eBasis : Fin k ≃ s_sub := (Fintype.equivFinOfCardEq hs_card).symm
  have hchoose : ∀ r : Fin k, ∃ i ∈ tight xstar, Arow i = (eBasis r).1 := fun r => by
    obtain ⟨i, hi, heq⟩ := hs_sub (eBasis r).2
    exact ⟨i, hi, heq⟩
  choose σ hσ_tight hσ_eq using hchoose
  let Mℤ : Matrix (Fin k) (Fin k) ℤ := fun r j => A (σ r) j
  let Mℝ : Matrix (Fin k) (Fin k) ℝ := fun r j => (A (σ r) j : ℝ)
  let rhsℤ : Fin k → ℤ := fun r => b (σ r)
  let rhsℝ : Fin k → ℝ := fun r => (b (σ r) : ℝ)
  have hMℝ_eq : Mℝ = Mℤ.map (Int.castRingHom ℝ) := by ext r j; rfl
  have hMℝ_li : LinearIndependent ℝ (fun r : Fin k => Mℝ r) := by
    have hfun : (fun r : Fin k => Mℝ r) = (fun v : s_sub => v.1) ∘ eBasis := by
      ext r j; exact congrFun (hσ_eq r) j
    rw [hfun]
    exact hs_basis.2.comp eBasis eBasis.injective
  have hMℝ_det : Mℝ.det ≠ 0 := by
    intro hdet0
    have hnot : ¬ LinearIndependent ℝ Mℝ.row := by
      rw [Matrix.linearIndependent_rows_iff_isUnit]
      intro hu
      obtain ⟨Bmat, hBmat⟩ := hu.exists_left_inv
      have h1 := congrArg Matrix.det hBmat
      rw [Matrix.det_mul, Matrix.det_one, hdet0, mul_zero] at h1
      exact one_ne_zero h1.symm
    exact hnot hMℝ_li
  have hMℤ_det : Mℤ.det ≠ 0 := by
    intro h0
    have hmap : ((Mℤ.det : ℤ) : ℝ) = Mℝ.det := by
      rw [hMℝ_eq]; exact (Int.castRingHom ℝ).map_det Mℤ
    rw [h0, Int.cast_zero] at hmap
    exact hMℝ_det hmap.symm
  have hmul_xstar : Mℝ.mulVec xstar = rhsℝ := by
    ext r
    simp only [Matrix.mulVec, dotProduct, Mℝ, rhsℝ]
    exact (Finset.mem_filter.mp (hσ_tight r)).2
  have hcramer_eq : Mℝ.det • xstar = Mℝ.cramer rhsℝ := by
    have h1 : Mℝ.mulVec (Mℝ.cramer rhsℝ) = Mℝ.det • rhsℝ := Matrix.mulVec_cramer Mℝ rhsℝ
    have h2 : Mℝ.mulVec (Mℝ.det • xstar) = Mℝ.det • rhsℝ := by
      rw [Matrix.mulVec_smul, hmul_xstar]
    have h3 : Mℝ.mulVec (Mℝ.det • xstar - Mℝ.cramer rhsℝ) = 0 := by
      rw [Matrix.mulVec_sub, h2, h1, sub_self]
    have hinv : Mℝ⁻¹ * Mℝ = 1 := Matrix.nonsing_inv_mul Mℝ (isUnit_iff_ne_zero.mpr hMℝ_det)
    have h4 : Mℝ.det • xstar - Mℝ.cramer rhsℝ = 0 := by
      calc Mℝ.det • xstar - Mℝ.cramer rhsℝ
          = (1 : Matrix (Fin k) (Fin k) ℝ).mulVec (Mℝ.det • xstar - Mℝ.cramer rhsℝ) := by simp
        _ = (Mℝ⁻¹ * Mℝ).mulVec (Mℝ.det • xstar - Mℝ.cramer rhsℝ) := by rw [hinv]
        _ = Mℝ⁻¹.mulVec (Mℝ.mulVec (Mℝ.det • xstar - Mℝ.cramer rhsℝ)) := by rw [Matrix.mulVec_mulVec]
        _ = 0 := by rw [h3, Matrix.mulVec_zero]
    exact sub_eq_zero.mp h4
  let q : ℚ := Rat.divInt (Mℤ.cramer rhsℤ coord) Mℤ.det
  have hq_val : (q : ℝ) = xstar coord := by
    have hcram_cast : ((Mℤ.cramer rhsℤ coord : ℤ) : ℝ) = Mℝ.cramer rhsℝ coord := by
      simp only [Matrix.cramer_apply]
      have hupd : Mℝ.updateCol coord rhsℝ = (Mℤ.updateCol coord rhsℤ).map (Int.castRingHom ℝ) := by
        ext r j
        simp only [Matrix.map_apply, Matrix.updateCol_apply, Int.coe_castRingHom]
        by_cases hj : j = coord
        · simp [hj, rhsℝ, rhsℤ]
        · simp [hj, Mℝ, Mℤ]
      rw [hupd]
      exact (Int.castRingHom ℝ).map_det (Mℤ.updateCol coord rhsℤ)
    have hdet_cast : ((Mℤ.det : ℤ) : ℝ) = Mℝ.det := by
      rw [hMℝ_eq]; exact (Int.castRingHom ℝ).map_det Mℤ
    have hcoord : Mℝ.det * xstar coord = Mℝ.cramer rhsℝ coord := by
      simpa using congrFun hcramer_eq coord
    have hdiv : (q : ℝ) = ((Mℤ.cramer rhsℤ coord : ℤ) : ℝ) / ((Mℤ.det : ℤ) : ℝ) := by
      simp only [q, Rat.divInt_eq_div]; push_cast; rfl
    rw [hdiv, hcram_cast, hdet_cast, ← hcoord, mul_div_cancel_left₀ _ hMℝ_det]
  have hdet_bound : Mℤ.det.natAbs ≤ Nat.factorial k * B ^ k := by
    rw [Matrix.det_apply]
    calc (∑ π : Equiv.Perm (Fin k), Equiv.Perm.sign π • ∏ r : Fin k, Mℤ (π r) r).natAbs
        ≤ ∑ π : Equiv.Perm (Fin k), (Equiv.Perm.sign π • ∏ r : Fin k, Mℤ (π r) r).natAbs :=
            Int.natAbs_sum_le _ _
      _ ≤ ∑ _π : Equiv.Perm (Fin k), B ^ k := by
            refine Finset.sum_le_sum fun π _ => ?_
            have hsign : (Equiv.Perm.sign π • ∏ r : Fin k, Mℤ (π r) r).natAbs =
                (∏ r : Fin k, Mℤ (π r) r).natAbs := by
              rw [Units.smul_def, zsmul_eq_mul, Int.natAbs_mul]
              rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> simp [h]
            rw [hsign, natAbs_finset_prod]
            calc ∏ r : Fin k, (Mℤ (π r) r).natAbs
                ≤ ∏ _r : Fin k, B := Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
                    (fun r _ => hA_bd (σ (π r)) r)
              _ = B ^ k := by simp
      _ = Nat.factorial k * B ^ k := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, smul_eq_mul]
  have hq_den : q.den ≤ Nat.factorial k * B ^ k := by
    have hdvd : (q.den : ℤ) ∣ Mℤ.det := Rat.den_dvd (Mℤ.cramer rhsℤ coord) Mℤ.det
    have hdvd_nat : q.den ∣ Mℤ.det.natAbs := Int.ofNat_dvd_left.mp hdvd
    exact le_trans (Nat.le_of_dvd (Int.natAbs_pos.mpr hMℤ_det) hdvd_nat) hdet_bound
  refine ⟨q, ⟨xstar, hxstarF.1, hq_val.symm⟩, fun x hx => ?_, hq_den⟩
  rw [hq_val, hxstarF.2]
  exact hx0max hx

/- ## Section 5: `BitstringEncoding` Length Bounds for `GameInput` -/

lemma encodePosNum_lt_two_pow : ∀ n : PosNum, (n : ℕ) < 2 ^ (Computability.encodePosNum n).length
  | PosNum.one => by simp [Computability.encodePosNum]
  | PosNum.bit0 m => by
    have ih := encodePosNum_lt_two_pow m
    simp only [Computability.encodePosNum, List.length_cons, pow_succ, PosNum.cast_bit0]
    omega
  | PosNum.bit1 m => by
    have ih := encodePosNum_lt_two_pow m
    simp only [Computability.encodePosNum, List.length_cons, pow_succ, PosNum.cast_bit1]
    omega

lemma nat_lt_two_pow_bitEncode (n : ℕ) :
    n < 2 ^ (BitstringEncoding.bitEncode n).length := by
  change n < 2 ^ (Computability.encodeNat n).length
  unfold Computability.encodeNat
  have hcast : ((n : Num) : ℕ) = n := Num.to_of_nat n
  rw [← hcast]
  cases h : (n : Num) with
  | zero => simp [Computability.encodeNum]
  | pos m => simpa [Computability.encodeNum] using encodePosNum_lt_two_pow m

lemma bitEncode_prod_length {α β : Type*} [BitstringEncoding α] [BitstringEncoding β] (p : α × β) :
    (BitstringEncoding.bitEncode p).length =
    2 * (BitstringEncoding.bitEncode p.1).length + 1 + (BitstringEncoding.bitEncode p.2).length := by
  change (BitstringEncoding.delimit (BitstringEncoding.bitEncode p.1) ++
    BitstringEncoding.bitEncode p.2).length = _
  rw [List.length_append, BitstringEncoding.length_delimit]

lemma bitEncode_list_length_ge_len {α : Type*} [BitstringEncoding α] (l : List α) :
    l.length ≤ (BitstringEncoding.bitEncode l).length := by
  change l.length ≤ (((l.map BitstringEncoding.bitEncode).map BitstringEncoding.delimit).flatten).length
  simpa using BitstringEncoding.length_le_length_flatten_delimit (l.map BitstringEncoding.bitEncode)

lemma bitEncode_list_sum_le {α : Type*} [BitstringEncoding α] (l : List α) :
    (l.map fun x => (BitstringEncoding.bitEncode x).length).sum ≤
      (BitstringEncoding.bitEncode l).length := by
  induction l with
  | nil => simp
  | cons a t ih =>
    change (BitstringEncoding.bitEncode a).length +
        (t.map fun x => (BitstringEncoding.bitEncode x).length).sum ≤
      (BitstringEncoding.delimit (BitstringEncoding.bitEncode a) ++
        BitstringEncoding.bitEncode t).length
    rw [List.length_append, BitstringEncoding.length_delimit]
    omega

lemma bitEncode_list_get_le {α : Type*} [BitstringEncoding α] (l : List α) (i : Fin l.length) :
    (BitstringEncoding.bitEncode (l.get i)).length ≤ (BitstringEncoding.bitEncode l).length := by
  have hmem : (BitstringEncoding.bitEncode (l.get i)).length ∈
      l.map (fun x => (BitstringEncoding.bitEncode x).length) :=
    List.mem_map_of_mem (List.get_mem l i)
  exact le_trans (List.le_sum_of_mem hmem) (bitEncode_list_sum_le l)

lemma rat_num_lt_two_pow_bitEncode (q : ℚ) :
    q.num.natAbs < 2 ^ (BitstringEncoding.bitEncode q).length := by
  have h1 : (BitstringEncoding.bitEncode q).length =
      2 * (BitstringEncoding.bitEncode q.num).length + 1 + (BitstringEncoding.bitEncode q.den).length :=
    bitEncode_prod_length (q.num, q.den)
  have h2 : (BitstringEncoding.bitEncode q.num).length =
      2 * (BitstringEncoding.bitEncode q.num.toNat).length + 1 +
      (BitstringEncoding.bitEncode (-q.num).toNat).length :=
    bitEncode_prod_length (q.num.toNat, (-q.num).toNat)
  have h3 := nat_lt_two_pow_bitEncode q.num.toNat
  have h4 := nat_lt_two_pow_bitEncode (-q.num).toNat
  have hlen1 : (BitstringEncoding.bitEncode q.num.toNat).length ≤ (BitstringEncoding.bitEncode q).length := by omega
  have hlen2 : (BitstringEncoding.bitEncode (-q.num).toNat).length ≤ (BitstringEncoding.bitEncode q).length := by omega
  rcases le_or_gt 0 q.num with hnn | hneg
  · have heq : q.num.natAbs = q.num.toNat := by omega
    rw [heq]; exact lt_of_lt_of_le h3 (Nat.pow_le_pow_right (by norm_num) hlen1)
  · have heq : q.num.natAbs = (-q.num).toNat := by omega
    rw [heq]; exact lt_of_lt_of_le h4 (Nat.pow_le_pow_right (by norm_num) hlen2)

lemma rat_den_lt_two_pow_bitEncode (q : ℚ) :
    q.den < 2 ^ (BitstringEncoding.bitEncode q).length := by
  have h1 : (BitstringEncoding.bitEncode q).length =
      2 * (BitstringEncoding.bitEncode q.num).length + 1 + (BitstringEncoding.bitEncode q.den).length :=
    bitEncode_prod_length (q.num, q.den)
  exact lt_of_lt_of_le (nat_lt_two_pow_bitEncode q.den)
    (Nat.pow_le_pow_right (by norm_num) (by omega))

lemma gameInput_bitEncode_bounds (g : GameInput) :
    let L := (BitstringEncoding.bitEncode g).length
    g.numTargets ≤ L ∧ g.numTypes ≤ L ∧
    (∏ θ : Fin g.numTypes, (g.prior θ).den) ≤ 2 ^ L ∧
    (∀ t : Fin g.numTargets,
      ((g.defenderPayoff t).2 - (g.defenderPayoff t).1).den ≤ 2 ^ L ∧
      ((g.defenderPayoff t).2 - (g.defenderPayoff t).1).num.natAbs ≤ 2 ^ (2 * L)) := by
  intro L
  have hL1 : L = 2 * (BitstringEncoding.bitEncode g.1).length + 1 +
      (BitstringEncoding.bitEncode g.2).length := bitEncode_prod_length g
  have hL2 : (BitstringEncoding.bitEncode g.2).length =
      2 * (BitstringEncoding.bitEncode g.2.1).length + 1 +
      (BitstringEncoding.bitEncode g.2.2).length := bitEncode_prod_length g.2
  have htargets_le : (BitstringEncoding.bitEncode g.2.1).length ≤ L := by omega
  have htypes_le : (BitstringEncoding.bitEncode g.2.2).length ≤ L := by omega
  refine ⟨le_trans (bitEncode_list_length_ge_len g.2.1) htargets_le,
    le_trans (bitEncode_list_length_ge_len g.2.2) htypes_le, ?_, ?_⟩
  · -- Product of prior denominators ≤ 2^L
    have hprod_le : ∏ θ : Fin g.numTypes, (g.prior θ).den ≤
        ∏ θ : Fin g.numTypes, 2 ^ (BitstringEncoding.bitEncode (g.2.2.get θ)).length := by
      refine Finset.prod_le_prod (fun _ _ => Nat.zero_le _) fun θ _ => ?_
      have h1 := le_of_lt (rat_den_lt_two_pow_bitEncode (g.prior θ))
      have h2 : (BitstringEncoding.bitEncode (g.prior θ)).length ≤
          (BitstringEncoding.bitEncode (g.2.2.get θ)).length := by
        have := bitEncode_prod_length (g.2.2.get θ)
        change (BitstringEncoding.bitEncode (g.2.2.get θ).1).length ≤ _
        omega
      exact le_trans h1 (Nat.pow_le_pow_right (by norm_num) h2)
    rw [Finset.prod_pow_eq_pow_sum] at hprod_le
    have hsum_le : ∑ θ : Fin g.numTypes, (BitstringEncoding.bitEncode (g.2.2.get θ)).length ≤ L := by
      have hlist : ∑ θ : Fin g.numTypes, (BitstringEncoding.bitEncode (g.2.2.get θ)).length =
          (g.2.2.map fun x => (BitstringEncoding.bitEncode x).length).sum :=
        sum_fin_get_eq_list_sum g.2.2 (fun x => (BitstringEncoding.bitEncode x).length)
      rw [hlist]
      exact le_trans (bitEncode_list_sum_le g.2.2) htypes_le
    exact le_trans hprod_le (Nat.pow_le_pow_right (by norm_num) hsum_le)
  · intro t
    let u0 := (g.defenderPayoff t).1
    let u1 := (g.defenderPayoff t).2
    have hpair_le : (BitstringEncoding.bitEncode (u0, u1)).length ≤ L :=
      le_trans (bitEncode_list_get_le g.2.1 t) htargets_le
    have hpair_eq : (BitstringEncoding.bitEncode (u0, u1)).length =
        2 * (BitstringEncoding.bitEncode u0).length + 1 + (BitstringEncoding.bitEncode u1).length :=
      bitEncode_prod_length (u0, u1)
    have hd0 := rat_den_lt_two_pow_bitEncode u0
    have hd1 := rat_den_lt_two_pow_bitEncode u1
    have hn0 := rat_num_lt_two_pow_bitEncode u0
    have hn1 := rat_num_lt_two_pow_bitEncode u1
    have hprod_den : u0.den * u1.den ≤ 2 ^ L := by
      calc u0.den * u1.den ≤ 2 ^ (BitstringEncoding.bitEncode u0).length *
            2 ^ (BitstringEncoding.bitEncode u1).length :=
              Nat.mul_le_mul (le_of_lt hd0) (le_of_lt hd1)
        _ = 2 ^ ((BitstringEncoding.bitEncode u0).length + (BitstringEncoding.bitEncode u1).length) :=
              (pow_add 2 _ _).symm
        _ ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hdiff_eq : u1 - u0 = Rat.divInt (u1.num * u0.den - u0.num * u1.den) (u1.den * u0.den) := by
      rw [Rat.divInt_eq_div]
      have hd1ne : (u1.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr u1.den_nz
      have hd0ne : (u0.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr u0.den_nz
      conv_lhs => rw [← Rat.num_div_den u1, ← Rat.num_div_den u0]
      push_cast
      field_simp [hd1ne, hd0ne]
    have hden_dvd : (u1 - u0).den ∣ u1.den * u0.den := by
      rw [hdiff_eq]
      have h := Rat.den_dvd (u1.num * u0.den - u0.num * u1.den) ((u1.den * u0.den : ℕ) : ℤ)
      exact Int.ofNat_dvd.mp (by simpa using h)
    have hden_pos : 0 < u1.den * u0.den := Nat.mul_pos u1.den_pos u0.den_pos
    have hden_le : (u1 - u0).den ≤ 2 ^ L :=
      le_trans (Nat.le_of_dvd hden_pos hden_dvd) (by simpa [Nat.mul_comm] using hprod_den)
    -- Numerator bound: `|(u1 - u0).num| ≤ |u1.num * u0.den - u0.num * u1.den|`
    have hnum_le : (u1 - u0).num.natAbs ≤ 2 ^ (2 * L) := by
      have hrat_eq : ((u1 - u0).num : ℤ) * (u1.den * u0.den : ℤ) =
          (u1.num * u0.den - u0.num * u1.den) * ((u1 - u0).den : ℤ) := by
        have hq : ((u1 - u0).num : ℚ) / ((u1 - u0).den : ℚ) =
            ((u1.num * u0.den - u0.num * u1.den : ℤ) : ℚ) / ((u1.den * u0.den : ℕ) : ℚ) := by
          rw [Rat.num_div_den, hdiff_eq, Rat.divInt_eq_div]; push_cast; rfl
        have hdne1 : ((u1 - u0).den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (u1 - u0).den_nz
        have hdne2 : ((u1.den * u0.den : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hden_pos)
        rw [div_eq_div_iff hdne1 hdne2] at hq
        exact_mod_cast hq
      have habs_eq : (u1 - u0).num.natAbs * (u1.den * u0.den) =
          (u1.num * u0.den - u0.num * u1.den).natAbs * (u1 - u0).den := by
        have := congrArg Int.natAbs hrat_eq
        simpa [Int.natAbs_mul] using this
      have hden_le' : (u1 - u0).den ≤ u1.den * u0.den := Nat.le_of_dvd hden_pos hden_dvd
      have hnum_le_raw : (u1 - u0).num.natAbs ≤ (u1.num * u0.den - u0.num * u1.den).natAbs := by
        have : (u1 - u0).num.natAbs * (u1.den * u0.den) ≤
            (u1.num * u0.den - u0.num * u1.den).natAbs * (u1.den * u0.den) := by
          rw [habs_eq]; exact Nat.mul_le_mul_left _ hden_le'
        exact Nat.le_of_mul_le_mul_right this hden_pos
      have htri : (u1.num * u0.den - u0.num * u1.den).natAbs ≤
          u1.num.natAbs * u0.den + u0.num.natAbs * u1.den := by
        calc (u1.num * u0.den - u0.num * u1.den).natAbs
            ≤ (u1.num * u0.den).natAbs + (u0.num * u1.den).natAbs := Int.natAbs_sub_le _ _
          _ = u1.num.natAbs * u0.den + u0.num.natAbs * u1.den := by simp [Int.natAbs_mul]
      have hterm1 : u1.num.natAbs * u0.den < 2 ^ L * 2 ^ (L - 1) := by
        have hlen_u1 : (BitstringEncoding.bitEncode u1).length ≤ L := by omega
        have hlen_u0 : (BitstringEncoding.bitEncode u0).length ≤ L - 1 := by omega
        exact Nat.mul_lt_mul'' (lt_of_lt_of_le hn1 (Nat.pow_le_pow_right (by norm_num) hlen_u1))
          (lt_of_lt_of_le hd0 (Nat.pow_le_pow_right (by norm_num) hlen_u0))
      have hterm2 : u0.num.natAbs * u1.den < 2 ^ (L - 1) * 2 ^ L := by
        have hlen_u0 : (BitstringEncoding.bitEncode u0).length ≤ L - 1 := by omega
        have hlen_u1 : (BitstringEncoding.bitEncode u1).length ≤ L := by omega
        exact Nat.mul_lt_mul'' (lt_of_lt_of_le hn0 (Nat.pow_le_pow_right (by norm_num) hlen_u0))
          (lt_of_lt_of_le hd1 (Nat.pow_le_pow_right (by norm_num) hlen_u1))
      have hLpos : 1 ≤ L := by omega
      have hpow_eq : 2 ^ L * 2 ^ (L - 1) + 2 ^ (L - 1) * 2 ^ L = 2 ^ (2 * L) := by
        have h1 : 2 ^ (L - 1) * 2 ^ L = 2 ^ L * 2 ^ (L - 1) := Nat.mul_comm _ _
        rw [h1, ← two_mul, ← mul_assoc, ← pow_succ', ← pow_add]
        congr 1; omega
      omega
    exact ⟨hden_le, hnum_le⟩

/- ## Section 6: Bridging `GameInput` and `RealGame`, Support Decoupling, and Main Proof -/

/-- Convert a valid `GameInput` to a `RealGame`. -/
noncomputable def ofGame (g : GameInput) (hg : g.Valid) : RealGame g.numTypes g.numTargets where
  π := fun θ => (g.prior θ : ℝ)
  b := fun θ t => ((g.attackerPayoff θ t).1 : ℝ)
  a := fun θ t => (((g.attackerPayoff θ t).1 - (g.attackerPayoff θ t).2 : ℚ) : ℝ)
  d := fun t => (((g.defenderPayoff t).2 - (g.defenderPayoff t).1 : ℚ) : ℝ)
  hn := hg.1
  hπ_nn := fun θ => Rat.cast_nonneg.mpr (hg.2.2.2.2 θ).1
  hπ_sum := by
    have := congrArg (Rat.cast : ℚ → ℝ) hg.2.2.1
    simpa using this
  ha_nn := fun θ t => Rat.cast_nonneg.mpr (sub_nonneg.mpr ((hg.2.2.2.2 θ).2.2 t))
  hd_nn := fun t => Rat.cast_nonneg.mpr (sub_nonneg.mpr (hg.2.2.2.1 t))

lemma ofGame_uA (g : GameInput) (hg : g.Valid) (c : Fin g.numTargets → ℝ)
    (θ : Fin g.numTypes) (t : Fin g.numTargets) :
    (ofGame g hg).uA c θ t =
      (1 - c t) * ((g.attackerPayoff θ t).1 : ℝ) + c t * ((g.attackerPayoff θ t).2 : ℝ) := by
  simp only [RealGame.uA, ofGame]
  push_cast
  ring

/-- Bridge from rational `EquilibriumOutput` to `RealGame.IsEq`. -/
lemma realIsEq_of_ratEq (g : GameInput) (hg : g.Valid) (lam : ℚ) (e : EquilibriumOutput)
    (_he1 : e.1.length = g.numTargets) (_he2 : e.2.length = g.numTypes)
    (hcov : ∀ t : Fin g.numTargets, 0 ≤ e.1[t.val]?.getD 0 ∧ e.1[t.val]?.getD 0 ≤ 1)
    (hatk : ∀ θ : Fin g.numTypes, (e.2[θ.val]?.getD []).length = g.numTargets ∧
      (∑ t : Fin g.numTargets, (e.2[θ.val]?.getD [])[t.val]?.getD 0) = 1 ∧
      ∀ t : Fin g.numTargets, 0 ≤ (e.2[θ.val]?.getD [])[t.val]?.getD 0)
    (hbr : ∀ (θ : Fin g.numTypes) (t s : Fin g.numTargets),
      0 < (e.2[θ.val]?.getD [])[t.val]?.getD 0 →
      (1 - e.1[s.val]?.getD 0) * (g.attackerPayoff θ s).1 +
        e.1[s.val]?.getD 0 * (g.attackerPayoff θ s).2 ≤
      (1 - e.1[t.val]?.getD 0) * (g.attackerPayoff θ t).1 +
        e.1[t.val]?.getD 0 * (g.attackerPayoff θ t).2)
    (hge : ∀ t : Fin g.numTargets, 0 < e.1[t.val]?.getD 0 →
      lam ≤ (∑ θ : Fin g.numTypes, g.prior θ * (e.2[θ.val]?.getD [])[t.val]?.getD 0) *
        ((g.defenderPayoff t).2 - (g.defenderPayoff t).1))
    (hle : ∀ t : Fin g.numTargets, e.1[t.val]?.getD 0 < 1 →
      (∑ θ : Fin g.numTypes, g.prior θ * (e.2[θ.val]?.getD [])[t.val]?.getD 0) *
        ((g.defenderPayoff t).2 - (g.defenderPayoff t).1) ≤ lam) :
    (ofGame g hg).IsEq (lam : ℝ)
      (fun t => (e.1[t.val]?.getD 0 : ℝ))
      (fun θ t => ((e.2[θ.val]?.getD [])[t.val]?.getD 0 : ℝ)) := by
  refine ⟨⟨fun t => ⟨Rat.cast_nonneg.mpr (hcov t).1, by dsimp only; exact_mod_cast (hcov t).2⟩,
    fun θ => ⟨by dsimp only; exact_mod_cast (hatk θ).2.1, fun t => Rat.cast_nonneg.mpr ((hatk θ).2.2 t)⟩,
    fun θ t s hpos => ?_, fun t hpos => ?_⟩, fun t hlt => ?_⟩
  · rw [ofGame_uA, ofGame_uA]
    dsimp only at hpos ⊢
    have hpos' : 0 < (e.2[θ.val]?.getD [])[t.val]?.getD 0 := by exact_mod_cast hpos
    exact_mod_cast hbr θ t s hpos'
  · dsimp only at hpos
    have hpos' : 0 < e.1[t.val]?.getD 0 := by exact_mod_cast hpos
    simp only [RealGame.gain, ofGame]
    exact_mod_cast hge t hpos'
  · dsimp only at hlt
    have hlt' : e.1[t.val]?.getD 0 < 1 := by exact_mod_cast hlt
    simp only [RealGame.gain, ofGame]
    exact_mod_cast hle t hlt'

/-- Support-decoupled rationality: any real equilibrium at rational `lam` with `∑ c ≥ r`
(or `∑ c = r`) yields a rational `EquilibriumOutput` with the same coverage relation! -/
lemma ratEq_of_realIsEq (g : GameInput) (hg : g.Valid) (lam : ℚ) (exactSum : Bool) (R : ℚ)
    {c : Fin g.numTargets → ℝ} {p : Fin g.numTypes → Fin g.numTargets → ℝ}
    (heq : (ofGame g hg).IsEq (lam : ℝ) c p)
    (hsum : if exactSum then ∑ t, c t = (R : ℝ) else (R : ℝ) ≤ ∑ t, c t) :
    ∃ e : EquilibriumOutput,
      let cov (t : Fin g.numTargets) := e.1[t.val]?.getD 0
      let row (θ : Fin g.numTypes) := e.2[θ.val]?.getD []
      let atk (θ : Fin g.numTypes) (t : Fin g.numTargets) := (row θ)[t.val]?.getD 0
      let uA (θ : Fin g.numTypes) (t : Fin g.numTargets) :=
        (1 - cov t) * (g.attackerPayoff θ t).1 + cov t * (g.attackerPayoff θ t).2
      let gain (t : Fin g.numTargets) :=
        (∑ θ : Fin g.numTypes, g.prior θ * atk θ t) *
          ((g.defenderPayoff t).2 - (g.defenderPayoff t).1)
      e.1.length = g.numTargets ∧ e.2.length = g.numTypes ∧
      (∀ t, 0 ≤ cov t ∧ cov t ≤ 1) ∧
      (∀ θ, (row θ).length = g.numTargets ∧ (∑ t, atk θ t) = 1 ∧ ∀ t, 0 ≤ atk θ t) ∧
      (∀ θ t s, 0 < atk θ t → uA θ s ≤ uA θ t) ∧
      (∀ t, 0 < cov t → lam ≤ gain t) ∧ (∀ t, cov t < 1 → gain t ≤ lam) ∧
      (if exactSum then (∑ t, cov t) = R else R ≤ ∑ t, cov t) := by
  classical
  let G := ofGame g hg
  let T0 : Finset (Fin g.numTargets) := Finset.univ.filter fun t => c t = 0
  let T1 : Finset (Fin g.numTargets) := Finset.univ.filter fun t => c t = 1
  let B : Fin g.numTypes → Finset (Fin g.numTargets) := fun θ =>
    Finset.univ.filter fun t => G.uA c θ t = G.maxUtil c θ
  -- 1. Rational `(c_ℚ, v_ℚ)` LP from real `(c, G.maxUtil c)`
  let eCV := Fintype.equivFin (Fin g.numTargets ⊕ Fin g.numTypes)
  let CVRow := (Fin g.numTargets ⊕ Fin g.numTargets) ⊕
    ((Fin g.numTypes × Fin g.numTargets) ⊕ (Fin g.numTypes × Fin g.numTargets)) ⊕
    (Unit ⊕ Unit)
  let eCVR := Fintype.equivFin CVRow
  let aCV : Fin (Fintype.card CVRow) → Fin (Fintype.card (Fin g.numTargets ⊕ Fin g.numTypes)) → ℚ :=
    fun r col =>
      match eCVR.symm r, eCV.symm col with
      | Sum.inl (Sum.inl t), Sum.inl t' => if t = t' then -1 else 0
      | Sum.inl (Sum.inl _), Sum.inr _ => 0
      | Sum.inl (Sum.inr t), Sum.inl t' => if t = t' then 1 else 0
      | Sum.inl (Sum.inr _), Sum.inr _ => 0
      | Sum.inr (Sum.inl (Sum.inl (θ, t))), Sum.inl t' =>
          if t = t' then -((g.attackerPayoff θ t).1 - (g.attackerPayoff θ t).2) else 0
      | Sum.inr (Sum.inl (Sum.inl (θ, _))), Sum.inr θ' => if θ = θ' then -1 else 0
      | Sum.inr (Sum.inl (Sum.inr (θ, t))), Sum.inl t' =>
          if t ∈ B θ ∧ t = t' then ((g.attackerPayoff θ t).1 - (g.attackerPayoff θ t).2) else 0
      | Sum.inr (Sum.inl (Sum.inr (θ, t))), Sum.inr θ' =>
          if t ∈ B θ ∧ θ = θ' then 1 else 0
      | Sum.inr (Sum.inr (Sum.inl ())), Sum.inl _ => -1
      | Sum.inr (Sum.inr (Sum.inl ())), Sum.inr _ => 0
      | Sum.inr (Sum.inr (Sum.inr ())), Sum.inl _ => if exactSum then 1 else 0
      | Sum.inr (Sum.inr (Sum.inr ())), Sum.inr _ => 0
  let bCV : Fin (Fintype.card CVRow) → ℚ := fun r =>
    match eCVR.symm r with
    | Sum.inl (Sum.inl t) => if t ∈ T1 then -1 else 0
    | Sum.inl (Sum.inr t) => if t ∈ T0 then 0 else 1
    | Sum.inr (Sum.inl (Sum.inl (θ, t))) => -(g.attackerPayoff θ t).1
    | Sum.inr (Sum.inl (Sum.inr (θ, t))) => if t ∈ B θ then (g.attackerPayoff θ t).1 else 0
    | Sum.inr (Sum.inr (Sum.inl ())) => -R
    | Sum.inr (Sum.inr (Sum.inr ())) => if exactSum then R else 0
  have hCV_real : ∃ x : Fin (Fintype.card (Fin g.numTargets ⊕ Fin g.numTypes)) → ℝ,
      ∀ r, ∑ col, (aCV r col : ℝ) * x col ≤ (bCV r : ℝ) := by
    let x : Fin (Fintype.card (Fin g.numTargets ⊕ Fin g.numTypes)) → ℝ := fun col =>
      match eCV.symm col with
      | Sum.inl t => c t
      | Sum.inr θ => G.maxUtil c θ
    refine ⟨x, fun r => ?_⟩
    rw [← eCV.sum_comp]
    simp only [x, Equiv.symm_apply_apply, Fintype.sum_sum_type]
    match hr : eCVR.symm r with
    | Sum.inl (Sum.inl t) =>
      simp only [aCV, bCV, hr, Equiv.symm_apply_apply, Rat.cast_zero, zero_mul, Finset.sum_const_zero, add_zero]
      rw [Finset.sum_eq_single t]
      · simp only [↓reduceIte, Rat.cast_neg, Rat.cast_one, neg_mul, one_mul]
        split_ifs with ht1
        · have := (Finset.mem_filter.mp ht1).2; simp; linarith
        · simp; linarith [(heq.1.1 t).1]
      · intro t' _ hne; simp [Ne.symm hne]
      · intro habs; exact absurd (Finset.mem_univ _) habs
    | Sum.inl (Sum.inr t) =>
      simp only [aCV, bCV, hr, Equiv.symm_apply_apply, Rat.cast_zero, zero_mul, Finset.sum_const_zero, add_zero]
      rw [Finset.sum_eq_single t]
      · simp only [↓reduceIte, Rat.cast_one, one_mul]
        split_ifs with ht0
        · have := (Finset.mem_filter.mp ht0).2; simp; linarith
        · simp; linarith [(heq.1.1 t).2]
      · intro t' _ hne; simp [Ne.symm hne]
      · intro habs; exact absurd (Finset.mem_univ _) habs
    | Sum.inr (Sum.inl (Sum.inl (θ, t))) =>
      simp only [aCV, bCV, hr, Equiv.symm_apply_apply]
      have h1 : ∑ t' : Fin g.numTargets,
          ((if t = t' then -((g.attackerPayoff θ t).1 - (g.attackerPayoff θ t).2) else 0 : ℚ) : ℝ) * c t' =
          -(((g.attackerPayoff θ t).1 - (g.attackerPayoff θ t).2 : ℚ) : ℝ) * c t := by
        rw [Finset.sum_eq_single t]
        · simp
        · intro t' _ hne; simp [Ne.symm hne]
        · intro habs; exact absurd (Finset.mem_univ _) habs
      have h2 : ∑ θ' : Fin g.numTypes, ((if θ = θ' then (-1 : ℚ) else 0 : ℚ) : ℝ) * G.maxUtil c θ' =
          -G.maxUtil c θ := by
        rw [Finset.sum_eq_single θ]
        · simp
        · intro θ' _ hne; simp [Ne.symm hne]
        · intro habs; exact absurd (Finset.mem_univ _) habs
      rw [h1, h2]
      have hmax := G.le_maxUtil c θ t
      simp only [RealGame.uA, G, ofGame] at hmax ⊢
      simp only [Rat.cast_neg]
      linarith
    | Sum.inr (Sum.inl (Sum.inr (θ, t))) =>
      simp only [aCV, bCV, hr, Equiv.symm_apply_apply]
      by_cases htB : t ∈ B θ
      · simp only [htB, true_and, ↓reduceIte]
        have h1 : ∑ t' : Fin g.numTargets,
            ((if t = t' then ((g.attackerPayoff θ t).1 - (g.attackerPayoff θ t).2) else 0 : ℚ) : ℝ) * c t' =
            (((g.attackerPayoff θ t).1 - (g.attackerPayoff θ t).2 : ℚ) : ℝ) * c t := by
          rw [Finset.sum_eq_single t]
          · simp
          · intro t' _ hne; simp [Ne.symm hne]
          · intro habs; exact absurd (Finset.mem_univ _) habs
        have h2 : ∑ θ' : Fin g.numTypes, ((if θ = θ' then (1 : ℚ) else 0 : ℚ) : ℝ) * G.maxUtil c θ' =
            G.maxUtil c θ := by
          rw [Finset.sum_eq_single θ]
          · simp
          · intro θ' _ hne; simp [Ne.symm hne]
          · intro habs; exact absurd (Finset.mem_univ _) habs
        rw [h1, h2]
        have hmax := (Finset.mem_filter.mp htB).2
        simp only [RealGame.uA, G, ofGame] at hmax ⊢
        linarith
      · simp [htB]
    | Sum.inr (Sum.inr (Sum.inl ())) =>
      simp only [aCV, bCV, hr, Equiv.symm_apply_apply, Rat.cast_neg, Rat.cast_one, neg_mul, one_mul,
        Finset.sum_neg_distrib, Rat.cast_zero, zero_mul, Finset.sum_const_zero, add_zero]
      cases exactSum <;> simp at hsum <;> linarith
    | Sum.inr (Sum.inr (Sum.inr ())) =>
      simp only [aCV, bCV, hr, Equiv.symm_apply_apply, Rat.cast_zero, zero_mul, Finset.sum_const_zero, add_zero]
      cases exactSum
      · simp
      · simp only [↓reduceIte, Rat.cast_one, one_mul] at hsum ⊢; linarith
  obtain ⟨qCV, hqCV⟩ := rat_of_real_feasible aCV bCV hCV_real
  let cQ : Fin g.numTargets → ℚ := fun t => qCV (eCV (Sum.inl t))
  let vQ : Fin g.numTypes → ℚ := fun θ => qCV (eCV (Sum.inr θ))
  -- 2. Rational `p_ℚ` LP from real `p`
  let eP := Fintype.equivFin (Fin g.numTypes × Fin g.numTargets)
  let PRow := (Fin g.numTypes × Fin g.numTargets) ⊕ (Fin g.numTypes × Fin g.numTargets) ⊕
    (Fin g.numTypes ⊕ Fin g.numTypes) ⊕ (Fin g.numTargets ⊕ Fin g.numTargets)
  let ePR := Fintype.equivFin PRow
  let aP : Fin (Fintype.card PRow) → Fin (Fintype.card (Fin g.numTypes × Fin g.numTargets)) → ℚ :=
    fun r col =>
      let (θ', t') := eP.symm col
      match ePR.symm r with
      | Sum.inl (θ, t) => if θ' = θ ∧ t' = t then -1 else 0
      | Sum.inr (Sum.inl (θ, t)) => if t ∉ B θ ∧ θ' = θ ∧ t' = t then 1 else 0
      | Sum.inr (Sum.inr (Sum.inl (Sum.inl θ))) => if θ' = θ then 1 else 0
      | Sum.inr (Sum.inr (Sum.inl (Sum.inr θ))) => if θ' = θ then -1 else 0
      | Sum.inr (Sum.inr (Sum.inr (Sum.inl t))) =>
          if t ∉ T0 ∧ t' = t then -(g.prior θ' * ((g.defenderPayoff t).2 - (g.defenderPayoff t).1)) else 0
      | Sum.inr (Sum.inr (Sum.inr (Sum.inr t))) =>
          if t ∉ T1 ∧ t' = t then g.prior θ' * ((g.defenderPayoff t).2 - (g.defenderPayoff t).1) else 0
  let bP : Fin (Fintype.card PRow) → ℚ := fun r =>
    match ePR.symm r with
    | Sum.inl _ => 0
    | Sum.inr (Sum.inl _) => 0
    | Sum.inr (Sum.inr (Sum.inl (Sum.inl _))) => 1
    | Sum.inr (Sum.inr (Sum.inl (Sum.inr _))) => -1
    | Sum.inr (Sum.inr (Sum.inr (Sum.inl t))) => if t ∉ T0 then -lam else 0
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr t))) => if t ∉ T1 then lam else 0
  have hP_real : ∃ x : Fin (Fintype.card (Fin g.numTypes × Fin g.numTargets)) → ℝ,
      ∀ r, ∑ col, (aP r col : ℝ) * x col ≤ (bP r : ℝ) := by
    let x : Fin (Fintype.card (Fin g.numTypes × Fin g.numTargets)) → ℝ := fun col =>
      p (eP.symm col).1 (eP.symm col).2
    refine ⟨x, fun r => ?_⟩
    rw [← eP.sum_comp]
    simp only [x, Equiv.symm_apply_apply]
    match hr : ePR.symm r with
    | Sum.inl (θ, t) =>
      simp only [aP, bP, hr, Equiv.symm_apply_apply, Rat.cast_zero]
      rw [Finset.sum_eq_single (θ, t)]
      · simp; linarith [(heq.1.2.1 θ).2 t]
      · intro q _ hne
        have : ¬ (q.1 = θ ∧ q.2 = t) := fun ⟨h1, h2⟩ => hne (Prod.ext h1 h2)
        simp [this]
      · intro habs; exact absurd (Finset.mem_univ _) habs
    | Sum.inr (Sum.inl (θ, t)) =>
      simp only [aP, bP, hr, Equiv.symm_apply_apply, Rat.cast_zero]
      by_cases htB : t ∈ B θ
      · simp [htB]
      · simp only [htB, not_false_eq_true, true_and]
        rw [Finset.sum_eq_single (θ, t)]
        · simp only [and_self, ↓reduceIte, Rat.cast_one, one_mul]
          by_contra hpos
          push Not at hpos
          exact htB (Finset.mem_filter.mpr ⟨Finset.mem_univ t,
            (G.isAtkBR_iff_maxUtil c p).mp heq.1.2.2.1 θ t hpos⟩)
        · intro q _ hne
          have : ¬ (q.1 = θ ∧ q.2 = t) := fun ⟨h1, h2⟩ => hne (Prod.ext h1 h2)
          simp [this]
        · intro habs; exact absurd (Finset.mem_univ _) habs
    | Sum.inr (Sum.inr (Sum.inl (Sum.inl θ))) =>
      simp only [aP, bP, hr, Equiv.symm_apply_apply, Rat.cast_one]
      rw [Fintype.sum_prod_type, Finset.sum_eq_single θ]
      · simp [(heq.1.2.1 θ).1]
      · intro θ' _ hne; simp [hne]
      · intro habs; exact absurd (Finset.mem_univ _) habs
    | Sum.inr (Sum.inr (Sum.inl (Sum.inr θ))) =>
      simp only [aP, bP, hr, Equiv.symm_apply_apply, Rat.cast_neg, Rat.cast_one]
      rw [Fintype.sum_prod_type, Finset.sum_eq_single θ]
      · simp [(heq.1.2.1 θ).1]
      · intro θ' _ hne; simp [hne]
      · intro habs; exact absurd (Finset.mem_univ _) habs
    | Sum.inr (Sum.inr (Sum.inr (Sum.inl t))) =>
      simp only [aP, bP, hr, Equiv.symm_apply_apply]
      by_cases ht0 : t ∈ T0
      · simp [ht0]
      · simp only [ht0, not_false_eq_true, true_and, ↓reduceIte, Rat.cast_neg]
        rw [Fintype.sum_prod_type]
        have hsum : ∑ θ : Fin g.numTypes, ∑ t' : Fin g.numTargets,
            ((if t' = t then -(g.prior θ * ((g.defenderPayoff t).2 - (g.defenderPayoff t).1)) else 0 : ℚ) : ℝ) *
              p θ t' = -G.gain p t := by
          have h1 : ∀ θ : Fin g.numTypes, ∑ t' : Fin g.numTargets,
              ((if t' = t then -(g.prior θ * ((g.defenderPayoff t).2 - (g.defenderPayoff t).1)) else 0 : ℚ) : ℝ) *
                p θ t' = -((g.prior θ : ℝ) * p θ t * (((g.defenderPayoff t).2 - (g.defenderPayoff t).1 : ℚ) : ℝ)) := by
            intro θ
            rw [Finset.sum_eq_single t]
            · simp; ring
            · intro t' _ hne; simp [hne]
            · intro habs; exact absurd (Finset.mem_univ _) habs
          simp only [h1, Finset.sum_neg_distrib, ← Finset.sum_mul, RealGame.gain, G, ofGame]
        rw [hsum]
        have htpos : 0 < c t := lt_of_le_of_ne (heq.1.1 t).1 fun h =>
          ht0 (Finset.mem_filter.mpr ⟨Finset.mem_univ t, h.symm⟩)
        linarith [heq.1.2.2.2 t htpos]
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr t))) =>
      simp only [aP, bP, hr, Equiv.symm_apply_apply]
      by_cases ht1 : t ∈ T1
      · simp [ht1]
      · simp only [ht1, not_false_eq_true, true_and, ↓reduceIte]
        rw [Fintype.sum_prod_type]
        have hsum : ∑ θ : Fin g.numTypes, ∑ t' : Fin g.numTargets,
            ((if t' = t then g.prior θ * ((g.defenderPayoff t).2 - (g.defenderPayoff t).1) else 0 : ℚ) : ℝ) *
              p θ t' = G.gain p t := by
          have h1 : ∀ θ : Fin g.numTypes, ∑ t' : Fin g.numTargets,
              ((if t' = t then g.prior θ * ((g.defenderPayoff t).2 - (g.defenderPayoff t).1) else 0 : ℚ) : ℝ) *
                p θ t' = (g.prior θ : ℝ) * p θ t * (((g.defenderPayoff t).2 - (g.defenderPayoff t).1 : ℚ) : ℝ) := by
            intro θ
            rw [Finset.sum_eq_single t]
            · simp; ring
            · intro t' _ hne; simp [hne]
            · intro habs; exact absurd (Finset.mem_univ _) habs
          simp only [h1, ← Finset.sum_mul, RealGame.gain, G, ofGame]
        rw [hsum]
        have htlt1 : c t < 1 := lt_of_le_of_ne (heq.1.1 t).2 fun h =>
          ht1 (Finset.mem_filter.mpr ⟨Finset.mem_univ t, h⟩)
        exact heq.2 t htlt1
  obtain ⟨qP, hqP⟩ := rat_of_real_feasible aP bP hP_real
  let pQ : Fin g.numTypes → Fin g.numTargets → ℚ := fun θ t => qP (eP (θ, t))
  -- Build `EquilibriumOutput` from `(cQ, pQ)` and verify every condition!
  let eOut : EquilibriumOutput :=
    (List.ofFn cQ, List.ofFn fun θ => List.ofFn fun t => pQ θ t)
  have hcov_eq : ∀ t : Fin g.numTargets, eOut.1[t.val]?.getD 0 = cQ t := fun t => by simp [eOut]
  have hatk_eq : ∀ θ t, (eOut.2[θ.val]?.getD [])[t.val]?.getD 0 = pQ θ t := fun θ t => by simp [eOut]
  have hcQ_ge0 : ∀ t, 0 ≤ cQ t := fun t => by
    have h := hqCV (eCVR (Sum.inl (Sum.inl t)))
    rw [← eCV.sum_comp] at h
    simp only [aCV, bCV, Equiv.symm_apply_apply, Fintype.sum_sum_type, zero_mul,
      Finset.sum_const_zero, add_zero] at h
    rw [Finset.sum_eq_single t] at h
    · simp only [↓reduceIte, neg_mul, one_mul] at h
      split_ifs at h <;> linarith
    · intro t' _ hne; simp [Ne.symm hne]
    · intro habs; exact absurd (Finset.mem_univ _) habs
  have hcQ_le1 : ∀ t, cQ t ≤ 1 := fun t => by
    have h := hqCV (eCVR (Sum.inl (Sum.inr t)))
    rw [← eCV.sum_comp] at h
    simp only [aCV, bCV, Equiv.symm_apply_apply, Fintype.sum_sum_type, zero_mul,
      Finset.sum_const_zero, add_zero] at h
    rw [Finset.sum_eq_single t] at h
    · simp only [↓reduceIte, one_mul] at h
      split_ifs at h <;> linarith
    · intro t' _ hne; simp [Ne.symm hne]
    · intro habs; exact absurd (Finset.mem_univ _) habs
  have hcQ_T0 : ∀ t ∈ T0, cQ t = 0 := fun t ht0 => by
    have h := hqCV (eCVR (Sum.inl (Sum.inr t)))
    rw [← eCV.sum_comp] at h
    simp only [aCV, bCV, Equiv.symm_apply_apply, Fintype.sum_sum_type, zero_mul,
      Finset.sum_const_zero, add_zero, ht0, ↓reduceIte] at h
    rw [Finset.sum_eq_single t] at h
    · simp only [↓reduceIte, one_mul] at h; linarith [hcQ_ge0 t]
    · intro t' _ hne; simp [Ne.symm hne]
    · intro habs; exact absurd (Finset.mem_univ _) habs
  have hcQ_T1 : ∀ t ∈ T1, cQ t = 1 := fun t ht1 => by
    have h := hqCV (eCVR (Sum.inl (Sum.inl t)))
    rw [← eCV.sum_comp] at h
    simp only [aCV, bCV, Equiv.symm_apply_apply, Fintype.sum_sum_type, zero_mul,
      Finset.sum_const_zero, add_zero, ht1, ↓reduceIte] at h
    rw [Finset.sum_eq_single t] at h
    · simp only [↓reduceIte, neg_mul, one_mul] at h; linarith [hcQ_le1 t]
    · intro t' _ hne; simp [Ne.symm hne]
    · intro habs; exact absurd (Finset.mem_univ _) habs
  have huA_le : ∀ θ t, (1 - cQ t) * (g.attackerPayoff θ t).1 + cQ t * (g.attackerPayoff θ t).2 ≤ vQ θ := by
    intro θ t
    have h := hqCV (eCVR (Sum.inr (Sum.inl (Sum.inl (θ, t)))))
    rw [← eCV.sum_comp] at h
    simp only [aCV, bCV, Equiv.symm_apply_apply, Fintype.sum_sum_type] at h
    have h1 : ∑ t' : Fin g.numTargets,
        (if t = t' then -((g.attackerPayoff θ t).1 - (g.attackerPayoff θ t).2) else 0) * cQ t' =
        -((g.attackerPayoff θ t).1 - (g.attackerPayoff θ t).2) * cQ t := by
      rw [Finset.sum_eq_single t]
      · simp
      · intro t' _ hne; simp [Ne.symm hne]
      · intro habs; exact absurd (Finset.mem_univ _) habs
    have h2 : ∑ θ' : Fin g.numTypes, (if θ = θ' then (-1 : ℚ) else 0) * vQ θ' = -vQ θ := by
      rw [Finset.sum_eq_single θ]
      · simp
      · intro θ' _ hne; simp [Ne.symm hne]
      · intro habs; exact absurd (Finset.mem_univ _) habs
    change (∑ t', (if t = t' then -((g.attackerPayoff θ t).1 - (g.attackerPayoff θ t).2) else 0) * cQ t') +
      (∑ θ', (if θ = θ' then (-1 : ℚ) else 0) * vQ θ') ≤ -(g.attackerPayoff θ t).1 at h
    rw [h1, h2] at h
    linarith
  have huA_eq_B : ∀ θ t, t ∈ B θ →
      (1 - cQ t) * (g.attackerPayoff θ t).1 + cQ t * (g.attackerPayoff θ t).2 = vQ θ := by
    intro θ t htB
    have h := hqCV (eCVR (Sum.inr (Sum.inl (Sum.inr (θ, t)))))
    rw [← eCV.sum_comp] at h
    simp only [aCV, bCV, Equiv.symm_apply_apply, Fintype.sum_sum_type, htB, true_and, ↓reduceIte] at h
    have h1 : ∑ t' : Fin g.numTargets,
        (if t = t' then ((g.attackerPayoff θ t).1 - (g.attackerPayoff θ t).2) else 0) * cQ t' =
        ((g.attackerPayoff θ t).1 - (g.attackerPayoff θ t).2) * cQ t := by
      rw [Finset.sum_eq_single t]
      · simp
      · intro t' _ hne; simp [Ne.symm hne]
      · intro habs; exact absurd (Finset.mem_univ _) habs
    have h2 : ∑ θ' : Fin g.numTypes, (if θ = θ' then (1 : ℚ) else 0) * vQ θ' = vQ θ := by
      rw [Finset.sum_eq_single θ]
      · simp
      · intro θ' _ hne; simp [Ne.symm hne]
      · intro habs; exact absurd (Finset.mem_univ _) habs
    change (∑ t', (if t = t' then ((g.attackerPayoff θ t).1 - (g.attackerPayoff θ t).2) else 0) * cQ t') +
      (∑ θ', (if θ = θ' then (1 : ℚ) else 0) * vQ θ') ≤ (g.attackerPayoff θ t).1 at h
    rw [h1, h2] at h
    linarith [huA_le θ t]
  have hpQ_nn : ∀ θ t, 0 ≤ pQ θ t := fun θ t => by
    have h := hqP (ePR (Sum.inl (θ, t)))
    rw [← eP.sum_comp] at h
    simp only [aP, bP, Equiv.symm_apply_apply] at h
    rw [Finset.sum_eq_single (θ, t)] at h
    · simp only [and_self, ↓reduceIte, neg_mul, one_mul] at h; exact neg_nonpos.mp h
    · intro q _ hne
      have : ¬ (q.1 = θ ∧ q.2 = t) := fun ⟨h1, h2⟩ => hne (Prod.ext h1 h2)
      simp [this]
    · intro habs; exact absurd (Finset.mem_univ _) habs
  have hpQ_supp : ∀ θ t, 0 < pQ θ t → t ∈ B θ := fun θ t hpos => by
    by_contra hnB
    have h := hqP (ePR (Sum.inr (Sum.inl (θ, t))))
    rw [← eP.sum_comp] at h
    simp only [aP, bP, Equiv.symm_apply_apply, hnB, not_false_eq_true, true_and] at h
    rw [Finset.sum_eq_single (θ, t)] at h
    · simp only [and_self, ↓reduceIte, one_mul] at h; linarith
    · intro q _ hne
      have : ¬ (q.1 = θ ∧ q.2 = t) := fun ⟨h1, h2⟩ => hne (Prod.ext h1 h2)
      simp [this]
    · intro habs; exact absurd (Finset.mem_univ _) habs
  refine ⟨eOut, by simp [eOut], by simp [eOut], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t; dsimp only; rw [hcov_eq]; exact ⟨hcQ_ge0 t, hcQ_le1 t⟩
  · intro θ
    refine ⟨by simp [eOut], ?_, fun t => by dsimp only; rw [hatk_eq]; exact hpQ_nn θ t⟩
    simp only [hatk_eq]
    have h1 := hqP (ePR (Sum.inr (Sum.inr (Sum.inl (Sum.inl θ)))))
    have h2 := hqP (ePR (Sum.inr (Sum.inr (Sum.inl (Sum.inr θ)))))
    rw [← eP.sum_comp, Fintype.sum_prod_type] at h1 h2
    simp only [aP, bP, Equiv.symm_apply_apply] at h1 h2
    rw [Finset.sum_eq_single θ] at h1 h2
    · simp only [↓reduceIte, one_mul, neg_mul, Finset.sum_neg_distrib] at h1 h2
      change ∑ t, pQ θ t ≤ 1 at h1
      change -(∑ t, pQ θ t) ≤ -1 at h2
      linarith
    · intro θ' _ hne; simp [hne]
    · intro habs; exact absurd (Finset.mem_univ _) habs
    · intro θ' _ hne; simp [hne]
    · intro habs; exact absurd (Finset.mem_univ _) habs
  · intro θ t s hpos
    simp only [hcov_eq, hatk_eq] at hpos ⊢
    rw [huA_eq_B θ t (hpQ_supp θ t hpos)]
    exact huA_le θ s
  · intro t hpos
    simp only [hcov_eq, hatk_eq] at hpos ⊢
    have hnt0 : t ∉ T0 := fun ht0 => by linarith [hcQ_T0 t ht0]
    have h := hqP (ePR (Sum.inr (Sum.inr (Sum.inr (Sum.inl t)))))
    rw [← eP.sum_comp, Fintype.sum_prod_type] at h
    simp only [aP, bP, Equiv.symm_apply_apply, hnt0, not_false_eq_true, true_and, ↓reduceIte] at h
    have hsum : ∑ θ : Fin g.numTypes, ∑ t' : Fin g.numTargets,
        (if t' = t then -(g.prior θ * ((g.defenderPayoff t).2 - (g.defenderPayoff t).1)) else 0) * pQ θ t' =
        -((∑ θ : Fin g.numTypes, g.prior θ * pQ θ t) * ((g.defenderPayoff t).2 - (g.defenderPayoff t).1)) := by
      have h1 : ∀ θ, ∑ t' : Fin g.numTargets,
          (if t' = t then -(g.prior θ * ((g.defenderPayoff t).2 - (g.defenderPayoff t).1)) else 0) * pQ θ t' =
          -(g.prior θ * pQ θ t * ((g.defenderPayoff t).2 - (g.defenderPayoff t).1)) := by
        intro θ; rw [Finset.sum_eq_single t]
        · simp; ring
        · intro t' _ hne; simp [hne]
        · intro habs; exact absurd (Finset.mem_univ _) habs
      simp only [h1, Finset.sum_neg_distrib, ← Finset.sum_mul]
    change (∑ θ, ∑ t', (if t' = t then -(g.prior θ * ((g.defenderPayoff t).2 - (g.defenderPayoff t).1)) else 0) * pQ θ t') ≤ -lam at h
    rw [hsum] at h
    linarith
  · intro t hlt
    simp only [hcov_eq, hatk_eq] at hlt ⊢
    have hnt1 : t ∉ T1 := fun ht1 => by linarith [hcQ_T1 t ht1]
    have h := hqP (ePR (Sum.inr (Sum.inr (Sum.inr (Sum.inr t)))))
    rw [← eP.sum_comp, Fintype.sum_prod_type] at h
    simp only [aP, bP, Equiv.symm_apply_apply, hnt1, not_false_eq_true, true_and, ↓reduceIte] at h
    have hsum : ∑ θ : Fin g.numTypes, ∑ t' : Fin g.numTargets,
        (if t' = t then g.prior θ * ((g.defenderPayoff t).2 - (g.defenderPayoff t).1) else 0) * pQ θ t' =
        (∑ θ : Fin g.numTypes, g.prior θ * pQ θ t) * ((g.defenderPayoff t).2 - (g.defenderPayoff t).1) := by
      have h1 : ∀ θ, ∑ t' : Fin g.numTargets,
          (if t' = t then g.prior θ * ((g.defenderPayoff t).2 - (g.defenderPayoff t).1) else 0) * pQ θ t' =
          g.prior θ * pQ θ t * ((g.defenderPayoff t).2 - (g.defenderPayoff t).1) := by
        intro θ; rw [Finset.sum_eq_single t]
        · simp; ring
        · intro t' _ hne; simp [hne]
        · intro habs; exact absurd (Finset.mem_univ _) habs
      simp only [h1, ← Finset.sum_mul]
    change (∑ θ, ∑ t', (if t' = t then g.prior θ * ((g.defenderPayoff t).2 - (g.defenderPayoff t).1) else 0) * pQ θ t') ≤ lam at h
    rw [hsum] at h
    exact h
  · simp only [hcov_eq]
    have hlo := hqCV (eCVR (Sum.inr (Sum.inr (Sum.inl ()))))
    rw [← eCV.sum_comp] at hlo
    simp only [aCV, bCV, Equiv.symm_apply_apply, Fintype.sum_sum_type, neg_mul, one_mul,
      Finset.sum_neg_distrib, zero_mul, Finset.sum_const_zero, add_zero] at hlo
    change -(∑ t, cQ t) ≤ -R at hlo
    cases hmode : exactSum
    · simp only [Bool.false_eq_true, ↓reduceIte]; linarith
    · simp only [↓reduceIte]
      have hhi := hqCV (eCVR (Sum.inr (Sum.inr (Sum.inr ()))))
      rw [← eCV.sum_comp] at hhi
      simp only [aCV, bCV, hmode, ↓reduceIte, Equiv.symm_apply_apply, Fintype.sum_sum_type,
        one_mul, zero_mul, Finset.sum_const_zero, add_zero] at hhi
      change ∑ t, cQ t ≤ R at hhi
      linarith

/-- Polynomial bit-bound `p` for `H2`: `p(L) = 10 * (L + 1)^4`. -/
noncomputable def polyBound : Polynomial ℕ :=
  10 * (Polynomial.X + 1) ^ 4

lemma polyBound_eval (L : ℕ) : polyBound.eval L = 10 * (L + 1) ^ 4 := by
  simp [polyBound]

/-- Core Cramer rationality theorem for the supremum threshold `q` when `0 < g.1`. -/
lemma exists_rational_sup_threshold (g : GameInput) (hg : g.Valid) (hr : 0 < g.1) :
    let L := (BitstringEncoding.bitEncode g).length
    let M : ℕ := 2 ^ polyBound.eval L
    ∃ q : ℚ,
      0 ≤ q ∧ q ≤ (M : ℚ) ∧ q.den ≤ M ∧
      (∃ c p, (ofGame g hg).IsEq (q : ℝ) c p ∧ (g.1 : ℝ) ≤ ∑ t, c t) ∧
      ∀ (lam : ℝ) (c : Fin g.numTargets → ℝ) (p : Fin g.numTypes → Fin g.numTargets → ℝ),
        (ofGame g hg).IsEq lam c p → (g.1 : ℝ) ≤ ∑ t, c t → lam ≤ (q : ℝ) := by
  classical
  intro L M
  let G := ofGame g hg
  obtain ⟨hn_le, hm_le, hDprior_le, hd_bd⟩ := gameInput_bitEncode_bounds g
  -- Common denominator for all priors
  let Dprior : ℕ := ∏ θ : Fin g.numTypes, (g.prior θ).den
  have hDprior_pos : 0 < Dprior := Finset.prod_pos fun θ _ => (g.prior θ).den_pos
  -- Upper bound on defender gain differences `d_t`
  have hd_le_2pow : ∀ t : Fin g.numTargets, G.d t ≤ (2 ^ (2 * L) : ℚ) := by
    intro t
    have hdt_nn : 0 ≤ (g.defenderPayoff t).2 - (g.defenderPayoff t).1 :=
      sub_nonneg.mpr (hg.2.2.2.1 t)
    have hnum := (hd_bd t).2
    have hq_le : (g.defenderPayoff t).2 - (g.defenderPayoff t).1 ≤ (2 ^ (2 * L) : ℚ) := by
      rw [← Rat.num_div_den ((g.defenderPayoff t).2 - (g.defenderPayoff t).1)]
      have hden1 : (1 : ℚ) ≤ (((g.defenderPayoff t).2 - (g.defenderPayoff t).1).den : ℚ) := by
        exact_mod_cast ((g.defenderPayoff t).2 - (g.defenderPayoff t).1).den_pos
      have hnum_le : (((g.defenderPayoff t).2 - (g.defenderPayoff t).1).num : ℚ) ≤ (2 ^ (2 * L) : ℚ) := by
        have h1 : (((g.defenderPayoff t).2 - (g.defenderPayoff t).1).num : ℚ) ≤
            (((g.defenderPayoff t).2 - (g.defenderPayoff t).1).num.natAbs : ℚ) := by
          simpa using (Int.cast_le (R := ℚ)).mpr
            (Int.le_natAbs (a := ((g.defenderPayoff t).2 - (g.defenderPayoff t).1).num))
        have h2 : (((g.defenderPayoff t).2 - (g.defenderPayoff t).1).num.natAbs : ℚ) ≤ (2 ^ (2 * L) : ℚ) := by
          exact_mod_cast hnum
        exact le_trans h1 h2
      have hden_pos : (0 : ℚ) < (((g.defenderPayoff t).2 - (g.defenderPayoff t).1).den : ℚ) := by
        exact_mod_cast ((g.defenderPayoff t).2 - (g.defenderPayoff t).1).den_pos
      have hpow_nn : (0 : ℚ) ≤ 2 ^ (2 * L) := by positivity
      rw [div_le_iff₀ hden_pos]
      nlinarith
    simp only [G, ofGame]; exact_mod_cast hq_le
  -- Bound on `∑ t, G.d t`
  have hsumd_le_M : (∑ t, G.d t) ≤ (M : ℝ) := by
    have h1 : ∑ t : Fin g.numTargets, G.d t ≤ (g.numTargets : ℝ) * (2 ^ (2 * L) : ℝ) := by
      calc ∑ t : Fin g.numTargets, G.d t
          ≤ ∑ _t : Fin g.numTargets, ((2 ^ (2 * L) : ℚ) : ℝ) :=
              Finset.sum_le_sum fun t _ => hd_le_2pow t
        _ = (g.numTargets : ℝ) * (2 ^ (2 * L) : ℝ) := by simp
    have h2 : g.numTargets * 2 ^ (2 * L) ≤ M := by
      have hn2 : g.numTargets ≤ 2 ^ L := le_trans hn_le (Nat.le_of_lt Nat.lt_two_pow_self)
      calc g.numTargets * 2 ^ (2 * L)
          ≤ 2 ^ L * 2 ^ (2 * L) := Nat.mul_le_mul_right _ hn2
        _ = 2 ^ (3 * L) := by rw [← pow_add]; congr 1; omega
        _ ≤ 2 ^ polyBound.eval L := by
            refine Nat.pow_le_pow_right (by norm_num) ?_
            rw [polyBound_eval]
            have : L ≤ (L + 1) ^ 4 := le_trans (Nat.le_succ L)
              (Nat.le_self_pow (by norm_num) (L + 1))
            omega
    have h3 : (g.numTargets : ℝ) * (2 ^ (2 * L) : ℝ) ≤ (M : ℝ) := by exact_mod_cast h2
    linarith
  -- Enumerate finite active-set tuples `cfg = (T0, T1, B)`
  let Cfg := Finset (Fin g.numTargets) × Finset (Fin g.numTargets) ×
    (Fin g.numTypes → Finset (Fin g.numTargets))
  -- A configuration `cfg = (T0, T1, B)` is `c`-feasible if `∃ c, ...`
  let cFeas (cfg : Cfg) : Prop :=
    ∃ c : Fin g.numTargets → ℝ,
      (∀ t, 0 ≤ c t ∧ c t ≤ 1) ∧ (g.1 : ℝ) ≤ ∑ t, c t ∧
      (∀ t ∈ cfg.1, c t = 0) ∧ (∀ t ∈ cfg.2.1, c t = 1) ∧
      (∀ θ t, t ∈ cfg.2.2 θ → G.uA c θ t = G.maxUtil c θ)
  let pFeas (cfg : Cfg) (lam : ℝ) (p : Fin g.numTypes → Fin g.numTargets → ℝ) : Prop :=
    0 ≤ lam ∧ G.IsAtkProfile p ∧
    (∀ θ t, t ∉ cfg.2.2 θ → p θ t = 0) ∧
    (∀ t, t ∉ cfg.1 → lam ≤ G.gain p t) ∧
    (∀ t, t ∉ cfg.2.1 → G.gain p t ≤ lam)
  -- For any `cfg` with `cFeas cfg` and `∃ lam p, pFeas cfg lam p`, apply `polytope_max_cramer`!
  let k : ℕ := g.numTypes * g.numTargets + 1
  let eVar : (Fin g.numTypes × Fin g.numTargets) ⊕ Unit ≃ Fin k :=
    (Equiv.sumCongr finProdFinEquiv (Equiv.equivPUnit (Fin 1)).symm).trans finSumFinEquiv
  let coord : Fin k := eVar (Sum.inr ())
  -- Integer entry bound `Bint = 2 ^ (4 * L)` for the cleared `(p, lam)` integer matrix!
  let Bint : ℕ := 2 ^ (4 * L)
  have hcramer_bound_le_M : Nat.factorial k * Bint ^ k ≤ M := by
    have hk_le : k ≤ (L + 1) ^ 2 := by
      dsimp only [k]
      have hmn : g.numTypes * g.numTargets ≤ L * L := Nat.mul_le_mul hm_le hn_le
      nlinarith
    have hfac : Nat.factorial k ≤ 2 ^ (k * k) := by
      calc Nat.factorial k ≤ k ^ k := Nat.factorial_le_pow k
        _ ≤ (2 ^ k) ^ k := Nat.pow_le_pow_left (Nat.le_of_lt Nat.lt_two_pow_self) k
        _ = 2 ^ (k * k) := (pow_mul 2 k k).symm
    calc Nat.factorial k * Bint ^ k
        ≤ 2 ^ (k * k) * (2 ^ (4 * L)) ^ k := Nat.mul_le_mul hfac le_rfl
      _ = 2 ^ (k * k + 4 * L * k) := by rw [← pow_mul, ← pow_add]
      _ ≤ 2 ^ polyBound.eval L := by
          refine Nat.pow_le_pow_right (by norm_num) ?_
          rw [polyBound_eval]
          have h1 : k * k ≤ (L + 1) ^ 4 := by
            calc k * k ≤ (L + 1) ^ 2 * (L + 1) ^ 2 := Nat.mul_le_mul hk_le hk_le
              _ = (L + 1) ^ 4 := by ring
          have h2 : 4 * L * k ≤ 4 * (L + 1) ^ 4 := by
            have hL1 : L ≤ (L + 1) ^ 2 := by nlinarith
            calc 4 * L * k ≤ 4 * (L + 1) ^ 2 * (L + 1) ^ 2 :=
                  Nat.mul_le_mul (Nat.mul_le_mul_left 4 hL1) hk_le
              _ = 4 * (L + 1) ^ 4 := by ring
          omega
  -- Per-configuration Cramer optimum lemma
  have hcfg_opt : ∀ cfg : Cfg, cFeas cfg → (∃ lam p, pFeas cfg lam p) →
      ∃ q : ℚ, 0 ≤ q ∧ (q : ℝ) ≤ ∑ t, G.d t ∧ q.den ≤ M ∧
        (∃ p, pFeas cfg (q : ℝ) p) ∧ (∀ lam p, pFeas cfg lam p → lam ≤ (q : ℝ)) := by
    intro cfg hcF hpF
    -- Since `cFeas cfg` and `0 < g.1`, there is some target `t_nz ∉ cfg.1`!
    have htnz : ∃ t, t ∉ cfg.1 := by
      obtain ⟨c, hc_bnds, hc_sum, hc_T0, _, _⟩ := hcF
      by_contra hall; push Not at hall
      have h0 : ∑ t, c t = 0 := Finset.sum_eq_zero fun t _ => hc_T0 t (hall t)
      have hr_pos : (0 : ℝ) < (g.1 : ℝ) := by exact_mod_cast hr
      linarith
    -- Build the cleared integer matrix `A` and RHS `b` for `pFeas cfg lam p`!
    let PRow := Unit ⊕ (Fin g.numTypes × Fin g.numTargets) ⊕ (Fin g.numTypes × Fin g.numTargets) ⊕
      (Fin g.numTypes ⊕ Fin g.numTypes) ⊕ (Fin g.numTargets ⊕ Fin g.numTargets)
    let eR := Fintype.equivFin PRow
    -- For target `t`, scale row by `Drow t = Dprior * d_t.den`
    let dtQ (t : Fin g.numTargets) : ℚ := (g.defenderPayoff t).2 - (g.defenderPayoff t).1
    let Drow (t : Fin g.numTargets) : ℕ := Dprior * (dtQ t).den
    have hDrow_pos : ∀ t, 0 < Drow t := fun t => Nat.mul_pos hDprior_pos (dtQ t).den_pos
    -- Integer coefficient of `p_{θ, t}` in `Drow t * gain(p, t)`:
    -- `(Dprior / (g.prior θ).den) * (g.prior θ).num * (dtQ t).num`
    let coeffZ (θ : Fin g.numTypes) (t : Fin g.numTargets) : ℤ :=
      ((Dprior / (g.prior θ).den : ℕ) : ℤ) * (g.prior θ).num * (dtQ t).num
    have hcoeffZ_cast : ∀ θ t, (coeffZ θ t : ℝ) = (Drow t : ℝ) * (G.π θ * G.d t) := by
      intro θ t
      have hdvd : (g.prior θ).den ∣ Dprior :=
        Finset.dvd_prod_of_mem (fun θ' => (g.prior θ').den) (Finset.mem_univ θ)
      have hmul_div : ((Dprior / (g.prior θ).den : ℕ) : ℝ) * ((g.prior θ).den : ℝ) = (Dprior : ℝ) := by
        exact_mod_cast Nat.div_mul_cancel hdvd
      have hπ_eq : G.π θ = ((g.prior θ).num : ℝ) / ((g.prior θ).den : ℝ) := by
        simp only [G, ofGame, Rat.cast_def]
      have hd_eq : G.d t = ((dtQ t).num : ℝ) / ((dtQ t).den : ℝ) := by
        simp only [G, ofGame, dtQ, Rat.cast_def]
      have h1 : ((g.prior θ).den : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (g.prior θ).den_nz
      have h2 : ((dtQ t).den : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (dtQ t).den_nz
      simp only [coeffZ, Drow, Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
      rw [hπ_eq, hd_eq]
      field_simp [h1, h2]
      calc ((Dprior / (g.prior θ).den : ℕ) : ℝ) * ((g.prior θ).num : ℝ) * ((dtQ t).num : ℝ) *
            ((g.prior θ).den : ℝ)
          = (((Dprior / (g.prior θ).den : ℕ) : ℝ) * ((g.prior θ).den : ℝ)) *
            ((g.prior θ).num : ℝ) * ((dtQ t).num : ℝ) := by ring
        _ = ((g.prior θ).num : ℝ) * ((dtQ t).num : ℝ) * (Dprior : ℝ) := by
            rw [hmul_div]; ring
    have hDrow_le : ∀ t, Drow t ≤ Bint := fun t => by
      calc Drow t = Dprior * (dtQ t).den := rfl
        _ ≤ 2 ^ L * 2 ^ L := Nat.mul_le_mul hDprior_le (hd_bd t).1
        _ = 2 ^ (2 * L) := by rw [← pow_add]; congr 1; omega
        _ ≤ 2 ^ (4 * L) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hcoeffZ_le : ∀ θ t, (coeffZ θ t).natAbs ≤ Bint := fun θ t => by
      have hπ_le1 : g.prior θ ≤ 1 := by
        have := Finset.single_le_sum (fun θ' _ => (hg.2.2.2.2 θ').1) (Finset.mem_univ θ)
        linarith [hg.2.2.1]
      have hnum_le_den : (g.prior θ).num.natAbs ≤ (g.prior θ).den := by
        have hnn : 0 ≤ (g.prior θ).num := Rat.num_nonneg.mpr (hg.2.2.2.2 θ).1
        have h1 : ((g.prior θ).num : ℚ) ≤ ((g.prior θ).den : ℚ) := by
          have hpos : (0 : ℚ) < ((g.prior θ).den : ℚ) := Nat.cast_pos.mpr (g.prior θ).den_pos
          have := (div_le_one hpos).mp (by rwa [Rat.num_div_den])
          exact this
        have h2 : (g.prior θ).num ≤ ((g.prior θ).den : ℤ) := by exact_mod_cast h1
        omega
      have hprod1 : (Dprior / (g.prior θ).den) * (g.prior θ).num.natAbs ≤ Dprior := by
        have hdvd : (g.prior θ).den ∣ Dprior :=
          Finset.dvd_prod_of_mem (fun θ' => (g.prior θ').den) (Finset.mem_univ θ)
        calc (Dprior / (g.prior θ).den) * (g.prior θ).num.natAbs
            ≤ (Dprior / (g.prior θ).den) * (g.prior θ).den := Nat.mul_le_mul_left _ hnum_le_den
          _ = Dprior := Nat.div_mul_cancel hdvd
      simp only [coeffZ, Int.natAbs_mul, Int.natAbs_natCast]
      calc Dprior / (g.prior θ).den * (g.prior θ).num.natAbs * (dtQ t).num.natAbs
          ≤ Dprior * (dtQ t).num.natAbs := Nat.mul_le_mul_right _ hprod1
        _ ≤ 2 ^ L * 2 ^ (2 * L) := Nat.mul_le_mul hDprior_le (hd_bd t).2
        _ = 2 ^ (3 * L) := by rw [← pow_add]; congr 1; omega
        _ ≤ 2 ^ (4 * L) := Nat.pow_le_pow_right (by norm_num) (by omega)
    let A : Matrix (Fin (Fintype.card PRow)) (Fin k) ℤ := fun r col =>
      match eR.symm r, eVar.symm col with
      | Sum.inl (), Sum.inr () => -1
      | Sum.inl (), Sum.inl _ => 0
      | Sum.inr (Sum.inl (θ, t)), Sum.inl (θ', t') => if θ' = θ ∧ t' = t then -1 else 0
      | Sum.inr (Sum.inl _), Sum.inr () => 0
      | Sum.inr (Sum.inr (Sum.inl (θ, t))), Sum.inl (θ', t') =>
          if t ∉ cfg.2.2 θ ∧ θ' = θ ∧ t' = t then 1 else 0
      | Sum.inr (Sum.inr (Sum.inl _)), Sum.inr () => 0
      | Sum.inr (Sum.inr (Sum.inr (Sum.inl (Sum.inl θ)))), Sum.inl (θ', _) =>
          if θ' = θ then 1 else 0
      | Sum.inr (Sum.inr (Sum.inr (Sum.inl (Sum.inl _)))), Sum.inr () => 0
      | Sum.inr (Sum.inr (Sum.inr (Sum.inl (Sum.inr θ)))), Sum.inl (θ', _) =>
          if θ' = θ then -1 else 0
      | Sum.inr (Sum.inr (Sum.inr (Sum.inl (Sum.inr _)))), Sum.inr () => 0
      | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl t)))), Sum.inl (θ', t') =>
          if t ∉ cfg.1 ∧ t' = t then -coeffZ θ' t else 0
      | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl t)))), Sum.inr () =>
          if t ∉ cfg.1 then (Drow t : ℤ) else 0
      | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr t)))), Sum.inl (θ', t') =>
          if t ∉ cfg.2.1 ∧ t' = t then coeffZ θ' t else 0
      | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr t)))), Sum.inr () =>
          if t ∉ cfg.2.1 then -(Drow t : ℤ) else 0
    let b : Fin (Fintype.card PRow) → ℤ := fun r =>
      match eR.symm r with
      | Sum.inl () => 0
      | Sum.inr (Sum.inl _) => 0
      | Sum.inr (Sum.inr (Sum.inl _)) => 0
      | Sum.inr (Sum.inr (Sum.inr (Sum.inl (Sum.inl _)))) => 1
      | Sum.inr (Sum.inr (Sum.inr (Sum.inl (Sum.inr _)))) => -1
      | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl _)))) => 0
      | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr _)))) => 0
    have hA_bd : ∀ r col, (A r col).natAbs ≤ Bint := by
      intro r col
      have h1_le : 1 ≤ Bint := Nat.one_le_pow _ _ (by norm_num)
      dsimp only [A]
      generalize eR.symm r = rr
      generalize eVar.symm col = cc
      rcases rr with ⟨⟩ | ⟨θ, t⟩ | ⟨θ, t⟩ | (θ | θ) | (t | t) <;>
        rcases cc with ⟨θ', t'⟩ | ⟨⟩ <;> dsimp only
      · simp
      · simp [h1_le]
      · split_ifs <;> simp [h1_le]
      · simp
      · split_ifs <;> simp [h1_le]
      · simp
      · split_ifs <;> simp [h1_le]
      · simp
      · split_ifs <;> simp [h1_le]
      · simp
      · split_ifs <;> simp [hcoeffZ_le θ' t]
      · split_ifs <;> simp [hDrow_le t]
      · split_ifs <;> simp [hcoeffZ_le θ' t]
      · split_ifs <;> simp [hDrow_le t]
    -- Equivalence between `A x ≤ b` and `pFeas cfg (x coord) (fun θ t => x (eVar (Sum.inl (θ, t))))`
    have hiff : ∀ x : Fin k → ℝ,
        (∀ r, ∑ col, (A r col : ℝ) * x col ≤ (b r : ℝ)) ↔
        pFeas cfg (x coord) (fun θ t => x (eVar (Sum.inl (θ, t)))) := by
      intro x
      constructor
      · intro hx
        have hlam0 : 0 ≤ x coord := by
          have h := hx (eR (Sum.inl ()))
          rw [← eVar.sum_comp] at h
          simp only [A, b, Equiv.symm_apply_apply, Fintype.sum_sum_type, Int.cast_zero, zero_mul,
            Finset.sum_const_zero, zero_add, Fintype.sum_unique, Int.cast_neg, Int.cast_one,
            neg_mul, one_mul] at h
          linarith
        have hpnn : ∀ θ t, 0 ≤ x (eVar (Sum.inl (θ, t))) := by
          intro θ t
          have h := hx (eR (Sum.inr (Sum.inl (θ, t))))
          rw [← eVar.sum_comp] at h
          simp only [A, b, Equiv.symm_apply_apply, Fintype.sum_sum_type, Int.cast_zero, zero_mul,
            Fintype.sum_unique, add_zero] at h
          rw [Finset.sum_eq_single (θ, t)] at h
          · simp only [and_self, ↓reduceIte, Int.cast_neg, Int.cast_one, neg_mul, one_mul] at h
            linarith
          · intro q _ hne
            have : ¬ (q.1 = θ ∧ q.2 = t) := fun ⟨h1, h2⟩ => hne (Prod.ext h1 h2)
            simp [this]
          · intro habs; exact absurd (Finset.mem_univ _) habs
        refine ⟨hlam0, fun θ => ⟨?_, hpnn θ⟩, ?_, ?_, ?_⟩
        · have h1 := hx (eR (Sum.inr (Sum.inr (Sum.inr (Sum.inl (Sum.inl θ))))))
          have h2 := hx (eR (Sum.inr (Sum.inr (Sum.inr (Sum.inl (Sum.inr θ))))))
          rw [← eVar.sum_comp] at h1 h2
          simp only [A, b, Equiv.symm_apply_apply, Fintype.sum_sum_type, Int.cast_zero, zero_mul,
            Fintype.sum_unique, add_zero, Int.cast_one, Int.cast_neg, Fintype.sum_prod_type] at h1 h2
          rw [Finset.sum_eq_single θ] at h1 h2
          · simp only [↓reduceIte, Int.cast_one, one_mul, Int.cast_neg, neg_mul,
              Finset.sum_neg_distrib] at h1 h2
            linarith
          · intro θ' _ hne; simp [hne]
          · intro habs; exact absurd (Finset.mem_univ _) habs
          · intro θ' _ hne; simp [hne]
          · intro habs; exact absurd (Finset.mem_univ _) habs
        · intro θ t hntB
          have h := hx (eR (Sum.inr (Sum.inr (Sum.inl (θ, t)))))
          rw [← eVar.sum_comp] at h
          simp only [A, b, Equiv.symm_apply_apply, Fintype.sum_sum_type, Int.cast_zero, zero_mul,
            Fintype.sum_unique, add_zero, hntB, not_false_eq_true, true_and] at h
          rw [Finset.sum_eq_single (θ, t)] at h
          · simp only [and_self, ↓reduceIte, Int.cast_one, one_mul] at h
            linarith [hpnn θ t]
          · intro q _ hne
            have : ¬ (q.1 = θ ∧ q.2 = t) := fun ⟨h1, h2⟩ => hne (Prod.ext h1 h2)
            simp [this]
          · intro habs; exact absurd (Finset.mem_univ _) habs
        · intro t hnt0
          have h := hx (eR (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl t))))))
          rw [← eVar.sum_comp] at h
          simp only [A, b, Equiv.symm_apply_apply, Fintype.sum_sum_type, hnt0, not_false_eq_true,
            true_and, ↓reduceIte, Fintype.sum_unique, Int.cast_natCast, Int.cast_zero,
            Fintype.sum_prod_type] at h
          have hsum : ∑ θ : Fin g.numTypes, ∑ t' : Fin g.numTargets,
              ((if t' = t then -coeffZ θ t else 0 : ℤ) : ℝ) * x (eVar (Sum.inl (θ, t'))) =
              -(Drow t : ℝ) * G.gain (fun θ t => x (eVar (Sum.inl (θ, t)))) t := by
            have h1 : ∀ θ, ∑ t' : Fin g.numTargets,
                ((if t' = t then -coeffZ θ t else 0 : ℤ) : ℝ) * x (eVar (Sum.inl (θ, t'))) =
                -(Drow t : ℝ) * (G.π θ * x (eVar (Sum.inl (θ, t))) * G.d t) := by
              intro θ; rw [Finset.sum_eq_single t]
              · simp only [↓reduceIte, Int.cast_neg, hcoeffZ_cast θ t]; ring
              · intro t' _ hne; simp [hne]
              · intro habs; exact absurd (Finset.mem_univ _) habs
            simp only [h1, ← Finset.mul_sum, ← Finset.sum_mul, RealGame.gain]
          rw [hsum] at h
          have hDp : (0 : ℝ) < (Drow t : ℝ) := Nat.cast_pos.mpr (hDrow_pos t)
          nlinarith
        · intro t hnt1
          have h := hx (eR (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr t))))))
          rw [← eVar.sum_comp] at h
          simp only [A, b, Equiv.symm_apply_apply, Fintype.sum_sum_type, hnt1, not_false_eq_true,
            true_and, ↓reduceIte, Fintype.sum_unique, Int.cast_neg, Int.cast_natCast,
            Int.cast_zero, Fintype.sum_prod_type] at h
          have hsum : ∑ θ : Fin g.numTypes, ∑ t' : Fin g.numTargets,
              ((if t' = t then coeffZ θ t else 0 : ℤ) : ℝ) * x (eVar (Sum.inl (θ, t'))) =
              (Drow t : ℝ) * G.gain (fun θ t => x (eVar (Sum.inl (θ, t)))) t := by
            have h1 : ∀ θ, ∑ t' : Fin g.numTargets,
                ((if t' = t then coeffZ θ t else 0 : ℤ) : ℝ) * x (eVar (Sum.inl (θ, t'))) =
                (Drow t : ℝ) * (G.π θ * x (eVar (Sum.inl (θ, t))) * G.d t) := by
              intro θ; rw [Finset.sum_eq_single t]
              · simp only [↓reduceIte, hcoeffZ_cast θ t]; ring
              · intro t' _ hne; simp [hne]
              · intro habs; exact absurd (Finset.mem_univ _) habs
            simp only [h1, ← Finset.mul_sum, ← Finset.sum_mul, RealGame.gain]
          rw [hsum] at h
          have hDp : (0 : ℝ) < (Drow t : ℝ) := Nat.cast_pos.mpr (hDrow_pos t)
          nlinarith
      · intro hpf r
        rw [← eVar.sum_comp]
        simp only [Fintype.sum_sum_type]
        match hr : eR.symm r with
        | Sum.inl () =>
          simp only [A, b, hr, Equiv.symm_apply_apply, Int.cast_zero, zero_mul,
            Finset.sum_const_zero, zero_add, Fintype.sum_unique, Int.cast_neg, Int.cast_one,
            neg_mul, one_mul]
          linarith [hpf.1]
        | Sum.inr (Sum.inl (θ, t)) =>
          simp only [A, b, hr, Equiv.symm_apply_apply, Int.cast_zero, zero_mul,
            Fintype.sum_unique, add_zero]
          rw [Finset.sum_eq_single (θ, t)]
          · simp; linarith [(hpf.2.1 θ).2 t]
          · intro q _ hne
            have : ¬ (q.1 = θ ∧ q.2 = t) := fun ⟨h1, h2⟩ => hne (Prod.ext h1 h2)
            simp [this]
          · intro habs; exact absurd (Finset.mem_univ _) habs
        | Sum.inr (Sum.inr (Sum.inl (θ, t))) =>
          simp only [A, b, hr, Equiv.symm_apply_apply, Int.cast_zero, zero_mul,
            Fintype.sum_unique, add_zero]
          by_cases htB : t ∈ cfg.2.2 θ
          · simp [htB]
          · simp only [htB, not_false_eq_true, true_and]
            rw [Finset.sum_eq_single (θ, t)]
            · simp [hpf.2.2.1 θ t htB]
            · intro q _ hne
              have : ¬ (q.1 = θ ∧ q.2 = t) := fun ⟨h1, h2⟩ => hne (Prod.ext h1 h2)
              simp [this]
            · intro habs; exact absurd (Finset.mem_univ _) habs
        | Sum.inr (Sum.inr (Sum.inr (Sum.inl (Sum.inl θ)))) =>
          simp only [A, b, hr, Equiv.symm_apply_apply, Int.cast_zero, zero_mul,
            Fintype.sum_unique, add_zero, Int.cast_one, Fintype.sum_prod_type]
          rw [Finset.sum_eq_single θ]
          · simp [(hpf.2.1 θ).1]
          · intro θ' _ hne; simp [hne]
          · intro habs; exact absurd (Finset.mem_univ _) habs
        | Sum.inr (Sum.inr (Sum.inr (Sum.inl (Sum.inr θ)))) =>
          simp only [A, b, hr, Equiv.symm_apply_apply, Int.cast_zero, zero_mul,
            Fintype.sum_unique, add_zero, Int.cast_neg, Int.cast_one, Fintype.sum_prod_type]
          rw [Finset.sum_eq_single θ]
          · simp [(hpf.2.1 θ).1]
          · intro θ' _ hne; simp [hne]
          · intro habs; exact absurd (Finset.mem_univ _) habs
        | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl t)))) =>
          simp only [A, b, hr, Equiv.symm_apply_apply, Int.cast_zero, Fintype.sum_unique,
            Fintype.sum_prod_type]
          by_cases ht0 : t ∈ cfg.1
          · simp [ht0]
          · simp only [ht0, not_false_eq_true, true_and, ↓reduceIte, Int.cast_natCast]
            have hsum : ∑ θ : Fin g.numTypes, ∑ t' : Fin g.numTargets,
                ((if t' = t then -coeffZ θ t else 0 : ℤ) : ℝ) * x (eVar (Sum.inl (θ, t'))) =
                -(Drow t : ℝ) * G.gain (fun θ t => x (eVar (Sum.inl (θ, t)))) t := by
              have h1 : ∀ θ, ∑ t' : Fin g.numTargets,
                  ((if t' = t then -coeffZ θ t else 0 : ℤ) : ℝ) * x (eVar (Sum.inl (θ, t'))) =
                  -(Drow t : ℝ) * (G.π θ * x (eVar (Sum.inl (θ, t))) * G.d t) := by
                intro θ; rw [Finset.sum_eq_single t]
                · simp only [↓reduceIte, Int.cast_neg, hcoeffZ_cast θ t]; ring
                · intro t' _ hne; simp [hne]
                · intro habs; exact absurd (Finset.mem_univ _) habs
              simp only [h1, ← Finset.mul_sum, ← Finset.sum_mul, RealGame.gain]
            rw [hsum]
            have hDp : (0 : ℝ) < (Drow t : ℝ) := Nat.cast_pos.mpr (hDrow_pos t)
            nlinarith [hpf.2.2.2.1 t ht0]
        | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr t)))) =>
          simp only [A, b, hr, Equiv.symm_apply_apply, Int.cast_zero, Fintype.sum_unique,
            Fintype.sum_prod_type]
          by_cases ht1 : t ∈ cfg.2.1
          · simp [ht1]
          · simp only [ht1, not_false_eq_true, true_and, ↓reduceIte, Int.cast_neg, Int.cast_natCast]
            have hsum : ∑ θ : Fin g.numTypes, ∑ t' : Fin g.numTargets,
                ((if t' = t then coeffZ θ t else 0 : ℤ) : ℝ) * x (eVar (Sum.inl (θ, t'))) =
                (Drow t : ℝ) * G.gain (fun θ t => x (eVar (Sum.inl (θ, t)))) t := by
              have h1 : ∀ θ, ∑ t' : Fin g.numTargets,
                  ((if t' = t then coeffZ θ t else 0 : ℤ) : ℝ) * x (eVar (Sum.inl (θ, t'))) =
                  (Drow t : ℝ) * (G.π θ * x (eVar (Sum.inl (θ, t))) * G.d t) := by
                intro θ; rw [Finset.sum_eq_single t]
                · simp only [↓reduceIte, hcoeffZ_cast θ t]; ring
                · intro t' _ hne; simp [hne]
                · intro habs; exact absurd (Finset.mem_univ _) habs
              simp only [h1, ← Finset.mul_sum, ← Finset.sum_mul, RealGame.gain]
            rw [hsum]
            have hDp : (0 : ℝ) < (Drow t : ℝ) := Nat.cast_pos.mpr (hDrow_pos t)
            nlinarith [hpf.2.2.2.2 t ht1]
    have hP_ne : ∃ x : Fin k → ℝ, ∀ r, ∑ col, (A r col : ℝ) * x col ≤ (b r : ℝ) := by
      obtain ⟨lam, p, hpf⟩ := hpF
      let x : Fin k → ℝ := fun col =>
        match eVar.symm col with
        | Sum.inl (θ, t) => p θ t
        | Sum.inr () => lam
      refine ⟨x, (hiff x).mpr ?_⟩
      simpa [x, coord] using hpf
    have hP_bdd : ∀ x : Fin k → ℝ, (∀ r, ∑ col, (A r col : ℝ) * x col ≤ (b r : ℝ)) →
        ∀ col, |x col| ≤ (∑ t, G.d t) + 1 := by
      intro x hx col
      have hpf := (hiff x).mp hx
      have hsumd_nn : 0 ≤ ∑ t, G.d t := Finset.sum_nonneg fun t _ => G.hd_nn t
      cases hcol : eVar.symm col with
      | inl q =>
        have hcol_eq : col = eVar (Sum.inl q) := by rw [← hcol, Equiv.apply_symm_apply]
        rw [hcol_eq, abs_of_nonneg ((hpf.2.1 q.1).2 q.2)]
        have hle1 : x (eVar (Sum.inl q)) ≤ 1 := by
          have := Finset.single_le_sum (f := fun t' : Fin g.numTargets => x (eVar (Sum.inl (q.1, t')))) (fun t' _ => (hpf.2.1 q.1).2 t') (Finset.mem_univ q.2)
          linarith [(hpf.2.1 q.1).1]
        linarith
      | inr u =>
        cases u
        have hcol_eq : col = coord := by dsimp only [coord]; rw [← hcol, Equiv.apply_symm_apply]
        rw [hcol_eq, abs_of_nonneg hpf.1]
        obtain ⟨t0, ht0⟩ := htnz
        have h1 : x coord ≤ G.gain (fun θ t => x (eVar (Sum.inl (θ, t)))) t0 := hpf.2.2.2.1 t0 ht0
        have h2 : ∑ θ, G.π θ * x (eVar (Sum.inl (θ, t0))) ≤ 1 := by
          calc ∑ θ, G.π θ * x (eVar (Sum.inl (θ, t0)))
              ≤ ∑ θ, G.π θ * 1 := Finset.sum_le_sum fun θ _ =>
                  mul_le_mul_of_nonneg_left (by
                    have := Finset.single_le_sum (f := fun t' : Fin g.numTargets => x (eVar (Sum.inl (θ, t')))) (fun t' _ => (hpf.2.1 θ).2 t') (Finset.mem_univ t0)
                    linarith [(hpf.2.1 θ).1]) (G.hπ_nn θ)
            _ = 1 := by simp [G.hπ_sum]
        have h3 : G.gain (fun θ t => x (eVar (Sum.inl (θ, t)))) t0 ≤ G.d t0 := by
          dsimp only [RealGame.gain]; nlinarith [G.hd_nn t0]
        have h4 : G.d t0 ≤ ∑ t, G.d t := Finset.single_le_sum (fun t _ => G.hd_nn t) (Finset.mem_univ t0)
        linarith
    obtain ⟨q, ⟨xstar, hxstar, hxstar_eq⟩, hq_max, hq_den⟩ :=
      polytope_max_cramer A b coord Bint hA_bd ((∑ t, G.d t) + 1) hP_ne hP_bdd
    have hpf_star := (hiff xstar).mp hxstar
    rw [hxstar_eq] at hpf_star
    have hq_le_sumd : (q : ℝ) ≤ ∑ t, G.d t := by
      obtain ⟨t0, ht0⟩ := htnz
      have h1 : (q : ℝ) ≤ G.gain (fun θ t => xstar (eVar (Sum.inl (θ, t)))) t0 := hpf_star.2.2.2.1 t0 ht0
      have h2 : ∑ θ, G.π θ * xstar (eVar (Sum.inl (θ, t0))) ≤ 1 := by
        calc ∑ θ, G.π θ * xstar (eVar (Sum.inl (θ, t0)))
            ≤ ∑ θ, G.π θ * 1 := Finset.sum_le_sum fun θ _ =>
                mul_le_mul_of_nonneg_left (by
                  have := Finset.single_le_sum (f := fun t' : Fin g.numTargets => xstar (eVar (Sum.inl (θ, t')))) (fun t' _ => (hpf_star.2.1 θ).2 t') (Finset.mem_univ t0)
                  linarith [(hpf_star.2.1 θ).1]) (G.hπ_nn θ)
          _ = 1 := by simp [G.hπ_sum]
      have h3 : G.gain (fun θ t => xstar (eVar (Sum.inl (θ, t)))) t0 ≤ G.d t0 := by
        dsimp only [RealGame.gain]; nlinarith [G.hd_nn t0]
      have h4 : G.d t0 ≤ ∑ t, G.d t := Finset.single_le_sum (fun t _ => G.hd_nn t) (Finset.mem_univ t0)
      linarith
    refine ⟨q, by exact_mod_cast hpf_star.1, hq_le_sumd, le_trans hq_den hcramer_bound_le_M,
      ⟨fun θ t => xstar (eVar (Sum.inl (θ, t))), hpf_star⟩, fun lam p hpf => ?_⟩
    let x : Fin k → ℝ := fun col =>
      match eVar.symm col with
      | Sum.inl (θ, t) => p θ t
      | Sum.inr () => lam
    have hx : ∀ r, ∑ col, (A r col : ℝ) * x col ≤ (b r : ℝ) :=
      (hiff x).mpr (by simpa [x, coord] using hpf)
    simpa [x, coord] using hq_max x hx
  -- Take the finite maximum of `q` over all feasible configurations!
  let GoodCfgs : Finset Cfg := Finset.univ.filter fun cfg => cFeas cfg ∧ ∃ lam p, pFeas cfg lam p
  -- Every equilibrium `(lam, c, p)` with `lam ≥ 0` and `∑ c ≥ g.1` belongs to some `cfg ∈ GoodCfgs`!
  have hmem_good : ∀ (lam : ℝ) (c : Fin g.numTargets → ℝ) (p : Fin g.numTypes → Fin g.numTargets → ℝ),
      0 ≤ lam → G.IsEq lam c p → (g.1 : ℝ) ≤ ∑ t, c t →
      ∃ cfg ∈ GoodCfgs, pFeas cfg lam p := by
    intro lam c p hlam0 heq hsum
    let cfg : Cfg := (Finset.univ.filter fun t => c t = 0,
      Finset.univ.filter fun t => c t = 1,
      fun θ => Finset.univ.filter fun t => G.uA c θ t = G.maxUtil c θ)
    have hcF : cFeas cfg :=
      ⟨c, heq.1.1, hsum, fun t ht => (Finset.mem_filter.mp ht).2,
        fun t ht => (Finset.mem_filter.mp ht).2, fun θ t ht => (Finset.mem_filter.mp ht).2⟩
    have hpF : pFeas cfg lam p :=
      ⟨hlam0, heq.1.2.1, fun θ t hntB => by
        by_contra hne
        have hpos : 0 < p θ t := lt_of_le_of_ne ((heq.1.2.1 θ).2 t) (Ne.symm hne)
        exact hntB (Finset.mem_filter.mpr ⟨Finset.mem_univ t,
          (G.isAtkBR_iff_maxUtil c p).mp heq.1.2.2.1 θ t hpos⟩),
      fun t hnt0 => heq.1.2.2.2 t (lt_of_le_of_ne (heq.1.1 t).1 fun h =>
        hnt0 (Finset.mem_filter.mpr ⟨Finset.mem_univ t, h.symm⟩)),
      fun t hnt1 => heq.2 t (lt_of_le_of_ne (heq.1.1 t).2 fun h =>
        hnt1 (Finset.mem_filter.mpr ⟨Finset.mem_univ t, h⟩))⟩
    exact ⟨cfg, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcF, lam, p, hpF⟩, hpF⟩
  have hGood_ne : GoodCfgs.Nonempty := by
    obtain ⟨p0, hp0⟩ := G.one_isEq_zero
    have hsum1 : (g.1 : ℝ) ≤ ∑ _t : Fin g.numTargets, (1 : ℝ) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
      exact_mod_cast hg.2.1
    obtain ⟨cfg, hcfg, _⟩ := hmem_good 0 (fun _ => 1) p0 le_rfl hp0 hsum1
    exact ⟨cfg, hcfg⟩
  have hq_cfg : ∀ cfg : {c : Cfg // c ∈ GoodCfgs},
      ∃ q : ℚ, 0 ≤ q ∧ (q : ℝ) ≤ ∑ t, G.d t ∧ q.den ≤ M ∧
        (∃ p, pFeas cfg.1 (q : ℝ) p) ∧ (∀ lam p, pFeas cfg.1 lam p → lam ≤ (q : ℝ)) :=
    fun cfg => hcfg_opt cfg.1 (Finset.mem_filter.mp cfg.2).2.1 (Finset.mem_filter.mp cfg.2).2.2
  choose qOf hqOf_nn hqOf_le hqOf_den hqOf_att hqOf_max using hq_cfg
  have hsub_ne : (Finset.univ : Finset {c : Cfg // c ∈ GoodCfgs}).Nonempty := by
    obtain ⟨cfg, hcfg⟩ := hGood_ne; exact ⟨⟨cfg, hcfg⟩, Finset.mem_univ _⟩
  obtain ⟨cfgBest, _, hcfgBest_max⟩ := Finset.univ.exists_max_image qOf hsub_ne
  let q : ℚ := qOf cfgBest
  have hq_nn : 0 ≤ q := hqOf_nn cfgBest
  have hq_leM : q ≤ (M : ℚ) := by
    have : (q : ℝ) ≤ (M : ℝ) := le_trans (hqOf_le cfgBest) hsumd_le_M
    exact_mod_cast this
  have hq_att_eq : ∃ c p, G.IsEq (q : ℝ) c p ∧ (g.1 : ℝ) ≤ ∑ t, c t := by
    obtain ⟨c, hc_bnds, hc_sum, hc_T0, hc_T1, hc_B⟩ := (Finset.mem_filter.mp cfgBest.2).2.1
    obtain ⟨p, _, hp_prof, hp_supp, hp_lo, hp_hi⟩ := hqOf_att cfgBest
    refine ⟨c, p, ⟨⟨hc_bnds, hp_prof, ?_, ?_⟩, ?_⟩, hc_sum⟩
    · rw [G.isAtkBR_iff_maxUtil]
      intro θ t hpos
      have htB : t ∈ cfgBest.1.2.2 θ := by by_contra hn; linarith [hp_supp θ t hn]
      exact hc_B θ t htB
    · intro t htpos
      exact hp_lo t fun ht0 => by linarith [hc_T0 t ht0]
    · intro t htlt
      exact hp_hi t fun ht1 => by linarith [hc_T1 t ht1]
  refine ⟨q, hq_nn, hq_leM, hqOf_den cfgBest, hq_att_eq, ?_⟩
  intro lam c p heq hsum
  by_cases hlam0 : 0 ≤ lam
  · obtain ⟨cfg, hcfg, hpf⟩ := hmem_good lam c p hlam0 heq hsum
    have h1 : lam ≤ (qOf ⟨cfg, hcfg⟩ : ℝ) := hqOf_max ⟨cfg, hcfg⟩ lam p hpf
    have h2 : qOf ⟨cfg, hcfg⟩ ≤ q := hcfgBest_max ⟨cfg, hcfg⟩ (Finset.mem_univ _)
    exact le_trans h1 (by exact_mod_cast h2)
  · linarith [show (0 : ℝ) ≤ (q : ℝ) by exact_mod_cast hq_nn]

end OMA.R2H3R1H2

theorem OMA.solution : OMA.R_Arxiv_2610_08796_exists_isPolyTime_bayesNash_R2_H3_R1.H2 := by
  refine ⟨OMA.R2H3R1H2.polyBound, fun g hg => ?_⟩
  dsimp only
  let L := (BitstringEncoding.bitEncode g).length
  let M : ℕ := 2 ^ OMA.R2H3R1H2.polyBound.eval L
  let G := OMA.R2H3R1H2.ofGame g hg
  by_cases hr : g.1 = 0
  · -- Case `g.1 = 0`: take `q = M`!
    have hM_pos : 1 ≤ M := Nat.one_le_pow _ _ (by norm_num)
    obtain ⟨hn_le, _, _, hd_bd⟩ := OMA.R2H3R1H2.gameInput_bitEncode_bounds g
    refine ⟨(M : ℚ), Nat.cast_nonneg M, le_rfl, by simpa using hM_pos, ?_, ?_⟩
    · -- At `q = M`, `cov = 0` is an exact equilibrium with `∑ cov = 0 = g.1`!
      have h0_eq : ∃ p, G.IsEq (M : ℝ) (fun _ => 0) p := by
        obtain ⟨p, hp, hbr⟩ := G.exists_pure_atkBR (fun _ => 0)
        refine ⟨p, ⟨fun _ => ⟨le_rfl, zero_le_one⟩, hp, hbr, fun _ h => absurd h (lt_irrefl 0)⟩,
          fun t _ => ?_⟩
        have h1 : ∑ θ, G.π θ * p θ t ≤ 1 := by
          calc ∑ θ, G.π θ * p θ t
              ≤ ∑ θ, G.π θ * 1 := Finset.sum_le_sum fun θ _ =>
                  mul_le_mul_of_nonneg_left (by
                    have := Finset.single_le_sum (f := fun t' : Fin g.numTargets => p θ t') (fun t' _ => (hp θ).2 t') (Finset.mem_univ t)
                    linarith [(hp θ).1]) (G.hπ_nn θ)
            _ = 1 := by simp [G.hπ_sum]
        have hdt_le : G.d t ≤ (2 ^ (2 * L) : ℝ) := by
          have hnum := (hd_bd t).2
          have hq_le : (g.defenderPayoff t).2 - (g.defenderPayoff t).1 ≤ (2 ^ (2 * L) : ℚ) := by
            rw [← Rat.num_div_den ((g.defenderPayoff t).2 - (g.defenderPayoff t).1)]
            have hden1 : (1 : ℚ) ≤ (((g.defenderPayoff t).2 - (g.defenderPayoff t).1).den : ℚ) := by
              exact_mod_cast ((g.defenderPayoff t).2 - (g.defenderPayoff t).1).den_pos
            have hnum_le : (((g.defenderPayoff t).2 - (g.defenderPayoff t).1).num : ℚ) ≤ (2 ^ (2 * L) : ℚ) := by
              have h1' : (((g.defenderPayoff t).2 - (g.defenderPayoff t).1).num : ℚ) ≤
                  (((g.defenderPayoff t).2 - (g.defenderPayoff t).1).num.natAbs : ℚ) := by
                simpa using (Int.cast_le (R := ℚ)).mpr
                  (Int.le_natAbs (a := ((g.defenderPayoff t).2 - (g.defenderPayoff t).1).num))
              have h2' : (((g.defenderPayoff t).2 - (g.defenderPayoff t).1).num.natAbs : ℚ) ≤ (2 ^ (2 * L) : ℚ) := by
                exact_mod_cast hnum
              exact le_trans h1' h2'
            have hden_pos : (0 : ℚ) < (((g.defenderPayoff t).2 - (g.defenderPayoff t).1).den : ℚ) := by
              exact_mod_cast ((g.defenderPayoff t).2 - (g.defenderPayoff t).1).den_pos
            have hpow_nn : (0 : ℚ) ≤ 2 ^ (2 * L) := by positivity
            rw [div_le_iff₀ hden_pos]
            nlinarith
          simp only [G, OMA.R2H3R1H2.ofGame]; exact_mod_cast hq_le
        have h2pow_le : (2 ^ (2 * L) : ℝ) ≤ (M : ℝ) := by
          have hnat : 2 ^ (2 * L) ≤ M := by
            refine Nat.pow_le_pow_right (by norm_num) ?_
            rw [OMA.R2H3R1H2.polyBound_eval]
            have : L ≤ (L + 1) ^ 4 := le_trans (Nat.le_succ L)
              (Nat.le_self_pow (by norm_num) (L + 1))
            omega
          exact_mod_cast hnat
        have hgain_le : G.gain p t ≤ G.d t := by
          dsimp only [OMA.R2H3R1H2.RealGame.gain]; nlinarith [G.hd_nn t]
        linarith
      obtain ⟨p0, hp0⟩ := h0_eq
      obtain ⟨e, hl1, hl2, hcov, hatk, hbr, hge, hle, hsum⟩ :=
        OMA.R2H3R1H2.ratEq_of_realIsEq g hg (M : ℚ) true (g.1 : ℚ)
          (by simpa using hp0) (by simp [hr])
      exact ⟨e, ⟨hl1, hl2, hcov, hatk, hbr, hge, hle⟩, by simpa using hsum⟩
    · -- For every `lam ∈ [0, M]`, `∃ e, isEq lam e ∧ 0 ≤ ∑ cov` holds!
      intro lam hlam0 hlamM
      constructor
      · intro _; exact hlamM
      · intro _
        obtain ⟨c, p, heq⟩ := G.exists_real_eq (Rat.cast_nonneg.mpr hlam0)
        have hsum0 : ((g.1 : ℚ) : ℝ) ≤ ∑ t, c t := by
          simp only [hr, Nat.cast_zero, Rat.cast_zero]
          exact Finset.sum_nonneg fun t _ => (heq.1.1 t).1
        obtain ⟨e, hl1, hl2, hcov, hatk, hbr, hge, hle, hsum⟩ :=
          OMA.R2H3R1H2.ratEq_of_realIsEq g hg lam false (g.1 : ℚ) heq (by simpa using hsum0)
        exact ⟨e, ⟨hl1, hl2, hcov, hatk, hbr, hge, hle⟩, by simpa using hsum⟩
  · -- Case `0 < g.1`!
    have hr_pos : 0 < g.1 := Nat.pos_of_ne_zero hr
    obtain ⟨q, hq0, hqM, hqden, hq_att, hq_max⟩ :=
      OMA.R2H3R1H2.exists_rational_sup_threshold g hg hr_pos
    have hRpos : (0 : ℝ) < (g.1 : ℝ) := Nat.cast_pos.mpr hr_pos
    have hRle : (g.1 : ℝ) ≤ (g.numTargets : ℝ) := Nat.cast_le.mpr hg.2.1
    have hq_exact : ∃ c p, G.IsEq (q : ℝ) c p ∧ ∑ t, c t = (g.1 : ℝ) :=
      G.exists_real_eq_exact_at_sup hRpos hRle (Rat.cast_nonneg.mpr hq0) hq_att
        (fun lam hgt c p heq => by
          by_contra hnot
          linarith [hq_max lam c p heq (not_lt.mp hnot)])
    refine ⟨q, hq0, hqM, hqden, ?_, ?_⟩
    · obtain ⟨c, p, heq, hsum⟩ := hq_exact
      obtain ⟨e, hl1, hl2, hcov, hatk, hbr, hge, hle, hsumQ⟩ :=
        OMA.R2H3R1H2.ratEq_of_realIsEq g hg q true (g.1 : ℚ) heq (by simpa using hsum)
      exact ⟨e, ⟨hl1, hl2, hcov, hatk, hbr, hge, hle⟩, by simpa using hsumQ⟩
    · intro lam hlam0 _
      constructor
      · rintro ⟨e, ⟨hl1, hl2, hcov, hatk, hbr, hge, hle⟩, hsum⟩
        have hreal := OMA.R2H3R1H2.realIsEq_of_ratEq g hg lam e hl1 hl2 hcov hatk hbr hge hle
        have hsumR : (g.1 : ℝ) ≤ ∑ t : Fin g.numTargets, (e.1[t.val]?.getD 0 : ℝ) := by
          exact_mod_cast hsum
        have hleR := hq_max (lam : ℝ) _ _ hreal hsumR
        exact_mod_cast hleR
      · intro hlam_le_q
        obtain ⟨cHi, pHi, hHi, hHisum⟩ := hq_att
        obtain ⟨c₁, p₁, h₁, hc_ge⟩ :=
          G.real_eq_monotone (Rat.cast_nonneg.mpr hlam0) (by exact_mod_cast hlam_le_q) hHi
        have hsum1 : (g.1 : ℝ) ≤ ∑ t, c₁ t :=
          le_trans hHisum (Finset.sum_le_sum fun t _ => hc_ge t)
        obtain ⟨e, hl1, hl2, hcov, hatk, hbr, hge, hle, hsumQ⟩ :=
          OMA.R2H3R1H2.ratEq_of_realIsEq g hg lam false (g.1 : ℚ) h₁ (by simpa using hsum1)
        exact ⟨e, ⟨hl1, hl2, hcov, hatk, hbr, hge, hle⟩, by simpa using hsumQ⟩
