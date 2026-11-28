import FormalConjectures.ErdosProblems.«1221»

-- Problem: Erdős Problem 1221 — iii
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/1221.lean:173 (declaration Erdos1221.erdos_1221.parts.iii)
-- Credit: @sobrien032 (the owner of the agent is credited as the solver)

/-!
# Erdős Problem 1221, part iii: `r (μ_r - 1) → ∞`

The proof follows S. Korsky, A Resolution of the de Bruijn-Erdős Consecutive-Gap Problem (arXiv:2609.07196),
Theorem 1.1 (the ratio bound), Sections 2-5, specialised to one fixed constant `A`: with `A` fixed, two
applications of Korsky's Lemma 2.1 replace the scale chain of his Proposition 3.1, and the finite-prefix
discrepancy input (his Theorem 4.1, after G. Larcher, arXiv:1407.2094) is replaced by the crude bound
`crude_discrepancy`, proved with Larcher's max-min splitting (his Lemma 2.1, after P. Liardet and
R. Tijdeman and G. Wagner) and a level-set count.

Lean formalization, November 27, 2026, for sobrien032: Gemini 4 Neon (extra-high effort) proved the crude
discrepancy bound, the localization (Korsky's Lemma 4.2) and the transfer; Claude Opus 5.5 proved the facts
about sorted points and their lifts, the passage from the ratio to span control, the terminal bounds, the
discrete averaging and Korsky's Lemma 2.1; Claude Fable 5.2 wrote the pen-and-paper proof of the route, which
Grok 4.7 and Claude Opus 5.5 refereed; the Lane B lead (Claude Opus 5.5) wrote the skeleton and the assembly.
-/

open Filter

namespace Erdos1221Ratio

/- ## Definitions -/

/-- The counting error of the first `j` points of the list `z` at `x`:
`#{i < j : z i ≤ x} - j * x`. -/
noncomputable def prefixErr {N : ℕ} (z : Fin N → ℝ) (j : ℕ) (x : ℝ) : ℝ :=
  ((Finset.univ.filter (fun i : Fin N => (i : ℕ) < j ∧ z i ≤ x)).card : ℝ) - (j : ℝ) * x

/-- The lifted sorted points on the line: `liftPt a n j = sortedPoint a n (j mod n) + ⌊j / n⌋` for
`j : ℤ` (junk value `0` when `n = 0`). On natural numbers it agrees with `Erdos1221.unrolled`. -/
noncomputable def liftPt (a : ℕ → ℝ) (n : ℕ) (j : ℤ) : ℝ :=
  if h : 0 < n then
    Erdos1221.sortedPoint a n ⟨(j % (n : ℤ)).toNat % n, Nat.mod_lt _ h⟩ + ((j / (n : ℤ) : ℤ) : ℝ)
  else 0

/-- The number of the first `n` points of `a` in the arc `(x, x + lam]` of the circle
(meaningful for `0 ≤ lam < 1`). -/
noncomputable def arcCount (a : ℕ → ℝ) (n : ℕ) (x lam : ℝ) : ℕ :=
  ((Finset.range n).filter (fun k => Int.fract (a k - x) ∈ Set.Ioc (0 : ℝ) lam)).card

/-- Korsky's hypothesis (2.1) at the real time `t`: with `n = ⌊t⌋`, every `r`-span of the first `n`
points lies in `[(r - α) / t, (r + β) / t]` for some `α, β ≥ 0` with `α + β ≤ A`. -/
def SpanControl (a : ℕ → ℝ) (r : ℕ) (A t : ℝ) : Prop :=
  ∃ α β : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ α + β ≤ A ∧
    ∀ i < ⌊t⌋₊, ((r : ℝ) - α) / t ≤ Erdos1221.rSpan a ⌊t⌋₊ r i ∧
      Erdos1221.rSpan a ⌊t⌋₊ r i ≤ ((r : ℝ) + β) / t

/-- Short-interval counting control (Korsky (4.1)) at the integer time `n`: every arc of length
`D / n` with `0 ≤ D ≤ S` holds `D` of the first `n` points, up to an error `B`. -/
def CountControl (a : ℕ → ℝ) (B S : ℝ) (n : ℕ) : Prop :=
  ∀ x D : ℝ, 0 ≤ D → D ≤ S → |(arcCount a n x (D / n) : ℝ) - D| ≤ B

/- ## P: lifted points, arcs and spans (builder: infrastructure) -/

section Infrastructure

variable (a : ℕ → ℝ)

/- Helpers for P1: the sorted points, and the decomposition `j = i + q * n`. -/

theorem sortedPoint_apply (n : ℕ) (i : Fin n) :
    Erdos1221.sortedPoint a n i =
      Int.fract (a ((Tuple.sort (Erdos1221.pts a n) i : Fin n) : ℕ)) := rfl

theorem sortedPoint_mem_Ico (n : ℕ) (i : Fin n) :
    Erdos1221.sortedPoint a n i ∈ Set.Ico (0 : ℝ) 1 := by
  rw [sortedPoint_apply]
  exact Set.mem_Ico.2 ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

theorem sortedPoint_strictMono (ha : Function.Injective fun k => Int.fract (a k)) (n : ℕ) :
    StrictMono (Erdos1221.sortedPoint a n) := by
  refine (Tuple.monotone_sort (Erdos1221.pts a n)).strictMono_of_injective ?_
  intro i j hij
  have h1 : ((Tuple.sort (Erdos1221.pts a n) i : Fin n) : ℕ) =
      ((Tuple.sort (Erdos1221.pts a n) j : Fin n) : ℕ) := ha hij
  exact (Tuple.sort (Erdos1221.pts a n)).injective (Fin.ext h1)

theorem sortedPoint_symm {n : ℕ} (k : ℕ) (hk : k < n) :
    Erdos1221.sortedPoint a n ((Tuple.sort (Erdos1221.pts a n)).symm ⟨k, hk⟩) =
      Int.fract (a k) := by
  rw [sortedPoint_apply, Equiv.apply_symm_apply]

theorem liftPt_of_pos {n : ℕ} (hn : 0 < n) (j : ℤ) :
    liftPt a n j = Erdos1221.sortedPoint a n ⟨(j % (n : ℤ)).toNat % n, Nat.mod_lt _ hn⟩ +
      ((j / (n : ℤ) : ℤ) : ℝ) := by
  unfold liftPt
  rw [dif_pos hn]

theorem liftPt_decomp {n : ℕ} (hn : 0 < n) (i : ℕ) (hi : i < n) (q : ℤ) :
    liftPt a n ((i : ℤ) + q * n) = Erdos1221.sortedPoint a n ⟨i, hi⟩ + q := by
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  have h0 : (0 : ℤ) ≤ i := by omega
  have h1 : (i : ℤ) < n := by exact_mod_cast hi
  have hmod : ((i : ℤ) + q * n) % (n : ℤ) = i := by
    rw [Int.add_mul_emod_self_right, Int.emod_eq_of_lt h0 h1]
  have hdiv : ((i : ℤ) + q * n) / (n : ℤ) = q := by
    rw [Int.add_mul_ediv_right _ _ hn', Int.ediv_eq_zero_of_lt h0 h1, zero_add]
  have hidx : (⟨(((i : ℤ) + q * n) % (n : ℤ)).toNat % n, Nat.mod_lt _ hn⟩ : Fin n) =
      ⟨i, hi⟩ := by
    apply Fin.ext
    show (((i : ℤ) + q * n) % (n : ℤ)).toNat % n = i
    rw [hmod, Int.toNat_natCast, Nat.mod_eq_of_lt hi]
  rw [liftPt_of_pos a hn, hidx, hdiv]

theorem exists_nat_lt_add_mul {n : ℕ} (hn : 0 < n) (j : ℤ) :
    ∃ i : ℕ, ∃ _ : i < n, ∃ q : ℤ, j = (i : ℤ) + q * n := by
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  have h0 : 0 ≤ j % (n : ℤ) := Int.emod_nonneg j hn'.ne'
  have h1 : j % (n : ℤ) < n := Int.emod_lt_of_pos j hn'
  refine ⟨(j % (n : ℤ)).toNat, (Int.toNat_lt h0).2 h1, j / n, ?_⟩
  rw [Int.toNat_of_nonneg h0, Int.emod_add_ediv_mul]

theorem liftPt_add_mul {n : ℕ} (hn : 0 < n) (j q : ℤ) :
    liftPt a n (j + q * n) = liftPt a n j + q := by
  obtain ⟨i, hi, p, rfl⟩ := exists_nat_lt_add_mul hn j
  have e : (i : ℤ) + p * n + q * n = i + (p + q) * n := by ring
  rw [e, liftPt_decomp a hn i hi, liftPt_decomp a hn i hi]
  push_cast
  ring

/-- P1a. -/
theorem liftPt_natCast (n j : ℕ) : liftPt a n (j : ℤ) = Erdos1221.unrolled a n j := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [liftPt, Erdos1221.unrolled]
  · have e : (j : ℤ) = ((j % n : ℕ) : ℤ) + ((j / n : ℕ) : ℤ) * n := by
      rw [← Nat.cast_mul, ← Nat.cast_add, Nat.mod_add_div']
    rw [e, liftPt_decomp a hn _ (Nat.mod_lt j hn), Erdos1221.unrolled, dif_pos hn,
      Int.cast_natCast]

/-- P1b. -/
theorem liftPt_add_period {n : ℕ} (hn : 0 < n) (j : ℤ) :
    liftPt a n (j + n) = liftPt a n j + 1 := by
  have h := liftPt_add_mul a hn j 1
  rwa [one_mul, Int.cast_one] at h

/-- P1c. -/
theorem liftPt_strictMono (ha : Function.Injective fun k => Int.fract (a k)) {n : ℕ}
    (hn : 0 < n) : StrictMono (liftPt a n) := by
  apply strictMono_int_of_lt_succ
  intro j
  obtain ⟨i, hi, q, rfl⟩ := exists_nat_lt_add_mul hn j
  rcases Nat.lt_or_ge (i + 1) n with h | h
  · have e : (i : ℤ) + q * n + 1 = ((i + 1 : ℕ) : ℤ) + q * n := by push_cast; ring
    rw [e, liftPt_decomp a hn i hi, liftPt_decomp a hn (i + 1) h]
    have hlt : Erdos1221.sortedPoint a n ⟨i, hi⟩ < Erdos1221.sortedPoint a n ⟨i + 1, h⟩ :=
      sortedPoint_strictMono a ha n (Fin.mk_lt_mk.2 (Nat.lt_succ_self i))
    linarith
  · have hi' : (i : ℤ) + 1 = n := by exact_mod_cast (show i + 1 = n by omega)
    have e : (i : ℤ) + q * n + 1 = ((0 : ℕ) : ℤ) + (q + 1) * n := by
      push_cast
      linear_combination hi'
    rw [e, liftPt_decomp a hn i hi, liftPt_decomp a hn 0 hn]
    have h1 := (sortedPoint_mem_Ico a n ⟨i, hi⟩).2
    have h2 := (sortedPoint_mem_Ico a n ⟨0, hn⟩).1
    push_cast
    linarith

/-- P1d: the integer part of a lifted point. -/
theorem floor_liftPt {n : ℕ} (hn : 0 < n) (j : ℤ) : ⌊liftPt a n j⌋ = j / (n : ℤ) := by
  rw [liftPt_of_pos a hn, Int.floor_add_intCast,
    Int.floor_eq_zero_iff.2 (sortedPoint_mem_Ico a n _), zero_add]

/-- P1e: every lifted point is a point of the sequence, read modulo `1`. -/
theorem exists_fract_liftPt {n : ℕ} (hn : 0 < n) (j : ℤ) :
    ∃ k < n, Int.fract (liftPt a n j) = Int.fract (a k) := by
  rw [liftPt_of_pos a hn, Int.fract_add_intCast, sortedPoint_apply, Int.fract_fract]
  exact ⟨_, Fin.is_lt _, rfl⟩

/-- P1f: every one of the first `n` points is a lifted point with index in `[0, n)`. -/
theorem exists_liftPt_eq_fract {n : ℕ} (k : ℕ) (hk : k < n) :
    ∃ j : ℤ, 0 ≤ j ∧ j < n ∧ liftPt a n j = Int.fract (a k) := by
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le k) hk
  obtain ⟨i, hi⟩ : ∃ i : Fin n, Erdos1221.sortedPoint a n i = Int.fract (a k) :=
    ⟨_, sortedPoint_symm a k hk⟩
  refine ⟨((i : ℕ) : ℤ), by omega, by exact_mod_cast i.is_lt, ?_⟩
  have e := liftPt_decomp a hn (i : ℕ) i.is_lt 0
  simp only [zero_mul, add_zero, Int.cast_zero, Fin.eta] at e
  rw [e, hi]

theorem exists_liftPt_eq_of_fract {n : ℕ} (k : ℕ) (hk : k < n) (y : ℝ)
    (hy : Int.fract y = Int.fract (a k)) : ∃ j : ℤ, liftPt a n j = y := by
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le k) hk
  obtain ⟨j₀, -, -, hj₀⟩ := exists_liftPt_eq_fract a k hk
  exact ⟨j₀ + ⌊y⌋ * n, by rw [liftPt_add_mul a hn, hj₀, ← hy, Int.fract_add_floor]⟩

/-- P2: arc counts are counts of lifted points. -/
theorem arcCount_eq_ncard (ha : Function.Injective fun k => Int.fract (a k)) {n : ℕ}
    (hn : 0 < n) (x lam : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam < 1) :
    arcCount a n x lam = Set.ncard {j : ℤ | x < liftPt a n j ∧ liftPt a n j ≤ x + lam} := by
  have hS : arcCount a n x lam =
      Set.ncard {k : ℕ | k < n ∧ Int.fract (a k - x) ∈ Set.Ioc (0 : ℝ) lam} := by
    rw [arcCount, ← Set.ncard_coe_finset]
    congr 1
    ext k
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq]
  have hex : ∀ k ∈ {k : ℕ | k < n ∧ Int.fract (a k - x) ∈ Set.Ioc (0 : ℝ) lam},
      ∃ j : ℤ, liftPt a n j = x + Int.fract (a k - x) := by
    intro k hk
    refine exists_liftPt_eq_of_fract a k hk.1 _ ?_
    rw [Int.fract_eq_fract]
    refine ⟨-⌊a k - x⌋, ?_⟩
    have h1 := Int.floor_add_fract (a k - x)
    push_cast
    linarith
  rw [hS]
  refine Set.ncard_congr (fun k hk => Classical.choose (hex k hk)) ?_ ?_ ?_
  · intro k hk
    have hspec := Classical.choose_spec (hex k hk)
    have h2 : Int.fract (a k - x) ∈ Set.Ioc (0 : ℝ) lam := hk.2
    show x < liftPt a n (Classical.choose (hex k hk)) ∧
      liftPt a n (Classical.choose (hex k hk)) ≤ x + lam
    rw [hspec]
    exact ⟨by linarith [h2.1], by linarith [h2.2]⟩
  · intro k k' hk hk' hkk'
    have hkk'' : Classical.choose (hex k hk) = Classical.choose (hex k' hk') := hkk'
    have e1 := Classical.choose_spec (hex k hk)
    have e2 := Classical.choose_spec (hex k' hk')
    rw [hkk''] at e1
    have h3 : Int.fract (a k - x) = Int.fract (a k' - x) := by linarith
    rw [Int.fract_eq_fract] at h3
    obtain ⟨z, hz⟩ := h3
    have h4 : Int.fract (a k) = Int.fract (a k') := Int.fract_eq_fract.2 ⟨z, by linarith⟩
    exact ha h4
  · intro j hj
    have hj' : x < liftPt a n j ∧ liftPt a n j ≤ x + lam := hj
    obtain ⟨k, hk, hfr⟩ := exists_fract_liftPt a hn j
    have hfx : Int.fract (a k - x) = liftPt a n j - x := by
      rw [Int.fract_eq_iff]
      refine ⟨by linarith [hj'.1], by linarith [hj'.2], ?_⟩
      rw [Int.fract_eq_fract] at hfr
      obtain ⟨z, hz⟩ := hfr
      exact ⟨-z, by push_cast; linarith⟩
    have hkS : k ∈ {k : ℕ | k < n ∧ Int.fract (a k - x) ∈ Set.Ioc (0 : ℝ) lam} :=
      ⟨hk, by rw [hfx]; exact ⟨by linarith [hj'.1], by linarith [hj'.2]⟩⟩
    refine ⟨k, hkS, ?_⟩
    show Classical.choose (hex k hkS) = j
    have e1 := Classical.choose_spec (hex k hkS)
    apply (liftPt_strictMono a ha hn).injective
    rw [e1, hfx]
    ring

/-- P3a. -/
theorem rSpan_eq_liftPt (n r i : ℕ) :
    Erdos1221.rSpan a n r i = liftPt a n ((i + r : ℕ) : ℤ) - liftPt a n (i : ℤ) := by
  rw [Erdos1221.rSpan, liftPt_natCast, liftPt_natCast]

/-- P3b: the spans of any length `L` sum to `L` over one period. -/
theorem sum_liftPt_span {n : ℕ} (hn : 0 < n) (j₀ : ℤ) (L : ℕ) :
    ∑ i ∈ Finset.range n, (liftPt a n (j₀ + i + L) - liftPt a n (j₀ + i)) = L := by
  induction L with
  | zero => simp
  | succ L ih =>
    have step : ∀ i : ℕ, liftPt a n (j₀ + i + ((L + 1 : ℕ) : ℤ)) - liftPt a n (j₀ + i) =
        (liftPt a n (j₀ + L + ((i + 1 : ℕ) : ℤ)) - liftPt a n (j₀ + L + (i : ℤ))) +
        (liftPt a n (j₀ + i + L) - liftPt a n (j₀ + i)) := by
      intro i
      have e1 : j₀ + (i : ℤ) + ((L + 1 : ℕ) : ℤ) = j₀ + L + ((i + 1 : ℕ) : ℤ) := by
        push_cast
        ring
      have e2 : j₀ + (i : ℤ) + (L : ℤ) = j₀ + L + (i : ℤ) := by ring
      rw [e1, e2]
      ring
    have tel : ∑ i ∈ Finset.range n, (liftPt a n (j₀ + L + ((i + 1 : ℕ) : ℤ)) -
        liftPt a n (j₀ + L + (i : ℤ))) =
        liftPt a n (j₀ + L + (n : ℤ)) - liftPt a n (j₀ + L + ((0 : ℕ) : ℤ)) :=
      Finset.sum_range_sub (fun i : ℕ => liftPt a n (j₀ + L + (i : ℤ))) n
    rw [Finset.sum_congr rfl (fun i _ => step i), Finset.sum_add_distrib, ih, tel,
      Nat.cast_zero, add_zero, liftPt_add_period a hn]
    push_cast
    ring

/-- P3c. -/
theorem rSpan_le_maxSpan {n : ℕ} (r : ℕ) {i : ℕ} (hi : i < n) :
    Erdos1221.rSpan a n r i ≤ Erdos1221.maxSpan a n r := by
  exact le_ciSup (f := fun j : Fin n => Erdos1221.rSpan a n r j) (Set.finite_range _).bddAbove
    ⟨i, hi⟩

/-- P3c'. -/
theorem minSpan_le_rSpan {n : ℕ} (r : ℕ) {i : ℕ} (hi : i < n) :
    Erdos1221.minSpan a n r ≤ Erdos1221.rSpan a n r i := by
  exact ciInf_le (f := fun j : Fin n => Erdos1221.rSpan a n r j) (Set.finite_range _).bddBelow
    ⟨i, hi⟩

/-- P3c''. -/
theorem exists_rSpan_eq_maxSpan {n : ℕ} (hn : 0 < n) (r : ℕ) :
    ∃ i < n, Erdos1221.rSpan a n r i = Erdos1221.maxSpan a n r := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun j : Fin n => Erdos1221.rSpan a n r j)
  exact ⟨i, i.is_lt, hi⟩

/-- P3c'''. -/
theorem exists_rSpan_eq_minSpan {n : ℕ} (hn : 0 < n) (r : ℕ) :
    ∃ i < n, Erdos1221.rSpan a n r i = Erdos1221.minSpan a n r := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨i, hi⟩ := exists_eq_ciInf_of_finite (f := fun j : Fin n => Erdos1221.rSpan a n r j)
  exact ⟨i, i.is_lt, hi⟩

theorem sum_rSpan {n : ℕ} (hn : 0 < n) (r : ℕ) :
    ∑ i ∈ Finset.range n, Erdos1221.rSpan a n r i = r := by
  rw [← sum_liftPt_span a hn 0 r]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [rSpan_eq_liftPt, zero_add, Nat.cast_add]

/-- P3d: the average-span identity, lower half. -/
theorem mul_minSpan_le {n : ℕ} (hn : 0 < n) (r : ℕ) :
    (n : ℝ) * Erdos1221.minSpan a n r ≤ r := by
  have h := Finset.card_nsmul_le_sum (Finset.range n) (fun i => Erdos1221.rSpan a n r i)
    (Erdos1221.minSpan a n r) (fun i hi => minSpan_le_rSpan a r (Finset.mem_range.1 hi))
  rw [Finset.card_range, nsmul_eq_mul, sum_rSpan a hn r] at h
  exact h

/-- P3d': the average-span identity, upper half. -/
theorem le_mul_maxSpan {n : ℕ} (hn : 0 < n) (r : ℕ) :
    (r : ℝ) ≤ n * Erdos1221.maxSpan a n r := by
  have h := Finset.sum_le_card_nsmul (Finset.range n) (fun i => Erdos1221.rSpan a n r i)
    (Erdos1221.maxSpan a n r) (fun i hi => rSpan_le_maxSpan a r (Finset.mem_range.1 hi))
  rw [Finset.card_range, nsmul_eq_mul, sum_rSpan a hn r] at h
  exact h

/-- P3e. -/
theorem minSpan_pos (ha : Function.Injective fun k => Int.fract (a k)) {n r : ℕ} (hn : 0 < n)
    (hr : 0 < r) : 0 < Erdos1221.minSpan a n r := by
  obtain ⟨i, -, he⟩ := exists_rSpan_eq_minSpan a hn r
  rw [← he, rSpan_eq_liftPt, sub_pos]
  apply liftPt_strictMono a ha hn
  push_cast
  omega

/-- P4: nestedness of the point sets. -/
theorem exists_liftPt_eq_of_le {n n' : ℕ} (hn : 0 < n) (hnn' : n ≤ n') (j : ℤ) :
    ∃ j' : ℤ, liftPt a n' j' = liftPt a n j := by
  obtain ⟨k, hk, hfr⟩ := exists_fract_liftPt a hn j
  exact exists_liftPt_eq_of_fract a k (lt_of_lt_of_le hk hnn') _ hfr

/-- P5a: span bounds at the `n` base indices hold at every integer index. -/
theorem liftPt_span_bounds {n : ℕ} (hn : 0 < n) (r : ℕ) (lo hi : ℝ)
    (h : ∀ i < n, lo ≤ Erdos1221.rSpan a n r i ∧ Erdos1221.rSpan a n r i ≤ hi) (j : ℤ) :
    lo ≤ liftPt a n (j + r) - liftPt a n j ∧ liftPt a n (j + r) - liftPt a n j ≤ hi := by
  obtain ⟨i, hi', q, rfl⟩ := exists_nat_lt_add_mul hn j
  have e1 : (i : ℤ) + q * n + r = ((i + r : ℕ) : ℤ) + q * n := by push_cast; ring
  have e2 : liftPt a n ((i : ℤ) + q * n + r) - liftPt a n ((i : ℤ) + q * n) =
      Erdos1221.rSpan a n r i := by
    rw [e1, liftPt_add_mul a hn, liftPt_add_mul a hn, rSpan_eq_liftPt]
    ring
  rw [e2]
  exact h i hi'

/-- P5b: `k` consecutive `r`-spans. -/
theorem liftPt_mul_span_bounds {n : ℕ} (hn : 0 < n) (r k : ℕ) (lo hi : ℝ)
    (h : ∀ i < n, lo ≤ Erdos1221.rSpan a n r i ∧ Erdos1221.rSpan a n r i ≤ hi) (j : ℤ) :
    (k : ℝ) * lo ≤ liftPt a n (j + ((k * r : ℕ) : ℤ)) - liftPt a n j ∧
      liftPt a n (j + ((k * r : ℕ) : ℤ)) - liftPt a n j ≤ (k : ℝ) * hi := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hb := liftPt_span_bounds a hn r lo hi h (j + ((k * r : ℕ) : ℤ))
    have e : j + (((k + 1) * r : ℕ) : ℤ) = j + ((k * r : ℕ) : ℤ) + r := by
      push_cast
      ring
    rw [e, Nat.cast_succ]
    constructor
    · linarith [ih.1, hb.1]
    · linarith [ih.2, hb.2]

end Infrastructure

/- ## P6: lifted counts (gate proof, section 2.6) -/

section Counting

variable (a : ℕ → ℝ)

/-- P1g: every integer translate of one of the first `n` points is a lifted point. -/
theorem exists_liftPt_eq_fract_add {n : ℕ} (k : ℕ) (hk : k < n) (e : ℤ) :
    ∃ j : ℤ, liftPt a n j = Int.fract (a k) + e := by
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le k) hk
  obtain ⟨j₁, -, -, hj₁⟩ := exists_liftPt_eq_fract a k hk
  exact ⟨j₁ + e * n, by rw [liftPt_add_mul a hn, hj₁]⟩

/-- P6a: the lifted points in a bounded interval are finitely many. -/
theorem finite_liftPt_Ioc {n : ℕ} (hn : 0 < n) (x y : ℝ) :
    {j : ℤ | x < liftPt a n j ∧ liftPt a n j ≤ y}.Finite := by
  refine (Set.finite_Icc (⌊x⌋ * (n : ℤ)) ((⌊y⌋ + 1) * (n : ℤ))).subset ?_
  intro j hj
  obtain ⟨h1, h2⟩ := hj
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  have e1 : ⌊x⌋ ≤ j / (n : ℤ) := by
    rw [← floor_liftPt a hn j]
    exact Int.floor_mono h1.le
  have e2 : j / (n : ℤ) ≤ ⌊y⌋ := by
    rw [← floor_liftPt a hn j]
    exact Int.floor_mono h2
  have hdiv := Int.emod_add_ediv_mul j n
  have h0 := Int.emod_nonneg j hn'.ne'
  have h3 := Int.emod_lt_of_pos j hn'
  have e3 : ⌊x⌋ * (n : ℤ) ≤ j / n * n := mul_le_mul_of_nonneg_right e1 hn'.le
  have e4 : j / (n : ℤ) * n ≤ ⌊y⌋ * n := mul_le_mul_of_nonneg_right e2 hn'.le
  rw [Set.mem_Icc]
  constructor
  · linarith
  · linarith

/-- P6b: lifted counts are additive over adjacent intervals. -/
theorem ncard_liftPt_Ioc_add {n : ℕ} (hn : 0 < n) {x y z : ℝ} (hxy : x ≤ y) (hyz : y ≤ z) :
    Set.ncard {j : ℤ | x < liftPt a n j ∧ liftPt a n j ≤ z} =
      Set.ncard {j : ℤ | x < liftPt a n j ∧ liftPt a n j ≤ y} +
        Set.ncard {j : ℤ | y < liftPt a n j ∧ liftPt a n j ≤ z} := by
  have hdisj : Disjoint {j : ℤ | x < liftPt a n j ∧ liftPt a n j ≤ y}
      {j : ℤ | y < liftPt a n j ∧ liftPt a n j ≤ z} := by
    rw [Set.disjoint_left]
    intro _ h1 h2
    exact absurd (lt_of_lt_of_le h2.1 h1.2) (lt_irrefl _)
  rw [← Set.ncard_union_eq hdisj (finite_liftPt_Ioc a hn x y) (finite_liftPt_Ioc a hn y z)]
  congr 1
  ext j
  simp only [Set.mem_union, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2⟩
    by_cases h : liftPt a n j ≤ y
    · exact Or.inl ⟨h1, h⟩
    · exact Or.inr ⟨not_le.1 h, h2⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨h1, le_trans h2 hyz⟩
    · exact ⟨lt_of_le_of_lt hxy h1, h2⟩

/-- P6c: the last lifted point at or before `x`. -/
theorem exists_liftPt_le_lt {n : ℕ} (hn : 0 < n) (x : ℝ) :
    ∃ j : ℤ, liftPt a n j ≤ x ∧ x < liftPt a n (j + 1) := by
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  have hbdd : ∃ b : ℤ, ∀ z : ℤ, liftPt a n z ≤ x → z ≤ b := by
    refine ⟨(⌊x⌋ + 1) * n, fun z hz => ?_⟩
    have e1 : z / (n : ℤ) ≤ ⌊x⌋ := by
      rw [← floor_liftPt a hn z]
      exact Int.floor_mono hz
    have hdiv := Int.emod_add_ediv_mul z n
    have h3 := Int.emod_lt_of_pos z hn'
    have e2 : z / (n : ℤ) * n ≤ ⌊x⌋ * n := mul_le_mul_of_nonneg_right e1 hn'.le
    linarith
  have hinh : ∃ z : ℤ, liftPt a n z ≤ x := by
    refine ⟨(⌊x⌋ - 1) * n, ?_⟩
    have e := liftPt_decomp a hn 0 hn (⌊x⌋ - 1)
    rw [Nat.cast_zero, zero_add] at e
    rw [e]
    have h1 := (sortedPoint_mem_Ico a n ⟨0, hn⟩).2
    have h2 := Int.floor_le x
    push_cast
    linarith
  obtain ⟨j, hj, hmax⟩ := Int.exists_greatest_of_bdd hbdd hinh
  refine ⟨j, hj, ?_⟩
  by_contra hcon
  have := hmax (j + 1) (not_lt.1 hcon)
  omega

/-- The integers in `(j, j + m]` are `m` in number. -/
theorem ncard_Ioc_int (j : ℤ) (m : ℕ) : Set.ncard (Set.Ioc j (j + m)) = m := by
  rw [← Finset.coe_Ioc, Set.ncard_coe_finset, Int.card_Ioc]
  simp

/-- Lifted counts are monotone in the interval. -/
theorem ncard_liftPt_mono {n : ℕ} (hn : 0 < n) {x x' y y' : ℝ} (hx : x' ≤ x) (hy : y ≤ y') :
    Set.ncard {j : ℤ | x < liftPt a n j ∧ liftPt a n j ≤ y} ≤
      Set.ncard {j : ℤ | x' < liftPt a n j ∧ liftPt a n j ≤ y'} :=
  Set.ncard_le_ncard (fun j hj => ⟨lt_of_le_of_lt hx hj.1, le_trans hj.2 hy⟩)
    (finite_liftPt_Ioc a hn x' y')

end Counting

/- ## R0: from the ratio to span control -/

/-- R0 (Korsky, Section 5, first half): an eventual ratio bound `1 + C / r` with `C < A` gives
the span control (2.1) with constant `A` at every large real time. -/
theorem span_control_of_ratio (a : ℕ → ℝ) (ha : Function.Injective fun k => Int.fract (a k))
    (r : ℕ) (hr : 1 ≤ r) (A C : ℝ) (hC : 0 ≤ C) (hCA : C < A)
    (h : ∀ᶠ n : ℕ in atTop, Erdos1221.maxSpan a n r ≤ (1 + C / r) * Erdos1221.minSpan a n r) :
    ∀ᶠ t : ℝ in atTop, SpanControl a r A t := by
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 h
  have hAC : 0 < A - C := by linarith
  obtain ⟨N₂, hN₂⟩ := exists_nat_ge ((r + C) / (A - C))
  refine Filter.eventually_atTop.2 ⟨((max (max N₀ N₂) 1 : ℕ) : ℝ), fun t ht => ?_⟩
  have ht0 : (0 : ℝ) ≤ t := le_trans (Nat.cast_nonneg _) ht
  have hNn : max (max N₀ N₂) 1 ≤ ⌊t⌋₊ := Nat.le_floor ht
  have hnt : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le ht0
  have htn : t < ⌊t⌋₊ + 1 := Nat.lt_floor_add_one t
  unfold SpanControl
  generalize ⌊t⌋₊ = n at hNn hnt htn ⊢
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hNn
  have hnN₀ : N₀ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hNn
  have hnN₂ : N₂ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hNn
  have hnpos : 0 < n := by omega
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have htpos : 0 < t := by linarith
  have hratio := hN₀ n hnN₀
  have hm := minSpan_pos a ha hnpos (by omega : 0 < r)
  have hlo := mul_minSpan_le a hnpos r
  have hmM : Erdos1221.minSpan a n r ≤ Erdos1221.maxSpan a n r :=
    le_trans (minSpan_le_rSpan a r hnpos) (rSpan_le_maxSpan a r hnpos)
  have hM0 : 0 ≤ Erdos1221.maxSpan a n r := by linarith
  have h1 : (n : ℝ) * Erdos1221.maxSpan a n r ≤ n * Erdos1221.minSpan a n r + C := by
    have e1 : (n : ℝ) * Erdos1221.maxSpan a n r ≤
        n * ((1 + C / r) * Erdos1221.minSpan a n r) :=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    have e2 : C / r * (n * Erdos1221.minSpan a n r) ≤ C / r * r :=
      mul_le_mul_of_nonneg_left hlo (by positivity)
    have e3 : C / r * r = C := div_mul_cancel₀ C hr'.ne'
    have e4 : (n : ℝ) * ((1 + C / r) * Erdos1221.minSpan a n r) =
        n * Erdos1221.minSpan a n r + C / r * (n * Erdos1221.minSpan a n r) := by ring
    linarith
  have h2 : (r : ℝ) + C ≤ n * (A - C) := by
    have hN₂' : ((N₂ : ℕ) : ℝ) ≤ n := by exact_mod_cast hnN₂
    exact (div_le_iff₀ hAC).1 (le_trans hN₂ hN₂')
  have h3 : Erdos1221.maxSpan a n r ≤ A - C := by
    have e1 : (n : ℝ) * Erdos1221.maxSpan a n r ≤ n * (A - C) := by linarith
    exact le_of_mul_le_mul_left e1 (by positivity)
  have h4 : t * Erdos1221.maxSpan a n r ≤ (n + 1) * Erdos1221.maxSpan a n r :=
    mul_le_mul_of_nonneg_right htn.le hM0
  have h5 : (n : ℝ) * Erdos1221.maxSpan a n r ≤ t * Erdos1221.maxSpan a n r :=
    mul_le_mul_of_nonneg_right hnt hM0
  refine ⟨r - n * Erdos1221.minSpan a n r, t * Erdos1221.maxSpan a n r - r, by linarith,
    by linarith [le_mul_maxSpan a hnpos r], by linarith, fun i hi => ⟨?_, ?_⟩⟩
  · rw [div_le_iff₀ htpos]
    have hmi := minSpan_le_rSpan a r hi
    have e1 : (n : ℝ) * Erdos1221.minSpan a n r ≤ t * Erdos1221.minSpan a n r :=
      mul_le_mul_of_nonneg_right hnt hm.le
    have e2 : t * Erdos1221.minSpan a n r ≤ t * Erdos1221.rSpan a n r i :=
      mul_le_mul_of_nonneg_left hmi htpos.le
    linarith
  · rw [le_div_iff₀ htpos]
    have hiM := rSpan_le_maxSpan a r hi
    have e1 : Erdos1221.rSpan a n r i * t ≤ Erdos1221.maxSpan a n r * t :=
      mul_le_mul_of_nonneg_right hiM htpos.le
    linarith

/-- R0': the eventual ratio bound in `ℝ≥0∞` of hypothesis H2 (Korsky, Section 5, steps (b) and (c))
gives span control at every large real time. -/
theorem exists_spanControl_of_ennreal (a : ℕ → ℝ) (ha : Function.Injective fun k => Int.fract (a k))
    (r : ℕ) (hr : 1 ≤ r) (A C : ℝ) (hC : 0 ≤ C) (hCA : C < A)
    (h : ∀ᶠ n : ℕ in atTop, ENNReal.ofReal (Erdos1221.maxSpan a n r) /
        ENNReal.ofReal (Erdos1221.minSpan a n r) ≤ ENNReal.ofReal (1 + C / r)) :
    ∃ T : ℝ, ∀ s ≥ T, SpanControl a r A s := by
  have h' : ∀ᶠ n : ℕ in atTop,
      Erdos1221.maxSpan a n r ≤ (1 + C / r) * Erdos1221.minSpan a n r := by
    filter_upwards [h, eventually_ge_atTop 1] with n hn hn1
    have hm := minSpan_pos a ha (n := n) (r := r) (by omega) (by omega)
    have hm0 : ENNReal.ofReal (Erdos1221.minSpan a n r) ≠ 0 := by
      rw [Ne, ENNReal.ofReal_eq_zero, not_le]
      exact hm
    have hle := (ENNReal.div_le_iff hm0 ENNReal.ofReal_ne_top).1 hn
    have hpos : (0 : ℝ) ≤ 1 + C / r := by positivity
    rw [← ENNReal.ofReal_mul hpos, ENNReal.ofReal_le_ofReal_iff (mul_nonneg hpos hm.le)] at hle
    exact hle
  exact Filter.eventually_atTop.1 (span_control_of_ratio a ha r hr A C hC hCA h')

/- ## T1: the terminal bounds (Korsky (3.2); gate proof, section 5.1) -/

/-- T1a (Korsky (3.2), upper half): under span control at the real time `t`, every arc of length
`(r - A) / t` holds at most `r` of the first `⌊t⌋₊` points. -/
theorem arcCount_le_of_spanControl (a : ℕ → ℝ) (ha : Function.Injective fun k => Int.fract (a k))
    (r : ℕ) (hr : 1 ≤ r) (A t : ℝ) (hAr : A ≤ r) (ht : (r : ℝ) + A < t)
    (h : SpanControl a r A t) (x : ℝ) :
    (arcCount a ⌊t⌋₊ x (((r : ℝ) - A) / t) : ℝ) ≤ r := by
  obtain ⟨α, β, hα, hβ, hαβ, hsp⟩ := h
  have hA0 : 0 ≤ A := by linarith
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have ht1 : 1 ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  have hn : 0 < ⌊t⌋₊ := Nat.floor_pos.2 ht1
  have hl0 : 0 ≤ ((r : ℝ) - A) / t := div_nonneg (by linarith) ht0.le
  have hl1 : ((r : ℝ) - A) / t < 1 := by
    rw [div_lt_one ht0]
    linarith
  have hgap : ∀ j : ℤ, ((r : ℝ) - A) / t ≤ liftPt a ⌊t⌋₊ (j + r) - liftPt a ⌊t⌋₊ j := by
    intro j
    have e := (liftPt_span_bounds a hn r _ _ hsp j).1
    have e2 : ((r : ℝ) - A) / t ≤ ((r : ℝ) - α) / t :=
      div_le_div_of_nonneg_right (by linarith) ht0.le
    linarith
  rw [arcCount_eq_ncard a ha hn x _ hl0 hl1]
  obtain ⟨j₀, hj₀, hj₁⟩ := exists_liftPt_le_lt a hn x
  have hsub : {j : ℤ | x < liftPt a ⌊t⌋₊ j ∧ liftPt a ⌊t⌋₊ j ≤ x + ((r : ℝ) - A) / t} ⊆
      Set.Ioc j₀ (j₀ + r) := by
    intro j hj
    obtain ⟨h1, h2⟩ := hj
    rw [Set.mem_Ioc]
    constructor
    · by_contra hcon
      have : liftPt a ⌊t⌋₊ j ≤ liftPt a ⌊t⌋₊ j₀ :=
        (liftPt_strictMono a ha hn).monotone (not_lt.1 hcon)
      linarith
    · by_contra hcon
      have e1 : liftPt a ⌊t⌋₊ (j₀ + 1 + r) ≤ liftPt a ⌊t⌋₊ j :=
        (liftPt_strictMono a ha hn).monotone (by omega)
      have e2 := hgap (j₀ + 1)
      linarith
  have := Set.ncard_le_ncard hsub (Set.finite_Ioc _ _)
  rw [ncard_Ioc_int] at this
  exact_mod_cast this

/-- T1b (Korsky (3.2), lower half): under span control at the real time `t`, every arc of length
`(r + A) / t` holds at least `r` of the first `⌊t⌋₊` points. -/
theorem le_arcCount_of_spanControl (a : ℕ → ℝ) (ha : Function.Injective fun k => Int.fract (a k))
    (r : ℕ) (hr : 1 ≤ r) (A t : ℝ) (ht : (r : ℝ) + A < t)
    (h : SpanControl a r A t) (x : ℝ) :
    (r : ℝ) ≤ arcCount a ⌊t⌋₊ x (((r : ℝ) + A) / t) := by
  obtain ⟨α, β, hα, hβ, hαβ, hsp⟩ := h
  have hA0 : 0 ≤ A := by linarith
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have ht1 : 1 ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  have hn : 0 < ⌊t⌋₊ := Nat.floor_pos.2 ht1
  have hl0 : 0 ≤ ((r : ℝ) + A) / t := div_nonneg (by linarith) ht0.le
  have hl1 : ((r : ℝ) + A) / t < 1 := by
    rw [div_lt_one ht0]
    exact ht
  have hgap : ∀ j : ℤ, liftPt a ⌊t⌋₊ (j + r) - liftPt a ⌊t⌋₊ j ≤ ((r : ℝ) + A) / t := by
    intro j
    have e := (liftPt_span_bounds a hn r _ _ hsp j).2
    have e2 : ((r : ℝ) + β) / t ≤ ((r : ℝ) + A) / t :=
      div_le_div_of_nonneg_right (by linarith) ht0.le
    linarith
  rw [arcCount_eq_ncard a ha hn x _ hl0 hl1]
  obtain ⟨j₀, hj₀, hj₁⟩ := exists_liftPt_le_lt a hn x
  have hsub : Set.Ioc j₀ (j₀ + r) ⊆
      {j : ℤ | x < liftPt a ⌊t⌋₊ j ∧ liftPt a ⌊t⌋₊ j ≤ x + ((r : ℝ) + A) / t} := by
    intro j hj
    rw [Set.mem_Ioc] at hj
    have e1 : liftPt a ⌊t⌋₊ (j₀ + 1) ≤ liftPt a ⌊t⌋₊ j :=
      (liftPt_strictMono a ha hn).monotone (by omega)
    have e2 : liftPt a ⌊t⌋₊ j ≤ liftPt a ⌊t⌋₊ (j₀ + r) :=
      (liftPt_strictMono a ha hn).monotone hj.2
    have e3 := hgap j₀
    exact ⟨by linarith, by linarith⟩
  have := Set.ncard_le_ncard hsub (finite_liftPt_Ioc a hn _ _)
  rw [ncard_Ioc_int] at this
  exact_mod_cast this

/- ## C0: discrete averaging over translations (gate proof, section 5.2) -/

/-- The regrouping identity behind C0: shifting by `H` over `m` windows equals shifting by `m`
over `H` windows. -/
theorem sum_range_shift_sub (φ : ℕ → ℝ) (m H : ℕ) :
    ∑ i ∈ Finset.range m, (φ (i + H) - φ i) = ∑ g ∈ Finset.range H, (φ (g + m) - φ g) := by
  have h1 := Finset.sum_range_add φ H m
  have h2 := Finset.sum_range_add φ m H
  rw [add_comm H m] at h1
  have e1 : ∑ i ∈ Finset.range m, φ (i + H) = ∑ i ∈ Finset.range m, φ (H + i) :=
    Finset.sum_congr rfl (fun i _ => by rw [add_comm])
  have e2 : ∑ g ∈ Finset.range H, φ (g + m) = ∑ g ∈ Finset.range H, φ (m + g) :=
    Finset.sum_congr rfl (fun g _ => by rw [add_comm])
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, e1, e2]
  linarith

/-- An Archimedean limit: a bound with an error `Y / m` for every `m ≥ 1` holds without it. -/
theorem le_of_forall_le_add_div (K X Y : ℝ) (h : ∀ m : ℕ, 0 < m → K ≤ X + Y / m) : K ≤ X := by
  by_contra hcon
  have hKX : 0 < K - X := by linarith [not_le.1 hcon]
  obtain ⟨m, hm⟩ := exists_nat_gt (|Y| / (K - X))
  have hm0 : (0 : ℝ) < m := lt_of_le_of_lt (div_nonneg (abs_nonneg Y) hKX.le) hm
  have h1 := h m (by exact_mod_cast hm0)
  have h2 : |Y| < m * (K - X) := by rwa [div_lt_iff₀ hKX] at hm
  have h3 : Y / m ≤ |Y| / m := div_le_div_of_nonneg_right (le_abs_self Y) hm0.le
  have h4 : |Y| / m < K - X := by
    rw [div_lt_iff₀ hm0]
    linarith
  linarith

/-- C0a: discrete averaging over translations, upper form. `N x y` is a nonnegative additive
function of the interval `(x, y]`. -/
theorem avg_translates_le (N : ℝ → ℝ → ℝ) (h0 : ∀ x y, 0 ≤ N x y)
    (hadd : ∀ x y z, x ≤ y → y ≤ z → N x z = N x y + N y z)
    (c d l K Y : ℝ) (hcd : c ≤ d) (hl : 0 < l)
    (hK : ∀ u, 0 ≤ u → u < l → K ≤ N (c + u) (d + u))
    (hY : ∀ v, c ≤ v → N v (v + l) ≤ Y) :
    K ≤ (d - c) / l * Y := by
  have hY0 : 0 ≤ Y := le_trans (h0 c (c + l)) (hY c le_rfl)
  refine le_of_forall_le_add_div K ((d - c) / l * Y) Y (fun m hm => ?_)
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hm0 : (m : ℝ) ≠ 0 := hm'.ne'
  have hl0 : l ≠ 0 := hl.ne'
  have hh : 0 < l / m := div_pos hl hm'
  have hmh : (m : ℝ) * (l / m) = l := by field_simp
  have hH1 : d - c ≤ (⌈(d - c) / (l / m)⌉₊ : ℝ) * (l / m) := by
    have := Nat.le_ceil ((d - c) / (l / m))
    rwa [div_le_iff₀ hh] at this
  have hH2 : (⌈(d - c) / (l / m)⌉₊ : ℝ) < (d - c) / (l / m) + 1 :=
    Nat.ceil_lt_add_one (div_nonneg (by linarith) hh.le)
  set h := l / m with hh_def
  set H := ⌈(d - c) / h⌉₊ with hH_def
  have step1 : ∀ i ∈ Finset.range m,
      K ≤ N c (c + ((i + H : ℕ) : ℝ) * h) - N c (c + (i : ℝ) * h) := by
    intro i hi
    have hi' : (i : ℝ) < m := by exact_mod_cast Finset.mem_range.1 hi
    have hu0 : 0 ≤ (i : ℝ) * h := by positivity
    have hul : (i : ℝ) * h < l := by
      rw [← hmh]
      exact mul_lt_mul_of_pos_right hi' hh
    have e1 := hK _ hu0 hul
    have hcast : ((i + H : ℕ) : ℝ) * h = (i : ℝ) * h + (H : ℝ) * h := by
      push_cast
      ring
    have e2 := hadd (c + (i : ℝ) * h) (d + (i : ℝ) * h) (c + ((i + H : ℕ) : ℝ) * h)
      (by linarith) (by rw [hcast]; linarith)
    have e3 := hadd c (c + (i : ℝ) * h) (c + ((i + H : ℕ) : ℝ) * h)
      (by linarith) (by rw [hcast]; linarith)
    have e4 := h0 (d + (i : ℝ) * h) (c + ((i + H : ℕ) : ℝ) * h)
    linarith
  have step2 : ∀ g ∈ Finset.range H,
      N c (c + ((g + m : ℕ) : ℝ) * h) - N c (c + (g : ℝ) * h) ≤ Y := by
    intro g _
    have hcast : c + ((g + m : ℕ) : ℝ) * h = c + (g : ℝ) * h + l := by
      rw [← hmh]
      push_cast
      ring
    have hg0 : 0 ≤ (g : ℝ) * h := by positivity
    have e1 := hadd c (c + (g : ℝ) * h) (c + ((g + m : ℕ) : ℝ) * h) (by linarith)
      (by rw [hcast]; linarith)
    have e2 := hY (c + (g : ℝ) * h) (by linarith)
    rw [hcast] at e1 ⊢
    linarith
  have hsum1 := Finset.sum_le_sum step1
  have hsum2 := Finset.sum_le_sum step2
  have hreg : ∑ i ∈ Finset.range m,
      (N c (c + ((i + H : ℕ) : ℝ) * h) - N c (c + (i : ℝ) * h)) =
      ∑ g ∈ Finset.range H, (N c (c + ((g + m : ℕ) : ℝ) * h) - N c (c + (g : ℝ) * h)) :=
    sum_range_shift_sub (fun i : ℕ => N c (c + (i : ℝ) * h)) m H
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum1 hsum2
  have h3 : (m : ℝ) * K ≤ H * Y := by linarith
  have h4 : (H : ℝ) * Y ≤ ((d - c) / h + 1) * Y := mul_le_mul_of_nonneg_right hH2.le hY0
  have h5 : (m : ℝ) * ((d - c) / l * Y + Y / m) = ((d - c) / h + 1) * Y := by
    rw [hh_def]
    field_simp
  have h6 : (m : ℝ) * K ≤ (m : ℝ) * ((d - c) / l * Y + Y / m) := by
    rw [h5]
    linarith
  exact le_of_mul_le_mul_left h6 hm'

/-- C0b: discrete averaging over translations, lower form. -/
theorem le_avg_translates (N : ℝ → ℝ → ℝ) (h0 : ∀ x y, 0 ≤ N x y)
    (hadd : ∀ x y z, x ≤ y → y ≤ z → N x z = N x y + N y z)
    (c d l K Y : ℝ) (hcd : c ≤ d) (hl : 0 < l) (hY0 : 0 ≤ Y)
    (hK : ∀ u, 0 ≤ u → u < l → N (c + u) (d + u) ≤ K)
    (hY : ∀ v, c ≤ v → Y ≤ N v (v + l)) :
    (d - c) / l * Y ≤ K := by
  refine le_of_forall_le_add_div ((d - c) / l * Y) K Y (fun m hm => ?_)
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hm0 : (m : ℝ) ≠ 0 := hm'.ne'
  have hl0 : l ≠ 0 := hl.ne'
  have hh : 0 < l / m := div_pos hl hm'
  have hmh : (m : ℝ) * (l / m) = l := by field_simp
  have hH1 : (⌊(d - c) / (l / m)⌋₊ : ℝ) * (l / m) ≤ d - c := by
    have := Nat.floor_le (div_nonneg (by linarith : (0 : ℝ) ≤ d - c) hh.le)
    rwa [le_div_iff₀ hh] at this
  have hH2 : (d - c) / (l / m) < (⌊(d - c) / (l / m)⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  set h := l / m with hh_def
  set H := ⌊(d - c) / h⌋₊ with hH_def
  have step1 : ∀ i ∈ Finset.range m,
      N c (c + ((i + H : ℕ) : ℝ) * h) - N c (c + (i : ℝ) * h) ≤ K := by
    intro i hi
    have hi' : (i : ℝ) < m := by exact_mod_cast Finset.mem_range.1 hi
    have hu0 : 0 ≤ (i : ℝ) * h := by positivity
    have hul : (i : ℝ) * h < l := by
      rw [← hmh]
      exact mul_lt_mul_of_pos_right hi' hh
    have e1 := hK _ hu0 hul
    have hcast : ((i + H : ℕ) : ℝ) * h = (i : ℝ) * h + (H : ℝ) * h := by
      push_cast
      ring
    have hH0 : 0 ≤ (H : ℝ) * h := by positivity
    have e2 := hadd (c + (i : ℝ) * h) (c + ((i + H : ℕ) : ℝ) * h) (d + (i : ℝ) * h)
      (by rw [hcast]; linarith) (by rw [hcast]; linarith)
    have e3 := hadd c (c + (i : ℝ) * h) (c + ((i + H : ℕ) : ℝ) * h)
      (by linarith) (by rw [hcast]; linarith)
    have e4 := h0 (c + ((i + H : ℕ) : ℝ) * h) (d + (i : ℝ) * h)
    linarith
  have step2 : ∀ g ∈ Finset.range H,
      Y ≤ N c (c + ((g + m : ℕ) : ℝ) * h) - N c (c + (g : ℝ) * h) := by
    intro g _
    have hcast : c + ((g + m : ℕ) : ℝ) * h = c + (g : ℝ) * h + l := by
      rw [← hmh]
      push_cast
      ring
    have hg0 : 0 ≤ (g : ℝ) * h := by positivity
    have e1 := hadd c (c + (g : ℝ) * h) (c + ((g + m : ℕ) : ℝ) * h) (by linarith)
      (by rw [hcast]; linarith)
    have e2 := hY (c + (g : ℝ) * h) (by linarith)
    rw [hcast] at e1 ⊢
    linarith
  have hsum1 := Finset.sum_le_sum step1
  have hsum2 := Finset.sum_le_sum step2
  have hreg : ∑ i ∈ Finset.range m,
      (N c (c + ((i + H : ℕ) : ℝ) * h) - N c (c + (i : ℝ) * h)) =
      ∑ g ∈ Finset.range H, (N c (c + ((g + m : ℕ) : ℝ) * h) - N c (c + (g : ℝ) * h)) :=
    sum_range_shift_sub (fun i : ℕ => N c (c + (i : ℝ) * h)) m H
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum1 hsum2
  have h3 : (H : ℝ) * Y ≤ m * K := by linarith
  have h4 : ((d - c) / h - 1) * Y ≤ (H : ℝ) * Y := mul_le_mul_of_nonneg_right (by linarith) hY0
  have h5 : (m : ℝ) * ((d - c) / l * Y) = (d - c) / h * Y := by
    rw [hh_def]
    field_simp
  have h6 : (m : ℝ) * ((d - c) / l * Y) ≤ (m : ℝ) * (K + Y / m) := by
    have e : (m : ℝ) * (K + Y / m) = m * K + Y := by
      field_simp
    rw [h5, e]
    nlinarith
  exact le_of_mul_le_mul_left h6 hm'

/- ## C1: the two injective compositions (gate proof, section 5.3) -/

/-- C1a: forward `m` places at time `n`, include into time `n'`, backward `m` places at time `n'`,
include into time `n''`. -/
theorem ncard_liftPt_le_fwd_bwd (a : ℕ → ℝ) (ha : Function.Injective fun k => Int.fract (a k))
    {n n' n'' : ℕ} (hn : 0 < n) (hnn' : n ≤ n') (hn'n'' : n' ≤ n'') (m : ℕ)
    (lo₁ hi₁ lo₂ hi₂ : ℝ)
    (h₁ : ∀ j : ℤ, lo₁ ≤ liftPt a n (j + m) - liftPt a n j ∧
      liftPt a n (j + m) - liftPt a n j ≤ hi₁)
    (h₂ : ∀ j : ℤ, lo₂ ≤ liftPt a n' (j + m) - liftPt a n' j ∧
      liftPt a n' (j + m) - liftPt a n' j ≤ hi₂)
    (x y : ℝ) :
    Set.ncard {j : ℤ | x < liftPt a n j ∧ liftPt a n j ≤ y} ≤
      Set.ncard {j : ℤ | x + lo₁ - hi₂ < liftPt a n'' j ∧ liftPt a n'' j ≤ y + hi₁ - lo₂} := by
  have hn' : 0 < n' := lt_of_lt_of_le hn hnn'
  have hn'' : 0 < n'' := lt_of_lt_of_le hn' hn'n''
  choose f hf using fun j : ℤ => exists_liftPt_eq_of_le a hn hnn' (j + m)
  choose g hg using fun j : ℤ => exists_liftPt_eq_of_le a hn' hn'n'' (f j - m)
  refine Set.ncard_le_ncard_of_injOn g ?_ ?_ (finite_liftPt_Ioc a hn'' _ _)
  · intro j hj
    obtain ⟨hx, hy⟩ := hj
    have e1 := h₁ j
    have e2 := h₂ (f j - m)
    rw [sub_add_cancel, hf j] at e2
    show x + lo₁ - hi₂ < liftPt a n'' (g j) ∧ liftPt a n'' (g j) ≤ y + hi₁ - lo₂
    rw [hg j]
    constructor
    · linarith [e1.1, e2.2]
    · linarith [e1.2, e2.1]
  · intro j₁ _ j₂ _ heq
    have e1 : liftPt a n' (f j₁ - m) = liftPt a n' (f j₂ - m) := by
      rw [← hg j₁, ← hg j₂, heq]
    have e2 : f j₁ - m = f j₂ - m := (liftPt_strictMono a ha hn').injective e1
    have e3 : liftPt a n (j₁ + m) = liftPt a n (j₂ + m) := by
      rw [← hf j₁, ← hf j₂, show f j₁ = f j₂ by linarith]
    have e4 := (liftPt_strictMono a ha hn).injective e3
    linarith

/-- C1b: include into time `n'`, backward `m` places at time `n'`, include into time `n''`,
forward `m` places at time `n''`. -/
theorem ncard_liftPt_le_bwd_fwd (a : ℕ → ℝ) (ha : Function.Injective fun k => Int.fract (a k))
    {n n' n'' : ℕ} (hn : 0 < n) (hnn' : n ≤ n') (hn'n'' : n' ≤ n'') (m : ℕ)
    (lo₂ hi₂ lo₃ hi₃ : ℝ)
    (h₂ : ∀ j : ℤ, lo₂ ≤ liftPt a n' (j + m) - liftPt a n' j ∧
      liftPt a n' (j + m) - liftPt a n' j ≤ hi₂)
    (h₃ : ∀ j : ℤ, lo₃ ≤ liftPt a n'' (j + m) - liftPt a n'' j ∧
      liftPt a n'' (j + m) - liftPt a n'' j ≤ hi₃)
    (x y : ℝ) :
    Set.ncard {j : ℤ | x < liftPt a n j ∧ liftPt a n j ≤ y} ≤
      Set.ncard {j : ℤ | x - hi₂ + lo₃ < liftPt a n'' j ∧ liftPt a n'' j ≤ y - lo₂ + hi₃} := by
  have hn' : 0 < n' := lt_of_lt_of_le hn hnn'
  have hn'' : 0 < n'' := lt_of_lt_of_le hn' hn'n''
  choose f hf using fun j : ℤ => exists_liftPt_eq_of_le a hn hnn' j
  choose g hg using fun j : ℤ => exists_liftPt_eq_of_le a hn' hn'n'' (f j - m)
  refine Set.ncard_le_ncard_of_injOn (fun j => g j + m) ?_ ?_ (finite_liftPt_Ioc a hn'' _ _)
  · intro j hj
    obtain ⟨hx, hy⟩ := hj
    have e2 := h₂ (f j - m)
    rw [sub_add_cancel, hf j] at e2
    have e3 := h₃ (g j)
    rw [hg j] at e3
    show x - hi₂ + lo₃ < liftPt a n'' (g j + m) ∧ liftPt a n'' (g j + m) ≤ y - lo₂ + hi₃
    constructor
    · linarith [e2.2, e3.1]
    · linarith [e2.1, e3.2]
  · intro j₁ _ j₂ _ heq
    have heq' : g j₁ = g j₂ := by
      have h' : g j₁ + (m : ℤ) = g j₂ + m := heq
      linarith
    have e1 : liftPt a n' (f j₁ - m) = liftPt a n' (f j₂ - m) := by
      rw [← hg j₁, ← hg j₂, heq']
    have e2 : f j₁ - m = f j₂ - m := (liftPt_strictMono a ha hn').injective e1
    have e3 : liftPt a n j₁ = liftPt a n j₂ := by
      rw [← hf j₁, ← hf j₂, show f j₁ = f j₂ by linarith]
    exact (liftPt_strictMono a ha hn).injective e3

/- ## C2: Korsky's Lemma 2.1, before division by `D` (gate proof, section 5.4) -/

/-- The comparison time `s(u)` of the upper comparison: `κ / t - κ / s = u` with `t ≤ s ≤ (1 + q) t`. -/
theorem exists_time_later (t q κ u : ℝ) (ht : 0 < t) (hκ : 0 < κ) (hq : 0 ≤ q) (hu0 : 0 ≤ u)
    (hu : u * ((1 + q) * t) < q * κ) :
    ∃ s : ℝ, t ≤ s ∧ s ≤ (1 + q) * t ∧ κ / t - κ / s = u := by
  have hut : u * t < κ := by nlinarith
  have hw : 0 < 1 / t - u / κ := by
    rw [sub_pos, div_lt_div_iff₀ hκ ht]
    linarith
  refine ⟨1 / (1 / t - u / κ), ?_, ?_, ?_⟩
  · rw [le_div_iff₀ hw]
    have e : t * (1 / t - u / κ) = 1 - u * t / κ := by
      field_simp
    rw [e]
    have : 0 ≤ u * t / κ := by positivity
    linarith
  · rw [div_le_iff₀ hw]
    have e : (1 + q) * t * (1 / t - u / κ) = (1 + q) - (1 + q) * (u * t) / κ := by
      field_simp
    rw [e]
    have : (1 + q) * (u * t) / κ ≤ q := by
      rw [div_le_iff₀ hκ]
      nlinarith
    linarith
  · rw [div_div_eq_mul_div, div_one]
    field_simp
    ring

/-- The comparison time `s(u)` of the lower comparison: `κ / s - κ / t = u` with
`(1 - q) t ≤ s ≤ t`. -/
theorem exists_time_earlier (t q κ u : ℝ) (ht : 0 < t) (hκ : 0 < κ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hu0 : 0 ≤ u) (hu : u * ((1 - q) * t) < q * κ) :
    ∃ s : ℝ, (1 - q) * t ≤ s ∧ s ≤ t ∧ κ / s - κ / t = u := by
  have hw : 0 < 1 / t + u / κ := by positivity
  refine ⟨1 / (1 / t + u / κ), ?_, ?_, ?_⟩
  · rw [le_div_iff₀ hw]
    have e : (1 - q) * t * (1 / t + u / κ) = (1 - q) + (1 - q) * (u * t) / κ := by
      field_simp
    rw [e]
    have : (1 - q) * (u * t) / κ ≤ q := by
      rw [div_le_iff₀ hκ]
      nlinarith
    linarith
  · rw [div_le_iff₀ hw]
    have e : t * (1 / t + u / κ) = 1 + u * t / κ := by
      field_simp
    rw [e]
    have : 0 ≤ u * t / κ := by positivity
    linarith
  · rw [div_div_eq_mul_div, div_one]
    field_simp
    ring

/-- C2a (Korsky (2.2), before division by `D`): counts at time `t` on arcs of length `D / t`,
from a uniform upper bound `c` at the later time `(1 + q) * t` on arcs of length `E / ((1 + q) * t)`. -/
theorem arcCount_le_of_later (a : ℕ → ℝ) (ha : Function.Injective fun k => Int.fract (a k))
    (r k : ℕ) (hr : 1 ≤ r) (hk : 1 ≤ k) (A D E q c t : ℝ) (hD : 0 ≤ D) (hE : 0 < E)
    (hq : q = E / ((k : ℝ) * r)) (hq1 : q < 1) (ht : 1 ≤ t) (hDt : D < t)
    (hEt : E < (1 + q) * t)
    (hspan : ∀ s : ℝ, t ≤ s → s ≤ (1 + q) * t → SpanControl a r A s)
    (hc : ∀ v : ℝ, (arcCount a ⌊(1 + q) * t⌋₊ v (E / ((1 + q) * t)) : ℝ) ≤ c) (x : ℝ) :
    (arcCount a ⌊t⌋₊ x (D / t) : ℝ) ≤ (D + 3 * (k : ℝ) * A) * (1 + q) / E * c := by
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hκ : (1 : ℝ) ≤ (k : ℝ) * r := by nlinarith
  have hq0 : 0 < q := by
    rw [hq]
    exact div_pos hE (by linarith)
  have ht0 : 0 < t := by linarith
  have htp : t ≤ (1 + q) * t := by nlinarith
  have htp0 : 0 < (1 + q) * t := by positivity
  have hq1' : (1 : ℝ) + q ≠ 0 := by positivity
  have ht0' : t ≠ 0 := ht0.ne'
  have hn : 0 < ⌊t⌋₊ := Nat.floor_pos.2 ht
  have hnp : ⌊t⌋₊ ≤ ⌊(1 + q) * t⌋₊ := Nat.floor_mono htp
  have hnp0 : 0 < ⌊(1 + q) * t⌋₊ := lt_of_lt_of_le hn hnp
  have hℓ0 : 0 < E / ((1 + q) * t) := div_pos hE htp0
  have hℓ1 : E / ((1 + q) * t) < 1 := by
    rw [div_lt_one htp0]
    exact hEt
  have hc0 : 0 ≤ c := le_trans (Nat.cast_nonneg _) (hc 0)
  obtain ⟨α, β, hα, hβ, hαβ, hsp⟩ := hspan t le_rfl htp
  have hA0 : 0 ≤ A := by linarith
  have hb1 := liftPt_mul_span_bounds a hn r k _ _ hsp
  have hDt1 : D / t < 1 := by
    rw [div_lt_one ht0]
    exact hDt
  rw [arcCount_eq_ncard a ha hn x _ (div_nonneg hD ht0.le) hDt1]
  have hE' : E = q * ((k : ℝ) * r) := by
    rw [hq]
    field_simp
  have hK : ∀ u, 0 ≤ u → u < E / ((1 + q) * t) →
      (Set.ncard {j : ℤ | x < liftPt a ⌊t⌋₊ j ∧ liftPt a ⌊t⌋₊ j ≤ x + D / t} : ℝ) ≤
        (Set.ncard {j : ℤ | x - k * (α + A) / t + u < liftPt a ⌊(1 + q) * t⌋₊ j ∧
          liftPt a ⌊(1 + q) * t⌋₊ j ≤ x + D / t + k * (β + A) / t + u} : ℝ) := by
    intro u hu0 hul
    have hul' : u * ((1 + q) * t) < q * ((k : ℝ) * r) := by
      have : u * ((1 + q) * t) < E := by rwa [lt_div_iff₀ htp0] at hul
      linarith
    obtain ⟨s, hts, hst, hsu⟩ :=
      exists_time_later t q ((k : ℝ) * r) u ht0 (by linarith) hq0.le hu0 hul'
    obtain ⟨α', β', hα', hβ', hαβ', hsp'⟩ := hspan s hts hst
    have hns : 0 < ⌊s⌋₊ := Nat.floor_pos.2 (le_trans ht hts)
    have hb2 := liftPt_mul_span_bounds a hns r k _ _ hsp'
    have hC1 := ncard_liftPt_le_fwd_bwd a ha hn (Nat.floor_mono hts) (Nat.floor_mono hst) (k * r)
      _ _ _ _ hb1 hb2 x (x + D / t)
    refine le_trans (Nat.cast_le.2 hC1) (Nat.cast_le.2 (ncard_liftPt_mono a hnp0 ?_ ?_))
    · have e1 : (k : ℝ) * ((r - α) / t) = k * r / t - k * α / t := by ring
      have e2 : (k : ℝ) * ((r + β') / s) = k * r / s + k * β' / s := by ring
      have e3 : (k : ℝ) * β' / s ≤ k * A / t :=
        div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
          ht0 hts
      have e4 : (k : ℝ) * (α + A) / t = k * α / t + k * A / t := by ring
      rw [e1, e2, e4]
      linarith
    · have e1 : (k : ℝ) * ((r + β) / t) = k * r / t + k * β / t := by ring
      have e2 : (k : ℝ) * ((r - α') / s) = k * r / s - k * α' / s := by ring
      have e3 : (k : ℝ) * α' / s ≤ k * A / t :=
        div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
          ht0 hts
      have e4 : (k : ℝ) * (β + A) / t = k * β / t + k * A / t := by ring
      rw [e1, e2, e4]
      linarith
  have hY : ∀ v, x - k * (α + A) / t ≤ v →
      (Set.ncard {j : ℤ | v < liftPt a ⌊(1 + q) * t⌋₊ j ∧
        liftPt a ⌊(1 + q) * t⌋₊ j ≤ v + E / ((1 + q) * t)} : ℝ) ≤ c := by
    intro v _
    rw [← arcCount_eq_ncard a ha hnp0 v _ hℓ0.le hℓ1]
    exact hc v
  have hcd : x - k * (α + A) / t ≤ x + D / t + k * (β + A) / t := by
    have e1 : 0 ≤ (k : ℝ) * (α + A) / t := by positivity
    have e2 : 0 ≤ (k : ℝ) * (β + A) / t := by positivity
    have e3 : 0 ≤ D / t := by positivity
    linarith
  have key := avg_translates_le
    (fun v w => (Set.ncard {j : ℤ | v < liftPt a ⌊(1 + q) * t⌋₊ j ∧
      liftPt a ⌊(1 + q) * t⌋₊ j ≤ w} : ℝ))
    (fun _ _ => Nat.cast_nonneg _)
    (fun v w z hvw hwz => by
      rw [ncard_liftPt_Ioc_add a hnp0 hvw hwz, Nat.cast_add])
    (x - k * (α + A) / t) (x + D / t + k * (β + A) / t) (E / ((1 + q) * t))
    _ c hcd hℓ0 hK hY
  have hdc : (x + D / t + k * (β + A) / t - (x - k * (α + A) / t)) / (E / ((1 + q) * t)) ≤
      (D + 3 * (k : ℝ) * A) * (1 + q) / E := by
    rw [div_le_div_iff₀ hℓ0 hE]
    have e : (D + 3 * (k : ℝ) * A) * (1 + q) * (E / ((1 + q) * t)) = (D + 3 * k * A) / t * E := by
      field_simp
    rw [e]
    apply mul_le_mul_of_nonneg_right _ hE.le
    have e2 : x + D / t + k * (β + A) / t - (x - k * (α + A) / t) =
        (D + k * (α + β) + 2 * k * A) / t := by ring
    rw [e2]
    apply div_le_div_of_nonneg_right _ ht0.le
    nlinarith [mul_le_mul_of_nonneg_left hαβ (show (0 : ℝ) ≤ k by positivity)]
  exact le_trans key (mul_le_mul_of_nonneg_right hdc hc0)

/-- C2b (Korsky (2.3), before division by `D`): counts at time `t` on arcs of length `D / t`,
from a uniform lower bound `c` at the earlier time `(1 - q) * t` on arcs of length
`E / ((1 - q) * t)`. -/
theorem le_arcCount_of_earlier (a : ℕ → ℝ) (ha : Function.Injective fun k => Int.fract (a k))
    (r k : ℕ) (hr : 1 ≤ r) (hk : 1 ≤ k) (A D E q c t : ℝ) (hD : 0 ≤ D) (hE : 0 < E)
    (hq : q = E / ((k : ℝ) * r)) (hq1 : q < 1) (ht : 1 ≤ (1 - q) * t) (hDt : D < t)
    (hEt : E < (1 - q) * t)
    (hspan : ∀ s : ℝ, (1 - q) * t ≤ s → s ≤ t → SpanControl a r A s) (hc0 : 0 ≤ c)
    (hc : ∀ v : ℝ, c ≤ (arcCount a ⌊(1 - q) * t⌋₊ v (E / ((1 - q) * t)) : ℝ)) (x : ℝ) :
    (D * (1 - q) - (k : ℝ) * A * (3 - q)) / E * c ≤ (arcCount a ⌊t⌋₊ x (D / t) : ℝ) := by
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hκ : (1 : ℝ) ≤ (k : ℝ) * r := by nlinarith
  have hq0 : 0 < q := by
    rw [hq]
    exact div_pos hE (by linarith)
  have h1q : 0 < 1 - q := by linarith
  have htm0 : 0 < (1 - q) * t := by linarith
  have ht0 : 0 < t := pos_of_mul_pos_right htm0 h1q.le
  have htm : (1 - q) * t ≤ t := by nlinarith
  have h1q' : (1 : ℝ) - q ≠ 0 := h1q.ne'
  have ht0' : t ≠ 0 := ht0.ne'
  have hE0 : E ≠ 0 := hE.ne'
  have hnm : 0 < ⌊(1 - q) * t⌋₊ := Nat.floor_pos.2 ht
  have hnn : ⌊(1 - q) * t⌋₊ ≤ ⌊t⌋₊ := Nat.floor_mono htm
  have hn : 0 < ⌊t⌋₊ := lt_of_lt_of_le hnm hnn
  have hℓ0 : 0 < E / ((1 - q) * t) := div_pos hE htm0
  have hℓ1 : E / ((1 - q) * t) < 1 := by
    rw [div_lt_one htm0]
    exact hEt
  obtain ⟨α, β, hα, hβ, hαβ, hsp⟩ := hspan t htm le_rfl
  have hA0 : 0 ≤ A := by linarith
  have hb1 := liftPt_mul_span_bounds a hn r k _ _ hsp
  have hDt1 : D / t < 1 := by
    rw [div_lt_one ht0]
    exact hDt
  rw [arcCount_eq_ncard a ha hn x _ (div_nonneg hD ht0.le) hDt1]
  have hE' : E = q * ((k : ℝ) * r) := by
    rw [hq]
    field_simp
  have hW : (D * (1 - q) - (k : ℝ) * A * (3 - q)) / E =
      (D / t - k * A / t - 2 * (k * A / ((1 - q) * t))) / (E / ((1 - q) * t)) := by
    field_simp
    ring
  have hdc : D / t - k * A / t - 2 * (k * A / ((1 - q) * t)) ≤
      (x + D / t - k * β / t - k * A / ((1 - q) * t)) -
        (x + k * α / t + k * A / ((1 - q) * t)) := by
    have e1 : (k : ℝ) * (α + β) / t ≤ k * A / t :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hαβ (by positivity)) ht0.le
    have e2 : (k : ℝ) * (α + β) / t = k * α / t + k * β / t := by ring
    linarith
  by_cases hcase : x + D / t - k * β / t - k * A / ((1 - q) * t) <
      x + k * α / t + k * A / ((1 - q) * t)
  · have hneg : D * (1 - q) - (k : ℝ) * A * (3 - q) ≤ 0 := by
      have h1 : D / t - k * A / t - 2 * (k * A / ((1 - q) * t)) < 0 := by linarith
      have h2 : D * (1 - q) - (k : ℝ) * A * (3 - q) =
          (D / t - k * A / t - 2 * (k * A / ((1 - q) * t))) * ((1 - q) * t) := by
        field_simp
        ring
      rw [h2]
      exact mul_nonpos_of_nonpos_of_nonneg h1.le htm0.le
    have h3 : (D * (1 - q) - (k : ℝ) * A * (3 - q)) / E * c ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonpos_of_nonneg hneg hE.le) hc0
    exact le_trans h3 (Nat.cast_nonneg _)
  · have hcd := not_lt.1 hcase
    have hK : ∀ u, 0 ≤ u → u < E / ((1 - q) * t) →
        (Set.ncard {j : ℤ | x + k * α / t + k * A / ((1 - q) * t) + u <
          liftPt a ⌊(1 - q) * t⌋₊ j ∧
          liftPt a ⌊(1 - q) * t⌋₊ j ≤ x + D / t - k * β / t - k * A / ((1 - q) * t) + u} : ℝ) ≤
        (Set.ncard {j : ℤ | x < liftPt a ⌊t⌋₊ j ∧ liftPt a ⌊t⌋₊ j ≤ x + D / t} : ℝ) := by
      intro u hu0 hul
      have hul' : u * ((1 - q) * t) < q * ((k : ℝ) * r) := by
        have : u * ((1 - q) * t) < E := by rwa [lt_div_iff₀ htm0] at hul
        linarith
      obtain ⟨s, hts, hst, hsu⟩ :=
        exists_time_earlier t q ((k : ℝ) * r) u ht0 (by linarith) hq0.le hq1 hu0 hul'
      have hs0 : 0 < s := lt_of_lt_of_le htm0 hts
      obtain ⟨α', β', hα', hβ', hαβ', hsp'⟩ := hspan s hts hst
      have hns : 0 < ⌊s⌋₊ := Nat.floor_pos.2 (le_trans ht hts)
      have hb2 := liftPt_mul_span_bounds a hns r k _ _ hsp'
      have hC1 := ncard_liftPt_le_bwd_fwd a ha hnm (Nat.floor_mono hts) (Nat.floor_mono hst)
        (k * r) _ _ _ _ hb2 hb1 (x + k * α / t + k * A / ((1 - q) * t) + u)
        (x + D / t - k * β / t - k * A / ((1 - q) * t) + u)
      refine le_trans (Nat.cast_le.2 hC1) (Nat.cast_le.2 (ncard_liftPt_mono a hn ?_ ?_))
      · have e1 : (k : ℝ) * ((r + β') / s) = k * r / s + k * β' / s := by ring
        have e2 : (k : ℝ) * ((r - α) / t) = k * r / t - k * α / t := by ring
        have e3 : (k : ℝ) * β' / s ≤ k * A / ((1 - q) * t) :=
          div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
            htm0 hts
        rw [e1, e2]
        linarith
      · have e1 : (k : ℝ) * ((r - α') / s) = k * r / s - k * α' / s := by ring
        have e2 : (k : ℝ) * ((r + β) / t) = k * r / t + k * β / t := by ring
        have e3 : (k : ℝ) * α' / s ≤ k * A / ((1 - q) * t) :=
          div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
            htm0 hts
        rw [e1, e2]
        linarith
    have hY : ∀ v, x + k * α / t + k * A / ((1 - q) * t) ≤ v →
        c ≤ (Set.ncard {j : ℤ | v < liftPt a ⌊(1 - q) * t⌋₊ j ∧
          liftPt a ⌊(1 - q) * t⌋₊ j ≤ v + E / ((1 - q) * t)} : ℝ) := by
      intro v _
      rw [← arcCount_eq_ncard a ha hnm v _ hℓ0.le hℓ1]
      exact hc v
    have key := le_avg_translates
      (fun v w => (Set.ncard {j : ℤ | v < liftPt a ⌊(1 - q) * t⌋₊ j ∧
        liftPt a ⌊(1 - q) * t⌋₊ j ≤ w} : ℝ))
      (fun _ _ => Nat.cast_nonneg _)
      (fun v w z hvw hwz => by
        rw [ncard_liftPt_Ioc_add a hnm hvw hwz, Nat.cast_add])
      (x + k * α / t + k * A / ((1 - q) * t)) (x + D / t - k * β / t - k * A / ((1 - q) * t))
      (E / ((1 - q) * t)) _ c hcd hℓ0 hc0 hK hY
    rw [hW]
    refine le_trans ?_ key
    apply mul_le_mul_of_nonneg_right _ hc0
    exact div_le_div_of_nonneg_right hdc hℓ0.le

/-- C2a for all large times, uniformly for `D` in a bounded range. -/
theorem eventually_arcCount_le_of_later (a : ℕ → ℝ)
    (ha : Function.Injective fun k => Int.fract (a k))
    (r k : ℕ) (hr : 1 ≤ r) (hk : 1 ≤ k) (A E c Dmax : ℝ) (hE : 0 < E)
    (hq1 : E / ((k : ℝ) * r) < 1) (hSC : ∃ T : ℝ, ∀ s ≥ T, SpanControl a r A s)
    (h : ∀ᶠ t : ℝ in atTop, ∀ v : ℝ, (arcCount a ⌊t⌋₊ v (E / t) : ℝ) ≤ c) :
    ∀ᶠ t : ℝ in atTop, ∀ D x : ℝ, 0 ≤ D → D ≤ Dmax →
      (arcCount a ⌊t⌋₊ x (D / t) : ℝ) ≤
        (D + 3 * (k : ℝ) * A) * (1 + E / ((k : ℝ) * r)) / E * c := by
  obtain ⟨T, hT⟩ := hSC
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hq0 : 0 < E / ((k : ℝ) * r) := div_pos hE (mul_pos (by linarith) (by linarith))
  have hmul : Tendsto (fun t : ℝ => (1 + E / ((k : ℝ) * r)) * t) atTop atTop :=
    tendsto_id.const_mul_atTop (by linarith)
  have h' := hmul.eventually h
  filter_upwards [h', eventually_ge_atTop T, eventually_ge_atTop 1, eventually_gt_atTop Dmax,
    eventually_gt_atTop E] with t ht1 ht2 ht3 ht4 ht5
  intro D x hD hDm
  have htp : t ≤ (1 + E / ((k : ℝ) * r)) * t := by nlinarith
  exact arcCount_le_of_later a ha r k hr hk A D E _ c t hD hE rfl hq1 ht3 (by linarith)
    (by linarith) (fun s hs1 _ => hT s (by linarith)) ht1 x

/-- C2b for all large times, uniformly for `D` in a bounded range. -/
theorem eventually_le_arcCount_of_earlier (a : ℕ → ℝ)
    (ha : Function.Injective fun k => Int.fract (a k))
    (r k : ℕ) (hr : 1 ≤ r) (hk : 1 ≤ k) (A E c Dmax : ℝ) (hE : 0 < E)
    (hq1 : E / ((k : ℝ) * r) < 1) (hc0 : 0 ≤ c) (hSC : ∃ T : ℝ, ∀ s ≥ T, SpanControl a r A s)
    (h : ∀ᶠ t : ℝ in atTop, ∀ v : ℝ, c ≤ (arcCount a ⌊t⌋₊ v (E / t) : ℝ)) :
    ∀ᶠ t : ℝ in atTop, ∀ D x : ℝ, 0 ≤ D → D ≤ Dmax →
      (D * (1 - E / ((k : ℝ) * r)) - (k : ℝ) * A * (3 - E / ((k : ℝ) * r))) / E * c ≤
        (arcCount a ⌊t⌋₊ x (D / t) : ℝ) := by
  obtain ⟨T, hT⟩ := hSC
  have hmul : Tendsto (fun t : ℝ => (1 - E / ((k : ℝ) * r)) * t) atTop atTop :=
    tendsto_id.const_mul_atTop (by linarith)
  have h' := hmul.eventually h
  have h'' := hmul.eventually (eventually_ge_atTop (max T (max 1 (E + 1))))
  filter_upwards [h', h'', eventually_gt_atTop Dmax, eventually_gt_atTop 0] with t ht1 ht2 ht3 ht4
  intro D x hD hDm
  have ht2' : max T (max 1 (E + 1)) ≤ (1 - E / ((k : ℝ) * r)) * t := ht2
  have e1 : T ≤ (1 - E / ((k : ℝ) * r)) * t := le_trans (le_max_left _ _) ht2'
  have e2 : 1 ≤ (1 - E / ((k : ℝ) * r)) * t :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) ht2'
  have e3 : E + 1 ≤ (1 - E / ((k : ℝ) * r)) * t :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) ht2'
  exact le_arcCount_of_earlier a ha r k hr hk A D E _ c t hD hE rfl hq1 e2 (by linarith)
    (by linarith) (fun s hs1 _ => hT s (by linarith)) hc0 ht1 x

/- ## W: the crude finite-prefix discrepancy bound (builder: Neon) -/

noncomputable def blockMax {N : ℕ} (z : Fin N → ℝ) (a b : ℕ) (h : a ≤ b) (x : ℝ) : ℝ :=
  (Finset.Icc a b).sup' (Finset.nonempty_Icc.mpr h) (fun n => prefixErr z n x)

noncomputable def blockMin {N : ℕ} (z : Fin N → ℝ) (a b : ℕ) (h : a ≤ b) (x : ℝ) : ℝ :=
  (Finset.Icc a b).inf' (Finset.nonempty_Icc.mpr h) (fun n => prefixErr z n x)

noncomputable def blockOsc {N : ℕ} (z : Fin N → ℝ) (a b : ℕ) (h : a ≤ b) (x : ℝ) : ℝ :=
  blockMax z a b h x - blockMin z a b h x

noncomputable def fullOsc {N : ℕ} (z : Fin N → ℝ) (x : ℝ) : ℝ :=
  blockOsc z 0 N (Nat.zero_le N) x

lemma blockOsc_nonneg {N : ℕ} (z : Fin N → ℝ) (a b : ℕ) (h : a ≤ b) (x : ℝ) :
    0 ≤ blockOsc z a b h x := by
  have ha : a ∈ Finset.Icc a b := Finset.mem_Icc.mpr ⟨le_rfl, h⟩
  have h1 : blockMin z a b h x ≤ prefixErr z a x :=
    Finset.inf'_le (f := fun n => prefixErr z n x) ha
  have h2 : prefixErr z a x ≤ blockMax z a b h x :=
    Finset.le_sup' (f := fun n => prefixErr z n x) ha
  unfold blockOsc
  linarith

lemma fullOsc_nonneg {N : ℕ} (z : Fin N → ℝ) (x : ℝ) : 0 ≤ fullOsc z x :=
  blockOsc_nonneg z 0 N (Nat.zero_le N) x

lemma blockMax_le_of_subset {N : ℕ} (z : Fin N → ℝ) {a₁ b₁ a₂ b₂ : ℕ}
    (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂) (ha : a₂ ≤ a₁) (hb : b₁ ≤ b₂) (x : ℝ) :
    blockMax z a₁ b₁ h₁ x ≤ blockMax z a₂ b₂ h₂ x := by
  unfold blockMax
  refine Finset.sup'_le _ _ fun n hn => ?_
  have hmem : n ∈ Finset.Icc a₂ b₂ := by
    have h' := Finset.mem_Icc.mp hn
    exact Finset.mem_Icc.mpr ⟨le_trans ha h'.1, le_trans h'.2 hb⟩
  exact Finset.le_sup' (f := fun n => prefixErr z n x) hmem

lemma blockMin_le_of_subset {N : ℕ} (z : Fin N → ℝ) {a₁ b₁ a₂ b₂ : ℕ}
    (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂) (ha : a₂ ≤ a₁) (hb : b₁ ≤ b₂) (x : ℝ) :
    blockMin z a₂ b₂ h₂ x ≤ blockMin z a₁ b₁ h₁ x := by
  unfold blockMin
  refine Finset.le_inf' _ _ fun n hn => ?_
  have hmem : n ∈ Finset.Icc a₂ b₂ := by
    have h' := Finset.mem_Icc.mp hn
    exact Finset.mem_Icc.mpr ⟨le_trans ha h'.1, le_trans h'.2 hb⟩
  exact Finset.inf'_le (f := fun n => prefixErr z n x) hmem

lemma real_max_min_split {U U₀ U₂ L L₀ L₂ : ℝ}
    (hU₀ : U₀ ≤ U) (hU₂ : U₂ ≤ U) (hL₀ : L ≤ L₀) (hL₂ : L ≤ L₂) :
    (U₀ - L₀) + (U₂ - L₂) + |U₂ - U₀| + |L₂ - L₀| ≤ 2 * (U - L) := by
  rcases le_total U₀ U₂ with hU | hU <;> rcases le_total L₀ L₂ with hL | hL
  · rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith
  · rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]; linarith
  · rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]; linarith
  · rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith

lemma fullOsc_split {M N : ℕ} (hN : 3 * M = N) (w : Fin N → ℝ) (x : ℝ) :
    blockOsc w 0 M (Nat.zero_le M) x + blockOsc w (2 * M) N (by omega) x +
      |blockMax w (2 * M) N (by omega) x - blockMax w 0 M (Nat.zero_le M) x| +
      |blockMin w (2 * M) N (by omega) x - blockMin w 0 M (Nat.zero_le M) x| ≤
    2 * fullOsc w x := by
  unfold fullOsc blockOsc
  exact real_max_min_split
    (blockMax_le_of_subset w (Nat.zero_le M) (Nat.zero_le N) le_rfl (by omega) x)
    (blockMax_le_of_subset w (by omega) (Nat.zero_le N) (Nat.zero_le _) le_rfl x)
    (blockMin_le_of_subset w (Nat.zero_le M) (Nat.zero_le N) le_rfl (by omega) x)
    (blockMin_le_of_subset w (by omega) (Nat.zero_le N) (Nat.zero_le _) le_rfl x)

def headList {M N : ℕ} (hN : 3 * M = N) (w : Fin N → ℝ) : Fin M → ℝ :=
  fun i => w ⟨i.1, by omega⟩

def tailList {M N : ℕ} (hN : 3 * M = N) (w : Fin N → ℝ) : Fin M → ℝ :=
  fun i => w ⟨2 * M + i.1, by omega⟩

lemma err_headList {M N : ℕ} (hN : 3 * M = N) (w : Fin N → ℝ) {k : ℕ} (hk : k ≤ M) (x : ℝ) :
    prefixErr w k x = prefixErr (headList hN w) k x := by
  unfold prefixErr
  have hcard :
      (Finset.univ.filter (fun i : Fin N => (i : ℕ) < k ∧ w i ≤ x)).card =
      (Finset.univ.filter (fun j : Fin M => (j : ℕ) < k ∧ headList hN w j ≤ x)).card := by
    symm
    refine Finset.card_bij (fun j _ => (⟨j.1, by omega⟩ : Fin N)) ?_ ?_ ?_
    · intro j hj
      have hj' := (Finset.mem_filter.mp hj).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj'⟩
    · intro j₁ _ j₂ _ heq
      exact Fin.ext (Fin.mk.inj heq)
    · intro i hi
      have hi' := (Finset.mem_filter.mp hi).2
      have hilt : (i : ℕ) < k := hi'.1
      refine ⟨⟨i.1, by omega⟩, ?_, Fin.ext rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hilt, hi'.2⟩
  rw [hcard]

lemma blockMax_headList {M N : ℕ} (hN : 3 * M = N) (w : Fin N → ℝ) (x : ℝ) :
    blockMax w 0 M (Nat.zero_le M) x = blockMax (headList hN w) 0 M (Nat.zero_le M) x := by
  unfold blockMax
  refine Finset.sup'_congr _ rfl fun k hk => ?_
  exact err_headList hN w (Finset.mem_Icc.mp hk).2 x

lemma blockMin_headList {M N : ℕ} (hN : 3 * M = N) (w : Fin N → ℝ) (x : ℝ) :
    blockMin w 0 M (Nat.zero_le M) x = blockMin (headList hN w) 0 M (Nat.zero_le M) x := by
  unfold blockMin
  refine Finset.inf'_congr _ rfl fun k hk => ?_
  exact err_headList hN w (Finset.mem_Icc.mp hk).2 x

lemma blockOsc_headList {M N : ℕ} (hN : 3 * M = N) (w : Fin N → ℝ) (x : ℝ) :
    blockOsc w 0 M (Nat.zero_le M) x = fullOsc (headList hN w) x := by
  unfold fullOsc blockOsc
  rw [blockMax_headList hN w x, blockMin_headList hN w x]

lemma err_tailList {M N : ℕ} (hN : 3 * M = N) (w : Fin N → ℝ) (k : ℕ) (x : ℝ) :
    prefixErr w (2 * M + k) x = prefixErr w (2 * M) x + prefixErr (tailList hN w) k x := by
  unfold prefixErr
  let sAll := Finset.univ.filter (fun i : Fin N => (i : ℕ) < 2 * M + k ∧ w i ≤ x)
  let sLo := Finset.univ.filter (fun i : Fin N => (i : ℕ) < 2 * M ∧ w i ≤ x)
  let sHi := Finset.univ.filter (fun i : Fin N => 2 * M ≤ (i : ℕ) ∧ (i : ℕ) < 2 * M + k ∧ w i ≤ x)
  let sTail := Finset.univ.filter (fun j : Fin M => (j : ℕ) < k ∧ tailList hN w j ≤ x)
  have hunion : sAll = sLo ∪ sHi := by
    ext i
    simp only [sAll, sLo, sHi, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro ⟨h1, h2⟩
      by_cases hlt : (i : ℕ) < 2 * M
      · exact Or.inl ⟨hlt, h2⟩
      · exact Or.inr ⟨by omega, h1, h2⟩
    · intro h
      rcases h with ⟨h1, h2⟩ | ⟨_, h1, h2⟩
      · exact ⟨by omega, h2⟩
      · exact ⟨h1, h2⟩
  have hdisj : Disjoint sLo sHi := by
    refine Finset.disjoint_filter.mpr fun i _ h1 h2 => ?_
    omega
  have hbij : sTail.card = sHi.card := by
    refine Finset.card_bij (fun j _ => (⟨2 * M + j.1, by omega⟩ : Fin N)) ?_ ?_ ?_
    · intro j hj
      have hj' := (Finset.mem_filter.mp hj).2
      have hjlt : (j : ℕ) < k := hj'.1
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp; omega, by dsimp; omega, hj'.2⟩
    · intro j₁ _ j₂ _ heq
      have hval : 2 * M + j₁.1 = 2 * M + j₂.1 := Fin.mk.inj heq
      exact Fin.ext (by omega)
    · intro i hi
      have hi' := (Finset.mem_filter.mp hi).2
      have hge : 2 * M ≤ (i : ℕ) := hi'.1
      have hlt : (i : ℕ) < 2 * M + k := hi'.2.1
      refine ⟨⟨i.1 - 2 * M, by omega⟩, ?_, Fin.ext (by dsimp; omega)⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp; omega, ?_⟩
      change w ⟨2 * M + (i.1 - 2 * M), _⟩ ≤ x
      have hidx : (⟨2 * M + (i.1 - 2 * M), by omega⟩ : Fin N) = i := Fin.ext (by dsimp; omega)
      rw [hidx]
      exact hi'.2.2
  have hcard : sAll.card = sLo.card + sTail.card := by
    rw [hunion, Finset.card_union_of_disjoint hdisj, hbij]
  change (sAll.card : ℝ) - ((2 * M + k : ℕ) : ℝ) * x =
    ((sLo.card : ℝ) - ((2 * M : ℕ) : ℝ) * x) + ((sTail.card : ℝ) - (k : ℝ) * x)
  rw [hcard]
  push_cast
  ring

lemma blockMax_tailList {M N : ℕ} (hN : 3 * M = N) (w : Fin N → ℝ) (x : ℝ) :
    blockMax w (2 * M) N (by omega) x =
      prefixErr w (2 * M) x + blockMax (tailList hN w) 0 M (Nat.zero_le M) x := by
  apply le_antisymm
  · unfold blockMax
    refine Finset.sup'_le _ _ fun n hn => ?_
    have hn' := Finset.mem_Icc.mp hn
    have hk : n - 2 * M ≤ M := by omega
    have hnk : 2 * M + (n - 2 * M) = n := by omega
    have heq : prefixErr w n x =
        prefixErr w (2 * M) x + prefixErr (tailList hN w) (n - 2 * M) x := by
      have h := err_tailList hN w (n - 2 * M) x
      rwa [hnk] at h
    have hle : prefixErr (tailList hN w) (n - 2 * M) x ≤
        (Finset.Icc 0 M).sup' (Finset.nonempty_Icc.mpr (Nat.zero_le M))
          (fun k => prefixErr (tailList hN w) k x) :=
      Finset.le_sup' (f := fun k => prefixErr (tailList hN w) k x)
        (Finset.mem_Icc.mpr ⟨Nat.zero_le _, hk⟩)
    linarith
  · suffices h : blockMax (tailList hN w) 0 M (Nat.zero_le M) x ≤
        blockMax w (2 * M) N (by omega) x - prefixErr w (2 * M) x by linarith
    unfold blockMax
    refine Finset.sup'_le _ _ fun k hk => ?_
    have hk' := Finset.mem_Icc.mp hk
    have heq := err_tailList hN w k x
    have hle : prefixErr w (2 * M + k) x ≤
        (Finset.Icc (2 * M) N).sup' (Finset.nonempty_Icc.mpr (by omega))
          (fun n => prefixErr w n x) :=
      Finset.le_sup' (f := fun n => prefixErr w n x)
        (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    linarith

lemma blockMin_tailList {M N : ℕ} (hN : 3 * M = N) (w : Fin N → ℝ) (x : ℝ) :
    blockMin w (2 * M) N (by omega) x =
      prefixErr w (2 * M) x + blockMin (tailList hN w) 0 M (Nat.zero_le M) x := by
  apply le_antisymm
  · suffices h : blockMin w (2 * M) N (by omega) x - prefixErr w (2 * M) x ≤
        blockMin (tailList hN w) 0 M (Nat.zero_le M) x by linarith
    unfold blockMin
    refine Finset.le_inf' _ _ fun k hk => ?_
    have hk' := Finset.mem_Icc.mp hk
    have heq := err_tailList hN w k x
    have hle :
        (Finset.Icc (2 * M) N).inf' (Finset.nonempty_Icc.mpr (by omega))
          (fun n => prefixErr w n x) ≤ prefixErr w (2 * M + k) x :=
      Finset.inf'_le (f := fun n => prefixErr w n x)
        (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    linarith
  · unfold blockMin
    refine Finset.le_inf' _ _ fun n hn => ?_
    have hn' := Finset.mem_Icc.mp hn
    have hk : n - 2 * M ≤ M := by omega
    have hnk : 2 * M + (n - 2 * M) = n := by omega
    have heq : prefixErr w n x =
        prefixErr w (2 * M) x + prefixErr (tailList hN w) (n - 2 * M) x := by
      have h := err_tailList hN w (n - 2 * M) x
      rwa [hnk] at h
    have hle :
        (Finset.Icc 0 M).inf' (Finset.nonempty_Icc.mpr (Nat.zero_le M))
          (fun k => prefixErr (tailList hN w) k x) ≤
        prefixErr (tailList hN w) (n - 2 * M) x :=
      Finset.inf'_le (f := fun k => prefixErr (tailList hN w) k x)
        (Finset.mem_Icc.mpr ⟨Nat.zero_le _, hk⟩)
    linarith

lemma blockOsc_tailList {M N : ℕ} (hN : 3 * M = N) (w : Fin N → ℝ) (x : ℝ) :
    blockOsc w (2 * M) N (by omega) x = fullOsc (tailList hN w) x := by
  unfold fullOsc blockOsc
  rw [blockMax_tailList hN w x, blockMin_tailList hN w x]
  ring

noncomputable def countLe {N : ℕ} (w : Fin N → ℝ) (x : ℝ) : ℕ :=
  (Finset.univ.filter (fun i : Fin N => w i ≤ x)).card

lemma countLe_lt {N : ℕ} (w : Fin N → ℝ) (x : ℝ) : countLe w x < N + 1 := by
  unfold countLe
  have hle : (Finset.univ.filter (fun i : Fin N => w i ≤ x)).card ≤ (Finset.univ : Finset (Fin N)).card :=
    Finset.card_filter_le _ _
  rw [Finset.card_univ, Fintype.card_fin] at hle
  omega

lemma err_sub_of_countLe_eq {N : ℕ} (w : Fin N → ℝ) {x y : ℝ}
    (hxy : x ≤ y) (hk : countLe w x = countLe w y) (n : ℕ) :
    prefixErr w n y = prefixErr w n x - (n : ℝ) * (y - x) := by
  have hsub :
      Finset.univ.filter (fun i : Fin N => w i ≤ x) ⊆
      Finset.univ.filter (fun i : Fin N => w i ≤ y) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact le_trans hi hxy
  have heqSet :
      Finset.univ.filter (fun i : Fin N => w i ≤ x) =
      Finset.univ.filter (fun i : Fin N => w i ≤ y) :=
    Finset.eq_of_subset_of_card_le hsub (le_of_eq hk.symm)
  have hiff : ∀ i : Fin N, w i ≤ x ↔ w i ≤ y := by
    intro i
    have h := Finset.ext_iff.mp heqSet i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
    exact h
  have hfilt :
      Finset.univ.filter (fun i : Fin N => (i : ℕ) < n ∧ w i ≤ y) =
      Finset.univ.filter (fun i : Fin N => (i : ℕ) < n ∧ w i ≤ x) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hiff i]
  unfold prefixErr
  rw [hfilt]
  ring

lemma blockMax_le_of_countLe_eq {N : ℕ} (w : Fin N → ℝ) {a b : ℕ} (hab : a ≤ b)
    {x y : ℝ} (hxy : x ≤ y) (hk : countLe w x = countLe w y) :
    blockMax w a b hab y ≤ blockMax w a b hab x - (a : ℝ) * (y - x) := by
  unfold blockMax
  refine Finset.sup'_le _ _ fun n hn => ?_
  have hn' := Finset.mem_Icc.mp hn
  have heq := err_sub_of_countLe_eq w hxy hk n
  have hmul : (a : ℝ) * (y - x) ≤ (n : ℝ) * (y - x) :=
    mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hn'.1) (sub_nonneg.mpr hxy)
  have hle : prefixErr w n x ≤
      (Finset.Icc a b).sup' (Finset.nonempty_Icc.mpr hab) (fun m => prefixErr w m x) :=
    Finset.le_sup' (f := fun m => prefixErr w m x) hn
  linarith

lemma blockMax_ge_of_countLe_eq {N : ℕ} (w : Fin N → ℝ) {a b : ℕ} (hab : a ≤ b)
    {x y : ℝ} (hxy : x ≤ y) (hk : countLe w x = countLe w y) :
    blockMax w a b hab x - (b : ℝ) * (y - x) ≤ blockMax w a b hab y := by
  suffices h : blockMax w a b hab x ≤ blockMax w a b hab y + (b : ℝ) * (y - x) by linarith
  unfold blockMax
  refine Finset.sup'_le _ _ fun n hn => ?_
  have hn' := Finset.mem_Icc.mp hn
  have heq := err_sub_of_countLe_eq w hxy hk n
  have hmul : (n : ℝ) * (y - x) ≤ (b : ℝ) * (y - x) :=
    mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hn'.2) (sub_nonneg.mpr hxy)
  have hle : prefixErr w n y ≤
      (Finset.Icc a b).sup' (Finset.nonempty_Icc.mpr hab) (fun m => prefixErr w m y) :=
    Finset.le_sup' (f := fun m => prefixErr w m y) hn
  linarith

lemma blockMin_le_of_countLe_eq {N : ℕ} (w : Fin N → ℝ) {a b : ℕ} (hab : a ≤ b)
    {x y : ℝ} (hxy : x ≤ y) (hk : countLe w x = countLe w y) :
    blockMin w a b hab y ≤ blockMin w a b hab x - (a : ℝ) * (y - x) := by
  suffices h : blockMin w a b hab y + (a : ℝ) * (y - x) ≤ blockMin w a b hab x by linarith
  unfold blockMin
  refine Finset.le_inf' _ _ fun n hn => ?_
  have hn' := Finset.mem_Icc.mp hn
  have heq := err_sub_of_countLe_eq w hxy hk n
  have hmul : (a : ℝ) * (y - x) ≤ (n : ℝ) * (y - x) :=
    mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hn'.1) (sub_nonneg.mpr hxy)
  have hle :
      (Finset.Icc a b).inf' (Finset.nonempty_Icc.mpr hab) (fun m => prefixErr w m y) ≤
      prefixErr w n y :=
    Finset.inf'_le (f := fun m => prefixErr w m y) hn
  linarith

lemma blockMin_ge_of_countLe_eq {N : ℕ} (w : Fin N → ℝ) {a b : ℕ} (hab : a ≤ b)
    {x y : ℝ} (hxy : x ≤ y) (hk : countLe w x = countLe w y) :
    blockMin w a b hab x - (b : ℝ) * (y - x) ≤ blockMin w a b hab y := by
  unfold blockMin
  refine Finset.le_inf' _ _ fun n hn => ?_
  have hn' := Finset.mem_Icc.mp hn
  have heq := err_sub_of_countLe_eq w hxy hk n
  have hmul : (n : ℝ) * (y - x) ≤ (b : ℝ) * (y - x) :=
    mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hn'.2) (sub_nonneg.mpr hxy)
  have hle :
      (Finset.Icc a b).inf' (Finset.nonempty_Icc.mpr hab) (fun m => prefixErr w m x) ≤
      prefixErr w n x :=
    Finset.inf'_le (f := fun m => prefixErr w m x) hn
  linarith

lemma maxDiff_slope {M N : ℕ} (hN : 3 * M = N) (w : Fin N → ℝ) {x y : ℝ}
    (hxy : x ≤ y) (hk : countLe w x = countLe w y) :
    (M : ℝ) * (y - x) ≤
      (blockMax w (2 * M) N (by omega) x - blockMax w 0 M (Nat.zero_le M) x) -
      (blockMax w (2 * M) N (by omega) y - blockMax w 0 M (Nat.zero_le M) y) := by
  have h2 := blockMax_le_of_countLe_eq w (a := 2 * M) (b := N) (by omega) hxy hk
  have h0 := blockMax_ge_of_countLe_eq w (a := 0) (b := M) (Nat.zero_le M) hxy hk
  push_cast at h2
  linarith

lemma minDiff_slope {M N : ℕ} (hN : 3 * M = N) (w : Fin N → ℝ) {x y : ℝ}
    (hxy : x ≤ y) (hk : countLe w x = countLe w y) :
    (M : ℝ) * (y - x) ≤
      (blockMin w (2 * M) N (by omega) x - blockMin w 0 M (Nat.zero_le M) x) -
      (blockMin w (2 * M) N (by omega) y - blockMin w 0 M (Nat.zero_le M) y) := by
  have h2 := blockMin_le_of_countLe_eq w (a := 2 * M) (b := N) (by omega) hxy hk
  have h0 := blockMin_ge_of_countLe_eq w (a := 0) (b := M) (Nat.zero_le M) hxy hk
  push_cast at h2
  linarith

lemma sum_abs_ge_of_fiber_slope
    {M N G : ℕ} (hM : 1 ≤ M) (hN : 3 * M = N) (hG : 4 * (N + 1) ≤ G)
    (κ : ℕ → ℕ) (hκ : ∀ m < G, κ m < N + 1)
    (h : ℕ → ℝ)
    (hslope : ∀ m₁ m₂, m₁ ≤ m₂ → m₂ < G → κ m₁ = κ m₂ →
      (M : ℝ) * (((m₂ : ℝ) - (m₁ : ℝ)) / (G : ℝ)) ≤ h m₁ - h m₂) :
    (G : ℝ) / 64 ≤ ∑ m ∈ Finset.range G, |h m| := by
  have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hG_pos : (0 : ℝ) < (G : ℝ) := by exact_mod_cast (by omega : 0 < G)
  have hN1_pos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  let ρ : ℝ := (M : ℝ) / (4 * ((N : ℝ) + 1))
  have hρ_pos : 0 < ρ := by positivity
  let bad := (Finset.range G).filter (fun m => |h m| < ρ)
  let good := (Finset.range G).filter (fun m => ¬ |h m| < ρ)
  have hfiber : ∀ k : ℕ,
      ((bad.filter (fun m => κ m = k)).card : ℝ) ≤ (G : ℝ) / (2 * ((N : ℝ) + 1)) + 1 := by
    intro k
    let fib := bad.filter (fun m => κ m = k)
    change (fib.card : ℝ) ≤ (G : ℝ) / (2 * ((N : ℝ) + 1)) + 1
    by_cases hne : fib.Nonempty
    · let a := fib.min' hne
      let b := fib.max' hne
      have ha : a ∈ fib := Finset.min'_mem fib hne
      have hb : b ∈ fib := Finset.max'_mem fib hne
      have hab : a ≤ b := Finset.min'_le fib b hb
      have hsub : fib ⊆ Finset.Icc a b := by
        intro m hm
        exact Finset.mem_Icc.mpr ⟨Finset.min'_le fib m hm, Finset.le_max' fib m hm⟩
      have hcard_nat : fib.card ≤ b + 1 - a := by
        have h1 := Finset.card_le_card hsub
        rwa [Nat.card_Icc] at h1
      have hcard_real : (fib.card : ℝ) ≤ (b : ℝ) - (a : ℝ) + 1 := by
        have hcast : (fib.card : ℝ) ≤ ((b + 1 - a : ℕ) : ℝ) := Nat.cast_le.mpr hcard_nat
        have hnat : b + 1 - a + a = b + 1 := by omega
        have hreal : ((b + 1 - a : ℕ) : ℝ) + (a : ℝ) = (b : ℝ) + 1 := by
          exact_mod_cast hnat
        linarith
      have ha_mem := Finset.mem_filter.mp ha
      have hb_mem := Finset.mem_filter.mp hb
      have ha_bad := Finset.mem_filter.mp ha_mem.1
      have hb_bad := Finset.mem_filter.mp hb_mem.1
      have hbG : b < G := Finset.mem_range.mp hb_bad.1
      have hκab : κ a = κ b := ha_mem.2.trans hb_mem.2.symm
      have hha : h a < ρ := (abs_lt.mp ha_bad.2).2
      have hhb : -ρ < h b := (abs_lt.mp hb_bad.2).1
      have hsl := hslope a b hab hbG hκab
      have hdiff_le : (M : ℝ) * (((b : ℝ) - (a : ℝ)) / (G : ℝ)) ≤
          (M : ℝ) / (2 * ((N : ℝ) + 1)) := by
        have h2ρ : 2 * ρ = (M : ℝ) / (2 * ((N : ℝ) + 1)) := by
          dsimp [ρ]
          rw [show (4 * ((N : ℝ) + 1)) = 2 * (2 * ((N : ℝ) + 1)) by ring, ← mul_div_assoc,
            mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)]
        linarith
      have hdiv : ((M : ℝ) * ((b : ℝ) - (a : ℝ))) / (G : ℝ) ≤
          (M : ℝ) / (2 * ((N : ℝ) + 1)) := by
        rwa [mul_div_assoc]
      have hcross : (M : ℝ) * ((b : ℝ) - (a : ℝ)) * (2 * ((N : ℝ) + 1)) ≤ (M : ℝ) * (G : ℝ) :=
        (div_le_div_iff₀ hG_pos (by positivity)).mp hdiv
      have hba_mul : ((b : ℝ) - (a : ℝ)) * (2 * ((N : ℝ) + 1)) ≤ (G : ℝ) := by
        nlinarith
      have hba : (b : ℝ) - (a : ℝ) ≤ (G : ℝ) / (2 * ((N : ℝ) + 1)) :=
        (le_div_iff₀ (by positivity)).mpr hba_mul
      linarith
    · have hempty : fib = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      rw [hempty, Finset.card_empty, Nat.cast_zero]
      positivity
  have hmaps : ∀ m ∈ bad, κ m ∈ Finset.range (N + 1) := by
    intro m hm
    exact Finset.mem_range.mpr (hκ m (Finset.mem_range.mp (Finset.mem_filter.mp hm).1))
  have hbad_eq : bad.card = ∑ k ∈ Finset.range (N + 1), (bad.filter (fun m => κ m = k)).card :=
    Finset.card_eq_sum_card_fiberwise hmaps
  have hbad_le : (bad.card : ℝ) ≤ (G : ℝ) / 2 + ((N : ℝ) + 1) := by
    rw [hbad_eq, Nat.cast_sum]
    calc
      ∑ k ∈ Finset.range (N + 1), ((bad.filter (fun m => κ m = k)).card : ℝ)
          ≤ ∑ _k ∈ Finset.range (N + 1), ((G : ℝ) / (2 * ((N : ℝ) + 1)) + 1) :=
        Finset.sum_le_sum fun k _ => hfiber k
      _ = ((N + 1 : ℕ) : ℝ) * ((G : ℝ) / (2 * ((N : ℝ) + 1)) + 1) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = (G : ℝ) / 2 + ((N : ℝ) + 1) := by
        have hne0 : (N : ℝ) + 1 ≠ 0 := ne_of_gt hN1_pos
        push_cast
        field_simp [hne0]
  have hG_real : 4 * ((N : ℝ) + 1) ≤ (G : ℝ) := by exact_mod_cast hG
  have hbad_34 : (bad.card : ℝ) ≤ 3 * (G : ℝ) / 4 := by linarith
  have hpart : bad.card + good.card = G := by
    have hun : bad ∪ good = Finset.range G := by
      ext m
      simp only [bad, good, Finset.mem_union, Finset.mem_filter]
      tauto
    have hdj : Disjoint bad good :=
      Finset.disjoint_filter.mpr fun _ _ h1 h2 => h2 h1
    rw [← Finset.card_union_of_disjoint hdj, hun, Finset.card_range]
  have hpart_real : (bad.card : ℝ) + (good.card : ℝ) = (G : ℝ) := by exact_mod_cast hpart
  have hgood_ge : (G : ℝ) / 4 ≤ (good.card : ℝ) := by linarith
  have hsum_ge : (good.card : ℝ) * ρ ≤ ∑ m ∈ Finset.range G, |h m| := by
    calc
      (good.card : ℝ) * ρ = ∑ _m ∈ good, ρ := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ m ∈ good, |h m| := by
        refine Finset.sum_le_sum fun m hm => ?_
        have hnot : ¬ |h m| < ρ := (Finset.mem_filter.mp hm).2
        exact le_of_not_gt hnot
      _ ≤ ∑ m ∈ Finset.range G, |h m| := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
        intro m _ _
        exact abs_nonneg _
  have hprod_ge : ((G : ℝ) / 4) * ρ ≤ (good.card : ℝ) * ρ :=
    mul_le_mul_of_nonneg_right hgood_ge (le_of_lt hρ_pos)
  have hN_le_4M : (N : ℝ) + 1 ≤ 4 * (M : ℝ) := by
    have h1 : N + 1 ≤ 4 * M := by omega
    exact_mod_cast h1
  have hfinal : (G : ℝ) / 64 ≤ ((G : ℝ) / 4) * ρ := by
    have heq : ((G : ℝ) / 4) * ρ = ((G : ℝ) * (M : ℝ)) / (16 * ((N : ℝ) + 1)) := by
      dsimp [ρ]
      rw [div_mul_div_comm]
      congr 1
      ring
    rw [heq]
    refine (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 64) (by positivity)).mpr ?_
    nlinarith
  linarith

lemma sum_fullOsc_ge (G : ℕ) :
    ∀ (s : ℕ), 4 * (3 ^ s + 1) ≤ G → ∀ (w : Fin (3 ^ s) → ℝ),
      (s : ℝ) * (G : ℝ) / 64 ≤ ∑ m ∈ Finset.range G, fullOsc w ((m : ℝ) / (G : ℝ)) := by
  intro s
  induction s with
  | zero =>
    intro _ w
    simp only [Nat.cast_zero, zero_mul, zero_div]
    exact Finset.sum_nonneg fun m _ => fullOsc_nonneg w _
  | succ s ih =>
    intro hG w
    let M : ℕ := 3 ^ s
    let N : ℕ := 3 ^ (s + 1)
    have hN : 3 * M = N := by dsimp [M, N]; ring
    have hM : 1 ≤ M := Nat.one_le_pow s 3 (by norm_num)
    have hGs : 4 * (3 ^ s + 1) ≤ G := by
      have : 3 ^ s ≤ 3 ^ (s + 1) := by dsimp [M, N] at hN; omega
      omega
    have hHead := ih hGs (headList hN w)
    have hTail := ih hGs (tailList hN w)
    have hMaxDiff : (G : ℝ) / 64 ≤ ∑ m ∈ Finset.range G,
        |blockMax w (2 * M) N (by omega) ((m : ℝ) / (G : ℝ)) -
         blockMax w 0 M (Nat.zero_le M) ((m : ℝ) / (G : ℝ))| := by
      refine sum_abs_ge_of_fiber_slope hM hN hG
        (fun m => countLe w ((m : ℝ) / (G : ℝ)))
        (fun m _ => countLe_lt w _)
        (fun m => blockMax w (2 * M) N (by omega) ((m : ℝ) / (G : ℝ)) -
          blockMax w 0 M (Nat.zero_le M) ((m : ℝ) / (G : ℝ))) ?_
      intro m₁ m₂ hm _ hk
      have hxy : (m₁ : ℝ) / (G : ℝ) ≤ (m₂ : ℝ) / (G : ℝ) :=
        div_le_div_of_nonneg_right (Nat.cast_le.mpr hm) (Nat.cast_nonneg G)
      have hsub : (m₂ : ℝ) / (G : ℝ) - (m₁ : ℝ) / (G : ℝ) = ((m₂ : ℝ) - (m₁ : ℝ)) / (G : ℝ) :=
        (sub_div _ _ _).symm
      rw [← hsub]
      exact maxDiff_slope hN w hxy hk
    have hMinDiff : (G : ℝ) / 64 ≤ ∑ m ∈ Finset.range G,
        |blockMin w (2 * M) N (by omega) ((m : ℝ) / (G : ℝ)) -
         blockMin w 0 M (Nat.zero_le M) ((m : ℝ) / (G : ℝ))| := by
      refine sum_abs_ge_of_fiber_slope hM hN hG
        (fun m => countLe w ((m : ℝ) / (G : ℝ)))
        (fun m _ => countLe_lt w _)
        (fun m => blockMin w (2 * M) N (by omega) ((m : ℝ) / (G : ℝ)) -
          blockMin w 0 M (Nat.zero_le M) ((m : ℝ) / (G : ℝ))) ?_
      intro m₁ m₂ hm _ hk
      have hxy : (m₁ : ℝ) / (G : ℝ) ≤ (m₂ : ℝ) / (G : ℝ) :=
        div_le_div_of_nonneg_right (Nat.cast_le.mpr hm) (Nat.cast_nonneg G)
      have hsub : (m₂ : ℝ) / (G : ℝ) - (m₁ : ℝ) / (G : ℝ) = ((m₂ : ℝ) - (m₁ : ℝ)) / (G : ℝ) :=
        (sub_div _ _ _).symm
      rw [← hsub]
      exact minDiff_slope hN w hxy hk
    have hSplitSum :
        (∑ m ∈ Finset.range G, fullOsc (headList hN w) ((m : ℝ) / (G : ℝ))) +
        (∑ m ∈ Finset.range G, fullOsc (tailList hN w) ((m : ℝ) / (G : ℝ))) +
        (∑ m ∈ Finset.range G,
          |blockMax w (2 * M) N (by omega) ((m : ℝ) / (G : ℝ)) -
           blockMax w 0 M (Nat.zero_le M) ((m : ℝ) / (G : ℝ))|) +
        (∑ m ∈ Finset.range G,
          |blockMin w (2 * M) N (by omega) ((m : ℝ) / (G : ℝ)) -
           blockMin w 0 M (Nat.zero_le M) ((m : ℝ) / (G : ℝ))|) ≤
        2 * ∑ m ∈ Finset.range G, fullOsc w ((m : ℝ) / (G : ℝ)) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
          Finset.mul_sum]
      refine Finset.sum_le_sum fun m _ => ?_
      have hpt := fullOsc_split hN w ((m : ℝ) / (G : ℝ))
      rw [blockOsc_headList hN w, blockOsc_tailList hN w] at hpt
      exact hpt
    push_cast
    linarith

/-- W (crude finite-prefix discrepancy bound): every list of `3 ^ t` points of `[0, 1)` has a
prefix and a point of `[0, 1)` where the counting error is at least `t / 128`. -/
theorem crude_discrepancy (t : ℕ) (z : Fin (3 ^ t) → ℝ) (hz : ∀ i, z i ∈ Set.Ico (0 : ℝ) 1) :
    ∃ j ≤ 3 ^ t, ∃ x ∈ Set.Ico (0 : ℝ) 1, (t : ℝ) / 128 ≤ |prefixErr z j x| := by
  have _ := hz
  let G : ℕ := 4 * (3 ^ t + 1)
  have hG_pos : 0 < G := Nat.mul_pos (by norm_num) (Nat.succ_pos _)
  have hsum := sum_fullOsc_ge G t le_rfl z
  have hex : ∃ m ∈ Finset.range G, (t : ℝ) / 64 ≤ fullOsc z ((m : ℝ) / (G : ℝ)) := by
    by_contra hnone
    push Not at hnone
    have hlt :
        ∑ m ∈ Finset.range G, fullOsc z ((m : ℝ) / (G : ℝ)) <
        ∑ _m ∈ Finset.range G, ((t : ℝ) / 64) :=
      Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.mpr (by omega)) hnone
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hlt
    linarith
  obtain ⟨m, hm, hosc⟩ := hex
  let x : ℝ := (m : ℝ) / (G : ℝ)
  have hx : x ∈ Set.Ico (0 : ℝ) 1 := by
    refine ⟨by positivity, ?_⟩
    exact (div_lt_one (by exact_mod_cast hG_pos)).mpr (by exact_mod_cast (Finset.mem_range.mp hm))
  have hne : (Finset.Icc 0 (3 ^ t)).Nonempty := Finset.nonempty_Icc.mpr (Nat.zero_le (3 ^ t))
  obtain ⟨j₁, hj₁, hmax⟩ := Finset.exists_mem_eq_sup' hne (fun n => prefixErr z n x)
  obtain ⟨j₂, hj₂, hmin⟩ := Finset.exists_mem_eq_inf' hne (fun n => prefixErr z n x)
  have hdiff : (t : ℝ) / 64 ≤ prefixErr z j₁ x - prefixErr z j₂ x := by
    change (t : ℝ) / 64 ≤ fullOsc z x at hosc
    unfold fullOsc blockOsc blockMax blockMin at hosc
    rw [hmax, hmin] at hosc
    exact hosc
  have h1 : prefixErr z j₁ x ≤ |prefixErr z j₁ x| := le_abs_self _
  have h2 : -prefixErr z j₂ x ≤ |prefixErr z j₂ x| := neg_le_abs _
  by_cases hcase : (t : ℝ) / 128 ≤ |prefixErr z j₁ x|
  · exact ⟨j₁, (Finset.mem_Icc.mp hj₁).2, x, hx, hcase⟩
  · exact ⟨j₂, (Finset.mem_Icc.mp hj₂).2, x, hx, by linarith⟩

/- ## G0 -/

/-- G0: a limsup of the ratio below `1 + A / r` gives an eventual real ratio bound `1 + C / r`. -/
theorem eventually_ratio_le_of_limsup_lt (a : ℕ → ℝ)
    (ha : Function.Injective fun k => Int.fract (a k)) (r : ℕ) (hr : 1 ≤ r) (A : ℝ) (hA : 0 < A)
    (h : limsup (fun n : ℕ => ENNReal.ofReal (Erdos1221.maxSpan a n r) /
        ENNReal.ofReal (Erdos1221.minSpan a n r)) atTop < ENNReal.ofReal (1 + A / r)) :
    ∃ C : ℝ, 0 ≤ C ∧ C < A ∧
      ∀ᶠ n : ℕ in atTop, Erdos1221.maxSpan a n r ≤ (1 + C / r) * Erdos1221.minSpan a n r := by
  obtain ⟨c, hc0, hLc, hcA⟩ := ENNReal.lt_iff_exists_real_btwn.1 h
  have hcA' : c < 1 + A / r := (ENNReal.ofReal_lt_ofReal_iff'.1 hcA).1
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hev := eventually_lt_of_limsup_lt hLc
  have hcC : c ≤ 1 + max (r * (c - 1)) 0 / r := by
    have h1 : c - 1 ≤ max (r * (c - 1)) 0 / r := by
      rw [le_div_iff₀ hr']
      linarith [le_max_left ((r : ℝ) * (c - 1)) 0]
    linarith
  refine ⟨max (r * (c - 1)) 0, le_max_right _ _, ?_, ?_⟩
  · refine max_lt ?_ hA
    have h1 : c - 1 < A / r := by linarith
    have h2 : (r : ℝ) * (c - 1) < r * (A / r) := mul_lt_mul_of_pos_left h1 hr'
    have h3 : (r : ℝ) * (A / r) = A := mul_div_cancel₀ A hr'.ne'
    linarith
  · filter_upwards [hev, eventually_ge_atTop 1] with n hn hn1
    have hm := minSpan_pos a ha (n := n) (r := r) (by omega) (by omega)
    have hm0 : ENNReal.ofReal (Erdos1221.minSpan a n r) ≠ 0 := by
      rw [Ne, ENNReal.ofReal_eq_zero, not_le]
      exact hm
    have hle : ENNReal.ofReal (Erdos1221.maxSpan a n r) ≤
        ENNReal.ofReal c * ENNReal.ofReal (Erdos1221.minSpan a n r) :=
      (ENNReal.div_le_iff hm0 ENNReal.ofReal_ne_top).1 hn.le
    rw [← ENNReal.ofReal_mul hc0, ENNReal.ofReal_le_ofReal_iff (by positivity)] at hle
    calc Erdos1221.maxSpan a n r ≤ c * Erdos1221.minSpan a n r := hle
      _ ≤ (1 + max (r * (c - 1)) 0 / r) * Erdos1221.minSpan a n r :=
        mul_le_mul_of_nonneg_right hcC hm.le

/- ## F: the transfer (Korsky, Lemma 2.1 applied twice; gate proof, sections 5.5-5.7) -/

lemma one_le_of_one_le_mul {k : ℕ} {ε : ℝ} (hkε : 1 ≤ (k : ℝ) * ε) : 1 ≤ k := by
  by_contra hk0
  have hk0' : k = 0 := by omega
  subst hk0'
  norm_num at hkε

lemma pos_of_mul_eq_three_mul {k : ℕ} {A ε D₁ : ℝ} (hA : 1 ≤ A) (hε : 0 < ε)
    (hkε : 1 ≤ (k : ℝ) * ε) (hD₁ : D₁ * ε = 3 * (k : ℝ) * A) : 0 < D₁ := by
  have hk : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast one_le_of_one_le_mul hkε
  have hk_pos : (0 : ℝ) < (k : ℝ) := by linarith
  have hA_pos : 0 < A := by linarith
  have hD₁_eq : D₁ = 3 * (k : ℝ) * A / ε := eq_div_of_mul_eq hε.ne' hD₁
  rw [hD₁_eq]
  positivity

/-- F1a (GATE-PROOF.md, referee-cleared statement). -/
theorem first_transfer_upper (a : ℕ → ℝ) (ha : Function.Injective fun k => Int.fract (a k))
    (r k : ℕ) (A ε D₁ T₀ : ℝ) (hA : 1 ≤ A) (hAr : A < r) (hε : 0 < ε)
    (hkε : 1 ≤ (k : ℝ) * ε) (hD₁ : D₁ * ε = 3 * (k : ℝ) * A)
    (hspan : ∀ s : ℝ, T₀ ≤ s → SpanControl a r A s)
    (t : ℝ) (htT : T₀ ≤ t) (ht : D₁ + r + A < t) (x : ℝ) :
    (arcCount a ⌊t⌋₊ x (D₁ / t) : ℝ) ≤ D₁ * (1 + ε) ^ 2 * ((r : ℝ) / ((r : ℝ) - A)) := by
  have hk : 1 ≤ k := one_le_of_one_le_mul hkε
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hr : 1 ≤ r := by
    have : (1 : ℝ) ≤ (r : ℝ) := by linarith
    exact_mod_cast this
  have hr_pos : (0 : ℝ) < (r : ℝ) := by linarith
  have hD₁_pos : 0 < D₁ := pos_of_mul_eq_three_mul hA hε hkε hD₁
  let E : ℝ := (r : ℝ) - A
  let q : ℝ := E / ((k : ℝ) * (r : ℝ))
  have hE : 0 < E := by dsimp [E]; linarith
  have hkr_pos : 0 < (k : ℝ) * (r : ℝ) := mul_pos (by linarith) hr_pos
  have hq_pos : 0 < q := div_pos hE hkr_pos
  have hq1 : q < 1 := by
    dsimp [q]
    rw [div_lt_one hkr_pos]
    have hr_le_kr : (r : ℝ) ≤ (k : ℝ) * (r : ℝ) := le_mul_of_one_le_left hr_pos.le hkR
    dsimp [E]
    linarith
  have hqε : q ≤ ε := by
    dsimp [q]
    rw [div_le_iff₀ hkr_pos]
    have hr_le : (r : ℝ) ≤ (k : ℝ) * ε * (r : ℝ) := le_mul_of_one_le_left hr_pos.le hkε
    have heq : ε * ((k : ℝ) * (r : ℝ)) = (k : ℝ) * ε * (r : ℝ) := by ring
    dsimp [E]
    linarith
  have ht_pos : 0 < t := by linarith
  have ht1 : 1 ≤ t := by linarith
  have hDt : D₁ < t := by linarith
  have hqt_pos : 0 < q * t := mul_pos hq_pos ht_pos
  have ht_le : t ≤ (1 + q) * t := by linarith
  have hEt : E < (1 + q) * t := by dsimp [E]; linarith
  have hspan' : ∀ s : ℝ, t ≤ s → s ≤ (1 + q) * t → SpanControl a r A s :=
    fun s hts _ => hspan s (le_trans htT hts)
  have hc : ∀ v : ℝ,
      (arcCount a ⌊(1 + q) * t⌋₊ v (E / ((1 + q) * t)) : ℝ) ≤ (r : ℝ) := fun v =>
    arcCount_le_of_spanControl a ha r hr A ((1 + q) * t) hAr.le (by linarith)
      (hspan _ (le_trans htT ht_le)) v
  have hC2 := arcCount_le_of_later a ha r k hr hk A D₁ E q (r : ℝ) t hD₁_pos.le hE rfl hq1
    ht1 hDt hEt hspan' hc x
  have hrhs_eq : (D₁ + 3 * (k : ℝ) * A) * (1 + q) / E * (r : ℝ) =
      (D₁ * (1 + ε)) * (1 + q) * ((r : ℝ) / ((r : ℝ) - A)) := by
    rw [← hD₁]
    dsimp [E]
    ring
  have hrhs_le : (D₁ * (1 + ε)) * (1 + q) * ((r : ℝ) / ((r : ℝ) - A)) ≤
      (D₁ * (1 + ε)) * (1 + ε) * ((r : ℝ) / ((r : ℝ) - A)) := by
    have h1 : (D₁ * (1 + ε)) * (1 + q) ≤ (D₁ * (1 + ε)) * (1 + ε) :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hD₁_pos.le (by linarith))
    exact mul_le_mul_of_nonneg_right h1 (div_nonneg hr_pos.le (by linarith))
  have hfin : (D₁ * (1 + ε)) * (1 + ε) * ((r : ℝ) / ((r : ℝ) - A)) =
      D₁ * (1 + ε) ^ 2 * ((r : ℝ) / ((r : ℝ) - A)) := by ring
  linarith

/-- F1b (GATE-PROOF.md, referee-cleared statement). -/
theorem first_transfer_lower (a : ℕ → ℝ) (ha : Function.Injective fun k => Int.fract (a k))
    (r k : ℕ) (A ε D₁ T₀ : ℝ) (hA : 1 ≤ A) (hAr : A < r) (hε : 0 < ε) (hε3 : ε ≤ 1 / 3)
    (hkε : 1 ≤ (k : ℝ) * ε) (hD₁ : D₁ * ε = 3 * (k : ℝ) * A)
    (hspan : ∀ s : ℝ, T₀ ≤ s → SpanControl a r A s)
    (t : ℝ) (htT : T₀ ≤ (1 - 2 * ε) * t) (ht : D₁ + r + A < (1 - 2 * ε) * t) (x : ℝ) :
    D₁ * (1 - 3 * ε) * ((r : ℝ) / ((r : ℝ) + A)) ≤ (arcCount a ⌊t⌋₊ x (D₁ / t) : ℝ) := by
  have hk : 1 ≤ k := one_le_of_one_le_mul hkε
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hr : 1 ≤ r := by
    have : (1 : ℝ) ≤ (r : ℝ) := by linarith
    exact_mod_cast this
  have hr_pos : (0 : ℝ) < (r : ℝ) := by linarith
  have hD₁_pos : 0 < D₁ := pos_of_mul_eq_three_mul hA hε hkε hD₁
  let E : ℝ := (r : ℝ) + A
  let q : ℝ := E / ((k : ℝ) * (r : ℝ))
  have hE : 0 < E := by dsimp [E]; linarith
  have hkr_pos : 0 < (k : ℝ) * (r : ℝ) := mul_pos (by linarith) hr_pos
  have hq_pos : 0 < q := div_pos hE hkr_pos
  have hq2ε : q ≤ 2 * ε := by
    dsimp [q]
    rw [div_le_iff₀ hkr_pos]
    have hr_le : (r : ℝ) ≤ (k : ℝ) * ε * (r : ℝ) := le_mul_of_one_le_left hr_pos.le hkε
    have heq : 2 * ε * ((k : ℝ) * (r : ℝ)) = 2 * ((k : ℝ) * ε * (r : ℝ)) := by ring
    dsimp [E]
    linarith
  have hq1 : q < 1 := by linarith
  have h12ε_pos : 0 < 1 - 2 * ε := by linarith
  have ht_prod_pos : 0 < (1 - 2 * ε) * t := by linarith
  have ht_pos : 0 < t := pos_of_mul_pos_right ht_prod_pos h12ε_pos.le
  have h2ε_le_q : (1 - 2 * ε) * t ≤ (1 - q) * t :=
    mul_le_mul_of_nonneg_right (by linarith) ht_pos.le
  have hqt_pos : 0 < q * t := mul_pos hq_pos ht_pos
  have hq_le_t : (1 - q) * t ≤ t := by linarith
  have ht1 : 1 ≤ (1 - q) * t := by linarith
  have hDt : D₁ < t := by linarith
  have hEt : E < (1 - q) * t := by dsimp [E]; linarith
  have hspan' : ∀ s : ℝ, (1 - q) * t ≤ s → s ≤ t → SpanControl a r A s :=
    fun s hs _ => hspan s (le_trans htT (le_trans h2ε_le_q hs))
  have hc : ∀ v : ℝ,
      (r : ℝ) ≤ (arcCount a ⌊(1 - q) * t⌋₊ v (E / ((1 - q) * t)) : ℝ) := fun v =>
    le_arcCount_of_spanControl a ha r hr A ((1 - q) * t) hEt
      (hspan _ (le_trans htT h2ε_le_q)) v
  have hC2 := le_arcCount_of_earlier a ha r k hr hk A D₁ E q (r : ℝ) t hD₁_pos.le hE rfl hq1
    ht1 hDt hEt hspan' hr_pos.le hc x
  have hnum : D₁ * (1 - 3 * ε) ≤ D₁ * (1 - q) - (k : ℝ) * A * (3 - q) := by
    have hqD₁ : q * D₁ ≤ 2 * (D₁ * ε) := by
      have h1 : q * D₁ ≤ (2 * ε) * D₁ := mul_le_mul_of_nonneg_right hq2ε hD₁_pos.le
      have e : 2 * (D₁ * ε) = (2 * ε) * D₁ := by ring
      linarith
    have hqkA : 0 ≤ q * ((k : ℝ) * A) :=
      mul_nonneg hq_pos.le (mul_nonneg (by linarith) (by linarith))
    have hid : D₁ * (1 - q) - (k : ℝ) * A * (3 - q) =
        D₁ - 3 * (k : ℝ) * A - q * D₁ + q * ((k : ℝ) * A) := by ring
    have hgoal_id : D₁ * (1 - 3 * ε) = D₁ - 3 * (D₁ * ε) := by ring
    linarith
  have hlhs_le : D₁ * (1 - 3 * ε) * ((r : ℝ) / ((r : ℝ) + A)) ≤
      (D₁ * (1 - q) - (k : ℝ) * A * (3 - q)) * ((r : ℝ) / ((r : ℝ) + A)) :=
    mul_le_mul_of_nonneg_right hnum (div_nonneg hr_pos.le (by linarith))
  have hlhs_eq : (D₁ * (1 - q) - (k : ℝ) * A * (3 - q)) / E * (r : ℝ) =
      (D₁ * (1 - q) - (k : ℝ) * A * (3 - q)) * ((r : ℝ) / ((r : ℝ) + A)) := by
    dsimp [E]
    ring
  linarith

lemma cube_one_add_le {ε : ℝ} (hε0 : 0 < ε) (hε30 : ε ≤ 1 / 30) :
    (1 + ε) ^ 3 ≤ 1 + 4 * ε := by
  have hε2 : ε * ε ≤ (1 / 30) * (1 / 30) :=
    mul_le_mul hε30 hε30 hε0.le (by norm_num)
  have hdiff : (1 + 4 * ε) - (1 + ε) ^ 3 = ε * (1 - 3 * ε - ε * ε) := by ring
  have hfac : 0 ≤ 1 - 3 * ε - ε * ε := by linarith
  have hprod : 0 ≤ ε * (1 - 3 * ε - ε * ε) := mul_nonneg hε0.le hfac
  linarith

/-- F2 (GATE-PROOF.md, referee-cleared statement). -/
theorem second_transfer (a : ℕ → ℝ) (ha : Function.Injective fun k => Int.fract (a k))
    (r k : ℕ) (A S ε D₁ T₀ : ℝ) (hA : 1 ≤ A) (hS : 0 ≤ S)
    (hε : ε = 1 / (10 * (S + 3 * A))) (hkε : 1 ≤ (k : ℝ) * ε)
    (hD₁ : D₁ * ε = 3 * (k : ℝ) * A) (hr : D₁ + 2 * A ≤ ε * r)
    (hspan : ∀ s : ℝ, T₀ ≤ s → SpanControl a r A s)
    (t : ℝ) (htT : T₀ ≤ (1 - 2 * ε) * ((1 - ε) * t))
    (ht : S + D₁ + r + A < (1 - 2 * ε) * ((1 - ε) * t))
    (x D : ℝ) (hD0 : 0 ≤ D) (hDS : D ≤ S) :
    |(arcCount a ⌊t⌋₊ x (D / t) : ℝ) - D| ≤ 3 * A + 1 / 2 := by
  have hS3A : 3 ≤ S + 3 * A := by linarith
  have hε_pos : 0 < ε := by rw [hε]; exact div_pos one_pos (by linarith)
  have hε_mul : 10 * ε * (S + 3 * A) = 1 := by
    rw [hε]
    have heq : 10 * (1 / (10 * (S + 3 * A))) * (S + 3 * A) =
        (10 * (S + 3 * A)) / (10 * (S + 3 * A)) := by ring
    rw [heq, div_self (by linarith)]
  have hε_le : ε ≤ 1 / 30 := by
    have h1 : 10 * ε * 3 ≤ 10 * ε * (S + 3 * A) :=
      mul_le_mul_of_nonneg_left hS3A (by linarith)
    linarith
  have hD₁_pos : 0 < D₁ := pos_of_mul_eq_three_mul hA hε_pos hkε hD₁
  have hAr : A < (r : ℝ) := by
    have hεr : ε * (r : ℝ) ≤ (1 / 30) * (r : ℝ) :=
      mul_le_mul_of_nonneg_right hε_le (Nat.cast_nonneg r)
    linarith
  have hr_pos : (0 : ℝ) < (r : ℝ) := by linarith
  have hr1 : 1 ≤ r := by
    have : (1 : ℝ) ≤ (r : ℝ) := by linarith
    exact_mod_cast this
  let q₃ : ℝ := D₁ / (r : ℝ)
  have hq₃_pos : 0 < q₃ := div_pos hD₁_pos hr_pos
  have hq₃_le_ε : q₃ ≤ ε := by
    dsimp [q₃]
    rw [div_le_iff₀ hr_pos]
    linarith
  have hq₃_lt_1 : q₃ < 1 := by linarith
  have hq₃_eq : q₃ = D₁ / (((1 : ℕ) : ℝ) * (r : ℝ)) := by simp [q₃]
  have hrA_pos : 0 < (r : ℝ) - A := by linarith
  have hr3 : (1 + q₃) * ((r : ℝ) / ((r : ℝ) - A)) ≤ 1 + ε := by
    have h1q₃r : (1 + q₃) * (r : ℝ) = (r : ℝ) + D₁ := by
      dsimp [q₃]
      rw [add_mul, one_mul, div_mul_cancel₀ _ hr_pos.ne']
    rw [← mul_div_assoc, h1q₃r, div_le_iff₀ hrA_pos]
    have hεA : ε * A ≤ A := mul_le_of_le_one_left (by linarith) (by linarith)
    have hexp : (1 + ε) * ((r : ℝ) - A) = (r : ℝ) - A + ε * (r : ℝ) - ε * A := by ring
    linarith
  have hrA_add_pos : 0 < (r : ℝ) + A := by linarith
  have hr4 : 1 - ε ≤ (r : ℝ) / ((r : ℝ) + A) := by
    rw [le_div_iff₀ hrA_add_pos]
    have hεA : 0 ≤ ε * A := mul_nonneg hε_pos.le (by linarith)
    have hexp : (1 - ε) * ((r : ℝ) + A) = (r : ℝ) + A - ε * (r : ℝ) - ε * A := by ring
    linarith
  have h1ε_pos : 0 < 1 - ε := by linarith
  have h12ε_pos : 0 < 1 - 2 * ε := by linarith
  have hϑt_pos : 0 < (1 - 2 * ε) * ((1 - ε) * t) := by linarith
  have h1εt_pos : 0 < (1 - ε) * t := pos_of_mul_pos_right hϑt_pos h12ε_pos.le
  have ht_pos : 0 < t := pos_of_mul_pos_right h1εt_pos h1ε_pos.le
  have hϑt_le_1εt : (1 - 2 * ε) * ((1 - ε) * t) ≤ (1 - ε) * t :=
    mul_le_of_le_one_left h1εt_pos.le (by linarith)
  have h1εt_le_t : (1 - ε) * t ≤ t :=
    mul_le_of_le_one_left ht_pos.le (by linarith)
  have hq₃t_pos : 0 < q₃ * t := mul_pos hq₃_pos ht_pos
  have ht_le_1q₃t : t ≤ (1 + q₃) * t := by linarith
  have h1εt_le_1q₃t : (1 - ε) * t ≤ (1 - q₃) * t :=
    mul_le_mul_of_nonneg_right (by linarith) ht_pos.le
  have h1q₃t_le_t : (1 - q₃) * t ≤ t := by linarith
  have hup : (arcCount a ⌊t⌋₊ x (D / t) : ℝ) - D ≤ 3 * A + 1 / 2 := by
    let c₁ : ℝ := D₁ * (1 + ε) ^ 2 * ((r : ℝ) / ((r : ℝ) - A))
    have hspan1 : ∀ s : ℝ, t ≤ s → s ≤ (1 + q₃) * t → SpanControl a r A s :=
      fun s hts _ => hspan s (by linarith)
    have hc1 : ∀ v : ℝ,
        (arcCount a ⌊(1 + q₃) * t⌋₊ v (D₁ / ((1 + q₃) * t)) : ℝ) ≤ c₁ := fun v =>
      first_transfer_upper a ha r k A ε D₁ T₀ hA hAr hε_pos hkε hD₁ hspan
        ((1 + q₃) * t) (by linarith) (by linarith) v
    have hC2a := arcCount_le_of_later a ha r 1 hr1 (le_refl 1) A D D₁ q₃ c₁ t hD0 hD₁_pos
      hq₃_eq hq₃_lt_1 (by linarith) (by linarith) (by linarith) hspan1 hc1 x
    have hrew : (D + 3 * ((1 : ℕ) : ℝ) * A) * (1 + q₃) / D₁ * c₁ =
        (D + 3 * A) * (1 + ε) ^ 2 * ((1 + q₃) * ((r : ℝ) / ((r : ℝ) - A))) := by
      dsimp [c₁]
      rw [Nat.cast_one]
      have e : (D + 3 * 1 * A) * (1 + q₃) / D₁ *
          (D₁ * (1 + ε) ^ 2 * ((r : ℝ) / ((r : ℝ) - A))) =
          (D + 3 * A) * (1 + ε) ^ 2 * ((1 + q₃) * ((r : ℝ) / ((r : ℝ) - A))) * (D₁ / D₁) := by
        ring
      rw [e, div_self hD₁_pos.ne', mul_one]
    have hstep1 : (D + 3 * A) * (1 + ε) ^ 2 * ((1 + q₃) * ((r : ℝ) / ((r : ℝ) - A))) ≤
        (D + 3 * A) * (1 + ε) ^ 3 := by
      have hnonneg : 0 ≤ (D + 3 * A) * (1 + ε) ^ 2 :=
        mul_nonneg (by linarith) (sq_nonneg (1 + ε))
      have h1 := mul_le_mul_of_nonneg_left hr3 hnonneg
      have e : (D + 3 * A) * (1 + ε) ^ 2 * (1 + ε) = (D + 3 * A) * (1 + ε) ^ 3 := by ring
      linarith
    have hstep2 : (D + 3 * A) * (1 + ε) ^ 3 ≤ (D + 3 * A) * (1 + 4 * ε) :=
      mul_le_mul_of_nonneg_left (cube_one_add_le hε_pos hε_le) (by linarith)
    have hstep3 : 4 * ε * (D + 3 * A) ≤ 4 * ε * (S + 3 * A) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have hexp : (D + 3 * A) * (1 + 4 * ε) = D + 3 * A + 4 * ε * (D + 3 * A) := by ring
    have h4ε : 4 * ε * (S + 3 * A) = 2 / 5 := by
      have e : 4 * ε * (S + 3 * A) = (2 / 5) * (10 * ε * (S + 3 * A)) := by ring
      linarith
    linarith
  have hlo : -(3 * A + 1 / 2) ≤ (arcCount a ⌊t⌋₊ x (D / t) : ℝ) - D := by
    let c₁' : ℝ := D₁ * (1 - 3 * ε) * ((r : ℝ) / ((r : ℝ) + A))
    have hc₁'_nonneg : 0 ≤ c₁' :=
      mul_nonneg (mul_nonneg hD₁_pos.le (by linarith)) (div_nonneg hr_pos.le hrA_add_pos.le)
    have hspan2 : ∀ s : ℝ, (1 - q₃) * t ≤ s → s ≤ t → SpanControl a r A s :=
      fun s hs _ => hspan s (by linarith)
    have hϑ_le_t2 : (1 - 2 * ε) * ((1 - ε) * t) ≤ (1 - 2 * ε) * ((1 - q₃) * t) :=
      mul_le_mul_of_nonneg_left h1εt_le_1q₃t h12ε_pos.le
    have hc2 : ∀ v : ℝ,
        c₁' ≤ (arcCount a ⌊(1 - q₃) * t⌋₊ v (D₁ / ((1 - q₃) * t)) : ℝ) := fun v =>
      first_transfer_lower a ha r k A ε D₁ T₀ hA hAr hε_pos (by linarith) hkε hD₁ hspan
        ((1 - q₃) * t) (by linarith) (by linarith) v
    have hC2b := le_arcCount_of_earlier a ha r 1 hr1 (le_refl 1) A D D₁ q₃ c₁' t hD0 hD₁_pos
      hq₃_eq hq₃_lt_1 (by linarith) (by linarith) (by linarith) hspan2 hc₁'_nonneg hc2 x
    let X : ℝ := D * (1 - q₃) - A * (3 - q₃)
    let Z : ℝ := (1 - 3 * ε) * ((r : ℝ) / ((r : ℝ) + A))
    have hrew : (D * (1 - q₃) - ((1 : ℕ) : ℝ) * A * (3 - q₃)) / D₁ * c₁' = X * Z := by
      dsimp [X, Z, c₁']
      rw [Nat.cast_one]
      have e : (D * (1 - q₃) - 1 * A * (3 - q₃)) / D₁ *
          (D₁ * (1 - 3 * ε) * ((r : ℝ) / ((r : ℝ) + A))) =
          (D * (1 - q₃) - A * (3 - q₃)) * ((1 - 3 * ε) * ((r : ℝ) / ((r : ℝ) + A))) *
          (D₁ / D₁) := by ring
      rw [e, div_self hD₁_pos.ne', mul_one]
    have hZ : 1 - 4 * ε ≤ Z := by
      have h1 : (1 - 3 * ε) * (1 - ε) ≤ Z := mul_le_mul_of_nonneg_left hr4 (by linarith)
      have h2 : (1 - 3 * ε) * (1 - ε) - (1 - 4 * ε) = 3 * ε ^ 2 := by ring
      have h3 : 0 ≤ 3 * ε ^ 2 := by positivity
      linarith
    let X' : ℝ := D - ε * D - 3 * A
    have hX'_le_X : X' ≤ X := by
      have hdiff : X - X' = (ε - q₃) * D + q₃ * A := by dsimp [X, X']; ring
      have h1 : 0 ≤ (ε - q₃) * D := mul_nonneg (by linarith) hD0
      have h2 : 0 ≤ q₃ * A := mul_nonneg hq₃_pos.le (by linarith)
      linarith
    have hX'_le_D : X' ≤ D := by
      have hεD : 0 ≤ ε * D := mul_nonneg hε_pos.le hD0
      dsimp [X']
      linarith
    have hεD_le_εS : ε * D ≤ ε * S := mul_le_mul_of_nonneg_left hDS hε_pos.le
    have hεS : 10 * (ε * S) ≤ 1 := by
      have h1 : 10 * ε * S ≤ 10 * ε * (S + 3 * A) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      have e : 10 * (ε * S) = 10 * ε * S := by ring
      linarith
    rcases le_or_gt X' 0 with hX'0 | hX'0
    · have hcnt0 : (0 : ℝ) ≤ (arcCount a ⌊t⌋₊ x (D / t) : ℝ) := Nat.cast_nonneg _
      dsimp [X'] at hX'0
      linarith
    · have hX_pos : 0 < X := lt_of_lt_of_le hX'0 hX'_le_X
      have h1 : X * (1 - 4 * ε) ≤ X * Z := mul_le_mul_of_nonneg_left hZ hX_pos.le
      have h2 : X' * (1 - 4 * ε) ≤ X * (1 - 4 * ε) :=
        mul_le_mul_of_nonneg_right hX'_le_X (by linarith)
      have h3 : 4 * (ε * X') ≤ 4 * (ε * D) := by
        have h3' : (4 * ε) * X' ≤ (4 * ε) * D :=
          mul_le_mul_of_nonneg_left hX'_le_D (by linarith)
        have e1 : 4 * (ε * X') = (4 * ε) * X' := by ring
        have e2 : 4 * (ε * D) = (4 * ε) * D := by ring
        linarith
      have h4 : X' * (1 - 4 * ε) = X' - 4 * (ε * X') := by ring
      have h5 : X' = D - ε * D - 3 * A := rfl
      linarith
  exact abs_le.2 ⟨hlo, hup⟩

/-- F (Korsky, Lemma 2.1 and (3.2), applied twice): span control with a fixed `A` gives counting
control with error `3 A + 1 / 2` on all arcs of length `D / n` with `0 ≤ D ≤ S`, once `r` is
large. -/
theorem count_control_of_span_control (A S : ℝ) (hA : 1 ≤ A) (hS : 0 ≤ S) :
    ∃ r₀ : ℕ, ∀ r ≥ r₀, ∀ a : ℕ → ℝ, Function.Injective (fun k => Int.fract (a k)) →
      (∀ᶠ t : ℝ in atTop, SpanControl a r A t) →
      ∀ᶠ n : ℕ in atTop, CountControl a (3 * A + 1 / 2) S n := by
  let ε : ℝ := 1 / (10 * (S + 3 * A))
  have hS3A : 3 ≤ S + 3 * A := by linarith
  have hε_pos : 0 < ε := div_pos one_pos (by linarith)
  have hε_mul : 10 * ε * (S + 3 * A) = 1 := by
    dsimp [ε]
    have heq : 10 * (1 / (10 * (S + 3 * A))) * (S + 3 * A) =
        (10 * (S + 3 * A)) / (10 * (S + 3 * A)) := by ring
    rw [heq, div_self (by linarith)]
  have hε_le : ε ≤ 1 / 30 := by
    have h1 : 10 * ε * 3 ≤ 10 * ε * (S + 3 * A) :=
      mul_le_mul_of_nonneg_left hS3A (by linarith)
    linarith
  let k : ℕ := ⌈1 / ε⌉₊
  have hkε : 1 ≤ (k : ℝ) * ε := by
    have hk_ge : 1 / ε ≤ (k : ℝ) := Nat.le_ceil (1 / ε)
    have h1 : (1 / ε) * ε ≤ (k : ℝ) * ε := mul_le_mul_of_nonneg_right hk_ge hε_pos.le
    rwa [one_div_mul_cancel hε_pos.ne'] at h1
  let D₁ : ℝ := 3 * (k : ℝ) * A / ε
  have hD₁ : D₁ * ε = 3 * (k : ℝ) * A := div_mul_cancel₀ _ hε_pos.ne'
  let r₀ : ℕ := ⌈(D₁ + 2 * A) / ε⌉₊
  refine ⟨r₀, fun r hr a ha hspan_ev => ?_⟩
  have hr_ge : D₁ + 2 * A ≤ ε * (r : ℝ) := by
    have h1 : (D₁ + 2 * A) / ε ≤ (r : ℝ) := le_trans (Nat.le_ceil _) (Nat.cast_le.2 hr)
    have h2 : D₁ + 2 * A ≤ (r : ℝ) * ε := (div_le_iff₀ hε_pos).1 h1
    linarith
  rw [Filter.eventually_atTop] at hspan_ev ⊢
  obtain ⟨T₀, hT₀⟩ := hspan_ev
  let ϑ : ℝ := (1 - 2 * ε) * (1 - ε)
  have hϑ_pos : 0 < ϑ := mul_pos (by linarith) (by linarith)
  let Θ : ℝ := max T₀ (S + D₁ + (r : ℝ) + A + 1)
  refine ⟨⌈Θ / ϑ⌉₊, fun n hn x D hD0 hDS => ?_⟩
  have hn_ge : Θ / ϑ ≤ (n : ℝ) := le_trans (Nat.le_ceil _) (Nat.cast_le.2 hn)
  have hϑn : Θ ≤ ϑ * (n : ℝ) := by
    have h1 : Θ ≤ (n : ℝ) * ϑ := (div_le_iff₀ hϑ_pos).1 hn_ge
    linarith
  have hϑn_eq : ϑ * (n : ℝ) = (1 - 2 * ε) * ((1 - ε) * (n : ℝ)) := by dsimp [ϑ]; ring
  have htT : T₀ ≤ (1 - 2 * ε) * ((1 - ε) * (n : ℝ)) := by
    have h1 : T₀ ≤ Θ := le_max_left _ _
    linarith
  have ht : S + D₁ + (r : ℝ) + A < (1 - 2 * ε) * ((1 - ε) * (n : ℝ)) := by
    have h1 : S + D₁ + (r : ℝ) + A + 1 ≤ Θ := le_max_right _ _
    linarith
  simpa only [Nat.floor_natCast] using
    second_transfer a ha r k A S ε D₁ T₀ hA hS rfl hkε hD₁ hr_ge hT₀ (n : ℝ) htT ht x D hD0 hDS

/- ## L: localization to a finite list (builder: localization) -/

lemma liftPt_add_nat_mul_period (a : ℕ → ℝ) {n : ℕ} (hn : 0 < n) (j : ℤ) (k : ℕ) :
    liftPt a n (j + (k : ℤ) * (n : ℤ)) = liftPt a n j + (k : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hidx : j + ((k + 1 : ℕ) : ℤ) * (n : ℤ) = (j + (k : ℤ) * (n : ℤ)) + (n : ℤ) := by
      push_cast
      ring
    rw [hidx, liftPt_add_period a hn, ih]
    push_cast
    ring

lemma liftPt_add_int_mul_period (a : ℕ → ℝ) {n : ℕ} (hn : 0 < n) (j m : ℤ) :
    liftPt a n (j + m * (n : ℤ)) = liftPt a n j + (m : ℝ) := by
  cases m with
  | ofNat k =>
    simpa using liftPt_add_nat_mul_period a hn j k
  | negSucc k =>
    have h := liftPt_add_nat_mul_period a hn (j + Int.negSucc k * (n : ℤ)) (k + 1)
    have hidx : j + Int.negSucc k * (n : ℤ) + ((k + 1 : ℕ) : ℤ) * (n : ℤ) = j := by
      rw [Int.negSucc_eq]
      push_cast
      ring
    rw [hidx] at h
    have hcast : ((Int.negSucc k : ℤ) : ℝ) = -((k + 1 : ℕ) : ℝ) := by
      rw [Int.cast_negSucc]
    linarith

lemma liftPt_gap_ge_minSpan (a : ℕ → ℝ) (ha : Function.Injective fun k => Int.fract (a k))
    {n : ℕ} (hn : 0 < n) {j₁ j₂ : ℤ} (h : j₁ < j₂) :
    Erdos1221.minSpan a n 1 ≤ liftPt a n j₂ - liftPt a n j₁ := by
  have h1 := (liftPt_span_bounds a hn 1 (Erdos1221.minSpan a n 1) (Erdos1221.maxSpan a n 1)
    (fun i hi => ⟨minSpan_le_rSpan a 1 hi, rSpan_le_maxSpan a 1 hi⟩) j₁).1
  have h2 : liftPt a n (j₁ + 1) ≤ liftPt a n j₂ :=
    (liftPt_strictMono a ha hn).monotone (by omega)
  have h1' : Erdos1221.minSpan a n 1 ≤ liftPt a n (j₁ + 1) - liftPt a n j₁ := by
    simpa using h1
  linarith

lemma arcCount_le_one_of_lt_minSpan (a : ℕ → ℝ) (ha : Function.Injective fun k => Int.fract (a k))
    {n : ℕ} (hn : 0 < n) (c lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam < 1)
    (hgap : lam < Erdos1221.minSpan a n 1) :
    arcCount a n c lam ≤ 1 := by
  rw [arcCount_eq_ncard a ha hn c lam h0 h1]
  have hsub : {j : ℤ | c < liftPt a n j ∧ liftPt a n j ≤ c + lam}.Subsingleton := by
    intro j₁ hj₁ j₂ hj₂
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have hsep := liftPt_gap_ge_minSpan a ha hn hlt
      linarith [hj₁.1, hj₂.2]
    · have hsep := liftPt_gap_ge_minSpan a ha hn hlt
      linarith [hj₂.1, hj₁.2]
  rcases hsub.eq_empty_or_singleton with hEq | ⟨j, hEq⟩
  · rw [hEq, Set.ncard_empty]
    exact Nat.zero_le 1
  · rw [hEq, Set.ncard_singleton]

lemma arcCount_mono_n (a : ℕ → ℝ) {n₁ n₂ : ℕ} (h : n₁ ≤ n₂) (c lam : ℝ) :
    arcCount a n₁ c lam ≤ arcCount a n₂ c lam := by
  unfold arcCount
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono h))

lemma fract_sub_eq_fract_fract_sub (y μ : ℝ) :
    Int.fract (y - μ) = Int.fract (Int.fract y - μ) := by
  have h : y - μ = (Int.fract y - μ) + (⌊y⌋ : ℝ) := by
    linarith [Int.fract_add_floor y]
  rw [h, Int.fract_add_intCast]

lemma fract_eq_fract_fract_sub_add (y μ : ℝ) :
    Int.fract y = Int.fract (Int.fract (y - μ) + μ) := by
  have h : y = (Int.fract (y - μ) + μ) + (⌊y - μ⌋ : ℝ) := by
    linarith [Int.fract_add_floor (y - μ)]
  conv_lhs => rw [h]
  rw [Int.fract_add_intCast]

lemma arcCount_add (a : ℕ → ℝ) (n : ℕ) (c μ lam : ℝ)
    (hμ : 0 ≤ μ) (hμlam : μ ≤ lam) (hlam : lam < 1) :
    arcCount a n c lam = arcCount a n c μ + arcCount a n (c + μ) (lam - μ) := by
  unfold arcCount
  set s := (Finset.range n).filter (fun k => Int.fract (a k - c) ∈ Set.Ioc (0 : ℝ) lam)
  set s₁ := (Finset.range n).filter (fun k => Int.fract (a k - c) ∈ Set.Ioc (0 : ℝ) μ)
  set s₂ := (Finset.range n).filter (fun k => Int.fract (a k - (c + μ)) ∈ Set.Ioc (0 : ℝ) (lam - μ))
  have hdisj : Disjoint s₁ s₂ := by
    rw [Finset.disjoint_filter]
    intro k _ h1 h2
    have hsub : a k - (c + μ) = (a k - c) - μ := by ring
    rw [hsub] at h2
    have hfr := fract_sub_eq_fract_fract_sub (a k - c) μ
    rw [hfr] at h2
    rcases lt_or_eq_of_le h1.2 with hlt | heq
    · have hshift : Int.fract (a k - c) - μ =
          (Int.fract (a k - c) - μ + 1) + ((-1 : ℤ) : ℝ) := by
        push_cast
        ring
      have hself : Int.fract (Int.fract (a k - c) - μ + 1) =
          Int.fract (a k - c) - μ + 1 :=
        Int.fract_eq_self.mpr ⟨by linarith [h1.1], by linarith⟩
      rw [hshift, Int.fract_add_intCast, hself] at h2
      linarith [h1.1, h2.2]
    · rw [heq, sub_self, Int.fract_zero] at h2
      linarith [h2.1]
  have hunion : s = s₁ ∪ s₂ := by
    ext k
    simp only [s, s₁, s₂, Finset.mem_filter, Finset.mem_union, Set.mem_Ioc]
    have hsub : a k - (c + μ) = (a k - c) - μ := by ring
    rw [hsub]
    constructor
    · rintro ⟨hk, h0, hle⟩
      by_cases hleμ : Int.fract (a k - c) ≤ μ
      · exact Or.inl ⟨hk, h0, hleμ⟩
      · right
        push Not at hleμ
        have hself : Int.fract (Int.fract (a k - c) - μ) = Int.fract (a k - c) - μ :=
          Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
        rw [fract_sub_eq_fract_fract_sub, hself]
        exact ⟨hk, by linarith, by linarith⟩
    · rintro (⟨hk, h0, hle⟩ | ⟨hk, h0, hle⟩)
      · exact ⟨hk, h0, le_trans hle hμlam⟩
      · have hself : Int.fract (Int.fract ((a k - c) - μ) + μ) =
            Int.fract ((a k - c) - μ) + μ :=
          Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
        rw [fract_eq_fract_fract_sub_add (a k - c) μ, hself]
        exact ⟨hk, by linarith, by linarith⟩
  rw [hunion, Finset.card_union_of_disjoint hdisj]

lemma exists_liftPt_eq_add_fract (a : ℕ → ℝ) {N : ℕ} (hN : 0 < N) (c : ℝ) {k : ℕ} (hk : k < N) :
    ∃ j : ℤ, liftPt a N j = c + Int.fract (a k - c) := by
  obtain ⟨j₀, _, _, hj₀⟩ := exists_liftPt_eq_fract a k hk
  refine ⟨j₀ + (-⌊liftPt a N j₀ - c⌋) * (N : ℤ), ?_⟩
  rw [liftPt_add_int_mul_period a hN j₀ (-⌊liftPt a N j₀ - c⌋)]
  have hfr : Int.fract (a k - c) = Int.fract (liftPt a N j₀ - c) := by
    rw [hj₀]
    exact fract_sub_eq_fract_fract_sub (a k) c
  rw [hfr]
  have hfl := Int.fract_add_floor (liftPt a N j₀ - c)
  push_cast
  linarith

/-- L (Korsky, Lemma 4.2): eventual counting control with error `B` on arcs of length up to
`L / n` gives a list of `L` points in `(0, 1)` all of whose prefixes have counting error at
most `B`. -/
theorem localize (a : ℕ → ℝ) (ha : Function.Injective fun k => Int.fract (a k))
    (B : ℝ) (hB : 1 ≤ B) (L : ℕ) (hL : 2 ≤ L)
    (h : ∀ᶠ n : ℕ in atTop, CountControl a B L n) :
    ∃ z : Fin L → ℝ, (∀ i, z i ∈ Set.Ioo (0 : ℝ) 1) ∧
      ∀ j ≤ L, ∀ x ∈ Set.Icc (0 : ℝ) 1, |prefixErr z j x| ≤ B := by
  obtain ⟨n₁, hn₁⟩ := Filter.eventually_atTop.mp h
  set n₀ : ℕ := max n₁ 1
  have hn₀_pos : 0 < n₀ := lt_of_lt_of_le Nat.one_pos (le_max_right n₁ 1)
  have hcc : ∀ n ≥ n₀, CountControl a B L n :=
    fun n hn => hn₁ n (le_trans (le_max_left n₁ 1) hn)
  set δ : ℝ := Erdos1221.minSpan a n₀ 1
  have hδ_pos : 0 < δ := minSpan_pos a ha hn₀_pos Nat.one_pos
  obtain ⟨M, hM⟩ := exists_nat_gt ((L : ℝ) / δ)
  set N : ℕ := max (max L n₀ + 1) M
  have hL_lt_N : L < N := by
    have h1 : L < max L n₀ + 1 := Nat.lt_succ_of_le (le_max_left L n₀)
    exact lt_of_lt_of_le h1 (le_max_left _ _)
  have hN_pos : 0 < N := lt_trans (by omega : 0 < L) hL_lt_N
  have hN_pos_r : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN_pos
  have hLN_lt_δ : (L : ℝ) / (N : ℝ) < δ := by
    have hMN : (M : ℝ) ≤ (N : ℝ) := by exact_mod_cast le_max_right (max L n₀ + 1) M
    have hLδN : (L : ℝ) / δ < (N : ℝ) := lt_of_lt_of_le hM hMN
    rw [div_lt_iff₀ hN_pos_r]
    have := (div_lt_iff₀ hδ_pos).mp hLδN
    linarith
  have hLN_lt_1 : (L : ℝ) / (N : ℝ) < 1 := by
    rw [div_lt_one hN_pos_r]
    exact_mod_cast hL_lt_N
  obtain ⟨i₀, _, hi₀⟩ := exists_rSpan_eq_minSpan a hN_pos L
  set ℓ : ℝ := liftPt a N ((i₀ : ℤ) + (L : ℤ)) - liftPt a N (i₀ : ℤ)
  have hℓ_eq : ℓ = Erdos1221.minSpan a N L := by
    have hsp := rSpan_eq_liftPt a N L i₀
    rw [Nat.cast_add] at hsp
    linarith [hi₀, hsp]
  have hℓ_pos : 0 < ℓ := by
    rw [hℓ_eq]
    exact minSpan_pos a ha hN_pos (by omega)
  have hNℓ_le_L : (N : ℝ) * ℓ ≤ (L : ℝ) := by
    rw [hℓ_eq]
    exact mul_minSpan_le a hN_pos L
  have hℓ_le_LN : ℓ ≤ (L : ℝ) / (N : ℝ) := by
    rw [le_div_iff₀ hN_pos_r]
    linarith
  have hℓ_lt_δ : ℓ < δ := lt_of_le_of_lt hℓ_le_LN hLN_lt_δ
  have hℓ_lt_1 : ℓ < 1 := lt_of_le_of_lt hℓ_le_LN hLN_lt_1
  set δN : ℝ := Erdos1221.minSpan a N 1
  have hδN_pos : 0 < δN := minSpan_pos a ha hN_pos Nat.one_pos
  set η : ℝ := δN / 2
  have hη_pos : 0 < η := by positivity
  have hη_lt : η < δN := half_lt_self hδN_pos
  set c : ℝ := liftPt a N (i₀ : ℤ) + η
  have hIoc_iff : ∀ j : ℤ, (c < liftPt a N j ∧ liftPt a N j ≤ c + ℓ) ↔
      ((i₀ : ℤ) < j ∧ j ≤ (i₀ : ℤ) + (L : ℤ)) := by
    intro j
    constructor
    · rintro ⟨hlo, hhi⟩
      constructor
      · by_contra hle
        push Not at hle
        have := (liftPt_strictMono a ha hN_pos).monotone hle
        linarith
      · by_contra hgt
        push Not at hgt
        have hsep := liftPt_gap_ge_minSpan a ha hN_pos hgt
        linarith
    · rintro ⟨hlo, hhi⟩
      have hsep := liftPt_gap_ge_minSpan a ha hN_pos hlo
      have hmono := (liftPt_strictMono a ha hN_pos).monotone hhi
      exact ⟨by linarith, by linarith⟩
  have hIoc_lt : ∀ j : ℤ, c < liftPt a N j → liftPt a N j ≤ c + ℓ → liftPt a N j < c + ℓ := by
    intro j hlo hhi
    have hmem := (hIoc_iff j).mp ⟨hlo, hhi⟩
    have hmono := (liftPt_strictMono a ha hN_pos).monotone hmem.2
    linarith
  set S : Finset ℕ := (Finset.range N).filter (fun k => Int.fract (a k - c) ∈ Set.Ioc (0 : ℝ) ℓ)
  have hScard : S.card = L := by
    have h1 : S.card = arcCount a N c ℓ := rfl
    rw [h1, arcCount_eq_ncard a ha hN_pos c ℓ hℓ_pos.le hℓ_lt_1]
    have hset : {j : ℤ | c < liftPt a N j ∧ liftPt a N j ≤ c + ℓ} =
        ((Finset.Ioc (i₀ : ℤ) ((i₀ : ℤ) + (L : ℤ)) : Finset ℤ) : Set ℤ) := by
      ext j
      simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_Ioc]
      exact hIoc_iff j
    rw [hset, Set.ncard_coe_finset, Int.card_Ioc]
    have hsub : ((i₀ : ℤ) + (L : ℤ)) - (i₀ : ℤ) = (L : ℤ) := by ring
    rw [hsub]
    exact Int.toNat_natCast L
  set e : Fin L ↪o ℕ := S.orderEmbOfFin hScard
  have he_mem : ∀ i : Fin L, e i ∈ S := Finset.orderEmbOfFin_mem S hScard
  have he_range : Set.range e = (S : Set ℕ) := Finset.range_orderEmbOfFin S hScard
  let z : Fin L → ℝ := fun i => Int.fract (a (e i) - c) / ℓ
  have hz_mem : ∀ i : Fin L, z i ∈ Set.Ioo (0 : ℝ) 1 := by
    intro i
    have hiS := he_mem i
    simp only [S, Finset.mem_filter, Finset.mem_range] at hiS
    obtain ⟨hj, hjeq⟩ := exists_liftPt_eq_add_fract a hN_pos c hiS.1
    have hlt : liftPt a N hj < c + ℓ :=
      hIoc_lt hj (by linarith [hiS.2.1]) (by linarith [hiS.2.2])
    have hfr_lt : Int.fract (a (e i) - c) < ℓ := by linarith
    exact ⟨div_pos hiS.2.1 hℓ_pos, (div_lt_one hℓ_pos).mpr hfr_lt⟩
  refine ⟨z, hz_mem, fun j hj x hx => ?_⟩
  rcases Nat.eq_zero_or_pos j with rfl | hj_pos
  · have hemp : Finset.univ.filter (fun i : Fin L => (i : ℕ) < 0 ∧ z i ≤ x) = ∅ := by
      ext i
      simp
    unfold prefixErr
    rw [hemp, Finset.card_empty]
    simp only [Nat.cast_zero, zero_mul, sub_zero, abs_zero]
    linarith
  · set iLast : Fin L := ⟨j - 1, by omega⟩
    set n : ℕ := e iLast + 1
    have hn_pos : 0 < n := Nat.succ_pos _
    have hn_pos_r : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
    have hn_le_N : n ≤ N := by
      have hmem := he_mem iLast
      simp only [S, Finset.mem_filter, Finset.mem_range] at hmem
      exact Nat.succ_le_of_lt hmem.1
    have he_lt_n_iff : ∀ i : Fin L, e i < n ↔ (i : ℕ) < j := by
      intro i
      have h1 : e i < n ↔ e i ≤ e iLast := Nat.lt_succ_iff
      rw [h1, e.le_iff_le]
      change (i : ℕ) ≤ j - 1 ↔ (i : ℕ) < j
      omega
    have hcard_eq : ∀ u ∈ Set.Icc (0 : ℝ) 1,
        (Finset.univ.filter (fun i : Fin L => (i : ℕ) < j ∧ z i ≤ u)).card =
          arcCount a n c (u * ℓ) := by
      intro u hu
      unfold arcCount
      refine Finset.card_bij (fun i _ => e i) ?_ ?_ ?_
      · intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        have hiS := he_mem i
        simp only [S, Finset.mem_filter, Finset.mem_range] at hiS
        simp only [Finset.mem_filter, Finset.mem_range, Set.mem_Ioc]
        refine ⟨(he_lt_n_iff i).mpr hi.1, hiS.2.1, ?_⟩
        exact (div_le_iff₀ hℓ_pos).mp hi.2
      · intro i₁ _ i₂ _ hEq
        exact e.injective hEq
      · intro k hk
        simp only [Finset.mem_filter, Finset.mem_range, Set.mem_Ioc] at hk
        have hkS : k ∈ S := by
          simp only [S, Finset.mem_filter, Finset.mem_range, Set.mem_Ioc]
          refine ⟨lt_of_lt_of_le hk.1 hn_le_N, hk.2.1, ?_⟩
          have : u * ℓ ≤ 1 * ℓ := mul_le_mul_of_nonneg_right hu.2 hℓ_pos.le
          linarith [hk.2.2]
        have hk_ran : k ∈ Set.range e := by
          rw [he_range]
          exact hkS
        obtain ⟨i, hiEq⟩ := hk_ran
        refine ⟨i, ?_, hiEq⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨(he_lt_n_iff i).mp (hiEq.symm ▸ hk.1), ?_⟩
        rw [div_le_iff₀ hℓ_pos]
        exact hiEq.symm ▸ hk.2.2
    have hcard_j : (Finset.univ.filter (fun i : Fin L => (i : ℕ) < j)).card = j := by
      have hbij : (Finset.univ.filter (fun i : Fin L => (i : ℕ) < j)).card =
          (Finset.range j).card := by
        refine Finset.card_bij (fun i _ => (i : ℕ)) ?_ ?_ ?_
        · intro i hi
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
          exact Finset.mem_range.mpr hi
        · intro i₁ _ i₂ _ hEq
          exact Fin.ext hEq
        · intro m hm
          have hm' : m < j := Finset.mem_range.mp hm
          refine ⟨⟨m, lt_of_lt_of_le hm' hj⟩, ?_, rfl⟩
          simp [hm']
      rw [hbij, Finset.card_range]
    have harc_j : arcCount a n c ℓ = j := by
      have h1 := hcard_eq 1 ⟨by norm_num, le_rfl⟩
      rw [one_mul] at h1
      have hfilt : (Finset.univ.filter (fun i : Fin L => (i : ℕ) < j ∧ z i ≤ 1)) =
          Finset.univ.filter (fun i : Fin L => (i : ℕ) < j) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun h => h.1, fun hlt => ⟨hlt, (hz_mem i).2.le⟩⟩
      rw [← h1, hfilt, hcard_j]
    rcases le_or_gt n n₀ with hn_le_n₀ | hn₀_lt_n
    · have hj_le_1 : j ≤ 1 := by
        calc j = arcCount a n c ℓ := harc_j.symm
          _ ≤ arcCount a n₀ c ℓ := arcCount_mono_n a hn_le_n₀ c ℓ
          _ ≤ 1 := arcCount_le_one_of_lt_minSpan a ha hn₀_pos c ℓ hℓ_pos.le hℓ_lt_1 hℓ_lt_δ
      have hj_eq_1 : j = 1 := by omega
      have hcx_le : (Finset.univ.filter (fun i : Fin L => (i : ℕ) < j ∧ z i ≤ x)).card ≤ 1 := by
        calc (Finset.univ.filter (fun i : Fin L => (i : ℕ) < j ∧ z i ≤ x)).card
            ≤ (Finset.univ.filter (fun i : Fin L => (i : ℕ) < j)).card := by
              refine Finset.card_le_card fun i hi => ?_
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
              exact hi.1
          _ = j := hcard_j
          _ = 1 := hj_eq_1
      have hcx_le_r :
          ((Finset.univ.filter (fun i : Fin L => (i : ℕ) < j ∧ z i ≤ x)).card : ℝ) ≤ 1 := by
        exact_mod_cast hcx_le
      have hcx_nonneg :
          (0 : ℝ) ≤ ((Finset.univ.filter (fun i : Fin L => (i : ℕ) < j ∧ z i ≤ x)).card : ℝ) :=
        Nat.cast_nonneg _
      unfold prefixErr
      rw [hj_eq_1] at hcx_le_r hcx_nonneg ⊢
      rw [Nat.cast_one, one_mul, abs_le]
      exact ⟨by linarith [hx.2], by linarith [hx.1]⟩
    · have hcn : CountControl a B L n := hcc n (le_of_lt hn₀_lt_n)
      have hn_le_N_r : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hn_le_N
      have hnℓ_le_L : (n : ℝ) * ℓ ≤ (L : ℝ) :=
        le_trans (mul_le_mul_of_nonneg_right hn_le_N_r hℓ_pos.le) hNℓ_le_L
      set f : ℝ → ℝ := fun u => (arcCount a n c (u * ℓ) : ℝ) - (n : ℝ) * ℓ * u
      have hfx : |f x| ≤ B := by
        have hD0 : 0 ≤ (n : ℝ) * (x * ℓ) := mul_nonneg hn_pos_r.le (mul_nonneg hx.1 hℓ_pos.le)
        have hDL : (n : ℝ) * (x * ℓ) ≤ (L : ℝ) := by
          have hxℓ : x * ℓ ≤ ℓ := by nlinarith [hx.2]
          exact le_trans (mul_le_mul_of_nonneg_left hxℓ hn_pos_r.le) hnℓ_le_L
        have h1 := hcn c ((n : ℝ) * (x * ℓ)) hD0 hDL
        rw [mul_div_cancel_left₀ _ hn_pos_r.ne'] at h1
        have hfeq : f x = (arcCount a n c (x * ℓ) : ℝ) - (n : ℝ) * (x * ℓ) := by
          simp only [f]
          ring
        rw [hfeq]
        exact h1
      have hf1x : |f 1 - f x| ≤ B := by
        have hD0 : 0 ≤ (n : ℝ) * ((1 - x) * ℓ) :=
          mul_nonneg hn_pos_r.le (mul_nonneg (by linarith [hx.2]) hℓ_pos.le)
        have hDL : (n : ℝ) * ((1 - x) * ℓ) ≤ (L : ℝ) := by
          have h1xℓ : (1 - x) * ℓ ≤ ℓ := by nlinarith [hx.1]
          exact le_trans (mul_le_mul_of_nonneg_left h1xℓ hn_pos_r.le) hnℓ_le_L
        have h1 := hcn (c + x * ℓ) ((n : ℝ) * ((1 - x) * ℓ)) hD0 hDL
        rw [mul_div_cancel_left₀ _ hn_pos_r.ne'] at h1
        have hadd := arcCount_add a n c (x * ℓ) ℓ (mul_nonneg hx.1 hℓ_pos.le)
          (by nlinarith [hx.2]) hℓ_lt_1
        have hsub_len : (1 - x) * ℓ = ℓ - x * ℓ := by ring
        rw [hsub_len] at h1
        have hadd_r : (arcCount a n c ℓ : ℝ) =
            (arcCount a n c (x * ℓ) : ℝ) + (arcCount a n (c + x * ℓ) (ℓ - x * ℓ) : ℝ) := by
          exact_mod_cast hadd
        have hdiff : f 1 - f x =
            (arcCount a n (c + x * ℓ) (ℓ - x * ℓ) : ℝ) - (n : ℝ) * (ℓ - x * ℓ) := by
          simp only [f, one_mul]
          rw [hadd_r]
          ring
        rw [hdiff]
        exact h1
      have herr_eq : prefixErr z j x = (1 - x) * f x - x * (f 1 - f x) := by
        unfold prefixErr
        rw [hcard_eq x hx]
        have hj_r : (j : ℝ) = (arcCount a n c ℓ : ℝ) := by exact_mod_cast harc_j.symm
        rw [hj_r]
        simp only [f, one_mul]
        ring
      rw [herr_eq]
      have htri : |(1 - x) * f x - x * (f 1 - f x)| ≤
          |(1 - x) * f x| + |x * (f 1 - f x)| := abs_sub _ _
      rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr hx.2), abs_of_nonneg hx.1] at htri
      have hmul1 : (1 - x) * |f x| ≤ (1 - x) * B :=
        mul_le_mul_of_nonneg_left hfx (sub_nonneg.mpr hx.2)
      have hmul2 : x * |f 1 - f x| ≤ x * B :=
        mul_le_mul_of_nonneg_left hf1x hx.1
      linarith

/- ## G: assembly (lead) -/

/-- G1 (Theorem R): for every fixed `A ≥ 1`, once `r` is large, every sequence of distinct points
has `limsup M / m ≥ 1 + A / r`. -/
theorem ratio_lower_bound (A : ℝ) (hA : 1 ≤ A) :
    ∃ r₀ : ℕ, ∀ r ≥ r₀, ∀ a : ℕ → ℝ, Function.Injective (fun k => Int.fract (a k)) →
      ENNReal.ofReal (1 + A / r) ≤
        limsup (fun n : ℕ => ENNReal.ofReal (Erdos1221.maxSpan a n r) /
          ENNReal.ofReal (Erdos1221.minSpan a n r)) atTop := by
  obtain ⟨t, ht⟩ := exists_nat_gt (128 * (3 * A + 1))
  obtain ⟨r₁, hr₁⟩ := count_control_of_span_control A ((3 ^ t : ℕ) : ℝ) hA (by positivity)
  refine ⟨max r₁ 1, fun r hr a ha => ?_⟩
  have hr1 : 1 ≤ r := le_trans (le_max_right _ _) hr
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨C, hC0, hCA, hev⟩ :=
    eventually_ratio_le_of_limsup_lt a ha r hr1 A (by linarith) hlt
  have hspan := span_control_of_ratio a ha r hr1 A C hC0 hCA hev
  have hcount := hr₁ r (le_trans (le_max_left _ _) hr) a ha hspan
  have ht1 : 1 ≤ t := by
    have h1 : (1 : ℝ) < t := by linarith
    exact_mod_cast h1.le
  have hL : 2 ≤ 3 ^ t :=
    calc 2 ≤ 3 ^ 1 := by norm_num
      _ ≤ 3 ^ t := Nat.pow_le_pow_right (by norm_num) ht1
  obtain ⟨z, hz01, hzB⟩ := localize a ha (3 * A + 1 / 2) (by linarith) (3 ^ t) hL hcount
  obtain ⟨j, hj, x, hx, hW⟩ :=
    crude_discrepancy t z (fun i => ⟨(hz01 i).1.le, (hz01 i).2⟩)
  have hB := hzB j hj x ⟨hx.1, hx.2.le⟩
  have hlt' : 3 * A + 1 / 2 < (t : ℝ) / 128 := by
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 128)]
    linarith
  linarith

end Erdos1221Ratio

/-- Erdős 1221 part iii: `r (μ_r - 1) → ∞`. -/
theorem OMA.solution : type_of% @Erdos1221.erdos_1221.parts.iii := by
  intro K
  have hA1 : (1 : ℝ) ≤ max K 0 + 1 := by
    have := le_max_right K 0
    linarith
  obtain ⟨r₀, hr₀⟩ := Erdos1221Ratio.ratio_lower_bound (max K 0 + 1) hA1
  filter_upwards [Filter.eventually_ge_atTop (max r₀ 1)] with r hr
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast le_trans (le_max_right _ _) hr
  have hrpos : (0 : ℝ) < r := by linarith
  have hle : ENNReal.ofReal (1 + (max K 0 + 1) / r) ≤ Erdos1221.mu r := by
    unfold Erdos1221.mu
    exact le_iInf₂ fun a ha => hr₀ r (le_trans (le_max_left _ _) hr) a ha
  refine lt_of_lt_of_le ?_ hle
  have hdiv : K / r < (max K 0 + 1) / r := by
    have := le_max_left K 0
    exact (div_lt_div_iff_of_pos_right hrpos).2 (by linarith)
  have hpos : 0 < 1 + (max K 0 + 1) / r := by
    have : 0 ≤ (max K 0 + 1) / r := div_nonneg (by linarith) hrpos.le
    linarith
  exact (ENNReal.ofReal_lt_ofReal_iff hpos).2 (by linarith)
