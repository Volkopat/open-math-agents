import FormalConjectures.ErdosProblems.«288»

-- Reduction Erdos288.erdos_288.variants.exists_k_gt_2.R1 of Erdős problem 288 (some k > 2)
-- Credit: @LordMike
-- Credit: @desenyon (PR #2237): H1 and every lemma below are taken from the merged reduction
-- Erdos288.erdos_288.variants.k_intervals.R1; only H2 and main are new.
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Erdős 288 for some k > 2, from relative prime gaps and scale separation for one k

The target asks for one `k > 2` such that only finitely many families of `k` intervals have an
integer total reciprocal sum. The merged reduction of the sibling `k_intervals` (all `k`) proves
finiteness for each fixed `k` from two inputs, and its proof is uniform in `k`. So here the
scale-separation input is needed for a single `k > 2` only.

* `H1` (known, deep): for every `ε > 0` and every large `B` there is a prime in `(B / (1 + ε), B]`.
  This follows from the prime number theorem. It is the same statement, character for character,
  as `H1` of `Erdos288.erdos_288.variants.k_intervals.R1`.
* `H2` (open): for SOME `k > 2` there are `C` and `L` such that, in every family of `k` intervals
  with integer total, each interval longer than `L` has its right endpoint within a factor `C` of
  every other right endpoint. This is `H2` of the sibling reduction with `∀ k` replaced by
  `∃ k > 2`, so it is weaker than that hypothesis. It is implied by the target for the same `k`
  (a finite set of families has such a `C`), so given `H1` it is equivalent to the target: the
  reduction isolates the open core, it does not shrink it.

`main` takes the `k` of `H2` and applies `finite_fixed_scales` of the sibling reduction.
-/

namespace OMA.R_Erdos288_erdos_288_variants_exists_k_gt_2_R1

/-- Primes occur arbitrarily close in relative terms below every sufficiently large endpoint. -/
def H1 : Prop :=
  ∀ ε : ℚ, 0 < ε → ∃ N : ℕ, ∀ B : ℕ+, N ≤ B →
    ∃ p : ℕ+, (p : ℕ).Prime ∧ p ≤ B ∧ (B : ℚ) < (1 + ε) * p

/-- For some number of intervals `k > 2`: a sufficiently long block has its right endpoint
within a fixed factor of every other right endpoint. -/
def H2 : Prop :=
  ∃ k : ℕ, 2 < k ∧ ∃ C L : ℕ, 0 < C ∧ ∀ I : Fin k → ℕ+ × ℕ+,
    (∀ j, (I j).1 ≤ (I j).2) →
    (∃ n : ℕ+, (∑ j, ∑ d ∈ Set.Icc (I j).1 (I j).2, (d⁻¹ : ℚ)) = n) →
    ∀ i j, L < (Finset.Icc (I i).1 (I i).2).card →
      ((I j).2 : ℕ) ≤ C * ((I i).2 : ℕ)

/-- For a fixed number of unit fractions, every positive deficit from a natural number
is uniformly bounded away from zero. The natural number may vary. -/
lemma unit_fraction_gap (t : ℕ) :
    ∃ δ : ℚ, 0 < δ ∧ ∀ (n : ℕ) (f : Fin t → ℕ+),
      (∑ i, ((f i : ℕ) : ℚ)⁻¹) < n → δ ≤ n - ∑ i, ((f i : ℕ) : ℚ)⁻¹ := by
  let D (x : ℕ × (Fin t → ℕ+)) : ℚ := x.1 - ∑ i, ((x.2 i : ℕ) : ℚ)⁻¹
  have monoD : Monotone D := by
    intro x y h
    apply sub_le_sub
    · exact_mod_cast h.1
    · apply Finset.sum_le_sum
      intro i _
      exact inv_anti₀ (by exact_mod_cast (x.2 i).property) (by exact_mod_cast h.2 i)
  let S := {x | 0 < D x}
  have hS : S.Nonempty := by
    refine ⟨(t+1, fun _ => 1), ?_⟩
    simp [S, D]
  have ordered := (Set.isPWO_of_wellQuasiOrderedLE S).image_of_monotone monoD
  obtain ⟨q, hq, hmin⟩ := ordered.exists_minimal (hS.image D)
  obtain ⟨x, hx, rfl⟩ := hq
  refine ⟨D x, hx, ?_⟩
  intro n f hf
  have hmem : D (n, f) ∈ D '' S := ⟨(n, f), sub_pos.mpr hf, rfl⟩
  exact le_of_not_gt fun h => h.not_ge (hmin hmem h.le)

/-- A single lower bound works for every number of terms up to L. -/
lemma bounded_unit_fraction_gap (L : ℕ) :
    ∃ δ : ℚ, 0 < δ ∧ ∀ (α : Type) [Fintype α], Fintype.card α ≤ L →
    ∀ (n : ℕ) (f : α → ℕ+), (∑ i, ((f i : ℕ) : ℚ)⁻¹) < n →
      δ ≤ n - ∑ i, ((f i : ℕ) : ℚ)⁻¹ := by
  classical
  choose δ hpos hbound using unit_fraction_gap
  let values := (Finset.range (L+1)).image δ
  have hn : values.Nonempty := ⟨δ 0, Finset.mem_image.mpr ⟨0, by simp, rfl⟩⟩
  refine ⟨values.min' hn, ?_, ?_⟩
  · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (Finset.min'_mem values hn)
    rw [← hi]
    exact hpos i
  · intro α inst hcard n f hf
    let e := Fintype.equivFin α
    have he : (∑ i : Fin (Fintype.card α), ((f (e.symm i) : ℕ) : ℚ)⁻¹) =
        ∑ i, ((f i : ℕ) : ℚ)⁻¹ := e.symm.sum_comp (fun i : α => ((f i : ℕ) : ℚ)⁻¹)
    have hb := hbound (Fintype.card α) n (fun i => f (e.symm i)) (by rwa [he])
    rw [he] at hb
    exact (Finset.min'_le _ _ (Finset.mem_image.mpr ⟨_, Finset.mem_range.mpr (by omega), rfl⟩)).trans hb

/-- Omitting a prime from the denominators is preserved by finite addition. -/
lemma prime_free_sum {p : ℕ} (hp : p.Prime) {α : Type*} (s : Finset α) (f : α → ℚ)
    (h : ∀ x ∈ s, ¬ p ∣ (f x).den) : ¬ p ∣ (∑ x ∈ s, f x).den := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hp.not_dvd_one
  | @insert x s hx ih =>
    rw [Finset.sum_insert hx]
    intro hd
    rcases hp.dvd_mul.mp (hd.trans (Rat.add_den_dvd _ _)) with ha | hb
    · exact h x (Finset.mem_insert_self ..) ha
    · exact ih (fun y hy => h y (Finset.mem_insert_of_mem hy)) hb

/-- A large prime with bounded cofactors cannot divide a covered denominator.
Multiplication by M! clears the cofactors. Their positive contribution has numerator
at most k M M! when put over p. -/
lemma prime_avoids_blocks {k M : ℕ} (I : Fin k → ℕ+ × ℕ+) {p : ℕ+}
    (hp : (p : ℕ).Prime) (big : k * M * M.factorial < (p : ℕ))
    (top : ∀ j, ((I j).2 : ℕ) ≤ M * (p : ℕ))
    {n : ℕ+} (hn : (∑ j, ∑ d ∈ Set.Icc (I j).1 (I j).2, (d⁻¹ : ℚ)) = n) :
    ∀ j d, d ∈ Set.Icc (I j).1 (I j).2 → ¬ (p : ℕ) ∣ (d : ℕ) := by
  classical
  let s := Finset.univ.sigma fun j => Finset.Icc (I j).1 (I j).2
  let a := s.filter fun x => (p : ℕ) ∣ (x.2 : ℕ)
  let b := s.filter fun x => ¬ (p : ℕ) ∣ (x.2 : ℕ)
  let co (x : Σ _ : Fin k, ℕ+) := (x.2 : ℕ) / (p : ℕ)
  have cancel (x) (hx : x ∈ a) : co x * (p : ℕ) = (x.2 : ℕ) :=
    Nat.div_mul_cancel (Finset.mem_filter.mp hx).2
  have cpos (x) (hx : x ∈ a) : 0 < co x := by
    apply Nat.pos_of_ne_zero
    intro hz
    exact x.2.ne_zero ((cancel x hx).symm.trans (by rw [hz, Nat.zero_mul]))
  have cle (x) (hx : x ∈ a) : co x ≤ M := by
    refine Nat.le_of_mul_le_mul_right (c := (p : ℕ)) ?_ p.property
    rw [cancel x hx]
    have hd : (x.2 : ℕ) ≤ ((I x.1).2 : ℕ) :=
      (Finset.mem_Icc.mp (Finset.mem_sigma.mp (Finset.mem_filter.mp hx).1).2).2
    exact hd.trans (top x.1)
  have card : a.card ≤ k * M := by
    calc
      _ ≤ ((Finset.univ : Finset (Fin k)) ×ˢ Finset.Icc 1 M).card := by
        apply Finset.card_le_card_of_injOn (fun x => (x.1, co x))
        · intro x hx
          exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_Icc.mpr ⟨cpos x hx, cle x hx⟩⟩
        · rintro ⟨j, u⟩ hu ⟨i, v⟩ hv eq
          obtain rfl : j = i := congrArg Prod.fst eq
          have hc := congrArg Prod.snd eq
          have huv : (u : ℕ) = v := (cancel _ hu).symm.trans
            ((congrArg (· * (p : ℕ)) hc).trans (cancel _ hv))
          obtain rfl : u = v := Subtype.ext huv
          rfl
      _ = _ := by simp
  let A := ∑ x ∈ a, M.factorial / co x
  have smallA : A < (p : ℕ) :=
    (calc
      A ≤ a.card * M.factorial := by
        simpa only [smul_eq_mul] using a.sum_le_card_nsmul (fun x => M.factorial / co x)
          M.factorial (fun x _ => Nat.div_le_self _ _)
      _ ≤ k * M * M.factorial := Nat.mul_le_mul_right _ card).trans_lt big
  let w (x : Σ _ : Fin k, ℕ+) : ℚ := (M.factorial : ℚ) * ((x.2 : ℕ) : ℚ)⁻¹
  let r := ∑ x ∈ b, w x
  have hr : ¬ (p : ℕ) ∣ r.den := by
    apply prime_free_sum hp
    intro x hx h
    rcases hp.dvd_mul.mp (h.trans (Rat.mul_den_dvd _ _)) with h1 | h2
    · exact hp.not_dvd_one (by simpa using h1)
    · rw [Rat.den_inv_of_ne_zero (by exact_mod_cast x.2.ne_zero)] at h2
      exact (Finset.mem_filter.mp hx).2 (by simpa using h2)
  have ha : (∑ x ∈ a, w x) = (A : ℚ) / p := by
    unfold A
    push_cast
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro x hx
    have hd := Nat.dvd_factorial (cpos x hx) (cle x hx)
    rw [Nat.cast_div hd (by exact_mod_cast (cpos x hx).ne' : (co x : ℚ) ≠ 0)]
    have hprod : ((co x : ℚ) * p) = (x.2 : ℚ) := by exact_mod_cast cancel x hx
    dsimp only [w]
    rw [← hprod]
    ring
  have hs : (∑ x ∈ s, ((x.2 : ℕ) : ℚ)⁻¹) = n := by
    simpa only [s, Finset.sum_sigma, Set.toFinset_Icc] using hn
  have split := Finset.sum_filter_add_sum_filter_not s (fun x => (p : ℕ) ∣ (x.2 : ℕ)) w
  change (∑ x ∈ a, w x) + r = ∑ x ∈ s, (M.factorial : ℚ) * ((x.2 : ℕ) : ℚ)⁻¹ at split
  rw [ha, ← Finset.mul_sum, hs] at split
  intro j d hj hpd
  have hm : (⟨j, d⟩ : Σ _ : Fin k, ℕ+) ∈ a := Finset.mem_filter.mpr
    ⟨Finset.mem_sigma.mpr ⟨Finset.mem_univ _, Finset.mem_Icc.mpr hj⟩, hpd⟩
  have hpos : 0 < A := Finset.sum_pos (fun x hx =>
    Nat.div_pos (Nat.le_of_dvd (Nat.factorial_pos _) (Nat.dvd_factorial (cpos x hx) (cle x hx)))
      (cpos x hx)) ⟨_, hm⟩
  have hcop := (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hpos smallA)).symm
  have hden : ((A : ℚ) / p).den = (p : ℕ) := by
    apply Int.ofNat_inj.mp
    simpa only [Int.cast_natCast, Int.natAbs_natCast] using Rat.den_div_eq_of_coprime
      (a := (A : ℤ)) (b := ((p : ℕ) : ℤ)) (by exact_mod_cast p.property) (by simpa using hcop)
  have hsub : (A : ℚ) / p = ((M.factorial * (n : ℕ) : ℕ) : ℚ) - r := by
    push_cast
    linarith
  rw [hsub, Rat.natCast_sub_den] at hden
  exact hr (hden ▸ dvd_refl _)

/-- Every block whose endpoint is comparable with the greatest endpoint has uniformly
small reciprocal sum as the latter endpoint grows. -/
lemma light_comparable_block (primes : H1) (k C : ℕ) (ε : ℚ) (εpos : 0 < ε) :
    ∃ T : ℕ, ∀ (I : Fin k → ℕ+ × ℕ+) (B : ℕ+),
      T < (B : ℕ) → (∀ i, (I i).2 ≤ B) →
      (∃ n : ℕ+, (∑ i, ∑ d ∈ Set.Icc (I i).1 (I i).2, (d⁻¹ : ℚ)) = n) →
      ∀ j, (B : ℕ) ≤ C * ((I j).2 : ℕ) →
        (∑ d ∈ Finset.Icc (I j).1 (I j).2, (d⁻¹ : ℚ)) < ε := by
  classical
  let M := 2 * C
  let ε' := min 1 ε
  obtain ⟨N, hN⟩ := primes ε' (lt_min (by norm_num) εpos)
  let U := max N (2 * (k * M * M.factorial + 1))
  refine ⟨C * U, ?_⟩
  intro I B hB top ⟨n, hn⟩ j comparable
  let b := (I j).2
  have hUb : U < (b : ℕ) := by
    by_contra! h
    exact (not_le_of_gt hB) (comparable.trans (Nat.mul_le_mul_left C h))
  have hNle : N ≤ U := le_max_left ..
  obtain ⟨p, hp, hpb, close⟩ := hN b (hNle.trans hUb.le)
  have hpq : 0 < (p : ℚ) := by exact_mod_cast p.property
  have ht : (b : ℕ) < 2 * (p : ℕ) := by
    have hr : (b : ℚ) < 2 * (p : ℚ) := close.trans_le (mul_le_mul_of_nonneg_right
      (by linarith [show ε' ≤ 1 from min_le_left _ _]) hpq.le)
    exact_mod_cast hr
  have hsize : 2 * (k * M * M.factorial + 1) ≤ U := le_max_right ..
  have cap : (B : ℕ) ≤ M * (p : ℕ) := calc
    _ ≤ C * (b : ℕ) := comparable
    _ ≤ C * (2 * (p : ℕ)) := Nat.mul_le_mul_left _ ht.le
    _ = _ := by dsimp [M]; ring
  have hole := prime_avoids_blocks I hp (by omega : k * M * M.factorial < (p : ℕ))
    (fun i => le_trans (show ((I i).2 : ℕ) ≤ B from top i) cap) hn j p
  have start : p < (I j).1 := lt_of_not_ge fun h => hole ⟨h, hpb⟩ (dvd_refl _)
  let block := Finset.Icc (I j).1 b
  have sub : block ⊆ Finset.Ioc p b := fun d hd =>
    Finset.mem_Ioc.mpr ⟨start.trans_le (Finset.mem_Icc.mp hd).1, (Finset.mem_Icc.mp hd).2⟩
  have card : block.card ≤ (b : ℕ) - p := by simpa using Finset.card_le_card sub
  have cardQ : (block.card : ℚ) ≤ (b : ℚ) - p := by
    rw [← Nat.cast_sub (show (p : ℕ) ≤ b from hpb)]
    exact_mod_cast card
  have sumle : (∑ d ∈ block, (d⁻¹ : ℚ)) ≤ (block.card : ℚ) * (p : ℚ)⁻¹ := by
    simpa only [nsmul_eq_mul] using block.sum_le_card_nsmul (fun d => (d⁻¹ : ℚ))
      (p : ℚ)⁻¹ (fun d hd => inv_anti₀ hpq (by exact_mod_cast (Finset.mem_Ioc.mp (sub hd)).1.le))
  calc
    _ ≤ (block.card : ℚ) * (p : ℚ)⁻¹ := sumle
    _ ≤ ((b : ℚ) - p) * (p : ℚ)⁻¹ := mul_le_mul_of_nonneg_right cardQ (inv_nonneg.mpr hpq.le)
    _ < ε' := by rw [← div_eq_mul_inv]; exact (div_lt_iff₀ hpq).mpr (by linarith)
    _ ≤ ε := min_le_right _ _

/-- Finiteness for any fixed k,C,L on the subfamily in which every interval is
short or ends within a factor C of the greatest endpoint. -/
lemma finite_fixed_scales (primes : H1) (k C L : ℕ) (hC : 0 < C) :
    Set.Finite { I : Fin k → ℕ+ × ℕ+ |
      (∀ j, (I j).1 ≤ (I j).2 ∧ ∃ n : ℕ+,
        (∑ i, ∑ d ∈ Set.Icc (I i).1 (I i).2, (d⁻¹ : ℚ)) = n) ∧
      ∀ i j, L < (Finset.Icc (I i).1 (I i).2).card →
        ((I j).2 : ℕ) ≤ C * ((I i).2 : ℕ) } := by
  classical
  cases k with
  | zero => exact Set.toFinite _
  | succ m =>
    let k := m + 1
    obtain ⟨δ, hδ, gap⟩ := bounded_unit_fraction_gap (k * L)
    let ε := δ / (k + 1 : ℚ)
    have he : 0 < ε := div_pos hδ (by positivity)
    have hed : ε * (k + 1 : ℚ) = δ := div_mul_cancel₀ _ (by positivity)
    obtain ⟨T, light⟩ := light_comparable_block primes k C ε he
    let U : ℕ+ := ⟨T + 1, by omega⟩
    let box := Set.Icc (1 : ℕ+) U
    apply (Set.Finite.pi' (ι := Fin k) (t := fun _ => box ×ˢ box)
      (fun _ => (Set.finite_Icc _ _).prod (Set.finite_Icc _ _))).subset
    rintro I ⟨hI, hL⟩
    have ordered (j : Fin k) := (hI j).1
    obtain ⟨n, hn⟩ := (hI (0 : Fin (m + 1))).2
    obtain ⟨j, _, hj⟩ := Finset.exists_max_image Finset.univ (fun i => (I i).2)
      ⟨(0 : Fin (m + 1)), Finset.mem_univ _⟩
    let B := (I j).2
    have top (i : Fin k) : (I i).2 ≤ B := hj i (Finset.mem_univ _)
    suffices bound : B ≤ U by
      intro i
      exact ⟨⟨one_le, (ordered i).trans ((top i).trans bound)⟩,
        one_le, (top i).trans bound⟩
    by_contra! large
    have hB : T < (B : ℕ) := lt_trans (Nat.lt_succ_self T) (show T+1 < (B : ℕ) from large)
    let block (i : Fin k) := Finset.Icc (I i).1 (I i).2
    let weight (i : Fin k) := ∑ d ∈ block i, (d⁻¹ : ℚ)
    let low := Finset.univ.filter fun i => C * ((I i).2 : ℕ) < (B : ℕ)
    let high := Finset.univ.filter fun i => ¬ C * ((I i).2 : ℕ) < (B : ℕ)
    have hsplit : (∑ i ∈ low, weight i) + (∑ i ∈ high, weight i) = n := by
      rw [show (∑ i ∈ low, weight i) + (∑ i ∈ high, weight i) = ∑ i, weight i from
        Finset.sum_filter_add_sum_filter_not ..]
      simpa only [Set.toFinset_Icc, weight, block] using hn
    have hcard (i) (hi : i ∈ low) : (block i).card ≤ L := by
      by_contra! hw
      exact (not_le_of_gt (Finset.mem_filter.mp hi).2) (hL i j hw)
    let terms := low.sigma block
    have lc : Fintype.card terms ≤ k * L := by
      rw [Fintype.card_coe, Finset.card_sigma]
      have hc : low.card ≤ k := by simpa using Finset.card_le_card (Finset.subset_univ low)
      exact (low.sum_le_card_nsmul (fun i => (block i).card) L hcard).trans (Nat.mul_le_mul_right _ hc)
    have hl : (∑ x : terms, ((x.val.2 : ℕ) : ℚ)⁻¹) = ∑ i ∈ low, weight i := by
      rw [Finset.sum_coe_sort terms (fun x => ((x.2 : ℕ) : ℚ)⁻¹)]
      exact Finset.sum_sigma ..
    have hjhigh : j ∈ high := Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, not_lt.mpr (Nat.le_mul_of_pos_left _ hC)⟩
    have hpos : 0 < ∑ i ∈ high, weight i := by
      apply Finset.sum_pos _ ⟨_, hjhigh⟩
      intro i _
      exact Finset.sum_pos (fun d _ => inv_pos.mpr (by exact_mod_cast d.property))
        ⟨_, Finset.mem_Icc.mpr ⟨le_rfl, ordered i⟩⟩
    have lb := gap terms lc (n : ℕ) (fun x => x.val.2)
    rw [hl] at lb
    have hd := lb (by linarith)
    have small (i) (hi : i ∈ high) : weight i ≤ ε :=
      (light I B hB top ⟨n, hn⟩ i (le_of_not_gt (Finset.mem_filter.mp hi).2)).le
    have ub : (∑ i ∈ high, weight i) ≤ (k : ℚ) * ε := by
      have hc : high.card ≤ k := by simpa using Finset.card_le_card (Finset.subset_univ high)
      calc
        _ ≤ (high.card : ℚ) * ε := by simpa only [nsmul_eq_mul] using high.sum_le_card_nsmul weight ε small
        _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hc) he.le
    nlinarith

theorem main : H1 → H2 → type_of% @Erdos288.erdos_288.variants.exists_k_gt_2 := by
  rintro primes ⟨k, hk, C, L, hC, hL⟩
  refine ⟨k, hk, (finite_fixed_scales primes k C L hC).subset ?_⟩
  intro I hI
  exact ⟨hI, hL I (fun j => (hI j).1) (hI ⟨0, by omega⟩).2⟩

end OMA.R_Erdos288_erdos_288_variants_exists_k_gt_2_R1
