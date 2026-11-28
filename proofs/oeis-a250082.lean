import OMAStatements.S_oeis_a250082
import Mathlib

/-!
# Counting six entries with equal second and third order statistics

Credit: @jacklarmer

The window condition is invariant under increasing relabelings of the
alphabet. Split a word into its range and the surjective word obtained by
replacing those values with their ranks. All rank patterns with a fixed
range size are counted once for every subset of that size. The finite
rank counts yield a binomial expansion, which gives the recurrence and
the generating series after correcting its constant coefficient.
-/

namespace RankCount

def Good {d : ℕ} (x : Fin 6 → Fin d) : Prop :=
  ∃ S ∈ (Finset.univ : Finset (Fin 6)).powersetCard 2,
    ∃ j ∈ S, ∃ k ∉ S, x j = x k ∧ (∀ i ∈ S, x i ≤ x j) ∧ (∀ i ∉ S, x k ≤ x i)

theorem good_comp_iff {d e : ℕ} (f : Fin d ↪o Fin e) (x : Fin 6 → Fin d) :
    Good (f ∘ x) ↔ Good x := by
  simp [Good]

open OMA.S_oeis_a250082 in
theorem good_iff {n : ℕ} (x : Fin 6 → Fin (n + 1)) :
    good x = true ↔ Good x := by
  have entry (t : Fin 6) : OMA.S_oeis_a250082.get x t = (x t : ℕ) := by
    simp [OMA.S_oeis_a250082.get, t.isLt]
  rw [good, decide_eq_true_eq]
  constructor
  · intro h
    specialize h 0 (by decide)
    simp only [Nat.zero_add, entry] at h
    obtain ⟨S, hS, v, _, hle, ⟨j, hj, hjv⟩, hge, k, hk, hkv⟩ := h
    refine ⟨S, hS, j, hj, k, hk, Fin.ext (hjv.trans hkv.symm), ?_, ?_⟩
    · intro i hi
      exact (hle i hi).trans_eq hjv.symm
    · intro i hi
      exact hkv.trans_le (hge i hi)
  · rintro ⟨S, hS, j, hj, k, hk, hjk, hle, hge⟩ i hi
    have : i = 0 := by omega
    subst i
    simp only [Nat.zero_add, entry]
    exact ⟨S, hS, (x k : ℕ), (x k).isLt, fun t ht => (hle t ht).trans_eq hjk,
      ⟨j, hj, congrArg Fin.val hjk⟩, hge, k, hk, rfl⟩

end RankCount

namespace RankCount

theorem good_iff_fastRank {d : ℕ} (x : Fin 6 → Fin d) :
    Good x ↔ ∃ v : Fin d,
      (Finset.univ.filter fun i => x i < v).card ≤ 1 ∧
      3 ≤ (Finset.univ.filter fun i => x i ≤ v).card := by
  constructor
  · rintro ⟨S, hS, j, hj, k, hk, hjk, hle, hge⟩
    have hcard : S.card = 2 := (Finset.mem_powersetCard.mp hS).2
    refine ⟨x j, ?_, ?_⟩
    · have hsub : (Finset.univ.filter fun i => x i < x j) ⊆ S.erase j := by
        intro i hi
        have hlt := (Finset.mem_filter.mp hi).2
        apply Finset.mem_erase.mpr
        refine ⟨fun h => (ne_of_lt hlt) (congrArg x h), ?_⟩
        by_contra hnot
        exact hlt.not_ge (hjk.trans_le (hge i hnot))
      simpa [Finset.card_erase_of_mem hj, hcard] using Finset.card_le_card hsub
    · have hsub : insert k S ⊆ Finset.univ.filter fun i => x i ≤ x j := by
        intro i hi
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        rcases Finset.mem_insert.mp hi with rfl | h
        · exact hjk.symm.le
        · exact hle i h
      simpa [Finset.card_insert_of_notMem hk, hcard] using Finset.card_le_card hsub
  · rintro ⟨v, hl, hu⟩
    let L := Finset.univ.filter fun i => x i < v
    let U := Finset.univ.filter fun i => x i ≤ v
    change L.card ≤ 1 at hl
    change 3 ≤ U.card at hu
    have hLU : L ⊆ U := by
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2.le⟩
    obtain ⟨S, hLS, hSU, hS⟩ := Finset.exists_subsuperset_card_eq hLU (show L.card ≤ 2 by omega) (show 2 ≤ U.card by omega)
    obtain ⟨j, hj, hjL⟩ := Finset.exists_mem_notMem_of_card_lt_card (show L.card < S.card by omega)
    obtain ⟨k, hkU, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card (show S.card < U.card by omega)
    have inside (i) (hi : i ∈ S) : x i ≤ v := (Finset.mem_filter.mp (hSU hi)).2
    have outside (i) (hi : i ∉ S) : v ≤ x i := by
      apply le_of_not_gt
      exact fun h => hi (hLS (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
    have hjv : x j = v := le_antisymm (inside j hj) (le_of_not_gt fun h => hjL (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
    have hkv : x k = v := le_antisymm (Finset.mem_filter.mp hkU).2 (outside k hk)
    exact ⟨S, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hS⟩, j, hj, k, hk, hjv.trans hkv.symm,
      fun i hi => (inside i hi).trans_eq hjv.symm, fun i hi => hkv.trans_le (outside i hi)⟩

theorem good_iff_fast {d : ℕ} (x : Fin 6 → Fin d) :
    Good x ↔ ∃ j : Fin 6,
      (Finset.univ.filter fun i => x i < x j).card ≤ 1 ∧
      3 ≤ (Finset.univ.filter fun i => x i ≤ x j).card := by
  rw [good_iff_fastRank]
  constructor
  · rintro ⟨v, hl, hu⟩
    obtain ⟨j, hjU, hjL⟩ := Finset.exists_mem_notMem_of_card_lt_card (lt_of_le_of_lt hl (lt_of_lt_of_le (by decide : 1 < 3) hu))
    have hj : x j = v := le_antisymm (Finset.mem_filter.mp hjU).2 (le_of_not_gt fun h => hjL (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
    exact ⟨j, hj ▸ hl, hj ▸ hu⟩
  · rintro ⟨j, hl, hu⟩
    exact ⟨x j, hl, hu⟩

end RankCount


namespace RankCount

def histogramList (d : ℕ) (xs : List ℕ) : Bool :=
  (List.range d).all (fun v => xs.contains v) &&
    (List.range (min d 2)).any fun v =>
      decide (xs.countP (fun z => decide (z < v)) ≤ 1) &&
      decide (3 ≤ xs.countP (fun z => decide (z ≤ v)))

def histogramTest {d : ℕ} (x : Fin 6 → Fin d) : Bool :=
  histogramList d ((List.ofFn x).map Fin.val)

lemma histogram_count {d : ℕ} (x : Fin 6 → Fin d) (p : ℕ → Prop) [DecidablePred p] :
    (((List.ofFn x).map Fin.val).countP (fun z => decide (p z))) =
      (Finset.univ.filter (fun i => p (x i).val)).card := by
  rw [List.ofFn_eq_map, List.countP_map, List.countP_map, List.countP_eq_length_filter]
  rfl

theorem histogramTest_iff {d : ℕ} (x : Fin 6 → Fin d) :
    histogramTest x = true ↔ Function.Surjective x ∧ ∃ j : Fin 6,
      (Finset.univ.filter (fun i => x i < x j)).card ≤ 1 ∧
      3 ≤ (Finset.univ.filter (fun i => x i ≤ x j)).card := by
  have hmem (v : ℕ) : v ∈ (List.ofFn x).map Fin.val ↔ ∃ i, (x i).val = v := by
    simp only [List.mem_map, List.mem_ofFn]
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, hv⟩
      exact ⟨i, hv⟩
    · rintro ⟨i, hv⟩
      exact ⟨_, ⟨i, rfl⟩, hv⟩
  simp only [histogramTest, histogramList, Bool.and_eq_true, List.all_eq_true,
    List.any_eq_true, List.mem_range, List.contains_iff_mem, hmem, decide_eq_true_eq,
    histogram_count]
  constructor
  · rintro ⟨hs, v, hv, hlo, hhi⟩
    have hvd : v < d := lt_of_lt_of_le hv (min_le_left _ _)
    obtain ⟨j, hj⟩ := hs v hvd
    refine ⟨fun z => ?_, j, ?_, ?_⟩
    · obtain ⟨i, hi⟩ := hs z.val z.isLt
      exact ⟨i, Fin.ext hi⟩
    · change (Finset.univ.filter (fun i => (x i).val < (x j).val)).card ≤ 1
      simpa only [hj] using hlo
    · change 3 ≤ (Finset.univ.filter (fun i => (x i).val ≤ (x j).val)).card
      simpa only [hj] using hhi
  · rintro ⟨hs, j, hlo, hhi⟩
    refine ⟨fun v hv => ?_, (x j).val, ?_, hlo, hhi⟩
    · obtain ⟨i, hi⟩ := hs ⟨v, hv⟩
      exact ⟨i, congrArg Fin.val hi⟩
    · apply lt_min (x j).isLt
      by_contra! h
      have hlt := (x j).isLt
      obtain ⟨a, ha⟩ := hs ⟨0, by omega⟩
      obtain ⟨b, hb⟩ := hs ⟨1, by omega⟩
      have ha' : (x a).val = 0 := congrArg Fin.val ha
      have hb' : (x b).val = 1 := congrArg Fin.val hb
      apply (Nat.not_lt_of_ge hlo)
      refine Finset.one_lt_card.mpr ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩,
        b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · change (x a).val < (x j).val
        omega
      · change (x b).val < (x j).val
        omega
      · intro hab
        subst b
        omega

end RankCount


namespace RankCount

def foldWords (d : ℕ) : ℕ → (List ℕ → ℕ) → ℕ
  | 0, f => f []
  | r+1, f => (List.ofFn fun a : Fin d => foldWords d r (fun xs => f (a.val :: xs))).sum

theorem sum_words (d r : ℕ) (f : List ℕ → ℕ) :
    (∑ x : Fin r → Fin d, f ((List.ofFn x).map Fin.val)) = foldWords d r f := by
  induction r generalizing f with
  | zero => simp [foldWords]
  | succ r ih =>
    rw [foldWords, List.sum_ofFn]
    let e := Fin.consEquiv (fun _ : Fin (r+1) => Fin d)
    rw [← e.sum_comp (fun x => f ((List.ofFn x).map Fin.val)), Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro a _
    rw [← ih]
    apply Finset.sum_congr rfl
    intro b _
    simp [e, Fin.consEquiv, List.ofFn_succ]

end RankCount

namespace RankCount

noncomputable def patternCount (d : ℕ) := Nat.card {x : Fin 6 → Fin d // Function.Surjective x ∧ Good x}

theorem patternCount_eq_words (d : ℕ) : patternCount d =
    foldWords d 6 (fun xs => if histogramList d xs then 1 else 0) := by
  classical
  rw [patternCount, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [← sum_words]
  calc
    _ = ∑ x : Fin 6 → Fin d, if Function.Surjective x ∧ Good x then 1 else 0 := by simp
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      change _ = if histogramTest x = true then 1 else 0
      simp only [histogramTest_iff, ← good_iff_fast]

theorem counts0 : patternCount 0 = 0 := by rw [patternCount_eq_words]; rfl

theorem counts1 : patternCount 1 = 1 := by rw [patternCount_eq_words]; rfl

theorem counts2 : patternCount 2 = 47 := by rw [patternCount_eq_words]; rfl

set_option maxHeartbeats 5000000 in
theorem counts3 : patternCount 3 = 300 := by rw [patternCount_eq_words]; rfl

set_option maxHeartbeats 5000000 in
theorem counts4 : patternCount 4 = 600 := by rw [patternCount_eq_words]; rfl

set_option maxHeartbeats 10000000 in
theorem counts5 : patternCount 5 = 360 := by rw [patternCount_eq_words]; rfl

theorem counts6 : patternCount 6 = 0 := by
  have : IsEmpty {x : Fin 6 → Fin 6 // Function.Surjective x ∧ Good x} := by
    constructor
    rintro ⟨x, hs, S, _, j, hj, k, hk, hjk, _⟩
    have hjk' : j = k := Finite.injective_iff_surjective.mpr hs hjk
    exact hk (hjk' ▸ hj)
  exact Nat.card_of_isEmpty

end RankCount

namespace RankCount

/-- The words whose set of entries is `S` correspond to surjective words on its ranks. -/
theorem count_one_range (P : (d : ℕ) → (Fin 6 → Fin d) → Prop)
    (hP : ∀ {d e} (f : Fin d ↪o Fin e) (x : Fin 6 → Fin d), P e (f ∘ x) ↔ P d x)
    {N : ℕ} (S : Finset (Fin N)) :
    Nat.card {x : {x : Fin 6 → Fin N // P N x} // Finset.univ.image x.1 = S} =
      Nat.card {y : Fin 6 → Fin S.card // Function.Surjective y ∧ P S.card y} := by
  classical
  let e := S.orderEmbOfFin rfl
  let pack (y : {y : Fin 6 → Fin S.card // Function.Surjective y ∧ P S.card y}) :
      {x : {x : Fin 6 → Fin N // P N x} // Finset.univ.image x.1 = S} :=
    ⟨⟨e ∘ y.1, (hP e _).2 y.2.2⟩, by
      change Finset.univ.image (e ∘ y.1) = S
      have hy : Finset.univ.image y.1 = Finset.univ := by
        ext j
        simp [Finset.mem_image, y.2.1 j]
      rw [← Finset.image_image, hy]
      exact S.image_orderEmbOfFin_univ rfl⟩
  symm
  apply Nat.card_congr (Equiv.ofBijective pack ?_)
  constructor
  · intro a b h
    apply Subtype.ext
    funext i
    apply e.injective
    exact congrFun (congrArg (fun z => z.1.1) h) i
  · intro x
    let cut (i : Fin 6) : S := ⟨x.1.1 i, by
      exact (Finset.ext_iff.mp x.2 _).mp (Finset.mem_image_of_mem _ (Finset.mem_univ i))⟩
    have hcut : Function.Surjective cut := by
      intro t
      have ht := (Finset.ext_iff.mp x.2 t.1).mpr t.2
      obtain ⟨i, -, hi⟩ := Finset.mem_image.mp ht
      exact ⟨i, Subtype.ext hi⟩
    let y := (S.orderIsoOfFin rfl).symm ∘ cut
    have hy : e ∘ y = x.1.1 := by
      funext i
      change ((S.orderIsoOfFin rfl ((S.orderIsoOfFin rfl).symm (cut i)) : S) : Fin N) = _
      simp [cut]
    refine ⟨⟨y, (S.orderIsoOfFin rfl).symm.surjective.comp hcut, (hP e y).1 ?_⟩, ?_⟩
    · rw [hy]; exact x.1.2
    · exact Subtype.ext (Subtype.ext hy)

/-- Partition the words by their set of entries. -/
theorem count_by_subset (P : (d : ℕ) → (Fin 6 → Fin d) → Prop)
    (hP : ∀ {d e} (f : Fin d ↪o Fin e) (x : Fin 6 → Fin d), P e (f ∘ x) ↔ P d x)
    (N : ℕ) : Nat.card {x : Fin 6 → Fin N // P N x} =
      ∑ S : Finset (Fin N), Nat.card {y : Fin 6 → Fin S.card // Function.Surjective y ∧ P S.card y} := by
  classical
  let rangeOf (x : {x : Fin 6 → Fin N // P N x}) := Finset.univ.image x.1
  rw [Nat.card_congr (Equiv.sigmaFiberEquiv rangeOf).symm, Nat.card_sigma]
  exact Finset.sum_congr rfl (fun S _ => count_one_range P hP S)

theorem group_by_card (N : ℕ) (A : ℕ → ℕ) (hz : ∀ d, 6 < d → A d = 0) :
    (∑ S : Finset (Fin N), A S.card) = ∑ d ∈ Finset.range 7, N.choose d * A d := by
  calc
    (∑ S : Finset (Fin N), A S.card) = ∑ d ∈ Finset.range (N + 1), N.choose d * A d := by
      rw [← Finset.powerset_univ, Finset.sum_powerset]
      simp_rw [Finset.sum_powersetCard]
      simp
    _ = _ := by
      rcases le_total (N + 1) 7 with h | h
      · apply Finset.sum_subset (Finset.range_mono h)
        intro d _ hd
        simp only [Finset.mem_range, not_lt] at hd
        rw [Nat.choose_eq_zero_of_lt (by omega), zero_mul]
      · symm
        apply Finset.sum_subset (Finset.range_mono h)
        intro d _ hd
        simp only [Finset.mem_range, not_lt] at hd
        rw [hz d (by omega), mul_zero]

/-- Count words by choosing their values, then filling them with an onto rank pattern. -/
theorem count_by_rank (P : (d : ℕ) → (Fin 6 → Fin d) → Prop)
    (hP : ∀ {d e} (f : Fin d ↪o Fin e) (x : Fin 6 → Fin d), P e (f ∘ x) ↔ P d x)
    (N : ℕ) : Nat.card {x : Fin 6 → Fin N // P N x} =
      ∑ d ∈ Finset.range 7, N.choose d * Nat.card {y : Fin 6 → Fin d // Function.Surjective y ∧ P d y} := by
  rw [count_by_subset P hP N]
  apply group_by_card N (fun d => Nat.card {y : Fin 6 → Fin d // Function.Surjective y ∧ P d y})
  intro d hd
  have : IsEmpty {y : Fin 6 → Fin d // Function.Surjective y ∧ P d y} :=
    ⟨fun y => by
      have hcard := Fintype.card_le_of_surjective y.1 y.2.1
      simp only [Fintype.card_fin] at hcard
      omega⟩
  exact Nat.card_of_isEmpty

end RankCount

namespace RankCount

theorem upstream_card (n : ℕ) : OMA.S_oeis_a250082.a n =
    (Nat.card {x : Fin 6 → Fin (n + 1) // Good x} : ℤ) := by
  classical
  unfold OMA.S_oeis_a250082.a
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 1
  apply congrArg Finset.card
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, good_iff]

end RankCount

namespace RankSeries

open PowerSeries

/-- Every binomial column of degree at most five has zero sixth finite difference. -/
theorem choose_column (k d : ℕ) (hd : d ≤ 5) : ((k + 8).choose d : ℚ) =
    6 * ((k + 7).choose d : ℚ) - 15 * ((k + 6).choose d : ℚ) +
    20 * ((k + 5).choose d : ℚ) - 15 * ((k + 4).choose d : ℚ) +
    6 * ((k + 3).choose d : ℚ) - ((k + 2).choose d : ℚ) := by
  interval_cases d <;>
    simp only [Nat.add_choose_eq k, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.sum_range_succ, Finset.sum_range_zero] <;>
    norm_num [Nat.choose] <;> ring

/-- The five binomial columns determine both the offset-one series and the recurrence. -/
theorem of_binomials (s : ℕ → ℤ) (hs : ∀ n : ℕ, (s n : ℚ) =
    ((n + 1).choose 1 : ℚ) + 47 * ((n + 1).choose 2 : ℚ) +
    300 * ((n + 1).choose 3 : ℚ) + 600 * ((n + 1).choose 4 : ℚ) +
    360 * ((n + 1).choose 5 : ℚ)) :
    (PowerSeries.mk (fun n => if n < 1 then 0 else (s n : ℚ)) * ((1 - X) ^ 6 : PowerSeries ℚ) =
      X * (49 + 150 * X + 157 * X ^ 2 - X ^ 3 + 6 * X ^ 4 - X ^ 5)) ∧
    (∀ n : ℕ, 7 ≤ n → (s n : ℚ) = 6 * s (n - 1) - 15 * s (n - 2) +
      20 * s (n - 3) - 15 * s (n - 4) + 6 * s (n - 5) - s (n - 6)) := by
  have recu (n : ℕ) (hn : 7 ≤ n) : (s n : ℚ) =
      6 * (s (n - 1) : ℚ) - 15 * (s (n - 2) : ℚ) + 20 * (s (n - 3) : ℚ) -
      15 * (s (n - 4) : ℚ) + 6 * (s (n - 5) : ℚ) - (s (n - 6) : ℚ) := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 7 := ⟨n - 7, by omega⟩
    simp only [hs]
    simp (disch := decide) only [Nat.add_sub_assoc, Nat.add_assoc, Nat.reduceSub, Nat.reduceAdd]
    linear_combination choose_column k 1 (by decide) + 47 * choose_column k 2 (by decide) +
      300 * choose_column k 3 (by decide) + 600 * choose_column k 4 (by decide) +
      360 * choose_column k 5 (by decide)
  refine ⟨?_, recu⟩
  let p := PowerSeries.mk fun n => if n < 1 then 0 else (s n : ℚ)
  change p * (1 - X) ^ 6 = _
  rw [show p * (1 - X) ^ 6 = p - 6 • (p * X ^ 1) + 15 • (p * X ^ 2) -
      20 • (p * X ^ 3) + 15 • (p * X ^ 4) - 6 • (p * X ^ 5) + p * X ^ 6 by
        simp only [nsmul_eq_mul]; ring]
  rw [show (X : PowerSeries ℚ) * (49 + 150 * X + 157 * X ^ 2 - X ^ 3 + 6 * X ^ 4 - X ^ 5) =
      49 • X ^ 1 + 150 • X ^ 2 + 157 • X ^ 3 - X ^ 4 + 6 • X ^ 5 - X ^ 6 by
        simp only [nsmul_eq_mul]; ring]
  apply PowerSeries.ext
  intro n
  simp only [map_add, map_sub, map_nsmul, coeff_mul_X_pow', coeff_X_pow, p, coeff_mk]
  by_cases hn : n < 7
  · interval_cases n <;> norm_num [hs, Nat.choose]
  · simp (disch := omega) only [if_pos, if_neg, nsmul_eq_mul, Nat.cast_ofNat]
    linear_combination recu n (by omega)

end RankSeries

namespace RankCount

theorem rank_formula (n : ℕ) : (OMA.S_oeis_a250082.a n : ℚ) =
    ((n + 1).choose 1 : ℚ) + 47 * ((n + 1).choose 2 : ℚ) +
    300 * ((n + 1).choose 3 : ℚ) + 600 * ((n + 1).choose 4 : ℚ) +
    360 * ((n + 1).choose 5 : ℚ) := by
  have count := count_by_rank (fun _ x => Good x) (fun f x => good_comp_iff f x) (n + 1)
  change Nat.card {x : Fin 6 → Fin (n + 1) // Good x} =
    ∑ d ∈ Finset.range 7, (n+1).choose d * patternCount d at count
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, counts0, counts1, counts2,
    counts3, counts4, counts5, counts6, mul_zero, mul_one, zero_add, add_zero] at count
  rw [upstream_card, count]
  push_cast
  ring

end RankCount

theorem OMA.solution : type_of% @OMA.S_oeis_a250082.main :=
  RankSeries.of_binomials OMA.S_oeis_a250082.a RankCount.rank_formula
