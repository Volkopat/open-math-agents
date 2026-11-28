import OMAReductions.R_Erdos470_erdos_470_variants_odd_weird_10_pow_21_R1_H1_R1_H2_R1
import Mathlib

namespace OddWeirdCover

open scoped BigOperators

def powerIndex (p e : ℕ) : ℚ :=
  (∑ i ∈ Finset.range (e + 1), (p : ℚ) ^ i) / (p : ℚ) ^ e

def ceiling (p : ℕ) : ℚ := (p : ℚ) / ((p : ℚ) - 1)

theorem powerIndex_nonneg (p e : ℕ) : 0 ≤ powerIndex p e := by
  unfold powerIndex
  positivity

theorem ceiling_nonneg {p : ℕ} (hp : 2 ≤ p) : 0 ≤ ceiling p := by
  have h : (1 : ℚ) ≤ p := by exact_mod_cast (by omega : 1 ≤ p)
  unfold ceiling
  exact div_nonneg (by positivity) (sub_nonneg.mpr h)

theorem ceiling_antitone {p q : ℕ} (hp : 2 ≤ p) (hpq : p ≤ q) :
    ceiling q ≤ ceiling p := by
  have ppos : (1 : ℚ) < p := by exact_mod_cast (by omega : 1 < p)
  have qpos : (1 : ℚ) < q := by exact_mod_cast (by omega : 1 < q)
  have pq : (p : ℚ) ≤ q := by exact_mod_cast hpq
  rw [ceiling, ceiling, div_le_div_iff₀ (sub_pos.mpr qpos) (sub_pos.mpr ppos)]
  nlinarith only [pq]

theorem powerIndex_le_ceiling {p : ℕ} (hp : 2 ≤ p) (e : ℕ) :
    powerIndex p e ≤ ceiling p := by
  have ppos : (0 : ℚ) < p := by exact_mod_cast (by omega : 0 < p)
  have hone : (1 : ℚ) < p := by exact_mod_cast (by omega : 1 < p)
  rw [powerIndex, ceiling, div_le_div_iff₀ (pow_pos ppos _) (sub_pos.mpr hone),
    geom_sum_mul, pow_succ]
  nlinarith

def clippedIndex (p e cap : ℕ) : ℚ :=
  if e < cap then powerIndex p e else ceiling p

theorem powerIndex_le_clipped {p : ℕ} (hp : 2 ≤ p) (e cap : ℕ) :
    powerIndex p e ≤ clippedIndex p (min e cap) cap := by
  by_cases h : e < cap
  · simp [clippedIndex, min_eq_left h.le, h]
  · rw [min_eq_right (by omega : cap ≤ e)]
    simpa [clippedIndex] using powerIndex_le_ceiling hp e

theorem clippedIndex_nonneg {p : ℕ} (hp : 2 ≤ p) (e cap : ℕ) :
    0 ≤ clippedIndex p e cap := by
  unfold clippedIndex
  split
  · exact powerIndex_nonneg _ _
  · exact ceiling_nonneg hp

theorem index_factors {n : ℕ} (hn : n ≠ 0) :
    n.abundancyIndex = ∏ p ∈ n.primeFactors, powerIndex p (n.factorization p) := by
  have castProduct : (n : ℚ) =
      ∏ p ∈ n.primeFactors, (p : ℚ) ^ n.factorization p := by
    simpa only [Nat.cast_prod, Nat.cast_pow] using
      congrArg (fun a : ℕ => (a : ℚ)) (Nat.prod_primeFactors_pow_factorization hn)
  rw [Nat.abundancyIndex, ← ArithmeticFunction.sigma_one_apply,
    ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hn]
  simp only [powerIndex, mul_one, Nat.cast_prod, Nat.cast_sum, Nat.cast_pow, Finset.prod_div_distrib]
  rw [← castProduct]

theorem sorted_factorization {n : ℕ} (hn : n ≠ 0) :
    n = ((n.primeFactors.sort).map fun p => p ^ n.factorization p).prod := by
  rw [← List.prod_toFinset _ (Finset.sort_nodup _ _), Finset.sort_toFinset]
  exact Nat.prod_primeFactors_pow_factorization hn

theorem sorted_index {n : ℕ} (hn : n ≠ 0) :
    n.abundancyIndex =
      ((n.primeFactors.sort).map fun p => powerIndex p (n.factorization p)).prod := by
  rw [← List.prod_toFinset _ (Finset.sort_nodup _ _), Finset.sort_toFinset]
  exact index_factors hn

theorem sorted_support {n : ℕ} (hn : n ≠ 0) (hodd : Odd n) (three : 3 ∣ n) :
    ∃ tail : List ℕ, n.primeFactors.sort = 3 :: tail ∧
      (3 :: tail).Pairwise (· < ·) ∧
      ∀ p ∈ 3 :: tail, p.Prime ∧ Odd p ∧ 0 < n.factorization p := by
  have member (p : ℕ) (hp : p ∈ n.primeFactors.sort) :
      p.Prime ∧ Odd p ∧ 0 < n.factorization p := by
    have mem : p ∈ n.primeFactors := by simpa using hp
    have prime := Nat.prime_of_mem_primeFactors mem
    have dvd := Nat.dvd_of_mem_primeFactors mem
    exact ⟨prime, hodd.of_dvd_nat dvd, prime.factorization_pos_of_dvd hn dvd⟩
  have h3 : 3 ∈ n.primeFactors.sort := by
    simpa using ((Nat.mem_primeFactors).mpr ⟨Nat.prime_three, three, hn⟩ : 3 ∈ n.primeFactors)
  have order : n.primeFactors.sort.Pairwise (· < ·) :=
    List.sortedLT_iff_pairwise.mp (Finset.sortedLT_sort _)
  cases hl : n.primeFactors.sort with
  | nil => simp [hl] at h3
  | cons p tail =>
    have hleast : 3 ≤ p := by
      have props := member p (by simp [hl])
      have two := props.1.two_le
      obtain ⟨k,hk⟩ := props.2.1
      omega
    have eq : p = 3 := by
      rw [hl, List.mem_cons] at h3
      rcases h3 with equal | after
      · exact equal.symm
      · rw [hl, List.pairwise_cons] at order
        have earlier := order.1 _ after
        omega
    subst p
    refine ⟨tail, rfl, ?_, ?_⟩
    · simpa only [hl] using order
    · simpa only [hl] using member

end OddWeirdCover

namespace OddWeirdCover

open scoped BigOperators

def factorProduct : List ℕ → List ℕ → ℕ
  | p :: ps, e :: es => p ^ e * factorProduct ps es
  | _, _ => 1

def indexProduct : List ℕ → List ℕ → ℚ
  | p :: ps, e :: es => powerIndex p e * indexProduct ps es
  | _, _ => 1

theorem indexProduct_nonneg (ps es : List ℕ) : 0 ≤ indexProduct ps es := by
  induction ps generalizing es with
  | nil => simp [indexProduct]
  | cons p ps ih =>
    cases es with
    | nil => simp [indexProduct]
    | cons e es => exact mul_nonneg (powerIndex_nonneg p e) (ih es)

def upperProduct : List ℕ → List ℕ → List ℕ → ℚ
  | p :: ps, e :: es, cap :: caps =>
    clippedIndex p e cap * upperProduct ps es caps
  | _, _, _ => 1

theorem indexProduct_le_upper (ps es caps : List ℕ) (hp : ∀ p ∈ ps, 2 ≤ p)
    (same : ps.length = es.length) (width : es.length = caps.length) :
    indexProduct ps es ≤ upperProduct ps (List.zipWith min es caps) caps := by
  induction ps generalizing es caps with
  | nil => simp [indexProduct, upperProduct]
  | cons p ps ih =>
    cases es with
    | nil => simp at same
    | cons e es =>
      cases caps with
      | nil => simp at width
      | cons cap caps =>
        have rem : ∀ q ∈ ps, 2 ≤ q := fun q h => hp q (by simp [h])
        simp only [List.length_cons, Nat.succ_inj] at same width
        simp only [indexProduct, List.zipWith_cons_cons, upperProduct]
        exact mul_le_mul (powerIndex_le_clipped (hp p (by simp)) e cap)
          (ih es caps rem same width) (indexProduct_nonneg ps es)
          (clippedIndex_nonneg (hp p (by simp)) _ _)

def grid : List ℕ → List (List ℕ)
  | [] => [[]]
  | cap :: caps => (List.range cap).flatMap fun i => (grid caps).map ((i+1) :: ·)

theorem clipped_mem_grid (es caps : List ℕ) (same : es.length = caps.length)
    (positive : ∀ e ∈ es, 0 < e) (width : ∀ cap ∈ caps, 0 < cap) :
    List.zipWith min es caps ∈ grid caps := by
  induction es generalizing caps with
  | nil =>
    cases caps <;> simp_all [grid]
  | cons e es ih =>
    cases caps with
    | nil => simp at same
    | cons cap caps =>
      have cpos : 0 < min e cap := lt_min (positive e (by simp)) (width cap (by simp))
      have inrange : min e cap - 1 ∈ List.range cap :=
        List.mem_range.mpr (by have := min_le_right e cap; omega)
      have rem : List.zipWith min es caps ∈ grid caps :=
        ih caps (by simpa using same) (fun x h => positive x (by simp [h]))
          (fun x h => width x (by simp [h]))
      simp only [List.zipWith_cons_cons, grid]
      apply List.mem_flatMap.mpr
      refine ⟨min e cap - 1, inrange, ?_⟩
      exact List.mem_map.mpr ⟨_, rem, by congr 1; omega⟩

def below : List ℕ → List ℕ → Bool
  | [], [] => true
  | a :: as, b :: bs => a ≤ b && below as bs
  | _, _ => false

theorem checked_dvd (ps es caps ws : List ℕ)
    (h : below ws (List.zipWith min es caps) = true) :
    factorProduct ps ws ∣ factorProduct ps es := by
  induction ps generalizing es caps ws with
  | nil => simp [factorProduct]
  | cons p ps ih =>
    cases ws with
    | nil => simp [factorProduct]
    | cons w ws =>
      cases es with
      | nil => simp [below] at h
      | cons e es =>
        cases caps with
        | nil => simp [below] at h
        | cons cap caps =>
          have h' : w ≤ min e cap ∧ below ws (List.zipWith min es caps) = true := by
            simpa [below] using h
          exact Nat.mul_dvd_mul (Nat.pow_dvd_pow p (h'.1.trans (min_le_left _ _)))
            (ih es caps ws h'.2)

def indexDivisor : List ℕ → List ℕ → ℕ → ℕ
  | p :: ps, e :: es, i =>
    p ^ (i % (e+1)) * indexDivisor ps es (i / (e+1))
  | _, _, _ => 1

abbrev Witness := List ℕ × List (ℕ × ℕ)

def selectionChunk (ps es : List ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | count+1, word =>
    indexDivisor ps es (word % 1024) :: selectionChunk ps es count (word / 1024)

def increasing : List ℕ → Bool
  | a :: b :: rest => (a < b) && increasing (b :: rest)
  | _ => true

theorem increasing_chain (values : List ℕ) (checked : increasing values = true) :
    values.IsChain (· < ·) := by
  induction values with
  | nil => exact .nil
  | cons a rest ih =>
    cases rest with
    | nil => exact .singleton a
    | cons b rest =>
      have h : a < b ∧ increasing (b :: rest) = true := by
        simpa [increasing] using checked
      exact List.isChain_cons_cons.mpr ⟨h.1, ih h.2⟩

def orderedSelection (ps : List ℕ) (row : Witness) : List ℕ :=
  row.2.flatMap fun (count,word) => selectionChunk ps.reverse row.1.reverse count word

def checkWitness (ps : List ℕ) (row : Witness) : Bool :=
  let n := factorProduct ps row.1
  let chosen := orderedSelection ps row
  0 < n && chosen.all (fun d => d < n && n % d == 0) &&
    increasing chosen && chosen.sum == n

theorem checkWitness_sound (ps : List ℕ) (row : Witness)
    (h : checkWitness ps row = true) : (factorProduct ps row.1).Pseudoperfect := by
  let n := factorProduct ps row.1
  let chosen := orderedSelection ps row
  have ok : ((0 < n ∧ chosen.all (fun d => d < n && n % d == 0) = true) ∧
      increasing chosen = true) ∧ chosen.sum = n := by
    simpa [checkWitness, n, chosen] using h
  have distinct : chosen.Nodup :=
    (List.isChain_iff_pairwise.mp (increasing_chain chosen ok.1.2)).imp (fun h => ne_of_lt h)
  refine ⟨ok.1.1.1, chosen.toFinset, ?_, ?_⟩
  · intro d hd
    have hchosen : d ∈ chosen := List.mem_toFinset.mp hd
    have hdvd : d < n ∧ n % d = 0 :=
      by simpa using List.all_eq_true.mp ok.1.1.2 d hchosen
    exact Nat.mem_properDivisors.mpr ⟨Nat.dvd_of_mod_eq_zero hdvd.2, hdvd.1⟩
  · simpa using (List.sum_toFinset (fun d => d) distinct).trans (by simpa using ok.2)

def localData (p e cap : ℕ) : ℕ × ℕ :=
  if e < cap then ((∑ i ∈ Finset.range (e+1), p^i), p^e) else (p,p-1)

private def mulData (a b : ℕ × ℕ) : ℕ × ℕ :=
  (a.1*b.1,a.2*b.2)

def ratioData : List ℕ → List ℕ → List ℕ → ℕ × ℕ
  | p :: ps, e :: es, cap :: caps =>
    mulData (localData p e cap) (ratioData ps es caps)
  | _, _, _ => (1,1)

private def toRatio (value : ℕ × ℕ) : ℚ := (value.1 : ℚ) / (value.2 : ℚ)

private theorem toRatio_mulData (a b : ℕ × ℕ) :
    toRatio (mulData a b) = toRatio a * toRatio b := by
  unfold toRatio mulData
  push_cast
  exact (div_mul_div_comm _ _ _ _).symm

private theorem localData_pos {p : ℕ} (hp : 2 ≤ p) (e cap : ℕ) :
    0 < (localData p e cap).2 := by
  by_cases h : e < cap
  · simpa [localData,h] using pow_pos (by omega : 0 < p) e
  · simp [localData,h]; omega

private theorem toRatio_localData {p : ℕ} (hp : 2 ≤ p) (e cap : ℕ) :
    toRatio (localData p e cap) = clippedIndex p e cap := by
  by_cases h : e < cap
  · simp [toRatio, localData, clippedIndex, powerIndex, h, Nat.cast_sum, Nat.cast_pow]
  · simp [toRatio, localData, clippedIndex, ceiling, h, Nat.cast_sub (by omega : 1 ≤ p)]

theorem ratioData_sound (ps es caps : List ℕ) (hp : ∀ p ∈ ps, 2 ≤ p) :
    0 < (ratioData ps es caps).2 ∧ toRatio (ratioData ps es caps) = upperProduct ps es caps := by
  induction ps generalizing es caps with
  | nil => simp [ratioData, toRatio, upperProduct]
  | cons p ps ih =>
    cases es with
    | nil => simp [ratioData, toRatio, upperProduct]
    | cons e es =>
      cases caps with
      | nil => simp [ratioData, toRatio, upperProduct]
      | cons cap caps =>
        have pbase := hp p (by simp)
        obtain ⟨restPos, rest⟩ := ih es caps (fun q h => hp q (by simp [h]))
        exact ⟨Nat.mul_pos (localData_pos pbase e cap) restPos,
          by rw [ratioData, toRatio_mulData, toRatio_localData pbase, rest, upperProduct]⟩

def checkBound (ps es caps : List ℕ) (limit : ℕ × ℕ) : Bool :=
  let r := ratioData ps es caps
  decide (r.1*limit.2 ≤ limit.1*r.2)

theorem checkBound_sound (ps es caps : List ℕ) (limit : ℕ × ℕ)
    (hp : ∀ p ∈ ps, 2 ≤ p) (ld : 0 < limit.2)
    (checked : checkBound ps es caps limit = true) :
    upperProduct ps es caps ≤ toRatio limit := by
  obtain ⟨pos, eq⟩ := ratioData_sound ps es caps hp
  rw [← eq, toRatio, toRatio, div_le_div_iff₀ (by exact_mod_cast pos) (by exact_mod_cast ld)]
  have h : (ratioData ps es caps).1*limit.2 ≤ limit.1*(ratioData ps es caps).2 := by
    simpa [checkBound] using checked
  exact_mod_cast h

def checkBox (ps caps : List ℕ) (limit : ℕ × ℕ) (rows : List Witness) : Bool :=
  rows.all (checkWitness ps) && (grid caps).all fun es =>
    checkBound ps es caps limit || rows.any fun row => below row.1 es

theorem checkBox_sound (ps caps es : List ℕ) (limit : ℕ × ℕ) (rows : List Witness)
    (checked : checkBox ps caps limit rows = true)
    (hp : ∀ p ∈ ps, 2 ≤ p) (he : ∀ e ∈ es, 0 < e) (hc : ∀ c ∈ caps, 0 < c)
    (len : ps.length = es.length) (len' : es.length = caps.length) (ld : 0 < limit.2) :
    indexProduct ps es ≤ (limit.1 : ℚ) / (limit.2 : ℚ) ∨
      ∃ d, d ∣ factorProduct ps es ∧ d.Pseudoperfect := by
  have parts : rows.all (checkWitness ps) = true ∧
      (grid caps).all (fun e => checkBound ps e caps limit ||
        rows.any fun row => below row.1 e) = true := by
    simpa only [checkBox, Bool.and_eq_true] using checked
  have clipped := clipped_mem_grid es caps len' he hc
  have hit := List.all_eq_true.mp parts.2 _ clipped
  have covered : checkBound ps (List.zipWith min es caps) caps limit = true ∨
      (rows.any fun row => below row.1 (List.zipWith min es caps)) = true := by
    simpa [Bool.or_eq_true] using hit
  rcases covered with bounded | witness
  · exact Or.inl ((indexProduct_le_upper ps es caps hp len len').trans
      (checkBound_sound ps _ caps limit hp ld bounded))
  · obtain ⟨row, mem, code⟩ := List.any_eq_true.mp witness
    exact Or.inr ⟨factorProduct ps row.1, checked_dvd ps es caps row.1 code,
      checkWitness_sound ps row (List.all_eq_true.mp parts.1 row mem)⟩

end OddWeirdCover

namespace OddWeirdCover

theorem majorant {base ps : List ℕ}
    (h : List.Forall₂ (fun lo p => 2 ≤ lo ∧ lo ≤ p) base ps)
    (es : List ℕ) (len : es.length = ps.length) :
    indexProduct ps es ≤ (base.map ceiling).prod := by
  induction h generalizing es with
  | nil => simp [indexProduct]
  | @cons lo p ls ps head tail ih =>
    cases es with
    | nil => simp at len
    | cons e es =>
      simp only [List.map_cons, List.prod_cons, indexProduct]
      exact mul_le_mul
        ((powerIndex_le_ceiling (head.1.trans head.2) e).trans (ceiling_antitone head.1 head.2))
        (ih es (by simpa using len)) (indexProduct_nonneg ps es) (ceiling_nonneg head.1)

theorem at_least_two_more {p q : ℕ} (podd : Odd p) (qodd : Odd q) (lt : p < q) : p + 2 ≤ q := by
  obtain ⟨i, hi⟩ := podd
  obtain ⟨j, hj⟩ := qodd
  omega

theorem one_impossible (a : ℕ) : indexProduct [3] [a] ≤ 2 := by
  have h : List.Forall₂ (fun lo p => 2 ≤ lo ∧ lo ≤ p) [3] [3] := by decide
  exact (majorant h [a] rfl).trans (by norm_num [ceiling])

theorem two_impossible (q a b : ℕ) (hq : 5 ≤ q) : indexProduct [3,q] [a,b] ≤ 2 := by
  have h : List.Forall₂ (fun lo p => 2 ≤ lo ∧ lo ≤ p) [3,5] [3,q] :=
    .cons (by omega) (.cons (by omega) .nil)
  exact (majorant h [a,b] rfl).trans (by norm_num [ceiling])

theorem three_support (q r a b c : ℕ) (hq : 5 ≤ q) (hqr : q + 2 ≤ r)
    (qodd : Odd q) (hr : r.Prime) (high : 2 < indexProduct [3,q,r] [a,b,c]) :
    q = 5 ∧ r ∈ [7,11,13] := by
  have qsmall : q < 7 := by
    by_contra! bad
    have h : List.Forall₂ (fun lo p => 2 ≤ lo ∧ lo ≤ p) [3,7,9] [3,q,r] :=
      .cons (by omega) (.cons (by omega) (.cons (by omega) .nil))
    exact (not_le_of_gt high) ((majorant h [a,b,c] rfl).trans (by norm_num [ceiling]))
  have qeq : q = 5 := by obtain ⟨i, hi⟩ := qodd; omega
  subst q
  have rsmall : r < 17 := by
    by_contra! bad
    have h : List.Forall₂ (fun lo p => 2 ≤ lo ∧ lo ≤ p) [3,5,17] [3,5,r] :=
      .cons (by omega) (.cons (by omega) (.cons (by omega) .nil))
    exact (not_le_of_gt high) ((majorant h [a,b,c] rfl).trans (by norm_num [ceiling]))
  refine ⟨rfl, ?_⟩
  interval_cases r <;> norm_num at *

theorem four_pairs (q r s a b c d : ℕ) (hq : 5 ≤ q) (hqr : q + 2 ≤ r) (hrs : r + 2 ≤ s)
    (qp : q.Prime) (rp : r.Prime) (high : 2 < indexProduct [3,q,r,s] [a,b,c,d]) :
    (q = 5 ∧ r ∈ [7,11,13,17,19,23,29]) ∨ (q = 7 ∧ r ∈ [11,13]) := by
  have qsmall : q < 11 := by
    by_contra! bad
    have h : List.Forall₂ (fun lo p => 2 ≤ lo ∧ lo ≤ p) [3,11,13,15] [3,q,r,s] :=
      .cons (by omega) (.cons (by omega) (.cons (by omega) (.cons (by omega) .nil)))
    exact (not_le_of_gt high) ((majorant h [a,b,c,d] rfl).trans (by norm_num [ceiling]))
  have qeq : q = 5 ∨ q = 7 := by interval_cases q <;> norm_num at *
  rcases qeq with rfl | rfl
  · have rsmall : r < 31 := by
      by_contra! bad
      have h : List.Forall₂ (fun lo p => 2 ≤ lo ∧ lo ≤ p) [3,5,31,33] [3,5,r,s] :=
        .cons (by omega) (.cons (by omega) (.cons (by omega) (.cons (by omega) .nil)))
      exact (not_le_of_gt high) ((majorant h [a,b,c,d] rfl).trans (by norm_num [ceiling]))
    refine Or.inl ⟨rfl, ?_⟩
    interval_cases r <;> norm_num at *
  · have rsmall : r < 17 := by
      by_contra! bad
      have h : List.Forall₂ (fun lo p => 2 ≤ lo ∧ lo ≤ p) [3,7,17,19] [3,7,r,s] :=
        .cons (by omega) (.cons (by omega) (.cons (by omega) (.cons (by omega) .nil)))
      exact (not_le_of_gt high) ((majorant h [a,b,c,d] rfl).trans (by norm_num [ceiling]))
    refine Or.inr ⟨rfl, ?_⟩
    interval_cases r <;> norm_num at *

theorem indexProduct_map (ps : List ℕ) (e : ℕ → ℕ) :
    indexProduct ps (ps.map e) = (ps.map fun p => powerIndex p (e p)).prod := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [indexProduct, ih]

theorem factorProduct_map (ps : List ℕ) (e : ℕ → ℕ) :
    factorProduct ps (ps.map e) = (ps.map fun p => p ^ e p).prod := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [factorProduct, ih]

theorem append_index (q r s a b c d : ℕ) :
    indexProduct [3,q,r,s] [a,b,c,d] = indexProduct [3,q,r] [a,b,c] * powerIndex s d := by
  simp [indexProduct, mul_assoc]

theorem factor_prefix_dvd (q r s a b c d : ℕ) :
    factorProduct [3,q,r] [a,b,c] ∣ factorProduct [3,q,r,s] [a,b,c,d] := by
  simp [factorProduct, ← mul_assoc]

theorem last_prime_bound (q r s a b c d B : ℕ) (level : ℚ)
    (low : 2 ≤ B) (pos : 0 ≤ level) (end_bound : level * ceiling B ≤ 2)
    (pref : indexProduct [3,q,r] [a,b,c] ≤ level)
    (high : 2 < indexProduct [3,q,r,s] [a,b,c,d]) :
    s < B := by
  by_contra! large
  have extra := (powerIndex_le_ceiling (low.trans large) d).trans (ceiling_antitone low large)
  rw [append_index] at high
  exact (not_le_of_gt high) ((mul_le_mul pref extra (powerIndex_nonneg _ _) pos).trans end_bound)

end OddWeirdCover

namespace OddWeirdCover

private def prefix7_rows : List Witness := [([2,1,2], [(15,0xb03810014080280d0080f01c090300100c06)]),
  ([2,2,1], [(13,0xb03c10014090280e00c0401c0803002)]),
  ([3,1,1], [(13,0xb0340e01c0902803014060200100800)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def prefix7_checked : PLift (checkBox [3,5,7] [3,2,2] (208,105) prefix7_rows = true) := ⟨by decide +kernel⟩

private theorem prefix7 (a b c : ℕ) (ap : 0 < a) (bp : 0 < b) (cp : 0 < c) :
    indexProduct [3,5,7] [a,b,c] ≤ (208 / 105 : ℚ) ∨
      ∃ d, d ∣ factorProduct [3,5,7] [a,b,c] ∧ d.Pseudoperfect :=
  checkBox_sound [3,5,7] [3,2,2] [a,b,c] (208,105) prefix7_rows prefix7_checked.down
    (by decide) (by simp [ap,bp,cp]) (by decide) rfl rfl (by decide)

private def prefix11_rows : List Witness := [([3,2,1], [(21,0x110540b0580f04c05040090500d0280303807010080040c00800)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def prefix11_checked : PLift (checkBox [3,5,11] [3,2,1] (143,72) prefix11_rows = true) := ⟨by decide +kernel⟩

private theorem prefix11 (a b c : ℕ) (ap : 0 < a) (bp : 0 < b) (cp : 0 < c) :
    indexProduct [3,5,11] [a,b,c] ≤ (143 / 72 : ℚ) ∨
      ∃ d, d ∣ factorProduct [3,5,11] [a,b,c] ∧ d.Pseudoperfect :=
  checkBox_sound [3,5,11] [3,2,1] [a,b,c] (143,72) prefix11_rows prefix11_checked.down
    (by decide) (by simp [ap,bp,cp]) (by decide) rfl rfl (by decide)

private def prefix13_rows : List Witness := [([3,3,2], [(45,0x230b0170b8200a40b088140ac1d058260202d07c110a00a068130142a0700e0542501c1e0400209c09064120100d0900603c010600303000)]),
  ([4,2,2], [(41,0x230a41a0ac2009811088170a01d020190382a05025040050841602c270700703402078130900f010150281b0180c0041200c00)]),
  ([4,3,1], [(37,0x1f094170981d08c0f078150901b01c160841c04c22038190141402c1a018110800c00c1206004028010400202000)]),
  ([5,2,1], [(33,0x1d084170881b07c11070150801902c1603c1a04c050781002414034180280303807048080040c00806)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def prefix13_checked : PLift (checkBox [3,5,13] [5,3,2] (52514,26325) prefix13_rows = true) := ⟨by decide +kernel⟩

private theorem prefix13 (a b c : ℕ) (ap : 0 < a) (bp : 0 < b) (cp : 0 < c) :
    indexProduct [3,5,13] [a,b,c] ≤ (52514 / 26325 : ℚ) ∨
      ∃ d, d ∣ factorProduct [3,5,13] [a,b,c] ∧ d.Pseudoperfect :=
  checkBox_sound [3,5,13] [5,3,2] [a,b,c] (52514,26325) prefix13_rows prefix13_checked.down
    (by decide) (by simp [ap,bp,cp]) (by decide) rfl rfl (by decide)

private def p5_7_keys : List ℕ := [11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103]

private def p5_7_11_rows : List Witness := [([1,1,1,2], [(21,0xb04414058050200a0381004c15010070240d03c120040303000)]),
  ([1,1,2,1], [(21,0xb04415058050240f04c100500301c040200d03812004020180c)]),
  ([1,2,1,1], [(19,0xb04c150580703c0a0441200c050180d0200e0400100804)]),
  ([2,1,1,1], [(21,0xf04c070580b0340e0440301414018090280c004100080402000)]),
  ([2,1,2,0], [(15,0xb03810014080280d0080f01c090300100c06)]),
  ([2,2,1,0], [(13,0xb03c10014090280e00c0401c0803002)]),
  ([3,1,1,0], [(13,0xb0340e01c0902803014060200100800)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_7_11_checked : PLift (checkBox [3,5,7,11] [3,2,2,2] (2,1) p5_7_11_rows = true) := ⟨by decide +kernel⟩

private def p5_7_13_rows : List Witness := [([1,1,2,1], [(21,0xb04415058050240f028130401400c0701008038120040201800)]),
  ([1,2,1,1], [(19,0xb04c15058070240f0281200c14014060200e0400100804)]),
  ([2,1,1,1], [(21,0xf04c150580b034110380504814024060280c004100080402000)]),
  ([2,1,2,0], [(15,0xb03810014080280d0080f01c090300100c06)]),
  ([2,2,1,0], [(13,0xb03c10014090280e00c0401c0803002)]),
  ([3,1,1,0], [(13,0xb0340e01c0902803014060200100800)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_7_13_checked : PLift (checkBox [3,5,7,13] [3,2,2,1] (2,1) p5_7_13_rows = true) := ⟨by decide +kernel⟩

private def p5_7_17_rows : List Witness := [([1,2,1,1], [(21,0xb04c1501c160240f0440a00c1201414034060200e004100080c)]),
  ([2,1,1,1], [(19,0xf04c1501c1603403038050480905006028010300201000)]),
  ([2,1,2,0], [(15,0xb03810014080280d0080f01c090300100c06)]),
  ([2,2,1,0], [(13,0xb03c10014090280e00c0401c0803002)]),
  ([3,1,1,0], [(13,0xb0340e01c0902803014060200100800)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_7_17_checked : PLift (checkBox [3,5,7,17] [3,2,2,1] (2,1) p5_7_17_rows = true) := ⟨by decide +kernel⟩

private def p5_7_19_rows : List Witness := [([1,2,2,1], [(33,0x110742102c2203c1706c100141c02420034150280e0580306807078130100803014004180080604800)]),
  ([1,3,1,1], [(29,0xf06c1d02c1e034170640e01c1a024130701502803030160141101808048010080404000)]),
  ([2,1,1,1], [(19,0xf04c1501c160341100c050480905006028010301000808)]),
  ([2,1,2,0], [(15,0xb03810014080280d0080f01c090300100c06)]),
  ([2,2,1,0], [(13,0xb03c10014090280e00c0401c0803002)]),
  ([3,1,1,0], [(13,0xb0340e01c0902803014060200100800)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_7_19_checked : PLift (checkBox [3,5,7,19] [3,3,2,1] (2,1) p5_7_19_rows = true) := ⟨by decide +kernel⟩

private def p5_7_23_rows : List Witness := [([1,2,2,1], [(33,0x110742102c0f0881706c1f040050241c080150640a03803058070681e04c040200c004140600604800)]),
  ([2,1,1,1], [(21,0xf04c1501c0d0581100c050380904814018010280c0400201000)]),
  ([2,1,2,0], [(15,0xb03810014080280d0080f01c090300100c06)]),
  ([2,2,1,0], [(13,0xb03c10014090280e00c0401c0803002)]),
  ([3,1,1,0], [(13,0xb0340e01c0902803014060200100800)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_7_23_checked : PLift (checkBox [3,5,7,23] [3,2,2,1] (2,1) p5_7_23_rows = true) := ⟨by decide +kernel⟩

private def p5_7_29_rows : List Witness := [([1,3,2,1], [(43,0x170a42d0441508c2e09c2b02c1603c1d0a0130842c09405024140880d06c2607c2a028030381c01c1208019090080040c0680201818)]),
  ([2,1,1,1], [(21,0xf04c1501c0b0581100c05038090481401801028100080402000)]),
  ([2,1,2,0], [(15,0xb03810014080280d0080f01c090300100c06)]),
  ([2,2,1,0], [(13,0xb03c10014090280e00c0401c0803002)]),
  ([3,1,1,0], [(13,0xb0340e01c0902803014060200100800)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_7_29_checked : PLift (checkBox [3,5,7,29] [3,3,2,1] (2,1) p5_7_29_rows = true) := ⟨by decide +kernel⟩

private def p5_7_31_rows : List Witness := [([1,3,2,2], [(64,0x68200d4460ec410442205c2c0743d0c8430e0080640e07c140d0291143a0bc40040050841602c2b0703c0c426108370600d0081e04c280e42e0fc0f010150282a06c30094360180c0041209c0309000),(3,0x230f844)]),
  ([1,3,3,1], [(59,0x1f0dc3d05c1d0bc3e0d43b03c1e0542706c360b43c0cc070580d070130b825064340ac3a0c40e0141402c260682c08c320a4380180c00c12024240602a0843002801040220a00202020)]),
  ([1,4,2,1], [(55,0x1d0d43905c1b0bc3a0cc370441c05429064340b4380c40b0580f08c1a04c2e09c320ac05040090500d0a0210602c094300280303807088120981f0a8040040c080020181e)]),
  ([2,1,1,1], [(19,0xf04c1501c0b0341100c0502412050060040a0400201000)]),
  ([2,1,2,0], [(15,0xb03810014080280d0080f01c090300100c06)]),
  ([2,2,1,0], [(13,0xb03c10014090280e00c0401c0803002)]),
  ([3,1,1,0], [(13,0xb0340e01c0902803014060200100800)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_7_31_checked : PLift (checkBox [3,5,7,31] [3,4,3,2] (2,1) p5_7_31_rows = true) := ⟨by decide +kernel⟩

private def p5_7_37_rows : List Witness := [([2,1,1,1], [(19,0xf04c1501c0b0341600c050240e050010180a0301000808)]),
  ([2,1,2,0], [(15,0xb03810014080280d0080f01c090300100c06)]),
  ([2,2,1,0], [(13,0xb03c10014090280e00c0401c0803002)]),
  ([3,1,1,0], [(13,0xb0340e01c0902803014060200100800)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_7_37_checked : PLift (checkBox [3,5,7,37] [3,2,2,1] (2,1) p5_7_37_rows = true) := ⟨by decide +kernel⟩

private def p5_7_41_rows : List Witness := [([2,1,1,1], [(21,0xf04c1501c0b0341600c050240e04814004060280c0080402000)]),
  ([2,1,2,0], [(15,0xb03810014080280d0080f01c090300100c06)]),
  ([2,2,1,0], [(13,0xb03c10014090280e00c0401c0803002)]),
  ([3,1,1,0], [(13,0xb0340e01c0902803014060200100800)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_7_41_checked : PLift (checkBox [3,5,7,41] [3,2,2,1] (2,1) p5_7_41_rows = true) := ⟨by decide +kernel⟩

private def p5_7_43_rows : List Witness := [([2,1,1,1], [(19,0xf04c1501c0b0341100c050240e048010180a0301000808)]),
  ([2,1,2,0], [(15,0xb03810014080280d0080f01c090300100c06)]),
  ([2,2,1,0], [(13,0xb03c10014090280e00c0401c0803002)]),
  ([3,1,1,0], [(13,0xb0340e01c0902803014060200100800)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_7_43_checked : PLift (checkBox [3,5,7,43] [3,2,2,1] (2,1) p5_7_43_rows = true) := ⟨by decide +kernel⟩

private def p5_7_47_rows : List Witness := [([2,1,1,1], [(19,0xf04c1501c0b03411058050240e04801050060280c00804)]),
  ([2,1,2,0], [(15,0xb03810014080280d0080f01c090300100c06)]),
  ([2,2,1,0], [(13,0xb03c10014090280e00c0401c0803002)]),
  ([3,1,1,0], [(13,0xb0340e01c0902803014060200100800)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_7_47_checked : PLift (checkBox [3,5,7,47] [3,2,2,1] (2,1) p5_7_47_rows = true) := ⟨by decide +kernel⟩

private def p5_7_53_rows : List Witness := [([2,1,1,1], [(19,0xf04c1501c0b0341100c160240e048010500a0301000808)]),
  ([2,1,2,0], [(15,0xb03810014080280d0080f01c090300100c06)]),
  ([2,2,1,0], [(13,0xb03c10014090280e00c0401c0803002)]),
  ([3,1,1,0], [(13,0xb0340e01c0902803014060200100800)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_7_53_checked : PLift (checkBox [3,5,7,53] [3,2,2,1] (2,1) p5_7_53_rows = true) := ⟨by decide +kernel⟩

private def p5_7_59_rows : List Witness := [([2,1,1,1], [(19,0xf04c1501c0b0341100c160140e004140180c0080402000)]),
  ([2,1,2,0], [(15,0xb03810014080280d0080f01c090300100c06)]),
  ([2,2,1,0], [(13,0xb03c10014090280e00c0401c0803002)]),
  ([3,1,1,0], [(13,0xb0340e01c0902803014060200100800)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_7_59_checked : PLift (checkBox [3,5,7,59] [3,2,2,1] (2,1) p5_7_59_rows = true) := ⟨by decide +kernel⟩

private def p5_7_61_rows : List Witness := [([2,1,1,1], [(19,0xf04c1501c0b0341100c160140e004140180a0300201000)]),
  ([2,1,2,0], [(15,0xb03810014080280d0080f01c090300100c06)]),
  ([2,2,1,0], [(13,0xb03c10014090280e00c0401c0803002)]),
  ([3,1,1,0], [(13,0xb0340e01c0902803014060200100800)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_7_61_checked : PLift (checkBox [3,5,7,61] [3,2,2,1] (2,1) p5_7_61_rows = true) := ⟨by decide +kernel⟩

private def p5_7_67_rows : List Witness := [([2,1,1,1], [(21,0xf04c1501c0b0341100c050580e0041205006030100080402000)]),
  ([2,1,2,0], [(15,0xb03810014080280d0080f01c090300100c06)]),
  ([2,2,1,0], [(13,0xb03c10014090280e00c0401c0803002)]),
  ([3,1,1,0], [(13,0xb0340e01c0902803014060200100800)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_7_67_checked : PLift (checkBox [3,5,7,67] [3,2,2,1] (2,1) p5_7_67_rows = true) := ⟨by decide +kernel⟩

private def p5_7_71_rows : List Witness := [([2,1,1,1], [(19,0xf04c1501c0b0341100c0505809048140180c0400201008)]),
  ([2,1,2,0], [(15,0xb03810014080280d0080f01c090300100c06)]),
  ([2,2,1,0], [(13,0xb03c10014090280e00c0401c0803002)]),
  ([3,1,1,0], [(13,0xb0340e01c0902803014060200100800)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_7_71_checked : PLift (checkBox [3,5,7,71] [3,2,2,1] (2,1) p5_7_71_rows = true) := ⟨by decide +kernel⟩

private def p5_7_73_rows : List Witness := [([2,1,1,1], [(19,0xf04c1501c0b0341100c0505809048140180a0301001008)]),
  ([2,1,2,0], [(15,0xb03810014080280d0080f01c090300100c06)]),
  ([2,2,1,0], [(13,0xb03c10014090280e00c0401c0803002)]),
  ([3,1,1,0], [(13,0xb0340e01c0902803014060200100800)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_7_73_checked : PLift (checkBox [3,5,7,73] [3,2,2,1] (2,1) p5_7_73_rows = true) := ⟨by decide +kernel⟩

private def p5_7_79_rows : List Witness := [([2,1,1,1], [(21,0xf04c1501c0b0341100c0505809004120180a030100080402000)]),
  ([2,1,2,0], [(15,0xb03810014080280d0080f01c090300100c06)]),
  ([2,2,1,0], [(13,0xb03c10014090280e00c0401c0803002)]),
  ([3,1,1,0], [(13,0xb0340e01c0902803014060200100800)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_7_79_checked : PLift (checkBox [3,5,7,79] [3,2,2,1] (2,1) p5_7_79_rows = true) := ⟨by decide +kernel⟩

private def p5_7_83_rows : List Witness := [([2,1,1,1], [(21,0xf04c1501c0b0341100c05058090041205006030100080402000)]),
  ([2,1,2,0], [(15,0xb03810014080280d0080f01c090300100c06)]),
  ([2,2,1,0], [(13,0xb03c10014090280e00c0401c0803002)]),
  ([3,1,1,0], [(13,0xb0340e01c0902803014060200100800)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_7_83_checked : PLift (checkBox [3,5,7,83] [3,2,2,1] (2,1) p5_7_83_rows = true) := ⟨by decide +kernel⟩

private def p5_7_89_rows : List Witness := [([2,1,1,1], [(21,0xf04c1501c0b0341100c050580903812050060280c0400201008)]),
  ([2,1,2,0], [(15,0xb03810014080280d0080f01c090300100c06)]),
  ([2,2,1,0], [(13,0xb03c10014090280e00c0401c0803002)]),
  ([3,1,1,0], [(13,0xb0340e01c0902803014060200100800)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_7_89_checked : PLift (checkBox [3,5,7,89] [3,2,2,1] (2,1) p5_7_89_rows = true) := ⟨by decide +kernel⟩

private def p5_7_97_rows : List Witness := [([2,1,1,1], [(21,0xf04c1501c0b0341100c050580903801048140280c0400402000)]),
  ([2,1,2,0], [(15,0xb03810014080280d0080f01c090300100c06)]),
  ([2,2,1,0], [(13,0xb03c10014090280e00c0401c0803002)]),
  ([3,1,1,0], [(13,0xb0340e01c0902803014060200100800)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_7_97_checked : PLift (checkBox [3,5,7,97] [3,2,2,1] (2,1) p5_7_97_rows = true) := ⟨by decide +kernel⟩

private def p5_7_101_rows : List Witness := [([2,1,1,1], [(21,0xf04c1501c0b0341100c050580903801048140180a0400201000)]),
  ([2,1,2,0], [(15,0xb03810014080280d0080f01c090300100c06)]),
  ([2,2,1,0], [(13,0xb03c10014090280e00c0401c0803002)]),
  ([3,1,1,0], [(13,0xb0340e01c0902803014060200100800)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_7_101_checked : PLift (checkBox [3,5,7,101] [3,2,2,1] (2,1) p5_7_101_rows = true) := ⟨by decide +kernel⟩

private def p5_7_103_rows : List Witness := [([2,1,1,1], [(21,0xf04c1501c0b0341100c050580903801048140180a0301000808)]),
  ([2,1,2,0], [(15,0xb03810014080280d0080f01c090300100c06)]),
  ([2,2,1,0], [(13,0xb03c10014090280e00c0401c0803002)]),
  ([3,1,1,0], [(13,0xb0340e01c0902803014060200100800)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_7_103_checked : PLift (checkBox [3,5,7,103] [3,2,2,1] (2,1) p5_7_103_rows = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_7_key_check : PLift ((∀ s : Fin 105, s.val.Prime → 7 < s.val → s.val ∈ p5_7_keys)) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem p5_7_box (i : Fin 23) :
    ∃ (caps : List ℕ) (rows : List Witness),
      caps.length = 4 ∧ (∀ c ∈ caps, 0 < c) ∧
      checkBox [3,5,7,p5_7_keys[i.val]!] caps (2,1) rows = true := by
  fin_cases i
  · exact ⟨[3,2,2,2], p5_7_11_rows, rfl, by decide, p5_7_11_checked.down⟩
  · exact ⟨[3,2,2,1], p5_7_13_rows, rfl, by decide, p5_7_13_checked.down⟩
  · exact ⟨[3,2,2,1], p5_7_17_rows, rfl, by decide, p5_7_17_checked.down⟩
  · exact ⟨[3,3,2,1], p5_7_19_rows, rfl, by decide, p5_7_19_checked.down⟩
  · exact ⟨[3,2,2,1], p5_7_23_rows, rfl, by decide, p5_7_23_checked.down⟩
  · exact ⟨[3,3,2,1], p5_7_29_rows, rfl, by decide, p5_7_29_checked.down⟩
  · exact ⟨[3,4,3,2], p5_7_31_rows, rfl, by decide, p5_7_31_checked.down⟩
  · exact ⟨[3,2,2,1], p5_7_37_rows, rfl, by decide, p5_7_37_checked.down⟩
  · exact ⟨[3,2,2,1], p5_7_41_rows, rfl, by decide, p5_7_41_checked.down⟩
  · exact ⟨[3,2,2,1], p5_7_43_rows, rfl, by decide, p5_7_43_checked.down⟩
  · exact ⟨[3,2,2,1], p5_7_47_rows, rfl, by decide, p5_7_47_checked.down⟩
  · exact ⟨[3,2,2,1], p5_7_53_rows, rfl, by decide, p5_7_53_checked.down⟩
  · exact ⟨[3,2,2,1], p5_7_59_rows, rfl, by decide, p5_7_59_checked.down⟩
  · exact ⟨[3,2,2,1], p5_7_61_rows, rfl, by decide, p5_7_61_checked.down⟩
  · exact ⟨[3,2,2,1], p5_7_67_rows, rfl, by decide, p5_7_67_checked.down⟩
  · exact ⟨[3,2,2,1], p5_7_71_rows, rfl, by decide, p5_7_71_checked.down⟩
  · exact ⟨[3,2,2,1], p5_7_73_rows, rfl, by decide, p5_7_73_checked.down⟩
  · exact ⟨[3,2,2,1], p5_7_79_rows, rfl, by decide, p5_7_79_checked.down⟩
  · exact ⟨[3,2,2,1], p5_7_83_rows, rfl, by decide, p5_7_83_checked.down⟩
  · exact ⟨[3,2,2,1], p5_7_89_rows, rfl, by decide, p5_7_89_checked.down⟩
  · exact ⟨[3,2,2,1], p5_7_97_rows, rfl, by decide, p5_7_97_checked.down⟩
  · exact ⟨[3,2,2,1], p5_7_101_rows, rfl, by decide, p5_7_101_checked.down⟩
  · exact ⟨[3,2,2,1], p5_7_103_rows, rfl, by decide, p5_7_103_checked.down⟩

private theorem p5_7_bounded (s a b c d : ℕ)
    (sp : s.Prime) (ordered : 7 < s) (sb : s < 105)
    (ap : 0 < a) (bp : 0 < b) (cp : 0 < c) (dp : 0 < d)
    (high : 2 < indexProduct [3,5,7,s] [a,b,c,d]) :
    ∃ k, k ∣ factorProduct [3,5,7,s] [a,b,c,d] ∧ k.Pseudoperfect := by
  have membership := p5_7_key_check.down ⟨s,sb⟩ sp ordered
  obtain ⟨i, hi, key⟩ := List.mem_iff_getElem.mp membership
  have word := p5_7_box ⟨i,hi⟩
  have ke : p5_7_keys[i]! = s := (getElem!_pos p5_7_keys i hi).trans key
  simp only [ke] at word
  obtain ⟨caps, rows, width, cp', checked⟩ := word
  have ps : ∀ p ∈ [3,5,7,s], 2 ≤ p := by simp [sp.two_le]
  have es : ∀ e ∈ [a,b,c,d], 0 < e := by simp [ap,bp,cp,dp]
  rcases checkBox_sound [3,5,7,s] caps [a,b,c,d] (2,1) rows checked ps es cp'
      rfl width.symm (by decide) with tooSmall | witness
  · exact False.elim ((not_le_of_gt high) (by simpa using tooSmall))
  · exact witness

private theorem p5_7 (s a b c d : ℕ)
    (sp : s.Prime) (ordered : 7 < s)
    (ap : 0 < a) (bp : 0 < b) (cp : 0 < c) (dp : 0 < d)
    (high : 2 < indexProduct [3,5,7,s] [a,b,c,d]) :
    ∃ k, k ∣ factorProduct [3,5,7,s] [a,b,c,d] ∧ k.Pseudoperfect := by
  rcases prefix7 a b c ap bp cp with prefixBound | ⟨k, kd, pp⟩
  · have sb := last_prime_bound 5 7 s a b c d 105 (208 / 105 : ℚ)
      (by decide) (by norm_num) (by norm_num [ceiling]) prefixBound high
    exact p5_7_bounded s a b c d sp ordered sb ap bp cp dp high
  · exact ⟨k,kd.trans (factor_prefix_dvd 5 7 s a b c d),pp⟩

private def p5_11_keys : List ℕ := [13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139]

private def p5_11_13_rows : List Witness := [([2,1,1,1], [(21,0xf04c070541602c0e00c1104805018140280c004020400402000)]),
  ([3,2,1,0], [(21,0x110540b0580f04c05040090500d0280303807010080040c00800)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_11_13_checked : PLift (checkBox [3,5,11,13] [3,2,1,1] (2,1) p5_11_13_rows = true) := ⟨by decide +kernel⟩

private def p5_11_17_rows : List Witness := [([2,1,1,1], [(21,0xf04c070540b0580d00c0e0441201406024140280c0081001008)]),
  ([3,2,1,0], [(21,0x110540b0580f04c05040090500d0280303807010080040c00800)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_11_17_checked : PLift (checkBox [3,5,11,17] [3,2,1,1] (2,1) p5_11_17_rows = true) := ⟨by decide +kernel⟩

private def p5_11_19_rows : List Witness := [([2,1,2,1], [(31,0x170740b08411088150141b0581c0241f03c0a0401300c1905004068070201e038010081801800)]),
  ([2,2,1,1], [(31,0x1707c0b0841306c1501c1d0580f078090440a080030481a01414034060700e020100081803000)]),
  ([3,1,1,1], [(27,0x1706c0f074130781502c190581a034030440e07005024060500a060010400402000)]),
  ([3,2,1,0], [(21,0x110540b0580f04c05040090500d0280303807010080040c00800)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_11_19_checked : PLift (checkBox [3,5,11,19] [3,2,2,1] (2,1) p5_11_19_rows = true) := ⟨by decide +kernel⟩

private def p5_11_23_rows : List Witness := [([2,2,1,1], [(29,0x1707c0b084130881b01c1d0580f0241e02803080190481a0500d0181c038010400206004)]),
  ([3,1,1,1], [(27,0x1706c0f0741307807054190580d068030440e07005048090180a060010300204008)]),
  ([3,2,1,0], [(21,0x110540b0580f04c05040090500d0280303807010080040c00800)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_11_23_checked : PLift (checkBox [3,5,11,23] [3,2,1,1] (2,1) p5_11_23_rows = true) := ⟨by decide +kernel⟩

private def p5_11_29_rows : List Witness := [([2,2,1,1], [(33,0x1707c0b0841306c220540703c160241e0440302819048050680d050060700e00408040020600403000)]),
  ([3,1,1,1], [(29,0x1706c0f0741301c1e0540b06416034030680e0141c0480901814028010600c0080402000)]),
  ([3,2,1,0], [(21,0x110540b0580f04c05040090500d0280303807010080040c00800)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_11_29_checked : PLift (checkBox [3,5,11,29] [3,2,1,1] (2,1) p5_11_29_rows = true) := ⟨by decide +kernel⟩

private def p5_11_31_rows : List Witness := [([2,2,1,1], [(33,0x1707c0b0841306c2205407074160241e0440302820048050680d050060700e00408040020600403000)]),
  ([3,1,1,1], [(27,0x1706c0f0741301c1e0540b064160340306811038050701202414028180300204004)]),
  ([3,2,1,0], [(21,0x110540b0580f04c05040090500d0280303807010080040c00800)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_11_31_checked : PLift (checkBox [3,5,11,31] [3,2,1,1] (2,1) p5_11_31_rows = true) := ⟨by decide +kernel⟩

private def p5_11_37_rows : List Witness := [([2,2,1,1], [(31,0x1707c0b0841306c15088070740f02416078030640a080050480d0681407001038080400206000)]),
  ([3,1,2,1], [(43,0x230a4170b41d02c210b81109c150882b014280241607c2c03c1c0940a04c0304019098070502a0100d068080780103824048180180c)]),
  ([4,1,1,1], [(37,0x1f08c170941b03c1d09813084070541e064220341600c240441a0141c02412080060500102818030020400402000)]),
  ([3,2,1,0], [(21,0x110540b0580f04c05040090500d0280303807010080040c00800)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_11_37_checked : PLift (checkBox [3,5,11,37] [4,2,2,1] (2,1) p5_11_37_rows = true) := ⟨by decide +kernel⟩

private def p5_11_41_rows : List Witness := [([2,2,1,1], [(31,0x1707c0b0841306c15088070740f024160441e00c190282001412068140181c00408040020600c)]),
  ([3,1,2,1], [(43,0x230a4170b41d02c210b81109c150ac220141b0a00907c160b00f070130282000c190402601c140a80d0101a07801038240480206000)]),
  ([4,1,1,1], [(37,0x1f08c170941b03c1d09813084070541e02c190880d00c240441a0140e07009080060500102818030020400402000)]),
  ([3,2,1,0], [(21,0x110540b0580f04c05040090500d0280303807010080040c00800)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_11_41_checked : PLift (checkBox [3,5,11,41] [4,2,2,1] (2,1) p5_11_41_rows = true) := ⟨by decide +kernel⟩

private def p5_11_43_rows : List Witness := [([2,2,1,2], [(49,0x230bc110c81d0a4200d00b0b017038220682e01426040310201c0502807c33028020580d084190b4040940f0c00706c1309c1e0a8010540c0600309000)]),
  ([2,2,2,1], [(49,0x230bc110cc1d0a4210d00b0b40f0c42206c2e0142707c100c8090ac1c0540d080190282c00c250583001c1a04c040981e0202a0040c060020900604800)]),
  ([2,3,1,1], [(43,0x1f0ac0f0b41b09c1d0b80b0a41708c1e0642a01c2504c0e0241a0542600c210700a0a00505811030220600609001020140082001010)]),
  ([3,1,2,2], [(64,0x44321181a0ec2010434020290f40e0bc2210c170e02b074100c405114190e80b07c400503301c280f00d0b80208442058370700f0c004094180e40a0783f04c0609c0c0b4010543606c030900904800),(5,0x350f8231102c)]),
  ([3,1,3,1], [(59,0x2f0dc1f0f42703c2d0f8170d41d0ec2e01c250d80d0ac1e0f0150cc2606c390b00508c160d00b0a41c0e81301831090190302a00c2105032068380440408828004120c0180082004000)]),
  ([4,1,1,1], [(37,0x1f08c170941b03c1d09813084070541e02c190880d05803090110680507009048200181400418030020400402000)]),
  ([3,2,1,0], [(21,0x110540b0580f04c05040090500d0280303807010080040c00800)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_11_43_checked : PLift (checkBox [3,5,11,43] [4,3,3,2] (2,1) p5_11_43_rows = true) := ⟨by decide +kernel⟩

private def p5_11_47_rows : List Witness := [([2,2,2,1], [(47,0x230bc110cc1d0a42102c340b4170c42206c050b82707c10024320ac1c0540d0a020064030b0250580e01c300681301026078010a8140301809012)]),
  ([2,3,1,1], [(45,0x1f0ac0f0b41b09c1d02c2e0a4170341e064070a82504c0e0242c0681500c260841c028050581103022060060042404808050020800404000)]),
  ([4,1,2,1], [(55,0x2f0d4230e42905c2d0743a0cc0b0dc110b8270d0150ac05088380c4280241f0580f0b0250703204c0a00c2006436098070500d0a804068300200107824048020600603000)]),
  ([5,1,1,1], [(43,0x270ac1f0b42305c2506c2e0a40f07413098210a8070541e0642c0880d00c1604424068280140e0241c0800600414028180080402000)]),
  ([3,2,1,0], [(21,0x110540b0580f04c05040090500d0280303807010080040c00800)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_11_47_checked : PLift (checkBox [3,5,11,47] [5,3,2,1] (2,1) p5_11_47_rows = true) := ⟨by decide +kernel⟩

private def p5_11_53_rows : List Witness := [([2,2,2,1], [(49,0x230bc110cc1d0a42102c340b41703c310881b0b82707c10024320ac150342808019028030b0250580e0c01a04c040981e020010a814030180082401800)]),
  ([2,3,1,1], [(45,0x1f0ac0f0b41b09c1d02c2e0a417034230781901c2a04c0e0242c0681500c260841c028050a0160440c088180180109012020140080404000)]),
  ([4,1,2,1], [(57,0x2f0d4230e42905c2d0743a0cc0b084370b8270d0150ac050881b0e0310a00907c1603c2c0941c0c81302803080190d82601c140342a0101a0c0080041e03824048020600603000)]),
  ([6,1,1,2], [(64,0x1183e05c4c0b01d0e83213c0b100200442e0984305051124050881a0dc28020450f4160384b0ac390c44e028020fc1f0402d094420cc13120040841909c070f0150342a06c300041e03c240480306000),(13,0x471343b140410bc440d452128230e029)]),
  ([7,1,1,1], [(61,0x370ec2f0f43309c350ac3e0e41f0b4230d83105c3a0941b0b8290f00f0c81d04c260843401c2a0e00b078190b0220343000c1604424068050a00e0241c048200180102818030020400402000)]),
  ([3,2,1,0], [(21,0x110540b0580f04c05040090500d0280303807010080040c00800)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_11_53_checked : PLift (checkBox [3,5,11,53] [7,3,2,2] (2,1) p5_11_53_rows = true) := ⟨by decide +kernel⟩

private def p5_11_59_rows : List Witness := [([2,2,2,1], [(49,0x230bc110cc1d0a42102c2d0d01703c3106c22014270b81f0402b0c8150700d0a01908003028250b01601c0e0c01306826078010202a0500c0080604800)]),
  ([2,3,1,2], [(64,0x10417110290ec2c0443e11823050350982e02c381001d0381610c200a0050c83a0ac100f4450682204c340942d0080a0dc3f070151081f09c040c4390a80703c3c064210cc24004090d81b030030c018),(1,0x2f)]),
  ([2,4,1,1], [(55,0x270dc130e4230cc2503c350e81f0442f0842602c310d81b0482b0e01d088070b43205c24038340641e00c100a42e08005028300541a0302a070060b016020180082801014)]),
  ([4,1,2,1], [(57,0x2f0d4230e42905c2d074330e80b08437044270b8150ac0506c220c4380a00907c0f058250b03204c0302819080360402601c0d0502a0101a0c0010201e03824048020600603000)]),
  ([3,2,1,0], [(21,0x110540b0580f04c05040090500d0280303807010080040c00800)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_11_59_checked : PLift (checkBox [3,5,11,59] [4,4,2,2] (2,1) p5_11_59_rows = true) := ⟨by decide +kernel⟩

private def p5_11_61_rows : List Witness := [([2,2,2,1], [(49,0x230bc110cc1d0a42102c2d0d01703c3106c22014270b81f024100ac320541c0a01908003028250b01601c0e0c01306826078010202a030180080604800)]),
  ([2,4,1,1], [(55,0x270dc130e4230cc2503c350e81f0442f0842602c310d81b034120ac38088070b43205c240240e0d019078030402908005028300541a0302a070010182c058080602801014)]),
  ([4,1,2,1], [(57,0x2f0d4230e42905c2d074330e80b08437044270b8150d02b06c220c4380242807c0f058250b01c04c3200c1908036040070980d0502a0101a0c0010201e03824048020600603000)]),
  ([3,2,1,0], [(21,0x110540b0580f04c05040090500d0280303807010080040c00800)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_11_61_checked : PLift (checkBox [3,5,11,61] [4,4,2,1] (2,1) p5_11_61_rows = true) := ⟨by decide +kernel⟩

private def p5_11_67_rows : List Witness := [([2,2,4,2], [(64,0xc86610c201500a06c610f87213c050e416170271b47e0d011114221e40c0bc63100070605e1bc4c0083604c241a87b0c442024600f44e0101516c6c0cc10084780b83f0185d12c01048300783c1682d),(63,0x591dc2c20c4a1a056074742143b0a48011c58038651d8530682b1c4820e0490987d19c441540b070621cc502103a05c281b87f0d44608c571e80d10475148080645f0a870134810dc14120251ac7c)]),
  ([2,3,2,1], [(64,0x114290ec2d0443f1182310c3509c2e02c391002b0740f0583d110210a0130cc3a0942c024100dc3e06c22034141083407c2600c0a0c4380a81c01c0e06420048040c824004080d81a078020c00606000),(3,0x2f10417)]),
  ([4,1,2,2], [(64,0xd04a1540e0f42f05c220e0430ac1d1300515c260c4520640b0e8450501f1384001c33124021500d0f02e058210dc420a81c12c0f09430144180283904c1e0fc0609c480040c0b4150d81b0900904800),(21,0x47140351583e08c440b04d160110c8530683b1182013c4102029)]),
  ([4,1,3,1], [(64,0xb44b05c350f81d1183b01c250b843130360ac490541e0cc3c0981b110390140e08c2c1044a0580b0d02904c1c0c43a0182406442030210a848050090c81106838010400040a0a0120c0180800804000),(11,0x3f11c2f1343707c3d09c451380f)]),
  ([5,1,2,1], [(64,0x1143508c390a43f118170b4430743302c2110037044270b83d110150d02b0141b088310e0090a03e03c160942c1081c04c3200c0a064200d81001c260f00d0502a0101a0c0010780e090120600603000),(3,0x3b1042f)]),
  ([3,2,1,0], [(21,0x110540b0580f04c05040090500d0280303807010080040c00800)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_11_67_checked : PLift (checkBox [3,5,11,67] [5,3,4,2] (2,1) p5_11_67_rows = true) := ⟨by decide +kernel⟩

private def p5_11_71_rows : List Witness := [([2,3,2,1], [(64,0x10417114290ec2d0443f118230543509c2e02c391002b0740f0f4161102104c050cc3a0942c024370403e06c22034420d01f098030c40a0e02a070070383c06420048040c824004080680c078020c000),(1,0x2f)]),
  ([4,1,4,2], [(64,0x1b40a0bc1b1f0540148d0f82a0586313c8809411178360800c114311f86a01c4006079144022282704c601302216c331b0091082e1ec040544e21c240405d07c301a4060fc010484b0845a0b4030f01e),(64,0x1d8382147103847200582441a19c53230291883a1cc490d4821b80b24c440707d1548e0ac1719050224750985f0dc841c00d118321fc6b15c08240410647a1985222c2805061134391c823170480d081),(15,0x7721859248680ec74128832501d1588f0b065)]),
  ([5,1,2,1], [(64,0x1143508c390a43f118170b443074330e80b10037044270f42e110150d02b0141b0c4220e0090a01f03c250582c1081c04c3200c19028200d81001c260f00d0502a0101a0c0010201e090120081801800),(3,0x3b1042f)]),
  ([3,2,1,0], [(21,0x110540b0580f04c05040090500d0280303807010080040c00800)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_11_71_checked : PLift (checkBox [3,5,11,71] [5,3,4,2] (2,1) p5_11_71_rows = true) := ⟨by decide +kernel⟩

private def p5_11_73_rows : List Witness := [([2,3,2,1], [(64,0x114290ec2d0443f118230543509c2e02c390ac400740f0f4161102104c28014330943a0b0090dc3e06c0d088141081f0d02600c31028380a8070700e0f019048040c824004080d81a0301e0c00606000),(3,0x2f10417)]),
  ([5,1,2,1], [(64,0x1143508c390a43f118170b443074330e80b08440044270f42e110150ac340141b0c4220e00907c280f80f094160b0420703200c19028200d807040260f00d0502a0101a0c0080780e090120081803000),(3,0x3b1042f)]),
  ([3,2,1,0], [(21,0x110540b0580f04c05040090500d0280303807010080040c00800)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_11_73_checked : PLift (checkBox [3,5,11,73] [5,3,2,1] (2,1) p5_11_73_rows = true) := ⟨by decide +kernel⟩

private def p5_11_79_rows : List Witness := [([2,3,2,1], [(64,0x114290ec2d0443f08c46054430d40b0b8390ac1d1000f0f4160844404c050a0330943a0b0370401b0f80d0881407c420d003098310e0070a81c038190f020048040c801090080680c078020c00606000),(3,0x2f10417)]),
  ([5,1,2,1], [(64,0x1143508c390a43f118170b443074330e80b084371001109c3d0b8440542b0d0050c4220e00907c280f80f09416108130703200c19028200d807040260f00d0502a0101a004080780e090120081801800),(3,0x3b1042f)]),
  ([3,2,1,0], [(21,0x110540b0580f04c05040090500d0280303807010080040c00800)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_11_79_checked : PLift (checkBox [3,5,11,79] [5,3,2,1] (2,1) p5_11_79_rows = true) := ⟨by decide +kernel⟩

private def p5_11_83_rows : List Witness := [([2,3,2,1], [(64,0x10417114290ec2d0443f08c46054430d4270b8390ac1d1000f0f4160844404c050cc250e8090b0370401b0f80d0881407c420d0030980a0e0070a81c038190f020048040c801090080d81a078020c006),(1,0x2f)]),
  ([5,1,3,1], [(64,0x1700711859094430b80d1302b0d849054540cc510783c06c5a098390144408c0e0b00b128160a43404c520c41c0e8060645809003108210302a0244805032044500e004088011000a048300600208010),(25,0x4f15c3f174470bc4d0dc5507c5e0f45b09c4503c4e0b44b05c560d4530f81d)]),
  ([6,1,2,1], [(64,0x5c460b4430744c0cc490e821140370444009c3d0b8151102b0143406c4a0c4220243807c4e0a00f0f8160b0131081c00c32064480282001c36040260343c0502a0101a004300200e090120081803000),(15,0x471343b144410bc450d44b08c520e44f0a43f)]),
  ([3,2,1,0], [(21,0x110540b0580f04c05040090500d0280303807010080040c00800)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_11_83_checked : PLift (checkBox [3,5,11,83] [6,3,3,1] (2,1) p5_11_83_rows = true) := ⟨by decide +kernel⟩

private def p5_11_89_rows : List Witness := [([2,3,2,1], [(64,0x114290ec2d0443f08c46054430d42702c2e0ac1d1000f0f4160844404c050a0330943a0242c0dc1006c3e034220501f1083400c310283801c2a0700e0643c080120103200424020360681e0083006000),(3,0x2f10417)]),
  ([6,1,2,2], [(64,0x144c0986d040570c47802c52064600e81416c4507c66100070a06f008490cc0d1502e1d43c0585d0dc211081c18c2a0104b0946c03c3002851060391681e0fc0609c011200c0b4150d81b00c2402400),(57,0x6b1d0591e86211c68140710d47c158770f85f08c6a110650b0731346e044580c87914c1a1843b17046080671040813c291c04a0d07b038550bc760f45e0e0221a443074640ac72)]),
  ([6,1,3,1], [(64,0x10c610b80d1302b1a8490d8150cc510783c06c5a0e4260144408c621040e0b00b12829058680d013148310e8190185809003108211800c0a809120140c8111401a010220044002828048300602002010),(41,0x5f19c4f1b4570fc5d11c650bc6e1346b0dc5507c5e0f45b09c661146303c4e1b04b05c691583514c3e0745c0ec071644609464)]),
  ([7,1,2,1], [(64,0x10c1d130331240b084500dc11100271583d0b8151102b168050d01b12831088090e01f1382803c3e150160b0131081c00c32064480282001c36040260343c05004068010c0080780e048020600603000),(27,0x53164471744d0ec51104570bc5e1145b0d44b08c520e44f0a4580fc5505c460b45c)]),
  ([3,2,1,0], [(21,0x110540b0580f04c05040090500d0280303807010080040c00800)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_11_89_checked : PLift (checkBox [3,5,11,89] [7,3,3,2] (2,1) p5_11_89_rows = true) := ⟨by decide +kernel⟩

private def p5_11_97_rows : List Witness := [([2,3,2,1], [(64,0x10417114290ec2d0443f08c46054430d42702c390b82b0744003c210584404c050cc280943a024370b01b0400d0881f050420d0030c4260283801c1c0640e0f020048040c801090080d81a0303001818),(1,0x2f)]),
  ([7,1,3,2], [(64,0x1b45107c7e1301a2ac790b45a0a0871543901cb4198340089318415108101bc3d0849c1381c1ec492a02a0940921036010630c4900483f0346c0784b0647809c060cc011800f0f01b090030c00c06000),(64,0x11814294731046e148202c47f134ac1e82e2345b0a4ba220560e8082d49919c35250620587510c11288700f8222044f074ae1f04a2a45d0ac8a16026028b7214690dc05258640c891114131c8400389f),(57,0xa72cc8f2f09b1dca420cb017cbe230b91ac9811ca61d0a114cb2200ad0bc8e170bb2243b2d89a1a09505c76110a31c42327882140af1f45e0b0bd22c5902cb82186a0e09719492)]),
  ([7,1,4,1], [(64,0x708416c42064680fc8e19424128210207011c2e014961502b1e8510d80d1703306882100171983d230221201f0186e0b003148291e00e0d00b1683e05464080460102a00450030320583c0780202814),(64,0x1349c1cc312648015c7d04c620e48817c1d2146c10c921a48f138251d04b268711602f25c7e1547b0e811180372185d1101b20c6a1049019c262344c08c721243001c981bc560b47c14c121e43803c35),(25,0x8b254772748118c891b49313c9e1d49b1647f0ec8a18487114941ac9109c76)]),
  ([8,1,3,1], [(64,0x1a8490d815220540cc721441e0f01b16839098051e04408c621040e2002c02c4a0a4160d013148311c01c0e8190185809003108211800c0a809120140c8111401a0e004088011000a048300600208000),(64,0x13c8e1b48b15c750fc7e1747b11c86194830bc6e1348c1ac37224761547307c5e0f47c16c271e4661148418c811382d1b04b05c8a1a4560d47414c710f81d1703b01c7a1644609443208610b80d1302b),(9,0x7f21c6f2347717c7d19c85)]),
  ([3,2,1,0], [(21,0x110540b0580f04c05040090500d0280303807010080040c00800)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_11_97_checked : PLift (checkBox [3,5,11,97] [8,3,4,2] (2,1) p5_11_97_rows = true) := ⟨by decide +kernel⟩

private def p5_11_101_rows : List Witness := [([2,3,2,1], [(64,0x114290ec2d0443f08c15118430d42702c390b82b0740f1003d08416110050cc28094090e8370b01b0400d0f81f0504200c340c426028070e02a070190383c0800400432090080d80c078020c00606000),(3,0x2f10417)]),
  ([3,2,1,0], [(21,0x110540b0580f04c05040090500d0280303807010080040c00800)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_11_101_checked : PLift (checkBox [3,5,11,101] [3,3,2,1] (2,1) p5_11_101_rows = true) := ⟨by decide +kernel⟩

private def p5_11_103_rows : List Witness := [([2,3,2,1], [(64,0x10417114290ec2d0443f08c15118430d42702c390b82b0740f1003d0841604c0511033094090e8370b01b0400d0f82207c1400c420d0310980a01c38070190383c08012010010c8080d81a030020c018),(1,0x2f)]),
  ([3,2,1,0], [(21,0x110540b0580f04c05040090500d0280303807010080040c00800)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_11_103_checked : PLift (checkBox [3,5,11,103] [3,3,2,1] (2,1) p5_11_103_rows = true) := ⟨by decide +kernel⟩

private def p5_11_107_rows : List Witness := [([2,3,2,2], [(64,0x505e0bc1f1a4051904f1283a0400b154451002b098161805b0c41c01c660084c0f03703457148420a01804c5d0cc2e0780418c4e12439028540fc2a094151683006c060044b0305109c120b40312000),(37,0x47188231a03e164440685f0d4201a8651403b04456118410b0171845c0c8220740819c4d0f4380385814c430a419)]),
  ([2,3,3,1], [(64,0x1c5c164450d8330344e12c3c0e42505813150510b81c064051684610c340c40e02c4c1243a09823050111482c0a41a01803160440c80c0244a0e024084121402a06004004420c048088100a00210000),(25,0x3f15c1f1743713c3d05c550bc1d1785b11c3503c4d0f83b09c15158530781b)]),
  ([2,4,2,1], [(64,0xe8370a45213c410b41c0640b158450d03108c4c1243809c1604c051403f0b82b02454118430c8210400d128360a02505003138400f42c0600a01c440881f03848098040043e0a80810820030240f01e),(17,0x3b14c1d15c351343905c510bc1b1605511c330444b)]),
  ([3,2,1,0], [(21,0x110540b0580f04c05040090500d0280303807010080040c00800)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_11_107_checked : PLift (checkBox [3,5,11,107] [3,4,3,2] (2,1) p5_11_107_rows = true) := ⟨by decide +kernel⟩

private def p5_11_109_rows : List Witness := [([2,3,3,1], [(64,0x164450d8330344e12c3c0e42505813150510b82b070190145a118340c40e02c4c1243a09823050111482c0a41a0180316044104320244a0e024084121402a060040043002848088100a0021000808000),(27,0x3f15c1f1743713c3d05c550bc1d1785b11c3503c4d0f83b09c15158530b41e01c5c)]),
  ([2,4,2,1], [(64,0x13c410b41c0640b158450d03108c0f130490e02705813014500b82b068091504610c32084100344a0d82809403138400f42c0600a01c440c02207c0e12026048040042a020420800c090020f00607800),(21,0x3b14c1d15c351343905c510bc1b1605511c330444b0e8370a452)]),
  ([3,2,1,0], [(21,0x110540b0580f04c05040090500d0280303807010080040c00800)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_11_109_checked : PLift (checkBox [3,5,11,109] [3,4,3,1] (2,1) p5_11_109_rows = true) := ⟨by decide +kernel⟩

private def p5_11_113_rows : List Witness := [([2,3,3,1], [(64,0x6c0717059114360cc0d1383c0e42505813150510b82b070190145a118430d0310380b130490e82608c14044520a41a0180316044104320304a0e024084121402a06004004420c00a120220400210000),(25,0x3f15c1f1743713c3d05c550bc1d1785b11c3503c4d0f83b09c15158530b41e)]),
  ([2,4,2,1], [(64,0xa4151484f1041c0640b158450d03108c0f1304909c1604c051403f0b82b068091504610c210400d128360a02505003138400f42c0600a01c300881f0384809812010010f82a10820030240f00607800),(19,0x3b14c1d15c351343905c510bc1b1605511c330444b0e837)]),
  ([3,2,1,0], [(21,0x110540b0580f04c05040090500d0280303807010080040c00800)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_11_113_checked : PLift (checkBox [3,5,11,113] [3,4,3,1] (2,1) p5_11_113_rows = true) := ⟨by decide +kernel⟩

private def p5_11_127_rows : List Witness := [([2,4,3,1], [(64,0x905b1c85e0b44404c16184640cc4a0d8190141c14c6a158390f00b0880e164701702b1082e050620c4480d00306806144681503a0800c168291002c0486000418010520e00a1602a040300085002028),(49,0x4f1bc271d44719c4d07c6d0fc251cc5f1d84505c6512c371381d1ac571b83d03c261c45d1d0430bc4605463198490d44c06c07078691546c0ec3e0840d)]),
  ([2,5,2,1], [(64,0x640b07051188290e80f08055198580b43e04c050584b17031108340241a13c60148270e01e040560ac3c0b803050491684c0c8070600a140250d828038540b0010484a0c008138260302a0084801824),(39,0x47194231a44117c45074630ec2119c591a83f05c5d10c351181b184531903907c11088571a03d0bc400545b1345e0cc44)]),
  ([3,2,1,0], [(21,0x110540b0580f04c05040090500d0280303807010080040c00800)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_11_127_checked : PLift (checkBox [3,5,11,127] [3,5,3,1] (2,1) p5_11_127_rows = true) := ⟨by decide +kernel⟩

private def p5_11_131_rows : List Witness := [([2,4,3,1], [(64,0x16c72178410b44404c16184640cc4a0d8190141c14c6a158390f022038591c05c0ac420b811050620c4480d00306806144681503a024200305a0a4400b0600c80106004148381602a04030008080a000),(49,0x4f1bc271d44719c4d07c6d0fc251cc5f1d84505c6512c371381d1ac571b83d08c0f098711747410c2f11863198490d44c06c07078691546c0ec3e03424)]),
  ([3,2,1,0], [(21,0x110540b0580f04c05040090500d0280303807010080040c00800)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_11_131_checked : PLift (checkBox [3,5,11,131] [3,4,3,1] (2,1) p5_11_131_rows = true) := ⟨by decide +kernel⟩

private def p5_11_137_rows : List Witness := [([2,4,4,2], [(64,0x1487e15c222d4ba1788a18c020b8070cc0c268c627c6a1bc130fc18298d22ac4f1ec5407c242dc5b21c600100925cc32706c0403c054a813078144212d05d0042d018991a4a51381e168032580f12c00),(64,0x8c282d8bb3005f22c642402f020340349b0e4a03306b1c07505040064a7114d32b0d82c4501f055204200942a2e0bd170881848d198050c40a260363109d324a21b4720443d0584206ca9354ae13479),(64,0x124d72c0dc20059214292f0c123065244350383a320a1334711d84106846350ad2c8de1f456208260acb92f8891888e19c930c80b0dcc5278ca28ccf1b8730f81710c1c2a848358af36c7a14c7f16084),(27,0x953444a37486308920ecce1dc47368b337c830b0bf23c682503832ca4340741101d)]),
  ([2,5,3,1], [(64,0x4c2a05871220740ec520f8190141c18c7a198411604402c22038692006c1283604428050720e4500f003068061847819042024200306a0c434048700e8010600418840028680c8100e002180080c000),(64,0x22c772385507c7d16c471782520c6f2184d0ac170b8891d48c14c3f1581d19c7e164451702303c262046d2104b0dc4e0a4150b073228761443d1501b01c1e1e4651f043168460840d0906b1b8490d44c),(11,0x5f21c2f234571fc5d09c8513c2d)]),
  ([3,2,1,0], [(21,0x110540b0580f04c05040090500d0280303807010080040c00800)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_11_137_checked : PLift (checkBox [3,5,11,137] [3,5,4,2] (2,1) p5_11_137_rows = true) := ⟨by decide +kernel⟩

private def p5_11_139_rows : List Witness := [([2,5,3,1], [(64,0x130130a8161c4881d03b0f8190141c18c7a198411604402c22038692006c0cc4a0d8110a0141c8391403c00c061847819042024200306a0c4480d0121c03a00418010621000a1a03204038008600c000),(64,0x22c772385507c7d16c471782520c6f2184d0ac170b8891d48c14c3f1581d1ec671f8591145c08c0f098811b44b0dc4e0a4150b073228761443d1501b01c1e1e4651f043168460840d0906b2086e12435),(11,0x5f21c2f234571fc5d09c8513c2d)]),
  ([3,2,1,0], [(21,0x110540b0580f04c05040090500d0280303807010080040c00800)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_11_139_checked : PLift (checkBox [3,5,11,139] [3,5,3,1] (2,1) p5_11_139_rows = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_11_key_check : PLift ((∀ s : Fin 144, s.val.Prime → 11 < s.val → s.val ∈ p5_11_keys)) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem p5_11_box (i : Fin 29) :
    ∃ (caps : List ℕ) (rows : List Witness),
      caps.length = 4 ∧ (∀ c ∈ caps, 0 < c) ∧
      checkBox [3,5,11,p5_11_keys[i.val]!] caps (2,1) rows = true := by
  fin_cases i
  · exact ⟨[3,2,1,1], p5_11_13_rows, rfl, by decide, p5_11_13_checked.down⟩
  · exact ⟨[3,2,1,1], p5_11_17_rows, rfl, by decide, p5_11_17_checked.down⟩
  · exact ⟨[3,2,2,1], p5_11_19_rows, rfl, by decide, p5_11_19_checked.down⟩
  · exact ⟨[3,2,1,1], p5_11_23_rows, rfl, by decide, p5_11_23_checked.down⟩
  · exact ⟨[3,2,1,1], p5_11_29_rows, rfl, by decide, p5_11_29_checked.down⟩
  · exact ⟨[3,2,1,1], p5_11_31_rows, rfl, by decide, p5_11_31_checked.down⟩
  · exact ⟨[4,2,2,1], p5_11_37_rows, rfl, by decide, p5_11_37_checked.down⟩
  · exact ⟨[4,2,2,1], p5_11_41_rows, rfl, by decide, p5_11_41_checked.down⟩
  · exact ⟨[4,3,3,2], p5_11_43_rows, rfl, by decide, p5_11_43_checked.down⟩
  · exact ⟨[5,3,2,1], p5_11_47_rows, rfl, by decide, p5_11_47_checked.down⟩
  · exact ⟨[7,3,2,2], p5_11_53_rows, rfl, by decide, p5_11_53_checked.down⟩
  · exact ⟨[4,4,2,2], p5_11_59_rows, rfl, by decide, p5_11_59_checked.down⟩
  · exact ⟨[4,4,2,1], p5_11_61_rows, rfl, by decide, p5_11_61_checked.down⟩
  · exact ⟨[5,3,4,2], p5_11_67_rows, rfl, by decide, p5_11_67_checked.down⟩
  · exact ⟨[5,3,4,2], p5_11_71_rows, rfl, by decide, p5_11_71_checked.down⟩
  · exact ⟨[5,3,2,1], p5_11_73_rows, rfl, by decide, p5_11_73_checked.down⟩
  · exact ⟨[5,3,2,1], p5_11_79_rows, rfl, by decide, p5_11_79_checked.down⟩
  · exact ⟨[6,3,3,1], p5_11_83_rows, rfl, by decide, p5_11_83_checked.down⟩
  · exact ⟨[7,3,3,2], p5_11_89_rows, rfl, by decide, p5_11_89_checked.down⟩
  · exact ⟨[8,3,4,2], p5_11_97_rows, rfl, by decide, p5_11_97_checked.down⟩
  · exact ⟨[3,3,2,1], p5_11_101_rows, rfl, by decide, p5_11_101_checked.down⟩
  · exact ⟨[3,3,2,1], p5_11_103_rows, rfl, by decide, p5_11_103_checked.down⟩
  · exact ⟨[3,4,3,2], p5_11_107_rows, rfl, by decide, p5_11_107_checked.down⟩
  · exact ⟨[3,4,3,1], p5_11_109_rows, rfl, by decide, p5_11_109_checked.down⟩
  · exact ⟨[3,4,3,1], p5_11_113_rows, rfl, by decide, p5_11_113_checked.down⟩
  · exact ⟨[3,5,3,1], p5_11_127_rows, rfl, by decide, p5_11_127_checked.down⟩
  · exact ⟨[3,4,3,1], p5_11_131_rows, rfl, by decide, p5_11_131_checked.down⟩
  · exact ⟨[3,5,4,2], p5_11_137_rows, rfl, by decide, p5_11_137_checked.down⟩
  · exact ⟨[3,5,3,1], p5_11_139_rows, rfl, by decide, p5_11_139_checked.down⟩

private theorem p5_11_bounded (s a b c d : ℕ)
    (sp : s.Prime) (ordered : 11 < s) (sb : s < 144)
    (ap : 0 < a) (bp : 0 < b) (cp : 0 < c) (dp : 0 < d)
    (high : 2 < indexProduct [3,5,11,s] [a,b,c,d]) :
    ∃ k, k ∣ factorProduct [3,5,11,s] [a,b,c,d] ∧ k.Pseudoperfect := by
  have membership := p5_11_key_check.down ⟨s,sb⟩ sp ordered
  obtain ⟨i, hi, key⟩ := List.mem_iff_getElem.mp membership
  have word := p5_11_box ⟨i,hi⟩
  have ke : p5_11_keys[i]! = s := (getElem!_pos p5_11_keys i hi).trans key
  simp only [ke] at word
  obtain ⟨caps, rows, width, cp', checked⟩ := word
  have ps : ∀ p ∈ [3,5,11,s], 2 ≤ p := by simp [sp.two_le]
  have es : ∀ e ∈ [a,b,c,d], 0 < e := by simp [ap,bp,cp,dp]
  rcases checkBox_sound [3,5,11,s] caps [a,b,c,d] (2,1) rows checked ps es cp'
      rfl width.symm (by decide) with tooSmall | witness
  · exact False.elim ((not_le_of_gt high) (by simpa using tooSmall))
  · exact witness

private theorem p5_11 (s a b c d : ℕ)
    (sp : s.Prime) (ordered : 11 < s)
    (ap : 0 < a) (bp : 0 < b) (cp : 0 < c) (dp : 0 < d)
    (high : 2 < indexProduct [3,5,11,s] [a,b,c,d]) :
    ∃ k, k ∣ factorProduct [3,5,11,s] [a,b,c,d] ∧ k.Pseudoperfect := by
  rcases prefix11 a b c ap bp cp with prefixBound | ⟨k, kd, pp⟩
  · have sb := last_prime_bound 5 11 s a b c d 144 (143 / 72 : ℚ)
      (by decide) (by norm_num) (by norm_num [ceiling]) prefixBound high
    exact p5_11_bounded s a b c d sp ordered sb ap bp cp dp high
  · exact ⟨k,kd.trans (factor_prefix_dvd 5 11 s a b c d),pp⟩

private def p5_13_keys : List ℕ := [17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199,211,223,227,229,233,239,241,251,257,263,269,271,277,281,283,293,307,311,313,317,331,337,347,349,353,359,367,373,379,383]

private def p5_13_17_rows : List Witness := [([2,2,1,1], [(33,0x1707c0b084130881501c160740f07809028110800304819014140180d0700e02001040020600403000)]),
  ([3,1,1,1], [(29,0x1706c0f074130780702c160641a034030381107012014060240a06001030020400402000)]),
  ([3,3,2,0], [(45,0x230b0170b8200a40b088140ac1d058260202d07c110a00a068130142a0700e0542501c1e0400209c09064120100d0900603c010600303000)]),
  ([4,2,2,0], [(41,0x230a41a0ac2009811088170a01d020190382a05025040050841602c270700703402078130900f010150281b0180c0041200c00)]),
  ([4,3,1,0], [(37,0x1f094170981d08c0f078150901b01c160841c04c22038190141402c1a018110800c00c1206004028010400202000)]),
  ([5,2,1,0], [(33,0x1d084170881b07c11070150801902c1603c1a04c050781002414034180280303807048080040c00806)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_13_17_checked : PLift (checkBox [3,5,13,17] [5,3,2,1] (2,1) p5_13_17_rows = true) := ⟨by decide +kernel⟩

private def p5_13_19_rows : List Witness := [([2,2,1,1], [(31,0x1707c0b084130881b01c160740f0780902811080120641a014140180d0700e020010081801000)]),
  ([3,1,1,1], [(27,0x1706c0f07413078070540b05819034030381104805018090500a0600c0081002000)]),
  ([3,3,2,0], [(45,0x230b0170b8200a40b088140ac1d058260202d07c110a00a068130142a0700e0542501c1e0400209c09064120100d0900603c010600303000)]),
  ([4,2,2,0], [(41,0x230a41a0ac2009811088170a01d020190382a05025040050841602c270700703402078130900f010150281b0180c0041200c00)]),
  ([4,3,1,0], [(37,0x1f094170981d08c0f078150901b01c160841c04c22038190141402c1a018110800c00c1206004028010400202000)]),
  ([5,2,1,0], [(33,0x1d084170881b07c11070150801902c1603c1a04c050781002414034180280303807048080040c00806)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_13_19_checked : PLift (checkBox [3,5,13,19] [5,3,2,1] (2,1) p5_13_19_rows = true) := ⟨by decide +kernel⟩

private def p5_13_23_rows : List Witness := [([2,2,1,1], [(31,0x1707c0b084130881b054070741603c090440a00c190481a014140340603808004100081801000)]),
  ([3,1,1,2], [(43,0x230a4170b01d0b80b08011098220a0140141a0582b070080b40e02810094210082704c040542a06c070340903c240041200c1801800)]),
  ([3,1,2,1], [(45,0x230a4170b41d0b80b0841109c22054050ac1b0582c0700907c0f02825080100981300c19050040a81a01c0d0201e03801048020600603000)]),
  ([4,1,1,1], [(35,0x1f08c170941b0980f074130841e0881502c19058240680d00c0e070120142002406050180040c0081002000)]),
  ([3,3,2,0], [(45,0x230b0170b8200a40b088140ac1d058260202d07c110a00a068130142a0700e0542501c1e0400209c09064120100d0900603c010600303000)]),
  ([4,2,2,0], [(41,0x230a41a0ac2009811088170a01d020190382a05025040050841602c270700703402078130900f010150281b0180c0041200c00)]),
  ([4,3,1,0], [(37,0x1f094170981d08c0f078150901b01c160841c04c22038190141402c1a018110800c00c1206004028010400202000)]),
  ([5,2,1,0], [(33,0x1d084170881b07c11070150801902c1603c1a04c050781002414034180280303807048080040c00806)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_13_23_checked : PLift (checkBox [3,5,13,23] [5,3,2,2] (2,1) p5_13_23_rows = true) := ⟨by decide +kernel⟩

private def p5_13_29_rows : List Witness := [([2,2,2,1], [(49,0x230bc110cc1d0a4340840b0b4170880f0b81b0141009c320701f024280ac150800a0342c05803038250c01a01007098130780805001030020900604800)]),
  ([2,3,1,1], [(45,0x1f0ac0f0b41b09c2e0740b0a4170780d0a81901c0e094130b01a02426054030700a084280580503011060060901200408050020800404000)]),
  ([3,2,1,1], [(43,0x230ac170b41f02c2e084130a41b0881501c2a03c16094090b01e044030281908012014280680d050060700e00424020020600403000)]),
  ([4,1,2,1], [(55,0x2f0d4230e42905c3a0b41d0cc0b0b8210d03709c2205438014280ac1b058310242c0701f0c80a09420040130d803098190500401c2a068300201e03801090120080603000)]),
  ([5,1,1,1], [(45,0x270ac1f0b42305c2e0941b0a40f0981d04c2a08407078150b022064160342400c1a044280380507012024200181400418030020400402000)]),
  ([3,3,2,0], [(45,0x230b0170b8200a40b088140ac1d058260202d07c110a00a068130142a0700e0542501c1e0400209c09064120100d0900603c010600303000)]),
  ([4,2,2,0], [(41,0x230a41a0ac2009811088170a01d020190382a05025040050841602c270700703402078130900f010150281b0180c0041200c00)]),
  ([4,3,1,0], [(37,0x1f094170981d08c0f078150901b01c160841c04c22038190141402c1a018110800c00c1206004028010400202000)]),
  ([5,2,1,0], [(33,0x1d084170881b07c11070150801902c1603c1a04c050781002414034180280303807048080040c00806)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_13_29_checked : PLift (checkBox [3,5,13,29] [5,3,2,1] (2,1) p5_13_29_rows = true) := ⟨by decide +kernel⟩

private def p5_13_31_rows : List Witness := [([2,2,2,1], [(51,0x230bc110cc1d0a4340840b0b4170880f0b83106c05040270c81c024280ac150800a0342c0581900c0e094300680401c26078080a8140040c060020900604800)]),
  ([2,3,1,1], [(43,0x1f0ac0f0b41b09c2e0740b0a4170780d08c2a06407094130b01a02426054030700a084280580c088110600609012004080502001010)]),
  ([3,2,1,1], [(43,0x230ac170b41f02c2e084130a41b0881501c2a0740f058250242c044030980a06420048050a01a034140181c03801090080400206004)]),
  ([4,1,2,1], [(55,0x2f0d4230e42905c3a0b41d0cc0b0b821044340dc2705438014280ac1b058310242c0701f03c32028250801004c3600c260640401c2a0680d0c01e0380109012008180180c)]),
  ([5,1,1,2], [(64,0x8c460e0290f8170e82c074400c80b0b82010c110d0260884505037014280683d058390202b0fc0e0c40a0b41f108100cc020942104c36010190f01501c2a06c0d0c0090780f00424048030600603000),(5,0x3b1042f11035)]),
  ([6,1,1,1], [(51,0x2f0cc270d42b07c360b4230c4170b82506c320a40f0981d0d0130a82101c1e0542c02c22064300580d09003068110a00e0141c0482001814028010600204008)]),
  ([3,3,2,0], [(45,0x230b0170b8200a40b088140ac1d058260202d07c110a00a068130142a0700e0542501c1e0400209c09064120100d0900603c010600303000)]),
  ([4,2,2,0], [(41,0x230a41a0ac2009811088170a01d020190382a05025040050841602c270700703402078130900f010150281b0180c0041200c00)]),
  ([4,3,1,0], [(37,0x1f094170981d08c0f078150901b01c160841c04c22038190141402c1a018110800c00c1206004028010400202000)]),
  ([5,2,1,0], [(33,0x1d084170881b07c11070150801902c1603c1a04c050781002414034180280303807048080040c00806)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_13_31_checked : PLift (checkBox [3,5,13,31] [6,3,2,2] (2,1) p5_13_31_rows = true) := ⟨by decide +kernel⟩

private def p5_13_37_rows : List Witness := [([2,3,2,1], [(64,0x114290ec460b4110fc230b8150d443100270e416074440ac2803c3d0e8210142c04c330403e09422024140d01b108260340a0e01f00c2a0c40e0f02001c0404832064240203606801078020c00606000),(3,0x2f10417)]),
  ([3,2,1,1], [(43,0x230ac170b41f09c0b084130a41b0881501c2a07425058090b01e044030981902820048050a01a050060700e0042402010008180100c)]),
  ([5,1,2,2], [(64,0xbc2b05c641804c0e0101143107419014661483a0985b0cc1f02c07150400f0280505d12421034420b82a0580218c4b0dc0f07018010510e4251681e028060fc131200c0b4150043606c030900904800),(39,0x59188471a0500d46a1583e17c23160440b0651844d044460c81a19c5313c3b17034080081a4551043d0a44a0880e15c43)]),
  ([6,1,2,1], [(64,0x1303f05c3a0b41d140431003302c490b821110370d0271283d08815014380ac2806c4e0f831058090b01f0700f108250284808013040030d8260643c050070101a034300201e03801090020600603000),(15,0x471343b144410bc521143512c23118390a44f)]),
  ([3,3,2,0], [(45,0x230b0170b8200a40b088140ac1d058260202d07c110a00a068130142a0700e0542501c1e0400209c09064120100d0900603c010600303000)]),
  ([4,2,2,0], [(41,0x230a41a0ac2009811088170a01d020190382a05025040050841602c270700703402078130900f010150281b0180c0041200c00)]),
  ([4,3,1,0], [(37,0x1f094170981d08c0f078150901b01c160841c04c22038190141402c1a018110800c00c1206004028010400202000)]),
  ([5,2,1,0], [(33,0x1d084170881b07c11070150801902c1603c1a04c050781002414034180280303807048080040c00806)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_13_37_checked : PLift (checkBox [3,5,13,37] [6,3,2,2] (2,1) p5_13_37_rows = true) := ⟨by decide +kernel⟩

private def p5_13_41_rows : List Witness := [([2,3,2,2], [(64,0x14c1f0a44513c640503a1802f154050842b1004a198160f05b02c3115c07070261084c060371740d0cc520081e1386304c3903c2e150040a83f124151680a0c00606c2512c3603051004270b40312000),(37,0x47188231a03e164441a81a17c3508046140650ec61044560882c1046705c3d170321600810c4d1a4190e05e03834)]),
  ([2,3,3,1], [(64,0x14c2d1380706c3c11416164540342e12c1c094460e45a04c34038510ac4c014260e843050311480b0b0061241a08c44160110c80c0a44a00c3810412140090a804060211083002848004220400210000),(25,0x3f15c1f1743713c3d178171542f0743e11c5b0d45603c4d078270ec5c05436)]),
  ([2,4,2,1], [(64,0x158150d04113c2d1300b064381141608c311400f0b849068270145404c320fc100ac4a024280d843050211004e0342c028180944400c220c03d03807098040481f0f82a0204200420030240083c01800),(21,0x3b14c1d15c3513439160171442f06c3a11c550cc520444b07029)]),
  ([3,2,1,1], [(43,0x230ac170b41f09c0b0b8130a41b0542201c1d0a80f094090582c0441e00c1909820014120a00d068140181c0040e090080081803000)]),
  ([3,3,2,0], [(45,0x230b0170b8200a40b088140ac1d058260202d07c110a00a068130142a0700e0542501c1e0400209c09064120100d0900603c010600303000)]),
  ([4,2,2,0], [(41,0x230a41a0ac2009811088170a01d020190382a05025040050841602c270700703402078130900f010150281b0180c0041200c00)]),
  ([4,3,1,0], [(37,0x1f094170981d08c0f078150901b01c160841c04c22038190141402c1a018110800c00c1206004028010400202000)]),
  ([5,2,1,0], [(33,0x1d084170881b07c11070150801902c1603c1a04c050781002414034180280303807048080040c00806)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_13_41_checked : PLift (checkBox [3,5,13,41] [5,4,3,2] (2,1) p5_13_41_rows = true) := ⟨by decide +kernel⟩

private def p5_13_43_rows : List Witness := [([2,4,2,2], [(64,0x13876050431c8100e02519c54014340845c12478058451b40b0e8271a4070bc1c1784b060401bc0d0f064144020c41e180131080f0dc24198040cc5b1206c028390182e06c5d0fc0c18c010c01216809),(61,0x591f42c20c501d056214231e8470a46b160801347c068710f82b14c820806213c771101109868154840d4221287905c461b83b0a06a15c081fc1d17c4c1ec191c00e0f42a194522043207c61)]),
  ([2,4,3,1], [(64,0x1900d0d82116c4a0b41c158411a8130f00e184330885c0142e1c01914c42050391880b0d006164480ac1a150680443a0c420168030b05110012180090c8040a41814838160010a8100c002140080a000),(51,0x4f1bc271d44719c4d1d81f1b43f0945f138731146e05c650dc2612c74074571186b0f46603c5d1302f0787110c6c0543e18c350905e01c4906c55110161a43b)]),
  ([2,5,2,1], [(64,0x1343a16c330805802c66064510f8290583703c34154420b41a148051801312c3804031078560242e13c3c09c141305a034320282b0605000c280d80e150070b0040941212830138010980c0a80212006),(37,0x47194231a44117c451a81d18c3b08459118670fc6405c5d0d42210c6806c53100610e45e0441f15c440bc1c18815)]),
  ([3,2,1,1], [(43,0x230ac170b41f09c0b084130a41b0542201c1d0a80f094090582c0441e00c2602820014120a00d068140181c0040e02010008180100c)]),
  ([3,3,2,0], [(45,0x230b0170b8200a40b088140ac1d058260202d07c110a00a068130142a0700e0542501c1e0400209c09064120100d0900603c010600303000)]),
  ([4,2,2,0], [(41,0x230a41a0ac2009811088170a01d020190382a05025040050841602c270700703402078130900f010150281b0180c0041200c00)]),
  ([4,3,1,0], [(37,0x1f094170981d08c0f078150901b01c160841c04c22038190141402c1a018110800c00c1206004028010400202000)]),
  ([5,2,1,0], [(33,0x1d084170881b07c11070150801902c1603c1a04c050781002414034180280303807048080040c00806)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_13_43_checked : PLift (checkBox [3,5,13,43] [5,5,3,2] (2,1) p5_13_43_rows = true) := ⟨by decide +kernel⟩

private def p5_13_47_rows : List Witness := [([3,2,1,1], [(41,0x230ac170b41f09c0b084130b81b054070881d0a825024160442c00c1e06426028200480d0a01a050060041c038240201006004)]),
  ([3,3,2,0], [(45,0x230b0170b8200a40b088140ac1d058260202d07c110a00a068130142a0700e0542501c1e0400209c09064120100d0900603c010600303000)]),
  ([4,2,2,0], [(41,0x230a41a0ac2009811088170a01d020190382a05025040050841602c270700703402078130900f010150281b0180c0041200c00)]),
  ([4,3,1,0], [(37,0x1f094170981d08c0f078150901b01c160841c04c22038190141402c1a018110800c00c1206004028010400202000)]),
  ([5,2,1,0], [(33,0x1d084170881b07c11070150801902c1603c1a04c050781002414034180280303807048080040c00806)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_13_47_checked : PLift (checkBox [3,5,13,47] [5,3,2,1] (2,1) p5_13_47_rows = true) := ⟨by decide +kernel⟩

private def p5_13_53_rows : List Witness := [([3,2,1,1], [(45,0x230ac170b41f09c0b084130b81b054070881d03c2a094090581100c2c078190980a014200480d06814018010700e09008040020600403000)]),
  ([3,3,2,0], [(45,0x230b0170b8200a40b088140ac1d058260202d07c110a00a068130142a0700e0542501c1e0400209c09064120100d0900603c010600303000)]),
  ([4,2,2,0], [(41,0x230a41a0ac2009811088170a01d020190382a05025040050841602c270700703402078130900f010150281b0180c0041200c00)]),
  ([4,3,1,0], [(37,0x1f094170981d08c0f078150901b01c160841c04c22038190141402c1a018110800c00c1206004028010400202000)]),
  ([5,2,1,0], [(33,0x1d084170881b07c11070150801902c1603c1a04c050781002414034180280303807048080040c00806)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_13_53_checked : PLift (checkBox [3,5,13,53] [5,3,2,1] (2,1) p5_13_53_rows = true) := ⟨by decide +kernel⟩

private def p5_13_59_rows : List Witness := [([3,2,1,1], [(43,0x230ac170b41f09c0b084130b82906c070881d03c2a02416044030b01e06426028050801203428050060041c03824020020600403000)]),
  ([3,3,2,0], [(45,0x230b0170b8200a40b088140ac1d058260202d07c110a00a068130142a0700e0542501c1e0400209c09064120100d0900603c010600303000)]),
  ([4,2,2,0], [(41,0x230a41a0ac2009811088170a01d020190382a05025040050841602c270700703402078130900f010150281b0180c0041200c00)]),
  ([4,3,1,0], [(37,0x1f094170981d08c0f078150901b01c160841c04c22038190141402c1a018110800c00c1206004028010400202000)]),
  ([5,2,1,0], [(33,0x1d084170881b07c11070150801902c1603c1a04c050781002414034180280303807048080040c00806)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_13_59_checked : PLift (checkBox [3,5,13,59] [5,3,2,1] (2,1) p5_13_59_rows = true) := ⟨by decide +kernel⟩

private def p5_13_61_rows : List Witness := [([3,2,1,1], [(43,0x230ac170b41f09c0b084130b82906c070881d03c2a09409044030b01e06426028050800d0a01a050060041c03824040020600403000)]),
  ([3,3,2,0], [(45,0x230b0170b8200a40b088140ac1d058260202d07c110a00a068130142a0700e0542501c1e0400209c09064120100d0900603c010600303000)]),
  ([4,2,2,0], [(41,0x230a41a0ac2009811088170a01d020190382a05025040050841602c270700703402078130900f010150281b0180c0041200c00)]),
  ([4,3,1,0], [(37,0x1f094170981d08c0f078150901b01c160841c04c22038190141402c1a018110800c00c1206004028010400202000)]),
  ([5,2,1,0], [(33,0x1d084170881b07c11070150801902c1603c1a04c050781002414034180280303807048080040c00806)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_13_61_checked : PLift (checkBox [3,5,13,61] [5,3,2,1] (2,1) p5_13_61_rows = true) := ⟨by decide +kernel⟩

private def p5_13_67_rows : List Witness := [([3,2,1,1], [(43,0x230ac170b41f09c0b084130a42e06c150742203c250a8090441600c2c0641e098050280d04828068140040603824020100081803000)]),
  ([3,3,2,0], [(45,0x230b0170b8200a40b088140ac1d058260202d07c110a00a068130142a0700e0542501c1e0400209c09064120100d0900603c010600303000)]),
  ([4,2,2,0], [(41,0x230a41a0ac2009811088170a01d020190382a05025040050841602c270700703402078130900f010150281b0180c0041200c00)]),
  ([4,3,1,0], [(37,0x1f094170981d08c0f078150901b01c160841c04c22038190141402c1a018110800c00c1206004028010400202000)]),
  ([5,2,1,0], [(33,0x1d084170881b07c11070150801902c1603c1a04c050781002414034180280303807048080040c00806)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_13_67_checked : PLift (checkBox [3,5,13,67] [5,3,2,1] (2,1) p5_13_67_rows = true) := ⟨by decide +kernel⟩

private def p5_13_71_rows : List Witness := [([3,2,1,1], [(45,0x230ac170b41f09c0b084130a42e06c1501c2203c250242a0441600c19078050980a0800d0482806814004060700e09008040020600403000)]),
  ([3,3,2,0], [(45,0x230b0170b8200a40b088140ac1d058260202d07c110a00a068130142a0700e0542501c1e0400209c09064120100d0900603c010600303000)]),
  ([4,2,2,0], [(41,0x230a41a0ac2009811088170a01d020190382a05025040050841602c270700703402078130900f010150281b0180c0041200c00)]),
  ([4,3,1,0], [(37,0x1f094170981d08c0f078150901b01c160841c04c22038190141402c1a018110800c00c1206004028010400202000)]),
  ([5,2,1,0], [(33,0x1d084170881b07c11070150801902c1603c1a04c050781002414034180280303807048080040c00806)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_13_71_checked : PLift (checkBox [3,5,13,71] [5,3,2,1] (2,1) p5_13_71_rows = true) := ⟨by decide +kernel⟩

private def p5_13_73_rows : List Witness := [([3,2,1,1], [(43,0x230ac170b41f09c0b084130a42e06c1501c2203c250242a0441600c2c0641e01426028200342806814004060700e09008040020100c)]),
  ([3,3,2,0], [(45,0x230b0170b8200a40b088140ac1d058260202d07c110a00a068130142a0700e0542501c1e0400209c09064120100d0900603c010600303000)]),
  ([4,2,2,0], [(41,0x230a41a0ac2009811088170a01d020190382a05025040050841602c270700703402078130900f010150281b0180c0041200c00)]),
  ([4,3,1,0], [(37,0x1f094170981d08c0f078150901b01c160841c04c22038190141402c1a018110800c00c1206004028010400202000)]),
  ([5,2,1,0], [(33,0x1d084170881b07c11070150801902c1603c1a04c050781002414034180280303807048080040c00806)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_13_73_checked : PLift (checkBox [3,5,13,73] [5,3,2,1] (2,1) p5_13_73_rows = true) := ⟨by decide +kernel⟩

private def p5_13_79_rows : List Witness := [([3,2,1,1], [(43,0x230ac170b41f09c0b084130a41b0b81501c1d03c220242a04403058190b01e014260280d0802806801050060700e090080400403000)]),
  ([3,3,2,0], [(45,0x230b0170b8200a40b088140ac1d058260202d07c110a00a068130142a0700e0542501c1e0400209c09064120100d0900603c010600303000)]),
  ([4,2,2,0], [(41,0x230a41a0ac2009811088170a01d020190382a05025040050841602c270700703402078130900f010150281b0180c0041200c00)]),
  ([4,3,1,0], [(37,0x1f094170981d08c0f078150901b01c160841c04c22038190141402c1a018110800c00c1206004028010400202000)]),
  ([5,2,1,0], [(33,0x1d084170881b07c11070150801902c1603c1a04c050781002414034180280303807048080040c00806)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_13_79_checked : PLift (checkBox [3,5,13,79] [5,3,2,1] (2,1) p5_13_79_rows = true) := ⟨by decide +kernel⟩

private def p5_13_83_rows : List Witness := [([3,2,1,1], [(43,0x230ac170b41f09c0b084130a41b0b81501c1d03c22094090a803058190b01e01426034200482806801050060700e090080081803000)]),
  ([3,3,2,0], [(45,0x230b0170b8200a40b088140ac1d058260202d07c110a00a068130142a0700e0542501c1e0400209c09064120100d0900603c010600303000)]),
  ([4,2,2,0], [(41,0x230a41a0ac2009811088170a01d020190382a05025040050841602c270700703402078130900f010150281b0180c0041200c00)]),
  ([4,3,1,0], [(37,0x1f094170981d08c0f078150901b01c160841c04c22038190141402c1a018110800c00c1206004028010400202000)]),
  ([5,2,1,0], [(33,0x1d084170881b07c11070150801902c1603c1a04c050781002414034180280303807048080040c00806)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_13_83_checked : PLift (checkBox [3,5,13,83] [5,3,2,1] (2,1) p5_13_83_rows = true) := ⟨by decide +kernel⟩

private def p5_13_89_rows : List Witness := [([3,2,1,1], [(45,0x230ac170b41f09c0b084130a41b0b81501c1d03c22094090a81100c160642c078260280d080120a01a004140181c03824020100081803000)]),
  ([3,3,2,0], [(45,0x230b0170b8200a40b088140ac1d058260202d07c110a00a068130142a0700e0542501c1e0400209c09064120100d0900603c010600303000)]),
  ([4,2,2,0], [(41,0x230a41a0ac2009811088170a01d020190382a05025040050841602c270700703402078130900f010150281b0180c0041200c00)]),
  ([4,3,1,0], [(37,0x1f094170981d08c0f078150901b01c160841c04c22038190141402c1a018110800c00c1206004028010400202000)]),
  ([5,2,1,0], [(33,0x1d084170881b07c11070150801902c1603c1a04c050781002414034180280303807048080040c00806)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_13_89_checked : PLift (checkBox [3,5,13,89] [5,3,2,1] (2,1) p5_13_89_rows = true) := ⟨by decide +kernel⟩

private def p5_13_97_rows : List Witness := [([3,2,2,1], [(64,0x1142f0ec110cc1d0fc291180b10c2d05c340e40f1003106c050f4271102e07c090e82b040150c8370700d0f8280640308025028420b01601c0e04c30068040f0260041e0202a05036030180080604800),(3,0x3510423)]),
  ([3,3,1,1], [(57,0x2f0ec1f0f42b0dc0f0b41b0e4270743302c2905c2e0d40d08c3a06407094130f02a0c4090d80e054030b01a084260141c0c80a04428058340302206006090120c0080500208000)]),
  ([4,2,1,1], [(55,0x2f0dc230e42b0cc170b41f09c0b0e82104c2906c2e0c41501c360740f08825024380a81100c32058190b01e014340980a0342004828068010c0140181c03808040020100c)]),
  ([3,3,2,0], [(45,0x230b0170b8200a40b088140ac1d058260202d07c110a00a068130142a0700e0542501c1e0400209c09064120100d0900603c010600303000)]),
  ([4,2,2,0], [(41,0x230a41a0ac2009811088170a01d020190382a05025040050841602c270700703402078130900f010150281b0180c0041200c00)]),
  ([4,3,1,0], [(37,0x1f094170981d08c0f078150901b01c160841c04c22038190141402c1a018110800c00c1206004028010400202000)]),
  ([5,2,1,0], [(33,0x1d084170881b07c11070150801902c1603c1a04c050781002414034180280303807048080040c00806)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_13_97_checked : PLift (checkBox [3,5,13,97] [5,3,2,1] (2,1) p5_13_97_rows = true) := ⟨by decide +kernel⟩

private def p5_13_101_rows : List Witness := [([3,2,2,1], [(64,0x104231142f0ec110cc1d0fc291180b10c2d05c340e40f1003106c050f42209c440b81f0243a0ac100c8370700d0f8280640308025028420b01601c3803813068040f0260041e020140d80c0600209012),(1,0x35)]),
  ([3,3,1,1], [(57,0x2f0ec1f0f42b0dc0f0b41b0e4270743302c2905c2e0d40d08c3a06407078250f02a0c4090d80e054030b01a084380980507032028110a016030220041801824048300200208010)]),
  ([4,2,1,1], [(53,0x2f0dc230e42b0cc170b41f0d40b0e82104c2906c2e0c41501c360740f094090e02a044030c8160642c078050d00a0342004828068010c0140180e09008040020600c)]),
  ([3,3,2,0], [(45,0x230b0170b8200a40b088140ac1d058260202d07c110a00a068130142a0700e0542501c1e0400209c09064120100d0900603c010600303000)]),
  ([4,2,2,0], [(41,0x230a41a0ac2009811088170a01d020190382a05025040050841602c270700703402078130900f010150281b0180c0041200c00)]),
  ([4,3,1,0], [(37,0x1f094170981d08c0f078150901b01c160841c04c22038190141402c1a018110800c00c1206004028010400202000)]),
  ([5,2,1,0], [(33,0x1d084170881b07c11070150801902c1603c1a04c050781002414034180280303807048080040c00806)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_13_101_checked : PLift (checkBox [3,5,13,101] [5,3,2,1] (2,1) p5_13_101_rows = true) := ⟨by decide +kernel⟩

private def p5_13_103_rows : List Witness := [([3,2,2,1], [(64,0x1142f0ec110cc1d0fc291182110c2d05c340e40f0c44006c050f4271101f0b8090ac3a040150c8370341c0f8190a00308025028420b0160e00e04c30068040f0260041e0202a05036030180082404800),(3,0x3510423)]),
  ([3,3,1,1], [(59,0x2f0ec1f0f42b0dc0f0b41b0e4270743302c2905c2e0d40d08c3a064070782504c3c0c4090d80e054030b01a08438098050c80a044280583403022004180182404830020020800404000)]),
  ([4,2,1,1], [(55,0x2f0dc230e42b0cc170b41f0d40b0e82104c2906c2e0c41501c360740f088250242a044030c8160642c078050d0260342004828068010c0140181c03824020100081801000)]),
  ([3,3,2,0], [(45,0x230b0170b8200a40b088140ac1d058260202d07c110a00a068130142a0700e0542501c1e0400209c09064120100d0900603c010600303000)]),
  ([4,2,2,0], [(41,0x230a41a0ac2009811088170a01d020190382a05025040050841602c270700703402078130900f010150281b0180c0041200c00)]),
  ([4,3,1,0], [(37,0x1f094170981d08c0f078150901b01c160841c04c22038190141402c1a018110800c00c1206004028010400202000)]),
  ([5,2,1,0], [(33,0x1d084170881b07c11070150801902c1603c1a04c050781002414034180280303807048080040c00806)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_13_103_checked : PLift (checkBox [3,5,13,103] [5,3,2,1] (2,1) p5_13_103_rows = true) := ⟨by decide +kernel⟩

private def p5_13_107_rows : List Witness := [([3,2,2,1], [(64,0x1142f0ec110cc1d0fc291182110c2d05c340e40f0c44006c050f42209c4407c2e0243a040150c8370341c0f8190a00308025028420b00705838038130c01a0103c098010202a05036030180082404800),(3,0x3510423)]),
  ([3,3,1,1], [(61,0x2f0ec1f0f42b0dc0f0b41b0e4270743302c2905c2e0d40d08c3a064070782504c3c0a8310240e054030b01a084380980507032028110a0160d00c0880106006090120c008050020800404000)]),
  ([4,2,1,1], [(57,0x2f0dc230e42b0cc170b41f0d40b0e82104c2906c2e0c41501c360740f08825024380a81100c32058190b01e014260280d080120a01a00430050060700e09008040020600403000)]),
  ([3,3,2,0], [(45,0x230b0170b8200a40b088140ac1d058260202d07c110a00a068130142a0700e0542501c1e0400209c09064120100d0900603c010600303000)]),
  ([4,2,2,0], [(41,0x230a41a0ac2009811088170a01d020190382a05025040050841602c270700703402078130900f010150281b0180c0041200c00)]),
  ([4,3,1,0], [(37,0x1f094170981d08c0f078150901b01c160841c04c22038190141402c1a018110800c00c1206004028010400202000)]),
  ([5,2,1,0], [(33,0x1d084170881b07c11070150801902c1603c1a04c050781002414034180280303807048080040c00806)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_13_107_checked : PLift (checkBox [3,5,13,107] [5,3,2,1] (2,1) p5_13_107_rows = true) := ⟨by decide +kernel⟩

private def p5_13_109_rows : List Witness := [([3,2,2,1], [(64,0x1142f0ec110cc1d0fc291182110c2d05c390d00f0c44006c050f4270884407c2e0242b0e815040370c80d0703e0642800c250800a0b0070583804c0e0c01a0103c098010782a05036030180082404800),(3,0x3510423)]),
  ([3,3,1,1], [(61,0x2f0ec1f0f42b0dc0f0b41b0e4270743302c2905c350b80d08c3a064070941e04c3c0c42a024360540e00c2c0843809805070320440a0a0160d00c0880106006090120c008050020800404000)]),
  ([4,2,1,1], [(55,0x2f0dc230e42b0cc170b41f0d4270e82104c2906c310b81501c360740f094220242a044030c8190582c078050d0260340a04828068010c0140181c03824020020600403000)]),
  ([3,3,2,0], [(45,0x230b0170b8200a40b088140ac1d058260202d07c110a00a068130142a0700e0542501c1e0400209c09064120100d0900603c010600303000)]),
  ([4,2,2,0], [(41,0x230a41a0ac2009811088170a01d020190382a05025040050841602c270700703402078130900f010150281b0180c0041200c00)]),
  ([4,3,1,0], [(37,0x1f094170981d08c0f078150901b01c160841c04c22038190141402c1a018110800c00c1206004028010400202000)]),
  ([5,2,1,0], [(33,0x1d084170881b07c11070150801902c1603c1a04c050781002414034180280303807048080040c00806)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_13_109_checked : PLift (checkBox [3,5,13,109] [5,3,2,1] (2,1) p5_13_109_rows = true) := ⟨by decide +kernel⟩

private def p5_13_113_rows : List Witness := [([3,2,2,1], [(64,0x104231142f0ec110cc1d0fc291182102c2d05c390d00f0c44006c050f4270881f0b8090ac3a054100dc320703e0642800c250800a1082c01c160e01303830068040f0260041e020140d80c0600201812),(1,0x35)]),
  ([3,3,1,1], [(59,0x2f0ec1f0f42b0dc0f0b41b0e4270f83302c2905c350b80d08c3a064070941e04c3c0c42a024360540e00c2c0841a09805070320440a0583403022004180182404830020020800404000)]),
  ([4,2,1,1], [(55,0x2f0dc230e42b0cc170b41f0d4270e82104c2906c310b81501c360740f09422024380a81100c32064160b01e014260340a080120a01a00430050060700e09008008180100c)]),
  ([3,3,2,0], [(45,0x230b0170b8200a40b088140ac1d058260202d07c110a00a068130142a0700e0542501c1e0400209c09064120100d0900603c010600303000)]),
  ([4,2,2,0], [(41,0x230a41a0ac2009811088170a01d020190382a05025040050841602c270700703402078130900f010150281b0180c0041200c00)]),
  ([4,3,1,0], [(37,0x1f094170981d08c0f078150901b01c160841c04c22038190141402c1a018110800c00c1206004028010400202000)]),
  ([5,2,1,0], [(33,0x1d084170881b07c11070150801902c1603c1a04c050781002414034180280303807048080040c00806)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_13_113_checked : PLift (checkBox [3,5,13,113] [5,3,2,1] (2,1) p5_13_113_rows = true) := ⟨by decide +kernel⟩

private def p5_13_127_rows : List Witness := [([3,2,2,1], [(64,0x104231142f0ec110cc1d0fc290844602c430b43903c340c41b100050f4270881f110090b8150e8100dc0d0c81c0643e00c28094200284201c1604c3803830068040f0010981e0202a050360300209012),(1,0x35)]),
  ([3,3,1,1], [(57,0x2f0ec1f0f42b0dc0f0b41b0e427074330f80b05c35034230b81901c2504c1e0c43c0242a0543600c0e0842c06838014260703202828058340040c08806090120c0080080404000)]),
  ([4,2,1,1], [(53,0x2f0dc230e42b0cc170b41f0d42702c3a04c2906c310542e01c3603c25024220e0110a80306432058050783403426028120a001068300500607024020100600403000)]),
  ([3,3,2,0], [(45,0x230b0170b8200a40b088140ac1d058260202d07c110a00a068130142a0700e0542501c1e0400209c09064120100d0900603c010600303000)]),
  ([4,2,2,0], [(41,0x230a41a0ac2009811088170a01d020190382a05025040050841602c270700703402078130900f010150281b0180c0041200c00)]),
  ([4,3,1,0], [(37,0x1f094170981d08c0f078150901b01c160841c04c22038190141402c1a018110800c00c1206004028010400202000)]),
  ([5,2,1,0], [(33,0x1d084170881b07c11070150801902c1603c1a04c050781002414034180280303807048080040c00806)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_13_127_checked : PLift (checkBox [3,5,13,127] [5,3,2,1] (2,1) p5_13_127_rows = true) := ⟨by decide +kernel⟩

private def p5_13_131_rows : List Witness := [([3,2,2,1], [(64,0x104231142f0ec110cc1d0fc290844602c430b41703c340c41b1000509c2207c440242e0ac150e8100dc0d0c81c0f8030a0250800a108070b01604c38038300680400426078080a8140d80c0080604800),(1,0x35)]),
  ([3,3,1,1], [(59,0x2f0ec1f0f42b0dc0f0b41b0e427074330f80b05c35034230b8190e80704c1e0c43c0242a0543600c0e0842c068050981107032028160d0010302206006090120c008050020800404000)]),
  ([4,2,1,1], [(53,0x2f0dc230e42b0cc170b41f0d42702c3a04c2906c310542e01c1d0d825024220e0110a803064320582c0141e0d00d0980a080120a001068140181c03808040020600c)]),
  ([3,3,2,0], [(45,0x230b0170b8200a40b088140ac1d058260202d07c110a00a068130142a0700e0542501c1e0400209c09064120100d0900603c010600303000)]),
  ([4,2,2,0], [(41,0x230a41a0ac2009811088170a01d020190382a05025040050841602c270700703402078130900f010150281b0180c0041200c00)]),
  ([4,3,1,0], [(37,0x1f094170981d08c0f078150901b01c160841c04c22038190141402c1a018110800c00c1206004028010400202000)]),
  ([5,2,1,0], [(33,0x1d084170881b07c11070150801902c1603c1a04c050781002414034180280303807048080040c00806)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_13_131_checked : PLift (checkBox [3,5,13,131] [5,3,2,1] (2,1) p5_13_131_rows = true) := ⟨by decide +kernel⟩

private def p5_13_137_rows : List Witness := [([3,2,2,1], [(64,0x1142f0ec110cc1d0fc290840b118430b41703c340c41b014400f427088091102e0ac150e8100dc0d0c81c064030f82809420028071082c058130e00e0c01a010010f0260780805036030180082401800),(3,0x3510423)]),
  ([3,3,1,1], [(57,0x2f0ec1f0f42b0dc0f0b41b0e4270743302c3e05c35034230b81901c3a09413078310243c054030d80e0842c068050e0260441c0c80a0a0160d00c08818018240c0080500208004)]),
  ([4,2,1,1], [(55,0x2f0dc230e42b0cc170b41f0d42702c130e82906c31054070b81d03c36094090443800c2a06432058050b01e034340980a08012004280c0140181c03824020020600403000)]),
  ([3,3,2,0], [(45,0x230b0170b8200a40b088140ac1d058260202d07c110a00a068130142a0700e0542501c1e0400209c09064120100d0900603c010600303000)]),
  ([4,2,2,0], [(41,0x230a41a0ac2009811088170a01d020190382a05025040050841602c270700703402078130900f010150281b0180c0041200c00)]),
  ([4,3,1,0], [(37,0x1f094170981d08c0f078150901b01c160841c04c22038190141402c1a018110800c00c1206004028010400202000)]),
  ([5,2,1,0], [(33,0x1d084170881b07c11070150801902c1603c1a04c050781002414034180280303807048080040c00806)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_13_137_checked : PLift (checkBox [3,5,13,137] [5,3,2,1] (2,1) p5_13_137_rows = true) := ⟨by decide +kernel⟩

private def p5_13_139_rows : List Witness := [([3,2,2,1], [(64,0x104231142f0ec110cc1d0fc290840b118430b41703c340c41b014400f4270881f024440b8150e8100dc0d0c81c064030f8280942001c420b01604c3803830068040043c0981e020140d80c0082401812),(1,0x35)]),
  ([3,3,1,1], [(59,0x2f0ec1f0f42b0dc0f0b41b0e4270743302c3e05c35034230b81901c3a09413078310243c0a8150d80e0842c068050e0260441c0c80a0a01600434030220602404830020140082001000)]),
  ([4,2,1,1], [(55,0x2f0dc230e42b0cc170b41f0d42702c130e82906c31054070b81d03c36094090883800c2a06432058050b01e034340980a048010a01a0c0140181c03824040020600403000)]),
  ([3,3,2,0], [(45,0x230b0170b8200a40b088140ac1d058260202d07c110a00a068130142a0700e0542501c1e0400209c09064120100d0900603c010600303000)]),
  ([4,2,2,0], [(41,0x230a41a0ac2009811088170a01d020190382a05025040050841602c270700703402078130900f010150281b0180c0041200c00)]),
  ([4,3,1,0], [(37,0x1f094170981d08c0f078150901b01c160841c04c22038190141402c1a018110800c00c1206004028010400202000)]),
  ([5,2,1,0], [(33,0x1d084170881b07c11070150801902c1603c1a04c050781002414034180280303807048080040c00806)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_13_139_checked : PLift (checkBox [3,5,13,139] [5,3,2,1] (2,1) p5_13_139_rows = true) := ⟨by decide +kernel⟩

private def p5_13_149_rows : List Witness := [([3,2,2,1], [(64,0x104231142f0ec110cc1d0fc290840b118430b4170e40f0c41b014400f4270881f024440b82b054100dc0d0c81c064030f8280940a01c420b01604c3803830068040043c098080a8140d80c0600201800),(1,0x35)]),
  ([3,3,1,1], [(61,0x2f0ec1f0f42b0dc0f0b41b0e4270743302c3e0a435034230b81901c3a09413078310243c0a81500c36038210b01a01438098110703202828004340302206006090120c008050020800404000)]),
  ([4,2,1,1], [(55,0x2f0dc230e42b0cc170b41f0d42702c210e82906c31054070b81d03c36094090443800c2a06432058050b01e034340980a048010a01a0c0140180e09008040020600403000)]),
  ([3,3,2,0], [(45,0x230b0170b8200a40b088140ac1d058260202d07c110a00a068130142a0700e0542501c1e0400209c09064120100d0900603c010600303000)]),
  ([4,2,2,0], [(41,0x230a41a0ac2009811088170a01d020190382a05025040050841602c270700703402078130900f010150281b0180c0041200c00)]),
  ([4,3,1,0], [(37,0x1f094170981d08c0f078150901b01c160841c04c22038190141402c1a018110800c00c1206004028010400202000)]),
  ([5,2,1,0], [(33,0x1d084170881b07c11070150801902c1603c1a04c050781002414034180280303807048080040c00806)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_13_149_checked : PLift (checkBox [3,5,13,149] [5,3,2,1] (2,1) p5_13_149_rows = true) := ⟨by decide +kernel⟩

private def p5_13_151_rows : List Witness := [([3,2,2,1], [(64,0x1142f0ec110cc1d0fc290840b118430b4170e40f0c41b014400f4270881f024440b82b0543a040370341c064030f82809420028071082c058130e00e068040043c0981e0202a05036030020900604800),(3,0x3510423)]),
  ([3,3,1,1], [(57,0x2f0ec1f0f42b0dc0f0b41b0e4270743302c3e0a417034230b81901c3a04c1e0c4090f02a054030d80e0841a01438098110703202828058340302206006090120c0080502001010)]),
  ([4,2,1,1], [(53,0x2f0dc230e42b0cc170b41f0d42702c210e82906c31054070b81d03c36094090883800c2a06432058050b01e034340980a048010a01a0c0140181c090080400206004)]),
  ([3,3,2,0], [(45,0x230b0170b8200a40b088140ac1d058260202d07c110a00a068130142a0700e0542501c1e0400209c09064120100d0900603c010600303000)]),
  ([4,2,2,0], [(41,0x230a41a0ac2009811088170a01d020190382a05025040050841602c270700703402078130900f010150281b0180c0041200c00)]),
  ([4,3,1,0], [(37,0x1f094170981d08c0f078150901b01c160841c04c22038190141402c1a018110800c00c1206004028010400202000)]),
  ([5,2,1,0], [(33,0x1d084170881b07c11070150801902c1603c1a04c050781002414034180280303807048080040c00806)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_13_151_checked : PLift (checkBox [3,5,13,151] [5,3,2,1] (2,1) p5_13_151_rows = true) := ⟨by decide +kernel⟩

private def p5_13_157_rows : List Witness := [([3,2,2,1], [(64,0x1142f0ec110cc1d0fc290840b118430b4170e40f0d031014400f4270881f024440b82b0543a0dc100341c064030f82809420028071082c058130e00e068040043c0981e020140d80c060020900604800),(3,0x3510423)]),
  ([3,3,1,1], [(59,0x2f0ec1f0f42b0dc0f0b41b0e4270743302c3e0a417034230b81901c3a094130c4090f02a054030d80e0842c068050e0260441c0c80a0a01600434030220600604830020020800404000)]),
  ([4,2,1,1], [(55,0x2f0dc230e42b0cc170b41f0d42702c210e82906c31054070b81d03c36094090881100c380a8190c8160142c078340980a0801200428068300181c0382402010008180100c)]),
  ([3,3,2,0], [(45,0x230b0170b8200a40b088140ac1d058260202d07c110a00a068130142a0700e0542501c1e0400209c09064120100d0900603c010600303000)]),
  ([4,2,2,0], [(41,0x230a41a0ac2009811088170a01d020190382a05025040050841602c270700703402078130900f010150281b0180c0041200c00)]),
  ([4,3,1,0], [(37,0x1f094170981d08c0f078150901b01c160841c04c22038190141402c1a018110800c00c1206004028010400202000)]),
  ([5,2,1,0], [(33,0x1d084170881b07c11070150801902c1603c1a04c050781002414034180280303807048080040c00806)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_13_157_checked : PLift (checkBox [3,5,13,157] [5,3,2,1] (2,1) p5_13_157_rows = true) := ⟨by decide +kernel⟩

private def p5_13_163_rows : List Witness := [([3,2,2,1], [(64,0x1142f0ec110cc1d0fc290840b118430b4170e40f0d03106c050f4270881f024440b82b0543a0dc100341c064030f82809420028070b01604c3803830068040043c0981e0202a05036030020900604800),(3,0x3510423)]),
  ([3,3,1,1], [(59,0x2f0ec1f0f42b0dc0f0b41b0e4270743302c3e0a417034230b81901c3a09413078310243c0a81500c0e0842c068050e0260441c0c80a0a01600434030220600609012020140082001000)]),
  ([4,2,1,1], [(53,0x2f0dc230e42b0cc170b41f0d42702c2104c2906c31054070b81d03c3609409044030e02a064160142c0780d0d02602820048010a01a0c0140181c090080400206004)]),
  ([3,3,2,0], [(45,0x230b0170b8200a40b088140ac1d058260202d07c110a00a068130142a0700e0542501c1e0400209c09064120100d0900603c010600303000)]),
  ([4,2,2,0], [(41,0x230a41a0ac2009811088170a01d020190382a05025040050841602c270700703402078130900f010150281b0180c0041200c00)]),
  ([4,3,1,0], [(37,0x1f094170981d08c0f078150901b01c160841c04c22038190141402c1a018110800c00c1206004028010400202000)]),
  ([5,2,1,0], [(33,0x1d084170881b07c11070150801902c1603c1a04c050781002414034180280303807048080040c00806)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_13_163_checked : PLift (checkBox [3,5,13,163] [5,3,2,1] (2,1) p5_13_163_rows = true) := ⟨by decide +kernel⟩

private def p5_13_167_rows : List Witness := [([3,2,2,1], [(64,0x104231142f0ec110cc1d0fc290840b118430b4170e40f0d03106c051003d0881f024440b82b0543a0dc10034320701900c2809420028071082c058130e00e0c0040043c0981e0202a050360300209012),(1,0x35)]),
  ([3,3,1,1], [(59,0x2f0ec1f0f42b0dc0f0b41b0e4270743302c3e0a4170d4230b81901c3a09413078310243c0a81500c3603821068050e0260441c0c80a058010d00c088180182404830020140082004000)]),
  ([4,2,1,1], [(53,0x2f0dc230e42b0cc170b41f0d42702c2104c2906c31054070b81d03c3609409044030e02a06432058050b01e0d02602820048010a01a0c0140180e09008040020600c)]),
  ([3,3,2,0], [(45,0x230b0170b8200a40b088140ac1d058260202d07c110a00a068130142a0700e0542501c1e0400209c09064120100d0900603c010600303000)]),
  ([4,2,2,0], [(41,0x230a41a0ac2009811088170a01d020190382a05025040050841602c270700703402078130900f010150281b0180c0041200c00)]),
  ([4,3,1,0], [(37,0x1f094170981d08c0f078150901b01c160841c04c22038190141402c1a018110800c00c1206004028010400202000)]),
  ([5,2,1,0], [(33,0x1d084170881b07c11070150801902c1603c1a04c050781002414034180280303807048080040c00806)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_13_167_checked : PLift (checkBox [3,5,13,167] [5,3,2,1] (2,1) p5_13_167_rows = true) := ⟨by decide +kernel⟩

private def p5_13_173_rows : List Witness := [([3,2,2,1], [(64,0x1142f0ec110cc1d0fc290840b10c460b4170e40f0c43406c050f44009c22024440ac2e054370e80d040320641c00c3e0942801c0a1082c04c160e00e0c01a004040981e020140d80c060020900604800),(3,0x3510423)]),
  ([3,3,1,1], [(59,0x2f0ec1f0f42b0dc0f0b41b0e4270743302c3e0a4170d40d08c1901c3a094130c4090f02a054030d80e0842c068050e0260443202828058010d00c088180182404830020020800404000)]),
  ([4,2,1,1], [(55,0x2f0dc230e42b0cc170b41f0d42702c2104c2906c31054070b81d03c3609409088030e02a06432058050b01e034340980a0801200428068300501c0382402010008180100c)]),
  ([3,3,2,0], [(45,0x230b0170b8200a40b088140ac1d058260202d07c110a00a068130142a0700e0542501c1e0400209c09064120100d0900603c010600303000)]),
  ([4,2,2,0], [(41,0x230a41a0ac2009811088170a01d020190382a05025040050841602c270700703402078130900f010150281b0180c0041200c00)]),
  ([4,3,1,0], [(37,0x1f094170981d08c0f078150901b01c160841c04c22038190141402c1a018110800c00c1206004028010400202000)]),
  ([5,2,1,0], [(33,0x1d084170881b07c11070150801902c1603c1a04c050781002414034180280303807048080040c00806)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_13_173_checked : PLift (checkBox [3,5,13,173] [5,3,2,1] (2,1) p5_13_173_rows = true) := ⟨by decide +kernel⟩

private def p5_13_179_rows : List Witness := [([3,2,2,1], [(64,0x1142f0ec110cc1d0fc290840b10c460b4170e40f0c43406c050f44009c1f088091102b0b8150e80d040320641c00c250a02001c0a1082c04c160e00e0c01a004040981e0202a0500c060020900604800),(3,0x3510423)]),
  ([3,3,1,1], [(61,0x2f0ec1f0f42b0dc0f0b41b0e4270743302c3e0a4170d40d08c1901c3a09413078310243c054030d80e0842c068050e0260441c0c80a0a016004340302206006090120c008050020800404000)]),
  ([4,2,1,1], [(55,0x2f0dc230e42b0cc170b41f0d42702c2104c2906c31054070b81d03c36094090881100c3806432058050b01e034340980a0801200428068140181c03824020100080403000)]),
  ([3,3,2,0], [(45,0x230b0170b8200a40b088140ac1d058260202d07c110a00a068130142a0700e0542501c1e0400209c09064120100d0900603c010600303000)]),
  ([4,2,2,0], [(41,0x230a41a0ac2009811088170a01d020190382a05025040050841602c270700703402078130900f010150281b0180c0041200c00)]),
  ([4,3,1,0], [(37,0x1f094170981d08c0f078150901b01c160841c04c22038190141402c1a018110800c00c1206004028010400202000)]),
  ([5,2,1,0], [(33,0x1d084170881b07c11070150801902c1603c1a04c050781002414034180280303807048080040c00806)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_13_179_checked : PLift (checkBox [3,5,13,179] [5,3,2,1] (2,1) p5_13_179_rows = true) := ⟨by decide +kernel⟩

private def p5_13_181_rows : List Witness := [([3,2,2,1], [(64,0xec110cc1d0fc290840b10c460b4170e40f0c43406c050f44009c1f088091102b0b8150dc3a034320641c00c3e0942808007028420b0130583803830068010103c0981e0a8140d80c060020900604800),(5,0x35104231142f)]),
  ([3,3,1,1], [(59,0x2f0ec1f0f42b0dc0f0b41b0e4270743302c3e0a4170d40d08c1901c3a094130c41e0243c0a81500c210382c068050e0260443202828058010d00c088180182404830020020800404000)]),
  ([4,2,1,1], [(53,0x2f0dc230e42b0cc170b41f0d42702c2104c2906c31054070b81d03c36094090881100c380a819058050b01e0342602820048010a01a050060700e090100080403000)]),
  ([3,3,2,0], [(45,0x230b0170b8200a40b088140ac1d058260202d07c110a00a068130142a0700e0542501c1e0400209c09064120100d0900603c010600303000)]),
  ([4,2,2,0], [(41,0x230a41a0ac2009811088170a01d020190382a05025040050841602c270700703402078130900f010150281b0180c0041200c00)]),
  ([4,3,1,0], [(37,0x1f094170981d08c0f078150901b01c160841c04c22038190141402c1a018110800c00c1206004028010400202000)]),
  ([5,2,1,0], [(33,0x1d084170881b07c11070150801902c1603c1a04c050781002414034180280303807048080040c00806)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_13_181_checked : PLift (checkBox [3,5,13,181] [5,3,2,1] (2,1) p5_13_181_rows = true) := ⟨by decide +kernel⟩

private def p5_13_191_rows : List Witness := [([3,2,3,1], [(64,0xb80d1703b0f81d12c13138161044408c2601451150330d8290b00b0385a0e43c06c1e1244c050420842400c06148310d02a0240c1603a0641c1281208801010500c8280283806848080020c00806000),(27,0x4715c2f1743f13c1711427154370b40f16c5e0f41f1341510c460940714c560d42b)]),
  ([3,3,1,1], [(59,0x2f0ec1f0f42b0dc0f0b41b0e4270743302c3e0a4170d40d08c2e0643a094130c41e0243c0a81500c360840e0b01a01438098110c80a0a01600434030220182404830020140082004000)]),
  ([4,2,1,1], [(55,0x2f0dc230e42b0cc170b41f0d42702c2104c2906c31054070b81d03c36094090881100c380a8190c8160142c0780d0d026028200042806830050060700e090080081801000)]),
  ([3,3,2,0], [(45,0x230b0170b8200a40b088140ac1d058260202d07c110a00a068130142a0700e0542501c1e0400209c09064120100d0900603c010600303000)]),
  ([4,2,2,0], [(41,0x230a41a0ac2009811088170a01d020190382a05025040050841602c270700703402078130900f010150281b0180c0041200c00)]),
  ([4,3,1,0], [(37,0x1f094170981d08c0f078150901b01c160841c04c22038190141402c1a018110800c00c1206004028010400202000)]),
  ([5,2,1,0], [(33,0x1d084170881b07c11070150801902c1603c1a04c050781002414034180280303807048080040c00806)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_13_191_checked : PLift (checkBox [3,5,13,191] [5,3,3,1] (2,1) p5_13_191_rows = true) := ⟨by decide +kernel⟩

private def p5_13_193_rows : List Witness := [([3,2,3,1], [(64,0xd42b0b80d1645c0ec1d12c13138161044408c2601451150330d8290b00b0385a0e43c06c1e0444c050420842400c06148310d02a0240c1603a0641c0484008801010500c8280283806848040020c000),(25,0x4715c2f1743f13c1711427154370b40f16c5e0f41f1341510c460940714c56)]),
  ([3,3,1,1], [(59,0x2f0ec1f0f42b0dc0f0b41b0e4270743302c3e0a4170d40d08c2e06407094130c41e0243c054030d8210382c068050e0260443202828058010d00c088180182404830020020800404000)]),
  ([4,2,1,1], [(55,0x2f0dc230e42b0cc170b41f0d42702c2104c3a06c31054070b81d03c36094090881100c380a8190c8160142c0780d0d026028200042806830050060700e09008008180100c)]),
  ([3,3,2,0], [(45,0x230b0170b8200a40b088140ac1d058260202d07c110a00a068130142a0700e0542501c1e0400209c09064120100d0900603c010600303000)]),
  ([4,2,2,0], [(41,0x230a41a0ac2009811088170a01d020190382a05025040050841602c270700703402078130900f010150281b0180c0041200c00)]),
  ([4,3,1,0], [(37,0x1f094170981d08c0f078150901b01c160841c04c22038190141402c1a018110800c00c1206004028010400202000)]),
  ([5,2,1,0], [(33,0x1d084170881b07c11070150801902c1603c1a04c050781002414034180280303807048080040c00806)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_13_193_checked : PLift (checkBox [3,5,13,193] [5,3,3,1] (2,1) p5_13_193_rows = true) := ⟨by decide +kernel⟩

private def p5_13_197_rows : List Witness := [([3,2,3,1], [(64,0x342e1643b1701d0f84b04c4e0582311005098510cc540d82902c2c038391681b0f01e12411130140844200c2401831148340a80c160190e81c1281210001088040c8280283806848040200083006000),(27,0x4715c2f1743f13c1711427154370b40f16c3d1781f1341510c251180714c351582b)]),
  ([3,3,1,1], [(59,0x2f0ec1f0f42b0dc0f0b41b0e4270743302c290f8170d40d08c190b8070e8130c4090783c0542a00c210d82c0141a0e0110981c0c80a0a00105834030220600609030020140082001010)]),
  ([4,2,1,1], [(53,0x2f0dc230e42b0cc170b41f0d42702c2104c290e831054070742e03c250d809044220e0190a832014160b00d078340980a0800104828068140181c038080400206004)]),
  ([3,3,2,0], [(45,0x230b0170b8200a40b088140ac1d058260202d07c110a00a068130142a0700e0542501c1e0400209c09064120100d0900603c010600303000)]),
  ([4,2,2,0], [(41,0x230a41a0ac2009811088170a01d020190382a05025040050841602c270700703402078130900f010150281b0180c0041200c00)]),
  ([4,3,1,0], [(37,0x1f094170981d08c0f078150901b01c160841c04c22038190141402c1a018110800c00c1206004028010400202000)]),
  ([5,2,1,0], [(33,0x1d084170881b07c11070150801902c1603c1a04c050781002414034180280303807048080040c00806)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_13_197_checked : PLift (checkBox [3,5,13,197] [5,3,3,1] (2,1) p5_13_197_rows = true) := ⟨by decide +kernel⟩

private def p5_13_199_rows : List Witness := [([3,2,3,1], [(64,0x342e1643b1701d0f84b04c4e0584108c4401426144331503602c2c038391681b0f01e12411130140844200c2401831148340a80c160190e81c128121000108804140320a00a0e01a040200083002000),(27,0x4715c2f1743f13c1711427154370b40f16c3d1781f1341510c251180714c351582b)]),
  ([3,3,1,1], [(59,0x2f0ec1f0f42b0dc0f0b41b0e4270743302c290f8170d40d08c190b8070e8130c4090783c0542a00c210d80e0b005068110981c0c80a0a00105834030180182404830020140082001000)]),
  ([4,2,1,1], [(55,0x2f0dc230e42b0cc170b41f0d42702c2104c290e831054070742e03c250d8090442200c190a832014160b00d078340980a08001048280c0140181c03824040020600403000)]),
  ([3,3,2,0], [(45,0x230b0170b8200a40b088140ac1d058260202d07c110a00a068130142a0700e0542501c1e0400209c09064120100d0900603c010600303000)]),
  ([4,2,2,0], [(41,0x230a41a0ac2009811088170a01d020190382a05025040050841602c270700703402078130900f010150281b0180c0041200c00)]),
  ([4,3,1,0], [(37,0x1f094170981d08c0f078150901b01c160841c04c22038190141402c1a018110800c00c1206004028010400202000)]),
  ([5,2,1,0], [(33,0x1d084170881b07c11070150801902c1603c1a04c050781002414034180280303807048080040c00806)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_13_199_checked : PLift (checkBox [3,5,13,199] [5,3,3,1] (2,1) p5_13_199_rows = true) := ⟨by decide +kernel⟩

private def p5_13_211_rows : List Witness := [([3,3,1,1], [(61,0x2f0ec1f0f42b0dc0f0b41b0e4270743302c290f8170d40d08c190b8070943a04c310243c0542a00c210d80e0b00506838044260703202828004340302206006090120c008050020800404000)]),
  ([4,2,1,1], [(53,0x2f0dc230e42b0cc170b41f0d42702c2104c290e81b054070742e03c090d811088030e0190a8050c82c0341e0d02602820004120a01a0c0140180e09008040020100c)]),
  ([3,3,2,0], [(45,0x230b0170b8200a40b088140ac1d058260202d07c110a00a068130142a0700e0542501c1e0400209c09064120100d0900603c010600303000)]),
  ([4,2,2,0], [(41,0x230a41a0ac2009811088170a01d020190382a05025040050841602c270700703402078130900f010150281b0180c0041200c00)]),
  ([4,3,1,0], [(37,0x1f094170981d08c0f078150901b01c160841c04c22038190141402c1a018110800c00c1206004028010400202000)]),
  ([5,2,1,0], [(33,0x1d084170881b07c11070150801902c1603c1a04c050781002414034180280303807048080040c00806)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_13_211_checked : PLift (checkBox [3,5,13,211] [5,3,2,1] (2,1) p5_13_211_rows = true) := ⟨by decide +kernel⟩

private def p5_13_223_rows : List Witness := [([3,3,1,1], [(61,0x2f0ec1f0f42b0dc0f0b41b0e4270743302c290f8170d40d08c190b8070943a04c310241e0f0150a803084360382c0141a0e0110983202828004160d00c088180182404830020020800404000)]),
  ([4,2,1,1], [(53,0x2f0dc230e42b0cc170b41f0d42702c2104c290e81b054070742e03c2502436088030e0190a8050c8160341e0d02602820004120a01a050060700e090080400403000)]),
  ([3,3,2,0], [(45,0x230b0170b8200a40b088140ac1d058260202d07c110a00a068130142a0700e0542501c1e0400209c09064120100d0900603c010600303000)]),
  ([4,2,2,0], [(41,0x230a41a0ac2009811088170a01d020190382a05025040050841602c270700703402078130900f010150281b0180c0041200c00)]),
  ([4,3,1,0], [(37,0x1f094170981d08c0f078150901b01c160841c04c22038190141402c1a018110800c00c1206004028010400202000)]),
  ([5,2,1,0], [(33,0x1d084170881b07c11070150801902c1603c1a04c050781002414034180280303807048080040c00806)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_13_223_checked : PLift (checkBox [3,5,13,223] [5,3,2,1] (2,1) p5_13_223_rows = true) := ⟨by decide +kernel⟩

private def p5_13_227_rows : List Witness := [([3,4,1,1], [(64,0x124330944303c3507c4e114110bc3f02c3a0c41b1280d0ac260744c01c360b417118120f43808819120030c82909042038050d01e054440402e0f80a00430068400302a070060b0160f0080600201014),(9,0x3b12c271343711c130e423)]),
  ([4,2,1,1], [(53,0x2f0dc230e42b0cc170b41f0d42702c2104c2906c3a054070740f0b8250243604422064380a8050c8160342c078340980a080120a01a0c0140700e090080400201000)]),
  ([3,3,2,0], [(45,0x230b0170b8200a40b088140ac1d058260202d07c110a00a068130142a0700e0542501c1e0400209c09064120100d0900603c010600303000)]),
  ([4,2,2,0], [(41,0x230a41a0ac2009811088170a01d020190382a05025040050841602c270700703402078130900f010150281b0180c0041200c00)]),
  ([4,3,1,0], [(37,0x1f094170981d08c0f078150901b01c160841c04c22038190141402c1a018110800c00c1206004028010400202000)]),
  ([5,2,1,0], [(33,0x1d084170881b07c11070150801902c1603c1a04c050781002414034180280303807048080040c00806)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_13_227_checked : PLift (checkBox [3,5,13,227] [5,4,2,1] (2,1) p5_13_227_rows = true) := ⟨by decide +kernel⟩

private def p5_13_229_rows : List Witness := [([3,4,1,1], [(64,0x124330944303c3507c4e114110bc3f02c3a0c41b1280d0ac260744c01c360b417118120f4090e0220644800c3209042038050d01e054440402e0803e028010c0400302a070060b0160f008060020a004),(9,0x3b12c271343711c130e423)]),
  ([4,2,1,1], [(53,0x2f0dc230e42b0cc170b41f0d42702c2104c2906c3a054070740f0b8250243604403088380a8050c8160b01e0d02602801080120a01a0c0140700e090080400206000)]),
  ([3,3,2,0], [(45,0x230b0170b8200a40b088140ac1d058260202d07c110a00a068130142a0700e0542501c1e0400209c09064120100d0900603c010600303000)]),
  ([4,2,2,0], [(41,0x230a41a0ac2009811088170a01d020190382a05025040050841602c270700703402078130900f010150281b0180c0041200c00)]),
  ([4,3,1,0], [(37,0x1f094170981d08c0f078150901b01c160841c04c22038190141402c1a018110800c00c1206004028010400202000)]),
  ([5,2,1,0], [(33,0x1d084170881b07c11070150801902c1603c1a04c050781002414034180280303807048080040c00806)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_13_229_checked : PLift (checkBox [3,5,13,229] [5,4,2,1] (2,1) p5_13_229_rows = true) := ⟨by decide +kernel⟩

private def p5_13_233_rows : List Witness := [([3,4,1,1], [(64,0x124330944303c3507c4e114110bc3f02c3a0c41b128410342b0744c01c360b417118120f4090e0220644800c320a424108050d01e054440402e0803e028010c01a1000c0a8060b03c020180082801014),(9,0x3b12c271343711c130e423)]),
  ([4,2,1,1], [(55,0x2f0dc230e42b0cc170b41f0d42702c2104c2906c3a054070740f0b8250243604403088190e0050c8160342c078340980a004200a01a0c0140181c03824020100081801000)]),
  ([3,3,2,0], [(45,0x230b0170b8200a40b088140ac1d058260202d07c110a00a068130142a0700e0542501c1e0400209c09064120100d0900603c010600303000)]),
  ([4,2,2,0], [(41,0x230a41a0ac2009811088170a01d020190382a05025040050841602c270700703402078130900f010150281b0180c0041200c00)]),
  ([4,3,1,0], [(37,0x1f094170981d08c0f078150901b01c160841c04c22038190141402c1a018110800c00c1206004028010400202000)]),
  ([5,2,1,0], [(33,0x1d084170881b07c11070150801902c1603c1a04c050781002414034180280303807048080040c00806)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_13_233_checked : PLift (checkBox [3,5,13,233] [5,4,2,1] (2,1) p5_13_233_rows = true) := ⟨by decide +kernel⟩

private def p5_13_239_rows : List Witness := [([3,4,1,1], [(64,0x124330944303c3507c4e114110bc3f02c3a0c41b128410342b0981d130070b417118120f4090e0220644800c320a4241080e01434078440402e0803e028010c01a0302a070060583c020180082801000),(9,0x3b12c271343711c130e423)]),
  ([4,2,1,1], [(55,0x2f0dc230e42b0cc170b41f0d42702c2104c2906c3a054070740f0b8250243604403088190e02a014320580d0b0340980a0042004828068300501c0382402010008180100c)]),
  ([3,3,2,0], [(45,0x230b0170b8200a40b088140ac1d058260202d07c110a00a068130142a0700e0542501c1e0400209c09064120100d0900603c010600303000)]),
  ([4,2,2,0], [(41,0x230a41a0ac2009811088170a01d020190382a05025040050841602c270700703402078130900f010150281b0180c0041200c00)]),
  ([4,3,1,0], [(37,0x1f094170981d08c0f078150901b01c160841c04c22038190141402c1a018110800c00c1206004028010400202000)]),
  ([5,2,1,0], [(33,0x1d084170881b07c11070150801902c1603c1a04c050781002414034180280303807048080040c00806)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_13_239_checked : PLift (checkBox [3,5,13,239] [5,4,2,1] (2,1) p5_13_239_rows = true) := ⟨by decide +kernel⟩

private def p5_13_241_rows : List Witness := [([3,4,1,1], [(64,0x944303c3507c4e114110bc3f02c3a0c41b128410342b0981d130070d817118120f4090e0220644800c320a4241080e0141e054440402e0803e028010c01a1000c0a81c0182c0583c060020a00405000),(11,0x3b12c271343711c130e42312433)]),
  ([4,2,1,1], [(55,0x2f0dc230e42b0cc170b41f0d42702c2104c2906c3a054070740f0b8250243604403088190e02a014320580d0b01e0d026028010802806830050060700e090080400403000)]),
  ([3,3,2,0], [(45,0x230b0170b8200a40b088140ac1d058260202d07c110a00a068130142a0700e0542501c1e0400209c09064120100d0900603c010600303000)]),
  ([4,2,2,0], [(41,0x230a41a0ac2009811088170a01d020190382a05025040050841602c270700703402078130900f010150281b0180c0041200c00)]),
  ([4,3,1,0], [(37,0x1f094170981d08c0f078150901b01c160841c04c22038190141402c1a018110800c00c1206004028010400202000)]),
  ([5,2,1,0], [(33,0x1d084170881b07c11070150801902c1603c1a04c050781002414034180280303807048080040c00806)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_13_241_checked : PLift (checkBox [3,5,13,241] [5,4,2,1] (2,1) p5_13_241_rows = true) := ⟨by decide +kernel⟩

private def p5_13_251_rows : List Witness := [([3,4,1,1], [(64,0x944303c3507c4e114110bc2102c3a0c41b128410342b0981d130070d82d05c460483d0243808819120030c82909042038050d01e054440402e0800a00430068400302a070060b0160f0080082801000),(11,0x3b12c271343711c130e42312433)]),
  ([4,2,1,1], [(55,0x2f0dc230e42b0cc170b41f0d42702c2104c2906c3a0c4150740f0b8250243604403088190a8050c8160342c078340980a004200482806830050060700e090100600403000)]),
  ([3,3,2,0], [(45,0x230b0170b8200a40b088140ac1d058260202d07c110a00a068130142a0700e0542501c1e0400209c09064120100d0900603c010600303000)]),
  ([4,2,2,0], [(41,0x230a41a0ac2009811088170a01d020190382a05025040050841602c270700703402078130900f010150281b0180c0041200c00)]),
  ([4,3,1,0], [(37,0x1f094170981d08c0f078150901b01c160841c04c22038190141402c1a018110800c00c1206004028010400202000)]),
  ([5,2,1,0], [(33,0x1d084170881b07c11070150801902c1603c1a04c050781002414034180280303807048080040c00806)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_13_251_checked : PLift (checkBox [3,5,13,251] [5,4,2,1] (2,1) p5_13_251_rows = true) := ⟨by decide +kernel⟩

private def p5_13_257_rows : List Witness := [([3,4,1,1], [(64,0x944303c3507c4e114110bc210fc0b0c41b128410342b0981d130070d82d05c46048090e0220644800c320a4241080e0143407815110100b8200f80a00430068400302a0702c0583c020180082801014),(11,0x3b12c271343711c130e42312433)]),
  ([4,2,1,1], [(55,0x2f0dc230e42b0cc170b41f0d42702c2104c2906c3a0c4150740f0b8250243604403088190e02a014320582c078340980a0042004828068140181c03824020100081803000)]),
  ([3,3,2,0], [(45,0x230b0170b8200a40b088140ac1d058260202d07c110a00a068130142a0700e0542501c1e0400209c09064120100d0900603c010600303000)]),
  ([4,2,2,0], [(41,0x230a41a0ac2009811088170a01d020190382a05025040050841602c270700703402078130900f010150281b0180c0041200c00)]),
  ([4,3,1,0], [(37,0x1f094170981d08c0f078150901b01c160841c04c22038190141402c1a018110800c00c1206004028010400202000)]),
  ([5,2,1,0], [(33,0x1d084170881b07c11070150801902c1603c1a04c050781002414034180280303807048080040c00806)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_13_257_checked : PLift (checkBox [3,5,13,257] [5,4,2,1] (2,1) p5_13_257_rows = true) := ⟨by decide +kernel⟩

private def p5_13_263_rows : List Witness := [([3,4,1,1], [(64,0x124330944303c3507c4e114110bc210fc0b0e81b128410342b0981d01c4c0d817118120f4090e02206403120320a4241080e01434078150402e0803e028010c01a1000c0a8060b016020180082801000),(9,0x3b12c271343711c130e423)]),
  ([4,2,1,1], [(53,0x2f0dc230e42b0cc170b41f0d42702c2104c2906c3a0c41501c0f0b8250243600c22064380a8050c8160b01e0d0260280108012068300500607024020100081801000)]),
  ([3,3,2,0], [(45,0x230b0170b8200a40b088140ac1d058260202d07c110a00a068130142a0700e0542501c1e0400209c09064120100d0900603c010600303000)]),
  ([4,2,2,0], [(41,0x230a41a0ac2009811088170a01d020190382a05025040050841602c270700703402078130900f010150281b0180c0041200c00)]),
  ([4,3,1,0], [(37,0x1f094170981d08c0f078150901b01c160841c04c22038190141402c1a018110800c00c1206004028010400202000)]),
  ([5,2,1,0], [(33,0x1d084170881b07c11070150801902c1603c1a04c050781002414034180280303807048080040c00806)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_13_263_checked : PLift (checkBox [3,5,13,263] [5,4,2,1] (2,1) p5_13_263_rows = true) := ⟨by decide +kernel⟩

private def p5_13_269_rows : List Witness := [([3,4,1,1], [(64,0x3c3507c4e114110bc210fc0b0e81b128410342b0981d01c4c0d82d05c460483d024380881900c480a4241080e0143407815110100b8200f80a00430068400302a070060b0160f008060020a00405000),(13,0x3b12c271343711c130e4231243309443)]),
  ([4,2,1,1], [(55,0x2f0dc230e42b0cc170b41f0d42702c2104c2906c3a0c41501c0f0b8250243604422064380a8050c8160342c0783409801080120a01a0c0140181c03824020100081801000)]),
  ([3,3,2,0], [(45,0x230b0170b8200a40b088140ac1d058260202d07c110a00a068130142a0700e0542501c1e0400209c09064120100d0900603c010600303000)]),
  ([4,2,2,0], [(41,0x230a41a0ac2009811088170a01d020190382a05025040050841602c270700703402078130900f010150281b0180c0041200c00)]),
  ([4,3,1,0], [(37,0x1f094170981d08c0f078150901b01c160841c04c22038190141402c1a018110800c00c1206004028010400202000)]),
  ([5,2,1,0], [(33,0x1d084170881b07c11070150801902c1603c1a04c050781002414034180280303807048080040c00806)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_13_269_checked : PLift (checkBox [3,5,13,269] [5,4,2,1] (2,1) p5_13_269_rows = true) := ⟨by decide +kernel⟩

private def p5_13_271_rows : List Witness := [([3,4,1,1], [(64,0x124330944303c3507c4e114110bc210fc0b0e831128410342b0981d01c4c0d82d05c46048090e02206403120320a4241080e0143407815110100b83e028010c01a1002a070060b0160f008060020a000),(9,0x3b12c271343711c130e423)]),
  ([4,2,1,1], [(53,0x2f0dc230e42b0cc170b41f0d42702c2104c2906c3a0c41501c0f0b8250243604403064380a8050c8160342c0782602801080120a030050060700e09008008180100c)]),
  ([3,3,2,0], [(45,0x230b0170b8200a40b088140ac1d058260202d07c110a00a068130142a0700e0542501c1e0400209c09064120100d0900603c010600303000)]),
  ([4,2,2,0], [(41,0x230a41a0ac2009811088170a01d020190382a05025040050841602c270700703402078130900f010150281b0180c0041200c00)]),
  ([4,3,1,0], [(37,0x1f094170981d08c0f078150901b01c160841c04c22038190141402c1a018110800c00c1206004028010400202000)]),
  ([5,2,1,0], [(33,0x1d084170881b07c11070150801902c1603c1a04c050781002414034180280303807048080040c00806)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_13_271_checked : PLift (checkBox [3,5,13,271] [5,4,2,1] (2,1) p5_13_271_rows = true) := ⟨by decide +kernel⟩

private def p5_13_277_rows : List Witness := [([3,4,1,1], [(64,0x944303c3507c4e114110bc210fc0b0e83106c410342b0981d01c4c0d82d05c460f4090e02206403120320a4241080e0143407815110100b8200f8010c01a1000c0a81c0182c0583c020180082805000),(11,0x3b12c271343711c130e42312433)]),
  ([4,2,1,1], [(55,0x2f0dc230e42b0cc170b41f0d42702c2104c2906c3a0c41501c0f0b8250243604403088190a8050c8160342c0783402801080120a01a0c0140181c0382402010008180100c)]),
  ([3,3,2,0], [(45,0x230b0170b8200a40b088140ac1d058260202d07c110a00a068130142a0700e0542501c1e0400209c09064120100d0900603c010600303000)]),
  ([4,2,2,0], [(41,0x230a41a0ac2009811088170a01d020190382a05025040050841602c270700703402078130900f010150281b0180c0041200c00)]),
  ([4,3,1,0], [(37,0x1f094170981d08c0f078150901b01c160841c04c22038190141402c1a018110800c00c1206004028010400202000)]),
  ([5,2,1,0], [(33,0x1d084170881b07c11070150801902c1603c1a04c050781002414034180280303807048080040c00806)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_13_277_checked : PLift (checkBox [3,5,13,277] [5,4,2,1] (2,1) p5_13_277_rows = true) := ⟨by decide +kernel⟩

private def p5_13_281_rows : List Witness := [([3,4,1,1], [(64,0x944303c3507c4e114110bc210fc0b0e83106c410342b0981d01c4c0d82d05c460483d024380881900c480c8241080e0143407815110100b820028010c01a1000c0a81c0182c0583c020020a00405000),(11,0x3b12c271343711c130e42312433)]),
  ([4,2,1,1], [(53,0x2f0dc230e42b0cc170b41f0d42702c2104c2906c3a0c41501c0f0b8250243604403088190e02a0c8160342c078340980a004120a01a0c0140181c038240200206000)]),
  ([3,3,2,0], [(45,0x230b0170b8200a40b088140ac1d058260202d07c110a00a068130142a0700e0542501c1e0400209c09064120100d0900603c010600303000)]),
  ([4,2,2,0], [(41,0x230a41a0ac2009811088170a01d020190382a05025040050841602c270700703402078130900f010150281b0180c0041200c00)]),
  ([4,3,1,0], [(37,0x1f094170981d08c0f078150901b01c160841c04c22038190141402c1a018110800c00c1206004028010400202000)]),
  ([5,2,1,0], [(33,0x1d084170881b07c11070150801902c1603c1a04c050781002414034180280303807048080040c00806)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_13_281_checked : PLift (checkBox [3,5,13,281] [5,4,2,1] (2,1) p5_13_281_rows = true) := ⟨by decide +kernel⟩

private def p5_13_283_rows : List Witness := [([3,4,1,1], [(64,0x944303c3507c4e114110bc210fc0b0e83106c410342b0981d01c4c0d82d05c460483d024380881900c480c82909042038050d01e054440402e0803e028010c01a1000c0a8060b03c020180082801014),(11,0x3b12c271343711c130e42312433)]),
  ([4,2,1,1], [(55,0x2f0dc230e42b0cc170b41f0d42702c2104c2906c3a0c41501c0f0b8250243604403088190e02a014160342c078340980a004120a01a0c0140181c03824020100600403000)]),
  ([3,3,2,0], [(45,0x230b0170b8200a40b088140ac1d058260202d07c110a00a068130142a0700e0542501c1e0400209c09064120100d0900603c010600303000)]),
  ([4,2,2,0], [(41,0x230a41a0ac2009811088170a01d020190382a05025040050841602c270700703402078130900f010150281b0180c0041200c00)]),
  ([4,3,1,0], [(37,0x1f094170981d08c0f078150901b01c160841c04c22038190141402c1a018110800c00c1206004028010400202000)]),
  ([5,2,1,0], [(33,0x1d084170881b07c11070150801902c1603c1a04c050781002414034180280303807048080040c00806)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_13_283_checked : PLift (checkBox [3,5,13,283] [5,4,2,1] (2,1) p5_13_283_rows = true) := ⟨by decide +kernel⟩

private def p5_13_293_rows : List Witness := [([3,4,1,1], [(64,0x944303c3507c4e114110bc210fc0b0e83106c4a1040d0ac1d01c4c0d82d05c460483d0242206403120320a4241080e0143407815110100b8200f80a00430068400302a0182c0583c020020a00405000),(11,0x3b12c271343711c130e42312433)]),
  ([4,2,1,1], [(53,0x2f0dc230e42b0cc170b41f0d42702c2104c2906c3a0c41501c1d0b8250243604403088190e02a014160342c078340980a004200481a0c0140180e09008040020600c)]),
  ([3,3,2,0], [(45,0x230b0170b8200a40b088140ac1d058260202d07c110a00a068130142a0700e0542501c1e0400209c09064120100d0900603c010600303000)]),
  ([4,2,2,0], [(41,0x230a41a0ac2009811088170a01d020190382a05025040050841602c270700703402078130900f010150281b0180c0041200c00)]),
  ([4,3,1,0], [(37,0x1f094170981d08c0f078150901b01c160841c04c22038190141402c1a018110800c00c1206004028010400202000)]),
  ([5,2,1,0], [(33,0x1d084170881b07c11070150801902c1603c1a04c050781002414034180280303807048080040c00806)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_13_293_checked : PLift (checkBox [3,5,13,293] [5,4,2,1] (2,1) p5_13_293_rows = true) := ⟨by decide +kernel⟩

private def p5_13_307_rows : List Witness := [([3,4,1,1], [(64,0x944303c3507c4e114110bc210fc0b0e83106c4a1040d0ac2607407130360b4170f412024380881900c480c8290900e0143407815110100b8200f80a00430068400302a0182c0583c060020a00405000),(11,0x3b12c271343711c130e42312433)]),
  ([4,2,1,1], [(53,0x2f0dc230e42b0cc170b41f0d42702c2104c2906c3a0c41501c1d03c250243604403088190e0050c8160342c078340980a004200a01a0c0140181c03808040020100c)]),
  ([3,3,2,0], [(45,0x230b0170b8200a40b088140ac1d058260202d07c110a00a068130142a0700e0542501c1e0400209c09064120100d0900603c010600303000)]),
  ([4,2,2,0], [(41,0x230a41a0ac2009811088170a01d020190382a05025040050841602c270700703402078130900f010150281b0180c0041200c00)]),
  ([4,3,1,0], [(37,0x1f094170981d08c0f078150901b01c160841c04c22038190141402c1a018110800c00c1206004028010400202000)]),
  ([5,2,1,0], [(33,0x1d084170881b07c11070150801902c1603c1a04c050781002414034180280303807048080040c00806)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_13_307_checked : PLift (checkBox [3,5,13,307] [5,4,2,1] (2,1) p5_13_307_rows = true) := ⟨by decide +kernel⟩

private def p5_13_311_rows : List Witness := [([3,4,1,1], [(64,0x3c3507c4e114110bc210fc0b0e83106c4a1040d0ac2607407130360b4171183d048090e01900c480c82909042038050d01e054440402e0803e028010c0400302a070060b0160f008060020a00405000),(13,0x3b12c271343711c130e4231243309443)]),
  ([4,2,1,1], [(55,0x2f0dc230e42b0cc170b41f0d42702c2104c2906c3a0c41501c1d03c250243604403088190e02a014160342c0783402801080120a01a0c0140181c09008040020600403000)]),
  ([3,3,2,0], [(45,0x230b0170b8200a40b088140ac1d058260202d07c110a00a068130142a0700e0542501c1e0400209c09064120100d0900603c010600303000)]),
  ([4,2,2,0], [(41,0x230a41a0ac2009811088170a01d020190382a05025040050841602c270700703402078130900f010150281b0180c0041200c00)]),
  ([4,3,1,0], [(37,0x1f094170981d08c0f078150901b01c160841c04c22038190141402c1a018110800c00c1206004028010400202000)]),
  ([5,2,1,0], [(33,0x1d084170881b07c11070150801902c1603c1a04c050781002414034180280303807048080040c00806)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_13_311_checked : PLift (checkBox [3,5,13,311] [5,4,2,1] (2,1) p5_13_311_rows = true) := ⟨by decide +kernel⟩

private def p5_13_313_rows : List Witness := [([3,4,1,1], [(64,0x944303c3507c4e114110bc210fc0b0e83106c4a1040d0ac2607407130360b4171183d048090e02206403120320a442038050d01e054440402e0f80a00430068400302a070060b03c020180082801014),(11,0x3b12c271343711c130e42312433)]),
  ([4,2,1,1], [(55,0x2f0dc230e42b0cc170b41f0d42702c2104c2906c3a0c41501c1d03c250243604403088190e02a014160342c078340980a00420048280c0140181c0382402010008180100c)]),
  ([3,3,2,0], [(45,0x230b0170b8200a40b088140ac1d058260202d07c110a00a068130142a0700e0542501c1e0400209c09064120100d0900603c010600303000)]),
  ([4,2,2,0], [(41,0x230a41a0ac2009811088170a01d020190382a05025040050841602c270700703402078130900f010150281b0180c0041200c00)]),
  ([4,3,1,0], [(37,0x1f094170981d08c0f078150901b01c160841c04c22038190141402c1a018110800c00c1206004028010400202000)]),
  ([5,2,1,0], [(33,0x1d084170881b07c11070150801902c1603c1a04c050781002414034180280303807048080040c00806)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_13_313_checked : PLift (checkBox [3,5,13,313] [5,4,2,1] (2,1) p5_13_313_rows = true) := ⟨by decide +kernel⟩

private def p5_13_317_rows : List Witness := [([3,5,1,1], [(64,0x144110dc2512c0b170420e41f1584d058331102a084071603e0d41b0b05212412024400981d00c540503a0c4281380e0143c08819140100d8241280a0041e1300c0c82001834068480201c0083006000),(27,0x4716c2f1744315c171142b1643f0b45304c4109c5e154150ec2913c0f1183d08c5a)]),
  ([4,2,1,1], [(55,0x2f0dc230e42b0cc170b41f0d42702c2104c2906c3a0c41501c1d03c250243604403088190e02a014320580d0b0340980a0042004828068300500607024020100081801000)]),
  ([3,3,2,0], [(45,0x230b0170b8200a40b088140ac1d058260202d07c110a00a068130142a0700e0542501c1e0400209c09064120100d0900603c010600303000)]),
  ([4,2,2,0], [(41,0x230a41a0ac2009811088170a01d020190382a05025040050841602c270700703402078130900f010150281b0180c0041200c00)]),
  ([4,3,1,0], [(37,0x1f094170981d08c0f078150901b01c160841c04c22038190141402c1a018110800c00c1206004028010400202000)]),
  ([5,2,1,0], [(33,0x1d084170881b07c11070150801902c1603c1a04c050781002414034180280303807048080040c00806)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_13_317_checked : PLift (checkBox [3,5,13,317] [5,5,2,1] (2,1) p5_13_317_rows = true) := ⟨by decide +kernel⟩

private def p5_13_331_rows : List Witness := [([3,5,1,1], [(64,0x168110dc250b84b02c5c0e44213456034160cc440842a01c580d43e06c2c12452024120742600c54050310e84e0140e0f01908850040360904a0040a0784c03032080060d01a12008070020c00406000),(27,0x4716c2f1744315c171142b1643f0b45304c4109c55178150ec2913c0f0f44608c51)]),
  ([4,2,1,1], [(55,0x2f0dc230e42b0cc170b41f0d42702c2104c2906c310e81501c1d03c250b80904403064220a8050c80d0582c0783409801028200a01a0c0140181c03824020100600403000)]),
  ([3,3,2,0], [(45,0x230b0170b8200a40b088140ac1d058260202d07c110a00a068130142a0700e0542501c1e0400209c09064120100d0900603c010600303000)]),
  ([4,2,2,0], [(41,0x230a41a0ac2009811088170a01d020190382a05025040050841602c270700703402078130900f010150281b0180c0041200c00)]),
  ([4,3,1,0], [(37,0x1f094170981d08c0f078150901b01c160841c04c22038190141402c1a018110800c00c1206004028010400202000)]),
  ([5,2,1,0], [(33,0x1d084170881b07c11070150801902c1603c1a04c050781002414034180280303807048080040c00806)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_13_331_checked : PLift (checkBox [3,5,13,331] [5,5,2,1] (2,1) p5_13_331_rows = true) := ⟨by decide +kernel⟩

private def p5_13_337_rows : List Witness := [([3,5,1,1], [(64,0x168110dc250b84b02c5c0e44207c4d1580d058330842a01c580d43e06c2c12452024120742600c54050310e828138050383c06422140100d82412801028380780c0c8200181a12008070020c00406000),(27,0x4716c2f1744315c171142b1643f0b45304c4109c55178150ec2913c0f0f44608c51)]),
  ([4,2,1,1], [(55,0x2f0dc230e42b0cc170b41f0d42702c2104c2906c310e81501c1d03c250b80904403064220e02a0140d0582c078340040a080120a01a0c0140181c03824020100600403000)]),
  ([3,3,2,0], [(45,0x230b0170b8200a40b088140ac1d058260202d07c110a00a068130142a0700e0542501c1e0400209c09064120100d0900603c010600303000)]),
  ([4,2,2,0], [(41,0x230a41a0ac2009811088170a01d020190382a05025040050841602c270700703402078130900f010150281b0180c0041200c00)]),
  ([4,3,1,0], [(37,0x1f094170981d08c0f078150901b01c160841c04c22038190141402c1a018110800c00c1206004028010400202000)]),
  ([5,2,1,0], [(33,0x1d084170881b07c11070150801902c1603c1a04c050781002414034180280303807048080040c00806)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_13_337_checked : PLift (checkBox [3,5,13,337] [5,5,2,1] (2,1) p5_13_337_rows = true) := ⟨by decide +kernel⟩

private def p5_13_347_rows : List Witness := [([3,6,1,1], [(64,0x140290c85702c681044a08c341640d0583b130250b807190180f44607c301545e02412120210a803180140e4420b05a0140e07426170100f8281580102840088580303a090060f01e020200083801000),(43,0x531ac371b44f19c1b144331a44b0d46305c4d0bc651b81911c3117c13124520ac611a81510c2d0d85b03c6c1144e09c5d198110683f)]),
  ([4,2,1,1], [(55,0x2f0dc230e42b0cc170b41f0d42702c2104c2906c310e81501c1d03c250b80904403064220e02a01432034160b01e0d0260040a080120a01a0c0140180e090080400201000)]),
  ([3,3,2,0], [(45,0x230b0170b8200a40b088140ac1d058260202d07c110a00a068130142a0700e0542501c1e0400209c09064120100d0900603c010600303000)]),
  ([4,2,2,0], [(41,0x230a41a0ac2009811088170a01d020190382a05025040050841602c270700703402078130900f010150281b0180c0041200c00)]),
  ([4,3,1,0], [(37,0x1f094170981d08c0f078150901b01c160841c04c22038190141402c1a018110800c00c1206004028010400202000)]),
  ([5,2,1,0], [(33,0x1d084170881b07c11070150801902c1603c1a04c050781002414034180280303807048080040c00806)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_13_347_checked : PLift (checkBox [3,5,13,347] [5,6,2,1] (2,1) p5_13_347_rows = true) := ⟨by decide +kernel⟩

private def p5_13_349_rows : List Witness := [([3,6,1,2], [(64,0x1e03d2084b00810270611bc342144e24c13160210dc450289616c241a42e1208d0341b1b0310fc04240550784221c07054660ac39228181743c2040103c600cc84048570d8090b47e03003150060a800),(64,0x2245205ca31a0760ec8c2681a17c281e43e20c4c0449d188700d48613c9405059088730e04602c972945c0946a0bc492380e0706d1ec321000527c5607c6410c8814408058a219c750b03a2641917827),(31,0x7d284532907726c291e84d278711409508c7411c98298261ac4a23c1d1b87c104922802019444)]),
  ([3,7,1,1], [(64,0x68580b4630d80b1241c14827194381b80d10c16150290c8701141813823184341a809048500942e00c6c1041412830198050384c0842a1a0101182c18801028480980c1082801822180080900201020),(57,0x5f1ec3f1f45b1dc1f1743b1e4570f47306c590dc751f81d14c391bc171545e0cc711e81913c351ac3e04c7c1445a0bc6d1d81512c1e1703119c3a03c78134560ac690f07204447)]),
  ([4,2,1,1], [(55,0x2f0dc230e42b0cc170b41f0d42702c2104c2906c310e81501c1d03c250b8090d811064220e02a01432034160b01e098010282004828068140181c03808040020600403000)]),
  ([3,3,2,0], [(45,0x230b0170b8200a40b088140ac1d058260202d07c110a00a068130142a0700e0542501c1e0400209c09064120100d0900603c010600303000)]),
  ([4,2,2,0], [(41,0x230a41a0ac2009811088170a01d020190382a05025040050841602c270700703402078130900f010150281b0180c0041200c00)]),
  ([4,3,1,0], [(37,0x1f094170981d08c0f078150901b01c160841c04c22038190141402c1a018110800c00c1206004028010400202000)]),
  ([5,2,1,0], [(33,0x1d084170881b07c11070150801902c1603c1a04c050781002414034180280303807048080040c00806)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_13_349_checked : PLift (checkBox [3,5,13,349] [5,7,2,2] (2,1) p5_13_349_rows = true) := ⟨by decide +kernel⟩

private def p5_13_353_rows : List Witness := [([4,2,1,1], [(55,0x2f0dc230e42b0cc170b41f0d42702c2104c2906c310543a01c1d03c250242e0443600c220e0050a8320582c0783400426028120a01a0c0140180e09008040020600403000)]),
  ([3,3,2,0], [(45,0x230b0170b8200a40b088140ac1d058260202d07c110a00a068130142a0700e0542501c1e0400209c09064120100d0900603c010600303000)]),
  ([4,2,2,0], [(41,0x230a41a0ac2009811088170a01d020190382a05025040050841602c270700703402078130900f010150281b0180c0041200c00)]),
  ([4,3,1,0], [(37,0x1f094170981d08c0f078150901b01c160841c04c22038190141402c1a018110800c00c1206004028010400202000)]),
  ([5,2,1,0], [(33,0x1d084170881b07c11070150801902c1603c1a04c050781002414034180280303807048080040c00806)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_13_353_checked : PLift (checkBox [3,5,13,353] [5,3,2,1] (2,1) p5_13_353_rows = true) := ⟨by decide +kernel⟩

private def p5_13_359_rows : List Witness := [([4,2,1,1], [(55,0x2f0dc230e42b0cc170b41f0d42702c2104c2906c310543a01c1d03c250242e0443600c220e0050a80d0c8160b01e004260282004828068300500603824020100080403000)]),
  ([3,3,2,0], [(45,0x230b0170b8200a40b088140ac1d058260202d07c110a00a068130142a0700e0542501c1e0400209c09064120100d0900603c010600303000)]),
  ([4,2,2,0], [(41,0x230a41a0ac2009811088170a01d020190382a05025040050841602c270700703402078130900f010150281b0180c0041200c00)]),
  ([4,3,1,0], [(37,0x1f094170981d08c0f078150901b01c160841c04c22038190141402c1a018110800c00c1206004028010400202000)]),
  ([5,2,1,0], [(33,0x1d084170881b07c11070150801902c1603c1a04c050781002414034180280303807048080040c00806)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_13_359_checked : PLift (checkBox [3,5,13,359] [5,3,2,1] (2,1) p5_13_359_rows = true) := ⟨by decide +kernel⟩

private def p5_13_367_rows : List Witness := [([4,2,1,1], [(53,0x2f0dc230e42b0cc170b41f0d42702c2104c2906c310543a01c1d03c250242e0443600c19088050a80d0c8160b01e00426028200481a0c0140181c03808040020100c)]),
  ([3,3,2,0], [(45,0x230b0170b8200a40b088140ac1d058260202d07c110a00a068130142a0700e0542501c1e0400209c09064120100d0900603c010600303000)]),
  ([4,2,2,0], [(41,0x230a41a0ac2009811088170a01d020190382a05025040050841602c270700703402078130900f010150281b0180c0041200c00)]),
  ([4,3,1,0], [(37,0x1f094170981d08c0f078150901b01c160841c04c22038190141402c1a018110800c00c1206004028010400202000)]),
  ([5,2,1,0], [(33,0x1d084170881b07c11070150801902c1603c1a04c050781002414034180280303807048080040c00806)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_13_367_checked : PLift (checkBox [3,5,13,367] [5,3,2,1] (2,1) p5_13_367_rows = true) := ⟨by decide +kernel⟩

private def p5_13_373_rows : List Witness := [([4,2,1,1], [(55,0x2f0dc230e42b0cc170b41f0d42702c2104c2906c310543a01c1d03c250242e0443600c19088380140d0c8160b01e0d0010980a080120a01a0c0140181c038080400206004)]),
  ([3,3,2,0], [(45,0x230b0170b8200a40b088140ac1d058260202d07c110a00a068130142a0700e0542501c1e0400209c09064120100d0900603c010600303000)]),
  ([4,2,2,0], [(41,0x230a41a0ac2009811088170a01d020190382a05025040050841602c270700703402078130900f010150281b0180c0041200c00)]),
  ([4,3,1,0], [(37,0x1f094170981d08c0f078150901b01c160841c04c22038190141402c1a018110800c00c1206004028010400202000)]),
  ([5,2,1,0], [(33,0x1d084170881b07c11070150801902c1603c1a04c050781002414034180280303807048080040c00806)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_13_373_checked : PLift (checkBox [3,5,13,373] [5,3,2,1] (2,1) p5_13_373_rows = true) := ⟨by decide +kernel⟩

private def p5_13_379_rows : List Witness := [([4,2,1,1], [(55,0x2f0dc230e42b0cc170b41f0d42702c2104c2906c310543a01c1d03c250242e0443600c19088380142a034320581e0d0010980a04828068300501c03824020100081803000)]),
  ([3,3,2,0], [(45,0x230b0170b8200a40b088140ac1d058260202d07c110a00a068130142a0700e0542501c1e0400209c09064120100d0900603c010600303000)]),
  ([4,2,2,0], [(41,0x230a41a0ac2009811088170a01d020190382a05025040050841602c270700703402078130900f010150281b0180c0041200c00)]),
  ([4,3,1,0], [(37,0x1f094170981d08c0f078150901b01c160841c04c22038190141402c1a018110800c00c1206004028010400202000)]),
  ([5,2,1,0], [(33,0x1d084170881b07c11070150801902c1603c1a04c050781002414034180280303807048080040c00806)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_13_379_checked : PLift (checkBox [3,5,13,379] [5,3,2,1] (2,1) p5_13_379_rows = true) := ⟨by decide +kernel⟩

private def p5_13_383_rows : List Witness := [([4,2,1,1], [(55,0x2f0dc230e42b0cc170b41f0d42702c2104c2906c310543a01c1d03c250242e0443600c19088380142a034320582c078010980a080120a01a0c0140181c03824020020600c)]),
  ([3,3,2,0], [(45,0x230b0170b8200a40b088140ac1d058260202d07c110a00a068130142a0700e0542501c1e0400209c09064120100d0900603c010600303000)]),
  ([4,2,2,0], [(41,0x230a41a0ac2009811088170a01d020190382a05025040050841602c270700703402078130900f010150281b0180c0041200c00)]),
  ([4,3,1,0], [(37,0x1f094170981d08c0f078150901b01c160841c04c22038190141402c1a018110800c00c1206004028010400202000)]),
  ([5,2,1,0], [(33,0x1d084170881b07c11070150801902c1603c1a04c050781002414034180280303807048080040c00806)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_13_383_checked : PLift (checkBox [3,5,13,383] [5,3,2,1] (2,1) p5_13_383_rows = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_13_key_check : PLift ((∀ s : Fin 388, s.val.Prime → 13 < s.val → s.val ∈ p5_13_keys)) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem p5_13_box (i : Fin 70) :
    ∃ (caps : List ℕ) (rows : List Witness),
      caps.length = 4 ∧ (∀ c ∈ caps, 0 < c) ∧
      checkBox [3,5,13,p5_13_keys[i.val]!] caps (2,1) rows = true := by
  fin_cases i
  · exact ⟨[5,3,2,1], p5_13_17_rows, rfl, by decide, p5_13_17_checked.down⟩
  · exact ⟨[5,3,2,1], p5_13_19_rows, rfl, by decide, p5_13_19_checked.down⟩
  · exact ⟨[5,3,2,2], p5_13_23_rows, rfl, by decide, p5_13_23_checked.down⟩
  · exact ⟨[5,3,2,1], p5_13_29_rows, rfl, by decide, p5_13_29_checked.down⟩
  · exact ⟨[6,3,2,2], p5_13_31_rows, rfl, by decide, p5_13_31_checked.down⟩
  · exact ⟨[6,3,2,2], p5_13_37_rows, rfl, by decide, p5_13_37_checked.down⟩
  · exact ⟨[5,4,3,2], p5_13_41_rows, rfl, by decide, p5_13_41_checked.down⟩
  · exact ⟨[5,5,3,2], p5_13_43_rows, rfl, by decide, p5_13_43_checked.down⟩
  · exact ⟨[5,3,2,1], p5_13_47_rows, rfl, by decide, p5_13_47_checked.down⟩
  · exact ⟨[5,3,2,1], p5_13_53_rows, rfl, by decide, p5_13_53_checked.down⟩
  · exact ⟨[5,3,2,1], p5_13_59_rows, rfl, by decide, p5_13_59_checked.down⟩
  · exact ⟨[5,3,2,1], p5_13_61_rows, rfl, by decide, p5_13_61_checked.down⟩
  · exact ⟨[5,3,2,1], p5_13_67_rows, rfl, by decide, p5_13_67_checked.down⟩
  · exact ⟨[5,3,2,1], p5_13_71_rows, rfl, by decide, p5_13_71_checked.down⟩
  · exact ⟨[5,3,2,1], p5_13_73_rows, rfl, by decide, p5_13_73_checked.down⟩
  · exact ⟨[5,3,2,1], p5_13_79_rows, rfl, by decide, p5_13_79_checked.down⟩
  · exact ⟨[5,3,2,1], p5_13_83_rows, rfl, by decide, p5_13_83_checked.down⟩
  · exact ⟨[5,3,2,1], p5_13_89_rows, rfl, by decide, p5_13_89_checked.down⟩
  · exact ⟨[5,3,2,1], p5_13_97_rows, rfl, by decide, p5_13_97_checked.down⟩
  · exact ⟨[5,3,2,1], p5_13_101_rows, rfl, by decide, p5_13_101_checked.down⟩
  · exact ⟨[5,3,2,1], p5_13_103_rows, rfl, by decide, p5_13_103_checked.down⟩
  · exact ⟨[5,3,2,1], p5_13_107_rows, rfl, by decide, p5_13_107_checked.down⟩
  · exact ⟨[5,3,2,1], p5_13_109_rows, rfl, by decide, p5_13_109_checked.down⟩
  · exact ⟨[5,3,2,1], p5_13_113_rows, rfl, by decide, p5_13_113_checked.down⟩
  · exact ⟨[5,3,2,1], p5_13_127_rows, rfl, by decide, p5_13_127_checked.down⟩
  · exact ⟨[5,3,2,1], p5_13_131_rows, rfl, by decide, p5_13_131_checked.down⟩
  · exact ⟨[5,3,2,1], p5_13_137_rows, rfl, by decide, p5_13_137_checked.down⟩
  · exact ⟨[5,3,2,1], p5_13_139_rows, rfl, by decide, p5_13_139_checked.down⟩
  · exact ⟨[5,3,2,1], p5_13_149_rows, rfl, by decide, p5_13_149_checked.down⟩
  · exact ⟨[5,3,2,1], p5_13_151_rows, rfl, by decide, p5_13_151_checked.down⟩
  · exact ⟨[5,3,2,1], p5_13_157_rows, rfl, by decide, p5_13_157_checked.down⟩
  · exact ⟨[5,3,2,1], p5_13_163_rows, rfl, by decide, p5_13_163_checked.down⟩
  · exact ⟨[5,3,2,1], p5_13_167_rows, rfl, by decide, p5_13_167_checked.down⟩
  · exact ⟨[5,3,2,1], p5_13_173_rows, rfl, by decide, p5_13_173_checked.down⟩
  · exact ⟨[5,3,2,1], p5_13_179_rows, rfl, by decide, p5_13_179_checked.down⟩
  · exact ⟨[5,3,2,1], p5_13_181_rows, rfl, by decide, p5_13_181_checked.down⟩
  · exact ⟨[5,3,3,1], p5_13_191_rows, rfl, by decide, p5_13_191_checked.down⟩
  · exact ⟨[5,3,3,1], p5_13_193_rows, rfl, by decide, p5_13_193_checked.down⟩
  · exact ⟨[5,3,3,1], p5_13_197_rows, rfl, by decide, p5_13_197_checked.down⟩
  · exact ⟨[5,3,3,1], p5_13_199_rows, rfl, by decide, p5_13_199_checked.down⟩
  · exact ⟨[5,3,2,1], p5_13_211_rows, rfl, by decide, p5_13_211_checked.down⟩
  · exact ⟨[5,3,2,1], p5_13_223_rows, rfl, by decide, p5_13_223_checked.down⟩
  · exact ⟨[5,4,2,1], p5_13_227_rows, rfl, by decide, p5_13_227_checked.down⟩
  · exact ⟨[5,4,2,1], p5_13_229_rows, rfl, by decide, p5_13_229_checked.down⟩
  · exact ⟨[5,4,2,1], p5_13_233_rows, rfl, by decide, p5_13_233_checked.down⟩
  · exact ⟨[5,4,2,1], p5_13_239_rows, rfl, by decide, p5_13_239_checked.down⟩
  · exact ⟨[5,4,2,1], p5_13_241_rows, rfl, by decide, p5_13_241_checked.down⟩
  · exact ⟨[5,4,2,1], p5_13_251_rows, rfl, by decide, p5_13_251_checked.down⟩
  · exact ⟨[5,4,2,1], p5_13_257_rows, rfl, by decide, p5_13_257_checked.down⟩
  · exact ⟨[5,4,2,1], p5_13_263_rows, rfl, by decide, p5_13_263_checked.down⟩
  · exact ⟨[5,4,2,1], p5_13_269_rows, rfl, by decide, p5_13_269_checked.down⟩
  · exact ⟨[5,4,2,1], p5_13_271_rows, rfl, by decide, p5_13_271_checked.down⟩
  · exact ⟨[5,4,2,1], p5_13_277_rows, rfl, by decide, p5_13_277_checked.down⟩
  · exact ⟨[5,4,2,1], p5_13_281_rows, rfl, by decide, p5_13_281_checked.down⟩
  · exact ⟨[5,4,2,1], p5_13_283_rows, rfl, by decide, p5_13_283_checked.down⟩
  · exact ⟨[5,4,2,1], p5_13_293_rows, rfl, by decide, p5_13_293_checked.down⟩
  · exact ⟨[5,4,2,1], p5_13_307_rows, rfl, by decide, p5_13_307_checked.down⟩
  · exact ⟨[5,4,2,1], p5_13_311_rows, rfl, by decide, p5_13_311_checked.down⟩
  · exact ⟨[5,4,2,1], p5_13_313_rows, rfl, by decide, p5_13_313_checked.down⟩
  · exact ⟨[5,5,2,1], p5_13_317_rows, rfl, by decide, p5_13_317_checked.down⟩
  · exact ⟨[5,5,2,1], p5_13_331_rows, rfl, by decide, p5_13_331_checked.down⟩
  · exact ⟨[5,5,2,1], p5_13_337_rows, rfl, by decide, p5_13_337_checked.down⟩
  · exact ⟨[5,6,2,1], p5_13_347_rows, rfl, by decide, p5_13_347_checked.down⟩
  · exact ⟨[5,7,2,2], p5_13_349_rows, rfl, by decide, p5_13_349_checked.down⟩
  · exact ⟨[5,3,2,1], p5_13_353_rows, rfl, by decide, p5_13_353_checked.down⟩
  · exact ⟨[5,3,2,1], p5_13_359_rows, rfl, by decide, p5_13_359_checked.down⟩
  · exact ⟨[5,3,2,1], p5_13_367_rows, rfl, by decide, p5_13_367_checked.down⟩
  · exact ⟨[5,3,2,1], p5_13_373_rows, rfl, by decide, p5_13_373_checked.down⟩
  · exact ⟨[5,3,2,1], p5_13_379_rows, rfl, by decide, p5_13_379_checked.down⟩
  · exact ⟨[5,3,2,1], p5_13_383_rows, rfl, by decide, p5_13_383_checked.down⟩

private theorem p5_13_bounded (s a b c d : ℕ)
    (sp : s.Prime) (ordered : 13 < s) (sb : s < 388)
    (ap : 0 < a) (bp : 0 < b) (cp : 0 < c) (dp : 0 < d)
    (high : 2 < indexProduct [3,5,13,s] [a,b,c,d]) :
    ∃ k, k ∣ factorProduct [3,5,13,s] [a,b,c,d] ∧ k.Pseudoperfect := by
  have membership := p5_13_key_check.down ⟨s,sb⟩ sp ordered
  obtain ⟨i, hi, key⟩ := List.mem_iff_getElem.mp membership
  have word := p5_13_box ⟨i,hi⟩
  have ke : p5_13_keys[i]! = s := (getElem!_pos p5_13_keys i hi).trans key
  simp only [ke] at word
  obtain ⟨caps, rows, width, cp', checked⟩ := word
  have ps : ∀ p ∈ [3,5,13,s], 2 ≤ p := by simp [sp.two_le]
  have es : ∀ e ∈ [a,b,c,d], 0 < e := by simp [ap,bp,cp,dp]
  rcases checkBox_sound [3,5,13,s] caps [a,b,c,d] (2,1) rows checked ps es cp'
      rfl width.symm (by decide) with tooSmall | witness
  · exact False.elim ((not_le_of_gt high) (by simpa using tooSmall))
  · exact witness

private theorem p5_13 (s a b c d : ℕ)
    (sp : s.Prime) (ordered : 13 < s)
    (ap : 0 < a) (bp : 0 < b) (cp : 0 < c) (dp : 0 < d)
    (high : 2 < indexProduct [3,5,13,s] [a,b,c,d]) :
    ∃ k, k ∣ factorProduct [3,5,13,s] [a,b,c,d] ∧ k.Pseudoperfect := by
  rcases prefix13 a b c ap bp cp with prefixBound | ⟨k, kd, pp⟩
  · have sb := last_prime_bound 5 13 s a b c d 388 (52514 / 26325 : ℚ)
      (by decide) (by norm_num) (by norm_num [ceiling]) prefixBound high
    exact p5_13_bounded s a b c d sp ordered sb ap bp cp dp high
  · exact ⟨k,kd.trans (factor_prefix_dvd 5 13 s a b c d),pp⟩

private def p5_17_keys : List ℕ := [19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199,211,223,227,229,233,239,241,251]

private def p5_17_19_rows : List Witness := [([2,2,1,2], [(49,0x230bc11074320d02902c20088170b02e038100141a070310cc260a00a07c21050160ac2d0340f0080406c300942701c09078130542a004030600604800)]),
  ([2,2,2,1], [(49,0x230bc11074330d02902c21088170b42e03c100141b070310c8280240a07c20054160ac2c0380301019068300942601c1e04c140a80c004020602401800)]),
  ([2,3,1,1], [(43,0x1f0ac0f06c2d0b82702c1d078170a42a0340e01c190682c04c250980902803054160a0210880c014060601104808004020502001000)]),
  ([3,2,1,1], [(43,0x230ac1707c2d0b80b04c210881b0a42a0541603c1d0782c094090980a00c11048200641a0a005018140340e07024020010081003000)]),
  ([4,1,1,2], [(55,0x2f0d4230a4380e8170742c0b80b0c83404420088260a039014140581a0702b0b408028310cc0e0401f0842509c360080404c1506c2a01c090c00f07824004030600603000)]),
  ([4,1,2,1], [(53,0x2f0d4230a4390e8170742d0b80b0cc3404421088280dc38014150581b0702b0b0090c40a0c81007c20094260d803010130501a0a807020300381e090010081201800)]),
  ([5,1,1,1], [(45,0x270ac1f08c2d0b81706c250980f0a42a04c1d078070842202c15058190682400c0d0382804412014060800902814060010080c0400402000)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_17_19_checked : PLift (checkBox [3,5,17,19] [5,3,2,2] (2,1) p5_17_19_rows = true) := ⟨by decide +kernel⟩

private def p5_17_23_rows : List Witness := [([2,3,2,2], [(64,0x13c1f03838084100e829190530f02b1985515c16014400bc1801c420c45b128331744c0700b1381e034370980f0e42818c5215013008150103f0b8060c05a1244b0280c0d82509c510480100c2d12024),(37,0x47188230f8681a859068441183517c6114020088110ec650f42c19c561a41710419020430c85c114341784d07460)]),
  ([2,4,2,1], [(64,0x1584b13041054370580b0e02d0b82314045064460680f0c4100143209c54124281283f04c14024360ac0a0b02113843088440600d038030c025010261203d0f81201c0807c201080c004020903c01800),(21,0x3b14c1d0d4571604d05c390e82f1445211c1b070110cc550d029)]),
  ([3,2,1,1], [(43,0x230ac1707c2d0b82702c210881b0a42a0541603c1d0782c094090980a00c11048200641a0a005018140340e0702402001008100100c)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_17_23_checked : PLift (checkBox [3,5,17,23] [3,4,2,2] (2,1) p5_17_23_rows = true) := ⟨by decide +kernel⟩

private def p5_17_29_rows : List Witness := [([3,2,1,1], [(45,0x230ac1707c2d09c0b0b8130841b088070a81503c1d05825078090b00309811028190482006805034060500e0700109008008100600403000)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_17_29_checked : PLift (checkBox [3,5,17,29] [3,2,1,1] (2,1) p5_17_29_rows = true) := ⟨by decide +kernel⟩

private def p5_17_31_rows : List Witness := [([3,2,1,1], [(45,0x230ac1707c2d09c0b0b8130841b0a4220542a03c1d058250241e0b00304426028190482006828034060500e0700109008008100600403000)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_17_31_checked : PLift (checkBox [3,5,17,31] [3,2,1,1] (2,1) p5_17_31_rows = true) := ⟨by decide +kernel⟩

private def p5_17_37_rows : List Witness := [([3,2,2,1], [(64,0x104230bc450ec111181d0cc290fc3402c211001710c220e40f0b8440141b0c43a040270f41c0c80907c280f82b028200dc0d0582c1080306438038250101a0c0070983c04c1e0502a004360300206006),(1,0x35)]),
  ([3,3,1,1], [(59,0x2f0ec1f0ac3d0dc0f0f81b0b4270e43302c1d0e8170a41e08c350342a0f0190d80e04c250682c0c4090983800c150c80a07021058280142203011018180482400430020020502004000)]),
  ([4,2,1,1], [(55,0x2f0dc230ac390cc170e81f0b40b0d42e04c210d81b0a42201c310542a0e00f07432058090782c00c110980a0d0190480506828034060c0140381c00408008100600403000)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_17_37_checked : PLift (checkBox [3,5,17,37] [4,3,2,1] (2,1) p5_17_37_rows = true) := ⟨by decide +kernel⟩

private def p5_17_41_rows : List Witness := [([3,2,2,2], [(64,0x104100c45305060088430146409833154160e04501c660a04902c570603a16c1d12c0d0b83c1741f1000203c301481308442010630945405437018271200a0e45a0702d078011441200c240d80906c00),(39,0x501883511c681641a1a82c1343e17c4f0443218423110650d05605c46020670a44a160190ec5c1a42b1300e0bc3d17820)]),
  ([3,3,1,1], [(59,0x2f0ec1f0ac3d0dc0f0f81b0b4270e42e0cc0b074170a41e08c350342a01c3c06436038130941a0c409098030e0150c80a0702105828014220d00c044180482400430020020502004000)]),
  ([4,2,1,1], [(55,0x2f0dc230ac390cc170e81f0b42702c3504c210d81b0a42201c310542a03c380741609409078030b0110980a0d019048200141a0a00d018300501c00424020020401801000)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_17_41_checked : PLift (checkBox [3,5,17,41] [4,3,2,2] (2,1) p5_17_41_rows = true) := ⟨by decide +kernel⟩

private def p5_17_43_rows : List Witness := [([3,3,1,1], [(59,0x2f0ec1f0ac3d0dc0f0f81b0b4270e4330b80b0743a05c29078350342a01c3c0643604c0e0941a0b009098030e0150c80a0841c05828014220d011030180482400430020020502004000)]),
  ([4,2,1,1], [(53,0x2f0dc230ac390cc170e81f0b42702c350b8130d81b0a42201c310542a03c3807432058250241e00c2c0440a0d019048200141a0a00d0c0140381c00424020100600c)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_17_43_checked : PLift (checkBox [3,5,17,43] [4,3,1,1] (2,1) p5_17_43_rows = true) := ⟨by decide +kernel⟩

private def p5_17_47_rows : List Witness := [([3,3,1,2], [(64,0x985b07452058380a04a1740e10c050e820154100c8450ac2215c080f4340682d13c130283f0945a07051008150dc49034420103907c5403c310a82101c3c0644e048090901b00436030030783001800),(25,0x471642f1045c14c170a45e1103b1584d044460b0231603e0d42e1401402c40)]),
  ([3,3,2,1], [(64,0x1704307452058391542812c0f1102b0143a084560f44c040330b04f04c220243e1683406c5005037028261240d1081c00c3807c541280e0c42a0102001c3c0644e048080901a00436030020c00606000),(25,0x471642f1045d14c170a45e1143b15c4d044460b4580fc5b0d42e1441502c40)]),
  ([3,4,1,1], [(64,0x1244303c3a0941f128350bc261141102c360844c06c46048310ac221040d0e0070c84805c420382d0901e0f4090d0030b819110100f80a0a420068050c02a0544003006070160042c0f0080081801000),(11,0x3b12c270dc4d11c1308c4e0e433)]),
  ([4,2,1,1], [(53,0x2f0dc230ac390cc1707c3a0b42702c3504c2e0841b0d829088310540f0a81d0e032058250241e0442c0980a06434048050801a034280c01403801070080081006000)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_17_47_checked : PLift (checkBox [3,5,17,47] [4,4,2,2] (2,1) p5_17_47_rows = true) := ⟨by decide +kernel⟩

private def p5_17_53_rows : List Witness := [([3,3,2,1], [(64,0x9c4010c5c0e4520585512c0f0a02b110050843a0f4561301013c130b009088250f85a0d037140140284903426108030701f0e0540c44a0382a010070803c0c84e048080900106848030020783001800),(25,0x471642f1045d14c170a4451783b15c4d0442d118230fc5816c35144150b80b)]),
  ([4,2,2,1], [(64,0x843405c2d10043158391300f0884f0141b0b84409c3a0403d140090704907c32054280ac3e1500a0dc4a0342000c160642c108250e04e010070683004c260f0081201e004140a836008180900604800),(21,0x4714c3510457134230bc451603b04451074331183f1485502c4b)]),
  ([4,3,1,1], [(64,0x1383703c4906c2d0f8270e44a02c450742e05c290e84c08c351180d078410642a0f01309436038480c4420241a0b003054260e0210c80a0700505828044220d00c0184006001048240c0080081408004),(9,0x3f12c2f0ec4d11c1f0ac3d)]),
  ([5,2,1,1], [(64,0xfc230ac391183305c4107c2d0e82702c3504c3d0842e06c290d84401c310f8150880f0742a0e0250c8090584000c110782c0642602834014120800d0682801830050010381c09008008100600403000),(5,0x3b10c2f0dc45)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_17_53_checked : PLift (checkBox [3,5,17,53] [5,3,2,1] (2,1) p5_17_53_rows = true) := ⟨by decide +kernel⟩

private def p5_17_59_rows : List Witness := [([3,4,2,2], [(64,0x58491140b01cab0e86d1a49c09c2f178912341c0604b1f80d1003c1bc02288311906024c1e1441303c421d4040dc33198990905b228151200a018391b02e2401b0303f0043018c87048030d8090b400),(64,0x298351a09b25c26088552108c05c4a11879020ac2a03b1b86a2742815c5f2488e074191fc7b038ae1043d1c0a327c2a0c8651849407c521388122414040431d872014a50e03419c9a25825084541708b),(45,0x862a8591f4b02842c140832c87429c9808c56214471e8ad2a46b278291608f0684d2007c2bc3e1c4a42802b1889514c4f208112c4441dc73)]),
  ([3,4,3,1], [(64,0x1043c1a805260330b8611708a088532047c064141087002c060e434188900ac542081a120790440c0e86800c310b05a220201447a04840024040c8600a45220018028380042a1e01000830140080a000),(64,0x1cc6e27037194932382615c850744b1187403c6b198992502f1748b218230784c1f41510c3e1c46c01c9a0d4631789123024154831f81b0584911072034361a4642482d16c56224840841c1287b04c0e),(27,0x7725c4f1bc9d23c2711c75278672548707c4d1d83f1b49b2585f234251387f05c45)]),
  ([3,5,2,1], [(64,0x1bc0f0dc34170052102d154521e81a1084b1cc7004c100e060024310b8561f82713c4c1d0140f06d0340a0c85a00c2b0a0501e0181246e0383601c040b05409472048080c0010984e1b00c0a84809000),(64,0x2385f21c7d074451a83b18c8b22059204211187705c3f19c6423035174852082214c7b06c401a071044391845e2182f15c7f1f01f07044134750543d0e86202c8a0cc5b1608008029144791d8190583e),(9,0x6b224471948d20c2310469)]),
  ([4,2,2,1], [(64,0x12c210d0170b4431003903c4f130220141b0c42e110270f43a040500244907c1c0c8150ac28150370340a1282000c190582c108250e00e138070101a0c013098081201e004140a836030020900604800),(21,0x4714c3510457134230bc451603b0445107433118290fc551480b)]),
  ([4,3,1,1], [(64,0x3c4910c2d0f8270e44a0cc0b1141d0b8170a43a130230d40d1181e01c410642a0f01309436038480c4091081a0b003054260e0210c80a1101c014160a011088340304006001048240c0080502001000),(11,0x3f12c2f0ec4d11c1f0ac3d13837)]),
  ([5,2,1,1], [(64,0xfc230ac391183305c4107c2d0e82702c35108130f4210b81b0a436110070c4150f82203c1d0a838094090c816100030441e0b0190980a0d0050f0200341a0a0060c0140040e07024020020600403000),(5,0x3b10c2f0dc45)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_17_59_checked : PLift (checkBox [3,5,17,59] [5,5,3,2] (2,1) p5_17_59_rows = true) := ⟨by decide +kernel⟩

private def p5_17_61_rows : List Witness := [([3,5,3,2], [(64,0x160512a4a23cc4a0cc84250e5378250786f3001002461168ab008fc0f04c2749639c271e0d9064122d0041544e27cf00c09136c1b1b00d018572a04924ce40900f1800112c9c3601800c542400c12000),(64,0x214951f8e633cdf0981f1c069304ba0440a42c6216cac294f60f44d0d89e21c973a0e10a0211e472368c30681345064174b52b8053fc560fc4f280993c4ea0c42a2487b330dc070151b4662dc0e01d08),(64,0x43105170452b4a63f8f70f837260813a4d2388290887a1ccc42f4144550e1945e2d8af400f9100500e4a12289a3c8eb0c82b1f075334dd3181d059171b8672e0b10210940859108522a8a33d0ed0d02d),(64,0x344ca46c6b2f10d4184629cf80e089208d338c23474743151643c5f2c1013e8410e88b26cec3542c1f476338c705d18444682e4b24290310c532908d3d4ee0d42e2187f340e032420468711a8c22ec0b),(27,0xd744c8f32d1c41c4720cd4478bf440fb0ec8c3587732119448b341044238ef0bc80)]),
  ([4,2,2,2], [(64,0x10c64180810e055058761c83301c28124451981d0e85b15c181e00d1b42e0a84b0081f1003c1747e04c0f1bc30010250844218c37150151d40a018271201c0e45a0306c0b4010fc51048030900906c00),(64,0x1f450188831d03511c68214590687a0b04d1a83e17c801f0111c43213c231106518482158171dc730d0291284619c840ec5c160191e40e1b82f0ac4c1a4201043d1787f1ec53050101c0311380509822),(1,0x6b)]),
  ([4,2,3,1], [(64,0xd8591507212c131a40e1900508c1e1043c168331444c0506a02c61018290904206c390d0521c0490440c1882a00c210703a16031128121a00901022064321400a180280041a0e048040020c00806000),(51,0x5f1bc4715c7519c2f0fc5d1d84f05c6d09c4517837154731b80f1942d1181f0f45b15874134151ac660b807094430f83514c4e1c4161b00d18c2b098440743b)]),
  ([4,3,1,1], [(64,0x3c4910c1b0b4270e44a0cc0b1141d0b8170a43a130230344607807104190a83c04c250d80e12031024420682c00c15098210c80a1101c014160a011088340300606001048240c008008140800404000),(11,0x3f12c2f0ec4d11c1f0ac3d13837)]),
  ([5,2,2,1], [(64,0x1583903c4f130221880506c5b0c42e110270f43a04050198091241f0705c0c8150ac280f8370340a1282018003064160b042094380384e01c040685a0c0130983c02048078010a836030020602404800),(39,0x591944714c6917c35104571a84d08c630bc450ec11144671901d17433118290fc551486802c4b084611783405c2d10c40)]),
  ([6,2,1,1], [(64,0x1183305c411381f1242d0e82702c351085004c3d1282e06c290d84401c310543e0884c03c1d0a838094090c81610011078480b0190980a0d0050483c0800d0682801830050010381c09008008180100c),(15,0x4713c3b10c5112c2f0dc451483f08c4d0ac39)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_17_61_checked : PLift (checkBox [3,5,17,61] [6,5,3,2] (2,1) p5_17_61_rows = true) := ⟨by decide +kernel⟩

private def p5_17_67_rows : List Witness := [([4,3,1,1], [(64,0x3c4910c1b0b43e09c390cc0b1141d0b8170a43a08c4c0d40d1181e01c410a8130f0250d80e1203102442068030b0150983808432028440700505828044220d00c0184006001048240c0080080404000),(11,0x3f12c2f0ec4d11c1f0ac3d13837)]),
  ([5,2,2,1], [(64,0x1583903c4f130221880506c5b0c44409c3d0e810140660244907c1c170320542b0a03e150370340a12820180030642c108250e00e138070101a1683004c260f0081201e004140a836030180900604800),(39,0x591944714c6917c35104571a84d08c630bc451603b0445119c6417433118290fc551486802c4b084611783405c2d10c40)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_17_67_checked : PLift (checkBox [3,5,17,67] [5,3,2,1] (2,1) p5_17_67_rows = true) := ⟨by decide +kernel⟩

private def p5_17_71_rows : List Witness := [([4,3,1,1], [(64,0x3c4910c1b0b43e09c391283302c45074170a43a08c4c0d40d1181e01c410642a04c3c0940e1203102442068030b0150983808432028440700505828044220d006100180041209030020020502001010),(11,0x3f12c2f0ec4d11c1f0ac3d13837)]),
  ([5,2,2,1], [(64,0x10c401583903c4f130221880506c5b0c42e09c3d0e810140660244907c1c170320542b0a03e150370340a12820180030642c108250e00e138070101a1683004c260f0081201e0042a0d80c0602401812),(37,0x591944714c6917c35104571a84d08c630bc451603b0445119c640745d0cc460a43f1545202c4b084611783405c2d)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_17_71_checked : PLift (checkBox [3,5,17,71] [5,3,2,1] (2,1) p5_17_71_rows = true) := ⟨by decide +kernel⟩

private def p5_17_73_rows : List Witness := [([4,3,1,1], [(64,0x3c4910c1b0b43e09c391283302c450742e05c2908c4c0d40d1181e01c410642a04c3c09436038480c4091081a00c2c0983808432028440700505828044220d00c0184006001048240c0080081401000),(11,0x3f12c2f0ec4d11c1f0ac3d13837)]),
  ([5,2,2,1], [(64,0x100560e40f13c4c0886206c5b0c42e110270f43a04050024661241f0705c0c8150ac280f8540dc0d0284a08003180190582c108250e00e138070105a0c0130983c02048078010502a0d80c0081801812),(39,0x591944714c6917c35104571a84d08c630bc451603b0445119c640745d0cc460a43f1545202c6812c211845e0d0170b443)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_17_73_checked : PLift (checkBox [3,5,17,73] [5,3,2,1] (2,1) p5_17_73_rows = true) := ⟨by decide +kernel⟩

private def p5_17_79_rows : List Witness := [([4,3,2,1], [(64,0x1b8670ac6401428084440f43a0cc5613c7204c4c04068024610b0250881b0f83716834140490506c0340a188030981f1081c0e0311504a0386601c2a080190f0321381202060004240d8480301e0c006),(47,0x5f1c447164751ac2f1045d14c7605c6f194291145e15c7313470044690b4231183f16c58144740546d1a80b18c2e09c43074400e45c1545212c16)]),
  ([4,4,1,1], [(64,0x443f1680b154260841b0d8311302b118410485c0345601c510881d0e0170c82d120420f40e1600914803078190d02e0a4440403e0285401420068150c02a1000c14001070160b03c020020602805000),(31,0x4f17c3b12c6116c270dc4d11c6204c5d15c230e4331384910c5e03c59094530e8350bc4a11460)]),
  ([5,3,1,1], [(64,0x2c451701d158171442e0a4230e8351300d118071041e16019148130a8250f0360c40e1200910803068540542c098210e0320280507016140110a0220d00c0184000418048240c008008140800404000),(29,0x4f16c3f12c5d15c2f0ec4d11c5e07c5914c2b0f44e03c4910c5a06c550b4270f8390cc4a)]),
  ([6,2,2,2], [(64,0x1c3324c282201d2d049114a50e86616c57060780346d008990b82a2281f12cab1003c174521f8131bc040c09009421108a20dc63150151d40a09c87070480e45a030010b41e0fc51048030d80906c00),(64,0x18456208171dc730209f0d0940a4892d44a2c4462983b19c5c16084064790386e2682f0ac8b080b7130ac104a80f469178531fc141ec101c005270312442623422138ae10ca30e064180810587602c72),(53,0xa12cc86260b92a86b1f49e23cbb140b0188831d0a00d4952d8b211ca71a0592141a1e89b25c2c230b8134ad2a43e1a85f2007c044710c892238232e84f2bc4429065)]),
  ([6,2,3,1], [(64,0x38640142c208231e4a01041e0f0920cc51130141a80b184880a4060907a06c42260390d052124700440c188030a8800841c0e8900c458048680240408878064400c850180010a01a0e0100082006000),(64,0x1f4a41149b25837178551cc0f1948c0b4832847e07c462703d24c5b1584d1d0151ac89198070b8840947b10c990f8940d45c14c71138161b00d18c8a0ac810987c074442683b244590d85412c7204c69),(31,0x8f27c7721ca525c5f1bc8d1fca611c9d15c7519c8e0bc8528c9e0fc951744f1d8171b48b21827)]),
  ([7,2,2,1], [(64,0x14221881b16c780c42e1b827110840f43a04050024491981f0705c054321c82b0a03e1f8371500d0284a00c60064160b06c094420e00e138070101a168130c0260f00812001078140a80c0081804800),(64,0x1c48e11c8714c6917c7c0d47522c881048115c4d1a82318c791d82f1bc8c114850ec580445119c640745d1e8331cc700a4462183f1fc551480b12c6808461178170d0740b48a10c40200391580f13c4c),(9,0x7d2246b1dc8d20c591947b)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_17_79_checked : PLift (checkBox [3,5,17,79] [7,4,3,2] (2,1) p5_17_79_rows = true) := ⟨by decide +kernel⟩

private def p5_17_83_rows : List Witness := [([4,3,2,1], [(64,0x19c2b014640a0211103d0e8331584f04c7213010024681842c0941b0f83716834140490500d1b00a00c620981f1081c0e0311504a01c660a804080190f03213812020011802406836030020783001818),(49,0x5f1c447164751ac2f1045d14c171d86f194291143b15c73134111c0690b4231183f16c3516051054741b40b1a8630b82710c1d100391545212c1603c6e)]),
  ([4,4,1,1], [(64,0x44600fc0b16855098210d8311302b118410480d17007158510881d0e0170c82d120420f40e02458090031481e064340b829110100280515020068150c02a0300600450070160b03c020020602801000),(31,0x4f17c3b12c6116c270dc4d11c131885d15c230e4331384910c0f178590945307c3a0d42f12845)]),
  ([5,3,1,1], [(64,0xb4270f8390cc0b128450745c158510b82908c3a0d40d130071184107819160131482a094360c40e0244800c42068151502c098210e032028051101c044500a0220d00c0180110018090300201408004),(23,0x4f16c3f12c5d15c2f0ec4d11c1f1785914c2b0f43703c4e1241b16855)]),
  ([7,2,3,2], [(64,0x98c32d4613c02d1684c36c871e5081c81e0400227c910f4cc024360a0b718c553904e1ec6d3f0192a00424c3f0c4c00a857124d82106f06c0d27033094b41804b1e0012403c09c541b0030c04803024),(64,0x45d091cd0207c112b8a02483e3340a264450dc29318b8190563cce51744f3788a1f06e42cfd068a908413014a2250400c8cf304390acba19858128e736485450511f8703fc1c038ab2741501c9610834),(64,0x194f43985e140ed37c8b1f51a430fe2a87641422050b128c95104d03083a0b0c92ec67164f63a0da21915148e12347f1c50e4001d2b09e058082949710c35348c42d8623c42e2f46916c4d3a8dc2207a),(64,0x2c09b11cd6320f517cee3808c46d0d1dd0608cb2290d10ecca2f0683dce9458533888e2011d43d012b41729898110d3314f20bcbe1a85c3e4eb374894610a2087444503080af284ce02c460e0d531cb9),(23,0xfb44cd73bd1c41cb332cf838c8f4791029cd42fc6b3e8ec4648344904)]),
  ([9,2,3,1], [(64,0x1e4d8104a00783c0cc92168512c04c0500b1a861300292200606c7a1083926034148492a0111c00c00c620a8212001c0e83124058128091a004088191e0400c850028011802806838040020800806000),(64,0x24c5b2e8b11584d2b0151d06b328c1224e81982e094841ecda10ca22643e0d494170532c8a91c4d0138160346c18cc20ac8a204e00747c1103b26891164b80d85412caa04c721a4c8038051902c08c82),(64,0x15cb62b475350cb3a4673182f23885390db28c3f27895174bc2ccd113cae05c761b4cc30c8b3a8e109c861f4dc114a426cb90dc96178552d0ab1ccd23240f1b8653102d23083388d92841f1f8460f49c),(41,0xd739cbf33ced37ca72dcd531c8f3b8e527cbd2bc77358cd3ac87398dd2949717cbe2d4d31bcce3148d3b0e31fcde11ca6274bb)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_17_83_checked : PLift (checkBox [3,5,17,83] [9,4,3,2] (2,1) p5_17_83_rows = true) := ⟨by decide +kernel⟩

private def p5_17_89_rows : List Witness := [([4,3,2,1], [(64,0x58671b82b01464084280f4440cc3a13c5604c7202410184680942c06c220dc3e1683412450034141b00a1881f09842070310e054128071982a010190803c0c84e04801020600901a0d8480300207806),(47,0x5f1c447164751ac2f1045d14c171bc76194291143b15c5e1cc4d1a4700b4230fc4616c35144580546d1d00b18c6a09c2e10c1d0e4401545c1480f)]),
  ([5,3,1,1], [(64,0xcc0b1144a0745c05c51158290b8230d43a0344c01c460641e16013148250a83c0c4360240e1200310815068540b021098380c8050284407011058500a0220d00c004061001804824020020500404000),(27,0x4f16c3f12c5d15c2f0ec4d11c1f1645e14c2b0f43703c491384306c551682d0e43e)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_17_89_checked : PLift (checkBox [3,5,17,89] [5,3,2,1] (2,1) p5_17_89_rows = true) := ⟨by decide +kernel⟩

private def p5_17_97_rows : List Witness := [([4,3,2,1], [(64,0xac161b805084640f4281103313c3a158720246113025040680b01b0dc220f85a12434034500506c00c1f02862098420c41c0e05401c4a038660a8040803c0c84e0480102060090361200c0081e0c006),(49,0x5f1c447164751ac2f1045d14c171bc76194291143b15c731784d044690b47008c3f16c460d4151b4581d00b18c271a8430b81d0e4551005c12c0f19c52)]),
  ([5,3,1,2], [(64,0x1301019c2b1bc8a068221e43d204450d04f04c571c802184251a42d2101c0dc7b0fc5a1240d144151b00407c6309c7e108310e45401c4b03c660a8211e03c0cc4e04801024600901b0d8480301e0c018),(64,0x1ac2f2188e1f4411705305c6e1d8650a480110880ec561784d044680b07022c231e83e208460d450050581cc0b188261a82e2148d074381f04016c4a038520586d1d405080640a07f10c870c83a17408),(9,0x772245f1c48c20c4716474)]),
  ([5,4,1,1], [(64,0x1c01b194311a8361302b1040d11812170071441d158221b03805c2d198480f4091080e1602400c191481e1a0340a42e110100143e0285408015068640c02a1000101850070160b03c020020602801014),(51,0x631cc4f17c751bc3b12c6116c271c4761ac371344704c5d1885708c391c8670cc491384303c590945e1d05307c690d46e0e82f11411128600fc0b1542116826)]),
  ([6,3,1,1], [(64,0x1285c05c511582e1a0230d4620343a13007104191181e16013094520a8640f031024360384800c15068540b021098600e0050c80a1101c0441614028088340300101840060120c008008140800404000),(43,0x5f1ac4f16c6d19c3f12c5d15c2f1a46e18c3b1344707c59178530ac650f46a03c491384306c550b45a1b027184391983e0cc0b1141d)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_17_97_checked : PLift (checkBox [3,5,17,97] [6,4,2,2] (2,1) p5_17_97_rows = true) := ⟨by decide +kernel⟩

private def p5_17_101_rows : List Witness := [([4,3,2,1], [(64,0x586e014211903d0a0440cc4f0e813158720246113025040680b0370883e168490d00d140141b00307c0a1882610831070381504a038660a819010200f04e04801020600901a0d848030020783006000),(51,0x5f1c447164751ac2f1045d14c171bc76194291143b15c731784d044690b47008c3f16c460d4510546d1607402c6309c6a10c2e07439154401704b03c671482b)]),
  ([5,4,1,1], [(64,0x1c01b194311a84c0ac41034460485c01c51074560886c0e0170b4660c8480f4091080e1602400c191481e0d0290b844040050f80a150200541a190300a8400300101850070160b03c020020600405000),(51,0x631cc4f17c751bc3b12c6116c271c4761ac371344704c5d1885708c6d0e47219c491384303c590945e1d05307c690d46e0e82f11411128600fc0b1542116826)]),
  ([6,3,1,1], [(64,0x1285c05c510a4560b86808c35034620e84c01c41064460785804c251482a1903c0c4090d80e1200305442068540b021098600e0320284407011058500a03403001018400601209030020020502004000),(43,0x5f1ac4f16c6d19c3f12c5d15c2f1a46e18c3b1344707c59178530ac650f46a0dc0f1244e10c550b45a1b027184391983e0cc0b1141d)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_17_101_checked : PLift (checkBox [3,5,17,101] [6,4,2,1] (2,1) p5_17_101_rows = true) := ⟨by decide +kernel⟩

private def p5_17_103_rows : List Witness := [([4,3,3,1], [(64,0x3884144341684309869130191c89802c81190310508a0e8230182c14878184440446a0689000c29030820c858104241287002462048880e0210102a140421a018028800c02212060040281000808000),(64,0x1ec5e11c6d074931d89c03c850d48e16c3e09c4d1cc562647c1941522c6e0ec1e250070b48614c361e45c1146b1381b244742680d20c660cc16230590944b0b8711507a18c4604c891b039070920142b),(27,0x7f25c5f1dc9d23c3f15c7d1bc1f2549e21c371744f1d49b1f86705c8d0f4960bc55)]),
  ([4,4,2,1], [(64,0x1242e140720fc61118131a01a228091e45e0ac10200321502110c281286c16c4003462050840d8030287a0b04e0f42211066060071700e1f83007c04098480f8600480102078080421680c008240f000),(64,0x15c4d1bc911d86505c872387d0bc511cc5811c6906c8b1c09217c1120433220550e82912c6d1487410463054851a8370708c02c7b0b48213c341582311467130191b8901740f1fc640c4160e00509c7c),(15,0x7723c591c4932243b14c751ac1d2349420c35)]),
  ([5,3,2,1], [(64,0xf428200440cc4f0e813158721844c094101a02c2101b0dc221e83e168490d00d140141b00307c0a188261083107038150071280e1982a06404080780f032138120040818024068480301e0c00606000),(64,0x1ac2f21c8e1f441174171bc8b1d8650a481114880ec571cc5e134111a42d1c08c08c7b0fc8216c460d4510546d1607402c6309c7f1a8430b886074391f0551005c12c0f19c520ac161b88a014211e464),(9,0x772245f1c48d20c4716475)]),
  ([5,4,1,1], [(64,0x1c0650c46a0d84c0ac41034460485c01c51074560886c0e0170b4660c8480f4091080e1602400c191481e1a0340a42e110100143e0285408015190300a8400300101850070160b03c020020602801000),(51,0x631cc4f17c751bc3b12c6116c271c4761ac371344704c5d1885708c6d0e47219c331244303c590945e1d05307c690d46e0e82f11411128600fc0b1542116826)]),
  ([6,3,1,1], [(64,0x1285c05c510a4560b86808c35034620e84c01c41064460785804c251482a1903c0c4090d80e120031081a1502c0842618038014320284407011058500a03403001018400601209030020020502001000),(43,0x5f1ac4f16c6d19c3f12c5d15c2f1a46e18c3b1344707c59178530ac650f46a0dc0f1244e10c1b1542d1686c09c611983e0cc0b1141d)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_17_103_checked : PLift (checkBox [3,5,17,103] [6,4,3,1] (2,1) p5_17_103_rows = true) := ⟨by decide +kernel⟩

private def p5_17_107_rows : List Witness := [([4,4,2,1], [(64,0xb8501c83f18413118680688a024790ac5e040800c854084430a04a1b05b03440188840d8030940a1e82c1383d088441981801c5c0387e0c01f010261203e18012004081e02a1085a030020903c07800),(64,0x1bc911d86505c870e48e1f4511cc5811c6906c8b1c09217c1120433154880e82912c6d1487410463054850dc6a0708c02c7b0b44f2083415823114670644c1b8901740f1fc311901621838014271247c),(17,0x7723c591c4932243b14c751ac1d2349420c3515c4d)]),
  ([5,3,2,1], [(64,0x19028200440cc4f0e8561c80918425130101a02c2101b0dc221e83e1684903434140141b00307c0a188261f84207038150071280e1982a06404080780f03213812004081802406836120020780606000),(64,0x1ac2f21c8e1f441174531bc8b1d8650a481114880ec571cc5e134111a42d21470230231ec3f16c82118510546d1607402c6309c7f10c6a0b886074391547c1005c12c0f19c2b148161b805228211e43d),(9,0x772245f1c48d20c4716475)]),
  ([5,4,1,1], [(64,0x1c01b194311a8361302b1040d11812170071441d1586c0e0170b4660c8480f4091080e1602400c191481e1a0340a42e110100143e0285408015068640c02a1000c00406070160b03c020020a00405000),(51,0x631cc4f17c751bc3b12c6116c271c4761ac371344704c5d1885708c6d0e47219c331244e10c0f164251787414c1f1a46e0e82f11411128600fc0b1542116826)]),
  ([7,3,1,1], [(64,0x5c510a4561a0230d40d1883a1d04c01c41064460785804c251482a1903c0c4090d8700384800c151081a15021098600e0050c80a1101c0441614028088340300101818048240c008008140800404000),(59,0x6f1ec5f1ac7d1dc4f16c6d19c3f1e47e1cc4b174570bc691b8630ec751347a11c1f1645e14c2b1943d1a87c0dc7103c491d84e06c550b45a1b027184391983e1e03302c45074721285c)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_17_107_checked : PLift (checkBox [3,5,17,107] [7,4,2,1] (2,1) p5_17_107_rows = true) := ⟨by decide +kernel⟩

private def p5_17_109_rows : List Witness := [([4,4,2,1], [(64,0x1f02e140720fc6104c461a01a228091e42b17810200321502110c281286c16c0d10062050840d8030287a0b04e0f42211066060071700e1f83007c040984818012004081e02a08042030020903c07800),(64,0x15c4d1bc911d86505c870e48e1f42f1447311c6906c8b1c09217c1120433154880e82912c6d1487410463054850dc1c2300b1ec2d13c820d05608c4519c191306e2405d03c7f0c464058860e00509c49),(15,0x7723c591c4932243b14c751ac1d2349420c35)]),
  ([5,3,2,1], [(64,0x200440cc4f04c3a15872024610944c040680b08406c370887a0f85a1240d0d0500506c00c1f028620987e1083107038150071280e1982a06404080780f03213812004600901a0d848030020c00606000),(64,0x21c8e1f4411745305c8b1d8650a481114880ec571cc5e134111a42d21470230231ec3f16c8211835144151b4581d06309c7f10c6a0b886074391547c1005c12c0f19c2b148161b805228211e43d19028),(11,0x772245f1c48d20c47164751ac2f)]),
  ([5,4,1,1], [(64,0x1c01b194311a8361302b1040d11812170071441d158221b03805c2d198321203d0244203858090031481e1a0340a42e110100143e0285408015068640c02a1000c004061401c0b03c020020600405000),(51,0x631cc4f17c751bc3b12c6116c271c4761ac371344704c5d1885708c6d0e47219c331244e10c0f164251787414c1f1a4351b83a0bc450444a1803f02c550845a)]),
  ([7,3,1,2], [(64,0xf4811149c0d04f04c93008572b87202861094690b484070370fc9616849034512a0151b00407c6309c7e108310e4901500712c0f0a819084780f03313812004091802406c361200c00c1e0c00606000),(64,0x22c231e83e2084627435140a505094160af1cc0b188b70986a0b885074382347c1005b1289f038ba148a90586d014b108075190281fc430c8872883a2445526408174b41301019c2b2ac1a1bc8a08879),(59,0xa72e48f284bc2cc77224a426c5f2d8be2b4712308311c9e29895164b01d0b81ac2f2188e1f4412605c280bb14caa05c6e2c8761942920044220a30ec562685e2d44d044682f42c2b070)]),
  ([8,3,1,1], [(64,0x5c510a4560b86808c35034620e8741300710419118800785804c251482a1903c0c4090d8700384800c151081a1502c098600e0050c80a1101c0441614028088340300110018048240c0080081404000),(64,0x1dc4f2248e20c5b1b4670fc791f87312c851748a15c2f1a46e18c3b1d44d1e88c11c8107c592185e14c2b1943d1a8371c40f124761388810c1b1542d2085a1b027184391983e1e03302c450747212884),(9,0x7f22c6f1ec8d21c5f1ac7d)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_17_109_checked : PLift (checkBox [3,5,17,109] [8,4,2,2] (2,1) p5_17_109_rows = true) := ⟨by decide +kernel⟩

private def p5_17_113_rows : List Witness := [([4,4,2,1], [(64,0x1247c0b8500fc7218413118680688a024790ac10200320845410c281286c16c0d100620508400c360940a1e82c1383d088441981801c0e1f83007c04098480f86004801020780a8421680c008240181e),(64,0x15c4d1bc911d86505c870e48e1f42f14473160471a41b22c7017c9220433154880e82912c6d148411d063054850dc6a0708c02c7b0b44f2083408c56114670644c1b85d2400f1fc3119016218050e027),(15,0x7723c591c4932243b14c751ac1d2349420c35)]),
  ([5,3,2,1], [(64,0x190281103313c130e8561c80918425130101a02c2101b0dc221e83e1684903434140141b00307c0a188261f8420c41c0e05401c4a038660a819010201e03c0c84e0480118024068361200c0081e06000),(64,0x1ac2f21c8e1f4411745305c6f22c650a481114880ec571cc5e134111a42d21470230230fc5b208460d4510546d1607402c6309c7f10c6a0b886074391547c1005c12c0f19c2b148161b805228211e43d),(9,0x772245f1c48d20c4716475)]),
  ([5,5,1,2], [(64,0x198b5154bd1744c2107304c021ec1b2880a108910c4990e4c00a06013cb715c7e0786d1d415270040f02b24c332e85a124511e01801c6f03c960d8250b4b41504b1c812004900c0271386c030030a806),(64,0x2f85e134851d0142347c070a302c43248322ac9a3483a3042918450324692e0581fc1f1b80e21c762b8162743d0b0a511494330342ec5b128c318c522287906408204211c0a8040970dc2627c3f3182e),(64,0x2308308caa2c8a1104c81a0d02fc5f2188e1f41d290442b09b34c3b308623286a2e45920020220772bc172783e11895334352f05c354c41905322c7a06882088712a411260382c44031c2f19cb6158cf),(15,0xb33448f2b4d432c6b224b029c47338d631465)]),
  ([5,6,1,1], [(64,0x1308d104460ec64060590345e0487c01c301c4251d82a2501f1203d2384218014154091680e1e0030b0211c826240440e43e040051580a1d02807422230400e85803001018700903c150080082001000),(64,0x2187b2902f2644d2785224c47194191a85f220131f431208361dca00ac952684e23c431b061054660685b2100f1e42d1f8321cc9c09c50244452584a0fc68174111881615c8002c341d4291e82e26023),(33,0x8b28c6f21ca527c531ac8920c37284a626c4f1b46706c852287f0cc9d144a225c4b1a46e18c1720435)]),
  ([6,4,1,1], [(64,0x2002b130410347a11812170071441d158221b0170e02d198321f048024420385800c2406452078680d0290b878110100143e0285408015068640c02a1000c004061401c0582c0f008008180a00405000),(64,0x17c751bc3b2148a1fc4b1845b09c711d86b0dc81134861ec4704c5d15c231b4391c867220331f4492084e03c590945e14c7407c690d46e0e8840bc79114111f84a0fc6002c550845a0987006c650c436),(7,0x7721c631cc8920c4f)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_17_113_checked : PLift (checkBox [3,5,17,113] [6,6,2,2] (2,1) p5_17_113_rows = true) := ⟨by decide +kernel⟩

private def p5_17_127_rows : List Witness := [([5,3,2,1], [(64,0xf428200331104f04c3a15809184720944c0406806c2c210370887a0f8491680d0d05000c141b01f188261f8311081c0e05401c4a038660642a080780f03213801048081802406836030020780606000),(64,0x1ac2f21c7d238411745305c6f22c651d82920445220571cc4d178111a42d2147008c7b2303f16c820d446144151b45802c631d0271fc431a81d0b8860e4551f04012c5c03c670ac52014161b8211e48a),(9,0x772245f1c48d20c4716475)]),
  ([6,5,1,2], [(64,0x1cc84008131ec0a06c9128831108990a0393004f180b715cde1b47e0341e1d4040549c0ac3c24c332e849168513607801c181bc0f258250d82d1504b1c801048092403009c4e1b00c00c2a1200609000),(64,0x10c9a2ac290e8c134850184b8324581a4df3c06e1fc0e07ce71d88701416274ae0b03d250a50d0452eccc1285b14863364ea1e48a020193847020410084972a0260dc9f0b83f2d4c6154662f44c174e4),(64,0x1646a380f1200203a0f91dc8805c9e2bc3e254a60d4462f0cd170c435453190da3ac7a22c1a388f31c48204422260a90e0a02c42f100c7158672f8cf1345e394f61d085050dc3b47c2340b0709228c32),(55,0xd73d4b3344f83bc8f2b4d432c6b3c8e93e8892c0a711cce314d6194ec230e33d08308caa284b2104c81a0bf3405f398f7218dd3b87d2381d2904426cac0ecc234c622e4ca)]),
  ([6,7,1,1], [(64,0x10c4e320651c00d060c21a80704881230290d08608c2e2a0451404a310611b0090506600c0e220250c0820a8a41044c30068014101880a210210b0a01204219001030062002808844180080082410020),(64,0x4c1e234980d4872482f0e8b41445c28cae12c56314d01b478054ca19c7203c1a224940c43c20c8e0ac36294b0134582a847148c1330691d011070c618c6e02c16214900b438228270c8a12b049150a6),(64,0x3687707c9924c9e0ecb5174af2e857344dc1e4cb358731f81b2543d23c9a0dcb12f0592acb614c5e334d81d41d31cd21bc7a05c912703922c960cc3e2b4b8154a72c84f168c9350711f01930cce1ac76),(25,0xbf36c9f2ecdd35c7f26cbd2dc5f364d33787b274970fcb92ccbe16cd51f4cf)]),
  ([7,4,1,2], [(64,0x10051300611c80204cb71a4d80281b1e48a0ac8108833288431504b2e85b1b00d18cd201015210250d87b0b49c0f44e2d06601c181740f1f81f0c0272584818001048091e02a0845a030030903c0181e),(64,0x2cea0707a22c2c3848224c230d0a311055268ab130bb3305c1b40e30c641d4d3014e4058850983736c7c2342e274ae0f84f2944615cb531867020192f45e1bcde0407f240200c4d521c280e4972a049),(64,0x748c38883250352905626cac134bc3346e31076350e505c860e0dc3b47d2382f278af140a611c582d8c71a01a2f8cf17c7037c11200910c8d639c880a43a260a9128a02c441148c1188732e0c91a8d9),(39,0xd13a4b332cec38c952b4ce31477398dd3b88f2c0a7164c82fcd01c4e0248d73a0890ecaa284b214cc21d0b93286b368eb)]),
  ([7,5,1,1], [(64,0x1345803492148ac01c121846c0842c1981b098800d4400e8941245402414138a800c0e1a01d0a0620887c0c43624050014101280a190190901e1e0380c84c0040c018600801a0d048020020700406000),(64,0x2b4b804c6d0b4b219c7209c81230411ec860ec46254a01541513c5a2a4b403c691d0292b8631b8230b87d2203d208371089127051170112584b158b002c1619470094aa1a81f0a87921039110330f898),(57,0xa72ec8f28cbd2dc7722ca527c5f2e4b32f8732348711ca126ca616cb51d4af2e86f0bc8920c8e10c9d17497288572f0171c4ab2d86b1d82b214451fc8a0fc992905924c9e14c5e)]),
  ([8,4,1,1], [(64,0x1044c0347a1189001c121445c07456280170886c0b438198321f03d120091088c00c0e1601909052078680a4340b878110050f80a150150801a190300a8400040c01850070160b03c020020602805000),(64,0x218472449c04c5d25857188a12b0231b439298671c8331f4881248210c4e2349803c590949214c5e2a01f1a4740d4a21b82f0e879210450447e1289402c55180212385a2901b098651c0311a82b0d880),(47,0x9f2bc8b26cb12ac7721c9d25c632b4a72c8732248313c9924c9e17ca91d4a32b86f0ec851fc8a12c951848f2685b294b009c712a86b1d8372044d)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_17_127_checked : PLift (checkBox [3,5,17,127] [8,7,2,2] (2,1) p5_17_127_rows = true) := ⟨by decide +kernel⟩

private def p5_17_131_rows : List Witness := [([5,3,2,1], [(64,0x19028200331104f04c3a158091c825130101a01b0b0840dc221e83e1245a03434140030506c07c0a188261f8311081c0e05401c4a0386606404080780f032138010480818024068361200c0081e01800),(64,0x1ac2f21c7d238411745305c6f22c651d829204452203b15c73178111a42d2147008c7b2303f16c820d446144151b45802c631d0271fc6a0742e218391547c1004b1700f19c2b148050586e084792283d),(9,0x772245f1c48d20c4716475)]),
  ([7,5,1,1], [(64,0x2604d1600d2485201cac048611b0210b06606c26200351007a0e8941245402414138032a06807428188221f0310f03624050014101280a190190901e1e0380c84c0040c018600801a0d0080081c0c000),(64,0x178ad04cb81b42d2c8671c8272048c1047b2183b11895280550549a13c5a2a40f2d0691d02918c6e08c2e1f4880f4820dc422449c1445c0449612c0b2c01619470094aa1a81f0a879210391107e0cc3e),(57,0xa72ec8f28cbd2dc7722ca527c5f2e4b32f8732348711ca126ca616cb51d4af2e86f0bc8920c8e10c9d17497288572c4172f0712acb61ac760ac851147f2283f264a41649327853)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_17_131_checked : PLift (checkBox [3,5,17,131] [7,5,2,1] (2,1) p5_17_131_rows = true) := ⟨by decide +kernel⟩

private def p5_17_137_rows : List Witness := [([5,3,2,1], [(64,0xf48a190280cc801104f04c3a02456184251c81006c680b037210221e83e1240d1683400c500501f1b062098311f8420703801c541280e064660a8201e03c0c8011381218024068361200c0081e0c000),(64,0x164751ac2f21c7d1048e1745305c6f22c650a476204450ec8815c7313411178690b48508c701ec3f2305b20846144151b40b1606309c741fc430746a0b839218551004b03c5c19c2b01452058211b879),(7,0x772245f1c48d20c47)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_17_137_checked : PLift (checkBox [3,5,17,137] [5,3,2,1] (2,1) p5_17_137_rows = true) := ⟨by decide +kernel⟩

private def p5_17_139_rows : List Witness := [([5,3,2,1], [(64,0xa0332004413c130e809158611c84c0401b1a02c0dc840887a0f8490345a0d0031401407c6c02862098311f8420703801c541280e1982a010201e03c0c80113812020600901a0d848030020783001800),(64,0x21c7d1048e1745305c6f22c650a476204450ec8815c7313411178690b48508c701ec3f2305b0d482118510546d02c5818c741fc430746a0b839218551f04012c0f170670ac05148160846e1e43d22864),(11,0x772245f1c48d20c47164751ac2f)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_17_139_checked : PLift (checkBox [3,5,17,139] [5,3,2,1] (2,1) p5_17_139_rows = true) := ⟨by decide +kernel⟩

private def p5_17_149_rows : List Witness := [([5,4,2,1], [(64,0x140131c846024791a02b0688a08410200430c8a2150282605b1280d1b04000c62094142100a1e83d0b09c1382211007198181701f0387e0c004098961203e00460048080a8201085a030020903c01800),(64,0x1601b22c5f044700cca3248550a4992204b0e8aa1b4412806314815214740dc0b1ec6a0b49d0708c13cae08c821143429067158192685d1300f1fc6e0c4900146409c9705886124382a07c0fc2e27861),(45,0x952b47723cb129c591c4932243b2aca114cb21d46b0748d2bc830d4a525057134ac1bc911941721c760e4a91f42f27c8e144b01cc4729869)]),
  ([6,3,2,1], [(64,0x110132703a0249218456094721301b040680dc2c210221e8490f80d2585a0d0031401f0506c028620c4261f8420703801c901504a0640e1982a010201e03c0044e0480818024068361200c0081e0c018),(64,0x1149d0ec93220572907313411268691782d214231ec700fc9716c3520851118152786d02c9418c5809c7f1d0430746a0e4910b886154a21f04b1000f260671702b01452084790586e0f48a190332004f),(33,0x8f28477224a526c5f1c48d20c4727c95164a61d46b0bc8728c7d104992385d14c172806f22c2920476)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_17_149_checked : PLift (checkBox [3,5,17,149] [6,4,2,1] (2,1) p5_17_149_rows = true) := ⟨by decide +kernel⟩

private def p5_17_151_rows : List Witness := [([5,4,2,1], [(64,0x27861140131c846024791a02b0688a08410200430c8a2150282605b1280d1b04000c6209414210360287a0f42c2702211007198181701f0387e0c004098961203e00460048081e02a080421680209006),(64,0x298691601b22c5f044811c03328c92154992204b0e8aa1b4412806314815214740dc0b1ec6a0b49d0708c13cae08c821143429067158192685d1300f1fc6e0c4900146409c9705886124382a07c0fc2e),(43,0x952b47723cb129c591c4932243b2aca114cb21d46b0748d2bc830d4a52505726cac1bc911941721c760e4a91f42f27c8e144b01cc47)]),
  ([6,3,2,1], [(64,0x4c9c0e80924861158251c84c06c101a0370b0840887a1243e034961683400c5007c141b00a188261f8420703801c901504a0640e1982a010201e03c0c80113812020600901a0d848030020783001800),(64,0xec93220572907313411268691782d214231ec700fc972305b0d482144460549e1b40b25063160271fc7410c1d1a8392442e154a21f04b1000f260671702b01452084790586e0f48a190330a08013c44),(35,0x8f28477224a526c5f1c48d20c4727c95164a61d46b0bc8728c7d104992385d14c172806f22c65204761149d)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_17_151_checked : PLift (checkBox [3,5,17,151] [6,4,2,1] (2,1) p5_17_151_rows = true) := ⟨by decide +kernel⟩

private def p5_17_157_rows : List Witness := [([5,4,2,1], [(64,0x2781314072024461e42b1a01a2285e0404320032288540a05b2600d1286c00c4009462050840d80a0f47a0b09c1382201c441981807c5c1f83001026258480043e18012020780a8201080c008240f01e),(64,0x1a4a606c5822c11204331c0a3154920a49912c880e86d2a84118ca005452214371d00b1ec2d1a89d0704f230ae08c452083419ca4064562680f1307f0c46e2400509c6425c16124860e0a80fc7c0b861),(43,0x952b47723cb129c591c4932243b2aca114c752c86b0748d2bc830d4a515c9426c4d1bcac2441721c391d8a91f42f27c51238732c047)]),
  ([6,3,2,1], [(64,0x200131109c0243a18492094561c81b130100dc68210221247a0343e2585a00c3407c500506c02831188261f842070070e090150191280e1982a010201e03c0c84e0480818024068361200c0783001800),(64,0x114762743b24c5722073290111a49a0b45e214231ec3f1c09716c8c0d451208151186d2780b18c941607f10c74074391a8910b855218a212c7c03c4019c980ac5c01421148790583d1b88a0cc640a04f),(33,0x8f28477224a526c5f1c48d20c4727c95164752986b0bc8728c7d104991748e14c171bca022c650a481)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_17_157_checked : PLift (checkBox [3,5,17,157] [6,4,2,1] (2,1) p5_17_157_rows = true) := ⟨by decide +kernel⟩

private def p5_17_163_rows : List Witness := [([5,4,2,1], [(64,0xb89e04c501c8091182b1a01a2282117843040800c8a21505b0a0980344a1b0031002518814210360f40a1e82c2704e08807110660605c0387e0c00409896120010f860048780a8201085a0300209006),(64,0x1a4a606c8b1605f044810cca31c055248292644b2203a2a84118ca005485148371d00b1ec2d2746a13c1c230ae08c45208670d0a4064561749a03c7f130311b8900142725c6412416218382a03f1f061),(43,0x952b47723cb129c591c4932243b2aca114c752c86b0748d2bc830d4a515c9426c4d1bcac2446505c870e4a91d82f27c51238732c047)]),
  ([6,3,3,1], [(64,0x168d00980b2044c308311c89808c64124142283a018610b0a2044523207800c440a46a068901040c208322a05809009128c01c02118812220380102a28050004680600a2003008848180100082810020),(64,0x2c47c01c2d28c6e14c1e324941e4ba114861ac362b01b2445c3480d20c4e310332a4741649a1984b058c1230710f0b2360630b8a404c89150ca0e47a014460aca11b051070922e043038841a4342a819),(64,0x1bc1f254d62ec870dcad174d32784f314752d89b3706705cce0f4b31f8d90bca5154cb2587b2f0471b4ae07493178d42e40f214c60d4ab1d85b3449c09c4d30c8e1cc3e2d099368652981522c563303b),(25,0xbf35c9f2dcdd33c7f25cbd2bc5f354c71dc9d3788f0fcb536ca715ccd1f4be)]),
  ([7,3,2,1], [(64,0x1109c1843a24825158ae1c81b13037040680b084124221e80d0f8961683407c502a0141b031028620987e1081c01c38240540644a038660a804080780f0010c84e04808180240d848030020783001818),(64,0x44692682d2145e2d8231ecac0fc971c05b23035144a9208151b446278ba18c9409c7f160b010c74074392446a1542e218a212c7c03c67100980ac5c2d00508479148aa0f4161b88a0cc6413c2820013),(57,0xa72e48f284bd2cc77224a526c5f2dcad1c48d2f88311c9f2ec95164b11d4a61ac2f21cb828c7d10499174b52385305c6f2808b2f0650a4812c845274760ec9315caf220732904d)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_17_163_checked : PLift (checkBox [3,5,17,163] [7,4,3,1] (2,1) p5_17_163_rows = true) := ⟨by decide +kernel⟩

private def p5_17_167_rows : List Witness := [([5,4,2,1], [(64,0x278501c8091e4460ac680688a0845e10c10200322885416c28034981286c00c4009462050840d83d0287a2704e08807110660601f1700e1f83001026258480043e180121e02a080421680c0082407800),(64,0x2988b1605f044810cca31c055248292644b2206d0e8aa10463054a0214520dc7402c7b0b49d1a84f070ae08c45208670d019290561740f2687f130311b8900142725c6412416218382a03f1f0610b813),(45,0x952b47723cb129c591c4932243b2aca114c752c86b0748d2bc830d4a515c9426c4d1bcac2446505c870e4a91d87d0bc9f1448e1ccb01a41b)]),
  ([6,3,3,2], [(64,0x3fc874e039040c1125232ace40d0961b41e33c574200924442064f31ed2c2d0041983d27c2736061048c312cfc210360346f480a80c49306ccc150060fcf01e0632702403cc0120331b01800c3c1800c),(64,0x1f02d4b4de2d517014670f8c9280510a1023648a4ec6204cc41d44c498fd2b88539c37038991c021484d22a45a42d440c8941141c3d8cd1f8554bcb701c69100f1288790a8db45002190153189d13825),(64,0x514951181d3dcce1fc564c0e12e11a0206a104f228c7a0ad053708d4f9151941631c9e13d29099002c4884e4ea0e8113087312924354ac1750e3943525c6e07cf93408116132424ba0289210c1a3d0a5),(64,0x224eb5343b1d125358ad1790f39948260203e8d1208594cd0a2ed1d02c443d4a61f42e4b8df2d94146068328a11482940cda22d3c3b41431476135273f8af219113a14a0e0710892234caa16d35430bd),(64,0x38d1c41c8f5012b2ccec538d717d10524fb20d342f11e29c2f38142464cb14d042313d3b8774a0b0448e952c9b08cd417136434be518473e0804c4e22e51b1aca40b1063748e4fd1605cc81412a404b2),(7,0x11f50cef44d4c4dcbf)]),
  ([7,3,2,1], [(64,0x24610e825248562b87206c4c0dc101a02c124220347a0f896168030d01f140a80506c0c40a188261f842070070e090150191280e1982a010201e03c0044e0480818024068361200c0081e0c00606000),(64,0xb49a2145e2d8231ec3f2b0971c05b230512a4152086d1189e2e80b18c272507f160432c074074392446a1542e218a212c0f1f0671002b2605c2d005084791483d2a8161b88a0cc6413c2804c801109c),(59,0xa72e48f284bd2cc77224a526c5f2dcad1c48d2f88311c9f2ec95164b11d4a61ac2f21cb828c7d10499174b5238532ac171bca022cbc19429204452c89d1d89315caf220732904d04469)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_17_167_checked : PLift (checkBox [3,5,17,167] [7,4,3,2] (2,1) p5_17_167_rows = true) := ⟨by decide +kernel⟩

private def p5_17_173_rows : List Witness := [([5,4,3,1], [(64,0xb80b2845c0e48a088b81f059050aa108d81c0061e434044ca1889000c540c482068b012051030a20e8d01a02c0245a220200a47a048a8100040c8c818001148800600a280380a8581e0100083014028),(64,0x21863078b42444c38855298830f81b350b11b0492680d28c5e0ecd123069090ba3a02d16c162b08911021368721ec3604ccc2a464104923000515833324841841c2c84a38053038a42043c064d21a898),(64,0x26cec17c25378bb1d8e91fc172b44536c961ccc40dccd194b624c4e390c115c85074d62cc6e12ce12700f2943d2386b098bc264ea0bc5d2b88b11823370b91d07d054ce2ac6610cd925071308070d4cb),(41,0xc739c9f2fced37c7725cc52dc4f394d71bc9d3b88f09cbd3acaf11cdd1d4c633c67254e630c8707cb5134e3278a70fcd51b4be)]),
  ([5,5,2,1], [(64,0x2491148311e81a2884209c7013c1026038300601b42e034b61587e078031302b1d0142703c124920c8ba1682801c501e0180946e038960d8040b0b4150011287204808240261386c0302a1200609000),(64,0x3482f2dc572807f1001f3206813475054be2745e0f4862b80b24c332ec7c16c1c29044330291449a1e43a064c21888a1bc0f2e09716037200202a0050b4b51d8550589e3186612c941cc3404cbc17084),(64,0x8cab34ca1104c91a4b22fc5f21cd02bc7d074a5114cd2389b0ecc318c8b350b916481084ca2a46a1dc1727c3f31c8819cb0254352f45d29885118ce14c7b06cc428c6410c8c1c4990e4c120861088aa),(17,0xb33448f2b4d532c6b224b129c4733cc51948d35883)]),
  ([6,4,2,1], [(64,0x24791182b2d8680688a0845e10c10200322885416c2803498128ba1b0031002518814210360f40a1e82c2704e08807110b4198181700e1f83001026258480043e180120202a080421680c008240f01e),(64,0x2644b2ec881b43a2a8cc10463054a0214520dcc21d00b1ec2d2e09d1a84f0708c2b823114b5208670d019290563185d03c9a1fc4c0c4bc1b8900142725c6412416218382a03f1f0610b8132785030072),(64,0x324bf1c493340890ecab334a114cc31d4b21ac1d234ca2bc830d4a515cc72509b134bd1bcac244ce1941721c39310a91d87d0bc9f1448e1ccb011cb71a41b2988b160c817c11204332f8a31c05524829),(11,0xb332c952b4cf3147723cb129c59)]),
  ([7,3,3,1], [(64,0x2c8113031308723a09808c64124142283a2c0610b011288523207800c440a46a3801a24041030820c8a816009128c01c02118812220380102a28050004421a018200300884818010008281000808000),(64,0x78941e4ba114861ace10d81b2b091170d23e00d20c4e0ccc42a474164ea268251984b30416230710f0b218c2e04ca4224540e4ca1e8f0014460aca11b0513881c248b810c0e210690d0192a85a34026),(64,0x19c172343d338b31f8f43642f29455398cb2587b3c4bc11c6d38c1d2b893178d42e4fa03c850d4c62ac7616cec3449c09c4d30c8e1cce90f8b4264da194152988b1583b330b11f0f201ca31b853390c9),(57,0xdf3dcbf35cfd3bc9f2dcdd33c7f3d4e725cbd3f8af17cd53ecc71dced274de23c3f2d4f636ca715ccd1f4f32f86f3941f254d62ecfc21c372b45d3b8d3278f9314753acb626cdc)]),
  ([8,3,2,2], [(64,0x3a80d244570dcdb205052ac281c8520609c480423183304cb7174e121c041382e1e0fc078a21240f24c392f4630a80a150d81f8251bc990fc060c0b41680112c7506c0c2403609c51048030b44802424),(64,0x388a82212c3480513c2f1e4fd07cc328c693b517128102503a378be21064420ae4c82b02c553647f48c45324f309870058ba26860100e42290e01c312d47b16cff084a54a4cf0084c258760f01c30066),(64,0x3d13e1c4172ec9b184413948b4bd0f354080c8b61f05c400222992a3c0d04684d25c770f41d3046742ceb2c53503892160383708249906330ac0a47314c192752110ce731c8d4453b1b834050b817902),(64,0xf8c21a10c3b0b24d85920d2741ccd2b4f7504740689e488443a0c8239124f0352e45f40ce32a4894b4d3474501e8fe080c42906a3b938460112543b37cbf21465424af4ccf90b056368a020124118ca),(59,0x11f4e8fb459404c4d73c91c434b34dd28338f8508e923d134f5042a92e3511e3146b3bd39464e02190a2c1343e8a14944732d153d53f2f0623988c4c1103587d4042329d2b3c4d146c98)]),
  ([9,3,2,1], [(64,0x2700918425248562b87206c4c0dc101a0c00b084124220347a0f896168030d01f140a80506c0c40a188261f842070070e090150191280e1982a080780f0010c84e0480818024068361200c0081e0c000),(64,0xfcac25c7016cc8230e40d4512a4152086d36846278ba02c6309c941fc5810cb01d0cc074911a8553082e218de2884b03c7c19c400ac98170b4014211e4520f4aa0586e3188a0cc6413c2804c8036044),(64,0x2ecec254592c475388cd2986b30c2f21cdf2e0a33507d10499174ca2d48e398ab05c6f370c72808b2f0650a481364452c89d1d8ce3a83b24c57310af22073380a4134111a4c10b49a2145e2d8d208c7b),(41,0xd73a4bf344ed38ca72e4d532c8f39cdd284bd3b8b31dccf3acc5224e1294d626c5f2dce834cad1c4c9234e52f88336c4727cd0)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_17_173_checked : PLift (checkBox [3,5,17,173] [9,5,3,2] (2,1) p5_17_173_rows = true) := ⟨by decide +kernel⟩

private def p5_17_179_rows : List Witness := [([5,5,2,1], [(64,0x21009244311487a068a21082713c70040980e0c01806d0342e2d8561f81e00c2b130142703c1240a248322e85a01c2814078060251b80e258360102c2d0540044a04808240300984e1b00c0082a01824),(64,0x2a82f348b715c7f2801f100c81a04d1d415274be0f45e2180b2b8930ccbb16c7c070a411029330511e49a0643a308622286f03c972e03716080080052a02d2d4551d816278c61984b1cc9404c342f05c),(64,0x8cab34ca1104c91a4b22fc5f21caf3407d074a5114cd2389b0ecc318c8b2b0d42e459204212a4ca1a87705c9f0fcc719c882c0950d4bd1748529846338531ec1b28cc410c6423071264393046120822),(17,0xb33448f2b4d532c6b224b129c4733cc51948d35883)]),
  ([6,4,2,1], [(64,0x118b61a01a2282110c5e040800c8a21505b034282604a2e86c00c2510062050840d83d0287a0b09c13807088442d0660601f1700e1f80409896120010f860048081e02a080421680c008240f00607800),(64,0x2ec6d2203a2a841330630548528037148c21d00b1ec2d274b813c6a0708c08cae114b519c8206434290563185d03c7f26831130bc1b8052402725c4919016218382a03f1847c04c9e140c01c8091e42b),(64,0x1c493340890ecab334a114cc31d4b22e46b074af328830d4a515cc72509b134bd1bc912b0ce1941721c392a4c41d87d0bc9f144c11cc8e2c0472dc6906c8b298583205f044810cca315470248292644b),(13,0xb332c952b4cf3147723cb129c59324bf)]),
  ([8,3,3,2], [(64,0x1247248cab570e40d06d2581e33d8015d0802491064423cc7b4b0b40103d1989f540273601230c4b3f084034361bd202a03124c1b330540183f3c078004632702403cc0120331b01800c3c1800c0c000),(64,0x144d94088a4ec625d0133104c1d4fd498852b95f39d98038371c099484212a4d260c5a42c325109407045334f61547e4bcb75a007100693c479289530a8db6300245015274c60944e3fc874e0100e4c1),(64,0x4f8655dc16278c70984f40129220b1588ea66c110e8c212873490ac3555d6185d3950e0d5471b89707cd03e58116081425322e96b028926901a10cf41f0a54b5560b4b53798f015170f867280c954428),(64,0x3690322d3c594ed5d59e050c5134763f927218af581893a111664385287126922088aa34d8416d0c4d4bd5156e255a707446338f71587f4c1592e0e15a5920211a1046a3c87a28d540acdc4158d23515),(64,0x6388e4593f5e1a105cc8141014a8892c93a58ceb6703b53474494ad3595e61c5e3990f520986a820344fa608592090a4ccbb5b19502d1d694443d47d2992e55c2e2d8df64118504685e8a1329520a452),(64,0x5c9ab3ec834d0bc5b596479a629d580bce0645195097b32c534108c4f5663b97667c774a0b0628e94499a52c9b6b423351851710d4d8be5196f6a0473e0804c55a2e4e25a99346c6b5f4a45542c37506),(41,0x17f68d4f5cdac65d1f50d7c59cef6818b44d4c6b9372fd706a55b38d944717e41c8f501796892b2cd643b19d538d76205f44149)]),
  ([8,3,4,1], [(64,0xb8a10f45e239222f82b16c7c060ac50048370061e4150d8ca198fa258030cc5421118080b41440e2883e3486e02c2c170f0230291e8162a8460d0c819001148820780c2803c0a85a1e0140083214000),(64,0x29919084422d4d61c9064d80f0c0a30fc6034cf41bc90490c05502d1747e3c41a234ae5084a3790e0207b05c382accc11c683f0984b0050d456324652191a088b6528e614c1020ca407c40350704100d),(64,0x2a11b08c442dcd852c7439d084e01129441188d53d87124905498c25582f17c803cc1c23d235104c2fce04407d0643a2b4ce504491a8dd3f89a4b80757837160cb19c883ed1c090972e14c3a05504885),(64,0x3b15f16489474253694d1d8e94293a04ca710cd73e073251074a0c44dd580c4613d4912c9255184e304e2555121fc1b2bcd050c4b1b0df4009c43d30025600e4cd1a48a3f51e098992e92d538ea15c87),(64,0x31559458b351c4f38d134d1643446d4049d4c5523b96122d1f09cbb53ceb4313c2a445364754252a31939568633dc9349d4830ce455d142041d2c545134e14089e445325883b33c6b3fd2026cbc4bd50),(33,0x13f575174d56554cef4353d4acc756d49395155990327d3358d212f5513b53e36c7742d3b570f925529)]),
  ([9,3,3,1], [(64,0x2c2620431130c21c8e826023124640508a4003a2c006184110b0a2148c81e0030a4441a8e006890030820c8a8160090904a3007008462048880e02a28050004421a018028800c022180100082810000),(64,0x1ac863841b0d8912b122170d23e00d20c33138a9310591d0ea269100944b198c105871231020f0b24a06304c2e224a40e4543287a3c0050ac46284511b0e207092420b810c0e1a484064342a920168d0),(64,0x2f13211c6d38c1d24cae42524178b9350fa03c850d4ab319211d8d13b09c448274e04d30c73238e94103e264b44a8da1941522ca64043b158b13307c3c8074602d28c531b8c93901e1e494428ba4c045),(64,0x4acdb3d91c29c573347d3cd0e2f9194d06f07c9542d262ecd64c4fc21c372b523174d33b89e3e5144e84f314753ad0626cb64452c3706705c8d40c3d2ccce4a47e364f44682f2945532ce61ec963c50c),(55,0x11f4dcff45d3d4bcdf3dd1d43cbf4d52735cfd4f8ef27d154ed072dd2d3751e33c7f3d51b4d8e725d0d2f5333f8af4945f354fb4593c31c773b49d44d2e3793923d050fcb5)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_17_179_checked : PLift (checkBox [3,5,17,179] [9,5,4,2] (2,1) p5_17_179_rows = true) := ⟨by decide +kernel⟩

private def p5_17_181_rows : List Witness := [([5,5,3,1], [(64,0xd8c11046c28822360580cc69250143284a40080018910443c3c8722a02800c391909a068d014061030c2108f81e0090d06a280200c492048c81203a3c0700046226018028c0100321a0900403818008),(64,0x2286526cc606c46344fc1447c2c80d3a0c310c6e3e479290243685a0d5101ac96058a13302113102208b824c130f8c93d0491d0aa0a805380663c4712701c348524208818c0e264c4064443e87a2c00b),(64,0x3d4752acd60ac563850c230672741d34cfe14c7e424892d00f3a8c5114fb1eca6098b13705c0dd121b4a333823138d941059210ba2541532cf612c76404812b0073883d460f31cc9e078a9350291510a),(64,0x234ee3fc7f2d4eb458a709cdd175132f8cf13d05214bb3991c3dc770b4e34388e4649f07cd51550b22cb63b0c711cfd1f4b33785e3a5141bca5094db4185b219112f09705c4d40c832b82e2e4e40fd1a),(23,0xef45cbf39d1d43c8f2dced37c5f4550721cbd478af0bce546cd715d0d)]),
  ([5,6,2,1], [(64,0x90092a4371788c068ba1202d16c82040b00f8de1b07f03434350622401e00c3116086050b410855028aa0e0d8198070b85c228180ac0e2b83c01032348600045621012020a80d82c1f80c0083015000),(64,0x244b807c4639874164a221c152d4dc10c6a2602602cc62ac39364672381c2f04a0bcea1e05d22cb2064403806e2700f2bcd60f46424820014c01383334c61220162d8443907215c852b0130e8da1a096),(64,0x12ceb1e4a0338b3104e11bc9d310523c8d719493084c13a04f1d8a4224172dc453947326828320ad0ecf636c6925cbe0944c1e85f2341b2ece21247027883044cc2c43f37c6d25022308500d4f035463),(53,0xd13d4a732cf93bc7d284cf314533cce91dca53e89b0a4c93dcbf134ed1ecd038c7127ccd3d09508cc3144f1298b911ce71d4a3328f83746b2642731cee1f08f074bd)]),
  ([6,4,2,1], [(64,0x1e42b118b61a01a2282110c5e040800c8a21505b034282604a2e86c00c2510062050840d83d0287a0b09c13822110b41981807c5c0387e0c004098961200118012020780a8201085a030020900607800),(64,0x2644b2ec6d2203a2a841330630548528037148c21d00b1ec2d274b813c6a0708c08cae114b519c8206434290563185d03c7f2684c2f06e0149009c9712464058860e0a80fc611f0130b89e140c01c809),(64,0x324bf1c493340890ecab334a114cc31d4b22e46b0748d328830d4a515cc72509b134bd1bc912b0ce1941721c392a4c41d87d0bc9f144c11cc8e2c0472dc6906c8b160c817c112043328cbe1547024829),(11,0xb332c952b4cf3147723cb129c59)]),
  ([9,3,4,2], [(64,0x16d6b355b347440220ba091027806c528092d41f1452f26577384041307e319a40c10e1e4153cc5d4eca504042229683483d2dc213fc690184e4b0960047b30c2d048f01683f2d01e00c4b1e00f0f000),(64,0x1e9d1058483d05e2413c5b8a6361b6481fe0444322cbd5a42734d0578c6f5362b0f995030b808854401321a89c5e8e47080713c814b497325a70cd117bc025647c060c43d82e1813e870a861813114f1),(64,0x48e01050463ca491708e3016c0a8d6421b479872479508b841660892ec2515d034d5e11b49f52d7d39dc5028b683420148844c09a331786a836389147c8055723a1347f06cc73e5a50c46343e1f2ad89),(64,0x5a828351064e1e41c0a2539808b0ea659c8034b984023155011ac9d33d7b6b4393951770df50215f8f4502092e260ca3f1a80d066449447c2222b95a6307d75019314f70bc6124d3f5c61d2a4db61db9),(64,0x719f802d6283a4014c854c49b335796ac3738d1551df3894b15758f8ec8075c1c320fa698321911050974880ac3798a6f12674a0405c493d64c17c914f56f29cd942db77a475485537fe311119b230be),(64,0x3f5a90d46744d457c6232bd5b6fd2975607068f893c62251405ca1e2a8dc621ba7b12455a028d04767a4a23cc15b42b35d096d5e71cd1f545838bced665cb2f21309858411367886e2814c5f9b03a11a),(64,0x50d75884ad37d8b6f52774e058dc4a6864d249703690c6e1ea1d922552008c99c738bf8582941d397947128d4f6062d3ad97725fb039658464315934278d05f1ae0e8e6461c47da28581928f883768cb),(64,0x51a242c18e7012a75a08940955ccdd6eded55e038d59f92cc28642c429e81d152612303b99a73214918594dca15fdb13a51b71df958e0f90486774ce6b038459487d2262c95e6423c7620a074fb94865),(64,0x4ae09945ee562366821a614ef7361591db2471fa592427794989cb3645d982e535d8e06f92881a3868a4e435eb1dd558cd9d73e174e8a4608ec729fc59a12910d16bc3b465f78a56164e3f76cfe95468),(17,0x21b921df832548e5a3742187f5679162a651dc959c1)]),
  ([10,3,3,2], [(64,0x1247248cab570e40d06d2581e33d8015d0802491064423cc7b4b0b40103d1989f5402736061048c312cfc2100d0d86f480a80c49306ccc150060fcf01e00118c9c03cc0120331b090060030f06003030),(64,0x4edec1897404cc4130fd498852b95f39d98038371c099484212a4d260c5a42dbc0c9442501c114cd3d8551f92f780b75a007100693c479289530a8db63002450640549d31825138ff6c0874e0100e4c1),(64,0x2c539588ea66c110e8c27504a1cd242b0d557586174e5439bf0d5477e06e25c1f340f960458205094c9e32e96b028926901a10cf41f0a54b5560b4b53798f015177203e19ca0325510a051365026cc8a),(64,0x665c20e14a7ec7126922088aa34d8416d0c4d5bd798bd5156e255a707446338f71587f4c159784b83856964808469cb1046a3ca041e8a35502b37105635b6235154f8655dc16278c70984f401296c488),(64,0x7e4986a820345821648242933790bb5b19502d1d695ce110f581c7d2992e55c2e2d8df641b946141725f21a17a284ca54829148da40db422d3c595ed3b57567814315d7134763f927218af581893a111),(64,0x5bda8744473e20a20131569e22e4e25a99346dcc7d46b5f605291550b0dd4198e6dc8e4593f7c17868417321da141014a9b2224b24e9633ad9c7143b535d57f874494ad3595e61c5e3990f701e952171),(64,0x7a9495c9fa6acfb834834d1e52f16d6591e699cf820a75602f381916e942729f35eccb77453411b52313d599ee3b97667dd8804774a0b05858a3a512669c352dfc26dad08cd46145c435366f9e72f946),(64,0x71d4f801eb5cdac8399747dd0825bb50df45f1de59cef681d98098b44dc4531fd6b9377a0bf5c1a974a0b56ce36511c735f65fa0641db823d407c579689db4acb3590ec675c6539d67fcd76205f441c1),(9,0x1df80daf74e0c7dd7f68ddc)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_17_181_checked : PLift (checkBox [3,5,17,181] [10,6,4,2] (2,1) p5_17_181_rows = true) := ⟨by decide +kernel⟩

private def p5_17_191_rows : List Witness := [([6,4,2,1], [(64,0x1e42b118b61a01a2282110c5e040800c8a21505b034282604a2e8030944018814210360f40a1e82c2704e01c22110b41981807c5c0387e0c00409896120010f860048780a8201085a030240f00607800),(64,0x2644b2ec6d2203a2a84133063054850dca0148c21d00b1ec2d2744f2e06a0708c08cae114b519c1920834290563185d03c7f0c49a2f06e0149009c9712464058860e0a80fc6104c7c0b89e140c01c809),(64,0x324bf1c493340890ecab334a114cc31d4b22e46b0748d2bcca20c352945731c9b134bd1bc912b0ce1941721c392a4c41d87d0bc9f144c11cc8e2c0472dc6906c8b160c817c112043328c552f87024829),(11,0xb332c952b4cf3147723cb129c59)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_17_191_checked : PLift (checkBox [3,5,17,191] [6,4,2,1] (2,1) p5_17_191_rows = true) := ⟨by decide +kernel⟩

private def p5_17_193_rows : List Witness := [([6,4,2,1], [(64,0x24790ac462d8680688a0844317810200322885416c0d0a0982e86c00c2510062050840d83d0287a0b09c13807088442d0660601f1700e1f83001026258480f860048081e02a080421680c008240181e),(64,0xa49912cbb1b4880e8aa104cc18c1521437280c21d00b1ec2d2744f2e06a0708c08cae114b519c1920834290563185d03c7f0c49a130bc1b8052402725c4919016218382a03f184131f02e2785030072),(64,0x324bf1c493340890ecab334a114cc31d4b22e46b0748d2bcca20c352945731c94134bd1bc912b0ce1941721c392a4c41d87d0bc9f144c11cc8e2c0472dc6906c8b298583205f044810cca3154be1c092),(11,0xb332c952b4cf3147723cb129c59)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_17_193_checked : PLift (checkBox [3,5,17,193] [6,4,2,1] (2,1) p5_17_193_rows = true) := ⟨by decide +kernel⟩

private def p5_17_197_rows : List Witness := [([6,4,2,1], [(64,0x1e42b118b61a01a2282110c5e040800c8a21505b034282604a2e86c00c2510062050840d83d0287a0b09c13807088442d0660601f1700e1f83001026258480043e18012020780a8421680c0082401800),(64,0x2644b2ec6d2203a2a84133063054850dca0148c21d00b1ec2d2744f2e06a0708c08cae114b519c1920834290563185d03c7f0c49a130bc1b8052402725c4919016218382a03f184131f02e278501c809),(64,0x324bf1c493340890ecab334a114cc31d4b22e46b0748d2bcca20c352945731c9426c4d2f46f244ac1941721c392a4c41d87d0bc9f144c11cc8e2c0472dc6906c8b298583205f044810cca3154be24829),(11,0xb332c952b4cf3147723cb129c59)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_17_197_checked : PLift (checkBox [3,5,17,197] [6,4,2,1] (2,1) p5_17_197_rows = true) := ⟨by decide +kernel⟩

private def p5_17_199_rows : List Witness := [([6,4,2,1], [(64,0x1c8790ac462d868068212284317810200322885b034282604a2e8031b02510062050840d83d0287a0b09c13807088442d0660601f1700e1f83001026258480043e048081e02a080421680c0903c01800),(64,0x2489912cbb1b4880e8412a8633301521437280523080b1d07b0b49d13cb81a81c08c8c114ae2d4670643429056174c603c7f0c49a130bc0146e09c9025c4919016218380fca8184131f02e2785030009),(64,0x324bf1c493340890ecab334a114cc31d4b22e46b0748d2bcca20c352945731c9426c4d2f46f244ac194ce05c870e4c41d87d0bc9f144c11cc8e11cb02dc6906c8b2985817cc8044810cca3154be1c029),(11,0xb332c952b4cf3147723cb129c59)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_17_199_checked : PLift (checkBox [3,5,17,199] [6,4,2,1] (2,1) p5_17_199_rows = true) := ⟨by decide +kernel⟩

private def p5_17_211_rows : List Witness := [([6,4,3,1], [(64,0xe42e170f22282b088b8164142a842360791c01101834328623e0032403115082068b014448030a20e8d01a0090b05a3c0880a4201e8122a0400c8c818001148800600a280380a858040020c05002028),(64,0x6cb1298490f8d41b102034a32683b34469178f42302d090ba16cf13a0891f821058ac110da1ec72420132a4410d8cc190fa014920ccc93006115884070b214c4a380810640e2903c3486a4000b28498),(64,0x3ec93304b615c4e390854481d2cc4b384d61b90403ca52703d34c6b404f62648e0bc262f05d3ccea22c232e4ae118dc1f474428152ac43364ce1c4663f0072503532cc218cf9244862d055130e220d10),(64,0x13ce544cd71bd05274f73b88f09cbd3ad0e2bc473747542ccf318673f49530ce621d1407cb5134e34450629c9e0fcd51b50326cbe17cf53b08d094bb3a4de1fc76430172b4db1cd093f8960dccd31065),(17,0xef43cc739d1541c9f2fced37c77434ff25cc5458b7)]),
  ([6,5,2,1], [(64,0xc4523687a09c1a2884f10870040980e0c01b4600b8b6158de00c7e0ac1e130740509c1243c028920c8ba168070a05036078094181b80e258360102c2d0540044a1c812240300984e1b00c0a84809000),(64,0x320751a0f00549d0f4be178e602c93218332ecae16cdc1f029070a414444364cc1e4190e8c21bc623a80f25c8a0dcb8160e0014800b4202d4a8154760589e12c3e3187319813250342f05c3900924484),(64,0x30c633ac8b2e4ac164e135081084a9328771a8f205c9f0fcc719ce8254880d4bd2c05d3948529853118db3387b3d81b28c4331071190ec044992303930461388820bc222dcaa15cdf3487f07ca013440),(53,0xd73d4b3344f93bc8f2b4d532c6b3cce9224b13e8a711ccf3dcc5194ed234e33588308cab34cf428441324693c4bf2c85f39c872bcdd3407d3e01d29445334ee2383b)]),
  ([7,4,2,1], [(64,0xac462d868360210688a10c5e040800c8a216c54034282604a2e8031b02510062348142103d0d80a1e82c2704e01c22110b41981f0600e1f830010262584800460048081e02a080421680c008240f000),(64,0xe8aa18cd33301521437280523080b1ec743902d2744f2e06a36823070452d4ae19c19208342905d158c603c7f0c49a130bc0146e3782725c9012464350162183f0e0a8184131f02e27850300091e472),(64,0x234af328833b0a515cc73889b2504d2f46f37c912b065354ce05c870e4a93107d1d8e60bc9f144c11ccdc238472dcb01a4d906c8b2985f160c8044813a83328c552f870380292649212cbb1b4d622041),(41,0xd13a4b332ced38c952b4cf3147739cdd23cb13b8a7164c93acbf1c4e124cd7340890ecab334e82845330c75394b92c86b36c1d)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_17_211_checked : PLift (checkBox [3,5,17,211] [7,5,3,1] (2,1) p5_17_211_rows = true) := ⟨by decide +kernel⟩

private def p5_17_223_rows : List Witness := [([6,5,3,1], [(64,0xcc223606916094050ca1290024480044060f0f21c8034a0a80e4281909a068d018450030c210878024341a9202803108092048c8120040e8f01c001188980600a300400c8682401000838180080c000),(64,0x30cb210cf93a0791b92429035090da1ad211691028421258163304c40893208134e0c92e0490f8f41d0054a83b3c42a380711989c070d218c524209922019038c4110fa1e80b4c0c12c0410d86c488a2),(64,0x2d0453ecea1ed312c5260dc263706d48c5c448a308d48364593384e41095210154e8cb2e84b404813d87601d2c2b03d3cc2c388734a5182a4292781e350651510a26c8a06d4034451318463f07c03532),(64,0x22d414d8c72d8473f4ec1f5332cce93786f4945e450a50954a36c5b4450625c8605d3c334bc1350320d392e52e2b83f3d42e390754ad1a2ac2b384d619c564309d2301d508d314d09224fe1f80f4d0c5),(64,0x515372dced538df17d1552d0721d3d2f52f478af0bce546d4635c574348d50cff3b87f4d4b53ad27458a709d4c3745d44d494f8cf2f84f414854ecbb3dce61dd2d470ad0b4e34650e27c8e07cd51550b),(11,0x11f51cef45d4d4fcbf39d1d43c8f)]),
  ([7,4,3,1], [(64,0xad20088b81647c050aa108d81e470044060d0ca188033e0900c45420918068b014448030a20e8d01a0090b05a3c0880a420048a8100040c8c818001148800600a280380a8581e01000830140080a000),(64,0x408a32683b4c0d11a45e3d08c0b522090ba16cf13a0890847e058ac110da1ec7204d082a4410d8cc190053e8920ccc930061158844681c2c853128e020419038a40f0d21a80b400a1260390b85c3c88a),(64,0x410a52703d4c8d31ad01264f62382f490262f05d3ccea22d2108cb92b8463707d1d015428ab10d38364713386601cfc250354a8cb308633e4912191c078b41544c388834641b440b1124a60f8d41b00d),(64,0x21d1d07d142d44d38d11418a72783f4d0d51b50326d31498be17cf53b08d48c252ece93787f1d817430ad1153a36c73424fe258374b0cd310653ec934a4c1478b6138e42151b075122cc4b384d61b80f),(59,0x1174dcef43d3d4bcc739d1541c9f4d5272fced4f8df1dd0d4ecff25d2d3151f458b713ce544d3635c6f4149d4ccf73b88f494272f4eb438af11d3c3747542d394b8cf318673f52b30ce6)]),
  ([7,5,2,1], [(64,0x148da1e8274081a2884f10870040383006d1800d0b8b6158033787e0ac1e130743f014270490f00a248322e85a01c28140d81e0250606e038960d8040b0b41500112872048900c0261386c0082a12006),(64,0x2743d2f85e02ce624c860cd0e2ecae16cdc1f0294101c2905136444330790649a0e8c21bc6203cea25c8a0dc58014e02002d420b5080a8154763f8162784b0f8c61cc6604c940d0bc170093909121031),(64,0x1dcff1a8173c89f0fd1a31c673a09522035440bd2c05d39485418a614c463387b40c1b3d8a310cc41c464044ec2648c0e51430461388820bd0a2dc222a85737cd21fc1f400a013440320753f468054f0),(64,0x2c5073e8a711ccf3dd18314653b48d454e33588342c232acd3404f42851c324693c5122fcb217ce721d0f2bcdd3407d4141d3e0a5114cd3b89b2383b458c318ceb22d0c2e4ac164e135081424212a4ca),(23,0xfb464d73d51d44cb3344f93bc8f45d0d2b4d5478cb1acf346ce922511)]),
  ([8,4,2,2], [(64,0x4449c0c54409ccf1908d060c05a04b3cc881f8130f0e41bc0445ca20dc6024d3b078c616c5103cb710875028331990e2642e0908a054bd120060e4e11b0011749006c0c2d03f0c06321c1200c361682d),(64,0x3c07b041232e0ae10d563ac7602d1427c3451c2a348675e90f4149a0bc2530d6b3d88b204164a4be124e71c807468a50e94d388d81b4022593e084c917971150fc2441c2e8453b478035202d4ab10069),(64,0x498bb2c446564ee1e40e631212d8ac1054a3546a5f5124209d0c9450a0d01956e3e48e210194b0c15a44c57cf42247f0511d2a03d540e536c7001583460a30e141330615d0573fc944f01f4c8c717052),(64,0x570f11f01163d242e4af111573b0776011542ca00d5480acd31a17b4410626c264bcc45b04f588f72308205d2a2fc4a54ce8378730218646ca60ed4e38cd91b977408974fc224d4ca17d72154fd2481d),(64,0x500234d8cb5cc563f99249cbc2c847568ef1e98d488ad3586b5f9134249e518293456f594fa23c850692d3096a135603d4806251e2a43e544e63707161119291424e0cd18975161002553d0813332053),(64,0x64d282cd5b6394c35d7f42970598fb2192e5858a47caa548dd615434e4ce5d85940534574f21f590494b0561814590c285490b0d45f1074c0c55b45058cf820d2b550e937c7461d1c29d4f3697840c98),(15,0x16762d3a579916090d4c564554e06217941137)]),
  ([9,4,2,1], [(64,0xac462d868084d80688a10c10200f00c8a216c54034282604a00cba1b02510062348142103d0d80a1e82c2704e01c442d06607c181700e1f830010262584800460048081e02a08042030020903c07800),(64,0x21437281101480b3087b1d02d3909d13cb81a8233681c230453f0b52b867064823c8342905d4505603cc61fc31130052f06e09cde25c9012464350162183f3d8382a06104c7c0b89e43850024c01e472),(64,0x470d505cce21cf70e4a9448c41f4760bce627d0f1450830473370473f8b72c069480d906c8b3d0a617d1616011320813c4333a8a3154be1c029380992484b408bb1b4d6220413e03a2a863468d3054cc),(64,0x484f53b8a745c59324eb418bf1c5283849340d1e35cd0224f90ecab46ccd3a0a144453428c31d4e5400b92c86b488db0748d3f4af328833cc353b0a54545731ce226c94135042f46f498df244fa2b065),(35,0x10d494ef41d2947cd13a50b404b348d1932ced4a8e32550549cfb2b51d33d13430c51dce7425243748f3fcb1)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_17_223_checked : PLift (checkBox [3,5,17,223] [9,5,3,2] (2,1) p5_17_223_rows = true) := ⟨by decide +kernel⟩

private def p5_17_227_rows : List Witness := [([6,6,3,2], [(64,0x161170ccb55d0904081e57c7b3f5bc064d80246669c0430e04185200f0ae42c272a5682101254c6f6c00d3305a7e055450303fc1b570780186369001300ab4202403d501b0572d0fc06003180a803054),(64,0x38cd630bd7f91a0d8b85ddf924c56455d40c4f0414215887e401bf070db5761c1e5381a5aa01cc681c6448da50fc0230580270b14382a2b16b21d097202539015558726cc1033d518406d4b048175fb),(64,0x75c343ccb65d63424565205037081f3796087c7c4ecfe6f41a365986b40a3260a19d266a042014c460e0527c62485e00f5110b4af5b88a431cb0a0e72a9698a085511591d5b604cd2552131c12f6c44b),(64,0x1e9398346a4a5ab1140831d86820a21952478da6100c260640274b25c48d43dce0acea2b56c8ac8851d0a72426395b9058d555e161cd326d04e044d063d528452d7b2011245e474392ed7a7f09616518),(64,0x2c16f8b88b5290d730293a16a8a4865155a864764d5b71441434d92556141c5307bdb2130ce634be5f5ff2645c46dda0dcf62e5788ddfa25116754323c50671422385638887f4f9017001d3719b57a1d),(64,0x6d44f345908492e7b6021285f479dd0e8f92f17b8e9fd25d19760353d1768d49259a2520941411c3080df679618807d4f1be369996b80b3298982ca51a127799a910cc561243281227843e449d10b8ed),(64,0x2691c76c383dd798e095758f241dc6389a1592232013f704dd6721e4ea0e1ad2a7a5ac118c861e46824a3495e4105829049e2cd728c48e5351073c2c3ad6d8b089521ca399ba05cd66555885c744cdf2),(64,0x7ba0347dde0ecfa5f23b261d93d63689883509c43819f8853d669af32d8a9260c2992879c4461644285e244dd20bcee5c22f2314b734e98a94656e1a1dd367d5b8148d464e154c5f01358e2fd7e8f600),(64,0x7ae488cd4f65df477cfb8f22750da062e4a29de8915d33be305321b4ddf614d947c57f8f89b770f88e5c738da2891406760f4adea11d8891ca4796425ce3223d4e740ec8b5496ecd765a184d1f314191),(3,0x1f78fda3)]),
  ([6,6,4,1], [(64,0x124e80a8974d878358184906634d72054b40185458003289ae144f00c890378202352c1b80e4685c5a00b2a84a261a411ce60a0d405922190041495e004a03701e0311816848258d2050022300a11800),(64,0x2ad4a1389c6a04b3a82c265386947a39d860a4c83601a498683557405cb648dc2195040205658805291b014cf257c3428540208923802223d2e3757c07cbe0411c1796a034ac465b816cfa0f04c269a6),(64,0x1f0e96202b32937758da1e41c1a8d75d8192e12571067419732d5541616401ca66c8553d1610d8a3509af210f1640940cce2090914c07237d7e084c04b5cc1bd0e0491e1816c03cae46dba174fc5a43e),(64,0x421752dd5670d66414092a1b415cf658c38295446c4863cd920d541780e420c2624d321d0e1600233092f738714417d480bf1896e044b0475bc17cfe5ac402b54c6e4fb6689e6a83d134ec0b89b4e9a7),(64,0x220f56503750de221591255341d8e36082531131740734497f305cd5c10f04cb247dbe18500108af539bb3f59c6b03f52c4f3b8302753c6a47e3ad8a0b4cc4e5d81ed874a8c91b0d95e01b2e92771869),(64,0x64de13958409cc64cdd21d514604c373d11485c018d025bc442c5506f4ff678415359b27d3e6ac803b58c0bcce4edda1f58932dd736d7a074bc4a5c81ad0a5dcb9561c541db6554593e1650e8a7519b3),(64,0x76d7b2f55c7250b565b73e5980ed4779889655e34d5d41dd1660cc5745135c4b3549bf405a010d4f675ad3bd8e0c4d04f5dc1fd8b335d94adca1b50c5e4bb569c7425572a5486d48a3dd960e54579087),(35,0x1a377d5d665e77551754da163cd1775cb4355b525e822d977958531dd3455c140da21155167d3f77881634cf)]),
  ([6,7,3,1], [(64,0x6084334822225181a0c40510a168c1540112804c5080324988124d80a0843281a205101800c408525200926044229803402030812420580104a5000124082320180290014042220c0040021208002040),(64,0xc8994a07823984114d40908b469811a8d1580212c0c60590c170c35481328909660e80e04e510052518a12cda5042a245201c0863301c20d12188c9560192a00e410545280b2690164051380301188c),(64,0x471831b0d3588232c9196a0693e10e178c5550152910b6685b3a9510e8a14c14601c966304d371430b093489891c8d95a0292e0ce078854506432d5a06caa445a0184f0418565300d271036485338949),(64,0x5ca64359c174ec54c3c28d32664e95e18e0e44f379450b8954918b1d0db5a82b2e9216c07121d16198cd5701d2b113688633c9592a5385380f27905650553903426d2a6447a385706183111cd60988d),(64,0x66ceb5e83b4c54725d26634763756c0b4bc48db21cd692e4cf5781f2b915690653d15b2ad3a684f141d9615ce6534362752c64c7c38d720cd296e07923d1e6146e35564094b446daa1acfa584b131d56),(64,0x6acfb55ca74d99d3b57c0f5335e58f37d6e0bcbe495b41d56b2edb145da619cf6574ad4f1a33cd3953c9f6547e395740d52b6e87b5c58735d6609cb6475ac1b4fc58cb36a4f943d9e17cee5543e29534),(57,0x17f6dd3f5ddbd6bcff4dd7d5bcbf6d5a73dd3d4bdbe1fd756ed672ddad3f59f3bd7e0fd355ed276d8775b4bd6cd5f2bd3e694f54ed9739d760dd2d6f07d5cdb947dae1bcfe594b5)]),
  ([7,4,3,2], [(64,0x33db00cc85450ba078ff18cb5510192a0091392f010935d0493607e30da409c794206c048f315d380349c108875a03d330302dc1b3f0600184b4b0012407b3002403cf01503f210b4060031e00c0f000),(64,0x39d397200e2748d5b843349b30d88845d690f8cd570312f421408662e147070ab3f58c184514c80725977130db4b5bc0089148081319a70a87c42c6f54025054f61693b0409f3c580154e41148a5ac40),(64,0x118d56d83922d1a5b0413415f6c43421915414692ed4a07cae4018f190b6515d4068a94d40a2657a13cde4c1bf0149448d75128d9325aa0b47f4387231153694281e9096606d3e45d4f813288f460c58),(64,0x3395d0c8be534222c503648672e54875c1d2b0fe634625f452385337080825d265e04d3712e6f492485ad209111d4c7559a80ac7d4319b1c0c25442650416294f76185b3a93c72c11280f26045639571),(64,0x768202bd0164065519d52a9367140b269295ec5037d317009549176368ca565ab0b88043d9e1ccc5551a60a50a6646e3e9893b53f7381428cf5610593a13a7249e6e48e4756f110d3589b40dc894616a),(64,0x2c90464c68525d82b58e5f8533893470c9849d79375be489ae20d1268476321576a42c4359c1c552509d105ca63e187170eb4f5cc285823997211cd6595b70e88c46d6d345606c835459066546a2f14b),(64,0x1dd5867543748a7620ec7357335d666e03b4716141d961ad4c76cb0645d64ddc626d2a5f0e07052532d5a6b02f4419f1d155668fb6285f3b94073ca4614e9729ba47970351636d4384655e2fd4e77423),(27,0x1a374d6765ddc71d2b56da062cef741bb47d6453dde2cd947657f38dc44a1af44da2)]),
  ([7,4,4,1], [(64,0xe0724b8352b1681bce6268183505225d0e0548c018403f0031e9360f4b41a0a257820194dc1680e328484100b208361c12c0ccaa0a098058d2140040f8011e0662801e030c8118341b896050021900a),(64,0x218cb50849301055f0830e8744c0372b96a0b0713a12d2ad220a49c068d61509944017238d352851020423f8051f1380fcb63ed721e4f01a8a45802219cde170a14601f040cc12906034843254011cbe),(64,0x41d7e215412fc764c8392c16c0b8733a92f2b5245a42b39c9e070d81589b44819240d55305343d8623444400071f93a104b83f5741ecf24dcb51b0a6588241a4e0178a34695f084dd5505b0484c4200f),(64,0x5f5340ecb25b8301d4ec4c4af4996b0b4e948cda1609d4501b248d7538556208f52d02024804f0432e8ff5d87d3d1392dd733c4a8590261ace2180a54716108cdf5585d464d01390a044883354412cc2),(64,0x3190b60889514c35fd701dcee4ccb14a16d0bceb4949f4581d250d95411362891535874f8452f1015e07f3d93b2e5753cd661b4e4188a747963094e15605f46d5543013228cf5184d311096008750cc1),(64,0x4855b524c760d713bd2945d8e2555162d3f2f5793dd673955c18d1f5650d6108b51cc5605352cd2a5bc313b52736d52165156309353d8940d7a204f84f4bb5dcf52a5205942738d5a1851d55cd15204f),(7,0x15d6152b54d8d5ecf9)]),
  ([7,5,2,1], [(64,0x9c7a0684f288421c010260381b4c0034600b8b600c563782b1f81e130743f0141249c0f00a248322e80716828140d8094780606e038960d8040b0b4004541287204808240261386c030020a84801800),(64,0x2f80b17893398332190e16cae370291f10407051290d911079330192683a1bcc203c6225cea0dc8a2e005160e00b4802d508080552a0763f81612c9e0f87331813198940d0bc0245c244e40c484148da),(64,0x5c6a27cf231d1a19c953a035220bd4405d2c0e52150614ca636c461ecce40c1b28cf610c7131011190993b039230c1450613882f208b74282215caa37c7f3481f4004d280401d4c83f4151a09d3c03d),(64,0x29cfa11ccf3dcc5460653b48d454e320cd642c232acd3404a13d0413251c1a4f12fd1217cb239c8743caf1f4d04141d294f8114cd26cee0ec8e30d1618ceb22cb9430592b0e1204d4424212a477328ff),(25,0xfb464d73d51d44cb3344f93bc8f45d0d2b4d532d1e1acf346ce9225112c507)]),
  ([8,4,3,1], [(64,0x22920088592e07c050aa500421e4d8044700183432803188f80c490150824601a144b01200c2883a340091a02c168f00a4880807a048a810004320011805220018028a00e02a1607804002140080a000),(64,0x268d14c069178f40b48c4882416cba3c550224e80847e058ac508441ecda04c722a5081043633005190fa0cc9232528184562111a070532c9481288138019038a40f0d202c6a285000e4980b85c3c82b),(64,0x580993d82f239240985d2f0f35488b3a92108cb92b9441187d370151d0ab4294110cd94e0713380719835250cb4a863308f9560912191c078552d14a130833891906cb1440492983e3500d1b0a34083b),(64,0x26d314985f2f8f55508d3b123094bb544e95187f378171d8ad43143114db4e873424fe0dc963352c194c43ed5a24d293051e15cb65304e214e446c1d2cd125244b384d603c6e295040f49c34d321ad01),(64,0x4b4c556d1f2dd165344f3951335d361bd055909d4cd615588f3b92509cbd54ceb2bd0e514473753c1d50b4e4cf4b867318fd570954acc35654e21ce64741f2d51452c4d38d114183f278d54d06d40d62),(33,0x13f57d174dd6555cef43d3d4bcc75754f39d1541d6627d3558d272fd553b54737d3e1dd0d4ecff57897)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_17_227_checked : PLift (checkBox [3,5,17,227] [8,7,4,2] (2,1) p5_17_227_rows = true) := ⟨by decide +kernel⟩

private def p5_17_229_rows : List Witness := [([6,7,4,2], [(64,0x416d31f03f4020d30d6e091f22a1699d81f4b0092365b01111b7c886544b3d97a0c0f17f8b4055e3266670411d1f902b40796183c5ac217bca50188a96001438f35dc2d049e02587b3fd680780321c0f),(64,0x38508b587f6304240e10b44c61e987a503d5297109df52ad6c9e4224bdf0bf4a66cc0c1a49097807452e222d989644e0090f870d23e57d0ccf4804b75e2850b93b061e62726a04d20786ee25da416881),(64,0x2b96f9f0254c9f3c00a96d96a9dc6c0812d8e8939840a45ee52399b970510151287ee03548965aa33f04c565803de042e97ba20314f8f27ff0c2d5c206de927e6d05923792f1269a79a05d0451e8ac84),(64,0xca98334c393ea072f57ea2c34504f580b0f2e1c55e6867b02f4f24928a700652679ef4275aa9ac60051218b9e2bbce4261a5ac90bb645b2098f1150684ed43247d62a971014d4060ec6d74311d10a9f8),(64,0x3884842616b5ccc2018da6843541048471eb48c775188a55fb0f94b2c5729fc284d5f6c0cac6e56d9e86f08d308f5f1bfa6429db4036c146ae81a89167a5f1500845622b8cd823199a9a5a13d5c4421d),(64,0x896e636c8f672a99745257d138832db84d665ea43f60a1355a30181a39443e205c48bb7217ca24324fe4c8030d9ccb670c1c4a5eabdca06b66e18c1749231796f239c9b6a2b59a6dc1791f8b085ce592),(64,0xae26c185228bf3cbc0e569ab343219b685c33c836429d1195341e14c86d5329d762e981054e83f1c5d682315d20ad387e7062bdbc5c27d1c8264ce407d3012a9b7b1278bac6d4ba3b251a19885702d18),(64,0x8faff995b503ac246e28ba46b3789267eac980555891688f30b90d966aa71415d87b2b612913503a51cfb823152f9cb5fe8c0d54293e03c40b971a877b6fa4f64a28db09c466069278d1e8bd4ea279ab),(64,0xc3a747101d4aa377aef83b4a16babb9bc6449632cfce86a6b6b745f8b486ce993a80e31255642a17c92d8335da63a9b1115184b1f321d5a59fcc254c2c9bf5ce801d4294da437df042b5bab1e7b1c131),(64,0xc88cb7629953f1d5da8374c2c4e6467eb072c1bdb2a7e1cd34907026e2c5bb06e8f09568aaf98c585951989b33b9cdc676aa14d608872e35ea53fa0bc615b305ce60a8f0e14594a06c4cbc7268a5024d),(64,0xb20718fe66b0d1c8a736ba8dfab45658e24cc4daaa15ecb185a483b52255827162fdcca35439431171deebee4b291b1afa7219d288d742bd8eb6b2b918a30cf4e6ad10d86b27b6cd077591a784755215),(64,0x6facb1d242b1aed68eb01656689f34376ab5872f83319309cfa414694f1472a4e9d52b8e345be4ee6bebc19633d00e9adedeced94a844a55e18c94ce76e9c54b20759fdc28b3702cda04764de44c15bb),(63,0x2cfce257b0344ca5df922ccac567cd71a742548e7463bebdd06a2563267730b706ce1de45b262acdce0ab964cca9352656c5dcd946fc6cabf1a236d0cecaeb3e86f28345dea7d55c8dd9a113a91f08)]),
  ([7,5,2,1], [(64,0x368271e9020684f288421c010260381b4c0034600b8b600c563787e0784c1d0fc050492703c028920c8ba01c5a0a050360251e0181b80e258360102c2d0011507204808240300984e1b00c0082a01800),(64,0xf4be02c5e24c33218bb4385b2b8dc0a47c4101c144a4364441e4cc0649a0e86f3080f188973a837228b8014583802d200b542020154a81d8fe0584b2783e1ccc604c66250342f009170913903121052),(64,0x5c6a27cf20fcc746867254e80d4882f510174b03948541853298db1187b3390306ca33d8431c4c404464264ec0e48c30514184e20bc822dd0a088572a8df1fcd207d00134a010075320fd05468274f0),(64,0x29cfa11ccf3dcc5460653b48d454e320cd642c232acd3404a13d0413251c1a4f12fd1217cb239c8743caf3747d34105074a53e0453349b3b83b238c34586322cb9430592b0e1204d4424212a477328ff),(25,0xfb464d73d51d44cb3344f93bc8f45d0d2b4d532d1e1acf346ce9225112c507)]),
  ([8,4,3,1], [(64,0x3c82b22920088592e0142a94010879360111c0060d0ca00c623e0312405420918068512c048030a20e8d0024680b05a3c029220201e8122a0400c8c800460148800600a280380a8581e0020c05002028),(64,0xec9a345301a45e3d02d231220905b2e8f1540893a0211f8162b1421107b368131c8a9420410d8cc014643e833248c94a061300562111a070532c9481288138019038a40f0d202c6a285000e4980b85c),(64,0x40560264f60bc8e49026174bc3cd5222cea484232e4ae510461f4dc054742ad0a50443365381c4ce01c663f035250cb4a863308f9560912191c078552d04c20ce24641b2c510124a60f8d40346c28d02),(64,0x40d6226d314985f2f8f55508d3b123094bb544e95187f378171d8ad43143114db4e873424fe0dc963352c194c43ed5a24d29478572d94c138853911b074b34494912ce13580f1b8a54103d270d34c86b),(64,0x578974b4c556d1f2dd165344f3951335d361bd055909d4cd613dd5623cee494272f5533ad0e514473753c1d50b4e4cf4b867318fd570954acc35654e21ce64741f2d51452c4d38d114183f278d54d06d),(31,0x13f57d174dd6555cef43d3d4bcc75754f39d1541d6627d3558d272fd553b54737d3e1dd0d4ecff)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_17_229_checked : PLift (checkBox [3,5,17,229] [8,7,4,2] (2,1) p5_17_229_rows = true) := ⟨by decide +kernel⟩

private def p5_17_233_rows : List Witness := [([7,5,3,1], [(64,0x289580886936058250143284a24500044800183c3c8031c9282a0281909a5401a184d01400c308423e0091e0341a9200c4a008092048c8120040e8f000470188980600a300400c868040020e06002000),(64,0x5a0791b9240d4a4568241acda4845a2851008496058cc1309340813208c94e0492e03e3d0051d12a0ecaa3c5600a871380662715207063348522650806488038c4110fa02c7a30530104b00d86c48833),(64,0x986d37123170a34495908cd9520593384e255040548432d3a12cba40570204f601c764b03d2b0f35882c1cce24a4a94602927954078653505426d0a5441b228d150051318463f00d1f0c34c8432c8f9),(64,0x94db5285b4449741817218cd4f04d2f1035c8834e4b94b83f2b8f55902e1d4e44acab469610ace155867358562750c54c1d230d35085342578224fe03c7e31534114b43ed6a1ecea4c4b1498372995c),(64,0x5aceb49ca74595d09cdd5305d44d4933d3e13cbe415742153b2ed713dd661dce64b4ad471630b4e34649f4395507c8e355441550b5e88b504c74d8472d8fd5b07d3b1332cd693a55e1bd25178a54515b),(57,0x14f5dd1f51d7d5bcef45d4d4fcbf5d56739d1d43d7e23d455ed372dd6d3b55f37d4e17d1552d075d8874f4bd5cd2f2bd1e5942f3951b55cd75190d5f08d50d793fd6e1fcee4d4b5)]),
  ([7,6,2,2], [(64,0x10cd270827221171b0c306108174be534132884e4f80424d83124d80b484325b90787f4386303cff15144028991148a5e84033c24300154145a12d3b00490204c606c0c3f05121cbd04803120090fc00),(64,0x515d402c392692960046355c50a88b4697b1046f3415f094b442c6030550058a54199516cea5040725986130db4f1cb00830245201d4cc6f02120911198c75581c2ad0215d470349c3f58c384362357d),(64,0x7208e4757e1107234d6270c28224b7461a71b4c454c192a1096605e2fd4e7741428d326244f3793f738050cc9448d8412878365680b9bf215141a4ca565ba07c802b90f678643cd4a0409f4018f154e4),(64,0x7bc262d50c66c61308f0545e005ca641d356585c3add102097499871347b3713d5adcc0c492485b01d8cd571bd088832c51268467320f655de6074ac40d92160e7521d70383c274fe4b18d14ce25c437),(64,0x53dde291336285037d405b9cf0d095491856cc79369690bdc0219156906a32cf9569bb7a4202bd1067c653d14b76811281014bd90158e5519747543a26d2a60447359657182b230ba46d7c6a87034560),(64,0x7489849d886d87c3756c73432489b11dcce575be7b0232c913688683dd5879cad41193164e8525777603d2792d638e35c8387248f4797f6b47335163711f20a5196a06e3155478c1a2a50a4e19917cee),(64,0x591f32e5a9555e42a939668ef77d3462ce05bdd00d5256d07a5a9c1459a51acfa56dea2c1a03d5db28530644e65d5d60ed2b608d7599c77d42c2ed1c6ac71585f02d90d670623c552784a74d9973b143),(47,0x1b87b9796bdf47953a5c1b5698fb7addc4c57659df62f1ac7c59d3c9e24ddd34a1b71f56d6c95e7b4b368cf87a1943a5787643e4b9737291f6b874)]),
  ([7,7,2,1], [(64,0x5581a19cd213894040c8110913f00d1e03a3c8031b9260dca207864261500506133048028c20f8f601c720d06848031270182480e31842010383c0011b06225812020c00f0321989003002180060c000),(64,0x98733785a490352815807069351211409d42019210ca118933f80f1e8c74c8432b82a3d0051c1280e4a43c55c0806d3605426952058633384a25d0204c7e310403e0091d0c14b03d2a0241a9220cc9e),(64,0x450255686b359231489f4295706c8634d3e13cba255000447c32534114b03f5680b0793912a0eca63cd5e0886f36927158a34381f22954194d013099411510548033538124b43e80b1d8c30fcaa3dd62),(64,0x494a1431590748835540144bc42574214cb4d8472c8ff5a82e1ece64ccaf4682b3d5601c4dc4a4582951057421230d95105526d0654c17208cf4e8b640d6e1fcea31530104ac3e5640a0753812d170a9),(64,0x4c4ad461650a4e15305d4555b35d4214cbe42d7621d3f2ed015b07d3a1352c51c5a42d3952b4495f08c8e36d4615d0f5e88b554d14f04d2e1055c0813b1392d4fb598773892f178ab4596309cdf5285b),(59,0x14f5e51f5257d5ccef4654d50cbf5dd6d3a51d44d7e23d475ed3d2e5713b56738d4e17d1752d0d5e089504bd5d5372cd1e5ac2f39d1b584dd520594457c2354541d7220cee4ecb75bceb)]),
  ([8,4,3,2], [(64,0x100cf6c033215142e81e3fde018cb5510192a0091392f010935d0493607e30da409c794206c048f315d380349c21d680f4cc0c0b706cfc1800612d2c004903002403cf01503f210b400c481e00c0f000),(64,0x7200e2748d5b843349b30d88845d697e03e3355c0c4bd0850278c662e147070ab3f58c184514c8072597736d2d6f00224520204c669c2a1f10b7b06f30550094153d85a4ec1027cf160055390452296b),(64,0x5b1fb104d057db10d08645505798692ed4a2b90063de1190b6515d4068a94d40a2657a13cde4c1bf0149448d758104a364c96a82d1fd0e7bc7231153694281e9096606d3e45d4f813288f460c5839d39),(64,0x2e54875c1d2b0fe634625f452385337080825d265e207134dc4b9bd249216b482445f21d4c7559a80ac7d4319b7b4703095109941058a53dd8616cea4f1cb044a03c9818405639571118d56d83922d1a),(64,0x255245da05369f5329596ac2e2010f679f01ccc5551a60a50a6646e3e989178ed4fdce050a33d58484c593a13a7249e6e48e4756f7f84434d626d037225185a9f93395d0c9e92f94d088b140d9279067),(64,0xb10d671ee1c552509d105ca63e1878585c3ad3d730a160a113997280447359656dc3a2311b5b5fc345606c83545906655e71a8bc52dda080af4059078865519d52a9367140b269295ee0a140df4c5c0),(64,0x67df11d155668fb62a1917cee501cf29185850e9729ba23d1e5c1ff351636d4387e95e7a8bf539dd08cb24119379468525d82b58e5fa0d14ce24d1c3261275e608375be489ae20d12685f31d8c855da9),(64,0x47e00591eb53dde2cd947657f838e371128825af44da27d0775619d50dd229d8885cec736125ce0235d666e03b471fd58507659e81ad4c76cb0645d64ddc626d2a5f20b381c1496067d8cb569ac0bd10),(21,0x1df83da374e1880d6765ddc71d2b831f756da062e1a3bdd0855bb)]),
  ([8,5,2,1], [(64,0x9c7a4081a13ca21087004098480381b4c0034600b8b600c563782b1f81e130743f0141249c0f00a248322e80716828140d8094781b80e258360102c2d0011504a1c812020900c0261386c0302a12024),(64,0x39833218bb4385b2b8dc0a47c4101c144a43652c1107933019269220e86f3080f188973a837228b8014583802d200b542020154a81d8fe0584b279260f87331813198940d0bc0245c244e40c484148da),(64,0xd4882f510174b0395382150614ca636c461ecce40c1b28cf610d241c4c404464264ec48439230c1450613882f208b74282215caa37d321fcd207d00134a04a0401d4c83f4151a09d3c03d2f80b17893),(64,0x3d129104c9470693c4bf4485f2c8e74e88743caf375301f4d04141d294f84b4453349b3b9230ec8e30d1618ceb4f88b2e50c164ac38534204d4424212a52a1dcca3fc171a89f3c9270fcc746867254e8),(61,0x11f4f4fb465414dcd73d51d44cb34ed31344f93bd4223d174fd0d2b5353552b32d1e1acf346ce94f089444b14e50729cfa4bc4733cf7494c5460653b5402351538d3620cd642c232ad3334d01)]),
  ([9,4,3,1], [(64,0x22920088592e07c050aa500421e4d8044700183432803188f80c490150824601a144b01200c2883a340091a02c3c029220201e8122a04001032320011805220018028a00e02a1e01000830140080a000),(64,0x4c069178f40b48c4882416cba3c550224e80847e058ac508441ecda04d701c8a9420410d8cc014643e833248c9184c0158844681c14cb25204a204e00640e2903c3480b5a06a285000e4980b85c3c82b),(64,0x985d2f0f35488b3a92108d802e5441187d370155c8742ad0a50443365381c4ce01c663f035250cb4a863308f9560912191c078552d14a130833891906d782c510124a60f8d40356a1b0a34083b268d1),(64,0x544e95187f378175d0762b50c50c4536d3a5c473424fe0dc963352c194c43ed5a24d29620c1478572d94c138853911b0757a2cd125244b384d603d6c1b8a54103d270d34c9691ad01580993d82f23924),(64,0x49427610bd54ceb604af4394511cdd4f1731d50b4e4cf4b867318fd570954ad8a30d59538873991d07d7c2d51452c4d38d794456e29d060fc9e355345ac6d5889b4c52617cbe3d554234ec48c25608bb),(64,0x55cef6157743d3d4bd8e31d5d62d4f39d7d4556f41d6627d3558d27618bf554ed60d4737d3e5d4774353b3fd5e25d2d630c556d8947d7e2dd165344f3957b44cd74d96d1bd055909d4cd613dd5623cee),(9,0x16761d3f57d8d5fd174dd65)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_17_233_checked : PLift (checkBox [3,5,17,233] [9,7,3,2] (2,1) p5_17_233_rows = true) := ⟨by decide +kernel⟩

private def p5_17_239_rows : List Witness := [([7,5,3,1], [(64,0xcca256069088d816094050ca2444a40011200060f0031c9280e4a80a064269501841a34050030c2108f8024780d06a480312802024812320480103a3c0011c0980600a300400c868040020e0080c000),(64,0x2c9681e4e81b9240d4a45686b09121368a11691008496058cc24c4c40813324824e0492e03e3d0051d12a0ecf12a9601c42a3806654863070d226452420192200e310443e80b3047a4c0412c0361b122),(64,0x2995c1b42648cdc28c5c5651208cd9520593389513904054cb2113a12cba5c0813d8071d92c0f4f32b1621cc2c4a4e22a5180a49e55065078d426c545450a06cd122940144c6118fc034c31f13210cf9),(64,0x56d14094db5285b4449741817334864f04d40cbc5c8834e4b94b83f3d4ae590750b92b390ab5851a0ace1558673589d159534301d34c8c5085342578224fe03cc51f934114fb2d16a1ed313a8b149837),(64,0x4d4ee2d56b3ad2729d5d458273754c175135253e13d052f9742153b2ed713dd661dd2d398ad58d1c0b4e34649f5550e07cd5239441550b5e88b504c74d8473f4b65b07d4ccec2cd693a46f494de2945e),(55,0x14f5dd1f51d7d5bcef45d4d4fcbf5d56739d1d43d7e23d455ed372dd6d3b55f37d4e17d1552d075d8874f4bd5cd2f2bd654782f3951b55cd7518574357c235435e4ff5b87f)]),
  ([8,6,2,2], [(64,0x10cd27088809d171b0c3061087e0be1754d04ca21393e0109360c493602d210c96e47f0790e18c0f3fc545100a2648a5e84033c24300154145a0184b4ec01240c606c0c3f051108872f41200c481f809),(64,0xe52960046355c522c2a5ed1a1060a3406f57c252d10b7ecc118150059062959516cea50407259861313c36c0272c910c1201d4cc6f08208511804c719956070ab4085751c0d3f49c63052384362357d),(64,0x588890a1182dda71b5fe31153065092a1f9660bf1794e3b414774a34c98913d3f37805738940cd8448c4a84cd91e1680b9bf21514810ca1a5ba5648007d0f2b99e190f3528104009f63c553900b7509a),(64,0x4d45c894eb508087449761d26136164f4dc1edcc5ac920c5216c07681ccd6f55c20c22448b1809a13206755cf6075e62b10364858520e7039d73f89d0f18d4b053870e25c4372397e47444834d31c9c3),(64,0x7008645605690cb1a9bb568f9081e9440af67c658b8f452c11404a06412f15a1f518e57557426c3a4a98111e10359c65948c0ad7c46cba82daa34470580267bcb5431fc66cc2185513c0177810729996),(64,0x16622524e8761772783d6392d874e35c8387248f5fd1e839ad35073711630a5f2464b86a06e7fcc55501a78d0a2a5fa6653817e2853cee778a44cd8a14219500df73d6e2543461524851b3368795a42f),(64,0x759750ed2b60a1135dc75982c7d51c2ee0c6ac71585f02d90d7f59c18a2b548f1784a765d36898ec50dd22612785db63747c7356c0c9226c477820ce6f95d08dec44cb280da21a231560f779cad41193),(64,0x7b4b368e323e1e8652233a5d95e03e4ba1e5cdca47e0f6b874591f32e5a980155790aa669398a4ef77d3462e1a381d05bc35496156d07a5a916819a51ae3456cfa7a8b06822f3d54c76ca164530880e6),(45,0x1f78b5b87ba33891796bdf47953a8aa1b5c1b569a353edeb8c1dc4c6215da1259df62f1ac7c59d8b0f27893789dd34a2186dc7d5b5b28255e)]),
  ([8,7,2,1], [(64,0x2795619c1a3484e2501032180244443f00d1e03a3c8031b9260dca207864261501841433048028c20f8f601c720d1200c49c06092038c6108040e0f00046c18896048083003c0c866240020d8060c000),(64,0x98de169240d4a056069070d46309d14108064843298224c463f80f31c7a4c8432b82a3d0051c1280e4f12915c1b420360542695218c163398625c4a408131f8c4100f8024c11d12c0f4a80906a48833),(64,0x27c5255d0a06cd32193e13cba61095400113247c60534114fd2c1681e42c3912a0ecf32995e1bc2249cda648a31590e07c8a55065341882644c54504054cd20138124b43e80b30c764b83f3dcaa58873),(64,0x32d834d8473fcb25a87b0b9333999e2bd1a0acf5580714a4dc650a51615d440213648c510556289b54d0605ccf209874e84b40cb65b87f3a8c54c0413e4ac590750a12d380a9171140955a1ad233598e),(64,0x1f5353a1a02c569470e54ad9629d5f4482336c8e64d4615d0f5e88b554d16253c135052e170205393b1a42d4fb598774bce2668ab179634582737d4a16d25640a15650c074d52218d50051424bc5d085),(64,0x45d4b6450d5e089505ac2f5754dda22cd6b4782f39d9f46d6137595520594457c2354562d075c8834ecee698b75bceb4c59c2b56546029385995305d4555b35d8f5085342cbe5d8874fdaa2ed854056c),(41,0x17f6a54f5e5ad68d1f5257d5ccef69d9d4654d50dae2fd776ad6d3a5a14759744d7e23d475ed3d6a0b95c4ed6956738d9b5385f)]),
  ([9,6,2,1], [(64,0xb48c4b05b068ba12082040b05407f0f8de0346c0d0d400c62408312401e1608649855050b41080a2a838360071982e3f02b228182000e2b83c01032348011805621012020360b05a1f80c008301502a),(64,0x19c26319000bc8e4b85d070fd2f15c22c4a3a8191e0b254881100e003d802bc6e4383d270d6014644103334c924c861080c0138884a057058b655885110e404c722b03a368095e8a91a1080dc24178fe),(64,0x5788d1312d3b01b630bb1e91a1255420ce2045822c470545100fcdf2793e1b4cc41835354944d0630890330962244503c01f4a8592e15821c4639815618b51d11410ca23700b5f0ab1a90a0e4d926138),(64,0x1e5842cd5344841384a0605401bd0f3396e274d74d865414c459093149333c821648c113d5a225293a017620b71d95745845394a4510735f8ad4303b36c9a5ed3a1a428424c85a0973d8254c05f3fcbe),(64,0x38d8350871444d05c09f4fd9e33507598954d4f408d9430d63488513c52b628b95651811ce729987518754557428cdd5f53c1ad0b3296a265393e027660c74056023d2f3b81d638bd1f15d4704b3ad4a),(64,0x29d475d53d670cb5acf9665613bd8f5387d4754b615135c8a1505a033d6f4dd9631565490533cd934855b3a5895207745d76295455fd0d26d3b3e829668c95a4f74c5902fd5f4784d3b58d5307b46d55),(27,0x1796754f5cda165d25525775b4fb66d9147d4d50da23457167d673d59548d8b46578)]),
  ([10,5,2,2], [(64,0xe8b71d8273cc632a018391b028c544801324045444042054d100bd0b4722b97a1b41e3a85a03cdb12d17028870f078510372d02429415384511090e0047e1bcab06c0c360480e4a20483f1b0090d800),(64,0x654884154a0f4ba618790a9453d838708b519932094e76cca615d23059ef3889357c5233d1401c84540438710f300026307f0c0fc5f470084ed6e4ac17529070993784e4680d798d922956124c61ed47),(64,0xa2013d171191b62a526065f2394966c562290558b921348146789154c4687d1230c0563c820cd4e3fc4172cbe4ec2e600733c1bc2bc605ed2c1b81f7e0eb2716816d1d041e93708d5644c895183240b),(64,0x342224540864885545021121d739103058d4f8800c60a3f5bf2c97e4bc71089fb3b89f6e96b2b45e8dd2a075a7269ec37d5c13e2846ccc039e7660da55d08129d431d891f1483e43b714b81a5844d477),(64,0x1863a5f12d081f96a8ec275691722b478117a99b3748e5690b1362675d1932996226134194b0f9c82ed874e07a0ae04518f770d742d86790133099f53a1b4594a716231490d505df0684e32516014ddd),(64,0x85958425d53218a1f5493e9c65dcb91aa43615360a6023d572195b72aa3449c1a7cda4398976c96315a2f7812234d9f2495411e207451331190504830d20d53d00730bf9253c0bd811d1fe3c5bd5b8b0),(64,0x711751a2414d1f63a5b5598598c9e3494d67c5a225561778d188d1664c868415240e1e73cc29318e4fc3282cfe700b38f57f4c0237f1ad3bca06ed6c17e384ada826ded3815d142297691c335e86648c),(64,0x5e06b9113780d736e2354a1f46949859230784d468155885d23164f645420d60e405cd9293d608f26f96f18a3b4b9fa6ac9e5aa2c47deb6708f8655b43227760cb65e1441d4c724bc919884e42c814f8),(64,0x8257991636699e274e5050e0f92e005c23c6b22d6761a435d9855ca91d3a81976909f759e33790d768ddf89194845047424d5020c7063e4c5fd6b8a15b6396a5ee57a2a76cce66a17429d662e083edc7),(9,0x21b921e584a4e8fdaf77218)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_17_239_checked : PLift (checkBox [3,5,17,239] [10,7,3,2] (2,1) p5_17_239_rows = true) := ⟨by decide +kernel⟩

private def p5_17_241_rows : List Witness := [([7,5,3,2], [(64,0x6cc4c3ce0427433510843781e4bcd91bd80064c00245a5ac042adbc154fc0f09639df8244274e0780492318d74034b427db0124f00c0db06d2c1b00615d68004a83902403d201809c360181509003048),(64,0x870b5570a56d84f3da07280366c44a51cf121d980c4e1085323707260c1c4b4c37506d4505d5b8072b9bf16169008ff840a90fd50264ea7ec940a93b3947b6302533015498665dc10484b77206142051),(64,0x8149e66c34515ec2153537c756181f4c0c6369d71c181069178a0c15c40a2c5c216d6c015022b0426f45654cfd6903d3b5fe25c2d4f8e81f9f92498f0a13933de01e5291a57a04d242e9cb191750390b),(64,0x1b9157145e5bc08416162bc45700595596a402112a9a710151269413ac817f0956482b4f0d2399e31f18d09a343357d059272f5ce19d780450e48a1f2e1c91895f425b9148f9828a30e5b41354a3d08a),(64,0xb93f354e97987f7e9900a53a8dcd07847a4a9d11a97b05111496222edcc195625d90c874b65760d299b71414d3dc8d820a1678376c9483c9ef221990c8e2624224ccc9375da1cd840751a4ba2b311d5),(64,0x1a1655e50f880b97290a6e8533ea0b291a10e9b552cf57c88b8199c0d5467b4864d8e07747661c20475318b8c776071609188a4c25c80b864b270c5c5656d40e142b5aa10dbe550fe6943e3b9ff26195),(64,0x6e14e3e1f523a0967c38525f02259a38d8a08d348c4ca76c746151b8b0c5759167185f5c10685cb06b44670557406126a04154a0226d423b1e9209fd64c2c4f63a34de41f58e8d4ce5f8174a2252f9cf),(64,0x898bf7416644221585bb3ee0c6883b531f32319d7b937778776211e8bcc8765198a973868b371104855ab11155698ef801960bd408f4d679c8064638345e24add21ad7c44a232f1cd58d0d8795e838a7),(53,0x1f78cdaf7ae3c89d6768df477d1f8c21b56dac65e3e35de88e5d344e245920f53df623da07c58b8c8cb7711c8b5c741e186b847561a980d437a8836523b351e58d97f)]),
  ([7,5,4,1], [(64,0x329ae20c2a438b8060fc2d45c50015280061292e00c8e5c847348321f0c069079081041900e3c8524d80b25840211680f4c80a0b6058fa168484b0012307a2f81e030f01403e208b4008461e00a0f000),(64,0x110885b041331b02142c5a51032470550292e81a3f8b71794205cfb2898616ce60204c4c005241741252d351b8234344607e309a61ec22418bf1994a07caa040f415138034f12617c144dc108865a83f),(64,0x5582b43d9a1bcbc071002e460510fd29188175413a1cc2844e4c8072497612d2f359ba23c365cd1a34d5e0cc80311a81f424420c11a1a553021414ac64065048f61593a03cf32697e14d37379c225d22),(64,0x28d8739d34024945e04d4c4d86f0910e175470d56e5600d519319aa1fc26428c31a9a75382341cae6486752dd62acf81613c044f52718015539381c42657d490dd2296e10cce6c8870b96b448cb1c9af),(64,0x6ed620dd1b57dac2050c3146c6a550095092c1941a54d760ad6453e04cf7608574ece27189b5fd2637dc348d70114d06d0890c16d450cd1d1b15602d4459c1c555408bb1894606cff2998a17d433a9ce),(64,0x4756131d5209d0b2c9961ad4f768af64dd73e5841653d391c8275814a0e1715256d88b5bd1633c766cd5a0bd136787355d9b2f548075012a18c185453b1d0295893a5cd5e84f4ccda6f8930e977478d7),(64,0x45da21dd5b67d49750a9634ed7457b36dbf5983b47d636b50d6606d545dc2c5957653f7289f60d2a38dc749d71345b557031455a01d559675036386351cee748a762ceb73d35700955e520365bd59039),(25,0x1a375567665dd72d2b575a163cef74dc14856554dde2cd9776d85395c94a5b7)]),
  ([7,6,3,1], [(64,0x5483b2e9901e4223e0602b0143a8a914928044061111a00c8256041300281d0b262071068f01600c3884a480092203c1e9500e4b8080aa048e81404246001200722c018028e0120782a0101007002000),(64,0x4207e5503d2f1921ec24544fa2e4624e021280ae058ec2ac544a8133a4925a05134046470052115a10d19309982042a400681d8b462873070f22c45a4c0192600e3904c4880b3848a58049320300f87c),(64,0x6453a08cf928978184ee2b4564b0153ac945a8534a4d26a0914411e01c865704546cc4668830b159408c11a9400a4b663075078f42cc5c6253206cf126970164d83984e4900d38c8c5884b329a022432),(64,0x6a8935a5123455e11d1d3199c2142e56d0430c6c665420ad0160069638773d8b51798b4d01d3cc9c5c85b4c4da6c0994980f3948e5904d48ccc6888b0d161428c9520315583f2f9941f42654cfc2ec64),(64,0x575063146e66d440b5036086b504b76353607cf52797417533371b226d71364e75984f494ce6908d0d963430cb6854a0cd096587f554fe2f46664d3c094fb2917a18d396e0a12bd2e05ced2596c154d4),(64,0x5b516355ab44d5f675460bd056106d50d8163cf75d85f4d4de6d09d5ccdb6c5276988f5950e335a35303542d4955cbf6553e09cfd2997c1953b6e8a35e4ef5b8574b4d66b0955ad1434da94451f67887),(55,0x1876dd4f5fdbd6bd1751d855dcdf6d5a743d4d4fdbe29d7d6ed6f35dad4559f41d861bd4560d376d89f5d4dd6cd6733da5538374354b65cff5f8674f5bc2957b6e52f6b897)]),
  ([8,5,3,1], [(64,0x56069088d816094050ca6009112900044800183c3c8031c9280e4a80a064269501841a34050030c2108f8024780d1200c4a008092048c8120040e8f000470188980600a300321a090040020e06002000),(64,0x490a45686b09121369902845a44021258163318224c4c40813324824e0492e03e3d0051d12a0ecf12a9601c42a380662715218c1c3498826452420192200e310443e80b3047a4c0412c0361b1220cca2),(64,0x8cd952059339842544e4101532c846053a12d012e970204f601c764b03d3ccac588730b129389982a5180a49e55065078d46289b151514281b3448a50051318463f00d30c7c4c8433e4b25a0793a06e),(64,0x2f17220d396a0b94b83f3d4ae590750b92b3919a2ad614682b3855619cd66309d159534301d34c8c6254214d095e0893f80f3147e4d0453ecb45a87b3a9a02c5260dca65706d099233719228c5c56512),(64,0x3dd661dd2d3999c2b5634702d38d994658e27d554381f3548e62d441550b5e88b504c74d8473f4b65b07d4ccec688b35a55e1bd25379942945e56d14094db6454a16d1161897418173348660d3c13503),(64,0x5385f4554b61d075d8874f5ac2f5736a59e2bd654782f3959b46d5735d8d518574357c235435e4ff5b87f4d4ee690b55aceb68527658a75751609cdd64d4c17513525854f84f414be5d0854edaa2ed71),(39,0x17f69d4f5ddad67d1f51d7d5bcef6959745d4d4fdae2fd756ad6739d9d4758f43d7e23d455ed37698b75b4ed68d5f37d95)]),
  ([9,6,2,2], [(64,0x7088809d171b0c3061087e0be1754d04ca21393e0109360c493602d210c96e47f0790e18cff15144028991148a5e84033c24300154145a0184b4ec01240813181b030fc1444221cbd00c481f8090fc00),(64,0x118d57148b0a97b1051a828d01bd5f094b442dfb3046054016901062959516cea50407259861313c008db2443048075331bc208214460131c665581c2ad0215d47036373f49c63052384362357d10cd2),(64,0x7f8c454c1990d092a1f92fd981794e050ed774a34c98913d3f014de738940cd841292384cd91e1680b9bf21514810ca1a5ba2015907e4943cae678643cd4a0423a4009f63c555140b391d4268394a580),(64,0x3707b730925ac3196d216c07681ccd6f48357022931122c602321a119d57074f6798ac8f503648585200e39e383f9d72743c634534b21c389710ddc82397e1111d834d31c9c3225620a252460b769c6d),(64,0x52c118ed01768a0640564bd4687ce57549b5d03a9912a60447840d67188c5942b5f25546cba82cd16a870580267bcb59190c7f0c266c61544173c24141de02999617135894eb508087449761c4d4993d),(64,0xa653465f22e1a81b9ff3155406a44429e32a5fa6645f4e14f8a0ee778a49b533628505021937dcf2556e0d18597924850da6cc795a42f7008693d15814cb6906a6ed5a080f9929107a4af67c658b8f4),(64,0x3b143748986226149e17375b61f1cd5b032971226c477820ce6f95d08e4d44dec2ca0368868562313dde72b63e4119316549888e88e5d8279770f58e99d2d874e35c83823d7f9611e838d46b47371163),(64,0x855b41e96a7065045a066946b56e343ea4b7a8b06822f3d54c8f1db285919a930880e6759750ee654ad82844d771d660b256471f52ee0c6ac71585f02da47435fd6706254a2b3c642784a765e704da26),(64,0x78a714de2774e624a2186dc7d5b65d6ca0957a4e7b4b368e323e1e88fd9488ce9765780fa684ba1e5cdca9651f83dae1d164951f32e5a955645790aa66a734e6293bddf9b93462e1a381d05bc3597d25),(47,0x2369b1f78b67298db87ba33891799a65a6bdf4796744ea2a9be1b5c2606d65169a353edeb8c1dc9ad318857699a1259e577d8bc6b1f19219d8b0f2)]),
  ([9,7,2,1], [(64,0xcc9e55867068d213894040c8600911100d1e03a3c8031b9260dca207864261501841433048028c20f8f601c720d06848031270182480e31842010383c0011b062258083003c0c8662400c0083618000),(64,0x3785a49035281581a41c484d46309d14108064843298224c463f80f6d8c71e93210cae3d0051c1280e4f12915c1b420360542695218c163398625c4a408131f8c4100f8025b0304744b03d2a0241a922),(64,0x708d32193e13cba61095400116e0c91f1814d0453f4b05a0790b0e44a83b3cca65786f089273699228c564381f22954194d06209913151410156f0cd20138124b43e80b6c8c31d92e0fcf72a9621cc26),(64,0x4cce6678af4682b3d5601c529371942945857510085c83648c510556289b54d0605dbe33c8261d3a12d032d96e1fcea6d0c54c0413e4ac6c5641d4284b4e0660a9171140955a1acd66389f149574281b),(64,0x239935185743d7a22d55700d16253c135052e1bd5c0814e4ec690b53edb3598774bce2668ab1796345827738df16d25640a15650c075c43548863540145092f174215ba32d834d8473fcb26dd6a1ec2e),(64,0x7257c2354562d076fd7220d3b3b9a62dd6f768eb6d531670ad595180a5d0385995305d455c635d8f5085342cbe70d7621d3f6a8bb615016e56c1f5353a1a02c5694702d750e54ad9629d5f44823728db),(64,0x535c750dae2fd776ad6d760e96851d7559744dcb5f88f51d7b7053d6a0b95c5dc3b5a559dd238d9b5385f45dcf52d91435c55e089505ac2f5756ed37688b35ad1e0bdd639d9f46d61730dd6554816511),(23,0x1af7657f6a5dd74d4f5e5ad68d1f75dcd5257d5cdde3bda776d9d465d1)]),
  ([10,6,2,1], [(64,0xb48c4b05b068ba12082040b05403e3780d1b03435003189020c4900785821926154142d042028aa0e0d801c660b85c3f02b228182000e2b83c01032348011805621012020a80d85a1f80c008300a800),(64,0x319000bc8e4b85d070fd2f15c22c4a3a8191e0b254881100e003d802bc6e4383d270d60146441033690d324932184203004e2212815c162d95621444390131c8ac0e8da0257a2a4684203725824178fe),(64,0x6d8c2ec7a468495508338811608b11c1514403f6c0df2793e1b4cc41835698d52513418c2240cc258891140f007d2a164b85608749ce6055862d47445043288dc02d7c2ac6a428396a8d92613819c26),(64,0x1bd0f3396e275a835d3619505311a559093149333c821648c14804f568894a4e805d882dc7655d16115b6394a4510735f8ad4303b6b0db2697b4e8690a1093216825cf60953017cff2f95e2344c4b4ec),(64,0x8d9430d6348851708f14ad8a2e559460476e0e729987518754557428dae3757d4f06b42cca6ad6a265393e027660c74056023d2f3b81d638bd1f15d4704b6f0eb52879610b354d12105b2384a060540),(64,0x658c55952414dc43cd934855b6e8e9625481dd176dd76295455fd0d6b56c26d3b3e829668c95a5c83dd31640bf57d1e134ed6354c1ed1b555b438d8350871444d06c57027d3f678cd41da7598954d4f4),(64,0x5cda165d25715bb525775b5cc3ed9b7259147dbf535b550da23457167d67718f56552370d8b465b95e0a751d756bd3d670cb5adca3e599585c03bd8f5387d475bd52d8544db35c8a1505a033d6f6a537),(7,0x1a371d79675cb7054f)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_17_241_checked : PLift (checkBox [3,5,17,241] [10,7,4,2] (2,1) p5_17_241_rows = true) := ⟨by decide +kernel⟩

private def p5_17_251_rows : List Witness := [([8,6,3,2], [(64,0x2d6580cd74241020795f3f6a01ec196f0d81980469cc3186044803c2b90b2a64c09d682101254c6f035b03305a2dc557e1140c0ff06d5c1e00618c01690c02ad080900f5406c2d0fc06003180a803054),(64,0x96df90d915ae0930c5d43c10508562402a31f81c6fd5d36c79871381a4076a8c61900281da548cc19903f6009c2c50e2b24f0a96b426ac21c25720e4055561c8106cd5133c6d8412c1205d2e8587ed17),(64,0x6a1f6f53b3667c6600a6b4c919c05829a8498c418a678144260d21b109f0f5e0444af9482d5b90c2aaaf9348a0a1cb5a4e721628511591d4136d9543487003a136c52f3367012d8c2f45b7f91a2e056),(64,0x2342b7396c42aad3a88809a2b72547396880595735473046166d1524c8d01ba738444e63d2db40497b05e8051d2ec59979fc0e57a460b6aee592583475d753cc918d16540ea62041f709603faa13787c),(64,0x265fa0ddda5e116ae4f6250328ddd53c69441aa9089c558d01a90e11fc1d889c05793e3707a9fe1d66d39b706a0220d6ad2931c659aa08115a66192430ac7994a2101e36049d900b29557143cadaca50),(64,0x9a0a5818437998448ac52803e90de1448b0ad6530b9d15bd0dac0ed9388b0a62e7316a528e821a8b8a545ba15a052196dd554d4d31c676850516c9924c0ceb4e71131ef634be172617fd7d46cb9afa5c),(64,0x9d21213df26412eb444a7b45f8091e2f2c197dfd0e9dd5ed19af0f9968970d63a761763d092a5e3559904a9c820822570d61506a237c7da0a206f99e4f0dab7e7d6640b6b8ca1a26d82da962527316ca),(64,0x6853f376e2a021e6713ab746b839ac4a8c8b366b824467a587496c8998a3106467918227a412ce565c910ace512382c8c5cf5b54dab8eb2268e8b1ca520e6bae8905dba560d61d27985db565533346d6),(64,0xbdd25c2b13b88ca462f7354b3a6eea322a51ae956c77869b84d8d4b6677854527d5934c6d49c84d7c18e2fe628017e472bf9749a0e23d76d79ae8f72569a8e1d63ca9541eaa08dc6592a538880a15c1),(64,0xa29bb35e7a861964d2d79d4507cd91b49ee80d1fb0a600edde5f2bd3e898a763b766988d967aa083899c4508e0b96838859f4f6e09f99a6bccb9ba0c62928b2e6929844925e7616c62864478913ada54),(64,0xaddd33be928c14cbbe8dbaa1b4deda9e0537d994b55f198d7fb009b8f9dc3e29b8e696aadc738e86891a2502e3a059db7a0f4aece9b0477a988b24a491de590a575ceb423e327414e3b2f1a3e2d526ec),(43,0x29fb9e4ba4ef0b6df78fe9ca1da3b92cf7ae488cd4fbca90bb67b65ed87d2c377cfba7a3ca662750ee6a11a0b866f62ecc29e4a7a245)]),
  ([8,7,4,1], [(64,0x418ab8e82a578823d018530f1a0070055a43200617803648b616dea43832290fc28630081541e1421980b668be150ac145e0410283c8165286e0105c00590288fa0780c50064148aa3c0140085a02850),(64,0x8f1e10b16041694210296e0dc3d81a538f31c8176994b3286f7f9220204618005650b8175ec645102d6440d168230a63f8a38c822558fba287a07dae34810510680359c504c0195f44603c158ae14de2),(64,0x69524326581217c18807658ba17dee64d122de467ac365a90fa788e0cdc22a0e6400a58d024560fda32311f0216c155350798212c049461a80f67943308677d99b468bf9383e5c858258b0155e4420ad),(64,0x6c957a2cd61ee0a6bd2e34e62521861b01168145310697e19d470c1941f510174466a82603d730b215de6428af8f9e30b96241e968ec860adba57cde20e123e136071503d6841d0196a14da04cc1c600),(64,0xb5bc5869538085851b94e0dd9b0f7a187606daa53e8333873809a7498cb969ff1297e48c09ac99811dd62f0617c195450b9921ed0e16c446a0914900d5c45a4e82361c408a78d826568ffa3a331f823),(64,0x5ae9f3a88f879c32a63839e7657101a4235200256d159a34d81f60c6c53035664825884b413af1a251cc61adfa67d1e30e527dc425d91baaa4f2683f73973165e825e26430b1901e50c164426988f488),(64,0x5d6a926628734b3909e75990ba6a3f2282f6f963a5ce221e166ed3a37e6e84cf9a2137076c66b151a14d01d6046a5283365c8044c60125ad259125d85f4637c997458bb929ef0e96e44ea291c920ddc6),(64,0x60927ada5b12dda5feb3665d72f64c7c570456a4924940e5c85b6a13b091881c53a67887503a4a3709db656e8f36a0e6cd3235e6682d8a4bebe98d4961c6d7f1a1480c5951f911178476ac9449c105d0),(64,0x87e399dd5da4481841b54d0d99a20d63131b0265626bd68cc7959fb5e91faba532784374977aac9b8a9cf7a6274369c9043170165a64e4226186f53c3867085539b226d54e871de066ad2a33e5e80c4e),(64,0xa4db736e6a83d8e4cec299d8bafdfd486b09544575179ab49d8b1d18a64359e9b22e1a6fd3e9ca174eeca9be89b1dad34660815844a6b89744d77181ad5d97cd17a9a4b0edca5bea33b893889c73ae7a),(64,0x8967d9ad8fb0eb17562d86d3fb3a73b2e61616b9776a772cef9fa239ee114d6c49a58db06575eeaf27e2e74e2ba75c1396748653db3271b26074aeba97c4f77983adddb93571a9495891c93b67c88679),(7,0x27fb162f9d6cdaeddf)]),
  ([9,6,3,1], [(64,0x2e879640223e0602b0143a8a9700520452824006110034688210558300281d0b21c588068f01600c3884a025202203c1e839540b8080123a0500104200518200722c018028e0120782a010008401c038),(64,0x64951090fa2e5d0188214e0a02b8163b0ab7085404d2a3a600248515a0d0118054708410d5a464c2205980a9001a0762d0736281c3c8b17205a065302600e1300b488e17e08a12560320300f87c0ed52),(64,0x3ae02704945a929348916a11001d1e218455711b31083669590b102305d81a829500b61d58c078f42cdca6245c06d323c608268595c0d83984e0352438dfa2304b5892132889680324207e0f5542f07b),(64,0x60077638f62d5cc62c5e075343ce0a7249c16d724c4da265b003d26395fc2384d591237e4cc22da258434428c9780315203f558be1f59454c263f0bb74991190234e8f9840a2185783b8ad710560552c),(64,0x430cb789a10cd4a426201fd96554fe2f5d464c660953c3ee12744a418d7a4e4a16e0af718174b8ed811c3258555b12b804d424daa5a512345e811d5e474c62159c56c2e410c3769991b02b5090186069),(64,0x5e4ef819c515d6e4b603358956b16b450d37a9a94462847c876795d418c57719b1b82d51103869d91ad82504b77398d07d363d60c2785d5d133824dc26db25c4d97c0e77f84f599257ecce235a458c36),(64,0x6ad138a9e957cc77799d0bd464161c76c6d611438658163cf7839cd17d764d60b3789d6d17336df26c5277f48f69965438cd791a30d54c42e227854955cbf7599509d3e3f61474ca61957c4ee1128dba),(64,0x29dbe5f5bb81d6f35dee6b5158b1eb8a59f41e1e7746f6194586d8373d378349f6d975375f46cdf17fd6733de6694375390d891e352d973fe16754675f93d84ca56f17b6e5c74be0525dae5b516355ec),(39,0x1f789dbf7be2d87d876ddf579d4f896175fdbd6bd178b9ed8addf51e1d6160f5dcdf7d9b57cda743e267954d88dd74fe15)]),
  ([10,5,4,2], [(64,0x312850fd95295140917a43ed02281f780f00246f011c53546a8ad3b12cba480b59d830618960556b041d1384603185b8712c0f1110857721c061b001708d22dd1d0b4125a0781750e078031a4b403c00),(64,0x874426612dbb8a80f5fe09d7d44ad32342278d78ce4f3222495640c1c807720d81b4028b9c3e113e34e94139a42f5232e2790cd8947adf2642e7bcff0616e1f81375169ca8e41e63a528633245e87d2f),(64,0xac875029cb36c700163171b87504d61ae978b05169d3cbf44c834c0498bb9f036631212dae29dc9c0c5f261f48408979601b5c481059d75b32d39c7c0463d74b93534e2a8db3198cc186224c8c717288),(64,0x402c15d084065da5bf303a87f052407556ae5b2b540e51eaa68edb652f0c33c64894ca17e8b8804566d30316f1a18ab1020165b5729a674682a60115b5890095e65ed10cf2d13d88b0824c787a2570f1),(64,0xcfed43e48e08e4f79179e973a57cf4226b59295a0371b738de1cc088d1c9e29443646ea6a2f151c4e15aa4fcd4c029513e10697664a4be9fc3963d242e6e59e89f0d1f56291fd2ee04149a0be5b7c3b1),(64,0x40c98b1259071dd5cb333b48205e437616de672e54ce81f6a98f9d3e51b9538e3c3ea46d067dd6284e0cd18a8e88c4867933322f4a24ae87843811994bb5abbca90fa6a7ffc060d18b64930a1e95f913),(64,0xea33d58ad23dc8cae24d78ba3574f2c7ab31d80b8ddcce3547370718c85771f886b54235f03a622d14a136a13dda6fe1360e307cfa099249cbcba27d288377e18d48b4eb8d089e09d0ca5e7cd88ed349),(64,0x919db5c39ccc5563ac80ab24175b976f32c544e6c4aa78f1b753378c34d019691899a14d8cbbde8c2c62111a0767131d76f2a1cac1066d80997f0f5829e6846edc0adec60516d0ad73f09109a5279d7c),(64,0xada4b56c0ec71cfe40df1d2a08d5cae2db0514dac1a9b8c05585b866ad40db301a5850845a6f4b674a8bfbae800e9fb64125d46e642e7b28035985f662fb7d32e14189bb1e5c7c7b2406c25d7362141a),(64,0x6ff2f550e9c56aa8ff956e94fdef10a95b51a3768a53933afaa3e241260a67d34d82f5a28af112708159af1b5bbc0aa9ae00f058446745b68940a6557a97feaf40596d53e88faee50797a6ced603d721),(64,0xe915ec7eb41de387378e520ddc269e8cc58867896b943dbf04a6453851a9f576abfe0f30bd0a0d934a354ba67e28c38991f963bbad3ee427aca97df4ed74a412c59681d77973e7f343b883abe447679a),(64,0xb0d76cdc8691ddce773255cecc62ad90b986f552dfb13aa1b8de70e3469289da24df63be28d2c8479ce08677c9d7af32b66e80fc4d6669472dd0b1ed60baed0ed83f492afa537a3a9cf9633e324ae64e),(64,0x9c606f1f5c9b3c261746b6c95959ebeb341598fbc9ebc947a758722adf1d74391382a18db8c6c546dcb07a705685dacf636dc0a12f4f684aeeca043b7f191ef752b9d0c286cd989f7ee34d41ec8977b3),(64,0xd10feafe54ea964c96bac8239e3d49c2a9f1661a6bfdbdc215f5b6bf468465355ba8a4995faeef5042acb983b6b19dfe83353beb09179b70155e0716aadbbdf311dde2a4eafba404a82da0f3361bd8b0),(64,0x99bbcb33a1ac5c1e0b17df6fc833cdd8a72f234795fad59f28af723e4aa26cb73c2218f676ef52ed7f7bed4d0db3a63ee6c9ce248e7958c66ae6fb7fc537aa4da3d92f92ce74827cad7e6ff16de7bbaf),(21,0x383f3b29dd3daefecfc6b80d9675f2fb0b0326c2e1bf7371f5f56)]),
  ([11,5,3,2], [(64,0x131b33cc9d81033510840792f366401bc19600c00245a0116b2ac556f0fc0f09639c917e0274e0780492318c0d5d0b41389f125b03c03006d2c1b00615c015a0a824ce4091201804b270d80605424048),(64,0x12a076c436c61473c65821c31660e108532372431c81c60d2da50c31b5d44505d01d6e2b858009bf5a6d03fca98403f540993a8947ec2a4ece59307b0958c330154986604177486882dc6172108144a2),(64,0x69d7606e845cc18a00a5c4b116c057096cb4d022b05684dbd10b2454cfd9903d690977f82d4f8e824a4f7e47e0a18f4e6a033c79781291a4135e924a2cba1900e72d75b710b2d61c570a513db63d8a0),(64,0xa8e4d3487c099e3636f4336340597d49e8e2f467045ce5e122b7e89438b818a1f7273057d099c0526e4f928c4d829b40e71b528f427a5b8148a0d19b516ac215ec4d4df9187507d864c0daa5e4131870),(64,0x220327bd99c00e292422625333769a910c91cc1d769844baeba551a3106e8add5cf1159f05e021c55bed6414af16616700455ab27b4556400aa99e11101a7546b826a01504eb256527f0810ad924f0e6),(64,0x955ff0b9954fce9a9a50355fa1fc29799904eaf7a84d01ea37787484aa911a8147457b496e2a31112ec65889cc5db33b7562430b69ce1d576c429850835b7c794d3dca197a08235b20df1967948abe59),(64,0x9720622c357c99c51b03ab4867b7544d8e0a76471d820775874c6eea611d908c71c62e76182cfee9460c29fe2902d72b64b21721970d6dcaad4565032b66a851be10f256a9543fabb9943e6970c3b898),(64,0x54b0fae49b809423b2a994dfd2082c7a5934f6faa924e34c7d8e9e463b4bbd4ce05d7e4a2e5a3cbe1a22573d79cdae05968a43cb99da2072b315810ab1e7114dbac84fa2926182db50eb1c6854b3d6b2),(64,0x538f8ad65f8248e0e1f5c699f52706ac25a225f066b57c04e39282362934bc69b914ca1d23176d85d0aeca591b316828b1d6cf5169f45f71970cb6d7418b09b61770446ca1adb4957406be9a212105a8),(64,0x7132bb555a412c19ae15113266ad55c4abc999a6c34ef95a000bd96502fda9e51358808f5e76474ebe2a23463878b494ae921add25f339b8e8d448bc9e62373734b7963436ca9d21e57ac529e0e6e31f),(64,0x8ede5d32f68d97fb9a902fe2674337b8566442cd9de21cc961b22726ef223ee628303bc75a253309ace5d231f36775ac12ae7bb554de9e9207777988d16efa651e322858bdd9d02ea466808a973b68b3),(64,0xb91139ea24cd564b2e75b1a0fc814fada6023df66835dc1eb17c758c0a4b62ef2a70cb8c9dcd0eed472838b73e9f9c7cbad841e6e86047ca5ae56315afe696a710aea0350eaa950837a994d46fba94d4),(64,0x8cf44a132f9bdafc5ac0c46ab7af52bf23cd36e789f3859ece9e2c9c8e6368f0aad1f4d6f05d5a9f77f46bc11fa1a30d0681b6e1bcb15bb0a6c6b313af70e95d97bfaa835e3e7a34fbe639d2a9374f3a),(21,0x317d4ecfc2f5cd1e87b0f14bfe3fd433b9eeccaddf7d7b08d66f3)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_17_251_checked : PLift (checkBox [3,5,17,251] [11,7,4,2] (2,1) p5_17_251_rows = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_17_key_check : PLift ((∀ s : Fin 256, s.val.Prime → 17 < s.val → s.val ∈ p5_17_keys)) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem p5_17_box (i : Fin 47) :
    ∃ (caps : List ℕ) (rows : List Witness),
      caps.length = 4 ∧ (∀ c ∈ caps, 0 < c) ∧
      checkBox [3,5,17,p5_17_keys[i.val]!] caps (2,1) rows = true := by
  fin_cases i
  · exact ⟨[5,3,2,2], p5_17_19_rows, rfl, by decide, p5_17_19_checked.down⟩
  · exact ⟨[3,4,2,2], p5_17_23_rows, rfl, by decide, p5_17_23_checked.down⟩
  · exact ⟨[3,2,1,1], p5_17_29_rows, rfl, by decide, p5_17_29_checked.down⟩
  · exact ⟨[3,2,1,1], p5_17_31_rows, rfl, by decide, p5_17_31_checked.down⟩
  · exact ⟨[4,3,2,1], p5_17_37_rows, rfl, by decide, p5_17_37_checked.down⟩
  · exact ⟨[4,3,2,2], p5_17_41_rows, rfl, by decide, p5_17_41_checked.down⟩
  · exact ⟨[4,3,1,1], p5_17_43_rows, rfl, by decide, p5_17_43_checked.down⟩
  · exact ⟨[4,4,2,2], p5_17_47_rows, rfl, by decide, p5_17_47_checked.down⟩
  · exact ⟨[5,3,2,1], p5_17_53_rows, rfl, by decide, p5_17_53_checked.down⟩
  · exact ⟨[5,5,3,2], p5_17_59_rows, rfl, by decide, p5_17_59_checked.down⟩
  · exact ⟨[6,5,3,2], p5_17_61_rows, rfl, by decide, p5_17_61_checked.down⟩
  · exact ⟨[5,3,2,1], p5_17_67_rows, rfl, by decide, p5_17_67_checked.down⟩
  · exact ⟨[5,3,2,1], p5_17_71_rows, rfl, by decide, p5_17_71_checked.down⟩
  · exact ⟨[5,3,2,1], p5_17_73_rows, rfl, by decide, p5_17_73_checked.down⟩
  · exact ⟨[7,4,3,2], p5_17_79_rows, rfl, by decide, p5_17_79_checked.down⟩
  · exact ⟨[9,4,3,2], p5_17_83_rows, rfl, by decide, p5_17_83_checked.down⟩
  · exact ⟨[5,3,2,1], p5_17_89_rows, rfl, by decide, p5_17_89_checked.down⟩
  · exact ⟨[6,4,2,2], p5_17_97_rows, rfl, by decide, p5_17_97_checked.down⟩
  · exact ⟨[6,4,2,1], p5_17_101_rows, rfl, by decide, p5_17_101_checked.down⟩
  · exact ⟨[6,4,3,1], p5_17_103_rows, rfl, by decide, p5_17_103_checked.down⟩
  · exact ⟨[7,4,2,1], p5_17_107_rows, rfl, by decide, p5_17_107_checked.down⟩
  · exact ⟨[8,4,2,2], p5_17_109_rows, rfl, by decide, p5_17_109_checked.down⟩
  · exact ⟨[6,6,2,2], p5_17_113_rows, rfl, by decide, p5_17_113_checked.down⟩
  · exact ⟨[8,7,2,2], p5_17_127_rows, rfl, by decide, p5_17_127_checked.down⟩
  · exact ⟨[7,5,2,1], p5_17_131_rows, rfl, by decide, p5_17_131_checked.down⟩
  · exact ⟨[5,3,2,1], p5_17_137_rows, rfl, by decide, p5_17_137_checked.down⟩
  · exact ⟨[5,3,2,1], p5_17_139_rows, rfl, by decide, p5_17_139_checked.down⟩
  · exact ⟨[6,4,2,1], p5_17_149_rows, rfl, by decide, p5_17_149_checked.down⟩
  · exact ⟨[6,4,2,1], p5_17_151_rows, rfl, by decide, p5_17_151_checked.down⟩
  · exact ⟨[6,4,2,1], p5_17_157_rows, rfl, by decide, p5_17_157_checked.down⟩
  · exact ⟨[7,4,3,1], p5_17_163_rows, rfl, by decide, p5_17_163_checked.down⟩
  · exact ⟨[7,4,3,2], p5_17_167_rows, rfl, by decide, p5_17_167_checked.down⟩
  · exact ⟨[9,5,3,2], p5_17_173_rows, rfl, by decide, p5_17_173_checked.down⟩
  · exact ⟨[9,5,4,2], p5_17_179_rows, rfl, by decide, p5_17_179_checked.down⟩
  · exact ⟨[10,6,4,2], p5_17_181_rows, rfl, by decide, p5_17_181_checked.down⟩
  · exact ⟨[6,4,2,1], p5_17_191_rows, rfl, by decide, p5_17_191_checked.down⟩
  · exact ⟨[6,4,2,1], p5_17_193_rows, rfl, by decide, p5_17_193_checked.down⟩
  · exact ⟨[6,4,2,1], p5_17_197_rows, rfl, by decide, p5_17_197_checked.down⟩
  · exact ⟨[6,4,2,1], p5_17_199_rows, rfl, by decide, p5_17_199_checked.down⟩
  · exact ⟨[7,5,3,1], p5_17_211_rows, rfl, by decide, p5_17_211_checked.down⟩
  · exact ⟨[9,5,3,2], p5_17_223_rows, rfl, by decide, p5_17_223_checked.down⟩
  · exact ⟨[8,7,4,2], p5_17_227_rows, rfl, by decide, p5_17_227_checked.down⟩
  · exact ⟨[8,7,4,2], p5_17_229_rows, rfl, by decide, p5_17_229_checked.down⟩
  · exact ⟨[9,7,3,2], p5_17_233_rows, rfl, by decide, p5_17_233_checked.down⟩
  · exact ⟨[10,7,3,2], p5_17_239_rows, rfl, by decide, p5_17_239_checked.down⟩
  · exact ⟨[10,7,4,2], p5_17_241_rows, rfl, by decide, p5_17_241_checked.down⟩
  · exact ⟨[11,7,4,2], p5_17_251_rows, rfl, by decide, p5_17_251_checked.down⟩

private theorem p5_17_bounded (s a b c d : ℕ)
    (sp : s.Prime) (ordered : 17 < s) (sb : s < 256)
    (ap : 0 < a) (bp : 0 < b) (cp : 0 < c) (dp : 0 < d)
    (high : 2 < indexProduct [3,5,17,s] [a,b,c,d]) :
    ∃ k, k ∣ factorProduct [3,5,17,s] [a,b,c,d] ∧ k.Pseudoperfect := by
  have membership := p5_17_key_check.down ⟨s,sb⟩ sp ordered
  obtain ⟨i, hi, key⟩ := List.mem_iff_getElem.mp membership
  have word := p5_17_box ⟨i,hi⟩
  have ke : p5_17_keys[i]! = s := (getElem!_pos p5_17_keys i hi).trans key
  simp only [ke] at word
  obtain ⟨caps, rows, width, cp', checked⟩ := word
  have ps : ∀ p ∈ [3,5,17,s], 2 ≤ p := by simp [sp.two_le]
  have es : ∀ e ∈ [a,b,c,d], 0 < e := by simp [ap,bp,cp,dp]
  rcases checkBox_sound [3,5,17,s] caps [a,b,c,d] (2,1) rows checked ps es cp'
      rfl width.symm (by decide) with tooSmall | witness
  · exact False.elim ((not_le_of_gt high) (by simpa using tooSmall))
  · exact witness

private theorem p5_17 (s a b c d : ℕ)
    (sp : s.Prime) (ordered : 17 < s)
    (ap : 0 < a) (bp : 0 < b) (cp : 0 < c) (dp : 0 < d)
    (high : 2 < indexProduct [3,5,17,s] [a,b,c,d]) :
    ∃ k, k ∣ factorProduct [3,5,17,s] [a,b,c,d] ∧ k.Pseudoperfect := by
  have rel : List.Forall₂ (fun lo p => 2 ≤ lo ∧ lo ≤ p) [3,5,17] [3,5,17] := by decide
  have prefixBound : indexProduct [3,5,17] [a,b,c] ≤ (255 / 128 : ℚ) :=
    (majorant rel [a,b,c] rfl).trans (by norm_num [ceiling])
  have sb := last_prime_bound 5 17 s a b c d 256 (255 / 128 : ℚ)
    (by decide) (by norm_num) (by norm_num [ceiling]) prefixBound high
  exact p5_17_bounded s a b c d sp ordered sb ap bp cp dp high

private def p5_19_keys : List ℕ := [23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89]

private def p5_19_23_rows : List Witness := [([3,2,1,1], [(45,0x230ac1707c2d0b82702c130881b0a42a01c150580f0741e0b0250242602803044120801906828014060340e0702402001008100600403000)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_19_23_checked : PLift (checkBox [3,5,19,23] [3,2,1,1] (2,1) p5_19_23_rows = true) := ⟨by decide +kernel⟩

private def p5_19_29_rows : List Witness := [([3,2,1,1], [(45,0x230ac1707c2d09c0b0b8130841b0882901c2a0540f0581d078250242c00c2602811048190801a0a006034140381c00424020020401803000)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_19_29_checked : PLift (checkBox [3,5,19,29] [3,2,1,1] (2,1) p5_19_29_rows = true) := ⟨by decide +kernel⟩

private def p5_19_31_rows : List Witness := [([3,2,2,1], [(64,0xbc450ec111181d0cc290d03f02c40084170882d10c2e0e40f110050401b0c41c09c320f4280243e07c0a054200ac160b0370344200c3806404068250c02601c3c02013078140a8010d80c0081809000),(3,0x3510423)]),
  ([3,3,1,1], [(59,0x2f0ec1f0ac3d0dc0f0f81b0b4270b83902c3a074170782908c2a0d40d0f0070d80e0641a0942c098310243800c320281507016084280143403006044180482400430020020500404000)]),
  ([4,2,1,1], [(57,0x2f0dc230ac390cc170e81f0b4270b83504c360841b0882901c2a0c4150e00f0c8160741e094090b0030980a0d01206420068050a006034300500e0700109008008100600403000)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_19_31_checked : PLift (checkBox [3,5,19,31] [4,3,2,1] (2,1) p5_19_31_rows = true) := ⟨by decide +kernel⟩

private def p5_19_37_rows : List Witness := [([3,3,1,2], [(64,0x148160745d0e02810c4a0383a01455114200402b15c320883d0b4080d04f04c3f0680a16825144150703709c0210849034390105407c4b03c2a0843c01c3313812064090901b0d801030030780606000),(27,0x471642f1045c14c17178291103b15846134110b05808c3e0b835140141000b16c26)]),
  ([3,3,2,1], [(64,0x1481610c1d0e4281544b03c3a0ac0515821130100f42c0cc2213c130f8090d0251401406c0a0dc261081c1240d0e0031501f1280e0a8040c4200f0070c84e0481902024068011200c0081e0c00606000),(27,0x471642f1045d14c17178291143b15c46134110b45808c2e16c35144151000b17027)]),
  ([3,4,1,1], [(64,0xe4331243a10c0f0944a07c350982f114110d83f02c4c1181206c310882b0e0410343201c4807442038240b41e0d03d0242e00c44040190f80a08029068300142a030150181c0582c00408008180a004),(9,0x3b12c270dc4d11c1313823)]),
  ([4,2,1,1], [(57,0x2f0dc230ac390cc170e81f0b42702c350b8130843606c29088310542a03c3807432058250241e00c2c0442602834064120800506828034300500e0700109008008100600403000)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_19_37_checked : PLift (checkBox [3,5,19,37] [4,4,2,2] (2,1) p5_19_37_rows = true) := ⟨by decide +kernel⟩

private def p5_19_41_rows : List Witness := [([3,3,2,2], [(64,0x1fc3c0bc661c01615c40128070c47216c1802c42130760cc1c0985d03487138371e01e0a05203c020e46d0a813150041f82e1bc150fc49018301680a12c7506c250303609c011b01200c2d1200909000),(64,0x20c6a1d01a110850d45f224461407a080610448b0ec7c194220b056234800f4671c41716041020820c8691cc5c06443134841dc340745e0384513c381e41f0a46014c102283a1ec641b8210ac1415405),(11,0x6b218471888c1f4232383e1a059)]),
  ([3,4,2,1], [(64,0x19c2e064501740f1c8460c4051a01a09c5e124100c83f150610a013128091b0400ac620502110c0a0b04e16c220344400c66060251700e0c03d01026120070f8600481f0a820108011680c008240181e),(49,0x591c43b14c751ac1d1d83515c4d1bc58194170e4700bc511cc3a11c6906c5217c110cc6a1541c0a44b1b4341045618c151303702c6e0b464058230e045)]),
  ([4,2,2,1], [(64,0x12c21100171582d130430883903c4f0b8051101b0e8310405009c3d0c8091242807c3e054540ac0a128200dc160342c00c42064380384e094040683001c260f01302048078140a801030020602404800),(21,0x4714c3510457134231602f1143b044511181d0cc520a43f15434)]),
  ([4,3,1,1], [(64,0x3c4910c1b0b44a09c390b83302c1d0e817130291181e08c350342a01c3c104190d80e04c48094420682c0c409098030e0150c80a1101c08428014220d00c0440610012090010c008008140800404000),(11,0x3f12c2f0ec4d11c1f1382b0f437)]),
  ([5,2,1,1], [(64,0xdc450fc231182b0e43305c410e81f0b44209c0b0d4130f4210d81b110290f82201c310542a03c3807432058400940900c2c0442602834064120f0200141a0a00d018300500e07001020020401801000),(3,0x3b10c2f)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_19_41_checked : PLift (checkBox [3,5,19,41] [5,4,2,2] (2,1) p5_19_41_rows = true) := ⟨by decide +kernel⟩

private def p5_19_43_rows : List Witness := [([3,4,2,2], [(64,0x1e0162ac5c1a44901c9c0e8272346d02c1812c911f82f0f01c1bc0d28860100930c41e190510080f108881d43304c04264370908a0545b120060e46c0285d0b81b0303f0c0630041200c36168090b400),(64,0x25c7721035088681549b2a0460988c1e4172b06a128570209d0ec282386e1ec192b85f1309227c7f0f41d0a870038a318441138942043207c651c85204043224961d8340502119c540149a0e0450948b),(45,0x862a8591f4b02842c2c85020c7429c9821423158a911c7a2b46b1609e0a48f1f01a2bc4d280800f82b1c4a42c46213c952082014c1129844)]),
  ([3,5,3,1], [(64,0x4cb01b049014a20ec22250711601418c4a018992003c0647202ca8190410a09a0cc691400c108911e0340446a00ca00e42024812184480103a1c009188980c418028400c8680049000838180080c000),(64,0x74ba1d85303cac2242c2787b0dc1e2c46d150a32284608c951f059054b21b84b01ca42043d090961cc5a058a91944c0a49b2083e06cb81d051034aa198430a89c1e4350706b1480e22044084931e836),(59,0x8f2dc5f21cbd2bc2f2f8572347f2d4a723827174b613c852ec77178ad0b49f2181f2f0552b88b11c2e1f4b31bc562948c094971f85b05cb4134a620c3f098b91d45c2ac671382b27484)]),
  ([4,2,2,1], [(64,0x2c4b0844005c560b44c10c220e40f13c2e0141b0e8310405009c3d07032024490a01f0f8151502b0284a080370580d0b003064380384e094040683001c260f0131201e0502a00436030180900604800),(21,0x4714c3510457134231602f1143b044511181d0cc520a43f15434)]),
  ([4,3,1,1], [(64,0x3c490f81b0b44a09c390cc2e02c450743a05c4c0a44608c1e0d40d0a8071043c0643604c0e120251081a0c42c0242600c380543202821070160a005088340440c018400601200430020020502001000),(11,0x3f12c2f0ec4d11c1f1382b0f437)]),
  ([5,2,1,1], [(64,0xdc450fc231182b0e43305c410e81f0b44209c0b0d42e04c3d0843606c440a43e088070c42a03c38074320584009409078030b0110980a0d0190483c080050680d018300500e0700109008008100100c),(3,0x3b10c2f)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_19_43_checked : PLift (checkBox [3,5,19,43] [5,5,3,2] (2,1) p5_19_43_rows = true) := ⟨by decide +kernel⟩

private def p5_19_47_rows : List Witness := [([4,3,1,1], [(64,0x3c4910c1b0f82d09c4a0cc0b0b845074170e829130231181e0d4070a8410643c04c360382512042068310242c00c26054380c80a084440701601428088110d00c100180480109030020020800404000),(11,0x3f12c2f0ec4d11c1f0ac4e0f437)]),
  ([5,2,2,1], [(64,0xb45610c4c088391880f13c050b81b110310e81009c500f4660705c024321241f0a0150f82b1500a128200dc600341600c2c064420e00e0944e0685a01c30098130f0081201e050010a80c0081809000),(37,0x591944714c6917c351046a15c4d08c630bc581143b190111446707446174291483f1a0551780b0d04b0846105c40)]),
  ([7,2,1,2], [(64,0x68430e8630402613c781bc1c1145b020840c4510503d1985d028331247207c160fc021f82b1504b084371800d0102d1b0191083903c251381b168070c02704c3c1201e054010a836030030602401800),(64,0x11c8614c7c1a05f220351d0411a8801584d1d8231888b2082f1606e1103b19011234501e47007446170850c8291487b19c5e02c870d04a1cc2005c401a47f0b05513075088381840e228052042e15c6d),(11,0x7d2246b1dc8c20c591948e1e871)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_19_47_checked : PLift (checkBox [3,5,19,47] [7,3,2,2] (2,1) p5_19_47_rows = true) := ⟨by decide +kernel⟩

private def p5_19_53_rows : List Witness := [([4,3,1,2], [(64,0xe8201bc5513032040671142b0880815c3d1c8340686913c2d04c0a1843f0945a07002144370546c18c4909c0d0103907c5412c3103c660a82101c3c0cc1913812024600901b00436030030c00606000),(51,0x5f1c447164741ac2f104761705305c6e19429178440ec701584d044681182c08c580f8730d46a1402e0500b188400987516c1d148380586d190280385d10c05)]),
  ([4,3,2,1], [(64,0xa00f19c440ac050e8211583d1c84c0cc101a04f0b013088091843e0945a0d01b140370506c188490980d1081c00c3807c5412831038660a804080070f0320644e0480818024068011200c0081e0c006),(49,0x5f1c447164751ac2f104761745305c6f19429178451c0571cc4d044691182d08c580fc7416c351a8510b8151b40b18c4009c5c10c1d0e4161b8551904b)]),
  ([4,4,1,1], [(64,0x114260443f02c550d8211301b118310485c0ac56104220343801c510c81d120170b40e160241483d078090d0030b819110100f82902854068050c02a05440030061401c058010b03c020020a00405000),(31,0x4f17c3b12c6116c270dc621344704c5d15c23138390cc5e1244303c590e85307c4a0d4600bc5a)]),
  ([5,3,1,1], [(64,0xe45c0cc0b158450b81d1443a0a44c08c460d41e0345801c521042a0643c04c360940e120420c41a024540b003098150e0320840a07016014500a0220443403006100180480109030020020800404000),(27,0x4f16c3f12c5d15c2f0ec5e1344707c5914c2b1383d03c5a1244306c550f82d09c4a)]),
  ([6,2,3,2], [(64,0x1cf016834038db2d487184721301e0989f1e40933036040b7244630f4e40a0021ec552a01224c6d0fc193002a010570c4d82106f1241b27006034b41804b0947803c900f0270045400c301200c09000),(64,0x16c35370ae2d888188991cc451341f318a01e80a3cccd17437044de2e08a248640f8e51d44f084292887c158cf2a43904cba250661b840068e7304510147e16032364ab21415258701084a070c32742d),(64,0x354dd2bc8926874118203b4c72840b3d0ce1783837cb12e48b194e61d850088c928c7d3d8d02a83a050e12ec8d25467104e8308520b0a51fc59348da2b086058bd25c691c443074ea3109e0b8083c481),(53,0xd73bcb332cf838c8f29cfa350bf1acec20cd62c09b11cee320f517ce02c88c1dc23328a43dcd10ece22f08e1a0e914ca6200f934cad05cbe2606a110eb3142f2085c)]),
  ([7,2,2,2], [(64,0x2d04502ca522066124c615c3a0601d1e05b2642a0348a1b44b0b8ab0f01f0085d100bd1f80f1bc520c01324021108252886315037054750182702887120390705a0306c0b41e00451048030903602400),(64,0x20b51182930ca62108919c4a31c580ec1925879170b72682b038a822c691b84c0bcc92b03d0807b178412f89c1fc1023470138530c4142b891088cf0146010c26300a3204641c8550cc38058931d807),(64,0x140cd2c0d1188c2280831d0352c89534cb611cc429c851a0c8164971e8d52e09b0b0a92306a134ca2b43e1f05f2e8bf274800448e1c44f0c8cc2bc9208cd0184443049f29082194731583405cb11dcd2),(17,0xbc338a12ccd431486260d62e4aa1accb1f4bb2788f)]),
  ([7,2,3,1], [(64,0x78052803c08c921e45a104b0130330506a144062202402c7a184420a4980d0520e4a81c00c188490a8112001c00c3a084901604a0c4121a004088091e04006450028600a01a00438120100803006000),(64,0x3c7e194460b49c20cba284560f4ac24c7416cb11984d0b8152106b01ca22243e094941ec5c10cb22644e0d4161b0532a48a1c4260347c18c440ac9a20436074b81503b244721640e1904b0b01320869),(57,0xa72dc8f27cbd2bc7721cbe2949717cb51bca62347f11cb6274bb15cad2387519c2f278852f0a30fcae25476174b313c172186d2908b09c961f45e114b426c372e46e154ab23073)]),
  ([9,2,2,1], [(64,0x14780b81b1b85b1103121027040500f4901981c0245c1243207c720a0150f82b1f8540284a0dc2003460058030b0191b0420e0250384e0101a01c5a0c02604c3c02048078140042a0d8020600604800),(64,0x15caa25c4d08c7618ca3230790bc821bc58114982143b2b864144a42447a19c1d1c05d11833218730a49c1483f2487f1a0552a00b1784b0d0211d06105c8a1002d2006d158432584c0e42203c6213ca2),(47,0xa12b48f26cb129c7d224b227c951acab1dca023483164ac264af194a52387b1c447268872c09d14ca624c7c1a4a917c35220752788b104942046a)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_19_53_checked : PLift (checkBox [3,5,19,53] [9,4,3,2] (2,1) p5_19_53_rows = true) := ⟨by decide +kernel⟩

private def p5_19_59_rows : List Witness := [([4,3,2,1], [(64,0xa0670ac44014210e83d158720cc4c0404f1a0130b009088610943e1681b0d037140141b00a124620984200c1c07c38150311280e1982a010070803c06432138120206009001068361200c0081e01818),(51,0x5f1c447164751ac2f1045d1d85305c6f194291145e0ec571c073134111a42d118230fc581d0351446a0542e1b40b18c27100431701d0e452058551b84b1900f)]),
  ([5,3,1,1], [(64,0xcc0b114560742e05c510a43a130230d4460341e16007104520642a0f01309436038480c4420241a1502c00c150983808432028440700505850044220d00c0184006001048240c008008140800404000),(29,0x4f16c3f12c5d15c2f0ec4d1784707c5914c2b0f44e0dc0f1245a10c1b1542d0f8271285c)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_19_59_checked : PLift (checkBox [3,5,19,59] [5,3,2,1] (2,1) p5_19_59_rows = true) := ⟨by decide +kernel⟩

private def p5_19_61_rows : List Witness := [([4,3,2,2], [(64,0x2684001c6602c5716c810984c2ac72060762701c1080d0cc910dc5d0082821c4e14878078a203c6d24c130e40418c2a0b8541f86f054990fc06028301682512c7506c0c24036004271441200c2d02400),(64,0x1f022200a61c49705c3d26c4102067234321605c208a8134ac1cc191dc9d074431a40e0d0920e05e210292204f2b8531e49f07c4528c101b8940503a180051902b2282f1547b0847f2944a1c0960583c),(45,0x8f2a86b218b0284471888c2c87d08ca72603e1a08e164832a4ad1d01a278441a83517c85224502bc7a28020118a4044950ec650b08b2c456)]),
  ([4,3,3,1], [(64,0xd0890e405168260ac4c1447210c9819069228190e80602c2c20431148231e0441246a0689003061208110c803160240a44a10462048880e0040242a14021108680600a2003000422120100082810000),(64,0x1782f154761ec472706d2381d0f89303c850d45616c271f04d1b81e1cc9426465218150d83b01c5c0b44e14c741e445268660586b2301b0f0910342e20c33150590947a1184b1b01c1c4920386321013),(25,0x7f25c5f1dc9d23c3f15c7d2786f07c9521c371747e13c752589b19c172343d)]),
  ([4,4,2,1], [(64,0x140271c846124680683f2285e0408004c32024540a0790ac4a0846c1004318814210360285b1e80d0b0031382209444198180f40e1f830010070984807c3e18012020780a801080421680c0903c07800),(64,0x15c761346f23891194170e4581f42f144701cc47248692201b0e88b17c1120433148550a44b1a81c1b44123063208150d0850dc0b1587b0b44c13c231b8452406405867218190e05d1f00f0b87f0c405),(15,0x7723c591c4932243b14c752506b0748d20c35)]),
  ([5,3,1,1], [(64,0xe44a0cc5c02c451581d0b817144290e823130351180d0785801c41148190a8130f036038480c4420241a150030b01509838084320284407005058500a0110880c018400600104824020020502001000),(27,0x4f16c3f12c5d15c2f0ec4d1784707c5914c2b0f44e0dc0f1245a10c1b1542d0f827)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_19_61_checked : PLift (checkBox [3,5,19,61] [5,4,3,2] (2,1) p5_19_61_rows = true) := ⟨by decide +kernel⟩

private def p5_19_67_rows : List Witness := [([4,4,3,2], [(64,0x2443e33c331f1142e8c1078253fc63024102a0f11385500893100d81f88530c274206c2d412064f315c042704212487330301e4b706cfc180060344b2403d1ecc003cf0150010fc842d01800c481e00c),(64,0x4005d1900a044a22a4f213c5639c8d25041348d90d87f219172f4c408428409091986d2d813068ab3d051160052589d128db20488480c63342a0c47a42c6f2e015070f63f45a184070389f1144c3908a),(64,0x1d4be314220a503428671b814294ac3d452164ea25c9e110d537039208894692131cce0ac324150c1a4702e416074ae3dcfe16c620209928046378e522c9248cc93402d0d07d439151c8bb3081f098f9),(64,0x1d8bf08d041a0a62b4533ac98358dd0e88346d223202c4190d1a87105caf3e05c3b49a2844737ce62311d490ca3442e0d50f458732f0202c4fa4045e1940b28caa140e13a08e2552634cda0dc8044518),(37,0xef47cb338d2844c7729cec4a8d70ed1c41c6b2c0ee26ce04792532c2f440742c8fb17ca4388e923d273503844919)]),
  ([4,5,2,1], [(64,0x148551e81a12ca21c0421cc1004c980e009180910b831158271f84c0784f1d0142703c1b40a034920c803168280ac501e0181246e038960d80401c2c15025128720480824030004261380c0082a12024),(64,0x174822142214caa1ec1b280a31007110c111a0990e45e1842f218572b87c1fc1c1341f290441d4152689d0e80b188930cc8a1605b0a480080512a0761e4160649e0f86f03c94198970d0370145c0b484),(47,0x8f2b46b224b129c471948d2c88308cab284411a48e17c872b0af1f41d294451a89b0ec632208b164b020421298a91187705c9f0fc64254670d48c)]),
  ([5,3,2,1], [(64,0x110211e43a0f4560cc721301004c680b00921061088251e83e06c5a0d037140141b0490280d1882600c7e1081c07c38150311280e1982a01007080780f032138120206009001068361200c0081e0c018),(64,0x2386b0bc871f4411747614c171bc8822c650a4451783b15c701cc4d0448c1a42d20885118231ec3f16c351d0510546a1b42e02c8618c271f07f100430745c0e452154161b84b03c8a190670a02b01480),(9,0x772245f1c48d20c4716475)]),
  ([5,4,1,2], [(64,0xa07225c490806906c402286104c810cc0a288541e42b2640212c221b04318c152103616c0d1ec2d0109c13825114660603d1740f1f83001c27258480fc60048091e02a004211085a030030900607800),(64,0x2205f044a920032280520a4732604a24c6a0704122c622ac142083402ca31547a0b0752684c08c6d1108d190162b8850dc5c038571f02e0149d13c261bc46240670643e21c39178102a07f0c49f02051),(47,0x952b47723cb029c591c4922c8890ecaa284531d0941ac1d230ac20c35290561d89b1346e2386505caf21838298581f42f278501c047244682c41a)]),
  ([5,5,1,1], [(64,0xf81f160790e452048331b02c1340d1982601c80100610847a06c54050351380e1a028124091882200c7c0f01d0d850040311280a190240141e1e038064321300c018200041a0d048020020700406000),(64,0xbc8920c431747615c171c48a1ac2b214451787f0fc591c85304c8c1b42d2184619c27204411687b0ec550546e0b84f03c881a4292084218c231707d0f456058371c0510446a0a84b02c84110650947e),(11,0x7722c5f1cc8d21c4716c752386f)]),
  ([6,4,1,1], [(64,0x6c80130650c47a118120ac5c1040d1582201c6c0e051074660c8171f0481080e160240f4091481e00c680d0190b878110100a43e0285408005068640c0150a840030061401c004160f0080081801014),(64,0x20c4f17c752286f0ec851fc4b1847616c271c4861ac372044d1887b04c5d1c85708c881b4392084e19c331f4491784303c74164251b83a14c1f210690d47e128601e4450445a0983f02c70154211a836),(5,0x7721c631cc89)]),
  ([7,3,1,2], [(64,0x270790f493068570d0ae1c84f04c690b40a210610947b0083f0709616837144152a0490346309c041f84207c39240540c44b03c660a807084780f0190cc4e04809180240041b0d848030030783006000),(64,0x1a0a50b04608c9d1e8b70f894160352bc731408d0506a0b80b2146227c261f0402e81d25c5b2c4381d452058a91b44a21c640a0a20147f10c990805d0e8b4244552ac321bc4c0408a19c2b2040811422),(59,0xa72e48f284bc2cc77224a42f89b17cb62b471230a620c47278b8254592c0742386b0bc862807d104bb2605c2c87614c172a86e220650a4a3200bd1109a1783b2d492158ac1c04d0448b)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_19_67_checked : PLift (checkBox [3,5,19,67] [7,5,3,2] (2,1) p5_19_67_rows = true) := ⟨by decide +kernel⟩

private def p5_19_71_rows : List Witness := [([5,3,2,1], [(64,0x110211e43a0f4560cc721304f040131a02c02484184220947a0f81b168340dc500506c1240d1882600c7e1081c07c38150311280e1982a01007080780f0190c84e0480809001068361200c0081e0c006),(64,0x2386b0bc871f4411747614c171bc8822c650a4811145e0ec571c073134111a42d20885118231ec3f1605b0d474144151a86d0b80b2186309c7c1fc4010c1d17039148550586e03c8a190670a02b01480),(9,0x772245f1c48d20c4716475)]),
  ([6,4,1,2], [(64,0x25c72124202dc691001b1841320433028a21e4540ac022644b088ba1b04318c152105b0d80d1ec2d0104e094452d0660f4181740f1f83001c272584807c3f18012024780a801084421680c0903c0181e),(64,0x26073128b824c6a1041c22c62050ab2083402ccc28c7a1542c30c9a1d44c08cbb1b48d190162b88517037038a51f0570b8053189d13c262f46f118b5240670f81921c5e0e4102a07f0c40827c510a0c0),(64,0x164c82fc71248b22243b2a8ca28453308742e4941ac1d230ac20c35334a4158c426c76134bc1b86505caf2183833ca61f4580bcc7278502f87011cb624468068b12205f0e8112a4800c8c9280520a4c1),(11,0xb332c952b4ce3147723cb0340a7)]),
  ([6,5,1,1], [(64,0x1e4580e492148330486c1342c034660980720061100211e81b250540d4141380e1a0490a0091882200c7c0f01d0d890140310404a028640900507838064321300c018600800106834120080083001000),(64,0x290851149e1fc5e0fc5924c7214c132306d0b48619c4609ca0204412687b1683b25474154151b84f0b80f220690a48218c4208c9c1f45c0f4961583705870144111a84b0a80b21065110251f83e07c98),(33,0x8f28c7722ca527c5f1cc8d2988711ca126c5b1d48e1bc2f224a220c432745d25c7615c171c48a1ac2b)]),
  ([7,4,1,1], [(64,0x20065130311e8460ac122405c1040d158221b0510e01d1983205c7c1202d1080e230580f42402452078031a0340642e1e0440a4100f80a150200141a0c0150a840030061401c004160b0080081805000),(64,0x23c7616c271c4861ac3727081134961884704c911747215c232206d0e48219c4e0cc981f4492485e10c0f23474164251b8530e81f210690d47e1282f25079180450448e1683f0980b1c0550846a0d81b),(25,0x8b26c7721c9d25c631cc892788313c9924c5f1d48a1bc3b2149a1fc4b25461)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_19_71_checked : PLift (checkBox [3,5,19,71] [7,5,2,2] (2,1) p5_19_71_rows = true) := ⟨by decide +kernel⟩

private def p5_19_73_rows : List Witness := [([5,3,2,1], [(64,0x84790f43a158331c84f13013040680b00921061094221e83e06c5a0dc34140141b0490340a1882600c7e1081f07038150311280e1982a01c040803c06432138120206009001068361200c0083001800),(64,0xbc871f4411747614c171bc8b220650a4811145e0ec571cc7013411230690b4852084608c7b0fc5b160351d0510546d1a82e02c8618c271fc7c10c400745c0e455148161b84b03c8a19c640ac2801444),(11,0x772245f1c48d20c47164752386b)]),
  ([6,5,1,2], [(64,0x36c7b1301b288731081326439028c0244600c4022dc570a0de1f84f078750549c1b43c03493010ba1682b144d81e0490606f03c960d8070b4b41502512c720480924030004271386c030031200609000),(64,0x3249a1a43a02cf0304921843239cb821c580a4df2b87f1401f29476114163309d1b83d038c3250630d0053a8bb2285b0b0e120421364a81e44a0649f1c03f040c625c660dc082f45d0b8e42d48415426),(64,0x308623a0b922059380af20020354a61dc4605c9e0f8f331095190353acbc22c5c388b120853088da2a47a068cf28071100113d8c7260670e0ed2f88d1782f394b621456370ab1f04d070d228c7410c14),(55,0xd73d4b3344f83bc8f2b4d43e8cb1acf23a4892c0d629c47338f4314653b08c38cb220c232a8d0284413dcc81a0ee2fc8e17ce6218dd2b07d074d3290443e4ca26c6a0ecf1)]),
  ([7,4,1,2], [(64,0x1a44006cd82286104c810cc0a288791502b0089912c222e86c10c63054d22105b0d80d1ec2d0109c13825114b41983d0605d03c7e01c272584807c3f18012024780a801084421680c00c240f00607800),(64,0x188142ac820d00b330a31e8550b0c32687513023390bb110db23464058d32b88517037038a51f0570b8053189d13c262f46f118de2d49019c3e064d521c5e0e4102a07f0c40827c510a0c025c72080b7),(64,0x2b0830d4cd290563b4c426c76134bc1b8dc2386505cd42bc860e0cf2987d1602f31c9e140e72f87011cdf2d8911a01a358b12205f0e8112a4800c8c9280520a4ea304981cc4a384b824c6a1041c3648b),(43,0xd13a4b332cec38c952b4ce3b8c51dce63748f2c0d029c59320e82fc713809235cb22243b2a8ca284533acc21d0e22e4941ac1d3688c)]),
  ([7,5,1,1], [(64,0xe4520cc122b06c1342c034660980720061100211e83a06c94150350504e038a81a0490a0091882200c7c0f01d0d890140310404a028640900507838064321300c018600800106834120080081c0c018),(64,0x24c7214c132b48c1b42d2186711827280811049a1ec5a0ecb425474154152b86e13c2e03ca9220690a463108232707d1703d258560dc162c0911c051044aa1a84b0a80b21065110251f83e07c981e458),(57,0xa72ec8f28cbd2dc7722ca52f89f17cb92cc73234a621c47284ba26c5b2d4752bc8e1bc2f224a220c432f09d174b625c7615c172c4712ac8a1aca4214452787f1783f2e099164b2)]),
  ([9,4,1,1], [(64,0xc47a1182b048901704103456088072806c14438074660c8171f0480b4420388c1603d09009078031a0340642e1e0440a4100f80a150200141a190300542a1000c01850004160b03c020020602801014),(64,0x1884704cac174a61c85708cbc284881b4392d88219c4e0cc981f4492485e10c0f2a08d1d059094a21b8530e81f2e0841a4351f84a0bc941e460114112385a0fc2602ca41c0550846a0d81b2d0801944c),(64,0x2bcc52fc8b26cb1318ab1dcc12ec87274b225c632b4c229c732f4892dc9e20c4f264ae24c5f310a91d4be28c8a1bc3b2e4852687f12cb0254612a88f1d85b09cc0294712e8861ac372d49c2044d2587b),(3,0xb330c9f)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_19_73_checked : PLift (checkBox [3,5,19,73] [9,5,2,2] (2,1) p5_19_73_rows = true) := ⟨by decide +kernel⟩

private def p5_19_79_rows : List Witness := [([5,4,2,1], [(64,0x1183f1a01a1848a04c5e04080024321e4a20ac540a0980844a10c6c100620505b2100d0d80a1e8030b09c0944e08844198181700e1f8070c0040989607c480f860048780042a08042030020903c0181e),(64,0x1c0692481b22c5f220110e8812a83328c55280291489912c741b4411a81c18c8c054852b8372080b0d07b2902d1589d13c9a08c4c1146e19c90064640585d2180f0e07f2a0311f0050b89e09c5012472),(45,0x952b47723cb129c591c493224b20ecab284531d46b2501d234af20cac0d4a515c9b134761bc911948e05c872c0392a4a60bc5827c511cc47)]),
  ([6,3,2,2], [(64,0x15cdb130811d8ab070720609c03442008c60dc332dc28174e114887138780786d2881303c93010392f42e18c2a150d81247e1bc152640a0fc060c0b40945a1d41b030900043609c511b01200c4802400),(64,0x38d210c9231c3830c341a4b80a4ed178e214c883784f210792b81f1b8a30509f04045250053243a2f82f3cc642e82b180e41548a3644a1fc7b08470294162680b33c40258070f0c00c4662d4263a85b),(64,0x3e46a2e4ee17c8937c502147a2bc20290a0044d5118953283b2fcf4194bb0b0f0184e51588b368801f0b1088712981726c4125c083303d304323d8672d8eb170e71608d3704d208772b01d1cca80649d),(53,0xd73c8b3338f83a48f2a8d4314fa1acef380862c0a13584732cf52f0f1188e62307d2c82329cd1260cd0f8c23dc683b0e81648e374832b4742a41a278d3110c831035)]),
  ([6,3,3,1], [(64,0x130c21c86926019190142280b0e806204b00c42c28823148c8124781106a06861240110308200c322a02916024128c01047018812220090e0040a8a00845010818028800043008848180100082810020),(64,0x2501522cba0ec8601c362c4ac0b45c28cd214c4e32479310451d09a06c66058912300d0f0832c8330b8a93605929025150ca12c7a118c11c46c0706324813038892e039210050d0aa0ac5a098a134051),(64,0x1f46f2781f254bb21cb60dcad3705d34cce13c7e3147526c6725817234bc0f4b32b82f178d9294d4154cb1ecc611c762701d24c8e03c3e2e4852d0352acda16ca609c56344cc1347c30c731b81e26465),(25,0xbf35c9f2dcdd33c7f25cbd2bcde17cd531c772748f2f83f2d4db29cd615ccd)]),
  ([7,3,2,1], [(64,0x158ae13c7204c4c040680242c18484094221e81b0f8960dc5a0d050050a81246c0340a188030987e07c42070900c4541280e198070a804080780643c0c8120206000424068361200c0081e0c00606000),(64,0x2b04d1c0111a48c0b485208231187b2783f25cba16c940d4582c074054a91b46a02c2e18c8609c7f288431f01d100980e45c244b415452058aa12c6e03c672282b190050a080084441e49c0f43a24833),(59,0xa72e48f284bd2cc77224a526cbe17cb72b471234832984727cbb254b8164b11d46b2382f21ca31f4a0104992f05d2d4b214c7605cab22c6522029204a41149d2683b178932d8572bc73)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_19_79_checked : PLift (checkBox [3,5,19,79] [7,4,3,2] (2,1) p5_19_79_rows = true) := ⟨by decide +kernel⟩

private def p5_19_83_rows : List Witness := [([5,5,2,2], [(64,0x9cac070f32a0630600d39054008d912520240450e911204762f4722b81e28c133a85a03c0436c4b1011721c3c1e06d2d02429415028e114406108374387e1bcab06c0c004d8120752881200c3f02436),(64,0x208c91dcbe1cc2e414ba0a8af07cf629066050eb16d32040e715c053704c48c93105182203d450cf210793006e0c0b5094fc2c421298163b45d02ce21492901cde2644e10d1a2283843c7f3187b1c0b7),(64,0x340853307a30431420b6098fd2c8223e4a71a4171793538c534a80837c9a13d262584446c8b440d2200c71f0c31c4332e0283fcad074f42a4644ec193c060038e51552c3689c12921244464748d0ed12),(64,0x26c5049c974708c34cc81f4c40d10b2e429400f52a8654f01a3c4614e0e61592d27522248474788e44cd520cca2fc740bd062ec2b408b0080f719d3e3b05c4cc113a0584bcdd27c4d49094464890f915),(61,0x10d4e8d7411404c4a13390a3ec6b509374a098350c50d50c4053d3c8624e52e2791f23cd632d072f02c40cf81a13f4d0e916530281252551634486334c20c9093f8b308cfa1a9413bd364ace0)]),
  ([5,5,3,1], [(64,0x360941601402cca1280630441400800f0333c8721a4a8190282681a244113405003003308420e4f81e0341a8612809204809320480103a0c4f01c0622601802801300400c8682401000838180080c000),(64,0x2c86e2a4650a4e82902426c1b368961681634451440cc130c310d022083e3e4790d4f42e0741acaa1982a284213809c0709304cd21480e3244942005310881103b3e87a0d8f11c4b01b0632882226419),(64,0x3f87e3d4b91d4b42ac670acea298e12741d3705c34c534480f3384e424c522445410843ec7b0dcf62e8762c46d2b02c28c233889e078d925459460153505432c4b428073188a119012043d3f07c3cc73),(64,0x1fcbe2d4eb29c27398dd1751c44ccf13d0e23905214f72ec772d8ad0b4ec38c9f07cde1791935455450c722c47418863f47d2f0b31bcae0b8e929425390db25c5b4681735856444cd1350c2310320c3f),(27,0xef45cbf39d1d43c8f2dced37c5f4791541c872f4af0bcee3951b35c574590d234ff)]),
  ([6,4,2,1], [(64,0x4c8a17810024800c8790aca21502808498128432e86c100620505b034840d80a00c7a0b0252704e088440f4b4198181700e01c7e0c0040981f258480f86004808004780a8201085a030020900607800),(64,0x33029280522644b308742ec6d104b81a81c18c15230850dcae02c820d07b0b4a41589d13cc608c4c114bc1b8b519c19240640585d03c860e07f0c4a80147c0b8272785025c49300721183f2d86806861),(64,0x2fc7124c890ecb22accd28453328c31d4b91ac1d2508d20c352b0a515cce31c9b134c41d8bd1bc9119417238392c0a91f42f2985827c51320c11cc472f8702dc6906c9222c5f044880e8810ccaa28c55),(13,0xb332c952b4cf3147723cb129c59340c9)]),
  ([9,3,3,2], [(64,0x57025390960781033c57008093058012508108343cc7b1b52c2d06627c2724550064d8048c312c3d3f0840d86f185202a09306c0d330540183f0c4f01e0632702403c01300331b090060030f06003000),(64,0x2815f0a0e7248995441a084d9660133485a014c460c4c42c3e114fd6f085510373d87e1c12f2dc621a5212a5682882a25153070db054cd63055450073184e100ff21c320e4f16c0794e072191232ac9d),(64,0x21d431d8613d0e105006fc8851c3a3c8f96c47a205391cd322e865490ac5ac9e2955d0982d395a425d5607cde3418f16117028c23258112851425c810d02228353d1b31f13b1b8754b4b55d067498ae),(64,0x5d46849caf5b9600a4e869c9a54959088da38599050d36485b468c56104d431cb118fe415bd2188d514383ddb61fd3e1c5302e1771a9224a4aa2c56928d620acea25554074dc66c16338d56345617515),(64,0x4591d754c861c5043dce700895203b3e9b26e4824e9411d1332ed7a494ad5b0a6579650b8e63b5a526157080df678d1640594600b75cca609891490a445c9111037088b528f56d07d4f0764b9352d8bd),(64,0x7450470c8c52db54f4774d8be5d97d4a0b05bd613a5a826d5a08ce2669a1351931711b76985435cc11d066f9c523946534f86dc804fd312e5781ad2a2c96a5c4a458c2c3adaa554dd670173598e6545e),(64,0x749c4531372fd7e5c1a956ce368994471db735077188f539b8501794acb35c9643b1ab674d76585f479d677588441cf705493edba20d424d0bc5ed6d29d660bcee699ad5619f64519760cb62853449ca),(23,0x1af74d7f68ddc71d4f5cdac65d1f779d06ed435f1673bdae681d962d13)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_19_83_checked : PLift (checkBox [3,5,19,83] [9,5,3,2] (2,1) p5_19_83_rows = true) := ⟨by decide +kernel⟩

private def p5_19_89_rows : List Witness := [([6,4,3,2], [(64,0x95142e81e040023fcf118c09155442a04e1012f24c855d0d81f8c32d427065081b012010f315c494e09c108871e568330302dc1b034fc1800612c3d4b0901ec2403c013c0540fc842d01800c480303c),(64,0x310362d828069172f5090846d04d5c015023d0661604a51d392ac512744363132258881e9775a4db204cd0c520318b80a81c0390b3f46f0546101d503d84c0f93b4b49f11491600e42287c5accf30433),(64,0x57c08415513dc6916c4d5293c2b92e280462498f4d581264e522c7d5e96c378d03083409923325152ec2d07c11439001c8f21900a159533e545174a913d981053e4c0a22508660d7539c8d3647f5b8d2),(64,0x25592611763a08e368805f56f384d3314370a526460be428221b8144455d40c753d467165565213a2b0522799b111416353329489619783a96a37082339710c8d5484c70e4b90ac1d4690c3f87005862),(64,0x374835c8d6488c80e82c4a51b4347105d60419523e06a1715952d3d2bca167847641366089a3988c6257b3b56d37cd10d524329162f02e0811d43d011cc655880b550fa5185e2a850535994fcb14c4a3),(64,0x4a91c585071ad5a530b067d914dc9b6297c3b8e0494cb0bd1e4407458d553ec5f5399a500b2291a164d853a48f5f9703503849d192fc234495e410761a16555d492b453671426393429898655875e4eb),(29,0x16765d2b56da062cef47d6453cb3689945fce34a1131dd665619d50ca7659883b17335c3b)]),
  ([6,5,2,1], [(64,0x288701081002498244380c4c01802e09cb61584f3787e1301e1d06d0500d0f00a00c920c82b2e85a0a050124d81e0181b80e01c960d8040b0252d0541287204808004900c0261386c030020a80609000),(64,0x37c861fc1f370ae1f075070152909d1103d02ccc268930e833308bb1885b0a4ea2e08a16051380d920079080192a0761bc1603c9e25c3e0dc0531894198340b4bc2d45c154e42105212cda1e87306813),(64,0xecca30c6a18cf23acb922c593a0e122081084a91dc172989f1183f338c7254670d4f6310bd1905d3b0e52308514ce236c821ec2206caa28c7110c11348a0264400e4c8304681842f3c0be2dc5e15ce6),(55,0xd73d4b3344f93bc8f2b4d532c6b3e8f33a4892c4a711cd633cf7314653d0ed234e320c232c8ab34ca1104d0324693e0f12fc5f3b8e723887374af1f41d2b0a5114d43349b)]),
  ([7,4,2,1], [(64,0x68133608a17810200790c82b288540a0212604a10cba1b0401885b0500d348840d80a00c7a0b0252704e088440f4b419818038071f8300102607c961203e18012020011e02a08042030020903c07800),(64,0x1484b308bb1d06d104e42e06a18c1c054da34c8c2143702cae2087b0d02d2745613c233189a130452f0b51b867064de240641741603cd42187f0e031014a81f02e09c9e25c50124c01c8460fcb61a061),(64,0x74e236c94234af20c352b0a515cce31c9b310bd1d86f398df2446505cdc3548e21c392c0a91f42f2989f16051320c11cc473a8be2dc701a41b380d92488b17c11358882043a0ccaa28c550a4cc28099),(41,0xd13a4b332ced38c952b4cf314773b8e73748f2c4a7164d0324eb2fc713a0e124cd72243b2c8ab334a114cca30c753b0e52e46b)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_19_89_checked : PLift (checkBox [3,5,19,89] [7,5,3,2] (2,1) p5_19_89_rows = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_19_key_check : PLift ((∀ s : Fin 96, s.val.Prime → 19 < s.val → s.val ∈ p5_19_keys)) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem p5_19_box (i : Fin 16) :
    ∃ (caps : List ℕ) (rows : List Witness),
      caps.length = 4 ∧ (∀ c ∈ caps, 0 < c) ∧
      checkBox [3,5,19,p5_19_keys[i.val]!] caps (2,1) rows = true := by
  fin_cases i
  · exact ⟨[3,2,1,1], p5_19_23_rows, rfl, by decide, p5_19_23_checked.down⟩
  · exact ⟨[3,2,1,1], p5_19_29_rows, rfl, by decide, p5_19_29_checked.down⟩
  · exact ⟨[4,3,2,1], p5_19_31_rows, rfl, by decide, p5_19_31_checked.down⟩
  · exact ⟨[4,4,2,2], p5_19_37_rows, rfl, by decide, p5_19_37_checked.down⟩
  · exact ⟨[5,4,2,2], p5_19_41_rows, rfl, by decide, p5_19_41_checked.down⟩
  · exact ⟨[5,5,3,2], p5_19_43_rows, rfl, by decide, p5_19_43_checked.down⟩
  · exact ⟨[7,3,2,2], p5_19_47_rows, rfl, by decide, p5_19_47_checked.down⟩
  · exact ⟨[9,4,3,2], p5_19_53_rows, rfl, by decide, p5_19_53_checked.down⟩
  · exact ⟨[5,3,2,1], p5_19_59_rows, rfl, by decide, p5_19_59_checked.down⟩
  · exact ⟨[5,4,3,2], p5_19_61_rows, rfl, by decide, p5_19_61_checked.down⟩
  · exact ⟨[7,5,3,2], p5_19_67_rows, rfl, by decide, p5_19_67_checked.down⟩
  · exact ⟨[7,5,2,2], p5_19_71_rows, rfl, by decide, p5_19_71_checked.down⟩
  · exact ⟨[9,5,2,2], p5_19_73_rows, rfl, by decide, p5_19_73_checked.down⟩
  · exact ⟨[7,4,3,2], p5_19_79_rows, rfl, by decide, p5_19_79_checked.down⟩
  · exact ⟨[9,5,3,2], p5_19_83_rows, rfl, by decide, p5_19_83_checked.down⟩
  · exact ⟨[7,5,3,2], p5_19_89_rows, rfl, by decide, p5_19_89_checked.down⟩

private theorem p5_19_bounded (s a b c d : ℕ)
    (sp : s.Prime) (ordered : 19 < s) (sb : s < 96)
    (ap : 0 < a) (bp : 0 < b) (cp : 0 < c) (dp : 0 < d)
    (high : 2 < indexProduct [3,5,19,s] [a,b,c,d]) :
    ∃ k, k ∣ factorProduct [3,5,19,s] [a,b,c,d] ∧ k.Pseudoperfect := by
  have membership := p5_19_key_check.down ⟨s,sb⟩ sp ordered
  obtain ⟨i, hi, key⟩ := List.mem_iff_getElem.mp membership
  have word := p5_19_box ⟨i,hi⟩
  have ke : p5_19_keys[i]! = s := (getElem!_pos p5_19_keys i hi).trans key
  simp only [ke] at word
  obtain ⟨caps, rows, width, cp', checked⟩ := word
  have ps : ∀ p ∈ [3,5,19,s], 2 ≤ p := by simp [sp.two_le]
  have es : ∀ e ∈ [a,b,c,d], 0 < e := by simp [ap,bp,cp,dp]
  rcases checkBox_sound [3,5,19,s] caps [a,b,c,d] (2,1) rows checked ps es cp'
      rfl width.symm (by decide) with tooSmall | witness
  · exact False.elim ((not_le_of_gt high) (by simpa using tooSmall))
  · exact witness

private theorem p5_19 (s a b c d : ℕ)
    (sp : s.Prime) (ordered : 19 < s)
    (ap : 0 < a) (bp : 0 < b) (cp : 0 < c) (dp : 0 < d)
    (high : 2 < indexProduct [3,5,19,s] [a,b,c,d]) :
    ∃ k, k ∣ factorProduct [3,5,19,s] [a,b,c,d] ∧ k.Pseudoperfect := by
  have rel : List.Forall₂ (fun lo p => 2 ≤ lo ∧ lo ≤ p) [3,5,19] [3,5,19] := by decide
  have prefixBound : indexProduct [3,5,19] [a,b,c] ≤ (95 / 48 : ℚ) :=
    (majorant rel [a,b,c] rfl).trans (by norm_num [ceiling])
  have sb := last_prime_bound 5 19 s a b c d 96 (95 / 48 : ℚ)
    (by decide) (by norm_num) (by norm_num [ceiling]) prefixBound high
  exact p5_19_bounded s a b c d sp ordered sb ap bp cp dp high

private def p5_23_keys : List ℕ := [29,31,37,41,43,47]

private def p5_23_29_rows : List Witness := [([3,3,2,2], [(64,0x15c6e0507f014700588101c720602f100311084a16c4c1744e02c7607087034780780f098370a0390a85218c540086d04c7e0106f054060fc301245a12c0a1d41b030250d8270046c048030b44809000),(64,0x1a0591a8831d01a214440d44617c50184891e88b0447c0888d0ec2c0f46515867160692007105c8202073064841043210c341145c1344f18077074880387907c8a0407b084380a43a0ac3c14c6415466),(9,0x6b218471888c1f4232383e)]),
  ([3,4,1,2], [(64,0x1104f118510386701419178720406906c260c4280cc3e124401504b0206104c6c028630542b088360b443138450085b03466010181740f0943009c3d0fc07180120241f0a8211085a030030903c0181e),(49,0x591c43b14c741ac1d1d8351584d1606e194171c0380bc3a14047148680685f1cc111a81c1d4320a4341045513057188141b40b190161bc2c08c370b839)]),
  ([3,4,2,1], [(64,0x13c45140460645d1c80f1a0050685e0403109c320a0490fc54128401846c024620500a0ac210d82c088431384416c0d198030605c0380409430098480f807180120201f0a820108011680c0082407800),(49,0x591c43b14c751ac1d1d83515c4d1606f194171c0390bc3a144471486906c5f1d0111a81c0cc290d05512c411584c1b4630546e02c64058370b4230e02e)]),
  ([4,2,1,2], [(64,0xf80b10020154171302215c2c0b838038430143a040450684f07051098310a0330203d0fc141241f1501612c210ac2d00837034420103903c191381b0c02701c3c024131201e0542a0d80c00c1809000),(19,0x4714c3510456134231602f1103b044461401d148320a434)]),
  ([4,2,2,1], [(64,0x1544b0845605c4c0882d0b8430e40f110050e81013c1b1403109c320a03d0243e0284907c540544a080160ac2c0dc0d108030e00e010191381a09430098070f00804c480781400436030020900604800),(21,0x4714c3510457134231602f1143b044461441d148330a43402c40)]),
  ([4,3,1,1], [(64,0xf84910c1b1282d09c2e0e43302c3a1141d130171181e0a4230a8350343c01c36038410644804c42068250b0260c4090e0030c8151101c058210a02201434030060444006012090010c0080082004000),(11,0x3f12c2f0ec4d11c1f1382b0f437)]),
  ([5,2,1,1], [(64,0xdc450fc231182b0e43305c3a1041f1082702c2e0d4130d83d0844406c3e0882901c2a0c4150e00f0c81607440078090b0030980a04434048190f020068050a006034300501c00424020020401801000),(3,0x3b10c2f)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_23_29_checked : PLift (checkBox [3,5,23,29] [5,4,2,2] (2,1) p5_23_29_rows = true) := ⟨by decide +kernel⟩

private def p5_23_31_rows : List Witness := [([3,5,2,2], [(64,0x2dc4109ca80605210c631b8541147f1c0902040b1c8ac0700d2f42d2b8380780f1243a1684b0f07621c78008a304c042d02429415018511086d1f86f028ab06c0c0dc480e4012881200c3f1b0090d800),(64,0x1f0b62702629c8d05cc7020b80a0a9064c914c440a86415446200661c457244821ccad24c1d2100e2f82e2bc1f33c103004a0c0b10ec2116c4c0f4771744e22079264a4228141ec052d4252981631807),(64,0x2548625cd1308322cc2334cc40d0d517c501849b2307d2748e320b927c292a81a328bb0ac653304719c58248831a474250852fc2f2c096080d0044c10c4b2088d2170c3134330f85e13c891e8602688b),(19,0xa13386b260d431435358622788f280cb2f02c334681646a)]),
  ([4,2,2,2], [(64,0x1140519055058071982615c181d8281e0380a8490e84b02c3c16c0d1740f1b42e07c7e1bc300844010802148130106315015018251d4270dc480e40a1680c0706c0b41e0fc011441200c240d80906c00),(64,0x188831d035214471a0590686a1e82c1f04d0f84f17c11184801c43208c821cc34210441945605c0819c58064771a4291e42b1287b0ec4c1704e0385e0406e0bc600807f1c03108881104720cc4314c14),(3,0x6b1f450)]),
  ([4,3,1,1], [(64,0xf43703c3e1241b1282d09c2e0e43302c3a1141d05c4c1181e0a4230a835034070f036038410641312042068250b0260c4090e032028151101c058210a02201434030060444006012090300200208010),(9,0x3f12c2f0ec4d11c1f1382b)]),
  ([5,2,1,1], [(64,0xdc450fc231182b0e43305c3a1041f1082d09c0b0b83504c360f42106c440f8220a4070c41503c380c8160744007825024030b026028110d0120643c0801a014280180d0c01403801090080081001000),(3,0x3b10c2f)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_23_31_checked : PLift (checkBox [3,5,23,31] [5,5,2,2] (2,1) p5_23_31_rows = true) := ⟨by decide +kernel⟩

private def p5_23_37_rows : List Witness := [([4,3,2,1], [(64,0xe84b03c05158671302b084721a02c0f4220cc3e13c3404c0916850184140940a06c6c188260dc1c108381240d00c541280e07c041982a080310f0321381202019180240683600448030020780606000),(51,0x5f1c447164751ac2f1d8411745305c5e1bc650a4701143b11857134111cc581a42d1d06a0b83f0d45b100510540b1706d14863058270746e190430a03911055)]),
  ([4,4,1,1], [(64,0xd42f0d8450443f02c46154120841b17056088310ac380c84103448108510381d05c58090520782d0d02e0f40900c440403e0281915020068290c02a014400300605450070160b001020020602805000),(31,0x4f17c3b12c6116c27188371344704c4e1745708c5e0e4330e84910c0f128590945307c6016826)]),
  ([5,3,1,1], [(64,0x170560b8390cc0b0e84507417118510782908c581482a0d40d01c3c0d8410381904c481081a094540b026024030e032028151101c0582114028088050d00c01811100180482400430020020500404000),(27,0x4f16c3f12c5d15c2f1783b1344707c4e164530ac5a0f43703c4910c1b128550b427)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_23_37_checked : PLift (checkBox [3,5,23,37] [5,4,2,1] (2,1) p5_23_37_rows = true) := ⟨by decide +kernel⟩

private def p5_23_41_rows : List Witness := [([4,4,2,2], [(64,0x1245c09c8d0e81833cc01b44b1780b0f07e2446f0702f1800d288b524c400783103cc6144b719042008332206604c042642422837054062f45b0e46c1740a2401b0b80c2d03f0c063004870480316809),(64,0x2fc9d1287b0a08e0ec19340ae3046e27c4c17c2a0f4d21fc9230c1d13861038a32d881250411c81f0c81031ca5148b81949610c210d0d832476224542e867050450149a1e02522c381a41601cab2f89c),(64,0x2a4562f047370cd1e8581acad3789e1f02923c1a344af308a01342b0f8d3200b13107113c62354822547308011320a614cb921097110220d4d9328772a0552ec68118db26ccc1e426230571a817020ac),(25,0xb335c862a8dd3385937c7d2c0a10b0d42c8c5140d620c7429c8526023368cb)]),
  ([5,3,2,1], [(64,0x14671582b13021040791a03d0b033088841e84f0f8130d009168611402506c0a1b0620dc260707e108490e00d00c541281f038041982a0c4201e03c0c807138120640818024068011200c0081e06000),(64,0x1d46b0bc871d87d104881745305c6f178650a4811c0450ec8c208571184d044731a4580b423214741ec6a0fc2e0d48616c7c144400540b1b45c18c5209c160747f1b843190390a08a200551104b0e80f),(9,0x772245f1c48d20c4723859)]),
  ([5,4,1,1], [(64,0x443f02c4c154460841206c5c194560c4220ac6c0e0661043203407144420740e05c58090520b41e1a0340f42e024030403e0640a150200a41a190300a8051000c05406070160b0010f0080082801014),(49,0x631cc4f17c751bc3b1d84b1845b09c711886b0dc721344704c5d1385708c6d1783919c331d06e1243a10c591282514c1f18069168350982f1c06a11436)]),
  ([6,3,1,1], [(64,0xb83302c68188450e81d05c511182907823160520d42a034071903c104360640e04c4810825068540b0310980900c600e0320540a1101c08416140280880503011018400601200430020020500404000),(43,0x5f1ac4f16c6d19c3f1b84b174570bc69178630ec6a1344707c59138530ac651683d0dc0f1b0661243e10c1b1544a0b4271706115839)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_23_41_checked : PLift (checkBox [3,5,23,41] [6,4,2,2] (2,1) p5_23_41_rows = true) := ⟨by decide +kernel⟩

private def p5_23_43_rows : List Witness := [([5,3,2,2], [(64,0x1c8182d4ab16c9c02c4c10833318762dc260705d0344e244870dc780a01e03c5224c020e42a2f46d18c13150041f82e1bc15018991243f0c05a0284b1d42506c0c0d827144011b01200c2d1200909000),(64,0x208c30c8731a4192d8ac1709d134432103431c772e0ae0745e27c0e13c4524888324381e4ba0a41f040a314c942283a1ec2b084be1b86429414154960143c33c7f3002f1c0660585701c9a1284020431),(64,0x3347d08ca72608e0f8d1308682a45934c83310741a81a278d5110850d4c82e4af17ca014046224ca1e8bb2c420184112908b3303b1f02c088bf194a6158972343d340803047119ca805c580209b34841),(17,0xb33388f2a8d43146b358862c0a111ccb2f0b21888c)]),
  ([5,4,2,1], [(64,0x9c1a17810228492003f0c828288611509804c4a024401e46c0ac6208414028430d87a0b0222705b1380d11003198250605c038041f83d0c0262584801c3e1801f048081e02a080011680c0082407800),(64,0x1448811c3a1ccaa1a4a006c5f1481122c811d0331a829070a3154992304b208410d0ae1b4a418c56268151300b214371ec6e0b46408c162404f218450e07c0b8a819c9e0645d1400f118051fc720c468),(43,0x952b47723cb129c592c87124c890ecab2849414c752b06b0748d20c760d4a515c9b2384d2c06f2986516017244870e47d1c02f2a492)]),
  ([5,5,1,2], [(64,0x6cb528855108990204c0e4c01cc602dc2604c57028911f831078750a0152704f0f093008332e85a03451010780ac181bc0f258490d82d2d05401c4b1c825048092403009c4e0040c00c2a1200609000),(64,0xe07c1a42f070b628c5610c9a21c4d0e8c12b874184b8294141604502ccc2487f30c3207c7618c290589d228500f4940d0212eca81b85b27c0e1483f014c61e4662f42c064701741025c84128371ec2e),(64,0x8caa2848e104c81a0bf2b05f34c863287d1a81d290d51109b2203b308af188b92985911880310b108077190172788b33c3e254820d4222f0a9170a023453100c71e8672f8ab068711781134898214c9),(19,0xb33448f2b4d432c6b358892c0a711cce314b21948c34083)]),
  ([6,3,2,1], [(64,0x15821130101e4720f4680cc2c0888413c7a04c3e0243425861168251401b0500a1b0620981c1f8491080d0e0032405407c4a03804198310a8201e03c01c32138190480818024068011200c0081e0c018),(64,0x1782922c81114700ec9d24c8c15c821344604473278692502d160232147b1d03f1a8350b89716c861447c0544002ca226063170271481d0587f10c6e0e4640a091228552004b1100f0e805270672482b),(33,0x8f28477224a526c5f298712348311c9f2548e164752806b0bc871f476104a32645d220172906f26865)]),
  ([6,4,1,1], [(64,0x844606c121945c0c4560ac221b0410e0660343201c7c144480744205c0e1602d090520783d0d0090b8031e044064100f80a150290801a190300142a10015030061401c0582c0043c020020602801000),(64,0x2285f1d46f0ec851fc7612c612185b09c711ac620dc811347b1c84704c881748215c4e08c6d0e467178331d0491b8430e80f210591f82514c4a07c600d45a0bc261e4701146a0443f0d80b200551307a),(7,0x7721c631cc8920c4f)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_23_43_checked : PLift (checkBox [3,5,23,43] [6,5,2,2] (2,1) p5_23_43_rows = true) := ⟨by decide +kernel⟩

private def p5_23_47_rows : List Witness := [([5,6,3,2], [(64,0x305742b09057c7b19856425bc095a7040c32b9511b5201603c42c27048022d568211531bc5a3f5b0064cc010b7185140c0ff06c062a55c1e0636900d300ab155080900f5406c15cb43f01800c602a000),(64,0x1a5521b921165d40f50c3c1bf0a0db6a813318b15a485551381c12316c3f4382a054fe6c41a33405600b82716b21d561c85d1891572031400e46cc1c33c072e8aa574794b064121170cd02078096940e),(64,0x109110b51672432404e56d01d660d0021832ec9f5b88a564755787a4b46578049461cb0d10339db607cd2028bd698c25d4ad245605107c4bc6712d1a0d9050850a6f426365a80458c311772bc935887e),(64,0x88d56f8da6a58d315782c09458d471fd321a84e47439489d50f90d3c5c00a4dc6ac1463cc75e8b2259652056a219554e4717b124171d743cf37082b379ad058c96c8ce604b92756c221574ec734985e),(64,0x2796d225584f0747bd2717dda10d123d9c50b8e1728e66d599345842f0a05bc8b5693e1d9291152e7844a465cc0d5043a1b70819b34c0b618be2897123576249615147d4c06878c4c46dce0dd063a9b9),(64,0x28d7223941519317904d471cf0e1073adba08d9e359892958e5e49559148201331ade613d1e7443a3b5d63c9c1375ac640c85ecb325d66528824d4514e9ed495d8105103d1c30b0df6b8176497d26582),(64,0x67cd7628a65253479c5047dd20ecee685915f09859d4b20d367a4527b9d93d5c4381af64ccb5f89a5353d4a1db111133ddc60bce26559a614a15c08c56d3f1ddf24a9dd118f9789cd3a5b8670d461cbf),(47,0x1a37ad4f65df477cfb50df66818b29de874cef6894c4ddea14d945fc9b539f1770f871ce3659407cd2b778473e99d620a45cc8f509f5795d03b1bb)]),
  ([6,4,2,1], [(64,0x40971248a0fc800c828184a204c5426009128401e4ba0ac6c0846202843210361e82c0885b2700d13803110b4094660605c038040f47e0c026258071201f18012020780a820004421680c0083c07800),(64,0x22ccc204c20cc742e0291a81c28c552644b23041208342ec6d2b863290151589a02c4c214c60dc7b2f02d1b823190162744f240452187c0b8b519ca80645d2780f140051187f300311c8b609c680685e),(64,0x164c92fc712c893224ca0ecab28453250cd30c752e46b2b01d234ce20cc40d4762bca515c9b1348e31cbd1bcb0194a605c5821cc80e47d2f82f1c0a927c51248472203a304732dc692a81b17ca004452),(11,0xb332c952b4cf3147723cd02c4a7)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_23_47_checked : PLift (checkBox [3,5,23,47] [6,6,3,2] (2,1) p5_23_47_rows = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_23_key_check : PLift ((∀ s : Fin 51, s.val.Prime → 23 < s.val → s.val ∈ p5_23_keys)) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem p5_23_box (i : Fin 6) :
    ∃ (caps : List ℕ) (rows : List Witness),
      caps.length = 4 ∧ (∀ c ∈ caps, 0 < c) ∧
      checkBox [3,5,23,p5_23_keys[i.val]!] caps (2,1) rows = true := by
  fin_cases i
  · exact ⟨[5,4,2,2], p5_23_29_rows, rfl, by decide, p5_23_29_checked.down⟩
  · exact ⟨[5,5,2,2], p5_23_31_rows, rfl, by decide, p5_23_31_checked.down⟩
  · exact ⟨[5,4,2,1], p5_23_37_rows, rfl, by decide, p5_23_37_checked.down⟩
  · exact ⟨[6,4,2,2], p5_23_41_rows, rfl, by decide, p5_23_41_checked.down⟩
  · exact ⟨[6,5,2,2], p5_23_43_rows, rfl, by decide, p5_23_43_checked.down⟩
  · exact ⟨[6,6,3,2], p5_23_47_rows, rfl, by decide, p5_23_47_checked.down⟩

private theorem p5_23_bounded (s a b c d : ℕ)
    (sp : s.Prime) (ordered : 23 < s) (sb : s < 51)
    (ap : 0 < a) (bp : 0 < b) (cp : 0 < c) (dp : 0 < d)
    (high : 2 < indexProduct [3,5,23,s] [a,b,c,d]) :
    ∃ k, k ∣ factorProduct [3,5,23,s] [a,b,c,d] ∧ k.Pseudoperfect := by
  have membership := p5_23_key_check.down ⟨s,sb⟩ sp ordered
  obtain ⟨i, hi, key⟩ := List.mem_iff_getElem.mp membership
  have word := p5_23_box ⟨i,hi⟩
  have ke : p5_23_keys[i]! = s := (getElem!_pos p5_23_keys i hi).trans key
  simp only [ke] at word
  obtain ⟨caps, rows, width, cp', checked⟩ := word
  have ps : ∀ p ∈ [3,5,23,s], 2 ≤ p := by simp [sp.two_le]
  have es : ∀ e ∈ [a,b,c,d], 0 < e := by simp [ap,bp,cp,dp]
  rcases checkBox_sound [3,5,23,s] caps [a,b,c,d] (2,1) rows checked ps es cp'
      rfl width.symm (by decide) with tooSmall | witness
  · exact False.elim ((not_le_of_gt high) (by simpa using tooSmall))
  · exact witness

private theorem p5_23 (s a b c d : ℕ)
    (sp : s.Prime) (ordered : 23 < s)
    (ap : 0 < a) (bp : 0 < b) (cp : 0 < c) (dp : 0 < d)
    (high : 2 < indexProduct [3,5,23,s] [a,b,c,d]) :
    ∃ k, k ∣ factorProduct [3,5,23,s] [a,b,c,d] ∧ k.Pseudoperfect := by
  have rel : List.Forall₂ (fun lo p => 2 ≤ lo ∧ lo ≤ p) [3,5,23] [3,5,23] := by decide
  have prefixBound : indexProduct [3,5,23] [a,b,c] ≤ (345 / 176 : ℚ) :=
    (majorant rel [a,b,c] rfl).trans (by norm_num [ceiling])
  have sb := last_prime_bound 5 23 s a b c d 51 (345 / 176 : ℚ)
    (by decide) (by norm_num) (by norm_num [ceiling]) prefixBound high
  exact p5_23_bounded s a b c d sp ordered sb ap bp cp dp high

private def p5_29_keys : List ℕ := [31]

private def p5_29_31_rows : List Witness := [([5,3,2,2], [(64,0x2689c100422ac4a1304e2d4b716c5d3180b0340f1d8780701e21c260a02a244930dc39148542f463008040186d1bc130547e0b8302643f1244b2d05a0280c1d41b0942724036004031b0120b44802400),(64,0x6480208840c83426c9d1049f10c452b0ae1344f2d8b8170ba1786031cc9038101dc790747b07c212208a0a42b248940e0960e83c28c53154572f8c01906633c0501c6e1c0141c8160607f2042f0c433),(64,0x1f4232308e2603e29ca9164c2310681a8d134cd51d01a20c85278a0110462b4af2c4502e4bb17c61320ca330111e87c080222248b2342c25c3b0f4a4298a8158582fcc1194c319c69340d2020711cc17),(17,0xb33388f2a8c51acd435886284472c0b22f06232ccd)]),
  ([5,4,1,2], [(64,0x98281fc810c4332283e1009726449288540200a1846304c151b020088791ec2b0b4840d8431149c138020105b1740d03c660602509c7e0c03d0fc9612007024600481f1e02a1080100c5a030240f000),(64,0x278a0140522a4ab17c111a06a0681c1cc750a480208320d08b234412609a1284c28ca5154572b80b188140586d1bc231e87c0b02e214870dc39240441189d27c4f144a80145c1780e040671a41906c72),(45,0x952b47723ca7164b02c8712243b24894284532a8ac1ac1d1d07620c352308e26c4d290a6158582bcb11946e1c07d0bc86220380e89124c47)]),
  ([5,4,2,1], [(64,0xa07f200310c88a0fc4025c981244a288540240a1846204c141b021088791e82b0b0840d8432704e00c0416c5c0340e19818094261f8300f43e2584801c081801207c201e02a108010085a0303c07800),(64,0x27ca0144522a4aa17c111a46a06c1c1cc740a481208330d08b230412649a12c4c28ca4154562b80b18c64054161b46e1ec7c0b42e214860dc38240451189d2784f140a80145d1780f040671a01906872),(45,0x952b47723ca7164b12c8712243b24c94284532acac1ac1d1d47620c352348e26c4d294a615c582bc6505c6f1c07d0bc87220390e89124847)]),
  ([6,3,1,2], [(64,0x88671a42b0b4720c8341e47b0f43f210080284f14413258151681a0706118c2509c6c0dc391f842008041244b0349003c5407c211982a0c4331e03c01c09138120641b180240d8011200c0783001818),(64,0x1b8700ec80208441188b2344d24811250561609d27c231a06a0b02e1cc351e87c0f8402148702c501481425c162645b174a207462190260a06d1bc380e87f204431148a0144a1300e2441024c5515c9c),(35,0x8f284772249b17ca42987120c472308e25459278a01ac2f1d0761f4412188814c9805c9a1705e28ca519429)]),
  ([6,3,2,1], [(64,0x1589c084671a02b0b0720cc341e47a0f43e210090284f14013258141681b07061188250986c0dc381f84200c041244a0349003854080660a8310c8780f0070204e048190686009036004021200c0c018),(64,0x194291bc700ec812084522c8c134930449415c582749e08c691a82d0b8731d0351ec7c0fc402148602c5114897054980585b170a207463190270a06d1b8390e87f200431108a0144b1309103c9204055),(33,0x8f284772249b17ca52987120c472348e2545927ca01ac2f1d4761f44121c8814c9905c9a1745e28ca4)]),
  ([6,4,1,1], [(64,0x11811200121301b15456084221702b194660c4321b03801c411080d1f00e12017144520741e160240b42e1a0340f43e02478028440401906854080290a8640c0061000c054161401c0b0020f00806004),(64,0x1cc8313c892285f1bc3b1d4761fc4b2148616c27184621ac371c4721ec47204132084d1388815c231745e0cc6d1b8390e87410c7d03c7e1244a2105307c59168251802f1a46a0d4361c03f1e40b1e845),(3,0x7721c63)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_29_31_checked : PLift (checkBox [3,5,29,31] [6,4,2,2] (2,1) p5_29_31_rows = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p5_29_key_check : PLift ((∀ s : Fin 35, s.val.Prime → 29 < s.val → s.val ∈ p5_29_keys)) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem p5_29_box (i : Fin 1) :
    ∃ (caps : List ℕ) (rows : List Witness),
      caps.length = 4 ∧ (∀ c ∈ caps, 0 < c) ∧
      checkBox [3,5,29,p5_29_keys[i.val]!] caps (2,1) rows = true := by
  fin_cases i
  · exact ⟨[6,4,2,2], p5_29_31_rows, rfl, by decide, p5_29_31_checked.down⟩

private theorem p5_29_bounded (s a b c d : ℕ)
    (sp : s.Prime) (ordered : 29 < s) (sb : s < 35)
    (ap : 0 < a) (bp : 0 < b) (cp : 0 < c) (dp : 0 < d)
    (high : 2 < indexProduct [3,5,29,s] [a,b,c,d]) :
    ∃ k, k ∣ factorProduct [3,5,29,s] [a,b,c,d] ∧ k.Pseudoperfect := by
  have membership := p5_29_key_check.down ⟨s,sb⟩ sp ordered
  obtain ⟨i, hi, key⟩ := List.mem_iff_getElem.mp membership
  have word := p5_29_box ⟨i,hi⟩
  have ke : p5_29_keys[i]! = s := (getElem!_pos p5_29_keys i hi).trans key
  simp only [ke] at word
  obtain ⟨caps, rows, width, cp', checked⟩ := word
  have ps : ∀ p ∈ [3,5,29,s], 2 ≤ p := by simp [sp.two_le]
  have es : ∀ e ∈ [a,b,c,d], 0 < e := by simp [ap,bp,cp,dp]
  rcases checkBox_sound [3,5,29,s] caps [a,b,c,d] (2,1) rows checked ps es cp'
      rfl width.symm (by decide) with tooSmall | witness
  · exact False.elim ((not_le_of_gt high) (by simpa using tooSmall))
  · exact witness

private theorem p5_29 (s a b c d : ℕ)
    (sp : s.Prime) (ordered : 29 < s)
    (ap : 0 < a) (bp : 0 < b) (cp : 0 < c) (dp : 0 < d)
    (high : 2 < indexProduct [3,5,29,s] [a,b,c,d]) :
    ∃ k, k ∣ factorProduct [3,5,29,s] [a,b,c,d] ∧ k.Pseudoperfect := by
  have rel : List.Forall₂ (fun lo p => 2 ≤ lo ∧ lo ≤ p) [3,5,29] [3,5,29] := by decide
  have prefixBound : indexProduct [3,5,29] [a,b,c] ≤ (435 / 224 : ℚ) :=
    (majorant rel [a,b,c] rfl).trans (by norm_num [ceiling])
  have sb := last_prime_bound 5 29 s a b c d 35 (435 / 224 : ℚ)
    (by decide) (by norm_num) (by norm_num [ceiling]) prefixBound high
  exact p5_29_bounded s a b c d sp ordered sb ap bp cp dp high

private def p7_11_keys : List ℕ := [13,17,19,23]

private def p7_11_13_rows : List Witness := [([2,2,2,3], [(64,0xd8390f8071040a12c441380f14412054590685c07427080610a8640b4320d43800c3d018400244a1340e14011050551601907026180290b0310d03c014081244c0341015018094280c0041200c09000),(39,0x4717c2319c6a0ec431185305c5b1781f088631982f1a4370e83f1080b1144f14813058571681b1741e1882b1942e1a033)]),
  ([2,2,3,2], [(64,0xb8350dc390f840020420284d13c1114413158151601a1681c078610a42b0b4320d0360f4050fc07128091300e138100485515c19098600a02a0c4330083c010061244b0340f0602509c3000c4809000),(37,0x4717c231a06a0ec441185305c5c178200886519c2f1a4380e84110c0b11450148141645b0745d07c62084640b066)]),
  ([2,3,2,2], [(64,0xd0380e8080f04d13c4003842040531541415c160605b0a45d0ac1c0782f0c4330dc050e4071284c02c4e0fc0d03c521501305426168280a82e0c0020d8040184912c0a030510482509c2d00c4802424),(37,0x47188231a06a0f844118590685f184200886519c351a43d1404110c1111456160170645c1782c0746007c2119032)]),
  ([3,1,1,2], [(45,0x230a4170b02e0740b08022044260a0140582b0b4050681c0200a07c21038100942704c150a8020101906c070241e0340f090120041803000)]),
  ([3,1,2,1], [(43,0x230a4170b42e0740b08422044270a0150582b0b00506c090281f0800f04025098130502a01019068070201e0340e09012008180180c)]),
  ([3,2,1,1], [(43,0x230ac170b42e07c0b0842204c290a8150582c06c07074090282003c25098110482805003064050181c0200d03824040010080403000)]),
  ([4,1,1,1], [(37,0x1f08c170942606c0f0741e04c2101c2205416090190680d0381c00c110480508006050090600c004020400402000)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p7_11_13_checked : PLift (checkBox [3,7,11,13] [4,3,3,3] (2,1) p7_11_13_rows = true) := ⟨by decide +kernel⟩

private def p7_11_17_rows : List Witness := [([3,2,2,1], [(64,0x114460bc110cc3b0d01d0fc21100430a42202c2d03c2e0c417040390c81b0e83d0701f0f80509c20108090a02b0342c0540e0dc30058190e01a0f0030941e010070982a04c0c05036004020900604800),(3,0x3510423)]),
  ([3,3,1,2], [(64,0x10c26148450d4281540b0e02b15c0e0e82d0745a0403d080131303f0881513c0510832094510203409c54028370a81a034390700f1243c07c1212c020844e0103109033024360640c06c48078010c018),(25,0x471642f1705e1041711053118291582c1603b0b85b0443e174141344008c16)]),
  ([4,2,1,1], [(57,0x2f0dc230e43a0ac170b4330b81f0d40b084360883804c290542a06c160c42c01c1d0c8090783403c0a09420044120a003064140141a0c0060700d0200e09010004020600403000)]),
  ([5,1,3,2], [(64,0xdc3e04c39100661b41d0544a1086f07c261307908428138550147b0c82a15c07038840d061024100d83d068120fc6c070490782512c021e027150040c406034331800f0f01906c480900100c3003000),(64,0xbc5c208891788b0ec6805c8d1106a1c4461cc231407d1d42c148591fc860b85b02c81220381945d0508a0e8411b81610c691c020134451e8720882913c561f02b144580207e214350b4621680a04487),(11,0x7720c5f2308e1ac471d07614c80)]),
  ([6,1,2,2], [(64,0x38660ac2f130101b4311385205c6f0e03315019074750e85b07c3c10005098211080702c630a0490342a0b84b0500f1b030144160dc1c0e4021681e0fc0409406028271200c0b4130543606c0102400),(55,0x6b1d0591e87c188471a06a140710d4561cc77160790f85f08c7b110611944619c2c134111b8690c84f14c701541a1c8760ec5c15c201e03d1045e08843020601902912845)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p7_11_17_checked : PLift (checkBox [3,7,11,17] [6,3,3,2] (2,1) p7_11_17_rows = true) := ⟨by decide +kernel⟩

private def p7_11_19_rows : List Witness := [([3,2,3,2], [(64,0x1081a04c87160510a41c1b8151845a0c82b0787018c340b4051e4721283d0d80e1ec4c0fc10024841544e09819048570a01b1b4600c42a0086f0cc041e0490f00d12c0f15025060271b0300040303024),(64,0x1a83b200442248214c4605c8b17020234651782f0887419c381f4761a4410e80b2187f1401422081164521141d0588a1885b0b01f1c464174350b87a084731983e0dc081f075134400440a2147e1584f),(9,0x6b20c472308e17c231a077)]),
  ([3,3,2,2], [(64,0xa4420586e21c570bc2b070181c05d0c405078761c84a18c370cc0b01c78130390347e1484e0983f04c0f150280546d1682e0a80206c6f0c0041d4490d80612c0c14425048271b02d004031200909000),(64,0x20c4422485164460688b17c7423465184350887a19c3b2007c14069104112085610c1722084170580b045074191c48a1783207c771cc64180380d00808479134660e80e1fc7b14c4f1003c0501020455),(11,0x6b218472308e188231a07d1a83e)]),
  ([3,3,3,1], [(64,0xe4340347212c460e813038781444c09419050631482b0981a1a464160310b0051a8430c80b01870110380440c128230486114029090181882a00c6810430024041084808410088600a0010084002020),(59,0x5f1dc3f1f47e15c1f1746f178371d43d1ec7613c3e05c7c1541d19c5b1582f0786d170351cc6e11c3b0d80f1e4741343c0547a14c4e06c16194591502d0706b1985a0cc2e01c711b045)]),
  ([4,2,1,2], [(64,0xa4221280b10c2c0384c1142e05c100e031068510e833070051503d0981f0203f0a0211240a1082b0500d12c2d0584e03c30064020e41b0103c0941e01c27120090a813030150d818004030900604800),(23,0x4714c3515858104231104d1182f140110c8520ec34074550f82015c40)]),
  ([4,2,2,1], [(64,0xa42212c0b1102d13c0f130310b817140100e4321503d0e81f070050f82708049024420ac280344a0282c0544e038370c01905838068030f0250780701026120080a813030140d818004020900604800),(23,0x4714c3515c58104231144d1182f14411154520ec34074560fc2110c40)]),
  ([4,3,1,1], [(64,0xb44a0dc2e06c4c0e41d10c3a09c1e1140b0f029034460cc2a05c48038350b01908c1a104070e02507009108261100a0c4280540c0c81600c3408418014221000609011020120c014004020800404000),(13,0x3f12c2f1344e0ec1f0f4470f82b1240f)]),
  ([5,2,1,1], [(64,0x114460dc230e43f0e82b104170b4420cc2e07c440d40b0843609c220f4130e0290543e06c400583101c2c074090c81e03c3402825080110f01200c28064140141a0c0060700d0200e090100041803000),(3,0x3b10c2f)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p7_11_19_checked : PLift (checkBox [3,7,11,19] [5,3,3,2] (2,1) p7_11_19_rows = true) := ⟨by decide +kernel⟩

private def p7_11_23_rows : List Witness := [([4,3,2,2], [(64,0x16c9621c2b070571c09c060050c45d128762881e02c371c86301c331e09103439098521f8131383f24c0f0a0541b499054020b85a0a81b1bc040c0491d40a0d80612c9003025048271b0010b44802424),(64,0x2b0501047c2a0950443d1a456208ae26c1710c5c25c880b0582107127419114321788a1dca307c381cc6427c080d06013479294920840e0e86614c7f2ac1413c401ec940403c0a4552046e268161082f),(45,0x8f2a86b2c0862c847230a11888e29c231a0ad1f4a90f86a20caf1109822459214b12781a17c8b290201d065280351848d1e8a60883b19c80)]),
  ([4,4,3,1], [(64,0x184a4038900b419170481ecaa05033188810b8b0068391f0680143414c822840b0e8590188804454100a20302b168792a0120c4600b0181e8030c851200090e004148a002829160101e0010c00214028),(64,0x198851c4b40783d1b08b2e82415c43218722940f2443e3005d1248c2ac1511063298920bcb106c5e1287d1a4ac058980d421190832c81c0ec7e1a807224b808855104841c0a30343c16c8a2a41315842),(64,0x2fc77314973184f274b71bc9e2f4271d4c323cbe11c76254c4134af26c67258b507c4e1b49c2ec2521c732d83f3046e234bc098451d0a724cc217c4b238ad05c99118652501d1307f1acae268372e423),(1,0x9f)]),
  ([5,2,2,2], [(64,0x124720884515418014880a04b0e05b1f80b0b85701c8a0a83a1746d034900c01d1006304c3c1bc0f07c42148750540209448084540108709c371680a018391b00c0703f0481e14401090030d80906c00),(64,0x17c82248321948e0f86121071044940d04419c7705c9a128732582311869158790649c224291307f0bc581ec0822c2b1383b178811b80e2443110464234140f4601c01024c3308043198531d81626426),(29,0x862606b2787d2805020c8f18885254351a09b1d09711c6a1e81a2744d2005927c8c0b04f)]),
  ([5,2,4,1], [(64,0x1c08305c422a87c040231285d2101825c2b148650908c0cc5e014980b03f19879034a00d0061b8151007a038211205b208160a4500885c00c960a83d1900b0c8040f80c07c4605020168280083c0281e),(64,0x6cae1548009c8f138612201c26c2f15869240a30dc6202471270432ac6a1f4112903812c7221419110ac14c7e048252344c17c86068990b45419c26238a10d46001c6f2682e104681ec0f2883612408),(45,0x952a4772c48b2c85924c9f1b49429c3b1d4af204a813c762241d2c057244632289d0c4581ac92294391cc9e114ad1b07f04ca60e84d1d087)]),
  ([5,3,2,1], [(64,0xb03d1905a074130e84b1a0101e4210f84f1b0140944c108051e8220cc50184091f8260dc54034340a8620281b0e0491980e07c3c07012128780803113807090040c860020190d80c12001078020c018),(64,0x1647621c2f1748b1ac881045e1bc172307d1cc531c0810a44615c742142d1945b2083b16069044860b83f1706d0548a134431a87b08c511b8161fc27110551f0720d42b1486302c800a0391586703c84),(9,0x772245f23471238471d483)]),
  ([6,2,2,1], [(64,0x13c0f19831130171b82e0e4500405b06c720c83d1501f0e805170270f849024600802b1080d0a04a028151b02c0dc4e038190c0160e0031681a0943c01c1e010261200804c2a03036004180080604800),(57,0x6b1dc591ec651f0471a47114c6a1d43515c7917c761045818c231e84519c4d1906f0bc46144111a0730cc551c03b1485d074740d03f158211e043178291004b02c620886d0b444)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p7_11_23_checked : PLift (checkBox [3,7,11,23] [6,4,4,2] (2,1) p7_11_23_rows = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p7_11_key_check : PLift ((∀ s : Fin 27, s.val.Prime → 11 < s.val → s.val ∈ p7_11_keys)) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem p7_11_box (i : Fin 4) :
    ∃ (caps : List ℕ) (rows : List Witness),
      caps.length = 4 ∧ (∀ c ∈ caps, 0 < c) ∧
      checkBox [3,7,11,p7_11_keys[i.val]!] caps (2,1) rows = true := by
  fin_cases i
  · exact ⟨[4,3,3,3], p7_11_13_rows, rfl, by decide, p7_11_13_checked.down⟩
  · exact ⟨[6,3,3,2], p7_11_17_rows, rfl, by decide, p7_11_17_checked.down⟩
  · exact ⟨[5,3,3,2], p7_11_19_rows, rfl, by decide, p7_11_19_checked.down⟩
  · exact ⟨[6,4,4,2], p7_11_23_rows, rfl, by decide, p7_11_23_checked.down⟩

private theorem p7_11_bounded (s a b c d : ℕ)
    (sp : s.Prime) (ordered : 11 < s) (sb : s < 27)
    (ap : 0 < a) (bp : 0 < b) (cp : 0 < c) (dp : 0 < d)
    (high : 2 < indexProduct [3,7,11,s] [a,b,c,d]) :
    ∃ k, k ∣ factorProduct [3,7,11,s] [a,b,c,d] ∧ k.Pseudoperfect := by
  have membership := p7_11_key_check.down ⟨s,sb⟩ sp ordered
  obtain ⟨i, hi, key⟩ := List.mem_iff_getElem.mp membership
  have word := p7_11_box ⟨i,hi⟩
  have ke : p7_11_keys[i]! = s := (getElem!_pos p7_11_keys i hi).trans key
  simp only [ke] at word
  obtain ⟨caps, rows, width, cp', checked⟩ := word
  have ps : ∀ p ∈ [3,7,11,s], 2 ≤ p := by simp [sp.two_le]
  have es : ∀ e ∈ [a,b,c,d], 0 < e := by simp [ap,bp,cp,dp]
  rcases checkBox_sound [3,7,11,s] caps [a,b,c,d] (2,1) rows checked ps es cp'
      rfl width.symm (by decide) with tooSmall | witness
  · exact False.elim ((not_le_of_gt high) (by simpa using tooSmall))
  · exact witness

private theorem p7_11 (s a b c d : ℕ)
    (sp : s.Prime) (ordered : 11 < s)
    (ap : 0 < a) (bp : 0 < b) (cp : 0 < c) (dp : 0 < d)
    (high : 2 < indexProduct [3,7,11,s] [a,b,c,d]) :
    ∃ k, k ∣ factorProduct [3,7,11,s] [a,b,c,d] ∧ k.Pseudoperfect := by
  have rel : List.Forall₂ (fun lo p => 2 ≤ lo ∧ lo ≤ p) [3,7,11] [3,7,11] := by decide
  have prefixBound : indexProduct [3,7,11] [a,b,c] ≤ (77 / 40 : ℚ) :=
    (majorant rel [a,b,c] rfl).trans (by norm_num [ceiling])
  have sb := last_prime_bound 7 11 s a b c d 27 (77 / 40 : ℚ)
    (by decide) (by norm_num) (by norm_num [ceiling]) prefixBound high
  exact p7_11_bounded s a b c d sp ordered sb ap bp cp dp high

private def p7_13_keys : List ℕ := [17,19]

private def p7_13_17_rows : List Witness := [([4,2,3,3], [(64,0x344390a092204d40f0422548400c45260e00184828409188512900c1945405468304b00607131032084740d42434038244801049400844014a00206114064050c01c031080342404000404180100c000),(64,0x686d17073318b5074231d8c92e03709879330d20e8291f093208d50f42c10c963604626488384071249c288e40284c18c522940d04c66154a805869160c22c4191b072314b407033088753203609478),(64,0x38c4b2788d3984e29ce903c572a8ec1ac5a2b4b306c6e174c72d81e1dcca09c7a334bc34c3b0a87d20cd60f82d25c863644726889370e21289d230a33940b13453298e803867158a905c6a164ac30cb2),(43,0xbf37c8f3acee2bc5f2eccf2f87f0bcdb22cde27c8e39c4f3a8ab3b45b2b86f178b707ccb2e87b338bd0ac7e35c3f0b8873689b228dd)]),
  ([4,3,2,2], [(64,0xac181b85b2702f1c01c174311c81e288050cc7618c07128371e00b13039138911f80f148930fc2604c540a0152642a1b45a0b86f06c020c0041d4060d80a12c0c240510941209c6c0b4011200909000),(64,0x1f0692b0500f4802b811254412089710c8405c581149b2202c0645c2748a1c41d1789f0c87307c6028c3408477294080e0791984d0e87b2ac0e13c3c2487f04053250402041415496108290585726887),(45,0x8f2a86b2c0b221847230a12386208ca71a0a91f46a2b43e2bcb12604421459118890689e22c5f2808d1d020184a40d422194a61e8672a03b)]),
  ([5,2,2,2], [(64,0x114760881814c491e0261544b0a057220050a85b228070e02e1740b0e8302400d0f06d18c0f1006f074131081f0547508452120251500209c870105a018370b40a0e46c0fc1c0481e1440100c360241b),(64,0xb08c2085f238840c8612483e0d065250111c467258441cc69268171187727019128791584c1ec291604e2247f0ac5c22c810202f1788d0ec31180910383d0cc6e19093040411c066050431c89908016),(27,0x862606b278a01f45020c8f214620d4951a0971d06a26c472747a27c4d1f05913c80)]),
  ([5,3,2,1], [(64,0x1681d0403d1a04b04c3e0844c050791b02213c7a10805094500cc261f8090d0611500a0dc620a80d06c0e1981c1243c07c4a048201e003138040c42401c32020600d8190301a1201e004020c00606000),(64,0x174881ac5e22c41230171bc7d1c053118730a4811d057208650b4582143b0b85b218111a45c0fc6a2284d054401b4230587b10c6e1447c110271487f1c8350a0552000b18c2b158391902c2100f0e867),(13,0x772245f2348e1c4471d4831d8590bc87)]),
  ([6,2,3,1], [(64,0x220130f0692481d050411a81e12c4226023130791c0241447a01429148060cc2a2000b0d05803039188110e89006c121a01c124400844a0887800c50010310a0090c80a180380401a120200043002018),(64,0x1146e26c4f11873270271f4a11547e2882d158830dc2e16c8403c65170890f46624c8a0543e1ac9407c1610c6c2644d11071268251387b1c82614c7c01ca00ac54204350b0592080d0d8631683b19091),(33,0x8f27c77294a621c5f234972386f11c9d1d49e1fc7628c572902f2145d218671788b0fc95230171b496)]),
  ([6,3,1,2], [(64,0x741019c931684a0f4690804c04c3f258151e46c0144f1ec420c825144080d0271f80a184540dc630a81a034392401c03c661243c12c12008211e00413831090070cc09180360640c06c1e004030c018),(64,0x2347d1107014c46274292007327c56208751942c160a20ec92214111a09416c870f86a1744d0504025c8a08c161e86d264501f0431bc2614845270350a07f1c80b18855204381902b15c0e0e82d24484),(33,0x8f28477290a62245f2309b2387111c9e1d0a020c76164a30bc8629495170881ac5e1049822c171b89a)]),
  ([7,2,2,1], [(64,0x1980f0b84f1b81704031140390c87206c3a16c540703d1700507c3e1f8270806002428124420282b1282c1b0150384e058370c0190e01a168030f0040941e01c26020480a80c05036060010082404800),(64,0x11c871a4881c46a22c53230351d4571d85f16079104811e82318c82114642144d118672182f1bc68044511c08a0cc520ec34154740745d1583f1787f1e0211006120029088431880b12c442102d1306d),(11,0x7d2246b2348e1dc591ec831f065)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p7_13_17_checked : PLift (checkBox [3,7,13,17] [7,3,3,3] (2,1) p7_13_17_rows = true) := ⟨by decide +kernel⟩

private def p7_13_19_rows : List Witness := [([6,4,3,3], [(64,0xc4c4195f0019913e034581011a0a2025943407104904100a503074055a0504a8440b10605251080084b4155e0091503c458184023d0301900564100284081c01129014500b014420150600040428050),(64,0x321021a5f44c0a3029953f0d10e072590134146c104a603598350758001668508111422a570444782c819690e014d452b081089142d41c159e152084095b0544b83c859791203042818954240033d45c),(64,0x2a99c5c4d844879810b3069a5430e1121462b4825d0234547c2d81d6a0e415de252485840266c518548b9600f3169e553121220c20a5b4554bc244f6174327a1243142c199f15609401d923e43570161),(64,0x850c30a9b5471562f492610f7178337a5252302d6e0677c9592562064cfa0d9ec70528588c940c6a7d55c4c49802d963f4d20e5c41cd65331061b4427e13429c0e664d50f0768056805da24244574143),(64,0x1b8437e5352700f668d60f5c81de025a5a3428467f1d14e0ab67572365131ea055b01b6990d38849751472b8835d4dc4587d820b7079a93944c78d4a21a115e0276c91954cba6b1813a05b7994d48889),(64,0x6a8e6135d852c87849796cd1a830bb6b5823a5e75392322a155f02b6d91d2f893614ec17dea4988d860c70b9b97cd5a25a21620fb0dded7092958cca6f06b7d95d4c899891973f8d30e9c54b16633507),(64,0x7ad2723a190bdba56c97889897b9c34aa1c32dbd7dd5e4cc9a8958c3fc3b7192d59cce1bdfa4d89d8a19b35c3e726035a90b11dfd7493967973369cc1ee065b5a7438e3129d54f0af5d8dd45c7e8241f),(64,0x5f91f61cee23e1a6ee23629ef4ae1d6f95f26e26635c74b8cf7ed3727a290fdca5adfe74d3a8b19f36dcd81d6e43c4b7593d5dcde1fe0a6ace7139d984d7a46e0d6b9833a9dc53c8b8597d6dd1e618ed),(39,0x1df87d8f8ae2e73d3f76e0f7797f3be1b62e1e6fe276392f27e2a72dff4ee2d7396f75d3e37e0b13dda5ee0e6bceb77617)]),
  ([7,3,4,4], [(64,0x130ff20e7101df54d8507094621cca02df944c9706d4a3380faf09b07e0d644d2578e208c66654af3986a960376a52d1b8fa1f8024c44b208067d1453240a2581a3341e384650c8694b07d0040532064),(64,0x70d0451c889d8cb031fa4ed141549871c1c52c8c33c10af5fe4609ca28208394f648d3052c176d5f280e30921219d9635cb00d16339c28b546b9659a2d038899aa3ad2e1be5d5dcfb0f07f6b8034c873),(64,0x7711d580a1a3ce4096135506865cd82c6c678035590a53a2d685c6c9699b370b5a8c3989d686acec0b6da4bc709799f5e0b93f03d8ac806bcf0011331d04d9897c40041bb8849c9b3021f64dc781463f),(64,0x1d44e98da45f4be40442bbe30216736d0f5025f74e07914a67901817110511af3520899ddb83300d7ed3c4545691099721090754c2367b34011af9ff5011916b072768b7302183d502459335015b0a03),(64,0x35416b0e047751e17f0c28a90744e509a1455598364b2b1e08785220d96529a943a42ab5e185646d96d9c374b6b2ea47943a8a1692a9ac3b42eb6e1c4c07197da05e4baaa0fd0fa2c5b4816c0f1b7d34),(64,0x2fead40843bc2315c8869d1b53dae47e1391e8539a241608c37150611ef48d54922a786e40e7f13d458579b2456189a7250abe14d23a7c6f4d104abf801414685bc224927a8c7350e08a1054492a0194),(64,0x28e917482785556a1599368b3b220978923c456629e95758ea0aed88655a9719d378b7b32a5799270ee295a8aba65ad3b82fb721d1ca606857a2eed0aa5ea3f83f8b56e6c4f2b82214d47613e646957e),(64,0x9d5b63dee54e87b1526990983312b271907122f58d88b9e5baba5fd4f9171626d919877290bbe63a5388f9f5be04ec08054246c5cc264a62c9fa35ce43efd8455224e8135817b12057791f1830d93962),(64,0x2929274f0285957a18dbb260a78d2494d672a29675c2cb661a56d9e37cb8b36a679d28c5a2a5acaca68ef0c2dd87a616897b2f2d1aa9eb1022e5be9e6c8f3b86221de656997f302ae7bd03112f18c973),(64,0x3d2e288e6669d80306af7c045bca335d1b73e2e61f26a90d84316b342049bda379e9bbba93f1666e91d88addcb432fa8ec909f9bf809434705dc2a4b6328e73d10bf95325282062c5819df48061c3a4f),(64,0xbde386f2eb9be48626b8436fb8f27f7014417b0b9318d74111bfc95a0e0748462c3e50a4dd4c0d58a1eca82de449713950a9a5dd886d5cb3aa77a129c5d6c2b69b0c6de87da32f6d2aadecc6e2f5c29f),(64,0x7bb1da8625ac5f25dae831eb58e6ec9c18aae6fc8f5c19358e44b00a1063c425175704a220c49b14956987655db3de94ab182ba9c882d3ab1edc7171a82e3891a830ab07c6345d4f9b9e6b614c6ad04a),(23,0x2bbc1a57c6b1ea89f3adaedaea3e63f0194b05a2715959da4af19a76d4)]),
  ([7,3,5,3], [(64,0x1f658019e14a04c6c08030809791082441a4f0c5032a02501d7e1813215036420189842a0313706590034661211a0f01e402490481f0057813830408240193101c600610c06448078004043001818000),(64,0x3e081970c3029e54b109140926d01b4f4843180da85e8430959c01e7e540608c9042a472151260da085fc18d85330a90c95437424ae066905882b03584199381221a6445a0f10e07a670034946c124f4),(64,0x441522667436c227f544618cd2a814aa1cc0cd55270de096b98006790989340ada203684558668e10a2bc48c6a9158c5a4b03c8398507b674e44986d12a485b0f50f2d01fa5968007789291c04d8a1b1),(64,0xb01271b84b925905b4b43d83db46181fe5a684e878d2a1c44e932295c1b23e440b513b20a5d6900b7992d428741462c6d4fc4f885980c703aa27a53043454ba0969c5b807dfa5048860cca046a57b1c9),(64,0x990cb04aa67b5ca4d111162ec54c9a9d5bc08dfe5148c61cce2ac15aa5f0735145589d9e0df09aba8054890d8a344aeab28974037849592819b38829af6041ae466356a350b1a30f30ea155719e3942c),(64,0x8206f929915b8b5a40f70fad28656096da23a6c44ac7213e4d8a9945c4b86ccfa106d587083979a53b1e74b90b1d4529422d5d1b63f444b613f21a616a00fa8dea4c50e156e98c0979c9b9401fb50889),(64,0x7b9cb4d512166ed8d09b9d9bd411ff5188d9a0cf05aaa7c5ce4545cbc15727a7970027aee025258b348afab68a7d1d146213568a19f0e30aabe8154c91d8e5acd52cab0a35d40ee16574a467ce60b6c1),(64,0x8264b6496f2dab4a45d80fed38696168ceab160c1ce4e8ad955c8b9a50fb10ad68756497da63b6c84bc7614e518b9756dcfe116d988087989a97ad3243c56baa548c5789cdba406dc50c8a995ac04ea7),(64,0x6ed02b762422e666b5ef4d91316aee8d57c9ddbe416e051c8e9a417aadf273d16176f18e09f9e9c180d4a9b0d3aba8b7d5d2466f456ca29f5c40aebf8194d63cd62ceb1a39d547217578a5a00e70bac2),(64,0x7d9d346af58f0a39f9c581d4e35eb2a3dd6476f857ca6a042fb0e0a64cb7ad6927661b58a843aec68364f659732ea9577043b5e1e595a73bac91de528bd762f6983fc46b6a216aacc4cc57bae558c979),(64,0x7194facdd747af929e8282eb6a4ddabf163a16c7839972ee967761f598efb2a535dcbea6447b6e226aecd95a335ea9c40ede896676b93716eef8d97d6fd06b848f9a9f345c5ebca399edc2b914b9b6af),(57,0x29fb9e3fbeefea1ddfa6ecfa7a275fee38eee69bef78f9c747efaa0eb776efda1a0fa5dde59ecb2fe9a88ece95d7ba76df899af8dd7e41ee29ac5fbce3a70ee59b9f746ef68f67f)]),
  ([7,4,3,2], [(64,0x24c4c5d0054b4ba09d083044e01d2f27055038c30c07c025a415c104e0f11f8cc214120f8f31801921c405a01b3f0b510890124022dc2412c044b0c0018540347b03cf02103d0603f2d00100c7803000),(64,0x424963084f5dce4021302f49d0a85642c510c47d029a54c89f1618004539318333c87f69d143345a218134eca83d0811841a33c88055b0105693d863071443f48a2d8435acd82441e128ff1b0b811425),(64,0x570806a135454a23385b60c144f0c92a4363d482189aa45cd017489059b14f8ab5a8f71918c07545348fe22db3480445b0f9364662481f51d002346d2e4460996e36c94085bc135754086f4b8bb0a150),(64,0x505212b96d3e8da19d8f08148355012386e6d92311d6f37069254226f54a5d9031c1982f0295c5513790a25dbf14178414e51c9312f89e0ad5343099314520c97a39c0b699332802d720596050e31c34),(64,0x53579418e61cd9b2fc2c550e14349a708535ece81d5342842e725566090f320355f55d3a9a94d91628dcb171844453d328aa0dd5f20dab460a53445e618176c93f2b039750f8195ad6351a518d3231b4),(64,0x72957441c55f95e3ad37291cc56585448cb0e1603b5ac464a67385f61d402b43a755626b98e46cd4625b5509222bdd73ec686411d3588f6dd242c5703746a648236f94b410716e59949972548df261c0),(64,0x4a1dd6594f6752a38dc41dd9f561c65fcec685cd56913584ee29dcf6203b759636bd1c745432c1d859591478d76e1252c9da1ad93531ba669275cce0655c1539071d19c4a5553889b70d7c3a4766782f),(23,0x1a374d67771de65d2b681c76895b3bdd0591d262dd95991f2cddb651bb)]),
  ([8,3,3,3], [(64,0x2905564006504c80d1203445820809510b01841235085031c01901554101220e024418109041c02125045601103044828051008c40c054015403408102060044840510024041080c0140010108004000),(64,0x348596508302945330b10e062490133545c84086035c1520b4195a00595136102225c44c0e11a0920655410d0523071088e42541c74046605081d02558111260c2125843c0a10a052450033144c80031),(64,0x4c4b838869690930695537106234727213408ce51b2202581d7455811d82424756c026584e844899750c312985430f11e0a20a56414d15270c6136010c9883d02c780566451801d42326040d570484a8),(64,0x4589d760c713a020cd893d47c8c0a60b5e15a0576491950cca81436631713e1222a5e434c5a6551c02d46334b2820395d063494ac3585d8459821c0e709492d43c7c0666852805d523661440c8a7154c),(64,0x2da0c0f5f15e0676892954cda8559c22dc6535322e5f438c6a6952c06d563761841c8e1cdc94d4bc3986d885a825c1e7495960d0a1d9cc6c53809d623a62444c9a7555c12d86434f21e5b428c2a594ec),(64,0x58cea895ac26dd657587438f31e9b54f02b598ed8a117279d913e03628f61f5b829c2e7896964d1a770cb81837635723e63448caa7956c16d9647547338b38243a5d4fc498ad7a0d717a126640f70d4a),(64,0x639733ea356f0ab7996d65d1e33e0a0ed763f63849cae7a45f84d9a52cb78343e7c97968d2a7b0db8599d71d4e4ccba7d57c1ada64b55737a1923dca4d8bd7e0e71ba226a41f74d5a8710b1ddcd6c939),(64,0x5b91f82d773fa392bdea66e0e0fdf35ea3c7b6176794f2edf65f5a74b8df869cb4dcbe7e46f88daa56e1d739b34e9fc3ae266b5d75790f1edb64f5673ba2927dda62cf71fa326e42f78d6a8b11b77607),(57,0x1ff8bdbf8ee3e7bd7f7ee1f7f9af4fe2b6ee2e77e376f96f3fe3a7ae0f5ee3d7b99f7dd7e4be1b2fdfa6ae1e73d3b7f6276b95f6dd3e3be2a76c7f8cdba5ae2d7798f3ee366f5e7)]),
  ([8,4,2,3], [(64,0x780252504d5d0064b4bc0a1081407a0253027055038c40c07d69058045383c480330850503e3d0600648810568070fc2d44424049008b80904c0152c30079020540347c3c0840f41810048004780303c),(64,0xa55042498145783907b029312742c1590c03cc57b0311f9a54d0a01658004939320343c8816a1143345c218154f0a80fcf51841a340896c0425a4f81901d510fd230b61156c360910804a4006c00cb9),(64,0xd55c3cc826a515290ce1758421c164f4a90e0f6189ac4601b345f8229b1500ac10d6a3e4656301e514d43f88d6d1202dc465b4d91a0920854812d011b4ba784265c0dc255bc139754107001d2e2f5e4),(64,0x11d6e3686964093089494086e6e124788275c4dd810966f54c13d76414716612f2f9e50a9513810a265c030c525e4e51d00b4c89e7a02d55057434c67b4325f0e81fda64d4a17205a6051004d3a325f0),(64,0xb955439c431dee0cd7d3a61069d36289c95605b609114ecca7c436574ec20daa458a5730cf1798505d3e2a9f40e5603dc636b519349f96208b6c9412b5d45acfa1998d4701f518d57f0ff239b5484b0),(64,0x6b91a740d37e9896cd422b9d5590fb19d8e47547359fd23db6488b17616f36c6a6442352a0040c6f6e52578d7237a05650976f94d5dd061c9994a0bf7982b548e18210b269c114d7a398756713327de9),(64,0x6dd232c9d91ad9252e016e9267717337e06655bf539071cd9a4a5e754ce28249b7097b39c76675ea0bd568310f715ef5f8ea845a04dca37295960d1232df20dd5e3b6146aca67345f6193f2adf50e961),(64,0x3be1673df758e197498b75d6647dff2cdda64e026ed27776076594f66d2a38e0a70c77679eb55e0d7197f3ae12685cb569137cd5f3ba1529dce61df60ed62861af46dd17ed8a50caf7596563d1e35dfe),(19,0x1df83da385e1a74d6776e03779974ae0b67e0e71e136895b)]),
  ([10,3,4,2], [(64,0x115e00b89913d770152d2e830438c41447a01d2f2945b044c6025a4174134ecf11f8d2220150f8f31a41f228405a0213fcb510896130022dc2d138044b0790185a0407b048f021c3d0783f2d00100c78),(64,0x78c315650f270c51497a021302f658298331711131c547bc7d029a54c8a8179860513c3247f031a7474d3180890593e3d0818706a080d522c186cc415a4f61b02252900234b610d6b384970904d408b8),(64,0x35a84d51e2acd41858905d3f332673d4828746b6a920358637f88c065b45056a3dc8487c6d6542352cd84048e06db61116c3e4e21bc980954d40c908acb9119e10bd6e3909a09dc2141784152e2ec48),(64,0x36e76410918b1b911de25bcfc394728349b0a1c354179418938b8bc125e40c971568e74409d0a9c514d7b421312fa5929de60d15c4489f8e8c8155f05f5a64ccc096ca90d9d117d874513d328577c880),(64,0x7495f6211528a3d32c587cd80039a94d91f978ac0e5d41898a45d40336687d483879ab4e1212ba4935c647fd8c069b5508cf9a8f8216201b9ad65923530d919a0123c1c6dd445b4fa38e221c1980994e),(64,0x1c5b06652653cdc9de0424a2d6e9475c0fd39a251ce0e66c297115137a7941c948bdbc129e55c95b3a0758409e0adc654d7c426312fe5a79c355d15d3aa8544ca08edc8159f15f90b4d0c1970aa7a437),(64,0x5597f4323430a5d7a83874d603b688458a38f9cb165f46053797cad7b03a7556262d18900ce9a5f660dac4e522984af929d719600469433426b7e086885ae65d242c64c368678098f075b85166d3ee23),(64,0x46e433466c7e5af496642ca4d7686880d9051a6e7ee246c59a49e4f37678815926ed489c0fe8987483d9c4a55237e7a81c958c1bd5cce98a0768459e0b1c75527c42a326fde85d55e3ae8684ca18f1c9),(64,0x7f1b24a2507760664d499c6276752a948e09ee086fa738a4778499f5567d82a33701763b287851a1729579fd0d8d5eb584eea26162923f731828de607b43b75963a2e41739f76113a988b092dd85958e),(64,0x95a0c68e81862838e68d869d059e8f916667729191dfd945de652724ae53826748a9a09567e82dc1855a2562808d8efa2a17736828e1ee5928c8664273d8598dd959a8e472447ea652ce4e76d9191a6f),(9,0x257a121ba4292921df95275)])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p7_13_19_checked : PLift (checkBox [3,7,13,19] [10,4,5,4] (2,1) p7_13_19_rows = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def p7_13_key_check : PLift ((∀ s : Fin 20, s.val.Prime → 13 < s.val → s.val ∈ p7_13_keys)) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem p7_13_box (i : Fin 2) :
    ∃ (caps : List ℕ) (rows : List Witness),
      caps.length = 4 ∧ (∀ c ∈ caps, 0 < c) ∧
      checkBox [3,7,13,p7_13_keys[i.val]!] caps (2,1) rows = true := by
  fin_cases i
  · exact ⟨[7,3,3,3], p7_13_17_rows, rfl, by decide, p7_13_17_checked.down⟩
  · exact ⟨[10,4,5,4], p7_13_19_rows, rfl, by decide, p7_13_19_checked.down⟩

private theorem p7_13_bounded (s a b c d : ℕ)
    (sp : s.Prime) (ordered : 13 < s) (sb : s < 20)
    (ap : 0 < a) (bp : 0 < b) (cp : 0 < c) (dp : 0 < d)
    (high : 2 < indexProduct [3,7,13,s] [a,b,c,d]) :
    ∃ k, k ∣ factorProduct [3,7,13,s] [a,b,c,d] ∧ k.Pseudoperfect := by
  have membership := p7_13_key_check.down ⟨s,sb⟩ sp ordered
  obtain ⟨i, hi, key⟩ := List.mem_iff_getElem.mp membership
  have word := p7_13_box ⟨i,hi⟩
  have ke : p7_13_keys[i]! = s := (getElem!_pos p7_13_keys i hi).trans key
  simp only [ke] at word
  obtain ⟨caps, rows, width, cp', checked⟩ := word
  have ps : ∀ p ∈ [3,7,13,s], 2 ≤ p := by simp [sp.two_le]
  have es : ∀ e ∈ [a,b,c,d], 0 < e := by simp [ap,bp,cp,dp]
  rcases checkBox_sound [3,7,13,s] caps [a,b,c,d] (2,1) rows checked ps es cp'
      rfl width.symm (by decide) with tooSmall | witness
  · exact False.elim ((not_le_of_gt high) (by simpa using tooSmall))
  · exact witness

private theorem p7_13 (s a b c d : ℕ)
    (sp : s.Prime) (ordered : 13 < s)
    (ap : 0 < a) (bp : 0 < b) (cp : 0 < c) (dp : 0 < d)
    (high : 2 < indexProduct [3,7,13,s] [a,b,c,d]) :
    ∃ k, k ∣ factorProduct [3,7,13,s] [a,b,c,d] ∧ k.Pseudoperfect := by
  have rel : List.Forall₂ (fun lo p => 2 ≤ lo ∧ lo ≤ p) [3,7,13] [3,7,13] := by decide
  have prefixBound : indexProduct [3,7,13] [a,b,c] ≤ (91 / 48 : ℚ) :=
    (majorant rel [a,b,c] rfl).trans (by norm_num [ceiling])
  have sb := last_prime_bound 7 13 s a b c d 20 (91 / 48 : ℚ)
    (by decide) (by norm_num) (by norm_num [ceiling]) prefixBound high
  exact p7_13_bounded s a b c d sp ordered sb ap bp cp dp high

private theorem choose_three (q r a b c : ℕ)
    (qlo : 5 ≤ q) (qr : q + 2 ≤ r) (qodd : Odd q) (rp : r.Prime)
    (ap : 0 < a) (bp : 0 < b) (cp : 0 < c)
    (high : 2 < indexProduct [3,q,r] [a,b,c]) :
    ∃ k, k ∣ factorProduct [3,q,r] [a,b,c] ∧ k.Pseudoperfect := by
  obtain ⟨rfl, rset⟩ := three_support q r a b c qlo qr qodd rp high
  simp at rset
  rcases rset with rfl | rfl | rfl
  · rcases prefix7 a b c ap bp cp with lo | witness
    · exact False.elim ((not_le_of_gt high) (lo.trans (by norm_num)))
    · exact witness
  · rcases prefix11 a b c ap bp cp with lo | witness
    · exact False.elim ((not_le_of_gt high) (lo.trans (by norm_num)))
    · exact witness
  · rcases prefix13 a b c ap bp cp with lo | witness
    · exact False.elim ((not_le_of_gt high) (lo.trans (by norm_num)))
    · exact witness

private theorem choose_four (q r s a b c d : ℕ)
    (qlo : 5 ≤ q) (qr : q + 2 ≤ r) (rs : r + 2 ≤ s)
    (qp : q.Prime) (rp : r.Prime) (sp : s.Prime)
    (ap : 0 < a) (bp : 0 < b) (cp : 0 < c) (dp : 0 < d)
    (high : 2 < indexProduct [3,q,r,s] [a,b,c,d]) :
    ∃ k, k ∣ factorProduct [3,q,r,s] [a,b,c,d] ∧ k.Pseudoperfect := by
  rcases four_pairs q r s a b c d qlo qr rs qp rp high with ⟨rfl, rset⟩ | ⟨rfl, rset⟩
  · simp at rset
    rcases rset with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact p5_7 s a b c d sp (by omega) ap bp cp dp high
    · exact p5_11 s a b c d sp (by omega) ap bp cp dp high
    · exact p5_13 s a b c d sp (by omega) ap bp cp dp high
    · exact p5_17 s a b c d sp (by omega) ap bp cp dp high
    · exact p5_19 s a b c d sp (by omega) ap bp cp dp high
    · exact p5_23 s a b c d sp (by omega) ap bp cp dp high
    · exact p5_29 s a b c d sp (by omega) ap bp cp dp high
  · simp at rset
    rcases rset with rfl | rfl
    · exact p7_11 s a b c d sp (by omega) ap bp cp dp high
    · exact p7_13 s a b c d sp (by omega) ap bp cp dp high

private theorem from_support (n : ℕ) (tail : List ℕ) (size : tail.length < 4)
    (ordered : (3 :: tail).Pairwise (· < ·))
    (primeData : ∀ p ∈ 3 :: tail, p.Prime ∧ Odd p ∧ 0 < n.factorization p)
    (high : 2 < indexProduct (3 :: tail) ((3 :: tail).map n.factorization)) :
    ∃ k, k ∣ factorProduct (3 :: tail) ((3 :: tail).map n.factorization) ∧ k.Pseudoperfect := by
  have first := (primeData 3 (by simp)).2.2
  cases tail with
  | nil => exact False.elim ((not_le_of_gt high) (one_impossible _))
  | cons q rest =>
    have qData := primeData q (by simp)
    have qLt : 3 < q := (List.pairwise_cons.mp ordered).1 q (by simp)
    have qlo : 5 ≤ q := at_least_two_more (by decide) qData.2.1 qLt
    cases rest with
    | nil => exact False.elim ((not_le_of_gt high) (two_impossible q _ _ qlo))
    | cons r rest =>
      have rData := primeData r (by simp)
      have tailOrdered := (List.pairwise_cons.mp ordered).2
      have rLt : q < r := (List.pairwise_cons.mp tailOrdered).1 r (by simp)
      have rlo : q + 2 ≤ r := at_least_two_more qData.2.1 rData.2.1 rLt
      cases rest with
      | nil =>
        exact choose_three q r _ _ _ qlo rlo qData.2.1 rData.1 first
          qData.2.2 rData.2.2 high
      | cons s rest =>
        have none : rest = [] := by
          have z : rest.length = 0 := by simp at size; omega
          exact List.eq_nil_of_length_eq_zero z
        subst rest
        have sData := primeData s (by simp)
        have lastOrdered := (List.pairwise_cons.mp tailOrdered).2
        have sLt : r < s := (List.pairwise_cons.mp lastOrdered).1 s (by simp)
        have slo : r + 2 ≤ s := at_least_two_more rData.2.1 sData.2.1 sLt
        exact choose_four q r s _ _ _ _ qlo rlo slo qData.1 rData.1 sData.1
          first qData.2.2 rData.2.2 sData.2.2 high

theorem certifiedLow {n : ℕ} (odd : Odd n) (abundant : n.Abundant)
    (three : 3 ∣ n) (count : n.primeFactors.card ≤ 4) :
    ∃ k, k ∣ n ∧ k.Pseudoperfect := by
  have nonzero : n ≠ 0 := abundant.pos.ne'
  obtain ⟨tail, order, sorted, primes⟩ := sorted_support nonzero odd three
  have len : tail.length < 4 := by
    have hsize : (n.primeFactors.sort).length ≤ 4 := by simpa using count
    simpa [order] using hsize
  have hFactor : n = factorProduct (3 :: tail) ((3 :: tail).map n.factorization) := by
    rw [factorProduct_map, ← order]
    exact sorted_factorization nonzero
  have high : 2 < indexProduct (3 :: tail) ((3 :: tail).map n.factorization) := by
    rw [indexProduct_map, ← order, ← sorted_index nonzero]
    exact Nat.abundant_iff_two_lt_abundancyIndex.mp abundant
  simpa only [← hFactor] using from_support n tail len sorted primes high

end OddWeirdCover

theorem OMA.solution : OMA.R_Erdos470_erdos_470_variants_odd_weird_10_pow_21_R1_H1_R1_H2_R1.H1 := by
  intro b q j hp
  dsimp only
  intro size odd abundant primitive three small
  obtain ⟨d,dvd,witness⟩ := OddWeirdCover.certifiedLow odd abundant three small
  exact OMA.R_Erdos470_erdos_470_variants_odd_weird_10_pow_21_R1.pp_of_dvd
    dvd abundant.pos witness