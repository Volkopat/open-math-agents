import OMAReductions.R_oeis_a003075_R1

namespace OMA.A003075

open OMA.S_oeis_a003075

/-- Apply the standard zero-one principle to the registered comparator and fold. -/
def threshold (t a : ℕ) : ℕ := if t < a then 1 else 0

lemma threshold_monotone (t : ℕ) : Monotone (threshold t) := by
  intro a b hab
  by_cases ha : t < a
  · simp [threshold, ha, ha.trans_le hab]
  · simp [threshold, ha]

lemma run_threshold {n : ℕ} (L : List (Fin n × Fin n)) (t : ℕ) (v : Fin n → ℕ) :
    run L (threshold t ∘ v) = threshold t ∘ run L v := by
  induction L generalizing v with
  | nil => rfl
  | cons c L ih =>
    have commute : comparator c (threshold t ∘ v) = threshold t ∘ comparator c v := by
      funext k
      simp only [comparator, Function.comp_apply]
      split_ifs
      · exact ((threshold_monotone t).map_min).symm
      · exact ((threshold_monotone t).map_max).symm
      · rfl
    change run L (comparator c (threshold t ∘ v)) = threshold t ∘ run L (comparator c v)
    rw [commute, ih]

lemma sorting_of_zero_one {n : ℕ} (L : List (Fin n × Fin n))
    (hordered : ∀ c ∈ L, c.1 < c.2)
    (hbool : ∀ v : Fin n → Bool, Monotone (run L (fun i => (v i).toNat))) :
    IsSortingNetwork L := by
  refine ⟨hordered, fun v i j hij => ?_⟩
  by_contra! h
  let t := run L v j
  have hb := hbool (fun k => decide (t < v k)) hij
  have he : (fun k => (decide (t < v k)).toNat) = threshold t ∘ v := by
    funext k
    by_cases hk : t < v k <;> simp [threshold, hk]
  rw [he, run_threshold] at hb
  change threshold t (run L v i) ≤ threshold t t at hb
  have ht : t < run L v i := h
  simp [threshold, ht] at hb

lemma minSize_le_of_network {n : ℕ} (L : List (Fin n × Fin n)) (h : IsSortingNetwork L) :
    minSize n ≤ L.length :=
  Nat.sInf_le ⟨L, h, rfl⟩

/-- Bit k in wire i's mask is bit i of input index k. The top half repeats the lower
half for earlier wires and consists entirely of ones for the new wire. -/
def inputMask : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, i =>
      if i = n then (2 ^ (2 ^ n) - 1) <<< (2 ^ n)
      else let m := inputMask n i; m ||| (m <<< (2 ^ n))

lemma inputMask_spec (n i k : ℕ) (hi : i < n) :
    (inputMask n i).testBit k = (decide (k < 2 ^ n) && k.testBit i) := by
  induction n generalizing k with
  | zero => omega
  | succ n ih =>
    have pow : (2 : ℕ) ^ (n + 1) = 2 ^ n + 2 ^ n := by rw [Nat.pow_succ]; omega
    have pos : 0 < (2 : ℕ) ^ n := Nat.two_pow_pos n
    rw [pow]
    by_cases hlow : k < 2 ^ n
    · have hb : k < 2 ^ n + 2 ^ n := by omega
      by_cases he : i = n
      · subst i
        simp [inputMask, Nat.not_le_of_lt hlow, Nat.testBit_lt_two_pow hlow]
      · have hin : i < n := by omega
        simp [inputMask, he, hlow, hb, Nat.not_le_of_lt hlow, ih k hin]
    · have hge : 2 ^ n ≤ k := by omega
      have hk : 2 ^ n + (k - 2 ^ n) = k := by omega
      have hsub : k - 2 ^ n < 2 ^ n ↔ k < 2 ^ n + 2 ^ n := by omega
      by_cases he : i = n
      · subst i
        rw [inputMask]
        by_cases hb : k < 2 ^ n + 2 ^ n
        · have hs : k - 2 ^ n < 2 ^ n := hsub.mpr hb
          have ht : k.testBit n = true := by
            rw [← hk, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hs, Bool.not_false]
          simp [hb, ht, hge, hs]
        · have hs : ¬ k - 2 ^ n < 2 ^ n := fun h => hb (hsub.mp h)
          simp [hb, hge, hs]
      · have hin : i < n := by omega
        have ht : (k - 2 ^ n).testBit i = k.testBit i := by
          nth_rewrite 2 [← hk]
          exact (Nat.testBit_two_pow_add_gt hin _).symm
        simp [inputMask, he, hlow, hge, ih _ hin, hsub, ht]

/-- Every Boolean vector is represented by an input index below two to the wire count. -/
lemma input_index {n : ℕ} (v : Fin n → Bool) :
    ∃ k : ℕ, k < 2 ^ n ∧ ∀ i : Fin n, k.testBit i.val = v i := by
  let bits := List.ofFn v
  let word := BitVec.ofBoolListLE bits
  refine ⟨word.toNat, ?_, ?_⟩
  · simpa [bits] using word.isLt
  · intro i
    change word.getLsbD i.val = v i
    rw [BitVec.getLsbD_ofBoolListLE]
    have hi : i.val < bits.length := by simp [bits]
    rw [List.getD_eq_getElem _ _ hi]
    simp [bits]

def readBit {n : ℕ} (mask : Vector ℕ n) (k : ℕ) (i : Fin n) : ℕ :=
  (mask[i.val].testBit k).toNat

def comparatorPacked {n : ℕ} (w : Vector ℕ n) (c : Fin n × Fin n) : Vector ℕ n :=
  let lo := w[c.1.val] &&& w[c.2.val]
  let hi := w[c.1.val] ||| w[c.2.val]
  (w.set c.2.val hi).set c.1.val lo

lemma and_toNat (a b : Bool) : (a && b).toNat = min a.toNat b.toNat := by
  cases a <;> cases b <;> decide

lemma or_toNat (a b : Bool) : (a || b).toNat = max a.toNat b.toNat := by
  cases a <;> cases b <;> decide

lemma readBit_comparator {n : ℕ} (w : Vector ℕ n) (c : Fin n × Fin n) (k : ℕ) :
    readBit (comparatorPacked w c) k = comparator c (readBit w k) := by
  funext i
  simp only [readBit, comparatorPacked, Vector.getElem_set, comparator]
  by_cases h1 : i = c.1
  · subst i
    simp [Nat.testBit_and, and_toNat]
  · have h1' : c.1.val ≠ i.val := fun h => h1 (Fin.ext h.symm)
    by_cases h2 : i = c.2
    · subst i
      simp [h1, h1', Nat.testBit_or, or_toNat]
    · have h2' : c.2.val ≠ i.val := fun h => h2 (Fin.ext h.symm)
      simp [h1, h1', h2, h2']

lemma readBit_fold {n : ℕ} (L : List (Fin n × Fin n)) (w : Vector ℕ n) (k : ℕ) :
    readBit (L.foldl comparatorPacked w) k = run L (readBit w k) := by
  induction L generalizing w with
  | nil => rfl
  | cons c L ih =>
    change readBit (L.foldl comparatorPacked (comparatorPacked w c)) k =
      run L (comparator c (readBit w k))
    rw [ih, readBit_comparator]

def runPacked {n : ℕ} (L : List (Fin n × Fin n)) : Vector ℕ n :=
  L.foldl comparatorPacked (Vector.ofFn fun i => inputMask n i.val)

lemma runPacked_spec {n : ℕ} (L : List (Fin n × Fin n)) (v : Fin n → Bool) :
    ∃ k : ℕ, readBit (runPacked L) k = run L (fun i => (v i).toNat) := by
  obtain ⟨k, hk, hv⟩ := input_index v
  refine ⟨k, ?_⟩
  rw [runPacked, readBit_fold]
  congr 1
  funext i
  simp [readBit, inputMask_spec n i.val k i.isLt, hk, hv i]

lemma sorting_of_packed {n : ℕ} (L : List (Fin (n + 1) × Fin (n + 1)))
    (ordered : ∀ c ∈ L, c.1 < c.2)
    (adjacent : ∀ i : Fin n,
      (runPacked L)[i.val] &&& (runPacked L)[i.val + 1] = (runPacked L)[i.val]) :
    IsSortingNetwork L := by
  apply sorting_of_zero_one L ordered
  intro v
  obtain ⟨k, hv⟩ := runPacked_spec L v
  rw [← hv, Fin.monotone_iff_le_succ]
  intro i
  have he := congrArg (fun m : ℕ => m.testBit k) (adjacent i)
  rw [Nat.testBit_and] at he
  change ((runPacked L)[i.val].testBit k).toNat ≤ ((runPacked L)[i.val + 1].testBit k).toNat
  cases ha : (runPacked L)[i.val].testBit k <;>
    cases hb : (runPacked L)[i.val + 1].testBit k <;> simp [ha, hb] at he ⊢

-- Comparator layers published by Bert Dobbelaere.
-- https://bertdobbelaere.github.io/sorting_networks.html#N13L45D10
def network13 : List (Fin 13 × Fin 13) := [
  (0, 12), (1, 10), (2, 9), (3, 7), (5, 11), (6, 8),
  (1, 6), (2, 3), (4, 11), (7, 9), (8, 10),
  (0, 4), (1, 2), (3, 6), (7, 8), (9, 10), (11, 12),
  (4, 6), (5, 9), (8, 11), (10, 12),
  (0, 5), (3, 8), (4, 7), (6, 11), (9, 10),
  (0, 1), (2, 5), (6, 9), (7, 8), (10, 11),
  (1, 3), (2, 4), (5, 6), (9, 10),
  (1, 2), (3, 4), (5, 7), (6, 8),
  (2, 3), (4, 5), (6, 7), (8, 9),
  (3, 4), (5, 6)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
lemma network13_sorted : IsSortingNetwork network13 := by
  apply sorting_of_packed
  · decide +kernel
  · decide +kernel

lemma upper13 : minSize 13 ≤ 45 := minSize_le_of_network _ network13_sorted

-- Comparator layers published by Bert Dobbelaere.
-- https://bertdobbelaere.github.io/sorting_networks.html#N14L51D10
def network14 : List (Fin 14 × Fin 14) := [
  (0, 1), (2, 3), (4, 5), (6, 7), (8, 9), (10, 11), (12, 13),
  (0, 2), (1, 3), (4, 8), (5, 9), (10, 12), (11, 13),
  (0, 4), (1, 2), (3, 7), (5, 8), (6, 10), (9, 13), (11, 12),
  (0, 6), (1, 5), (3, 9), (4, 10), (7, 13), (8, 12),
  (2, 10), (3, 11), (4, 6), (7, 9),
  (1, 3), (2, 8), (5, 11), (6, 7), (10, 12),
  (1, 4), (2, 6), (3, 5), (7, 11), (8, 10), (9, 12),
  (2, 4), (3, 6), (5, 8), (7, 10), (9, 11),
  (3, 4), (5, 6), (7, 8), (9, 10),
  (6, 7)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
lemma network14_sorted : IsSortingNetwork network14 := by
  apply sorting_of_packed
  · decide +kernel
  · decide +kernel

lemma upper14 : minSize 14 ≤ 51 := minSize_le_of_network _ network14_sorted

-- Comparator layers published by Bert Dobbelaere.
-- https://bertdobbelaere.github.io/sorting_networks.html#N15L56D10
def network15 : List (Fin 15 × Fin 15) := [
  (1, 2), (3, 10), (4, 14), (5, 8), (6, 13), (7, 12), (9, 11),
  (0, 14), (1, 5), (2, 8), (3, 7), (6, 9), (10, 12), (11, 13),
  (0, 7), (1, 6), (2, 9), (4, 10), (5, 11), (8, 13), (12, 14),
  (0, 6), (2, 4), (3, 5), (7, 11), (8, 10), (9, 12), (13, 14),
  (0, 3), (1, 2), (4, 7), (5, 9), (6, 8), (10, 11), (12, 13),
  (0, 1), (2, 3), (4, 6), (7, 9), (10, 12), (11, 13),
  (1, 2), (3, 5), (8, 10), (11, 12),
  (3, 4), (5, 6), (7, 8), (9, 10),
  (2, 3), (4, 5), (6, 7), (8, 9), (10, 11),
  (5, 6), (7, 8)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
lemma network15_sorted : IsSortingNetwork network15 := by
  apply sorting_of_packed
  · decide +kernel
  · decide +kernel

lemma upper15 : minSize 15 ≤ 56 := minSize_le_of_network _ network15_sorted

-- Comparator layers published by Bert Dobbelaere.
-- https://bertdobbelaere.github.io/sorting_networks.html#N16L60D10
def network16 : List (Fin 16 × Fin 16) := [
  (0, 13), (1, 12), (2, 15), (3, 14), (4, 8), (5, 6), (7, 11), (9, 10),
  (0, 5), (1, 7), (2, 9), (3, 4), (6, 13), (8, 14), (10, 15), (11, 12),
  (0, 1), (2, 3), (4, 5), (6, 8), (7, 9), (10, 11), (12, 13), (14, 15),
  (0, 2), (1, 3), (4, 10), (5, 11), (6, 7), (8, 9), (12, 14), (13, 15),
  (1, 2), (3, 12), (4, 6), (5, 7), (8, 10), (9, 11), (13, 14),
  (1, 4), (2, 6), (5, 8), (7, 10), (9, 13), (11, 14),
  (2, 4), (3, 6), (9, 12), (11, 13),
  (3, 5), (6, 8), (7, 9), (10, 12),
  (3, 4), (5, 6), (7, 8), (9, 10), (11, 12),
  (6, 7), (8, 9)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
lemma network16_sorted : IsSortingNetwork network16 := by
  apply sorting_of_packed
  · decide +kernel
  · decide +kernel

lemma upper16 : minSize 16 ≤ 60 := minSize_le_of_network _ network16_sorted

end OMA.A003075

theorem OMA.solution : OMA.R_oeis_a003075_R1.H1 := by
  exact ⟨OMA.A003075.upper13, OMA.A003075.upper14, OMA.A003075.upper15, OMA.A003075.upper16⟩
