import OMAStatements.S_oeis_a226076

namespace OMA.S_oeis_a226076

open PowerSeries





/-! ## The set S and its increasing enumeration g -/

/-- Membership in S = {4^k, 9*4^k, 289*4^k}. -/
def InS (x : ℕ) : Prop := ∃ k, x = 4 ^ k ∨ x = 9 * 4 ^ k ∨ x = 289 * 4 ^ k

def c3 (r : ℕ) : ℕ := if r = 0 then 144 else if r = 1 then 256 else 289

/-- The increasing enumeration of S, from index 0. -/
def g (k : ℕ) : ℕ :=
  if k = 0 then 1 else if k = 1 then 4 else if k = 2 then 9 else if k = 3 then 16
  else if k = 4 then 36 else if k = 5 then 64 else 4 ^ ((k - 6) / 3) * c3 ((k - 6) % 3)

lemma g_big (k : ℕ) (hk : 6 ≤ k) : g k = 4 ^ ((k - 6) / 3) * c3 ((k - 6) % 3) := by
  unfold g
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega)]

lemma g_shift (k : ℕ) (hk : 6 ≤ k) : g (k + 3) = 4 * g k := by
  rw [g_big k hk, g_big (k + 3) (by omega), show (k + 3 - 6) / 3 = (k - 6) / 3 + 1 by omega,
    show (k + 3 - 6) % 3 = (k - 6) % 3 by omega, pow_succ]
  ring

lemma g_lt_succ (k : ℕ) : g k < g (k + 1) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.lt_or_ge k 9 with hk | hk
    · interval_cases k <;> decide
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
      rw [g_shift j (by omega), show j + 3 + 1 = (j + 1) + 3 by omega, g_shift (j + 1) (by omega)]
      have := ih j (by omega)
      omega

lemma g_strictMono : StrictMono g := strictMono_nat_of_lt_succ g_lt_succ

lemma g_pos (k : ℕ) : 0 < g k := by
  have : g 0 ≤ g k := g_strictMono.monotone (Nat.zero_le k)
  have h0 : g 0 = 1 := rfl
  omega

lemma g_inS (k : ℕ) : InS (g k) := by
  rcases Nat.lt_or_ge k 6 with hk | hk
  · interval_cases k
    · exact ⟨0, Or.inl rfl⟩
    · exact ⟨1, Or.inl rfl⟩
    · exact ⟨0, Or.inr (Or.inl rfl)⟩
    · exact ⟨2, Or.inl rfl⟩
    · exact ⟨1, Or.inr (Or.inl rfl)⟩
    · exact ⟨3, Or.inl rfl⟩
  · rw [g_big k hk]
    have hr : (k - 6) % 3 < 3 := Nat.mod_lt _ (by norm_num)
    set q := (k - 6) / 3
    interval_cases h : (k - 6) % 3
    · refine ⟨q + 2, Or.inr (Or.inl ?_)⟩
      simp only [c3, if_true, pow_add]
      ring
    · refine ⟨q + 4, Or.inl ?_⟩
      simp only [c3, show (1 : ℕ) ≠ 0 by norm_num, if_false, if_true, pow_add]
      ring
    · refine ⟨q, Or.inr (Or.inr ?_)⟩
      simp only [c3, show (2 : ℕ) ≠ 0 by norm_num, show (2 : ℕ) ≠ 1 by norm_num, if_false]
      ring

lemma inS_eq_g (x : ℕ) (hx : InS x) : ∃ k, g k = x := by
  obtain ⟨j, hj | hj | hj⟩ := hx
  · rcases Nat.lt_or_ge j 4 with h | h
    · interval_cases j
      · exact ⟨0, by rw [hj]; rfl⟩
      · exact ⟨1, by rw [hj]; rfl⟩
      · exact ⟨3, by rw [hj]; rfl⟩
      · exact ⟨5, by rw [hj]; rfl⟩
    · refine ⟨7 + 3 * (j - 4), ?_⟩
      rw [g_big _ (by omega), show (7 + 3 * (j - 4) - 6) / 3 = j - 4 by omega,
        show (7 + 3 * (j - 4) - 6) % 3 = 1 by omega, hj]
      simp only [c3, show (1 : ℕ) ≠ 0 by norm_num, if_false, if_true]
      rw [show j = (j - 4) + 4 by omega, pow_add]
      norm_num
  · rcases Nat.lt_or_ge j 2 with h | h
    · interval_cases j
      · exact ⟨2, by rw [hj]; rfl⟩
      · exact ⟨4, by rw [hj]; rfl⟩
    · obtain ⟨i, rfl⟩ : ∃ i, j = i + 2 := ⟨j - 2, by omega⟩
      refine ⟨6 + 3 * i, ?_⟩
      rw [g_big _ (by omega), show (6 + 3 * i - 6) / 3 = i by omega,
        show (6 + 3 * i - 6) % 3 = 0 by omega, hj]
      simp only [c3, if_true, pow_add]
      ring
  · refine ⟨8 + 3 * j, ?_⟩
    rw [g_big _ (by omega), show (8 + 3 * j - 6) / 3 = j by omega,
      show (8 + 3 * j - 6) % 3 = 2 by omega, hj]
    simp only [c3, show (2 : ℕ) ≠ 0 by norm_num, show (2 : ℕ) ≠ 1 by norm_num, if_false]
    ring

lemma g_isSquare (k : ℕ) : IsSquare (g k) := by
  obtain ⟨j, hj | hj | hj⟩ := g_inS k
  · exact ⟨2 ^ j, by rw [hj, ← mul_pow]; norm_num⟩
  · exact ⟨3 * 2 ^ j, by rw [hj]; ring_nf; rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]; ring⟩
  · exact ⟨17 * 2 ^ j, by rw [hj]; ring_nf; rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]; ring⟩

/-! ## Sums of distinct elements of S -/

/-- The subset sums of {1, 9, 289}. -/
def Dset : Finset ℕ := {0, 1, 9, 10, 289, 290, 298, 299}

lemma inS_pos (t : ℕ) (ht : InS t) : 0 < t := by
  obtain ⟨k, hk | hk | hk⟩ := ht <;> rw [hk] <;> positivity

lemma inS_odd (t : ℕ) (ht : InS t) (h4 : ¬ 4 ∣ t) : t = 1 ∨ t = 9 ∨ t = 289 := by
  obtain ⟨k, hk | hk | hk⟩ := ht
  · cases k with
    | zero => left; simpa using hk
    | succ k => exact absurd ⟨4 ^ k, by rw [hk, pow_succ]; ring⟩ h4
  · cases k with
    | zero => right; left; simpa using hk
    | succ k => exact absurd ⟨9 * 4 ^ k, by rw [hk, pow_succ]; ring⟩ h4
  · cases k with
    | zero => right; right; simpa using hk
    | succ k => exact absurd ⟨289 * 4 ^ k, by rw [hk, pow_succ]; ring⟩ h4

lemma inS_div4 (t : ℕ) (ht : InS t) (h4 : 4 ∣ t) : InS (t / 4) := by
  obtain ⟨k, hk | hk | hk⟩ := ht
  · cases k with
    | zero => simp at hk; omega
    | succ k => exact ⟨k, Or.inl (by rw [hk, pow_succ]; simp)⟩
  · cases k with
    | zero => simp at hk; omega
    | succ k => exact ⟨k, Or.inr (Or.inl (by rw [hk, pow_succ, ← mul_assoc]; simp))⟩
  · cases k with
    | zero => simp at hk; omega
    | succ k => exact ⟨k, Or.inr (Or.inr (by rw [hk, pow_succ, ← mul_assoc]; simp))⟩

lemma inS_mul4 (t : ℕ) (ht : InS t) : InS (4 * t) := by
  obtain ⟨k, hk | hk | hk⟩ := ht
  · exact ⟨k + 1, Or.inl (by rw [hk, pow_succ]; ring)⟩
  · exact ⟨k + 1, Or.inr (Or.inl (by rw [hk, pow_succ]; ring))⟩
  · exact ⟨k + 1, Or.inr (Or.inr (by rw [hk, pow_succ]; ring))⟩

lemma dset_sums : ∀ U ∈ ({1, 9, 289} : Finset ℕ).powerset, U.sum id ∈ Dset := by decide

/-- A finite sum of distinct elements of S is d + 4 * (a finite sum of distinct elements of S),
with d a subset sum of {1, 9, 289}; the new elements are a quarter of old ones. -/
lemma split_sum (T : Finset ℕ) (hT : ∀ t ∈ T, InS t) :
    ∃ d ∈ Dset, ∃ T' : Finset ℕ, (∀ t' ∈ T', InS t' ∧ 4 * t' ∈ T) ∧
      T.sum id = d + 4 * T'.sum id := by
  refine ⟨(T.filter (fun t => ¬ 4 ∣ t)).sum id, ?_, (T.filter (fun t => 4 ∣ t)).image (· / 4),
    ?_, ?_⟩
  · apply dset_sums
    rw [Finset.mem_powerset]
    intro t ht
    rw [Finset.mem_filter] at ht
    rcases inS_odd t (hT t ht.1) ht.2 with h | h | h <;> simp [h]
  · intro t' ht'
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp ht'
    rw [Finset.mem_filter] at ht
    exact ⟨inS_div4 t (hT t ht.1) ht.2, by rw [Nat.mul_div_cancel' ht.2]; exact ht.1⟩
  · rw [← Finset.sum_filter_add_sum_filter_not T (fun t => 4 ∣ t), add_comm]
    congr 1
    rw [Finset.sum_image]
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun t ht => ?_
      rw [Finset.mem_filter] at ht
      simp [Nat.mul_div_cancel' ht.2]
    · intro t ht u hu htu
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at ht hu
      have h1 := Nat.mul_div_cancel' ht.2
      have h2 := Nat.mul_div_cancel' hu.2
      simp only at htu
      rw [← h1, ← h2, htu]

lemma small_inS (t : ℕ) (ht : InS t) (hlt : t < 289) :
    t ∈ ({1, 4, 9, 16, 36, 64, 144, 256} : Finset ℕ) := by
  obtain ⟨k, hk | hk | hk⟩ := ht
  · have : k < 5 := by
      by_contra h
      have := Nat.pow_le_pow_right (by norm_num : 0 < 4) (not_lt.mp h)
      norm_num at this
      omega
    interval_cases k <;> simp [hk]
  · have : k < 3 := by
      by_contra h
      have := Nat.pow_le_pow_right (by norm_num : 0 < 4) (not_lt.mp h)
      norm_num at this
      omega
    interval_cases k <;> simp [hk]
  · have : 0 < 4 ^ k := by positivity
    omega

lemma small_check : ∀ U ∈ ({1, 4, 9, 16, 36, 64, 144, 256} : Finset ℕ).powerset,
    ∀ s ∈ ({1, 9, 289} : Finset ℕ), (∀ t ∈ U, t < s) → U.sum id ≠ s := by
  decide +kernel

/-- No element of S is a sum of distinct smaller elements of S. -/
lemma not_sum_smaller (s : ℕ) (hs : InS s) (T : Finset ℕ) (hT : ∀ t ∈ T, InS t ∧ t < s) :
    T.sum id ≠ s := by
  induction s using Nat.strong_induction_on generalizing T with
  | _ s ih =>
    intro hsum
    have hspos := inS_pos s hs
    by_cases h4 : 4 ∣ s
    · obtain ⟨d, hd, T', hT', hsplit⟩ := split_sum T (fun t ht => (hT t ht).1)
      have hd4 : d % 4 = 0 := by omega
      have hd0 : d = 0 := by
        simp only [Dset, Finset.mem_insert, Finset.mem_singleton] at hd
        omega
      apply ih (s / 4) (by omega) (inS_div4 s hs h4) T'
      · intro t' ht'
        refine ⟨(hT' t' ht').1, ?_⟩
        have := (hT (4 * t') (hT' t' ht').2).2
        omega
      · omega
    · have hsub : T ⊆ ({1, 4, 9, 16, 36, 64, 144, 256} : Finset ℕ) := by
        intro t ht
        have h289 : s ≤ 289 := by rcases inS_odd s hs h4 with h | h | h <;> omega
        exact small_inS t (hT t ht).1 (by have := (hT t ht).2; omega)
      have hs3 : s ∈ ({1, 9, 289} : Finset ℕ) := by
        rcases inS_odd s hs h4 with h | h | h <;> simp [h]
      exact small_check T (Finset.mem_powerset.mpr hsub) s hs3 (fun t ht => (hT t ht).2) hsum

/-! ## Every square is a sum of distinct elements of S -/

/-- x is a sum of distinct elements of S. -/
def RepS (x : ℕ) : Prop := ∃ T : Finset ℕ, (∀ t ∈ T, InS t) ∧ T.sum id = x

lemma rep_step (y d : ℕ) (hd : d ∈ Dset) (hy : RepS y) : RepS (d + 4 * y) := by
  obtain ⟨T, hT, hsum⟩ := hy
  obtain ⟨U, hU, hUs⟩ : ∃ U ⊆ ({1, 9, 289} : Finset ℕ), U.sum id = d := by
    simp only [Dset, Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨∅, by simp, by simp⟩
    · exact ⟨{1}, by decide, by decide⟩
    · exact ⟨{9}, by decide, by decide⟩
    · exact ⟨{1, 9}, by decide, by decide⟩
    · exact ⟨{289}, by decide, by decide⟩
    · exact ⟨{1, 289}, by decide, by decide⟩
    · exact ⟨{9, 289}, by decide, by decide⟩
    · exact ⟨{1, 9, 289}, by decide, by decide⟩
  have hUodd : ∀ u ∈ U, u % 2 = 1 := by
    intro u hu
    have := hU hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with rfl | rfl | rfl <;> norm_num
  refine ⟨U ∪ T.image (4 * ·), ?_, ?_⟩
  · intro t ht
    rcases Finset.mem_union.mp ht with h | h
    · have := hU h
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with rfl | rfl | rfl
      · exact ⟨0, Or.inl rfl⟩
      · exact ⟨0, Or.inr (Or.inl rfl)⟩
      · exact ⟨0, Or.inr (Or.inr rfl)⟩
    · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp h
      exact inS_mul4 s (hT s hs)
  · rw [Finset.sum_union, Finset.sum_image, hUs, ← hsum, Finset.mul_sum]
    · rfl
    · intro u _ v _ huv
      simp only at huv
      omega
    · rw [Finset.disjoint_left]
      intro t htU htI
      obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp htI
      have := hUodd _ htU
      omega

/-- A search for a representation, with fuel: x = d + 4y with d a subset sum of {1, 9, 289}. -/
def repB : ℕ → ℕ → Bool
  | 0, x => x == 0
  | f + 1, x =>
    if x = 0 then true
    else if x % 4 = 0 then repB f (x / 4)
    else if x % 4 = 1 then
      repB f (x / 4) || (decide (9 ≤ x) && repB f ((x - 9) / 4)) ||
        (decide (289 ≤ x) && repB f ((x - 289) / 4))
    else if x % 4 = 2 then
      (decide (10 ≤ x) && repB f ((x - 10) / 4)) || (decide (290 ≤ x) && repB f ((x - 290) / 4)) ||
        (decide (298 ≤ x) && repB f ((x - 298) / 4))
    else decide (299 ≤ x) && repB f ((x - 299) / 4)

lemma rep_of (x y d : ℕ) (hd : d ∈ Dset) (hxy : x = d + 4 * y) (hy : RepS y) : RepS x := by
  rw [hxy]
  exact rep_step y d hd hy

lemma repB_sound (f x : ℕ) (h : repB f x = true) : RepS x := by
  induction f generalizing x with
  | zero =>
    simp only [repB, beq_iff_eq] at h
    subst h
    exact ⟨∅, by simp, by simp⟩
  | succ f ih =>
    have hD : ∀ d ∈ ([0, 1, 9, 10, 289, 290, 298, 299] : List ℕ), d ∈ Dset := by decide
    simp only [repB] at h
    split_ifs at h with h0 h1 h2 h3
    · subst h0
      exact ⟨∅, by simp, by simp⟩
    · exact rep_of x (x / 4) 0 (by decide) (by omega) (ih _ h)
    · simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
      rcases h with (h | ⟨hle, h⟩) | ⟨hle, h⟩
      · exact rep_of x (x / 4) 1 (by decide) (by omega) (ih _ h)
      · exact rep_of x ((x - 9) / 4) 9 (by decide) (by omega) (ih _ h)
      · exact rep_of x ((x - 289) / 4) 289 (by decide) (by omega) (ih _ h)
    · simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
      rcases h with (⟨hle, h⟩ | ⟨hle, h⟩) | ⟨hle, h⟩
      · exact rep_of x ((x - 10) / 4) 10 (by decide) (by omega) (ih _ h)
      · exact rep_of x ((x - 290) / 4) 290 (by decide) (by omega) (ih _ h)
      · exact rep_of x ((x - 298) / 4) 298 (by decide) (by omega) (ih _ h)
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact rep_of x ((x - 299) / 4) 299 (by decide) (by omega) (ih _ h.2)

/-- The numbers 1 mod 4 that are not sums of distinct elements of S. -/
def F1 : List ℕ := [33, 97, 133, 137, 141, 177, 241, 397, 541, 557, 569, 573, 673, 713, 717, 817,
  973, 1697, 4001]

/-- The numbers 2 mod 4 that are not sums of distinct elements of S. -/
def F2 : List ℕ := [2, 6, 18, 22, 34, 38, 42, 54, 58, 70, 82, 86, 98, 102, 106, 118, 122, 134, 138,
  142, 146, 150, 162, 166, 178, 182, 186, 198, 202, 214, 226, 230, 242, 246, 250, 262, 278, 422,
  578, 678, 682, 722, 822, 826, 838, 854, 998, 1254, 1878, 4182]

lemma F1_le (x : ℕ) (hx : x ∈ F1) : x ≤ 4001 := by
  simp only [F1, List.mem_cons, List.not_mem_nil, or_false] at hx
  omega

lemma F2_le (x : ℕ) (hx : x ∈ F2) : x ≤ 4182 := by
  simp only [F2, List.mem_cons, List.not_mem_nil, or_false] at hx
  omega

/-- The property checked at k: 4k+1 and 4k+2 are found by the search unless they are listed. -/
def P (k : ℕ) : Bool :=
  (F1.contains (4 * k + 1) || repB 8 (4 * k + 1)) && (F2.contains (4 * k + 2) || repB 8 (4 * k + 2))

/-- P holds at lo, lo + 1, ..., lo + k - 1. -/
def chk : ℕ → ℕ → Bool
  | _, 0 => true
  | lo, k + 1 => P lo && chk (lo + 1) k

lemma chk_spec (lo k : ℕ) (h : chk lo k = true) (i : ℕ) (hi : i < k) : P (lo + i) = true := by
  induction k generalizing lo i with
  | zero => omega
  | succ k ih =>
    simp only [chk, Bool.and_eq_true] at h
    rcases i with _ | i
    · simpa using h.1
    · have := ih (lo + 1) h.2 i (by omega)
      rwa [show lo + 1 + i = lo + (i + 1) by omega] at this

/-! The finite part, in nine kernel checks: below 4 * 4500 every number 1 mod 4 outside F1 and
every number 2 mod 4 outside F2 is found by the search. -/
lemma chunk0 : chk 0 500 = true := by decide +kernel
lemma chunk1 : chk 500 500 = true := by decide +kernel
lemma chunk2 : chk 1000 500 = true := by decide +kernel
lemma chunk3 : chk 1500 500 = true := by decide +kernel
lemma chunk4 : chk 2000 500 = true := by decide +kernel
lemma chunk5 : chk 2500 500 = true := by decide +kernel
lemma chunk6 : chk 3000 500 = true := by decide +kernel
lemma chunk7 : chk 3500 500 = true := by decide +kernel
lemma chunk8 : chk 4000 500 = true := by decide +kernel

lemma P_all (k : ℕ) (hk : k < 4500) : P k = true := by
  have key : ∀ lo, chk lo 500 = true → lo ≤ k → k < lo + 500 → P k = true := by
    intro lo h h1 h2
    have := chk_spec lo 500 h (k - lo) (by omega)
    rwa [show lo + (k - lo) = k by omega] at this
  rcases Nat.lt_or_ge k 500 with h | h
  · exact key 0 chunk0 (by omega) (by omega)
  rcases Nat.lt_or_ge k 1000 with h' | h'
  · exact key 500 chunk1 (by omega) (by omega)
  rcases Nat.lt_or_ge k 1500 with h'' | h''
  · exact key 1000 chunk2 (by omega) (by omega)
  rcases Nat.lt_or_ge k 2000 with h3 | h3
  · exact key 1500 chunk3 (by omega) (by omega)
  rcases Nat.lt_or_ge k 2500 with h4 | h4
  · exact key 2000 chunk4 (by omega) (by omega)
  rcases Nat.lt_or_ge k 3000 with h5 | h5
  · exact key 2500 chunk5 (by omega) (by omega)
  rcases Nat.lt_or_ge k 3500 with h6 | h6
  · exact key 3000 chunk6 (by omega) (by omega)
  rcases Nat.lt_or_ge k 4000 with h7 | h7
  · exact key 3500 chunk7 (by omega) (by omega)
  · exact key 4000 chunk8 (by omega) (by omega)

lemma rep12 (x : ℕ) (hx : (x % 4 = 1 ∧ x ∉ F1) ∨ (x % 4 = 2 ∧ x ∉ F2)) : RepS x := by
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    rcases Nat.lt_or_ge x 17100 with hlt | hge
    · have hP := P_all (x / 4) (by omega)
      simp only [P, Bool.and_eq_true, Bool.or_eq_true] at hP
      apply repB_sound 8 x
      rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hx1 : 4 * (x / 4) + 1 = x := by omega
        rw [hx1] at hP
        exact hP.1.resolve_left (by simpa using h2)
      · have hx2 : 4 * (x / 4) + 2 = x := by omega
        rw [hx2] at hP
        exact hP.2.resolve_left (by simpa using h2)
    · have notF1 : ∀ z, 4001 < z → z ∉ F1 := fun z hz hm => by have := F1_le z hm; omega
      have notF2 : ∀ z, 4182 < z → z ∉ F2 := fun z hz hm => by have := F2_le z hm; omega
      have hD1 : (1 : ℕ) ∈ Dset := by decide
      have hD9 : (9 : ℕ) ∈ Dset := by decide
      have hD10 : (10 : ℕ) ∈ Dset := by decide
      have hD290 : (290 : ℕ) ∈ Dset := by decide
      rcases hx with ⟨h1, _⟩ | ⟨h1, _⟩
      · -- x = 1 + 4y = 9 + 4(y - 2)
        set y := (x - 1) / 4 with hy
        have hxy : x = 1 + 4 * y := by omega
        have hy4 : y % 4 = 0 ∨ y % 4 = 1 ∨ y % 4 = 2 ∨ y % 4 = 3 := by omega
        rcases hy4 with h | h | h | h
        · have := rep_step (y - 2) 9 hD9 (ih (y - 2) (by omega) (Or.inr ⟨by omega, notF2 _ (by omega)⟩))
          rwa [show 9 + 4 * (y - 2) = x by omega] at this
        · have := rep_step y 1 hD1 (ih y (by omega) (Or.inl ⟨h, notF1 _ (by omega)⟩))
          rwa [← hxy] at this
        · have := rep_step y 1 hD1 (ih y (by omega) (Or.inr ⟨h, notF2 _ (by omega)⟩))
          rwa [← hxy] at this
        · have := rep_step (y - 2) 9 hD9 (ih (y - 2) (by omega) (Or.inl ⟨by omega, notF1 _ (by omega)⟩))
          rwa [show 9 + 4 * (y - 2) = x by omega] at this
      · -- x = 10 + 4y = 290 + 4(y - 70)
        set y := (x - 10) / 4 with hy
        have hxy : x = 10 + 4 * y := by omega
        have hy4 : y % 4 = 0 ∨ y % 4 = 1 ∨ y % 4 = 2 ∨ y % 4 = 3 := by omega
        rcases hy4 with h | h | h | h
        · have := rep_step (y - 70) 290 hD290
            (ih (y - 70) (by omega) (Or.inr ⟨by omega, notF2 _ (by omega)⟩))
          rwa [show 290 + 4 * (y - 70) = x by omega] at this
        · have := rep_step y 10 hD10 (ih y (by omega) (Or.inl ⟨h, notF1 _ (by omega)⟩))
          rwa [← hxy] at this
        · have := rep_step y 10 hD10 (ih y (by omega) (Or.inr ⟨h, notF2 _ (by omega)⟩))
          rwa [← hxy] at this
        · have := rep_step (y - 70) 290 hD290
            (ih (y - 70) (by omega) (Or.inl ⟨by omega, notF1 _ (by omega)⟩))
          rwa [show 290 + 4 * (y - 70) = x by omega] at this

lemma F1_no_square : ∀ j < 64, j ^ 2 ∉ F1 := by decide

lemma rep_sq (j : ℕ) : RepS (j ^ 2) := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    rcases Nat.even_or_odd j with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · rcases Nat.eq_zero_or_pos i with rfl | hi
      · exact ⟨∅, by simp, by simp⟩
      · have := rep_step (i ^ 2) 0 (by decide) (ih i (by omega))
        rwa [show 0 + 4 * i ^ 2 = (i + i) ^ 2 by ring] at this
    · apply rep12
      left
      refine ⟨by ring_nf; omega, fun hm => ?_⟩
      have hle := F1_le _ hm
      have hj : 2 * i + 1 < 64 := by nlinarith
      exact F1_no_square (2 * i + 1) hj hm

/-! ## The greedy sequence is g -/

lemma list_nodup (n : ℕ) : ((List.range n).map g).Nodup :=
  List.Nodup.map g_strictMono.injective List.nodup_range

/-- Every square below g n is the sum of a subset of g(0), ..., g(n-1). -/
lemma sq_subset_sum (n m : ℕ) (hsq : IsSquare m) (hm : m < g n) :
    IsSubsetSum ((List.range n).map g) m := by
  obtain ⟨j, rfl⟩ := hsq
  obtain ⟨T, hT, hsum⟩ := rep_sq j
  rw [sq] at hsum
  set L := (List.range n).map g with hL
  have hTL : ∀ t ∈ T, t ∈ L := by
    intro t ht
    have hle : t ≤ T.sum id := by
      have := Finset.single_le_sum (f := id) (fun _ _ => Nat.zero_le _) ht
      simpa using this
    obtain ⟨k, rfl⟩ := inS_eq_g t (hT t ht)
    have hk : k < n := g_strictMono.lt_iff_lt.mp (by omega)
    exact List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩
  refine ⟨L.filter (fun x => decide (x ∈ T)), List.filter_sublist, ?_⟩
  have hnd : (L.filter (fun x => decide (x ∈ T))).Nodup := (list_nodup n).filter _
  have hfin : (L.filter (fun x => decide (x ∈ T))).toFinset = T := by
    ext x
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨hTL x h, h⟩⟩
  have := List.sum_toFinset id hnd
  rw [hfin, List.map_id] at this
  rw [← this, hsum]

/-- g n is not the sum of a subset of g(0), ..., g(n-1). -/
lemma g_not_subset_sum (n : ℕ) : ¬ IsSubsetSum ((List.range n).map g) (g n) := by
  rintro ⟨M, hM, hsum⟩
  have hnd : M.Nodup := (list_nodup n).sublist hM
  apply not_sum_smaller (g n) (g_inS n) M.toFinset
  · intro t ht
    have htL : t ∈ (List.range n).map g := hM.subset (List.mem_toFinset.mp ht)
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp htL
    exact ⟨g_inS k, g_strictMono (List.mem_range.mp hk)⟩
  · rw [List.sum_toFinset id hnd, List.map_id, hsum]

lemma next_eq (n : ℕ) : next ((List.range n).map g) = g n := by
  have hmem : g n ∈ {m : ℕ | IsSquare m ∧ ¬ IsSubsetSum ((List.range n).map g) m} :=
    ⟨g_isSquare n, g_not_subset_sum n⟩
  apply le_antisymm (Nat.sInf_le hmem)
  apply le_csInf ⟨g n, hmem⟩
  rintro m ⟨hsq, hns⟩
  by_contra hlt
  exact hns (sq_subset_sum n m hsq (by omega))

lemma terms_eq (n : ℕ) : terms n = (List.range n).map g := by
  induction n with
  | zero => rfl
  | succ n ih => rw [terms, ih, next_eq, List.range_succ, List.map_append]; rfl

lemma a_eq (n : ℕ) : a n = g (n - 1) := by rw [a, terms_eq, next_eq]

/-- Barker's recurrence: a(n) = 4 a(n-3) for n > 9. -/
theorem recurrence (n : ℕ) (hn : 9 < n) : a n = 4 * a (n - 3) := by
  rw [a_eq, a_eq, show n - 1 = (n - 4) + 3 by omega, g_shift _ (by omega),
    show n - 3 - 1 = n - 4 by omega]

/-- Barker's g.f., as A(x) * (4x^3 - 1) = -x * (33x^8 + ... + 1) in Q[[x]]. -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (4 * X ^ 3 - 1) =
    -X * (33 * X ^ 8 + 112 * X ^ 7 + 80 * X ^ 6 + 28 * X ^ 5 + 20 * X ^ 4 + 12 * X ^ 3 +
      9 * X ^ 2 + 4 * X + 1) := by
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have hC : ∀ c : ℕ, ((c : ℚ⟦X⟧)) = C (c : ℚ) := fun c => (map_natCast C c).symm
  have e1 : A * (4 * X ^ 3 - 1) = C (4 : ℚ) * (A * X ^ 3) - A := by
    rw [show (4 : ℚ⟦X⟧) = C (4 : ℚ) from (map_ofNat C 4).symm]
    ring
  have e2 : -X * (33 * X ^ 8 + 112 * X ^ 7 + 80 * X ^ 6 + 28 * X ^ 5 + 20 * X ^ 4 +
      12 * X ^ 3 + 9 * X ^ 2 + 4 * X + 1 : ℚ⟦X⟧) =
      -(C (33 : ℚ) * X ^ 9 + C (112 : ℚ) * X ^ 8 + C (80 : ℚ) * X ^ 7 + C (28 : ℚ) * X ^ 6 +
        C (20 : ℚ) * X ^ 5 + C (12 : ℚ) * X ^ 4 + C (9 : ℚ) * X ^ 3 + C (4 : ℚ) * X ^ 2 + X) := by
    rw [show (33 : ℚ⟦X⟧) = C (33 : ℚ) from (map_ofNat C 33).symm,
      show (112 : ℚ⟦X⟧) = C (112 : ℚ) from (map_ofNat C 112).symm,
      show (80 : ℚ⟦X⟧) = C (80 : ℚ) from (map_ofNat C 80).symm,
      show (28 : ℚ⟦X⟧) = C (28 : ℚ) from (map_ofNat C 28).symm,
      show (20 : ℚ⟦X⟧) = C (20 : ℚ) from (map_ofNat C 20).symm,
      show (12 : ℚ⟦X⟧) = C (12 : ℚ) from (map_ofNat C 12).symm,
      show (9 : ℚ⟦X⟧) = C (9 : ℚ) from (map_ofNat C 9).symm,
      show (4 : ℚ⟦X⟧) = C (4 : ℚ) from (map_ofNat C 4).symm]
    ring
  rw [e1, e2]
  ext n
  simp only [map_sub, map_neg, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_X_pow, coeff_X, hA,
    coeff_mk]
  rcases Nat.lt_or_ge n 13 with hn | hn
  · interval_cases n <;> norm_num [a_eq, g, c3]
  · have hr := recurrence n (by omega)
    simp only [coeff_C, show 3 ≤ n by omega, show 2 ≤ n by omega, show 4 ≤ n by omega,
      show 5 ≤ n by omega, show 6 ≤ n by omega, show 7 ≤ n by omega, show 8 ≤ n by omega,
      show 9 ≤ n by omega, if_true, show n - 2 ≠ 0 by omega, show n - 3 ≠ 0 by omega,
      show n - 4 ≠ 0 by omega, show n - 5 ≠ 0 by omega, show n - 6 ≠ 0 by omega,
      show n - 7 ≠ 0 by omega, show n - 8 ≠ 0 by omega, show n - 9 ≠ 0 by omega,
      show n ≠ 0 by omega, show n ≠ 1 by omega, if_false]
    rw [hr]
    push_cast
    ring

/-- The whole conjecture of the entry: recurrence and g.f. -/
theorem conjecture : (∀ n : ℕ, 9 < n → a n = 4 * a (n - 3)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (4 * X ^ 3 - 1) =
      -X * (33 * X ^ 8 + 112 * X ^ 7 + 80 * X ^ 6 + 28 * X ^ 5 + 20 * X ^ 4 + 12 * X ^ 3 +
        9 * X ^ 2 + 4 * X + 1) :=
  ⟨recurrence, gf⟩

/-- Controls from the entry: a(1..10) = 1, 4, 9, 16, 36, 64, 144, 256, 289, 576. -/
lemma controls : a 1 = 1 ∧ a 2 = 4 ∧ a 3 = 9 ∧ a 4 = 16 ∧ a 5 = 36 ∧ a 6 = 64 ∧ a 7 = 144 ∧
    a 8 = 256 ∧ a 9 = 289 ∧ a 10 = 576 := by
  simp only [a_eq]
  decide

end OMA.S_oeis_a226076

theorem OMA.solution : type_of% @OMA.S_oeis_a226076.main :=
  OMA.S_oeis_a226076.conjecture
