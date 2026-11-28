import OMAStatements.S_oeis_a344812
import Mathlib

namespace A344812

open OMA.S_oeis_a344812

/-- Multisets of k positive integers, all at most b, whose squares sum to m. -/
def T (k b m : ℕ) : Set (Multiset ℕ) :=
  {s | Multiset.card s = k ∧ (∀ x ∈ s, 0 < x ∧ x ≤ b) ∧ (s.map (· ^ 2)).sum = m}

def step (f : ℕ → ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | b+1, m => step f b m + (if (b+1)^2 ≤ m then f (b+1) (m - (b+1)^2) else 0)

/-- cnt k b m is the number of elements of T k b m. -/
def cnt : ℕ → ℕ → ℕ → ℕ
  | 0 => fun _ m => if m = 0 then 1 else 0
  | k+1 => step (cnt k)

/-- A lower bound for acc + cnt that is cheap to evaluate: it stops as soon as 8 is reached and
skips branches where the remaining parts cannot reach m. -/
def stepA (k : ℕ) (f : ℕ → ℕ → ℕ → ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, acc => acc
  | b+1, m, acc => if 8 ≤ acc then acc else if (k+1) * (b+1)^2 < m then acc else
      stepA k f b m (if (b+1)^2 ≤ m then f (b+1) (m - (b+1)^2) acc else acc)

def cntA : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0 => fun _ m acc => if m = 0 then acc + 1 else acc
  | k+1 => stepA k (cntA k)

theorem stepA_le (k : ℕ) (f : ℕ → ℕ → ℕ → ℕ) (g : ℕ → ℕ → ℕ)
    (h : ∀ b m acc, f b m acc ≤ acc + g b m) :
    ∀ b m acc, stepA k f b m acc ≤ acc + step g b m := by
  intro b
  induction b with
  | zero => intro m acc; simp [stepA, step]
  | succ b ih =>
    intro m acc
    simp only [stepA, step]
    by_cases h0 : 8 ≤ acc
    · rw [if_pos h0]
      exact Nat.le_add_right _ _
    · rw [if_neg h0]
      by_cases h1 : (k + 1) * (b + 1) ^ 2 < m
      · rw [if_pos h1]
        exact Nat.le_add_right _ _
      · rw [if_neg h1]
        refine le_trans (ih m _) ?_
        split_ifs
        · have := h (b + 1) (m - (b + 1) ^ 2) acc
          omega
        · omega

theorem cntA_le : ∀ k b m acc, cntA k b m acc ≤ acc + cnt k b m := by
  intro k
  induction k with
  | zero =>
    intro b m acc
    show (if m = 0 then acc + 1 else acc) ≤ acc + (if m = 0 then 1 else 0)
    split_ifs <;> omega
  | succ k ih => intro b m acc; exact stepA_le k _ _ ih b m acc

theorem T_zero (b m : ℕ) : T 0 b m = if m = 0 then {0} else ∅ := by
  ext s
  split_ifs with h
  · subst h
    simp only [T, Set.mem_ofPred_eq, Multiset.card_eq_zero, Set.mem_singleton_iff]
    constructor
    · exact fun h => h.1
    · rintro rfl; simp
  · simp only [T, Set.mem_ofPred_eq, Multiset.card_eq_zero, Set.mem_empty_iff_false, iff_false]
    rintro ⟨rfl, -, h'⟩
    simp at h'
    exact h h'.symm

theorem T_succ_zero (k m : ℕ) : T (k+1) 0 m = ∅ := by
  ext s
  simp only [T, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨hc, hb, -⟩
  obtain ⟨x, hx⟩ := Multiset.card_pos_iff_exists_mem.1 (by omega : 0 < Multiset.card s)
  have := hb x hx
  omega

theorem T_succ_succ (k b m : ℕ) : T (k+1) (b+1) m = T (k+1) b m ∪
    (if (b+1)^2 ≤ m then (fun t => (b+1) ::ₘ t) '' T k (b+1) (m - (b+1)^2) else ∅) := by
  ext s
  constructor
  · rintro ⟨hc, hb, hs⟩
    by_cases hmem : b+1 ∈ s
    · right
      obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem hmem
      simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons] at hs hc
      rw [if_pos (by omega)]
      exact ⟨t, ⟨by omega, fun x hx => hb x (Multiset.mem_cons_of_mem hx), by omega⟩, rfl⟩
    · left
      refine ⟨hc, fun x hx => ?_, hs⟩
      have h1 := hb x hx
      have h2 : x ≠ b+1 := fun h => hmem (h ▸ hx)
      omega
  · rintro (⟨hc, hb, hs⟩ | h)
    · exact ⟨hc, fun x hx => by have := hb x hx; omega, hs⟩
    · split_ifs at h with hle
      · obtain ⟨t, ⟨hc, hb, hs⟩, rfl⟩ := h
        refine ⟨by simp [hc], fun x hx => ?_, ?_⟩
        · rcases Multiset.mem_cons.1 hx with rfl | hx
          · omega
          · exact hb x hx
        · simp only [Multiset.map_cons, Multiset.sum_cons]
          omega
      · exact absurd h (Set.notMem_empty _)

theorem T_card : ∀ k b m, (T k b m).Finite ∧ (T k b m).ncard = cnt k b m := by
  intro k
  induction k with
  | zero =>
    intro b m
    rw [T_zero]
    split_ifs with h <;> simp [cnt, h]
  | succ k ih =>
    intro b
    induction b with
    | zero => intro m; rw [T_succ_zero]; simp [cnt, step]
    | succ b ihb =>
      intro m
      rw [T_succ_succ]
      have hstep : cnt (k+1) (b+1) m = cnt (k+1) b m +
          (if (b+1)^2 ≤ m then cnt k (b+1) (m - (b+1)^2) else 0) := rfl
      have hinj : Function.Injective (fun t : Multiset ℕ => (b+1) ::ₘ t) :=
        fun t t' h => (Multiset.cons_inj_right _).1 h
      split_ifs with hle
      · have hfin := ((ih (b+1) (m - (b+1)^2)).1.image (fun t => (b+1) ::ₘ t))
        refine ⟨(ihb m).1.union hfin, ?_⟩
        have hdisj : Disjoint (T (k+1) b m) ((fun t => (b+1) ::ₘ t) '' T k (b+1) (m - (b+1)^2)) := by
          rw [Set.disjoint_left]
          rintro s ⟨-, hb, -⟩ ⟨t, -, rfl⟩
          have := hb (b+1) (Multiset.mem_cons_self _ _)
          omega
        rw [Set.ncard_union_eq hdisj (ihb m).1 hfin, Set.ncard_image_of_injective _ hinj,
          (ihb m).2, (ih _ _).2, hstep, if_pos hle]
      · rw [hstep, if_neg hle, Set.union_empty, Nat.add_zero]
        exact ihb m

/-- The set counted by r. -/
def R (m : ℕ) : Set (Multiset ℕ) :=
  {s | Multiset.card s = 6 ∧ (∀ x ∈ s, 0 < x) ∧ (s.map (· ^ 2)).sum = m}

theorem r_eq_ncard (m : ℕ) : r m = (R m).ncard := rfl

theorem T_sub_R (b m : ℕ) : T 6 b m ⊆ R m :=
  fun _ hs => ⟨hs.1, fun x hx => (hs.2.1 x hx).1, hs.2.2⟩

theorem R_eq_T (m b : ℕ) (hb : m ≤ b ^ 2) : R m = T 6 b m := by
  refine Set.Subset.antisymm ?_ (T_sub_R b m)
  rintro s ⟨hc, hp, hs⟩
  refine ⟨hc, fun x hx => ⟨hp x hx, ?_⟩, hs⟩
  have h1 : x ^ 2 ≤ (s.map (· ^ 2)).sum :=
    Multiset.le_sum_of_mem (Multiset.mem_map_of_mem (· ^ 2) hx)
  by_contra hlt
  have : b + 1 ≤ x := by omega
  nlinarith

theorem R_finite (m : ℕ) : (R m).Finite := by
  rw [R_eq_T m m (Nat.le_self_pow (by norm_num) m)]
  exact (T_card 6 m m).1

theorem r_eq (m b : ℕ) (hb : m ≤ b ^ 2) : r m = cnt 6 b m := by
  rw [r_eq_ncard, R_eq_T m b hb, (T_card 6 b m).2]

theorem r_ge (m b : ℕ) : cntA 6 b m 0 ≤ r m := by
  rw [r_eq_ncard]
  calc cntA 6 b m 0 ≤ cnt 6 b m := by have := cntA_le 6 b m 0; omega
    _ = (T 6 b m).ncard := (T_card 6 b m).2.symm
    _ ≤ (R m).ncard := Set.ncard_le_ncard (T_sub_R b m) (R_finite m)

theorem mk5 (a b c d e t : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e)
    (h : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2 = t) :
    ∃ u : Multiset ℕ, Multiset.card u = 5 ∧ (∀ x ∈ u, 0 < x) ∧ (u.map (· ^ 2)).sum = t := by
  refine ⟨a ::ₘ b ::ₘ c ::ₘ d ::ₘ e ::ₘ 0, by simp, ?_, ?_⟩
  · intro x hx
    simp only [Multiset.mem_cons, Multiset.notMem_zero, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption
  · simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.map_zero, Multiset.sum_zero]
    omega

theorem five (t : ℕ) (ht : 170 ≤ t) :
    ∃ u : Multiset ℕ, Multiset.card u = 5 ∧ (∀ x ∈ u, 0 < x) ∧ (u.map (· ^ 2)).sum = t := by
  obtain ⟨a, b, c, d, h⟩ := Nat.sum_four_squares (t - 169)
  rcases Nat.eq_zero_or_pos a with ha | ha <;> rcases Nat.eq_zero_or_pos b with hb | hb <;>
    rcases Nat.eq_zero_or_pos c with hc | hc <;> rcases Nat.eq_zero_or_pos d with hd | hd <;>
    (try simp only [ha, hb, hc, hd, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      zero_add, add_zero] at h) <;>
    first
    | exact mk5 a b c d 13 t ha hb hc hd (by norm_num) (by omega)
    | exact mk5 a b c 5 12 t ha hb hc (by norm_num) (by norm_num) (by omega)
    | exact mk5 a b d 5 12 t ha hb hd (by norm_num) (by norm_num) (by omega)
    | exact mk5 a c d 5 12 t ha hc hd (by norm_num) (by norm_num) (by omega)
    | exact mk5 b c d 5 12 t hb hc hd (by norm_num) (by norm_num) (by omega)
    | exact mk5 a b 3 4 12 t ha hb (by norm_num) (by norm_num) (by norm_num) (by omega)
    | exact mk5 a c 3 4 12 t ha hc (by norm_num) (by norm_num) (by norm_num) (by omega)
    | exact mk5 a d 3 4 12 t ha hd (by norm_num) (by norm_num) (by norm_num) (by omega)
    | exact mk5 b c 3 4 12 t hb hc (by norm_num) (by norm_num) (by norm_num) (by omega)
    | exact mk5 b d 3 4 12 t hb hd (by norm_num) (by norm_num) (by norm_num) (by omega)
    | exact mk5 c d 3 4 12 t hc hd (by norm_num) (by norm_num) (by norm_num) (by omega)
    | exact mk5 a 4 5 8 8 t ha (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by omega)
    | exact mk5 b 4 5 8 8 t hb (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by omega)
    | exact mk5 c 4 5 8 8 t hc (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by omega)
    | exact mk5 d 4 5 8 8 t hd (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by omega)
    | omega

/-- Large numbers: eight representations with distinct largest parts. -/
theorem big (m : ℕ) (hm : 1259 ≤ m) : 8 ≤ r m := by
  have hk1 := Nat.sqrt_le' (m - 170)
  have hk2 := Nat.lt_succ_sqrt' (m - 170)
  have hk3 : 33 ≤ Nat.sqrt (m - 170) := by
    rw [Nat.le_sqrt]
    omega
  generalize Nat.sqrt (m - 170) = k at hk1 hk2 hk3
  simp only [Nat.succ_eq_add_one] at hk2
  have hk1' : k ^ 2 + 170 ≤ m := by omega
  have hk2' : m < (k + 1) ^ 2 + 170 := by omega
  clear hk1 hk2
  have H : ∀ i, i < 8 → ∃ u : Multiset ℕ, Multiset.card u = 5 ∧ (∀ x ∈ u, 0 < x) ∧
      (u.map (· ^ 2)).sum = m - (k - i) ^ 2 ∧ (∀ x ∈ u, x ≤ k - i) ∧ (k - i) ^ 2 ≤ m := by
    intro i hi
    obtain ⟨j, hj⟩ : ∃ j, j = k - i := ⟨_, rfl⟩
    rw [← hj]
    have hj1 : j ≤ k := by omega
    have hj2 : k ≤ j + 7 := by omega
    have hj0 : 26 ≤ j := by omega
    have hj3 : j ^ 2 + 170 ≤ m := by nlinarith
    have hj5 : (k + 1) ^ 2 ≤ (j + 8) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have hj4 : m ≤ 2 * j ^ 2 := by nlinarith
    obtain ⟨u, hu1, hu2, hu3⟩ := five (m - j ^ 2) (by omega)
    refine ⟨u, hu1, hu2, hu3, fun x hx => ?_, by omega⟩
    have h1 : x ^ 2 ≤ (u.map (· ^ 2)).sum :=
      Multiset.le_sum_of_mem (Multiset.mem_map_of_mem (· ^ 2) hx)
    by_contra hlt
    have : j + 1 ≤ x := by omega
    have : m - j ^ 2 ≤ j ^ 2 := by omega
    nlinarith
  choose! u hu using H
  have hsub : (fun i => (k - i) ::ₘ u i) '' (Finset.range 8 : Set ℕ) ⊆ R m := by
    rintro s ⟨i, hi, rfl⟩
    have hi : i < 8 := by simpa using hi
    obtain ⟨h1, h2, h3, h4, h5⟩ := hu i hi
    refine ⟨by simp [h1], fun x hx => ?_, ?_⟩
    · rcases Multiset.mem_cons.1 hx with rfl | hx
      · omega
      · exact h2 x hx
    · simp only [Multiset.map_cons, Multiset.sum_cons, h3]
      omega
  have key : ∀ i i', i < 8 → i' < 8 → (k - i) ::ₘ u i = (k - i') ::ₘ u i' → k - i ≤ k - i' := by
    intro i i' hi hi' h
    have hmem : k - i ∈ (k - i') ::ₘ u i' := h ▸ Multiset.mem_cons_self _ _
    rcases Multiset.mem_cons.1 hmem with h1 | h1
    · exact h1.le
    · exact (hu i' hi').2.2.2.1 _ h1
  have hinj : Set.InjOn (fun i => (k - i) ::ₘ u i) (Finset.range 8 : Set ℕ) := by
    intro i hi i' hi' h
    have hi : i < 8 := by simpa using hi
    have hi' : i' < 8 := by simpa using hi'
    have h1 := key i i' hi hi' h
    have h2 := key i' i hi' hi h.symm
    omega
  have hcard : ((fun i => (k - i) ::ₘ u i) '' (Finset.range 8 : Set ℕ)).ncard = 8 := by
    rw [hinj.ncard_image, Set.ncard_coe_finset, Finset.card_range]
  rw [r_eq_ncard, ← hcard]
  exact Set.ncard_le_ncard hsub (R_finite m)

def L : List ℕ := [78, 81, 84, 86, 87, 89, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103,
  104, 105, 107, 108, 109, 110, 111]

def q (m : ℕ) : Prop := m ∈ L ∨ 113 ≤ m

instance : DecidablePred q := fun m => by unfold q; infer_instance

theorem mid0 : ∀ m < 60, 8 ≤ cntA 6 36 (m + 113) 0 := by decide +kernel

theorem mid1 : ∀ m < 60, 8 ≤ cntA 6 36 (m + 173) 0 := by decide +kernel

theorem mid2 : ∀ m < 60, 8 ≤ cntA 6 36 (m + 233) 0 := by decide +kernel

theorem mid3 : ∀ m < 60, 8 ≤ cntA 6 36 (m + 293) 0 := by decide +kernel

theorem mid4 : ∀ m < 60, 8 ≤ cntA 6 36 (m + 353) 0 := by decide +kernel

theorem mid5 : ∀ m < 60, 8 ≤ cntA 6 36 (m + 413) 0 := by decide +kernel

theorem mid6 : ∀ m < 60, 8 ≤ cntA 6 36 (m + 473) 0 := by decide +kernel

theorem mid7 : ∀ m < 60, 8 ≤ cntA 6 36 (m + 533) 0 := by decide +kernel

theorem mid8 : ∀ m < 60, 8 ≤ cntA 6 36 (m + 593) 0 := by decide +kernel

theorem mid9 : ∀ m < 60, 8 ≤ cntA 6 36 (m + 653) 0 := by decide +kernel

theorem mid10 : ∀ m < 60, 8 ≤ cntA 6 36 (m + 713) 0 := by decide +kernel

theorem mid11 : ∀ m < 60, 8 ≤ cntA 6 36 (m + 773) 0 := by decide +kernel

theorem mid12 : ∀ m < 60, 8 ≤ cntA 6 36 (m + 833) 0 := by decide +kernel

theorem mid13 : ∀ m < 60, 8 ≤ cntA 6 36 (m + 893) 0 := by decide +kernel

theorem mid14 : ∀ m < 60, 8 ≤ cntA 6 36 (m + 953) 0 := by decide +kernel

theorem mid15 : ∀ m < 60, 8 ≤ cntA 6 36 (m + 1013) 0 := by decide +kernel

theorem mid16 : ∀ m < 60, 8 ≤ cntA 6 36 (m + 1073) 0 := by decide +kernel

theorem mid17 : ∀ m < 60, 8 ≤ cntA 6 36 (m + 1133) 0 := by decide +kernel

theorem mid18 : ∀ m < 60, 8 ≤ cntA 6 36 (m + 1193) 0 := by decide +kernel

theorem mid19 : ∀ m < 6, 8 ≤ cntA 6 36 (m + 1253) 0 := by decide +kernel

theorem mid (m : ℕ) (h1 : 113 ≤ m) (h2 : m < 1259) : 8 ≤ cntA 6 36 m 0 := by
  by_cases c0 : m < 173
  · have := mid0 (m - 113) (by omega)
    rwa [show m - 113 + 113 = m by omega] at this
  by_cases c1 : m < 233
  · have := mid1 (m - 173) (by omega)
    rwa [show m - 173 + 173 = m by omega] at this
  by_cases c2 : m < 293
  · have := mid2 (m - 233) (by omega)
    rwa [show m - 233 + 233 = m by omega] at this
  by_cases c3 : m < 353
  · have := mid3 (m - 293) (by omega)
    rwa [show m - 293 + 293 = m by omega] at this
  by_cases c4 : m < 413
  · have := mid4 (m - 353) (by omega)
    rwa [show m - 353 + 353 = m by omega] at this
  by_cases c5 : m < 473
  · have := mid5 (m - 413) (by omega)
    rwa [show m - 413 + 413 = m by omega] at this
  by_cases c6 : m < 533
  · have := mid6 (m - 473) (by omega)
    rwa [show m - 473 + 473 = m by omega] at this
  by_cases c7 : m < 593
  · have := mid7 (m - 533) (by omega)
    rwa [show m - 533 + 533 = m by omega] at this
  by_cases c8 : m < 653
  · have := mid8 (m - 593) (by omega)
    rwa [show m - 593 + 593 = m by omega] at this
  by_cases c9 : m < 713
  · have := mid9 (m - 653) (by omega)
    rwa [show m - 653 + 653 = m by omega] at this
  by_cases c10 : m < 773
  · have := mid10 (m - 713) (by omega)
    rwa [show m - 713 + 713 = m by omega] at this
  by_cases c11 : m < 833
  · have := mid11 (m - 773) (by omega)
    rwa [show m - 773 + 773 = m by omega] at this
  by_cases c12 : m < 893
  · have := mid12 (m - 833) (by omega)
    rwa [show m - 833 + 833 = m by omega] at this
  by_cases c13 : m < 953
  · have := mid13 (m - 893) (by omega)
    rwa [show m - 893 + 893 = m by omega] at this
  by_cases c14 : m < 1013
  · have := mid14 (m - 953) (by omega)
    rwa [show m - 953 + 953 = m by omega] at this
  by_cases c15 : m < 1073
  · have := mid15 (m - 1013) (by omega)
    rwa [show m - 1013 + 1013 = m by omega] at this
  by_cases c16 : m < 1133
  · have := mid16 (m - 1073) (by omega)
    rwa [show m - 1073 + 1073 = m by omega] at this
  by_cases c17 : m < 1193
  · have := mid17 (m - 1133) (by omega)
    rwa [show m - 1133 + 1133 = m by omega] at this
  by_cases c18 : m < 1253
  · have := mid18 (m - 1193) (by omega)
    rwa [show m - 1193 + 1193 = m by omega] at this
  have := mid19 (m - 1253) (by omega)
  rwa [show m - 1253 + 1253 = m by omega] at this

theorem low : ∀ m < 113, decide (8 ≤ cnt 6 11 m) = decide (m ∈ L) := by decide +kernel

theorem S_iff (m : ℕ) : m ∈ S ↔ q m := by
  show 8 ≤ r m ↔ q m
  rcases lt_or_ge m 113 with h | h
  · rw [r_eq m 11 (by omega)]
    have := low m h
    simp only [decide_eq_decide] at this
    rw [this]
    unfold q
    constructor
    · exact Or.inl
    · rintro (h' | h')
      · exact h'
      · omega
  · have hq : q m := Or.inr h
    refine ⟨fun _ => hq, fun _ => ?_⟩
    rcases lt_or_ge m 1259 with h' | h'
    · exact le_trans (mid m h h') (r_ge m 36)
    · exact big m h'

theorem a_eq (n : ℕ) : a n = Nat.nth q (n - 1) := by
  have : (· ∈ S) = q := funext fun m => propext (S_iff m)
  show Nat.nth (· ∈ S) (n - 1) = _
  rw [this]

theorem count_tail : ∀ i, Nat.count q (i + 113) = i + 25 := by
  intro i
  induction i with
  | zero => decide +kernel
  | succ i ih =>
    rw [show i + 1 + 113 = (i + 113) + 1 by ring, Nat.count_succ, ih,
      if_pos (show q (i + 113) from Or.inr (by omega))]

theorem nth_small : ∀ i < 25, Nat.count q (L.getD i 0) = i ∧ q (L.getD i 0) := by decide +kernel

theorem nth_q (i : ℕ) : Nat.nth q i = if i < 25 then L.getD i 0 else i + 88 := by
  split_ifs with h
  · obtain ⟨h1, h2⟩ := nth_small i h
    have := Nat.nth_count h2
    rwa [h1] at this
  · have h2 : q (i + 88) := Or.inr (by omega)
    have := Nat.nth_count h2
    rwa [show i + 88 = (i - 25) + 113 by omega, count_tail, show i - 25 + 25 = i by omega,
      show i - 25 + 113 = i + 88 by omega] at this

theorem a_big (n : ℕ) (hn : 26 ≤ n) : a n = n + 87 := by
  rw [a_eq, nth_q, if_neg (by omega)]
  omega

theorem a_small : ∀ n < 26, 1 ≤ n → a n = L.getD (n - 1) 0 := by
  intro n hn h1
  rw [a_eq, nth_q, if_pos (by omega)]

end A344812

theorem OMA.solution : type_of% @OMA.S_oeis_a344812.main := by
  refine ⟨fun n hn => ?_, ?_⟩
  · rw [A344812.a_big n (by omega), A344812.a_big (n - 1) (by omega),
      A344812.a_big (n - 2) (by omega)]
    omega
  · have hL : (PowerSeries.X - 1 : PowerSeries ℚ) ^ 2
        = PowerSeries.X ^ 2 - (PowerSeries.X ^ 1 + PowerSeries.X ^ 1) + 1 := by ring
    have hR : (PowerSeries.X * (-PowerSeries.X ^ 26 + PowerSeries.X ^ 25 - PowerSeries.X ^ 21
        + PowerSeries.X ^ 20 - 2 * PowerSeries.X ^ 7 + PowerSeries.X ^ 6
        + PowerSeries.X ^ 5 - PowerSeries.X ^ 4 - PowerSeries.X ^ 3
        - 75 * PowerSeries.X + 78) : PowerSeries ℚ)
        = -PowerSeries.X ^ 27 + PowerSeries.X ^ 26 - PowerSeries.X ^ 22 + PowerSeries.X ^ 21
          - PowerSeries.C 2 * PowerSeries.X ^ 8 + PowerSeries.X ^ 7 + PowerSeries.X ^ 6
          - PowerSeries.X ^ 5 - PowerSeries.X ^ 4 - PowerSeries.C 75 * PowerSeries.X ^ 2
          + PowerSeries.C 78 * PowerSeries.X ^ 1 := by
      simp only [map_ofNat]
      ring
    rw [hL, hR, mul_add, mul_sub, mul_add, mul_one]
    ext n
    simp only [map_add, map_sub, map_neg, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk,
      PowerSeries.coeff_X_pow]
    rcases lt_or_ge n 28 with h | h
    · have hs := A344812.a_small
      have hb := A344812.a_big
      interval_cases n <;> simp [hs, hb, A344812.L] <;> norm_num
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 28 := ⟨n - 28, by omega⟩
      have e1 : k + 28 - 2 = k + 26 := by omega
      have e2 : k + 28 - 1 = k + 27 := by omega
      simp only [e1, e2, A344812.a_big (k + 28) (by omega), A344812.a_big (k + 27) (by omega),
        A344812.a_big (k + 26) (by omega)]
      simp
      ring
