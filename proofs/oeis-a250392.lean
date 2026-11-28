import OMAStatements.S_oeis_a250392

/-!
# Proof of OEIS A250392

`a n` counts arrays `x : Fin 9 → Fin (n + 1)` such that in no 4 consecutive entries is there a
2-element subset `S` whose maximum equals the minimum of its complement.

Proof outline:
1. On a 4-tuple `(y 0, y 1, y 2, y 3)`, the forbidden condition holds iff
   `max (min (y 0) (y 1)) (min (y 2) (y 3)) = min (max (y 0) (y 1)) (max (y 2) (y 3))`,
   which is strictly order-invariant.
2. Partitioning valid arrays by their image `s ⊆ Fin (n + 1)` of size `k ∈ {0, ..., 9}` yields
   `a n = ∑ k ∈ range 10, c k * (n + 1).choose k`, where `c k` counts valid surjective arrays
   `Fin 9 → Fin k`.
3. Immediately `c 0 = 0`, `c 1 = 0`, and `c 9 = 9! = 362880`.
4. A 6-step dynamic program over triples `(p, q, r) ∈ (Fin m)^3` computes `a (m - 1)` for
   `m = 2, ..., 8`, verified in the kernel, determining `c 2, ..., c 8` uniquely.
5. Since `a n` is a linear combination of `(n + 1).choose k` for `k ≤ 9`, its 10th forward
   difference vanishes identically, establishing both the order-10 linear recurrence and the
   rational generating function.
-/

namespace OMA.A250392

open OMA.S_oeis_a250392 Finset

/-! ### 1. Equivalent 4-window condition and order-invariance -/

/-- Decidable check that the middle two sorted entries of `(a, b, c, d)` are distinct. -/
def good4 (a b c d : ℕ) : Bool :=
  max (min a b) (min c d) != min (max a b) (max c d)

/-- The array condition expressed via `good4` on all 6 windows of length 4. -/
def goodVal (y : Fin 9 → ℕ) : Bool :=
  good4 (y 0) (y 1) (y 2) (y 3) &&
  good4 (y 1) (y 2) (y 3) (y 4) &&
  good4 (y 2) (y 3) (y 4) (y 5) &&
  good4 (y 3) (y 4) (y 5) (y 6) &&
  good4 (y 4) (y 5) (y 6) (y 7) &&
  good4 (y 5) (y 6) (y 7) (y 8)

private lemma mem_powersetCard_two_fin4 (S : Finset (Fin 4)) :
    S ∈ (Finset.univ : Finset (Fin 4)).powersetCard 2 →
    S = {0, 1} ∨ S = {0, 2} ∨ S = {0, 3} ∨ S = {1, 2} ∨ S = {1, 3} ∨ S = {2, 3} := by
  revert S
  decide

private lemma bad4_of_split {a b c d v : ℕ} (ha : a ≤ v) (hb : b ≤ v) (hab : a = v ∨ b = v)
    (hc : v ≤ c) (hd : v ≤ d) (hcd : c = v ∨ d = v) :
    max (min a b) (min c d) = min (max a b) (max c d) ∧
    max (min a c) (min b d) = min (max a c) (max b d) ∧
    max (min a d) (min b c) = min (max a d) (max b c) := by
  omega

private lemma bad4_iff {n : ℕ} (y : Fin 4 → ℕ) (hy : ∀ t, y t < n + 1) :
    (∃ S ∈ (Finset.univ : Finset (Fin 4)).powersetCard 2, ∃ v < n + 1,
      (∀ t ∈ S, y t ≤ v) ∧ (∃ t ∈ S, y t = v) ∧
      (∀ t ∉ S, v ≤ y t) ∧ (∃ t ∉ S, y t = v)) ↔
    max (min (y 0) (y 1)) (min (y 2) (y 3)) = min (max (y 0) (y 1)) (max (y 2) (y 3)) := by
  constructor
  · rintro ⟨S, hS, v, _, h1, ⟨t1, ht1, hyt1⟩, h3, ⟨t2, ht2, hyt2⟩⟩
    rcases mem_powersetCard_two_fin4 S hS with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (bad4_of_split (h1 0 (by decide)) (h1 1 (by decide))
        (by fin_cases t1 <;> simp_all)
        (h3 2 (by decide)) (h3 3 (by decide))
        (by fin_cases t2 <;> simp_all)).1
    · exact (bad4_of_split (h1 0 (by decide)) (h1 2 (by decide))
        (by fin_cases t1 <;> simp_all)
        (h3 1 (by decide)) (h3 3 (by decide))
        (by fin_cases t2 <;> simp_all)).2.1
    · have := (bad4_of_split (h1 0 (by decide)) (h1 3 (by decide))
        (by fin_cases t1 <;> simp_all)
        (h3 1 (by decide)) (h3 2 (by decide))
        (by fin_cases t2 <;> simp_all)).2.1
      omega
    · have := (bad4_of_split (h1 1 (by decide)) (h1 2 (by decide))
        (by fin_cases t1 <;> simp_all)
        (h3 0 (by decide)) (h3 3 (by decide))
        (by fin_cases t2 <;> simp_all)).2.1
      omega
    · have := (bad4_of_split (h1 1 (by decide)) (h1 3 (by decide))
        (by fin_cases t1 <;> simp_all)
        (h3 0 (by decide)) (h3 2 (by decide))
        (by fin_cases t2 <;> simp_all)).2.1
      omega
    · have := (bad4_of_split (h1 2 (by decide)) (h1 3 (by decide))
        (by fin_cases t1 <;> simp_all)
        (h3 0 (by decide)) (h3 1 (by decide))
        (by fin_cases t2 <;> simp_all)).1
      omega
  · intro heq
    set v := max (min (y 0) (y 1)) (min (y 2) (y 3)) with hv_def
    have hv : v < n + 1 := by
      have := hy 0; have := hy 1; have := hy 2; have := hy 3; omega
    have hfin4 : ∀ t : Fin 4, t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 := by decide
    by_cases h01 : y 0 ≤ y 1 <;> by_cases h23 : y 2 ≤ y 3
    · refine ⟨{0, 2}, by decide, v, hv, ?_, ?_, ?_, ?_⟩
      · intro t ht; rcases hfin4 t with rfl | rfl | rfl | rfl <;> simp at ht <;> omega
      · by_cases h : y 0 = v
        · exact ⟨0, by decide, h⟩
        · exact ⟨2, by decide, by omega⟩
      · intro t ht; rcases hfin4 t with rfl | rfl | rfl | rfl <;> simp at ht <;> omega
      · by_cases h : y 1 = v
        · exact ⟨1, by decide, h⟩
        · exact ⟨3, by decide, by omega⟩
    · refine ⟨{0, 3}, by decide, v, hv, ?_, ?_, ?_, ?_⟩
      · intro t ht; rcases hfin4 t with rfl | rfl | rfl | rfl <;> simp at ht <;> omega
      · by_cases h : y 0 = v
        · exact ⟨0, by decide, h⟩
        · exact ⟨3, by decide, by omega⟩
      · intro t ht; rcases hfin4 t with rfl | rfl | rfl | rfl <;> simp at ht <;> omega
      · by_cases h : y 1 = v
        · exact ⟨1, by decide, h⟩
        · exact ⟨2, by decide, by omega⟩
    · refine ⟨{1, 2}, by decide, v, hv, ?_, ?_, ?_, ?_⟩
      · intro t ht; rcases hfin4 t with rfl | rfl | rfl | rfl <;> simp at ht <;> omega
      · by_cases h : y 1 = v
        · exact ⟨1, by decide, h⟩
        · exact ⟨2, by decide, by omega⟩
      · intro t ht; rcases hfin4 t with rfl | rfl | rfl | rfl <;> simp at ht <;> omega
      · by_cases h : y 0 = v
        · exact ⟨0, by decide, h⟩
        · exact ⟨3, by decide, by omega⟩
    · refine ⟨{1, 3}, by decide, v, hv, ?_, ?_, ?_, ?_⟩
      · intro t ht; rcases hfin4 t with rfl | rfl | rfl | rfl <;> simp at ht <;> omega
      · by_cases h : y 1 = v
        · exact ⟨1, by decide, h⟩
        · exact ⟨3, by decide, by omega⟩
      · intro t ht; rcases hfin4 t with rfl | rfl | rfl | rfl <;> simp at ht <;> omega
      · by_cases h : y 0 = v
        · exact ⟨0, by decide, h⟩
        · exact ⟨2, by decide, by omega⟩

private lemma good_eq_goodVal {n : ℕ} (x : Fin 9 → Fin (n + 1)) :
    good x = goodVal (fun i => (x i : ℕ)) := by
  rw [Bool.eq_iff_iff]
  unfold good goodVal
  rw [decide_eq_true_iff]
  have hget : ∀ (i : ℕ) (hi : i < 6) (t : Fin 4),
      OMA.S_oeis_a250392.get x (i + t.val) = (x ⟨i + t.val, by omega⟩ : ℕ) := by
    intro i hi t
    unfold OMA.S_oeis_a250392.get
    exact dif_pos (by omega)
  have hwin : ∀ (i : ℕ) (hi : i < 6),
      (¬ ∃ S ∈ (Finset.univ : Finset (Fin 4)).powersetCard 2, ∃ v < n + 1,
        (∀ t ∈ S, OMA.S_oeis_a250392.get x (i + t) ≤ v) ∧
        (∃ t ∈ S, OMA.S_oeis_a250392.get x (i + t) = v) ∧
        (∀ t ∉ S, v ≤ OMA.S_oeis_a250392.get x (i + t)) ∧
        (∃ t ∉ S, OMA.S_oeis_a250392.get x (i + t) = v)) ↔
      good4 (x ⟨i, by omega⟩ : ℕ) (x ⟨i + 1, by omega⟩ : ℕ)
        (x ⟨i + 2, by omega⟩ : ℕ) (x ⟨i + 3, by omega⟩ : ℕ) = true := by
    intro i hi
    have hcongr := bad4_iff (n := n) (fun t : Fin 4 => OMA.S_oeis_a250392.get x (i + t.val))
      (fun t => by rw [hget i hi t]; exact (x ⟨i + t.val, by omega⟩).isLt)
    rw [hcongr]
    simp only [good4, bne_iff_ne, ne_eq, hget i hi]
    rfl
  constructor
  · intro h
    simp only [Bool.and_eq_true]
    exact ⟨⟨⟨⟨⟨(hwin 0 (by omega)).1 (h 0 (by omega)),
               (hwin 1 (by omega)).1 (h 1 (by omega))⟩,
               (hwin 2 (by omega)).1 (h 2 (by omega))⟩,
               (hwin 3 (by omega)).1 (h 3 (by omega))⟩,
               (hwin 4 (by omega)).1 (h 4 (by omega))⟩,
               (hwin 5 (by omega)).1 (h 5 (by omega))⟩
  · intro h i hi
    simp only [Bool.and_eq_true] at h
    rcases h with ⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩
    interval_cases i
    · exact (hwin 0 (by omega)).2 h0
    · exact (hwin 1 (by omega)).2 h1
    · exact (hwin 2 (by omega)).2 h2
    · exact (hwin 3 (by omega)).2 h3
    · exact (hwin 4 (by omega)).2 h4
    · exact (hwin 5 (by omega)).2 h5

private lemma good4_strictMono_fin {k m : ℕ} {f : Fin k → Fin m} (hf : StrictMono f)
    (a b c d : Fin k) :
    good4 (f a : ℕ) (f b : ℕ) (f c : ℕ) (f d : ℕ) = good4 (a : ℕ) (b : ℕ) (c : ℕ) (d : ℕ) := by
  have hg : StrictMono (fun i : Fin k => (f i).val) := fun _ _ h => hf h
  have hv : StrictMono (Fin.val : Fin k → ℕ) := fun _ _ h => h
  have hmin : ∀ u v : Fin k, min (f u).val (f v).val = (f (min u v)).val := fun u v =>
    (hg.monotone.map_min (a := u) (b := v)).symm
  have hmax : ∀ u v : Fin k, max (f u).val (f v).val = (f (max u v)).val := fun u v =>
    (hg.monotone.map_max (a := u) (b := v)).symm
  have hminV : ∀ u v : Fin k, (min u v).val = min u.val v.val := fun u v =>
    hv.monotone.map_min (a := u) (b := v)
  have hmaxV : ∀ u v : Fin k, (max u v).val = max u.val v.val := fun u v =>
    hv.monotone.map_max (a := u) (b := v)
  rw [Bool.eq_iff_iff]
  simp only [good4, bne_iff_ne, ne_eq, hmin, hmax, hg.injective.ne_iff, Fin.ext_iff, hminV, hmaxV]

private lemma goodVal_strictMono_fin {k m : ℕ} {f : Fin k → Fin m} (hf : StrictMono f)
    (y : Fin 9 → Fin k) :
    goodVal (fun i => (f (y i) : ℕ)) = goodVal (fun i => (y i : ℕ)) := by
  unfold goodVal
  simp only [good4_strictMono_fin hf]

/-! ### 2. Binomial decomposition by image cardinality -/

/-- Valid surjective arrays `Fin 9 → Fin k`. -/
noncomputable def surjGood (k : ℕ) : Finset (Fin 9 → Fin k) := by
  classical
  exact Finset.univ.filter fun y =>
    Function.Surjective y ∧ goodVal (fun i => (y i : ℕ)) = true

/-- Number of valid surjective arrays `Fin 9 → Fin k`. -/
noncomputable def c (k : ℕ) : ℕ := (surjGood k).card

private lemma card_fiber_image_eq_c {n : ℕ} (s : Finset (Fin (n + 1))) :
    ((Finset.univ : Finset (Fin 9 → Fin (n + 1))).filter
      (fun x => good x = true ∧ Finset.univ.image x = s)).card = c s.card := by
  classical
  unfold c surjGood
  let e : Fin s.card ≃o s := s.orderIsoOfFin rfl
  let f : Fin s.card → Fin (n + 1) := fun j => (e j : Fin (n + 1))
  have hf : StrictMono f := fun u v huv => e.strictMono huv
  refine Finset.card_bij'
    (fun x hx => fun i => e.symm ⟨x i, by
      have him : Finset.univ.image x = s := (Finset.mem_filter.1 hx).2.2
      rw [← him]
      exact Finset.mem_image_of_mem x (Finset.mem_univ i)⟩)
    (fun y _ => fun i => f (y i))
    ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    obtain ⟨hgood, him⟩ := hx
    refine ⟨?_, ?_⟩
    · intro j
      have hmem : (e j : Fin (n + 1)) ∈ Finset.univ.image x := by rw [him]; exact (e j).2
      obtain ⟨i, _, hi⟩ := Finset.mem_image.1 hmem
      refine ⟨i, ?_⟩
      apply e.injective
      apply Subtype.ext
      simpa using hi
    · have hcomp : (fun i => (x i : ℕ)) = (fun i => (f (e.symm ⟨x i, by
          rw [← him]; exact Finset.mem_image_of_mem x (Finset.mem_univ i)⟩) : ℕ)) := by
        funext i
        simp [f]
      rw [good_eq_goodVal, hcomp, goodVal_strictMono_fin hf] at hgood
      exact hgood
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    obtain ⟨hsurj, hgood⟩ := hy
    refine ⟨?_, ?_⟩
    · rw [good_eq_goodVal, goodVal_strictMono_fin hf]
      exact hgood
    · ext a
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, rfl⟩
        exact (e (y i)).2
      · intro ha
        obtain ⟨i, hi⟩ := hsurj (e.symm ⟨a, ha⟩)
        exact ⟨i, by simp [f, hi]⟩
  · intro x hx
    funext i
    simp [f]
  · intro y hy
    funext i
    apply e.injective
    apply Subtype.ext
    simp [f]

private lemma card_good_eq_sum_choose (n : ℕ) :
    ((Finset.univ : Finset (Fin 9 → Fin (n + 1))).filter (fun x => good x)).card =
      ∑ k ∈ Finset.range 10, c k * (n + 1).choose k := by
  classical
  let T : Finset (Finset (Fin (n + 1))) :=
    (Finset.univ : Finset (Fin (n + 1))).powerset.filter (fun s => s.card < 10)
  have hmap : ∀ x ∈ (Finset.univ : Finset (Fin 9 → Fin (n + 1))).filter (fun x => good x),
      Finset.univ.image x ∈ T := by
    intro x _
    simp only [T, Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and]
    have hle : (Finset.univ.image x).card ≤ (Finset.univ : Finset (Fin 9)).card :=
      Finset.card_image_le
    simp only [Finset.card_univ, Fintype.card_fin] at hle
    omega
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  have hfib : ∀ s ∈ T,
      (((Finset.univ : Finset (Fin 9 → Fin (n + 1))).filter (fun x => good x)).filter
        (fun x => Finset.univ.image x = s)).card = c s.card := by
    intro s _
    rw [Finset.filter_filter]
    exact card_fiber_image_eq_c s
  rw [Finset.sum_congr rfl hfib]
  have hT : T = (Finset.range 10).biUnion
      (fun k => (Finset.univ : Finset (Fin (n + 1))).powersetCard k) := by
    ext s
    simp only [T, Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and,
      Finset.mem_biUnion, Finset.mem_range, Finset.mem_powersetCard]
    exact ⟨fun h => ⟨s.card, h, rfl⟩, fun ⟨_, hk, hs⟩ => hs ▸ hk⟩
  rw [hT, Finset.sum_biUnion]
  · refine Finset.sum_congr rfl fun k _ => ?_
    have hconst : ∑ s ∈ (Finset.univ : Finset (Fin (n + 1))).powersetCard k, c s.card =
        ∑ _s ∈ (Finset.univ : Finset (Fin (n + 1))).powersetCard k, c k :=
      Finset.sum_congr rfl fun s hs => by rw [(Finset.mem_powersetCard.1 hs).2]
    rw [hconst, Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
        smul_eq_mul, mul_comm]
  · intro i _ j _ hij
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro s hsi hsj
    exact hij ((Finset.mem_powersetCard.1 hsi).2.symm.trans (Finset.mem_powersetCard.1 hsj).2)

/-! ### 3. Boundary coefficients `c 0`, `c 1`, and `c 9` -/

private lemma c_zero : c 0 = 0 := by
  classical
  unfold c surjGood
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro y _
  exact Fin.elim0 (y 0)

private lemma c_one : c 1 = 0 := by
  classical
  unfold c surjGood
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro y _ hy
  have h0 : ∀ i : Fin 9, (y i : ℕ) = 0 := fun i => Nat.lt_one_iff.1 (y i).isLt
  have hgood := hy.2
  simp only [goodVal, h0] at hgood
  revert hgood
  decide

private lemma c_nine : c 9 = 362880 := by
  classical
  unfold c surjGood
  have hfilt : (Finset.univ.filter fun y : Fin 9 → Fin 9 =>
      Function.Surjective y ∧ goodVal (fun i => (y i : ℕ)) = true) =
      Finset.univ.filter Function.Bijective := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro ⟨hsurj, _⟩
      exact ⟨Finite.injective_iff_surjective.2 hsurj, hsurj⟩
    · intro hbij
      refine ⟨hbij.2, ?_⟩
      have hinj : Function.Injective y := hbij.1
      have h4 : ∀ i j k l : Fin 9, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
          good4 (y i : ℕ) (y j : ℕ) (y k : ℕ) (y l : ℕ) = true := by
        intro i j k l hij hik hil hjk hjl hkl
        have h1 : (y i : ℕ) ≠ (y j : ℕ) := fun h => hij (hinj (Fin.ext h))
        have h2 : (y i : ℕ) ≠ (y k : ℕ) := fun h => hik (hinj (Fin.ext h))
        have h3 : (y i : ℕ) ≠ (y l : ℕ) := fun h => hil (hinj (Fin.ext h))
        have h4' : (y j : ℕ) ≠ (y k : ℕ) := fun h => hjk (hinj (Fin.ext h))
        have h5 : (y j : ℕ) ≠ (y l : ℕ) := fun h => hjl (hinj (Fin.ext h))
        have h6 : (y k : ℕ) ≠ (y l : ℕ) := fun h => hkl (hinj (Fin.ext h))
        simp only [good4, bne_iff_ne, ne_eq]
        omega
      unfold goodVal
      simp only [Bool.and_eq_true]
      refine ⟨⟨⟨⟨⟨h4 0 1 2 3 ?_ ?_ ?_ ?_ ?_ ?_, h4 1 2 3 4 ?_ ?_ ?_ ?_ ?_ ?_⟩,
        h4 2 3 4 5 ?_ ?_ ?_ ?_ ?_ ?_⟩, h4 3 4 5 6 ?_ ?_ ?_ ?_ ?_ ?_⟩,
        h4 4 5 6 7 ?_ ?_ ?_ ?_ ?_ ?_⟩, h4 5 6 7 8 ?_ ?_ ?_ ?_ ?_ ?_⟩ <;> decide
  rw [hfilt]
  have hbij : (Finset.univ.filter (fun y : Fin 9 → Fin 9 => Function.Bijective y)).card =
      (Finset.univ : Finset (Equiv.Perm (Fin 9))).card := by
    refine Finset.card_bij' (fun y hy => Equiv.ofBijective y (Finset.mem_filter.1 hy).2)
      (fun e _ => (e : Fin 9 → Fin 9)) ?_ ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro e _; exact Finset.mem_filter.2 ⟨Finset.mem_univ _, e.bijective⟩
    · intro _ _; rfl
    · intro e _; ext i; rfl
  rw [hbij, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  decide

/-! ### 4. Sliding-window dynamic program for `a 1, ..., a 7` -/

/-- Number of valid length-`(k + 3)` arrays over `Fin m` ending in `(q, r, s)`. -/
def countEnd (m : ℕ) : ℕ → Fin m → Fin m → Fin m → ℕ
  | 0, _, _, _ => 1
  | k + 1, q, r, s =>
    ∑ p : Fin m, if good4 p.val q.val r.val s.val then countEnd m k p q r else 0

/-- Valid length-`(k + 3)` arrays over `Fin m`. -/
def validArr (m k : ℕ) : Finset (Fin (k + 3) → Fin m) :=
  Finset.univ.filter fun x =>
    ∀ i : Fin k, good4 (x ⟨i.val, by omega⟩).val (x ⟨i.val + 1, by omega⟩).val
      (x ⟨i.val + 2, by omega⟩).val (x ⟨i.val + 3, by omega⟩).val = true

private lemma countEnd_eq_card (m : ℕ) : ∀ k (q r s : Fin m),
    countEnd m k q r s =
      ((validArr m k).filter fun x =>
        x ⟨k, by omega⟩ = q ∧ x ⟨k + 1, by omega⟩ = r ∧ x ⟨k + 2, by omega⟩ = s).card
  | 0, q, r, s => by
    symm
    refine Finset.card_eq_one.2 ⟨fun i : Fin 3 =>
      if i.val = 0 then q else if i.val = 1 then r else s, ?_⟩
    ext x
    simp only [validArr, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨_, h0, h1, h2⟩
      funext i
      fin_cases i
      · simpa using h0
      · simpa using h1
      · simpa using h2
    · rintro rfl
      refine ⟨fun i => Fin.elim0 i, rfl, rfl, rfl⟩
  | k + 1, q, r, s => by
    simp only [countEnd]
    rw [Finset.card_eq_sum_card_fiberwise (f := fun x : Fin (k + 4) → Fin m => x ⟨k, by omega⟩)
      (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.filter_filter]
    by_cases h4 : good4 p.val q.val r.val s.val = true
    · rw [if_pos h4, countEnd_eq_card m k p q r]
      symm
      refine Finset.card_bij'
        (fun x _ => fun i : Fin (k + 3) => x ⟨i.val, by omega⟩)
        (fun y _ => fun i : Fin (k + 4) => if h : i.val < k + 3 then y ⟨i.val, h⟩ else s)
        ?_ ?_ ?_ ?_
      · intro x hx
        simp only [validArr, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        obtain ⟨hval, ⟨hq, hr, _⟩, hp⟩ := hx
        exact ⟨fun i => hval ⟨i.val, by omega⟩, hp, hq, hr⟩
      · intro y hy
        simp only [validArr, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
        obtain ⟨hval, hp, hq, hr⟩ := hy
        refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_⟩
        · intro i
          by_cases hi : i.val < k
          · have h1 : i.val < k + 3 := by omega
            have h2 : i.val + 1 < k + 3 := by omega
            have h3 : i.val + 2 < k + 3 := by omega
            have h4' : i.val + 3 < k + 3 := by omega
            simp only [dif_pos h1, dif_pos h2, dif_pos h3, dif_pos h4']
            exact hval ⟨i.val, hi⟩
          · have hik : i.val = k := by omega
            have h1 : i.val < k + 3 := by omega
            have h2 : i.val + 1 < k + 3 := by omega
            have h3 : i.val + 2 < k + 3 := by omega
            have h4' : ¬ (i.val + 3 < k + 3) := by omega
            simp only [dif_pos h1, dif_pos h2, dif_pos h3, dif_neg h4']
            have e0 : (⟨i.val, h1⟩ : Fin (k + 3)) = ⟨k, by omega⟩ := Fin.ext hik
            have e1 : (⟨i.val + 1, h2⟩ : Fin (k + 3)) = ⟨k + 1, by omega⟩ := Fin.ext (by dsimp; omega)
            have e2 : (⟨i.val + 2, h3⟩ : Fin (k + 3)) = ⟨k + 2, by omega⟩ := Fin.ext (by dsimp; omega)
            rw [e0, e1, e2, hp, hq, hr]
            exact h4
        · simp only [dif_pos (show k + 1 < k + 3 by omega)]; exact hq
        · simp only [dif_pos (show k + 2 < k + 3 by omega)]; exact hr
        · simp only [dif_neg (show ¬ (k + 3 < k + 3) by omega)]
        · simp only [dif_pos (show k < k + 3 by omega)]; exact hp
      · intro x hx
        simp only [validArr, Finset.mem_filter, Finset.mem_univ, true_and] at hx
        obtain ⟨_, ⟨_, _, hs⟩, _⟩ := hx
        funext i
        by_cases hi : i.val < k + 3
        · simp [dif_pos hi]
        · simp only [dif_neg hi]
          have hi3 : i = ⟨k + 3, by omega⟩ := Fin.ext (by dsimp; omega)
          rw [hi3, hs]
      · intro y _
        funext i
        simp
    · rw [if_neg h4]
      symm
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro x hx
      simp only [validArr, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      rintro ⟨⟨hq, hr, hs⟩, hp⟩
      have hlast := hx ⟨k, by omega⟩
      simp only [hp, hq, hr, hs] at hlast
      exact h4 hlast

private lemma card_good_eq_sum_countEnd (n : ℕ) :
    ((Finset.univ : Finset (Fin 9 → Fin (n + 1))).filter (fun x => good x)).card =
      ∑ q : Fin (n + 1), ∑ r : Fin (n + 1), ∑ s : Fin (n + 1), countEnd (n + 1) 6 q r s := by
  have hset : (Finset.univ : Finset (Fin 9 → Fin (n + 1))).filter (fun x => good x) =
      validArr (n + 1) 6 := by
    ext x
    simp only [validArr, Finset.mem_filter, Finset.mem_univ, true_and, good_eq_goodVal, goodVal,
      Bool.and_eq_true]
    constructor
    · rintro ⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩ i
      fin_cases i
      · exact h0
      · exact h1
      · exact h2
      · exact h3
      · exact h4
      · exact h5
    · intro h
      exact ⟨⟨⟨⟨⟨h 0, h 1⟩, h 2⟩, h 3⟩, h 4⟩, h 5⟩
  rw [hset]
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun x : Fin 9 → Fin (n + 1) => ((x 6, x 7), x 8))
    (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun r _ =>
    Finset.sum_congr rfl fun s _ => ?_
  rw [countEnd_eq_card (n + 1) 6 q r s]
  congr 1
  ext x
  simp only [Finset.mem_filter, Prod.mk.injEq, and_assoc]
  rfl

/-- Safe list lookup for fast kernel DP evaluation. -/
def listGet {α : Type*} : List α → ℕ → α → α
  | [], _, d => d
  | x :: _, 0, _ => x
  | _ :: xs, n + 1, d => listGet xs n d

/-- 3D table lookup. -/
def get3 (t : List (List (List ℕ))) (p q r : ℕ) : ℕ :=
  listGet (listGet (listGet t p []) q []) r 0

/-- Tail-recursive sum over `0 .. m - 1`. -/
def sumRangeGo (f : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, acc => acc
  | n + 1, acc => sumRangeGo f n (acc + f n)

/-- Sum of `f 0 + ... + f (m - 1)`. -/
def sumRange (m : ℕ) (f : ℕ → ℕ) : ℕ :=
  sumRangeGo f m 0

/-- Initial all-ones `m × m × m` table. -/
def dpInit (m : ℕ) : List (List (List ℕ)) :=
  List.replicate m (List.replicate m (List.replicate m 1))

/-- One sliding-window DP transition step. -/
def dpStep (m : ℕ) (t : List (List (List ℕ))) : List (List (List ℕ)) :=
  (List.range m).map fun q =>
    (List.range m).map fun r =>
      (List.range m).map fun s =>
        sumRange m fun p => if good4 p q r s then get3 t p q r else 0

/-- `k`-step DP table over `Fin m`. -/
def dpTable (m : ℕ) : ℕ → List (List (List ℕ))
  | 0 => dpInit m
  | k + 1 => dpStep m (dpTable m k)

/-- Total count extracted from `dpTable m k`. -/
def dpSum (m k : ℕ) : ℕ :=
  let t := dpTable m k
  sumRange m fun q => sumRange m fun r => sumRange m fun s => get3 t q r s

private lemma listGet_replicate {α : Type*} (x d : α) :
    ∀ m i, i < m → listGet (List.replicate m x) i d = x
  | 0, _, hi => absurd hi (Nat.not_lt_zero _)
  | _ + 1, 0, _ => rfl
  | m + 1, i + 1, hi => listGet_replicate x d m i (Nat.lt_of_succ_lt_succ hi)

private lemma listGet_append_left {α : Type*} :
    ∀ (l1 l2 : List α) (i : ℕ) (d : α), i < l1.length → listGet (l1 ++ l2) i d = listGet l1 i d
  | [], _, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | _ :: _, _, 0, _, _ => rfl
  | _ :: xs, l2, i + 1, d, hi =>
    listGet_append_left xs l2 i d (Nat.lt_of_succ_lt_succ hi)

private lemma listGet_append_right {α : Type*} :
    ∀ (l1 l2 : List α) (i : ℕ) (d : α),
      l1.length ≤ i → listGet (l1 ++ l2) i d = listGet l2 (i - l1.length) d
  | [], _, _, _, _ => rfl
  | _ :: _, _, 0, _, hi => absurd hi (by simp)
  | _ :: xs, l2, i + 1, d, hi => by
    simp only [List.cons_append, listGet, List.length_cons, Nat.add_sub_add_right]
    exact listGet_append_right xs l2 i d (Nat.le_of_succ_le_succ hi)

private lemma listGet_map_range {α : Type*} (f : ℕ → α) (d : α) :
    ∀ m i, i < m → listGet ((List.range m).map f) i d = f i
  | 0, _, hi => absurd hi (Nat.not_lt_zero _)
  | m + 1, i, hi => by
    rw [List.range_succ, List.map_append, List.map_singleton]
    by_cases him : i < m
    · rw [listGet_append_left _ _ _ _ (by simp [him])]
      exact listGet_map_range f d m i him
    · have heq : i = m := by omega
      rw [listGet_append_right _ _ _ _ (by simp [heq])]
      simp [heq, listGet]

private lemma sumRangeGo_eq (f : ℕ → ℕ) :
    ∀ m acc, sumRangeGo f m acc = acc + ∑ i ∈ Finset.range m, f i
  | 0, acc => by simp [sumRangeGo]
  | m + 1, acc => by
    rw [sumRangeGo, sumRangeGo_eq f m (acc + f m), Finset.sum_range_succ]
    omega

private lemma sumRange_eq_sum_fin (m : ℕ) (f : ℕ → ℕ) :
    sumRange m f = ∑ i : Fin m, f i.val := by
  rw [sumRange, sumRangeGo_eq, zero_add, Fin.sum_univ_eq_sum_range]

private lemma get3_dpTable (m : ℕ) :
    ∀ k (p q r : Fin m), get3 (dpTable m k) p.val q.val r.val = countEnd m k p q r
  | 0, p, q, r => by
    simp only [dpTable, dpInit, get3, countEnd,
      listGet_replicate _ _ m p.val p.isLt,
      listGet_replicate _ _ m q.val q.isLt,
      listGet_replicate _ _ m r.val r.isLt]
  | k + 1, q, r, s => by
    change listGet (listGet (listGet (dpStep m (dpTable m k)) q.val []) r.val []) s.val 0 =
      countEnd m (k + 1) q r s
    simp only [dpStep, countEnd,
      listGet_map_range _ _ m q.val q.isLt,
      listGet_map_range _ _ m r.val r.isLt,
      listGet_map_range _ _ m s.val s.isLt,
      sumRange_eq_sum_fin]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [get3_dpTable m k p q r]

private lemma a_eq_dpSum (n : ℕ) : a n = (dpSum (n + 1) 6 : ℤ) := by
  unfold a
  rw [card_good_eq_sum_countEnd]
  simp only [dpSum, sumRange_eq_sum_fin, get3_dpTable]

/-! ### 5. Exact values and closed-form binomial expansion -/

private lemma dpSum_2 : dpSum 2 6 = 6 := by decide +kernel
private lemma dpSum_3 : dpSum 3 6 = 966 := by decide +kernel
private lemma dpSum_4 : dpSum 4 6 = 26578 := by decide +kernel
private lemma dpSum_5 : dpSum 5 6 = 309452 := by decide +kernel
private lemma dpSum_6 : dpSum 6 6 = 2160160 := by decide +kernel
private lemma dpSum_7 : dpSum 7 6 = 10755158 := by decide +kernel
set_option maxHeartbeats 2000000 in
private lemma dpSum_8 : dpSum 8 6 = 42158796 := by decide +kernel

/-- Closed-form polynomial expression for `a n`. -/
def polyNat (n : ℕ) : ℕ :=
  6 * (n + 1).choose 2 +
  948 * (n + 1).choose 3 +
  22750 * (n + 1).choose 4 +
  186162 * (n + 1).choose 5 +
  682888 * (n + 1).choose 6 +
  1235984 * (n + 1).choose 7 +
  1079232 * (n + 1).choose 8 +
  362880 * (n + 1).choose 9

private lemma choose_small :
    (2 : ℕ).choose 2 = 1 ∧ (2 : ℕ).choose 3 = 0 ∧ (2 : ℕ).choose 4 = 0 ∧ (2 : ℕ).choose 5 = 0 ∧
    (2 : ℕ).choose 6 = 0 ∧ (2 : ℕ).choose 7 = 0 ∧ (2 : ℕ).choose 8 = 0 ∧ (2 : ℕ).choose 9 = 0 ∧
    (3 : ℕ).choose 2 = 3 ∧ (3 : ℕ).choose 3 = 1 ∧ (3 : ℕ).choose 4 = 0 ∧ (3 : ℕ).choose 5 = 0 ∧
    (3 : ℕ).choose 6 = 0 ∧ (3 : ℕ).choose 7 = 0 ∧ (3 : ℕ).choose 8 = 0 ∧ (3 : ℕ).choose 9 = 0 ∧
    (4 : ℕ).choose 2 = 6 ∧ (4 : ℕ).choose 3 = 4 ∧ (4 : ℕ).choose 4 = 1 ∧ (4 : ℕ).choose 5 = 0 ∧
    (4 : ℕ).choose 6 = 0 ∧ (4 : ℕ).choose 7 = 0 ∧ (4 : ℕ).choose 8 = 0 ∧ (4 : ℕ).choose 9 = 0 ∧
    (5 : ℕ).choose 2 = 10 ∧ (5 : ℕ).choose 3 = 10 ∧ (5 : ℕ).choose 4 = 5 ∧ (5 : ℕ).choose 5 = 1 ∧
    (5 : ℕ).choose 6 = 0 ∧ (5 : ℕ).choose 7 = 0 ∧ (5 : ℕ).choose 8 = 0 ∧ (5 : ℕ).choose 9 = 0 ∧
    (6 : ℕ).choose 2 = 15 ∧ (6 : ℕ).choose 3 = 20 ∧ (6 : ℕ).choose 4 = 15 ∧ (6 : ℕ).choose 5 = 6 ∧
    (6 : ℕ).choose 6 = 1 ∧ (6 : ℕ).choose 7 = 0 ∧ (6 : ℕ).choose 8 = 0 ∧ (6 : ℕ).choose 9 = 0 ∧
    (7 : ℕ).choose 2 = 21 ∧ (7 : ℕ).choose 3 = 35 ∧ (7 : ℕ).choose 4 = 35 ∧ (7 : ℕ).choose 5 = 21 ∧
    (7 : ℕ).choose 6 = 7 ∧ (7 : ℕ).choose 7 = 1 ∧ (7 : ℕ).choose 8 = 0 ∧ (7 : ℕ).choose 9 = 0 ∧
    (8 : ℕ).choose 2 = 28 ∧ (8 : ℕ).choose 3 = 56 ∧ (8 : ℕ).choose 4 = 70 ∧ (8 : ℕ).choose 5 = 56 ∧
    (8 : ℕ).choose 6 = 28 ∧ (8 : ℕ).choose 7 = 8 ∧ (8 : ℕ).choose 8 = 1 ∧ (8 : ℕ).choose 9 = 0 := by
  decide

private lemma a_eq_polyNat (n : ℕ) : a n = (polyNat n : ℤ) := by
  have hgen : ∀ m : ℕ, ((a m : ℤ)) =
      (c 2 * (m + 1).choose 2 + c 3 * (m + 1).choose 3 + c 4 * (m + 1).choose 4 +
       c 5 * (m + 1).choose 5 + c 6 * (m + 1).choose 6 + c 7 * (m + 1).choose 7 +
       c 8 * (m + 1).choose 8 + 362880 * (m + 1).choose 9 : ℕ) := by
    intro m
    unfold a
    rw [card_good_eq_sum_choose]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, c_zero, c_one, c_nine, zero_mul,
      zero_add]
  have hgenN : ∀ m : ℕ, dpSum (m + 1) 6 =
      c 2 * (m + 1).choose 2 + c 3 * (m + 1).choose 3 + c 4 * (m + 1).choose 4 +
      c 5 * (m + 1).choose 5 + c 6 * (m + 1).choose 6 + c 7 * (m + 1).choose 7 +
      c 8 * (m + 1).choose 8 + 362880 * (m + 1).choose 9 := by
    intro m
    have := hgen m
    rw [a_eq_dpSum m] at this
    exact Int.ofNat.inj this
  have h1 := hgenN 1; rw [dpSum_2] at h1
  have h2 := hgenN 2; rw [dpSum_3] at h2
  have h3 := hgenN 3; rw [dpSum_4] at h3
  have h4 := hgenN 4; rw [dpSum_5] at h4
  have h5 := hgenN 5; rw [dpSum_6] at h5
  have h6 := hgenN 6; rw [dpSum_7] at h6
  have h7 := hgenN 7; rw [dpSum_8] at h7
  simp only [Nat.reduceAdd, choose_small] at h1 h2 h3 h4 h5 h6 h7
  have hc2 : c 2 = 6 := by omega
  have hc3 : c 3 = 948 := by omega
  have hc4 : c 4 = 22750 := by omega
  have hc5 : c 5 = 186162 := by omega
  have hc6 : c 6 = 682888 := by omega
  have hc7 : c 7 = 1235984 := by omega
  have hc8 : c 8 = 1079232 := by omega
  have hn := hgen n
  rw [hc2, hc3, hc4, hc5, hc6, hc7, hc8] at hn
  exact hn

private lemma a_eq_poly (n : ℕ) :
    (a n : ℚ) =
      6 * ((n + 1).choose 2 : ℚ) +
      948 * ((n + 1).choose 3 : ℚ) +
      22750 * ((n + 1).choose 4 : ℚ) +
      186162 * ((n + 1).choose 5 : ℚ) +
      682888 * ((n + 1).choose 6 : ℚ) +
      1235984 * ((n + 1).choose 7 : ℚ) +
      1079232 * ((n + 1).choose 8 : ℚ) +
      362880 * ((n + 1).choose 9 : ℚ) := by
  rw [a_eq_polyNat]
  unfold polyNat
  push_cast
  rfl

/-! ### 6. Forward differences, recurrence, and generating function -/

/-- Forward difference operator on `ℕ → ℚ`. -/
def diff (f : ℕ → ℚ) : ℕ → ℚ := fun n => f (n + 1) - f n

private lemma diff_zero_fn : diff (fun _ => (0 : ℚ)) = fun _ => 0 := by
  funext n; simp [diff]

private lemma diff_iter_zero_fn : ∀ m, diff^[m] (fun _ => (0 : ℚ)) = fun _ => 0
  | 0 => rfl
  | m + 1 => by rw [Function.iterate_succ_apply', diff_iter_zero_fn m, diff_zero_fn]

private lemma diff_choose_zero : diff (fun n => ((n + 1).choose 0 : ℚ)) = fun _ => 0 := by
  funext n; simp [diff]

private lemma diff_choose_succ (k : ℕ) :
    diff (fun n => ((n + 1).choose (k + 1) : ℚ)) = fun n => ((n + 1).choose k : ℚ) := by
  funext n
  simp only [diff, Nat.choose_succ_succ, Nat.cast_add]
  ring

private lemma diff_iter_choose_eq_zero :
    ∀ k, diff^[k + 1] (fun n => ((n + 1).choose k : ℚ)) = fun _ => 0
  | 0 => diff_choose_zero
  | k + 1 => by
    rw [Function.iterate_succ_apply, diff_choose_succ]
    exact diff_iter_choose_eq_zero k

private lemma diff_ten_choose (k : ℕ) (hk : k ≤ 9) :
    diff^[10] (fun n => ((n + 1).choose k : ℚ)) = fun _ => 0 := by
  have hsplit : 10 = (9 - k) + (k + 1) := by omega
  rw [hsplit, Function.iterate_add_apply, diff_iter_choose_eq_zero k, diff_iter_zero_fn]

private lemma diff_five_expand (f : ℕ → ℚ) (n : ℕ) :
    diff^[5] f n =
      f (n + 5) - 5 * f (n + 4) + 10 * f (n + 3) - 10 * f (n + 2) + 5 * f (n + 1) - f n := by
  simp only [Function.iterate_succ_apply', Function.iterate_zero, id_eq, diff]
  ring

private lemma diff_ten_expand (f : ℕ → ℚ) (n : ℕ) :
    diff^[10] f n =
      f (n + 10) - 10 * f (n + 9) + 45 * f (n + 8) - 120 * f (n + 7) + 210 * f (n + 6) -
      252 * f (n + 5) + 210 * f (n + 4) - 120 * f (n + 3) + 45 * f (n + 2) -
      10 * f (n + 1) + f n := by
  rw [show (10 : ℕ) = 5 + 5 by rfl, Function.iterate_add_apply, diff_five_expand]
  simp only [diff_five_expand]
  ring

private lemma diff_add (f g : ℕ → ℚ) :
    diff (fun n => f n + g n) = fun n => diff f n + diff g n := by
  funext n; simp only [diff]; ring

private lemma diff_const_mul (r : ℚ) (f : ℕ → ℚ) :
    diff (fun n => r * f n) = fun n => r * diff f n := by
  funext n; simp only [diff]; ring

private lemma diff_iter_add : ∀ m (f g : ℕ → ℚ),
    diff^[m] (fun n => f n + g n) = fun n => diff^[m] f n + diff^[m] g n
  | 0, _, _ => rfl
  | m + 1, f, g => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        Function.iterate_succ_apply', diff_iter_add m f g, diff_add]

private lemma diff_iter_const_mul : ∀ m (r : ℚ) (f : ℕ → ℚ),
    diff^[m] (fun n => r * f n) = fun n => r * diff^[m] f n
  | 0, _, _ => rfl
  | m + 1, r, f => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        diff_iter_const_mul m r f, diff_const_mul]

private lemma a_rec_all (m : ℕ) :
    (a (m + 10) : ℚ) - 10 * a (m + 9) + 45 * a (m + 8) - 120 * a (m + 7) + 210 * a (m + 6) -
    252 * a (m + 5) + 210 * a (m + 4) - 120 * a (m + 3) + 45 * a (m + 2) -
    10 * a (m + 1) + a m = 0 := by
  rw [← diff_ten_expand (fun n => (a n : ℚ)) m]
  have hf : (fun n => (a n : ℚ)) = fun n =>
      6 * ((n + 1).choose 2 : ℚ) +
      948 * ((n + 1).choose 3 : ℚ) +
      22750 * ((n + 1).choose 4 : ℚ) +
      186162 * ((n + 1).choose 5 : ℚ) +
      682888 * ((n + 1).choose 6 : ℚ) +
      1235984 * ((n + 1).choose 7 : ℚ) +
      1079232 * ((n + 1).choose 8 : ℚ) +
      362880 * ((n + 1).choose 9 : ℚ) := funext a_eq_poly
  rw [hf]
  simp only [diff_iter_add, diff_iter_const_mul,
    diff_ten_choose 2 (by omega), diff_ten_choose 3 (by omega),
    diff_ten_choose 4 (by omega), diff_ten_choose 5 (by omega),
    diff_ten_choose 6 (by omega), diff_ten_choose 7 (by omega),
    diff_ten_choose 8 (by omega), diff_ten_choose 9 (by omega)]
  norm_num

theorem recurrence (n : ℕ) (hn : 11 ≤ n) :
    (a n : ℚ) = 10 * a (n - 1) - 45 * a (n - 2) + 120 * a (n - 3) - 210 * a (n - 4) +
      252 * a (n - 5) - 210 * a (n - 6) + 120 * a (n - 7) - 45 * a (n - 8) +
      10 * a (n - 9) - a (n - 10) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 10 := ⟨n - 10, by omega⟩
  have h := a_rec_all m
  simp only [show m + 10 - 1 = m + 9 by omega, show m + 10 - 2 = m + 8 by omega,
    show m + 10 - 3 = m + 7 by omega, show m + 10 - 4 = m + 6 by omega,
    show m + 10 - 5 = m + 5 by omega, show m + 10 - 6 = m + 4 by omega,
    show m + 10 - 7 = m + 3 by omega, show m + 10 - 8 = m + 2 by omega,
    show m + 10 - 9 = m + 1 by omega, show m + 10 - 10 = m by omega]
  linarith

private lemma polyNat_vals :
    polyNat 0 = 0 ∧ polyNat 1 = 6 ∧ polyNat 2 = 966 ∧ polyNat 3 = 26578 ∧
    polyNat 4 = 309452 ∧ polyNat 5 = 2160160 ∧ polyNat 6 = 10755158 ∧
    polyNat 7 = 42158796 ∧ polyNat 8 = 138336744 ∧ polyNat 9 = 395723154 := by
  decide

open PowerSeries in
theorem gen_fun :
    PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 10 : PowerSeries ℚ) =
      2 * X * (3 + 453 * X + 8594 * X ^ 2 + 43211 * X ^ 3 + 73495 * X ^ 4 +
        45443 * X ^ 5 + 9692 * X ^ 6 + 549 * X ^ 7) := by
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9⟩ := polyNat_vals
  have ha0 : (a 0 : ℚ) = 0 := by rw [a_eq_polyNat, v0]; norm_num
  have ha1 : (a 1 : ℚ) = 6 := by rw [a_eq_polyNat, v1]; norm_num
  have ha2 : (a 2 : ℚ) = 966 := by rw [a_eq_polyNat, v2]; norm_num
  have ha3 : (a 3 : ℚ) = 26578 := by rw [a_eq_polyNat, v3]; norm_num
  have ha4 : (a 4 : ℚ) = 309452 := by rw [a_eq_polyNat, v4]; norm_num
  have ha5 : (a 5 : ℚ) = 2160160 := by rw [a_eq_polyNat, v5]; norm_num
  have ha6 : (a 6 : ℚ) = 10755158 := by rw [a_eq_polyNat, v6]; norm_num
  have ha7 : (a 7 : ℚ) = 42158796 := by rw [a_eq_polyNat, v7]; norm_num
  have ha8 : (a 8 : ℚ) = 138336744 := by rw [a_eq_polyNat, v8]; norm_num
  have ha9 : (a 9 : ℚ) = 395723154 := by rw [a_eq_polyNat, v9]; norm_num
  have hF : (fun n => if n < 1 then (0 : ℚ) else (a n : ℚ)) = fun n => (a n : ℚ) := by
    funext n
    cases n with
    | zero => simp [ha0]
    | succ n => simp
  rw [hF]
  have key : PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 10 : PowerSeries ℚ) =
      C 1 * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 0) -
      C 10 * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 1) +
      C 45 * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 2) -
      C 120 * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 3) +
      C 210 * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 4) -
      C 252 * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 5) +
      C 210 * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 6) -
      C 120 * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 7) +
      C 45 * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 8) -
      C 10 * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 9) +
      C 1 * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 10) := by
    simp only [map_one, map_ofNat]
    ring
  have hrhs : (2 * X * (3 + 453 * X + 8594 * X ^ 2 + 43211 * X ^ 3 + 73495 * X ^ 4 +
      45443 * X ^ 5 + 9692 * X ^ 6 + 549 * X ^ 7) : ℚ⟦X⟧) =
      C 6 * X ^ 1 + C 906 * X ^ 2 + C 17188 * X ^ 3 + C 86422 * X ^ 4 +
      C 146990 * X ^ 5 + C 90886 * X ^ 6 + C 19384 * X ^ 7 + C 1098 * X ^ 8 := by
    simp only [map_ofNat]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  by_cases hk : k < 10
  · interval_cases k <;> norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 10 := ⟨k - 10, by omega⟩
    have hr := a_rec_all j
    simp only [show 0 ≤ j + 10 by omega, show 1 ≤ j + 10 by omega,
      show 2 ≤ j + 10 by omega, show 3 ≤ j + 10 by omega,
      show 4 ≤ j + 10 by omega, show 5 ≤ j + 10 by omega,
      show 6 ≤ j + 10 by omega, show 7 ≤ j + 10 by omega,
      show 8 ≤ j + 10 by omega, show 9 ≤ j + 10 by omega,
      show 10 ≤ j + 10 by omega,
      show j + 10 - 0 = j + 10 by omega, show j + 10 - 1 = j + 9 by omega,
      show j + 10 - 2 = j + 8 by omega, show j + 10 - 3 = j + 7 by omega,
      show j + 10 - 4 = j + 6 by omega, show j + 10 - 5 = j + 5 by omega,
      show j + 10 - 6 = j + 4 by omega, show j + 10 - 7 = j + 3 by omega,
      show j + 10 - 8 = j + 2 by omega, show j + 10 - 9 = j + 1 by omega,
      show j + 10 - 10 = j by omega,
      show ¬ (j + 10 = 1) by omega, show ¬ (j + 10 = 2) by omega,
      show ¬ (j + 10 = 3) by omega, show ¬ (j + 10 = 4) by omega,
      show ¬ (j + 10 = 5) by omega, show ¬ (j + 10 = 6) by omega,
      show ¬ (j + 10 = 7) by omega, show ¬ (j + 10 = 8) by omega,
      if_true, if_false]
    linarith

end OMA.A250392

theorem OMA.solution : type_of% @OMA.S_oeis_a250392.main :=
  ⟨OMA.A250392.gen_fun, OMA.A250392.recurrence⟩
