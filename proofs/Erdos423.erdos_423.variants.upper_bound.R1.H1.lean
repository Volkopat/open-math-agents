import OMAReductions.R_Erdos423_erdos_423_variants_upper_bound_R1

/-!
# Convex Difference-Set Lower Bound for Erdős Problem 423

Proves `OMA.R_Erdos423_erdos_423_variants_upper_bound_R1.H1`: for any strictly increasing
sequence `a : ℕ → ℕ` (on indices `≥ 1`), the number of distinct consecutive block sums
of length at least 2 among `a 1, ..., a m` is at least `m ^ (1101 / 688 - η)` eventually.

The proof follows Cushman's convex difference-set bound `|A - A| ≫_η |A|^(1101/688 - η)`
via an elementary order-theoretic convex incidence bound (Ruzsa-Shakan-Solymosi-Szemerédi),
the popular-difference projection lemma, and integer-power energy bounds.
-/

open Finset BigOperators Filter

namespace Erdos423Cushman

/- ## Section 1: Basic Combinatorial Definitions and Identities -/

/-- A strictly increasing, strictly convex finite sequence of integers of length `n`. -/
structure ConvexSeq where
  n : ℕ
  val : ℕ → ℤ
  strictMono : ∀ i j, i < j → j < n → val i < val j
  strictConvex : ∀ i, i + 2 < n → val (i + 1) - val i < val (i + 2) - val (i + 1)

/-- The finite set of values of a `ConvexSeq`. -/
def ConvexSeq.toFinset (cs : ConvexSeq) : Finset ℤ :=
  (Finset.range cs.n).image cs.val

lemma ConvexSeq.card_toFinset (cs : ConvexSeq) : cs.toFinset.card = cs.n := by
  rw [ConvexSeq.toFinset, Finset.card_image_of_injOn, Finset.card_range]
  intro i hi j hj hij
  rw [Finset.coe_range, Set.mem_Iio] at hi hj
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact (cs.strictMono i j hlt hj).ne hij
  · exact (cs.strictMono j i hlt hi).ne hij.symm

lemma ConvexSeq.step_one_mono (cs : ConvexSeq) :
    ∀ i j, i < j → j + 1 < cs.n → cs.val (i + 1) - cs.val i < cs.val (j + 1) - cs.val j := by
  intro i j hij hjn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hij
  induction k with
  | zero =>
    simpa [Nat.add_assoc] using cs.strictConvex i (by omega)
  | succ k ih =>
    have h1 := ih (by omega) (by omega)
    have h2 := cs.strictConvex (i + k + 1) (by omega)
    have heq1 : i + (k + 1) + 1 = (i + k + 1) + 1 := by omega
    have heq2 : i + (k + 1) + 1 + 1 = (i + k + 1) + 2 := by omega
    rw [heq2, heq1]
    linarith

lemma ConvexSeq.step_h_mono (cs : ConvexSeq) (h : ℕ) (hh : 1 ≤ h) :
    ∀ i j, i < j → j + h < cs.n → cs.val (i + h) - cs.val i < cs.val (j + h) - cs.val j := by
  induction h with
  | zero => omega
  | succ h ih =>
    intro i j hij hjh
    rcases Nat.eq_zero_or_pos h with rfl | hhpos
    · exact cs.step_one_mono i j hij hjh
    · have h1 := ih hhpos i j hij (by omega)
      have h2 := cs.step_one_mono (i + h) (j + h) (by omega) (by omega)
      have he1 : i + (h + 1) = (i + h) + 1 := by omega
      have he2 : j + (h + 1) = (j + h) + 1 := by omega
      rw [he1, he2]
      linarith

/-- Difference set `A - B`. -/
def diffSet (A B : Finset ℤ) : Finset ℤ :=
  (A ×ˢ B).image (fun p => p.1 - p.2)

/-- Sumset `A + B`. -/
def sumSet (A B : Finset ℤ) : Finset ℤ :=
  (A ×ˢ B).image (fun p => p.1 + p.2)

/-- Number of representations `x = a - b` with `a ∈ A, b ∈ B`. -/
def delta (A B : Finset ℤ) (x : ℤ) : ℕ :=
  ((A ×ˢ B).filter (fun p => p.1 - p.2 = x)).card

/-- Number of representations `x = a + b` with `a ∈ A, b ∈ B`. -/
def sigma (A B : Finset ℤ) (x : ℤ) : ℕ :=
  ((A ×ˢ B).filter (fun p => p.1 + p.2 = x)).card

/-- Second additive energy `E(A, B)`. -/
def E2 (A B : Finset ℤ) : ℕ :=
  ∑ x ∈ diffSet A B, (delta A B x) ^ 2

/-- Third additive energy `E_3(A, B)`. -/
def E3 (A B : Finset ℤ) : ℕ :=
  ∑ x ∈ diffSet A B, (delta A B x) ^ 3

lemma delta_eq_card_filter_left (A B : Finset ℤ) (x : ℤ) :
    delta A B x = (A.filter (fun a => a - x ∈ B)).card := by
  unfold delta
  refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product] at hp ⊢
    exact ⟨hp.1.1, by have h := hp.1.2; rwa [← hp.2, sub_sub_cancel]⟩
  · intro p1 hp1 p2 hp2 h1
    simp only [Finset.mem_filter, Finset.mem_product] at hp1 hp2
    exact Prod.ext h1 (by linarith [hp1.2, hp2.2])
  · intro a ha
    simp only [Finset.mem_filter] at ha
    exact ⟨(a, a - x), by simp [ha.1, ha.2], rfl⟩

lemma delta_eq_card_filter_right (A B : Finset ℤ) (x : ℤ) :
    delta A B x = (B.filter (fun b => b + x ∈ A)).card := by
  unfold delta
  refine Finset.card_bij (fun p _ => p.2) ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product] at hp ⊢
    exact ⟨hp.1.2, by have h := hp.1.1; rwa [← hp.2, add_sub_cancel]⟩
  · intro p1 hp1 p2 hp2 h2
    simp only [Finset.mem_filter, Finset.mem_product] at hp1 hp2
    exact Prod.ext (by linarith [hp1.2, hp2.2]) h2
  · intro b hb
    simp only [Finset.mem_filter] at hb
    exact ⟨(b + x, b), by simp [hb.1, hb.2], rfl⟩

lemma delta_le_card_left (A B : Finset ℤ) (x : ℤ) : delta A B x ≤ A.card := by
  rw [delta_eq_card_filter_left]
  exact Finset.card_filter_le _ _

lemma delta_le_card_right (A B : Finset ℤ) (x : ℤ) : delta A B x ≤ B.card := by
  rw [delta_eq_card_filter_right]
  exact Finset.card_filter_le _ _

lemma delta_eq_zero_of_notMem (A B : Finset ℤ) {x : ℤ} (hx : x ∉ diffSet A B) :
    delta A B x = 0 := by
  rw [delta, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro p hp hsub
  exact hx (Finset.mem_image.2 ⟨p, hp, hsub⟩)

lemma mem_diffSet_of_pos_delta (A B : Finset ℤ) {x : ℤ} (hx : 0 < delta A B x) :
    x ∈ diffSet A B := by
  by_contra h
  exact (delta_eq_zero_of_notMem A B h ▸ hx).false

lemma sigma_eq_delta_neg (A B : Finset ℤ) (x : ℤ) :
    sigma A B x = delta A (B.image Neg.neg) x := by
  unfold sigma delta
  refine Finset.card_bij (fun p _ => (p.1, -p.2)) ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_image] at hp ⊢
    exact ⟨⟨hp.1.1, p.2, hp.1.2, rfl⟩, by linarith [hp.2]⟩
  · intro p1 _ p2 _ h
    simp only [Prod.mk.injEq, neg_inj] at h
    exact Prod.ext h.1 h.2
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_image] at hp
    rcases hp.1.2 with ⟨b, hb, hbeq⟩
    exact ⟨(p.1, b), by simp [hp.1.1, hb]; linarith [hp.2, hbeq], Prod.ext rfl hbeq⟩

lemma sigma_le_card_left (A B : Finset ℤ) (x : ℤ) : sigma A B x ≤ A.card := by
  rw [sigma_eq_delta_neg]
  exact delta_le_card_left _ _ _

lemma card_image_neg (B : Finset ℤ) : (B.image Neg.neg).card = B.card :=
  Finset.card_image_of_injective B neg_injective

lemma sum_delta_eq_mul (A B : Finset ℤ) :
    ∑ x ∈ diffSet A B, delta A B x = A.card * B.card := by
  unfold delta
  have h1 := Finset.card_eq_sum_card_fiberwise (s := A ×ˢ B) (t := diffSet A B)
    (f := fun p : ℤ × ℤ => p.1 - p.2) (fun p hp => Finset.mem_image.2 ⟨p, hp, rfl⟩)
  rw [Finset.card_product] at h1
  exact h1.symm

lemma sum_delta_le_mul (A B S : Finset ℤ) :
    ∑ x ∈ S, delta A B x ≤ A.card * B.card := by
  rw [← sum_delta_eq_mul A B]
  calc ∑ x ∈ S, delta A B x
      = ∑ x ∈ S ∩ diffSet A B, delta A B x := by
        symm
        refine Finset.sum_subset Finset.inter_subset_left fun x hxS hxnot => ?_
        have hx : x ∉ diffSet A B := fun h => hxnot (Finset.mem_inter.2 ⟨hxS, h⟩)
        exact delta_eq_zero_of_notMem A B hx
    _ ≤ ∑ x ∈ diffSet A B, delta A B x :=
        Finset.sum_le_sum_of_subset Finset.inter_subset_right

lemma sum_delta_pow_le_E3 (A B S : Finset ℤ) :
    ∑ x ∈ S, (delta A B x) ^ 3 ≤ E3 A B := by
  unfold E3
  calc ∑ x ∈ S, (delta A B x) ^ 3
      = ∑ x ∈ S ∩ diffSet A B, (delta A B x) ^ 3 := by
        symm
        refine Finset.sum_subset Finset.inter_subset_left fun x hxS hxnot => ?_
        have hx : x ∉ diffSet A B := fun h => hxnot (Finset.mem_inter.2 ⟨hxS, h⟩)
        simp [delta_eq_zero_of_notMem A B hx]
    _ ≤ ∑ x ∈ diffSet A B, (delta A B x) ^ 3 :=
        Finset.sum_le_sum_of_subset Finset.inter_subset_right

lemma sum_delta_comm (A B C : Finset ℤ) :
    ∑ c ∈ C, delta A B c = ∑ b ∈ B, delta A C b := by
  have hL : ∑ c ∈ C, delta A B c =
      ((A ×ˢ B ×ˢ C).filter (fun t => t.1 - t.2.1 = t.2.2)).card := by
    simp only [delta]
    rw [← Finset.card_sigma]
    refine Finset.card_bij (fun p _ => (p.2.1, p.2.2, p.1)) ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_product] at hp ⊢
      exact ⟨⟨hp.2.1.1, hp.2.1.2, hp.1⟩, hp.2.2⟩
    · intro p1 _ p2 _ h
      simp only [Prod.mk.injEq] at h
      exact Sigma.ext h.2.2 (heq_of_eq (Prod.ext h.1 h.2.1))
    · intro t ht
      simp only [Finset.mem_filter, Finset.mem_product] at ht
      exact ⟨⟨t.2.2, (t.1, t.2.1)⟩, by simp [ht.1.1, ht.1.2.1, ht.1.2.2, ht.2], rfl⟩
  have hR : ∑ b ∈ B, delta A C b =
      ((A ×ˢ B ×ˢ C).filter (fun t => t.1 - t.2.1 = t.2.2)).card := by
    simp only [delta]
    rw [← Finset.card_sigma]
    refine Finset.card_bij (fun p _ => (p.2.1, p.1, p.2.2)) ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_product] at hp ⊢
      exact ⟨⟨hp.2.1.1, hp.1, hp.2.1.2⟩, by linarith [hp.2.2]⟩
    · intro p1 _ p2 _ h
      simp only [Prod.mk.injEq] at h
      exact Sigma.ext h.2.1 (heq_of_eq (Prod.ext h.1 h.2.2))
    · intro t ht
      simp only [Finset.mem_filter, Finset.mem_product] at ht
      exact ⟨⟨t.2.1, (t.1, t.2.2)⟩, by simp [ht.1.1, ht.1.2.1, ht.1.2.2]; linarith [ht.2], rfl⟩
  rw [hL, hR]

lemma sum_delta_mul_delta_comm (A B C E : Finset ℤ) :
    ∑ x ∈ diffSet A B, delta A B x * delta C E x =
    ∑ y ∈ diffSet A C, delta A C y * delta B E y := by
  have hQuad (X Y Z W : Finset ℤ) :
      ∑ x ∈ diffSet X Y, delta X Y x * delta Z W x =
      (((X ×ˢ Y) ×ˢ (Z ×ˢ W)).filter (fun q => q.1.1 - q.1.2 = q.2.1 - q.2.2)).card := by
    have h1 : ∑ x ∈ diffSet X Y, delta X Y x * delta Z W x =
        ∑ x ∈ diffSet X Y,
          (((X ×ˢ Y).filter (fun p => p.1 - p.2 = x)) ×ˢ
            ((Z ×ˢ W).filter (fun p => p.1 - p.2 = x))).card := by
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.card_product, delta, delta]
    rw [h1, ← Finset.card_sigma]
    refine Finset.card_bij (fun s _ => s.2) ?_ ?_ ?_
    · intro s hs
      simp only [Finset.mem_sigma, Finset.mem_product, Finset.mem_filter] at hs ⊢
      exact ⟨⟨hs.2.1.1, hs.2.2.1⟩, by linarith [hs.2.1.2, hs.2.2.2]⟩
    · intro s1 hs1 s2 hs2 h
      simp only [Finset.mem_sigma, Finset.mem_product, Finset.mem_filter] at hs1 hs2
      have hx : s1.1 = s2.1 := by
        rw [← hs1.2.1.2, ← hs2.2.1.2, h]
      exact Sigma.ext hx (heq_of_eq h)
    · intro q hq
      simp only [Finset.mem_filter, Finset.mem_product] at hq
      refine ⟨⟨q.1.1 - q.1.2, q⟩, ?_, rfl⟩
      simp only [Finset.mem_sigma, Finset.mem_product, Finset.mem_filter]
      exact ⟨Finset.mem_image.2 ⟨q.1, Finset.mem_product.2 hq.1.1, rfl⟩,
        ⟨hq.1.1, trivial⟩, ⟨hq.1.2, hq.2.symm⟩⟩
  rw [hQuad A B C E, hQuad A C B E]
  refine Finset.card_bij (fun q _ => ((q.1.1, q.2.1), (q.1.2, q.2.2))) ?_ ?_ ?_
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_product] at hq ⊢
    exact ⟨⟨⟨hq.1.1.1, hq.1.2.1⟩, ⟨hq.1.1.2, hq.1.2.2⟩⟩, by linarith [hq.2]⟩
  · intro q1 _ q2 _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (Prod.ext h.1.1 h.2.1) (Prod.ext h.1.2 h.2.2)
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_product] at hq
    exact ⟨((q.1.1, q.2.1), (q.1.2, q.2.2)),
      by simp [hq.1.1.1, hq.1.1.2, hq.1.2.1, hq.1.2.2]; linarith [hq.2], rfl⟩

lemma sum_delta_mul_delta_le_comm (A B C E S : Finset ℤ) :
    ∑ x ∈ S, delta A B x * delta C E x ≤
    ∑ y ∈ diffSet A C, delta A C y * delta B E y := by
  rw [← sum_delta_mul_delta_comm A B C E]
  calc ∑ x ∈ S, delta A B x * delta C E x
      = ∑ x ∈ S ∩ diffSet A B, delta A B x * delta C E x := by
        symm
        refine Finset.sum_subset Finset.inter_subset_left fun x hxS hxnot => ?_
        have hx : x ∉ diffSet A B := fun h => hxnot (Finset.mem_inter.2 ⟨hxS, h⟩)
        simp [delta_eq_zero_of_notMem A B hx]
    _ ≤ ∑ x ∈ diffSet A B, delta A B x * delta C E x :=
        Finset.sum_le_sum_of_subset Finset.inter_subset_right

/- ## Section 2: Elementary Convex Incidence Bound (RSSS) and `E_3(A, B)` -/

lemma telescoping_sum_nat (g : ℕ → ℕ) (m : ℕ) (hmono : ∀ i < m, g i ≤ g (i + 1)) :
    ∑ t ∈ Finset.range m, (g (t + 1) - g t) = g m - g 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih (fun i hi => hmono i (by omega))]
    have h0m : g 0 ≤ g m := by
      clear ih
      induction m with
      | zero => exact le_rfl
      | succ k ihk =>
        exact le_trans (ihk (fun i hi => hmono i (by omega))) (hmono k (by omega))
    have hms : g m ≤ g (m + 1) := hmono m (Nat.lt_succ_self m)
    omega

lemma markov_bad_steps {r M : ℕ} (g : ℕ → ℕ) (hr : 2 ≤ r)
    (hsum : ∑ t ∈ Finset.range (r - 1), g t < M) :
    3 * ((Finset.range (r - 1)).filter (fun t => 3 * M < (r - 1) * g t)).card < r - 1 := by
  set T := (Finset.range (r - 1)).filter (fun t => 3 * M < (r - 1) * g t)
  rcases Nat.eq_zero_or_pos T.card with h0 | hpos
  · rw [h0]; omega
  · have hstrict : 3 * M * T.card < ∑ t ∈ T, (r - 1) * g t := by
      have hne : T.Nonempty := Finset.card_pos.1 hpos
      have := Finset.sum_lt_sum_of_nonempty hne (f := fun _ => 3 * M)
        (g := fun t => (r - 1) * g t) (fun t ht => (Finset.mem_filter.1 ht).2)
      simpa [Finset.sum_const, smul_eq_mul, mul_comm] using this
    have hle : ∑ t ∈ T, (r - 1) * g t ≤ (r - 1) * ∑ t ∈ Finset.range (r - 1), g t := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum_of_subset (f := fun t => (r - 1) * g t) (Finset.filter_subset _ _)
    have hlt2 : (r - 1) * ∑ t ∈ Finset.range (r - 1), g t ≤ (r - 1) * M :=
      Nat.mul_le_mul_left (r - 1) (le_of_lt hsum)
    have hlt3 : 3 * M * T.card < (r - 1) * M := lt_of_lt_of_le (lt_of_lt_of_le hstrict hle) hlt2
    have hMpos : 0 < M := lt_of_le_of_lt (Nat.zero_le _) hsum
    have : 3 * T.card * M < (r - 1) * M := by linarith
    exact Nat.lt_of_mul_lt_mul_right this

/-- Elementary convex incidence bound: for a strictly convex sequence `A` and any finite
    `B ⊂ ℤ`, the set `D` of shifts with `delta A B d ≥ k` satisfies `k^3 * |D| ≤ 216 * |A| * |B|^2`. -/
theorem convex_level_bound (cs : ConvexSeq) (B D : Finset ℤ) (k : ℕ) (hk : 1 ≤ k)
    (hD : ∀ d ∈ D, k ≤ delta cs.toFinset B d) :
    k ^ 3 * D.card ≤ 216 * cs.n * B.card ^ 2 := by
  rcases Nat.eq_zero_or_pos D.card with hD0 | hDpos
  · simp [hD0]
  have hBpos : 0 < B.card := by
    obtain ⟨d, hd⟩ := Finset.card_pos.1 hDpos
    have h1 : 1 ≤ delta cs.toFinset B d := le_trans hk (hD d hd)
    have h2 : delta cs.toFinset B d ≤ B.card := delta_le_card_right _ _ _
    omega
  have hApos : 0 < cs.n := by
    obtain ⟨d, hd⟩ := Finset.card_pos.1 hDpos
    have h1 : 1 ≤ delta cs.toFinset B d := le_trans hk (hD d hd)
    have h2 : delta cs.toFinset B d ≤ cs.toFinset.card := delta_le_card_left _ _ _
    rw [cs.card_toFinset] at h2
    omega
  rcases eq_or_lt_of_le hk with rfl | hk2
  · have hsub : D ⊆ diffSet cs.toFinset B := fun d hd =>
      mem_diffSet_of_pos_delta _ _ (lt_of_lt_of_le Nat.zero_lt_one (hD d hd))
    have hcard : D.card ≤ cs.n * B.card := by
      calc D.card ≤ (diffSet cs.toFinset B).card := Finset.card_le_card hsub
        _ ≤ (cs.toFinset ×ˢ B).card := Finset.card_image_le
        _ = cs.n * B.card := by rw [Finset.card_product, cs.card_toFinset]
    nlinarith
  have hk2' : 2 ≤ k := hk2
  let bEmb : Fin B.card ↪o ℤ := B.orderEmbOfFin rfl
  let I : ℤ → Finset ℕ := fun d => (Finset.range cs.n).filter (fun i => cs.val i - d ∈ B)
  have hIcard : ∀ d, (I d).card = delta cs.toFinset B d := by
    intro d
    rw [delta_eq_card_filter_left, ConvexSeq.toFinset]
    refine Finset.card_bij (fun i _ => cs.val i) ?_ ?_ ?_
    · intro i hi
      simp only [I, Finset.mem_filter, Finset.mem_range] at hi
      simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range]
      exact ⟨⟨i, hi.1, rfl⟩, hi.2⟩
    · intro i1 hi1 i2 hi2 heq
      simp only [I, Finset.mem_filter, Finset.mem_range] at hi1 hi2
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · exact (cs.strictMono i1 i2 hlt hi2.1).ne heq
      · exact (cs.strictMono i2 i1 hlt hi1.1).ne heq.symm
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range] at ha
      rcases ha.1 with ⟨i, hi, rfl⟩
      exact ⟨i, by simp [I, hi, ha.2], rfl⟩
  have hb_mem : ∀ z ∈ B, ∃ j : Fin B.card, bEmb j = z := by
    intro z hz
    have hz' : z ∈ Set.range bEmb := by rw [Finset.range_orderEmbOfFin]; exact hz
    exact hz'
  let bIdx (z : ℤ) (hz : z ∈ B) : Fin B.card := Classical.choose (hb_mem z hz)
  have hbIdx_spec : ∀ z (hz : z ∈ B), bEmb (bIdx z hz) = z := fun z hz =>
    Classical.choose_spec (hb_mem z hz)
  let eI (d : ℤ) : Fin (I d).card ↪o ℕ := (I d).orderEmbOfFin rfl
  have heI_mem : ∀ d (t : Fin (I d).card), eI d t ∈ I d := fun d t =>
    Finset.orderEmbOfFin_mem (I d) rfl t
  let eJ (d : ℤ) (t : Fin (I d).card) : Fin B.card :=
    bIdx (cs.val (eI d t) - d) (Finset.mem_filter.1 (heI_mem d t)).2
  have heJ_spec : ∀ d (t : Fin (I d).card), bEmb (eJ d t) = cs.val (eI d t) - d :=
    fun d t => hbIdx_spec _ (Finset.mem_filter.1 (heI_mem d t)).2
  have heJ_mono : ∀ d, StrictMono (eJ d) := by
    intro d t1 t2 hlt
    have hi1 : eI d t1 < eI d t2 := (eI d).strictMono hlt
    have hi2 : eI d t2 < cs.n := Finset.mem_range.1 (Finset.mem_filter.1 (heI_mem d t2)).1
    have hval : cs.val (eI d t1) < cs.val (eI d t2) := cs.strictMono _ _ hi1 hi2
    have hb : bEmb (eJ d t1) < bEmb (eJ d t2) := by
      rw [heJ_spec, heJ_spec]; linarith
    exact bEmb.strictMono.lt_iff_lt.1 hb
  let di (d : ℤ) (t : ℕ) : ℕ :=
    if h : t + 1 < (I d).card then eI d ⟨t + 1, h⟩ - eI d ⟨t, by omega⟩ else 0
  let dj (d : ℤ) (t : ℕ) : ℕ :=
    if h : t + 1 < (I d).card then (eJ d ⟨t + 1, h⟩).1 - (eJ d ⟨t, by omega⟩).1 else 0
  let G (d : ℤ) : Finset ℕ :=
    (Finset.range ((I d).card - 1)).filter
      (fun t => ((I d).card - 1) * di d t ≤ 3 * cs.n ∧
                ((I d).card - 1) * dj d t ≤ 3 * B.card)
  have hG_card : ∀ d ∈ D, k - 1 ≤ 3 * (G d).card := by
    intro d hd
    have hr : 2 ≤ (I d).card := by rw [hIcard]; exact le_trans hk2' (hD d hd)
    have hsum_i : ∑ t ∈ Finset.range ((I d).card - 1), di d t < cs.n := by
      let gi : ℕ → ℕ := fun t => if h : t < (I d).card then eI d ⟨t, h⟩ else 0
      have hcongr : ∑ t ∈ Finset.range ((I d).card - 1), di d t =
          ∑ t ∈ Finset.range ((I d).card - 1), (gi (t + 1) - gi t) := by
        refine Finset.sum_congr rfl fun t ht => ?_
        have hlt : t + 1 < (I d).card := by rw [Finset.mem_range] at ht; omega
        have hlt0 : t < (I d).card := by omega
        simp [di, gi, hlt, hlt0]
      have hgi_mono : ∀ t < (I d).card - 1, gi t ≤ gi (t + 1) := by
        intro t ht
        have hlt : t + 1 < (I d).card := by omega
        have hlt0 : t < (I d).card := by omega
        simp only [gi, dif_pos hlt, dif_pos hlt0]
        exact le_of_lt ((eI d).strictMono (show (⟨t, hlt0⟩ : Fin (I d).card) < ⟨t + 1, hlt⟩ by
          exact Nat.lt_succ_self t))
      rw [hcongr, telescoping_sum_nat gi ((I d).card - 1) hgi_mono]
      have hlt_end : (I d).card - 1 < (I d).card := by omega
      have hlt_val : eI d ⟨(I d).card - 1, hlt_end⟩ < cs.n :=
        Finset.mem_range.1 (Finset.mem_filter.1 (heI_mem d _)).1
      simp only [gi, dif_pos hlt_end]
      omega
    have hsum_j : ∑ t ∈ Finset.range ((I d).card - 1), dj d t < B.card := by
      let gj : ℕ → ℕ := fun t => if h : t < (I d).card then (eJ d ⟨t, h⟩).1 else 0
      have hcongr : ∑ t ∈ Finset.range ((I d).card - 1), dj d t =
          ∑ t ∈ Finset.range ((I d).card - 1), (gj (t + 1) - gj t) := by
        refine Finset.sum_congr rfl fun t ht => ?_
        have hlt : t + 1 < (I d).card := by rw [Finset.mem_range] at ht; omega
        have hlt0 : t < (I d).card := by omega
        simp [dj, gj, hlt, hlt0]
      have hgj_mono : ∀ t < (I d).card - 1, gj t ≤ gj (t + 1) := by
        intro t ht
        have hlt : t + 1 < (I d).card := by omega
        have hlt0 : t < (I d).card := by omega
        simp only [gj, dif_pos hlt, dif_pos hlt0]
        exact le_of_lt (heJ_mono d (show (⟨t, hlt0⟩ : Fin (I d).card) < ⟨t + 1, hlt⟩ by
          exact Nat.lt_succ_self t))
      rw [hcongr, telescoping_sum_nat gj ((I d).card - 1) hgj_mono]
      have hlt_end : (I d).card - 1 < (I d).card := by omega
      have hlt_val : (eJ d ⟨(I d).card - 1, hlt_end⟩).1 < B.card := (eJ d _).2
      simp only [gj, dif_pos hlt_end]
      omega
    have hT1 := markov_bad_steps (di d) hr hsum_i
    have hT2 := markov_bad_steps (dj d) hr hsum_j
    set R := Finset.range ((I d).card - 1)
    set T1 := R.filter (fun t => 3 * cs.n < ((I d).card - 1) * di d t)
    set T2 := R.filter (fun t => 3 * B.card < ((I d).card - 1) * dj d t)
    have hcov : R ⊆ G d ∪ (T1 ∪ T2) := by
      intro t ht
      simp only [Finset.mem_union, G, T1, T2, Finset.mem_filter]
      by_cases h1 : ((I d).card - 1) * di d t ≤ 3 * cs.n
      · by_cases h2 : ((I d).card - 1) * dj d t ≤ 3 * B.card
        · left; exact ⟨ht, h1, h2⟩
        · right; right; exact ⟨ht, by omega⟩
      · right; left; exact ⟨ht, by omega⟩
    have hcle : R.card ≤ (G d).card + T1.card + T2.card := by
      calc R.card ≤ (G d ∪ (T1 ∪ T2)).card := Finset.card_le_card hcov
        _ ≤ (G d).card + (T1 ∪ T2).card := Finset.card_union_le _ _
        _ ≤ (G d).card + (T1.card + T2.card) := Nat.add_le_add_left (Finset.card_union_le _ _) _
        _ = (G d).card + T1.card + T2.card := by omega
    rw [Finset.card_range] at hcle
    have hk_le : k ≤ (I d).card := by rw [hIcard]; exact hD d hd
    omega
  let box : Finset (ℕ × ℕ × ℕ) :=
    (Finset.range B.card) ×ˢ
      ((Finset.Icc 1 (3 * B.card / (k - 1))) ×ˢ (Finset.Icc 1 (3 * cs.n / (k - 1))))
  let phi (p : Σ _d : ℤ, ℕ) : ℕ × ℕ × ℕ :=
    if h : p.2 + 1 < (I p.1).card then
      ((eJ p.1 ⟨p.2, by omega⟩).1, dj p.1 p.2, di p.1 p.2)
    else (0, 0, 0)
  have hcard_sigma : (D.sigma G).card ≤ box.card := by
    refine Finset.card_le_card_of_injOn phi ?_ ?_
    · intro p hp
      simp only [Finset.mem_coe, Finset.mem_sigma, G, Finset.mem_filter,
        Finset.mem_range] at hp
      have hr : k ≤ (I p.1).card := by rw [hIcard]; exact hD p.1 hp.1
      have hlt : p.2 + 1 < (I p.1).card := by omega
      simp only [phi, dif_pos hlt, box, Finset.mem_coe, Finset.mem_product,
        Finset.mem_range, Finset.mem_Icc]
      have hdi_pos : 1 ≤ di p.1 p.2 := by
        simp only [di, dif_pos hlt]
        have := (eI p.1).strictMono (show (⟨p.2, by omega⟩ : Fin (I p.1).card) < ⟨p.2 + 1, hlt⟩
          by exact Nat.lt_succ_self p.2)
        omega
      have hdj_pos : 1 ≤ dj p.1 p.2 := by
        simp only [dj, dif_pos hlt]
        have := heJ_mono p.1 (show (⟨p.2, by omega⟩ : Fin (I p.1).card) < ⟨p.2 + 1, hlt⟩
          by exact Nat.lt_succ_self p.2)
        change (eJ p.1 ⟨p.2, by omega⟩).1 < (eJ p.1 ⟨p.2 + 1, hlt⟩).1 at this
        omega
      have hdi_ub : di p.1 p.2 ≤ 3 * cs.n / (k - 1) := by
        refine (Nat.le_div_iff_mul_le (by omega : 0 < k - 1)).2 ?_
        calc di p.1 p.2 * (k - 1) = (k - 1) * di p.1 p.2 := mul_comm _ _
          _ ≤ ((I p.1).card - 1) * di p.1 p.2 := Nat.mul_le_mul_right _ (by omega)
          _ ≤ 3 * cs.n := hp.2.2.1
      have hdj_ub : dj p.1 p.2 ≤ 3 * B.card / (k - 1) := by
        refine (Nat.le_div_iff_mul_le (by omega : 0 < k - 1)).2 ?_
        calc dj p.1 p.2 * (k - 1) = (k - 1) * dj p.1 p.2 := mul_comm _ _
          _ ≤ ((I p.1).card - 1) * dj p.1 p.2 := Nat.mul_le_mul_right _ (by omega)
          _ ≤ 3 * B.card := hp.2.2.2
      exact ⟨(eJ p.1 ⟨p.2, by omega⟩).2, ⟨hdj_pos, hdj_ub⟩, ⟨hdi_pos, hdi_ub⟩⟩
    · intro p1 hp1 p2 hp2 hphi
      simp only [Finset.mem_coe, Finset.mem_sigma, G, Finset.mem_filter,
        Finset.mem_range] at hp1 hp2
      have hr1 : k ≤ (I p1.1).card := by rw [hIcard]; exact hD p1.1 hp1.1
      have hr2 : k ≤ (I p2.1).card := by rw [hIcard]; exact hD p2.1 hp2.1
      have hlt1 : p1.2 + 1 < (I p1.1).card := by omega
      have hlt2 : p2.2 + 1 < (I p2.1).card := by omega
      simp only [phi, dif_pos hlt1, dif_pos hlt2, Prod.mk.injEq] at hphi
      rcases hphi with ⟨hj_eq, hdj_eq, hdi_eq⟩
      set j1 : Fin B.card := eJ p1.1 ⟨p1.2, by omega⟩
      set j1' : Fin B.card := eJ p1.1 ⟨p1.2 + 1, hlt1⟩
      set j2 : Fin B.card := eJ p2.1 ⟨p2.2, by omega⟩
      set j2' : Fin B.card := eJ p2.1 ⟨p2.2 + 1, hlt2⟩
      set i1 : ℕ := eI p1.1 ⟨p1.2, by omega⟩
      set i1' : ℕ := eI p1.1 ⟨p1.2 + 1, hlt1⟩
      set i2 : ℕ := eI p2.1 ⟨p2.2, by omega⟩
      set i2' : ℕ := eI p2.1 ⟨p2.2 + 1, hlt2⟩
      have hi1_lt : i1 < i1' := (eI p1.1).strictMono (Nat.lt_succ_self p1.2)
      have hi2_lt : i2 < i2' := (eI p2.1).strictMono (Nat.lt_succ_self p2.2)
      have hj1_lt : j1.1 < j1'.1 := heJ_mono p1.1 (Nat.lt_succ_self p1.2)
      have hj2_lt : j2.1 < j2'.1 := heJ_mono p2.1 (Nat.lt_succ_self p2.2)
      simp only [dj, dif_pos hlt1, dif_pos hlt2] at hdj_eq
      simp only [di, dif_pos hlt1, dif_pos hlt2] at hdi_eq
      have hj_fin : j1 = j2 := Fin.ext hj_eq
      have hj'_fin : j1' = j2' := Fin.ext (by omega)
      set h : ℕ := i1' - i1
      have hh : 1 ≤ h := by omega
      have hi1'_eq : i1' = i1 + h := by omega
      have hi2'_eq : i2' = i2 + h := by omega
      have hi1'_lt : i1 + h < cs.n := by
        rw [← hi1'_eq]; exact Finset.mem_range.1 (Finset.mem_filter.1 (heI_mem p1.1 _)).1
      have hi2'_lt : i2 + h < cs.n := by
        rw [← hi2'_eq]; exact Finset.mem_range.1 (Finset.mem_filter.1 (heI_mem p2.1 _)).1
      have hdiff1 : cs.val (i1 + h) - cs.val i1 = bEmb j1' - bEmb j1 := by
        rw [← hi1'_eq, heJ_spec, heJ_spec]; ring
      have hdiff2 : cs.val (i2 + h) - cs.val i2 = bEmb j2' - bEmb j2 := by
        rw [← hi2'_eq, heJ_spec, heJ_spec]; ring
      have hdiff_eq : cs.val (i1 + h) - cs.val i1 = cs.val (i2 + h) - cs.val i2 := by
        rw [hdiff1, hdiff2, hj_fin, hj'_fin]
      have hi_eq : i1 = i2 := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hlt
        · exact (cs.step_h_mono h hh i1 i2 hlt hi2'_lt).ne hdiff_eq
        · exact (cs.step_h_mono h hh i2 i1 hlt hi1'_lt).ne hdiff_eq.symm
      have hd_eq : p1.1 = p2.1 := by
        have h1 : bEmb j1 = cs.val i1 - p1.1 := heJ_spec p1.1 ⟨p1.2, by omega⟩
        have h2 : bEmb j2 = cs.val i2 - p2.1 := heJ_spec p2.1 ⟨p2.2, by omega⟩
        rw [hj_fin, hi_eq] at h1
        linarith
      cases p1 with | mk d1 t1 =>
      cases p2 with | mk d2 t2 =>
      dsimp only at hd_eq hi_eq hlt1 hlt2
      subst hd_eq
      have ht_fin : (⟨t1, by omega⟩ : Fin (I d1).card) = ⟨t2, by omega⟩ :=
        (eI d1).injective hi_eq
      have ht_eq : t1 = t2 := congrArg Fin.val ht_fin
      subst ht_eq
      rfl
  have hsum_G : (k - 1) * D.card ≤ 3 * (D.sigma G).card := by
    rw [Finset.card_sigma, Finset.mul_sum]
    calc (k - 1) * D.card = ∑ _d ∈ D, (k - 1) := by
          rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ d ∈ D, 3 * (G d).card := Finset.sum_le_sum hG_card
  have hbox_card : box.card =
      B.card * ((3 * B.card / (k - 1)) * (3 * cs.n / (k - 1))) := by
    simp [box, Finset.card_product, Nat.card_Icc]
  have h1 : (k - 1) * D.card ≤
      3 * (B.card * ((3 * B.card / (k - 1)) * (3 * cs.n / (k - 1)))) :=
    le_trans hsum_G (by rw [← hbox_card]; exact Nat.mul_le_mul_left 3 hcard_sigma)
  have hdiv1 : (k - 1) * (3 * B.card / (k - 1)) ≤ 3 * B.card :=
    Nat.mul_div_le (3 * B.card) (k - 1)
  have hdiv2 : (k - 1) * (3 * cs.n / (k - 1)) ≤ 3 * cs.n :=
    Nat.mul_div_le (3 * cs.n) (k - 1)
  have hkm1 : (k - 1) ^ 3 * D.card ≤ 27 * cs.n * B.card ^ 2 := by
    calc (k - 1) ^ 3 * D.card
        = (k - 1) * (k - 1) * ((k - 1) * D.card) := by ring
      _ ≤ (k - 1) * (k - 1) * (3 * (B.card * ((3 * B.card / (k - 1)) * (3 * cs.n / (k - 1))))) :=
          Nat.mul_le_mul_left _ h1
      _ = 3 * B.card * ((k - 1) * (3 * B.card / (k - 1))) * ((k - 1) * (3 * cs.n / (k - 1))) := by
          ring
      _ ≤ 3 * B.card * (3 * B.card) * (3 * cs.n) := by
          gcongr
      _ = 27 * cs.n * B.card ^ 2 := by ring
  have hk_cube : k ^ 3 ≤ 8 * (k - 1) ^ 3 := by
    have hk_le : k ≤ 2 * (k - 1) := by omega
    calc k ^ 3 ≤ (2 * (k - 1)) ^ 3 := Nat.pow_le_pow_left hk_le 3
      _ = 8 * (k - 1) ^ 3 := by ring
  calc k ^ 3 * D.card ≤ (8 * (k - 1) ^ 3) * D.card := Nat.mul_le_mul_right _ hk_cube
    _ = 8 * ((k - 1) ^ 3 * D.card) := by ring
    _ ≤ 8 * (27 * cs.n * B.card ^ 2) := Nat.mul_le_mul_left 8 hkm1
    _ = 216 * cs.n * B.card ^ 2 := by ring

/- ## Section 3: Dyadic Decomposition and `E_3(A, B)` Bound -/

/-- Dyadic bucket `{x ∈ S | 2^j ≤ f x < 2^(j+1)}`. -/
def dyadicBucket (S : Finset ℤ) (f : ℤ → ℕ) (j : ℕ) : Finset ℤ :=
  S.filter (fun x => 2 ^ j ≤ f x ∧ f x < 2 ^ (j + 1))

lemma dyadic_sum_decomp (S : Finset ℤ) (f w : ℤ → ℕ) (M : ℕ)
    (hfM : ∀ x ∈ S, f x ≤ M) (hw0 : ∀ x ∈ S, f x = 0 → w x = 0) :
    ∑ x ∈ S, w x = ∑ j ∈ Finset.range (Nat.log 2 M + 1), ∑ x ∈ dyadicBucket S f j, w x := by
  have h1 : ∑ x ∈ S, w x = ∑ x ∈ S.filter (fun x => 1 ≤ f x), w x := by
    symm
    refine Finset.sum_subset (Finset.filter_subset _ _) fun x hxS hxnot => ?_
    simp only [Finset.mem_filter] at hxnot
    have hnot1 : ¬(1 ≤ f x) := fun h => hxnot ⟨hxS, h⟩
    exact hw0 x hxS (by omega)
  rw [h1, ← Finset.sum_biUnion]
  · refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext x
    simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_range, dyadicBucket]
    constructor
    · intro ⟨hxS, hxpos⟩
      refine ⟨Nat.log 2 (f x), ?_, hxS, ?_, ?_⟩
      · exact Nat.lt_succ_of_le (Nat.log_mono_right (hfM x hxS))
      · exact Nat.pow_log_le_self 2 (by omega)
      · exact Nat.lt_pow_succ_log_self (by norm_num) (f x)
    · rintro ⟨j, _, hxS, hge, _⟩
      exact ⟨hxS, le_trans Nat.one_le_two_pow hge⟩
  · intro i _ j _ hij
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro x hxi hxj
    simp only [dyadicBucket, Finset.mem_filter] at hxi hxj
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · have : 2 ^ (i + 1) ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hlt
      omega
    · have : 2 ^ (j + 1) ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hlt
      omega

lemma exists_dyadic_max (L : ℕ) (hL : 1 ≤ L) (g : ℕ → ℕ) :
    ∃ j < L, ∑ i ∈ Finset.range L, g i ≤ L * g j := by
  have hne : (Finset.range L).Nonempty := ⟨0, Finset.mem_range.2 (by omega)⟩
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image (Finset.range L) g hne
  refine ⟨j, Finset.mem_range.1 hj, ?_⟩
  calc ∑ i ∈ Finset.range L, g i
      ≤ ∑ _i ∈ Finset.range L, g j := Finset.sum_le_sum fun i hi => hmax i hi
    _ = L * g j := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

/-- Third energy bound for a strictly convex set `A` and any finite set `B`. -/
theorem convex_E3_bound (cs : ConvexSeq) (B : Finset ℤ) :
    E3 cs.toFinset B ≤ 1728 * (Nat.log 2 cs.n + 1) * cs.n * B.card ^ 2 := by
  unfold E3
  have hM : ∀ x ∈ diffSet cs.toFinset B, delta cs.toFinset B x ≤ cs.n := fun x _ => by
    rw [← cs.card_toFinset]; exact delta_le_card_left _ _ _
  rw [dyadic_sum_decomp (diffSet cs.toFinset B) (delta cs.toFinset B)
    (fun x => (delta cs.toFinset B x) ^ 3) cs.n hM (fun x _ h => by simp [h])]
  calc ∑ j ∈ Finset.range (Nat.log 2 cs.n + 1),
        ∑ x ∈ dyadicBucket (diffSet cs.toFinset B) (delta cs.toFinset B) j,
          (delta cs.toFinset B x) ^ 3
      ≤ ∑ j ∈ Finset.range (Nat.log 2 cs.n + 1),
          (2 ^ (j + 1)) ^ 3 * (dyadicBucket (diffSet cs.toFinset B) (delta cs.toFinset B) j).card := by
        refine Finset.sum_le_sum fun j _ => ?_
        calc ∑ x ∈ dyadicBucket (diffSet cs.toFinset B) (delta cs.toFinset B) j,
              (delta cs.toFinset B x) ^ 3
            ≤ ∑ _x ∈ dyadicBucket (diffSet cs.toFinset B) (delta cs.toFinset B) j,
                (2 ^ (j + 1)) ^ 3 := by
              refine Finset.sum_le_sum fun x hx => ?_
              have hlt := (Finset.mem_filter.1 hx).2.2
              exact Nat.pow_le_pow_left (le_of_lt hlt) 3
          _ = (2 ^ (j + 1)) ^ 3 *
                (dyadicBucket (diffSet cs.toFinset B) (delta cs.toFinset B) j).card := by
              rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ _j ∈ Finset.range (Nat.log 2 cs.n + 1), 1728 * cs.n * B.card ^ 2 := by
        refine Finset.sum_le_sum fun j _ => ?_
        have hlev := convex_level_bound cs B
          (dyadicBucket (diffSet cs.toFinset B) (delta cs.toFinset B) j)
          (2 ^ j) Nat.one_le_two_pow
          (fun d hd => (Finset.mem_filter.1 hd).2.1)
        have h2 : (2 ^ (j + 1)) ^ 3 = 8 * (2 ^ j) ^ 3 := by ring
        rw [h2, mul_assoc]
        calc 8 * ((2 ^ j) ^ 3 *
              (dyadicBucket (diffSet cs.toFinset B) (delta cs.toFinset B) j).card)
            ≤ 8 * (216 * cs.n * B.card ^ 2) := Nat.mul_le_mul_left 8 hlev
          _ = 1728 * cs.n * B.card ^ 2 := by ring
    _ = 1728 * (Nat.log 2 cs.n + 1) * cs.n * B.card ^ 2 := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
        ring

/- ## Section 4: Algebraic 6th-Power Inequality and Projection Lemmas -/

/-- Sum-of-squares algebraic inequality replacing Hölder `(3, 3/2)` plus `(1, 3)` interpolation. -/
lemma sum_mul_pow_six_le (S : Finset ℤ) (f g : ℤ → ℝ)
    (hf : ∀ x ∈ S, 0 ≤ f x) (hg : ∀ x ∈ S, 0 ≤ g x) :
    (∑ x ∈ S, f x * g x) ^ 6 ≤
      (∑ x ∈ S, f x ^ 3) ^ 2 * (∑ x ∈ S, g x) ^ 3 * (∑ x ∈ S, g x ^ 3) := by
  set A3 : ℝ := ∑ x ∈ S, f x ^ 3
  set B1 : ℝ := ∑ x ∈ S, g x
  set B3 : ℝ := ∑ x ∈ S, g x ^ 3
  have hA3_nn : 0 ≤ A3 := Finset.sum_nonneg fun x hx => pow_nonneg (hf x hx) 3
  have hB1_nn : 0 ≤ B1 := Finset.sum_nonneg hg
  have hB3_nn : 0 ≤ B3 := Finset.sum_nonneg fun x hx => pow_nonneg (hg x hx) 3
  by_cases hA3 : A3 = 0
  · have hzero : ∀ x ∈ S, f x = 0 := by
      intro x hx
      have h3 : f x ^ 3 = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun y hy => pow_nonneg (hf y hy) 3)).1 hA3 x hx
      by_contra hne
      exact pow_ne_zero 3 hne h3
    have hsum0 : ∑ x ∈ S, f x * g x = 0 :=
      Finset.sum_eq_zero fun x hx => by simp [hzero x hx]
    rw [hsum0, hA3]; norm_num
  by_cases hB1 : B1 = 0
  · have hzero : ∀ x ∈ S, g x = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hg).1 hB1
    have hsum0 : ∑ x ∈ S, f x * g x = 0 :=
      Finset.sum_eq_zero fun x hx => by simp [hzero x hx]
    rw [hsum0, hB1]; norm_num
  by_cases hB3 : B3 = 0
  · have hzero : ∀ x ∈ S, g x = 0 := by
      intro x hx
      have h3 : g x ^ 3 = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun y hy => pow_nonneg (hg y hy) 3)).1 hB3 x hx
      by_contra hne
      exact pow_ne_zero 3 hne h3
    have hsum0 : ∑ x ∈ S, f x * g x = 0 :=
      Finset.sum_eq_zero fun x hx => by simp [hzero x hx]
    rw [hsum0, hB3]; norm_num
  have hA3_pos : 0 < A3 := lt_of_le_of_ne hA3_nn (Ne.symm hA3)
  have hB1_pos : 0 < B1 := lt_of_le_of_ne hB1_nn (Ne.symm hB1)
  have hB3_pos : 0 < B3 := lt_of_le_of_ne hB3_nn (Ne.symm hB3)
  set u : ℝ := A3 ^ ((1 : ℝ) / 6)
  set v : ℝ := B1 ^ ((1 : ℝ) / 6)
  set w : ℝ := B3 ^ ((1 : ℝ) / 6)
  have hu : 0 < u := Real.rpow_pos_of_pos hA3_pos _
  have hv : 0 < v := Real.rpow_pos_of_pos hB1_pos _
  have hw : 0 < w := Real.rpow_pos_of_pos hB3_pos _
  have hu6 : u ^ 6 = A3 := by
    rw [← Real.rpow_natCast u 6, ← Real.rpow_mul (le_of_lt hA3_pos)]
    norm_num
  have hv6 : v ^ 6 = B1 := by
    rw [← Real.rpow_natCast v 6, ← Real.rpow_mul (le_of_lt hB1_pos)]
    norm_num
  have hw6 : w ^ 6 = B3 := by
    rw [← Real.rpow_natCast w 6, ← Real.rpow_mul (le_of_lt hB3_pos)]
    norm_num
  have hpt : ∀ x ∈ S,
      6 * (f x * g x / (u ^ 2 * v ^ 3 * w)) ≤
      2 * (f x ^ 3 / u ^ 6) + 3 * (g x / v ^ 6) + g x ^ 3 / w ^ 6 := by
    intro x hx
    have hfx := hf x hx
    have hgx := hg x hx
    set a := f x / u ^ 2
    set b := g x / w ^ 2
    have ha : 0 ≤ a := div_nonneg hfx (by positivity)
    have hb : 0 ≤ b := div_nonneg hgx (by positivity)
    have hsq1 : 0 ≤ (2 * a + b) * (a - b) ^ 2 := by positivity
    have hsq2 : 0 ≤ 3 * g x * (f x / (u ^ 2 * w) - 1 / v ^ 3) ^ 2 := by positivity
    have hid :
        2 * (f x ^ 3 / u ^ 6) + 3 * (g x / v ^ 6) + g x ^ 3 / w ^ 6 -
        6 * (f x * g x / (u ^ 2 * v ^ 3 * w)) =
        (2 * a + b) * (a - b) ^ 2 + 3 * g x * (f x / (u ^ 2 * w) - 1 / v ^ 3) ^ 2 := by
      simp only [a, b]
      field_simp [hu.ne', hv.ne', hw.ne']
      ring
    linarith
  have hsum_le :
      6 * ((∑ x ∈ S, f x * g x) / (u ^ 2 * v ^ 3 * w)) ≤ 6 := by
    calc 6 * ((∑ x ∈ S, f x * g x) / (u ^ 2 * v ^ 3 * w))
        = ∑ x ∈ S, 6 * (f x * g x / (u ^ 2 * v ^ 3 * w)) := by
          rw [Finset.sum_div, Finset.mul_sum]
      _ ≤ ∑ x ∈ S, (2 * (f x ^ 3 / u ^ 6) + 3 * (g x / v ^ 6) + g x ^ 3 / w ^ 6) :=
          Finset.sum_le_sum hpt
      _ = 2 * (A3 / u ^ 6) + 3 * (B1 / v ^ 6) + B3 / w ^ 6 := by
          simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div, A3, B1, B3]
      _ = 6 := by rw [hu6, hv6, hw6, div_self hA3_pos.ne', div_self hB1_pos.ne',
          div_self hB3_pos.ne']; ring
  have hlin : ∑ x ∈ S, f x * g x ≤ u ^ 2 * v ^ 3 * w := by
    have hdiv : (∑ x ∈ S, f x * g x) / (u ^ 2 * v ^ 3 * w) ≤ 1 := by linarith
    exact (div_le_one (by positivity)).1 hdiv
  have hnn : 0 ≤ ∑ x ∈ S, f x * g x := Finset.sum_nonneg fun x hx => mul_nonneg (hf x hx) (hg x hx)
  calc (∑ x ∈ S, f x * g x) ^ 6
      ≤ (u ^ 2 * v ^ 3 * w) ^ 6 := pow_le_pow_left₀ hnn hlin 6
    _ = (u ^ 6) ^ 2 * (v ^ 6) ^ 3 * w ^ 6 := by ring
    _ = A3 ^ 2 * B1 ^ 3 * B3 := by rw [hu6, hv6, hw6]

/-- Combined 6th-power convex incidence bound for `∑ x ∈ S, f x * delta A B x`. -/
lemma convex_sum_mul_delta_pow6 (cs : ConvexSeq) (B S : Finset ℤ) (f : ℤ → ℕ) :
    ((∑ x ∈ S, f x * delta cs.toFinset B x : ℕ) : ℝ) ^ 6 ≤
      1728 * ((Nat.log 2 cs.n + 1 : ℕ) : ℝ) * (cs.n : ℝ) ^ 4 * (B.card : ℝ) ^ 5 *
        ((∑ x ∈ S, f x ^ 3 : ℕ) : ℝ) ^ 2 := by
  have h6 := sum_mul_pow_six_le S (fun x => (f x : ℝ)) (fun x => (delta cs.toFinset B x : ℝ))
    (fun _ _ => Nat.cast_nonneg _) (fun _ _ => Nat.cast_nonneg _)
  have hB1 : ∑ x ∈ S, (delta cs.toFinset B x : ℝ) ≤ (cs.n : ℝ) * (B.card : ℝ) := by
    have hnat := sum_delta_le_mul cs.toFinset B S
    rw [cs.card_toFinset] at hnat
    exact_mod_cast hnat
  have hB3 : ∑ x ∈ S, (delta cs.toFinset B x : ℝ) ^ 3 ≤
      1728 * ((Nat.log 2 cs.n + 1 : ℕ) : ℝ) * (cs.n : ℝ) * (B.card : ℝ) ^ 2 := by
    have hnat := le_trans (sum_delta_pow_le_E3 cs.toFinset B S) (convex_E3_bound cs B)
    exact_mod_cast hnat
  have hL : (∑ x ∈ S, (f x : ℝ) * (delta cs.toFinset B x : ℝ)) =
      ((∑ x ∈ S, f x * delta cs.toFinset B x : ℕ) : ℝ) := by push_cast; rfl
  have hF3 : (∑ x ∈ S, (f x : ℝ) ^ 3) = ((∑ x ∈ S, f x ^ 3 : ℕ) : ℝ) := by push_cast; rfl
  rw [hL, hF3] at h6
  have hnn1 : 0 ≤ ∑ x ∈ S, (delta cs.toFinset B x : ℝ) :=
    Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  have hnn3 : 0 ≤ ∑ x ∈ S, (delta cs.toFinset B x : ℝ) ^ 3 :=
    Finset.sum_nonneg fun _ _ => pow_nonneg (Nat.cast_nonneg _) 3
  calc ((∑ x ∈ S, f x * delta cs.toFinset B x : ℕ) : ℝ) ^ 6
      ≤ ((∑ x ∈ S, f x ^ 3 : ℕ) : ℝ) ^ 2 *
          (∑ x ∈ S, (delta cs.toFinset B x : ℝ)) ^ 3 *
          (∑ x ∈ S, (delta cs.toFinset B x : ℝ) ^ 3) := h6
    _ ≤ ((∑ x ∈ S, f x ^ 3 : ℕ) : ℝ) ^ 2 *
          ((cs.n : ℝ) * (B.card : ℝ)) ^ 3 *
          (1728 * ((Nat.log 2 cs.n + 1 : ℕ) : ℝ) * (cs.n : ℝ) * (B.card : ℝ) ^ 2) := by
        gcongr
    _ = 1728 * ((Nat.log 2 cs.n + 1 : ℕ) : ℝ) * (cs.n : ℝ) ^ 4 * (B.card : ℝ) ^ 5 *
          ((∑ x ∈ S, f x ^ 3 : ℕ) : ℝ) ^ 2 := by ring

/-- Cauchy-Schwarz projection lemma: `|X|^2 ≤ |Y| * #{(x1, x2) ∈ X^2 | f x1 = f x2}`. -/
lemma cs_projection {α β : Type*} [DecidableEq β] (X : Finset α) (Y : Finset β)
    (f : α → β) (hf : ∀ x ∈ X, f x ∈ Y) :
    X.card ^ 2 ≤ Y.card * ((X ×ˢ X).filter (fun p => f p.1 = f p.2)).card := by
  have h1 : X.card = ∑ y ∈ Y, (X.filter (fun x => f x = y)).card :=
    Finset.card_eq_sum_card_fiberwise hf
  have h2 : ((X ×ˢ X).filter (fun p => f p.1 = f p.2)).card =
      ∑ y ∈ Y, (X.filter (fun x => f x = y)).card ^ 2 := by
    have hs : ∑ y ∈ Y, (X.filter (fun x => f x = y)).card ^ 2 =
        ∑ y ∈ Y, ((X.filter (fun x => f x = y)) ×ˢ (X.filter (fun x => f x = y))).card := by
      refine Finset.sum_congr rfl fun y _ => by rw [Finset.card_product, sq]
    rw [hs, ← Finset.card_sigma]
    refine Finset.card_bij (fun p hp => ⟨f p.1, p⟩) ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_product] at hp
      simp only [Finset.mem_sigma, Finset.mem_product, Finset.mem_filter]
      exact ⟨hf p.1 hp.1.1, ⟨hp.1.1, trivial⟩, ⟨hp.1.2, hp.2.symm⟩⟩
    · intro p1 _ p2 _ h
      exact congrArg Sigma.snd h
    · intro s hs
      simp only [Finset.mem_sigma, Finset.mem_product, Finset.mem_filter] at hs
      refine ⟨s.2, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨hs.2.1.1, hs.2.2.1⟩, hs.2.1.2.trans hs.2.2.2.symm⟩
      · exact Sigma.ext hs.2.1.2 (heq_of_eq rfl)
  rw [h1, h2]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Y
    (fun _ => (1 : ℝ)) (fun y => ((X.filter (fun x => f x = y)).card : ℝ))
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
  exact_mod_cast hcs

/-- Cushman's Lemma 1.6 (`lem:diff-proj`) with clean rational constants `1/10` and `1/2`:
    for `P = {x ∈ D | 10 * |D| * delta A A x ≥ |A|^2}`,
    `9 * |A|^6 ≤ 625 * E_3(A) * ∑ x ∈ P, delta P P x`. -/
theorem diff_proj_lemma (A : Finset ℤ) :
    let D := diffSet A A
    let P := D.filter (fun x => A.card ^ 2 ≤ 10 * D.card * delta A A x)
    9 * A.card ^ 6 ≤ 625 * E3 A A * ∑ x ∈ P, delta P P x := by
  intro D P
  rcases Nat.eq_zero_or_pos A.card with hA0 | hApos
  · simp [hA0]
  have hDpos : 0 < D.card := by
    obtain ⟨a, ha⟩ := Finset.card_pos.1 hApos
    exact Finset.card_pos.2 ⟨0, Finset.mem_image.2 ⟨(a, a), Finset.mem_product.2 ⟨ha, ha⟩, sub_self a⟩⟩
  -- Step 1: ∑_{x ∈ P} delta A A x ≥ (9/10) |A|^2
  have hsum_notP : 10 * ∑ x ∈ D \ P, delta A A x ≤ A.card ^ 2 := by
    have h1 : 10 * D.card * ∑ x ∈ D \ P, delta A A x ≤ D.card * A.card ^ 2 := by
      rw [Finset.mul_sum]
      calc ∑ x ∈ D \ P, 10 * D.card * delta A A x
          ≤ ∑ _x ∈ D \ P, A.card ^ 2 := by
            refine Finset.sum_le_sum fun x hx => ?_
            simp only [Finset.mem_sdiff, P, Finset.mem_filter] at hx
            have hlt : 10 * D.card * delta A A x < A.card ^ 2 := by
              by_contra hge
              exact hx.2 ⟨hx.1, not_lt.1 hge⟩
            exact le_of_lt hlt
        _ = (D \ P).card * A.card ^ 2 := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ D.card * A.card ^ 2 := Nat.mul_le_mul_right _ (Finset.card_le_card Finset.sdiff_subset)
    have h2 : D.card * (10 * ∑ x ∈ D \ P, delta A A x) ≤ D.card * A.card ^ 2 := by linarith
    exact Nat.le_of_mul_le_mul_left h2 hDpos
  have hsum_split : ∑ x ∈ P, delta A A x + ∑ x ∈ D \ P, delta A A x = A.card ^ 2 := by
    have hsub : P ⊆ D := Finset.filter_subset _ _
    rw [add_comm, Finset.sum_sdiff hsub, sum_delta_eq_mul A A, sq]
  have hsum_P : 9 * A.card ^ 2 ≤ 10 * ∑ x ∈ P, delta A A x := by omega
  -- Step 2: Rich elements R = {r ∈ A | 2 * |{a ∈ A | r - a ∈ P}| ≥ |A|}
  let S1 : Finset (ℤ × ℤ) := (A ×ˢ A).filter (fun p => p.1 - p.2 ∈ P)
  have hS1_card : S1.card = ∑ x ∈ P, delta A A x := by
    have h1 : S1.card = ∑ x ∈ P, (S1.filter (fun p => p.1 - p.2 = x)).card :=
      Finset.card_eq_sum_card_fiberwise (fun p hp => (Finset.mem_filter.1 hp).2)
    rw [h1]
    refine Finset.sum_congr rfl fun x hx => ?_
    unfold delta
    congr 1
    ext p
    simp only [S1, Finset.mem_filter]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2 ▸ hx⟩, h.2⟩⟩
  let deg (r : ℤ) : ℕ := (A.filter (fun a => r - a ∈ P)).card
  have hS1_sum : S1.card = ∑ r ∈ A, deg r := by
    have h1 : S1.card = ∑ r ∈ A, (S1.filter (fun p => p.1 = r)).card :=
      Finset.card_eq_sum_card_fiberwise (fun p hp => (Finset.mem_product.1 (Finset.mem_filter.1 hp).1).1)
    rw [h1]
    refine Finset.sum_congr rfl fun r hr => ?_
    refine Finset.card_bij (fun p _ => p.2) ?_ ?_ ?_
    · intro p hp
      simp only [S1, Finset.mem_filter, Finset.mem_product] at hp ⊢
      exact ⟨hp.1.1.2, by have h := hp.1.2; rwa [← hp.2]⟩
    · intro p1 hp1 p2 hp2 h2
      simp only [Finset.mem_filter] at hp1 hp2
      exact Prod.ext (hp1.2.trans hp2.2.symm) h2
    · intro a ha
      simp only [Finset.mem_filter] at ha
      exact ⟨(r, a), by simp [S1, hr, ha.1, ha.2], rfl⟩
  let R : Finset ℤ := A.filter (fun r => A.card ≤ 2 * deg r)
  have hR_card : 4 * A.card ≤ 5 * R.card := by
    have hpart : S1.card = ∑ r ∈ R, deg r + ∑ r ∈ A \ R, deg r := by
      rw [hS1_sum, add_comm, Finset.sum_sdiff (Finset.filter_subset _ _)]
    have h1 : ∑ r ∈ R, deg r ≤ R.card * A.card := by
      calc ∑ r ∈ R, deg r ≤ ∑ _r ∈ R, A.card :=
            Finset.sum_le_sum fun r _ => Finset.card_filter_le _ _
        _ = R.card * A.card := by rw [Finset.sum_const, smul_eq_mul]
    have h2 : 2 * ∑ r ∈ A \ R, deg r ≤ (A \ R).card * A.card := by
      rw [Finset.mul_sum]
      calc ∑ r ∈ A \ R, 2 * deg r ≤ ∑ _r ∈ A \ R, A.card := by
            refine Finset.sum_le_sum fun r hr => ?_
            simp only [Finset.mem_sdiff, R, Finset.mem_filter] at hr
            have : 2 * deg r < A.card := by
              by_contra hge; exact hr.2 ⟨hr.1, not_lt.1 hge⟩
            exact le_of_lt this
        _ = (A \ R).card * A.card := by rw [Finset.sum_const, smul_eq_mul]
    have hRsub : R.card ≤ A.card := Finset.card_filter_le _ _
    have hsdiff : (A \ R).card = A.card - R.card :=
      Finset.card_sdiff_of_subset (Finset.filter_subset _ _)
    have hS1_lb : 9 * A.card ^ 2 ≤ 10 * S1.card := by rwa [hS1_card]
    have h2S1 : 2 * S1.card ≤ 2 * (R.card * A.card) + (A.card - R.card) * A.card := by
      rw [← hsdiff]; omega
    have hsub_mul : (A.card - R.card) * A.card + R.card * A.card = A.card ^ 2 := by
      rw [← add_mul, Nat.sub_add_cancel hRsub, sq]
    have hfactor : (4 * A.card) * A.card ≤ (5 * R.card) * A.card := by
      have h9 : 9 * A.card ^ 2 ≤ 10 * (R.card * A.card) + 5 * ((A.card - R.card) * A.card) := by
        omega
      have h4 : 4 * A.card ^ 2 ≤ 5 * (R.card * A.card) := by omega
      calc (4 * A.card) * A.card = 4 * A.card ^ 2 := by ring
        _ ≤ 5 * (R.card * A.card) := h4
        _ = (5 * R.card) * A.card := by ring
    exact Nat.le_of_mul_le_mul_right hfactor hApos
  -- Step 3: Inclusion-exclusion for triples S = {(r, a1, a2) ∈ R × A^2 | r-a1, r-a2, a1-a2 ∈ P}
  let S : Finset (ℤ × ℤ × ℤ) :=
    (R ×ˢ (A ×ˢ A)).filter (fun t => t.1 - t.2.1 ∈ P ∧ t.1 - t.2.2 ∈ P ∧ t.2.1 - t.2.2 ∈ P)
  have hS_card : 3 * A.card ^ 3 ≤ 25 * S.card := by
    have hfib : S.card = ∑ r ∈ R,
        ((A ×ˢ A).filter (fun p => r - p.1 ∈ P ∧ r - p.2 ∈ P ∧ p.1 - p.2 ∈ P)).card := by
      have h1 := Finset.card_eq_sum_card_fiberwise (s := S) (t := R) (f := Prod.fst)
        (fun t ht => (Finset.mem_product.1 (Finset.mem_filter.1 ht).1).1)
      rw [h1]
      refine Finset.sum_congr rfl fun r hr => ?_
      refine Finset.card_bij (fun t _ => t.2) ?_ ?_ ?_
      · intro t ht
        simp only [S, Finset.mem_filter, Finset.mem_product] at ht ⊢
        rcases ht with ⟨⟨⟨_, h12⟩, hP1, hP2, hP3⟩, rfl⟩
        exact ⟨h12, hP1, hP2, hP3⟩
      · intro t1 ht1 t2 ht2 h2
        simp only [Finset.mem_filter] at ht1 ht2
        exact Prod.ext (ht1.2.trans ht2.2.symm) h2
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_product] at hp
        exact ⟨(r, p), by simp [S, hr, hp.1.1, hp.1.2, hp.2.1, hp.2.2.1, hp.2.2.2], rfl⟩
    have hper_r : ∀ r ∈ R, 3 * A.card ^ 2 ≤
        20 * ((A ×ˢ A).filter (fun p => r - p.1 ∈ P ∧ r - p.2 ∈ P ∧ p.1 - p.2 ∈ P)).card := by
      intro r hr
      let Sr : Finset (ℤ × ℤ) := (A ×ˢ A).filter (fun p => r - p.1 ∈ P ∧ r - p.2 ∈ P)
      have hSr_card : A.card ^ 2 ≤ 4 * Sr.card := by
        have hprod : Sr = (A.filter (fun a => r - a ∈ P)) ×ˢ (A.filter (fun a => r - a ∈ P)) := by
          ext p; simp [Sr, and_assoc, and_left_comm]
        rw [hprod, Finset.card_product]
        have hr_deg : A.card ≤ 2 * deg r := (Finset.mem_filter.1 hr).2
        have hsq : A.card ^ 2 ≤ 4 * (deg r * deg r) := by nlinarith [hr_deg]
        simpa [deg] using hsq
      have hinter : (S1 ∩ Sr) =
          (A ×ˢ A).filter (fun p => r - p.1 ∈ P ∧ r - p.2 ∈ P ∧ p.1 - p.2 ∈ P) := by
        ext p; simp [S1, Sr, and_assoc, and_left_comm, and_comm]
      have hunion : (S1 ∪ Sr).card ≤ A.card ^ 2 := by
        calc (S1 ∪ Sr).card ≤ (A ×ˢ A).card :=
              Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ _)
                (Finset.filter_subset _ _))
          _ = A.card ^ 2 := by rw [Finset.card_product, sq]
      have hie := Finset.card_union_add_card_inter S1 Sr
      rw [hinter] at hie
      have hS1_lb : 9 * A.card ^ 2 ≤ 10 * S1.card := by rwa [hS1_card]
      omega
    have hsum_r : 3 * R.card * A.card ^ 2 ≤ 20 * S.card := by
      rw [hfib, Finset.mul_sum]
      calc 3 * R.card * A.card ^ 2 = ∑ _r ∈ R, 3 * A.card ^ 2 := by
            rw [Finset.sum_const, smul_eq_mul]; ring
        _ ≤ ∑ r ∈ R,
            20 * ((A ×ˢ A).filter (fun p => r - p.1 ∈ P ∧ r - p.2 ∈ P ∧ p.1 - p.2 ∈ P)).card :=
            Finset.sum_le_sum hper_r
    have hmul5 : 12 * A.card ^ 3 ≤ 100 * S.card := by
      calc 12 * A.card ^ 3 = 3 * (4 * A.card) * A.card ^ 2 := by ring
        _ ≤ 3 * (5 * R.card) * A.card ^ 2 := by gcongr
        _ = 5 * (3 * R.card * A.card ^ 2) := by ring
        _ ≤ 5 * (20 * S.card) := Nat.mul_le_mul_left 5 hsum_r
        _ = 100 * S.card := by ring
    omega
  -- Step 4: Project S → Y = {(p1, p2) ∈ P^2 | p1 - p2 ∈ P} via (r, a1, a2) ↦ (r - a2, r - a1)
  let Y : Finset (ℤ × ℤ) := (P ×ˢ P).filter (fun p => p.1 - p.2 ∈ P)
  have hY_card : Y.card = ∑ x ∈ P, delta P P x := by
    have h1 : Y.card = ∑ x ∈ P, (Y.filter (fun p => p.1 - p.2 = x)).card :=
      Finset.card_eq_sum_card_fiberwise (fun p hp => (Finset.mem_filter.1 hp).2)
    rw [h1]
    refine Finset.sum_congr rfl fun x hx => ?_
    unfold delta
    congr 1
    ext p
    simp only [Y, Finset.mem_filter]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2 ▸ hx⟩, h.2⟩⟩
  let proj (t : ℤ × ℤ × ℤ) : ℤ × ℤ := (t.1 - t.2.2, t.1 - t.2.1)
  have hproj_mem : ∀ t ∈ S, proj t ∈ Y := by
    intro t ht
    simp only [S, Finset.mem_filter, Finset.mem_product] at ht
    simp only [Y, proj, Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨ht.2.2.1, ht.2.1⟩,
      (by have h : t.1 - t.2.2 - (t.1 - t.2.1) = t.2.1 - t.2.2 := by ring
          rw [h]; exact ht.2.2.2)⟩
  have hcs := cs_projection S Y proj hproj_mem
  -- Step 5: Collisions ≤ E_3(A)
  have hcoll : ((S ×ˢ S).filter (fun q => proj q.1 = proj q.2)).card ≤ E3 A A := by
    have hE3 : E3 A A =
        ∑ d ∈ D,
          (((A ×ˢ A).filter (fun p => p.1 - p.2 = d)) ×ˢ
            (((A ×ˢ A).filter (fun p => p.1 - p.2 = d)) ×ˢ
             ((A ×ˢ A).filter (fun p => p.1 - p.2 = d)))).card := by
      unfold E3
      refine Finset.sum_congr rfl fun d _ => ?_
      simp only [Finset.card_product, delta]
      ring
    rw [hE3, ← Finset.card_sigma]
    refine Finset.card_le_card_of_injOn
      (fun q => ⟨q.1.1 - q.2.1, ((q.1.1, q.2.1), ((q.1.2.1, q.2.2.1), (q.1.2.2, q.2.2.2)))⟩)
      ?_ ?_
    · intro q hq
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, S, proj,
        Prod.mk.injEq] at hq
      rcases hq with ⟨⟨⟨⟨hr1, ha1, ha1'⟩, _⟩, ⟨⟨hr2, ha2, ha2'⟩, _⟩⟩, hpeq1, hpeq2⟩
      have hr1A : q.1.1 ∈ A := (Finset.mem_filter.1 hr1).1
      have hr2A : q.2.1 ∈ A := (Finset.mem_filter.1 hr2).1
      simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_product, Finset.mem_filter]
      refine ⟨Finset.mem_image.2 ⟨(q.1.1, q.2.1), Finset.mem_product.2 ⟨hr1A, hr2A⟩, rfl⟩,
        ⟨⟨hr1A, hr2A⟩, trivial⟩, ⟨⟨ha1, ha2⟩, by linarith⟩, ⟨⟨ha1', ha2'⟩, by linarith⟩⟩
    · intro q1 _ q2 _ heq
      have h2 := congrArg Sigma.snd heq
      simp only [Prod.mk.injEq] at h2
      rcases h2 with ⟨⟨h11, h21⟩, ⟨h121, h221⟩, ⟨h122, h222⟩⟩
      exact Prod.ext (Prod.ext h11 (Prod.ext h121 h122)) (Prod.ext h21 (Prod.ext h221 h222))
  -- Combine: (3 |A|^3)^2 ≤ (25 |S|)^2 ≤ 625 * |Y| * E_3(A)
  calc 9 * A.card ^ 6 = (3 * A.card ^ 3) ^ 2 := by ring
    _ ≤ (25 * S.card) ^ 2 := Nat.pow_le_pow_left hS_card 2
    _ = 625 * S.card ^ 2 := by ring
    _ ≤ 625 * (Y.card * ((S ×ˢ S).filter (fun q => proj q.1 = proj q.2)).card) :=
        Nat.mul_le_mul_left 625 hcs
    _ ≤ 625 * (Y.card * E3 A A) := Nat.mul_le_mul_left 625 (Nat.mul_le_mul_left _ hcoll)
    _ = 625 * E3 A A * ∑ x ∈ P, delta P P x := by rw [hY_card]; ring

/-- Unified double Cauchy-Schwarz lemma used for both Proposition `prop-ea` and `E(A, P)`. -/
lemma double_cs_energy_bound (A B X : Finset ℤ) (η : ℕ) (hX : ∀ x ∈ X, η ≤ delta A B x) :
    η ^ 4 * X.card ^ 4 ≤
      B.card ^ 2 * (∑ d ∈ diffSet A A, delta X X d) *
        (∑ z ∈ diffSet B B, delta A A z ^ 2 * delta B B z) := by
  let D := diffSet A A
  -- First CS: (η |X|)^2 ≤ |B| * ∑_{b ∈ B} (delta A X b)^2
  have h1 : η * X.card ≤ ∑ b ∈ B, delta A X b := by
    rw [← sum_delta_comm A B X]
    calc η * X.card = ∑ _x ∈ X, η := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ x ∈ X, delta A B x := Finset.sum_le_sum hX
  have hcs1 : (η * X.card) ^ 2 ≤ B.card * ∑ b ∈ B, (delta A X b) ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq B (fun _ => (1 : ℝ)) (fun b => (delta A X b : ℝ))
    simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at h
    have hnat : (∑ b ∈ B, delta A X b) ^ 2 ≤ B.card * ∑ b ∈ B, (delta A X b) ^ 2 := by
      exact_mod_cast h
    exact le_trans (Nat.pow_le_pow_left h1 2) hnat
  -- Rewrite ∑_{b ∈ B} (delta A X b)^2 as sum over pairs (x1, x2) ∈ X^2 with x1 - x2 ∈ D
  let P_good : Finset (ℤ × ℤ) := (X ×ˢ X).filter (fun p => p.1 - p.2 ∈ D)
  let cB (p : ℤ × ℤ) : ℕ := (B.filter (fun b => b + p.1 ∈ A ∧ b + p.2 ∈ A)).card
  have hexpand : ∑ b ∈ B, (delta A X b) ^ 2 = ∑ p ∈ P_good, cB p := by
    have hL : ∑ b ∈ B, (delta A X b) ^ 2 =
        ((B ×ˢ (X ×ˢ X)).filter (fun t => t.1 + t.2.1 ∈ A ∧ t.1 + t.2.2 ∈ A)).card := by
      have hs : ∑ b ∈ B, (delta A X b) ^ 2 =
          ∑ b ∈ B, ((X.filter (fun x => b + x ∈ A)) ×ˢ (X.filter (fun x => b + x ∈ A))).card := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.card_product, ← sq, delta_eq_card_filter_right]
        congr 2; ext x; simp [add_comm]
      rw [hs, ← Finset.card_sigma]
      refine Finset.card_bij (fun s _ => (s.1, s.2)) ?_ ?_ ?_
      · intro s hs
        simp only [Finset.mem_sigma, Finset.mem_product, Finset.mem_filter] at hs ⊢
        exact ⟨⟨hs.1, hs.2.1.1, hs.2.2.1⟩, hs.2.1.2, hs.2.2.2⟩
      · intro s1 _ s2 _ h
        simp only [Prod.mk.injEq] at h
        exact Sigma.ext h.1 (heq_of_eq h.2)
      · intro t ht
        simp only [Finset.mem_filter, Finset.mem_product] at ht
        exact ⟨⟨t.1, t.2⟩, by simp [ht.1.1, ht.1.2.1, ht.1.2.2, ht.2.1, ht.2.2], rfl⟩
    have hR : ∑ p ∈ P_good, cB p =
        ((B ×ˢ (X ×ˢ X)).filter (fun t => t.1 + t.2.1 ∈ A ∧ t.1 + t.2.2 ∈ A)).card := by
      rw [← Finset.card_sigma]
      refine Finset.card_bij (fun s _ => (s.2, s.1)) ?_ ?_ ?_
      · intro s hs
        simp only [Finset.mem_sigma, P_good, Finset.mem_filter, Finset.mem_product] at hs ⊢
        exact ⟨⟨hs.2.1, hs.1.1⟩, hs.2.2⟩
      · intro s1 _ s2 _ h
        simp only [Prod.mk.injEq] at h
        exact Sigma.ext h.2 (heq_of_eq h.1)
      · intro t ht
        simp only [Finset.mem_filter, Finset.mem_product] at ht
        refine ⟨⟨t.2, t.1⟩, ?_, rfl⟩
        simp only [Finset.mem_sigma, P_good, Finset.mem_filter, Finset.mem_product]
        have hdiff : t.2.1 - t.2.2 ∈ D :=
          Finset.mem_image.2 ⟨(t.1 + t.2.1, t.1 + t.2.2),
            Finset.mem_product.2 ⟨ht.2.1, ht.2.2⟩, by ring⟩
        exact ⟨⟨ht.1.2, hdiff⟩, ht.1.1, ht.2⟩
    rw [hL, hR]
  -- Second CS: (∑_{p ∈ P_good} cB p)^2 ≤ |P_good| * ∑_{p ∈ P_good} (cB p)^2
  have hcs2 : (∑ p ∈ P_good, cB p) ^ 2 ≤ P_good.card * ∑ p ∈ P_good, (cB p) ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq P_good (fun _ => (1 : ℝ)) (fun p => (cB p : ℝ))
    simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at h
    exact_mod_cast h
  have hPgood_card : P_good.card = ∑ d ∈ D, delta X X d := by
    have h1 := Finset.card_eq_sum_card_fiberwise (s := P_good) (t := D)
      (f := fun p : ℤ × ℤ => p.1 - p.2) (fun p hp => (Finset.mem_filter.1 hp).2)
    rw [h1]
    refine Finset.sum_congr rfl fun d hd => ?_
    unfold delta
    congr 1
    ext p
    simp only [P_good, Finset.mem_filter]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2 ▸ hd⟩, h.2⟩⟩
  -- Regroup ∑_{p ∈ P_good} (cB p)^2 ≤ ∑_{z ∈ B - B} delta A A z ^ 2 * delta B B z
  have hregroup : ∑ p ∈ P_good, (cB p) ^ 2 ≤
      ∑ z ∈ diffSet B B, delta A A z ^ 2 * delta B B z := by
    have hstep1 : ∑ p ∈ P_good, (cB p) ^ 2 ≤ ∑ p ∈ X ×ˢ X, (cB p) ^ 2 :=
      Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    have hstep2 : ∑ p ∈ X ×ˢ X, (cB p) ^ 2 =
        ∑ q ∈ B ×ˢ B, ((X.filter (fun x => q.1 + x ∈ A ∧ q.2 + x ∈ A)).card) ^ 2 := by
      have hLHS : ∑ p ∈ X ×ˢ X, (cB p) ^ 2 =
          (((X ×ˢ X) ×ˢ (B ×ˢ B)).filter
            (fun t => t.2.1 + t.1.1 ∈ A ∧ t.2.1 + t.1.2 ∈ A ∧
                      t.2.2 + t.1.1 ∈ A ∧ t.2.2 + t.1.2 ∈ A)).card := by
        have hs : ∑ p ∈ X ×ˢ X, (cB p) ^ 2 =
            ∑ p ∈ X ×ˢ X, ((B.filter (fun b => b + p.1 ∈ A ∧ b + p.2 ∈ A)) ×ˢ
              (B.filter (fun b => b + p.1 ∈ A ∧ b + p.2 ∈ A))).card := by
          refine Finset.sum_congr rfl fun p _ => by rw [Finset.card_product, sq]
        rw [hs, ← Finset.card_sigma]
        refine Finset.card_bij (fun s _ => (s.1, s.2)) ?_ ?_ ?_
        · intro s hs
          simp only [Finset.mem_sigma, Finset.mem_product, Finset.mem_filter] at hs ⊢
          exact ⟨⟨hs.1, hs.2.1.1, hs.2.2.1⟩, hs.2.1.2.1, hs.2.1.2.2, hs.2.2.2.1, hs.2.2.2.2⟩
        · intro s1 _ s2 _ h
          simp only [Prod.mk.injEq] at h
          exact Sigma.ext h.1 (heq_of_eq h.2)
        · intro t ht
          simp only [Finset.mem_filter, Finset.mem_product] at ht
          exact ⟨⟨t.1, t.2⟩, by simp [ht.1.1, ht.1.2.1, ht.1.2.2, ht.2.1, ht.2.2.1, ht.2.2.2.1,
            ht.2.2.2.2], rfl⟩
      have hRHS : ∑ q ∈ B ×ˢ B, ((X.filter (fun x => q.1 + x ∈ A ∧ q.2 + x ∈ A)).card) ^ 2 =
          (((X ×ˢ X) ×ˢ (B ×ˢ B)).filter
            (fun t => t.2.1 + t.1.1 ∈ A ∧ t.2.1 + t.1.2 ∈ A ∧
                      t.2.2 + t.1.1 ∈ A ∧ t.2.2 + t.1.2 ∈ A)).card := by
        have hs : ∑ q ∈ B ×ˢ B, ((X.filter (fun x => q.1 + x ∈ A ∧ q.2 + x ∈ A)).card) ^ 2 =
            ∑ q ∈ B ×ˢ B, ((X.filter (fun x => q.1 + x ∈ A ∧ q.2 + x ∈ A)) ×ˢ
              (X.filter (fun x => q.1 + x ∈ A ∧ q.2 + x ∈ A))).card := by
          refine Finset.sum_congr rfl fun q _ => by rw [Finset.card_product, sq]
        rw [hs, ← Finset.card_sigma]
        refine Finset.card_bij (fun s _ => (s.2, s.1)) ?_ ?_ ?_
        · intro s hs
          simp only [Finset.mem_sigma, Finset.mem_product, Finset.mem_filter] at hs ⊢
          exact ⟨⟨⟨hs.2.1.1, hs.2.2.1⟩, hs.1⟩, hs.2.1.2.1, hs.2.2.2.1, hs.2.1.2.2, hs.2.2.2.2⟩
        · intro s1 _ s2 _ h
          simp only [Prod.mk.injEq] at h
          exact Sigma.ext h.2 (heq_of_eq h.1)
        · intro t ht
          simp only [Finset.mem_filter, Finset.mem_product] at ht
          exact ⟨⟨t.2, t.1⟩, by simp [ht.1.1.1, ht.1.1.2, ht.1.2, ht.2.1, ht.2.2.1, ht.2.2.2.1,
            ht.2.2.2.2], rfl⟩
      rw [hLHS, hRHS]
    have hstep3 : ∀ q ∈ B ×ˢ B,
        (X.filter (fun x => q.1 + x ∈ A ∧ q.2 + x ∈ A)).card ≤ delta A A (q.1 - q.2) := by
      intro q _
      unfold delta
      refine Finset.card_le_card_of_injOn (fun x => (q.1 + x, q.2 + x)) ?_ ?_
      · intro x hx
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hx ⊢
        exact ⟨⟨hx.2.1, hx.2.2⟩, by ring⟩
      · intro x1 _ x2 _ heq
        simp only [Prod.mk.injEq] at heq
        linarith
    have hstep4 : ∑ q ∈ B ×ˢ B, delta A A (q.1 - q.2) ^ 2 =
        ∑ z ∈ diffSet B B, delta A A z ^ 2 * delta B B z := by
      rw [← Finset.sum_fiberwise_of_maps_to (s := B ×ˢ B) (t := diffSet B B)
        (g := fun q : ℤ × ℤ => q.1 - q.2) (fun q hq => Finset.mem_image.2 ⟨q, hq, rfl⟩)]
      refine Finset.sum_congr rfl fun z _ => ?_
      have hcongr : ∑ q ∈ (B ×ˢ B).filter (fun q => q.1 - q.2 = z), delta A A (q.1 - q.2) ^ 2 =
          ∑ _q ∈ (B ×ˢ B).filter (fun q => q.1 - q.2 = z), delta A A z ^ 2 :=
        Finset.sum_congr rfl fun q hq => by rw [(Finset.mem_filter.1 hq).2]
      rw [hcongr, Finset.sum_const, smul_eq_mul, mul_comm]; rfl
    calc ∑ p ∈ P_good, (cB p) ^ 2
        ≤ ∑ p ∈ X ×ˢ X, (cB p) ^ 2 := hstep1
      _ = ∑ q ∈ B ×ˢ B, ((X.filter (fun x => q.1 + x ∈ A ∧ q.2 + x ∈ A)).card) ^ 2 := hstep2
      _ ≤ ∑ q ∈ B ×ˢ B, delta A A (q.1 - q.2) ^ 2 :=
          Finset.sum_le_sum fun q hq => Nat.pow_le_pow_left (hstep3 q hq) 2
      _ = ∑ z ∈ diffSet B B, delta A A z ^ 2 * delta B B z := hstep4
  -- Combine hcs1^2 and hcs2
  calc η ^ 4 * X.card ^ 4
      = ((η * X.card) ^ 2) ^ 2 := by ring
    _ ≤ (B.card * ∑ b ∈ B, (delta A X b) ^ 2) ^ 2 := Nat.pow_le_pow_left hcs1 2
    _ = B.card ^ 2 * (∑ p ∈ P_good, cB p) ^ 2 := by rw [hexpand]; ring
    _ ≤ B.card ^ 2 * (P_good.card * ∑ p ∈ P_good, (cB p) ^ 2) := Nat.mul_le_mul_left _ hcs2
    _ ≤ B.card ^ 2 * ((∑ d ∈ D, delta X X d) *
          (∑ z ∈ diffSet B B, delta A A z ^ 2 * delta B B z)) := by
        rw [hPgood_card]
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hregroup)
    _ = B.card ^ 2 * (∑ d ∈ D, delta X X d) *
          (∑ z ∈ diffSet B B, delta A A z ^ 2 * delta B B z) := by ring

/- ## Section 5: Cushman's Section 6 Energy Bounds in Pure Integer Powers -/

/-- Step 2 (`prop-ea` in integer powers): for any level set `U ⊆ D` with `delta A A x ≥ u`,
    `u^108 * |U|^45 ≤ 1728^35 * L^35 * |A|^114 * |D|^4`. -/
theorem prop_ea_integer (cs : ConvexSeq) (U : Finset ℤ) (u : ℕ)
    (hU : ∀ x ∈ U, u ≤ delta cs.toFinset cs.toFinset x) :
    let A := cs.toFinset
    let D := diffSet A A
    let L : ℝ := (Nat.log 2 cs.n + 1 : ℕ)
    (u : ℝ) ^ 108 * (U.card : ℝ) ^ 45 ≤
      (1728 : ℝ) ^ 35 * L ^ 35 * (cs.n : ℝ) ^ 114 * (D.card : ℝ) ^ 4 := by
  intro A D L
  rcases Nat.eq_zero_or_pos U.card with hU0 | hUpos
  · simp [hU0]; positivity
  have hAcard : A.card = cs.n := cs.card_toFinset
  have hE3A : (E3 A A : ℝ) ≤ 1728 * L * (cs.n : ℝ) ^ 3 := by
    have h := convex_E3_bound cs A
    rw [hAcard] at h
    have h' : (E3 A A : ℝ) ≤ 1728 * L * (cs.n : ℝ) * (cs.n : ℝ) ^ 2 := by
      dsimp only [L]; exact_mod_cast h
    linarith [show 1728 * L * (cs.n : ℝ) * (cs.n : ℝ) ^ 2 = 1728 * L * (cs.n : ℝ) ^ 3 by ring]
  have hE3AD : (E3 A D : ℝ) ≤ 1728 * L * (cs.n : ℝ) * (D.card : ℝ) ^ 2 := by
    dsimp only [L]; exact_mod_cast convex_E3_bound cs D
  -- From double_cs_energy_bound with B = A, X = U:
  have hdcs := double_cs_energy_bound A A U u hU
  have hsum_E3 : ∑ z ∈ D, delta A A z ^ 2 * delta A A z = E3 A A := by
    unfold E3; refine Finset.sum_congr rfl fun z _ => by ring
  rw [hsum_E3, hAcard] at hdcs
  -- Multiply by u and use sum_delta_comm + sum_delta_mul_delta_le_comm
  have hstep_u : u ^ 5 * U.card ^ 4 ≤
      cs.n ^ 2 * E3 A A * ∑ y ∈ diffSet A D, delta A D y * delta A U y := by
    have h1 : u * ∑ d ∈ D, delta U U d ≤ ∑ y ∈ diffSet A D, delta A D y * delta A U y := by
      rw [sum_delta_comm U U D]
      calc u * ∑ x ∈ U, delta U D x
          = ∑ x ∈ U, u * delta U D x := Finset.mul_sum _ _ _
        _ ≤ ∑ x ∈ U, delta A A x * delta U D x :=
            Finset.sum_le_sum fun x hx => Nat.mul_le_mul_right _ (hU x hx)
        _ ≤ ∑ y ∈ diffSet A U, delta A U y * delta A D y :=
            sum_delta_mul_delta_le_comm A A U D U
        _ = ∑ y ∈ diffSet A U, delta A D y * delta A U y :=
            Finset.sum_congr rfl fun y _ => mul_comm _ _
        _ ≤ ∑ y ∈ diffSet A D, delta A D y * delta A U y := by
            have hsub := sum_delta_mul_delta_le_comm A D A U (diffSet A U)
            -- Use direct support restriction instead:
            calc ∑ y ∈ diffSet A U, delta A D y * delta A U y
                = ∑ y ∈ diffSet A U ∩ diffSet A D, delta A D y * delta A U y := by
                  symm
                  refine Finset.sum_subset Finset.inter_subset_left fun y hy1 hy2 => ?_
                  have hnot : y ∉ diffSet A D := fun h => hy2 (Finset.mem_inter.2 ⟨hy1, h⟩)
                  simp [delta_eq_zero_of_notMem A D hnot]
              _ ≤ ∑ y ∈ diffSet A D, delta A D y * delta A U y :=
                  Finset.sum_le_sum_of_subset Finset.inter_subset_right
    calc u ^ 5 * U.card ^ 4
        = u * (u ^ 4 * U.card ^ 4) := by ring
      _ ≤ u * (cs.n ^ 2 * (∑ d ∈ D, delta U U d) * E3 A A) := Nat.mul_le_mul_left u hdcs
      _ = cs.n ^ 2 * E3 A A * (u * ∑ d ∈ D, delta U U d) := by ring
      _ ≤ cs.n ^ 2 * E3 A A * ∑ y ∈ diffSet A D, delta A D y * delta A U y :=
          Nat.mul_le_mul_left _ h1
  -- Raise to 6th power and apply convex_sum_mul_delta_pow6
  have h6_sum := convex_sum_mul_delta_pow6 cs U (diffSet A D) (delta A D)
  have hstep6 : (u : ℝ) ^ 30 * (U.card : ℝ) ^ 24 ≤
      (1728 : ℝ) ^ 9 * L ^ 9 * (cs.n : ℝ) ^ 36 * (D.card : ℝ) ^ 4 * (U.card : ℝ) ^ 5 := by
    have hcast : (u : ℝ) ^ 5 * (U.card : ℝ) ^ 4 ≤
        (cs.n : ℝ) ^ 2 * (E3 A A : ℝ) *
          ((∑ y ∈ diffSet A D, delta A D y * delta A U y : ℕ) : ℝ) := by exact_mod_cast hstep_u
    have hpow6 : ((u : ℝ) ^ 5 * (U.card : ℝ) ^ 4) ^ 6 ≤
        ((cs.n : ℝ) ^ 2 * (E3 A A : ℝ) *
          ((∑ y ∈ diffSet A D, delta A D y * delta A U y : ℕ) : ℝ)) ^ 6 :=
      pow_le_pow_left₀ (by positivity) hcast 6
    have hE3AD_eq : ((∑ y ∈ diffSet A D, delta A D y ^ 3 : ℕ) : ℝ) = (E3 A D : ℝ) := rfl
    rw [hE3AD_eq] at h6_sum
    calc (u : ℝ) ^ 30 * (U.card : ℝ) ^ 24
        = ((u : ℝ) ^ 5 * (U.card : ℝ) ^ 4) ^ 6 := by ring
      _ ≤ ((cs.n : ℝ) ^ 2 * (E3 A A : ℝ)) ^ 6 *
            ((∑ y ∈ diffSet A D, delta A D y * delta A U y : ℕ) : ℝ) ^ 6 := by
          linarith [show ((cs.n : ℝ) ^ 2 * (E3 A A : ℝ) *
            ((∑ y ∈ diffSet A D, delta A D y * delta A U y : ℕ) : ℝ)) ^ 6 =
            ((cs.n : ℝ) ^ 2 * (E3 A A : ℝ)) ^ 6 *
            ((∑ y ∈ diffSet A D, delta A D y * delta A U y : ℕ) : ℝ) ^ 6 by ring]
      _ ≤ ((cs.n : ℝ) ^ 2 * (1728 * L * (cs.n : ℝ) ^ 3)) ^ 6 *
            (1728 * L * (cs.n : ℝ) ^ 4 * (U.card : ℝ) ^ 5 *
              (1728 * L * (cs.n : ℝ) * (D.card : ℝ) ^ 2) ^ 2) := by
          gcongr
          calc ((∑ y ∈ diffSet A D, delta A D y * delta A U y : ℕ) : ℝ) ^ 6
              ≤ 1728 * L * (cs.n : ℝ) ^ 4 * (U.card : ℝ) ^ 5 * (E3 A D : ℝ) ^ 2 := h6_sum
            _ ≤ 1728 * L * (cs.n : ℝ) ^ 4 * (U.card : ℝ) ^ 5 *
                  (1728 * L * (cs.n : ℝ) * (D.card : ℝ) ^ 2) ^ 2 := by gcongr
      _ = (1728 : ℝ) ^ 9 * L ^ 9 * (cs.n : ℝ) ^ 36 * (D.card : ℝ) ^ 4 * (U.card : ℝ) ^ 5 := by
          ring
  have hU5_pos : (0 : ℝ) < (U.card : ℝ) ^ 5 := by positivity
  have hpart1 : (u : ℝ) ^ 30 * (U.card : ℝ) ^ 19 ≤
      (1728 : ℝ) ^ 9 * L ^ 9 * (cs.n : ℝ) ^ 36 * (D.card : ℝ) ^ 4 := by
    refine le_of_mul_le_mul_right ?_ hU5_pos
    calc (u : ℝ) ^ 30 * (U.card : ℝ) ^ 19 * (U.card : ℝ) ^ 5
        = (u : ℝ) ^ 30 * (U.card : ℝ) ^ 24 := by ring
      _ ≤ (1728 : ℝ) ^ 9 * L ^ 9 * (cs.n : ℝ) ^ 36 * (D.card : ℝ) ^ 4 * (U.card : ℝ) ^ 5 :=
          hstep6
  -- Also u^3 * |U| ≤ E_3(A) ≤ 1728 * L * n^3
  have hpart2 : (u : ℝ) ^ 3 * (U.card : ℝ) ≤ 1728 * L * (cs.n : ℝ) ^ 3 := by
    have hnat : u ^ 3 * U.card ≤ E3 A A := by
      calc u ^ 3 * U.card = ∑ _x ∈ U, u ^ 3 := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
        _ ≤ ∑ x ∈ U, delta A A x ^ 3 := Finset.sum_le_sum fun x hx => Nat.pow_le_pow_left (hU x hx) 3
        _ ≤ E3 A A := sum_delta_pow_le_E3 A A U
    exact le_trans (by exact_mod_cast hnat) hE3A
  -- Interpolate: (u^3 * |U|)^26 * (u^30 * |U|^19) = u^108 * |U|^45
  calc (u : ℝ) ^ 108 * (U.card : ℝ) ^ 45
      = ((u : ℝ) ^ 3 * (U.card : ℝ)) ^ 26 * ((u : ℝ) ^ 30 * (U.card : ℝ) ^ 19) := by ring
    _ ≤ (1728 * L * (cs.n : ℝ) ^ 3) ^ 26 *
          ((1728 : ℝ) ^ 9 * L ^ 9 * (cs.n : ℝ) ^ 36 * (D.card : ℝ) ^ 4) := by
        gcongr
    _ = (1728 : ℝ) ^ 35 * L ^ 35 * (cs.n : ℝ) ^ 114 * (D.card : ℝ) ^ 4 := by ring

/-- Convexity of `x ↦ x^3` on `L` nonnegative terms: `(∑_{i < L} a_i)^3 ≤ L^2 * ∑_{i < L} a_i^3`. -/
lemma sum_pow_three_le {ι : Type*} (s : Finset ι) (f : ι → ℕ) :
    (∑ i ∈ s, f i) ^ 3 ≤ s.card ^ 2 * ∑ i ∈ s, f i ^ 3 := by
  have h1 : (∑ i ∈ s, (f i : ℝ)) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, (f i : ℝ) ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun i => (f i : ℝ))
    simpa [Finset.sum_const, nsmul_eq_mul] using h
  have h2 : (∑ i ∈ s, (f i : ℝ) ^ 2) ^ 2 ≤
      (∑ i ∈ s, (f i : ℝ)) * (∑ i ∈ s, (f i : ℝ) ^ 3) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq s
      (fun i => Real.sqrt (f i : ℝ)) (fun i => Real.sqrt (f i : ℝ) * (f i : ℝ))
    have hL : ∑ i ∈ s, Real.sqrt (f i : ℝ) * (Real.sqrt (f i : ℝ) * (f i : ℝ)) =
        ∑ i ∈ s, (f i : ℝ) ^ 2 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← mul_assoc, Real.mul_self_sqrt (Nat.cast_nonneg _), sq]
    have hR1 : ∑ i ∈ s, (Real.sqrt (f i : ℝ)) ^ 2 = ∑ i ∈ s, (f i : ℝ) :=
      Finset.sum_congr rfl fun i _ => Real.sq_sqrt (Nat.cast_nonneg _)
    have hR2 : ∑ i ∈ s, (Real.sqrt (f i : ℝ) * (f i : ℝ)) ^ 2 = ∑ i ∈ s, (f i : ℝ) ^ 3 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; ring
    rw [hL, hR1, hR2] at h
    exact h
  have hreal : (∑ i ∈ s, (f i : ℝ)) ^ 3 ≤ (s.card : ℝ) ^ 2 * ∑ i ∈ s, (f i : ℝ) ^ 3 := by
    rcases eq_or_lt_of_le (Finset.sum_nonneg (s := s) (fun i _ => Nat.cast_nonneg (f i) :
      ∀ i ∈ s, (0 : ℝ) ≤ f i)) with h0 | hpos
    · rw [← h0, zero_pow (by norm_num : 3 ≠ 0)]
      exact mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ => pow_nonneg (Nat.cast_nonneg _) 3)
    · have h4 : (∑ i ∈ s, (f i : ℝ)) ^ 4 ≤
          (s.card : ℝ) ^ 2 * ((∑ i ∈ s, (f i : ℝ)) * (∑ i ∈ s, (f i : ℝ) ^ 3)) := by
        calc (∑ i ∈ s, (f i : ℝ)) ^ 4
            = ((∑ i ∈ s, (f i : ℝ)) ^ 2) ^ 2 := by ring
          _ ≤ ((s.card : ℝ) * ∑ i ∈ s, (f i : ℝ) ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
          _ = (s.card : ℝ) ^ 2 * (∑ i ∈ s, (f i : ℝ) ^ 2) ^ 2 := by ring
          _ ≤ (s.card : ℝ) ^ 2 * ((∑ i ∈ s, (f i : ℝ)) * (∑ i ∈ s, (f i : ℝ) ^ 3)) := by gcongr
      refine le_of_mul_le_mul_right ?_ hpos
      linarith [show (∑ i ∈ s, (f i : ℝ)) ^ 3 * (∑ i ∈ s, (f i : ℝ)) =
          (∑ i ∈ s, (f i : ℝ)) ^ 4 by ring]
  exact_mod_cast hreal

/-- Step 3: Bound on `E_3(P, D)^2` in pure integer powers. -/
theorem E3_PD_sq_bound (cs : ConvexSeq) (hn : 1 ≤ cs.n) :
    let A := cs.toFinset
    let D := diffSet A A
    let P := D.filter (fun x => A.card ^ 2 ≤ 10 * D.card * delta A A x)
    let L : ℝ := (Nat.log 2 cs.n + 1 : ℕ)
    (cs.n : ℝ) ^ 6 * (E3 P D : ℝ) ^ 2 ≤
      64 * (10 : ℝ) ^ 6 * (1728 : ℝ) ^ 3 * L ^ 9 * (D.card : ℝ) ^ 11 := by
  intro A D P L
  have hAcard : A.card = cs.n := cs.card_toFinset
  let Lnat : ℕ := Nat.log 2 cs.n + 1
  let B_buck (i : ℕ) : Finset ℤ := dyadicBucket (sumSet A D) (sigma A D) i
  -- Pointwise bound: n^2 * delta P D x ≤ 10 * |D| * ∑_{i < L} 2^(i+1) * delta A (B_buck i) x
  have hpt : ∀ x ∈ diffSet P D,
      cs.n ^ 2 * delta P D x ≤
        10 * D.card * ∑ i ∈ Finset.range Lnat, 2 ^ (i + 1) * delta A (B_buck i) x := by
    intro x _
    -- First: n^2 * delta P D x ≤ 10 * |D| * r_{A - (A + D)}(x)
    have h1 : cs.n ^ 2 * delta P D x ≤
        10 * D.card * ∑ z ∈ sumSet A D,
          (if x + z ∈ A then 1 else 0) * sigma A D z := by
      have hLHS : cs.n ^ 2 * delta P D x =
          ∑ p ∈ (P ×ˢ D).filter (fun q => q.1 - q.2 = x), A.card ^ 2 := by
        rw [Finset.sum_const, smul_eq_mul, delta, hAcard, mul_comm]
      have hmid : ∑ p ∈ (P ×ˢ D).filter (fun q => q.1 - q.2 = x), A.card ^ 2 ≤
          10 * D.card * ∑ p ∈ (P ×ˢ D).filter (fun q => q.1 - q.2 = x), delta A A p.1 := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun q hq => ?_
        have hqP : q.1 ∈ P := (Finset.mem_product.1 (Finset.mem_filter.1 hq).1).1
        exact (Finset.mem_filter.1 hqP).2
      have htriple : ∑ q ∈ (P ×ˢ D).filter (fun q => q.1 - q.2 = x), delta A A q.1 ≤
          ∑ z ∈ sumSet A D, (if x + z ∈ A then 1 else 0) * sigma A D z := by
        -- Count (a1, a2, d) ∈ A × A × D with a1 - a2 - d = x
        have hL : ∑ q ∈ (P ×ˢ D).filter (fun q => q.1 - q.2 = x), delta A A q.1 ≤
            ((A ×ˢ (A ×ˢ D)).filter (fun t => t.1 - t.2.1 - t.2.2 = x)).card := by
          have hs : ∑ q ∈ (P ×ˢ D).filter (fun q => q.1 - q.2 = x), delta A A q.1 =
              (((P ×ˢ D).filter (fun q => q.1 - q.2 = x)).sigma
                (fun q => (A ×ˢ A).filter (fun r => r.1 - r.2 = q.1))).card := by
            rw [Finset.card_sigma]; rfl
          rw [hs]
          refine Finset.card_le_card_of_injOn (fun s => (s.2.1, (s.2.2, s.1.2))) ?_ ?_
          · intro s hs
            simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_filter,
              Finset.mem_product] at hs ⊢
            exact ⟨⟨hs.2.1.1, hs.2.1.2, hs.1.1.2⟩, by linarith [hs.1.2, hs.2.2]⟩
          · intro s1 hs1 s2 hs2 heq
            simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_filter,
              Finset.mem_product] at hs1 hs2
            simp only [Prod.mk.injEq] at heq
            have hq1 : s1.1.1 = s2.1.1 := by linarith [hs1.2.2, hs2.2.2, heq.1, heq.2.1]
            exact Sigma.ext (Prod.ext hq1 heq.2.2) (heq_of_eq (Prod.ext heq.1 heq.2.1))
        have hR : ((A ×ˢ (A ×ˢ D)).filter (fun t => t.1 - t.2.1 - t.2.2 = x)).card =
            ∑ z ∈ sumSet A D, (if x + z ∈ A then 1 else 0) * sigma A D z := by
          have hfib := Finset.card_eq_sum_card_fiberwise
            (s := (A ×ˢ (A ×ˢ D)).filter (fun t => t.1 - t.2.1 - t.2.2 = x))
            (t := sumSet A D)
            (f := fun t : ℤ × ℤ × ℤ => t.2.1 + t.2.2)
            (fun t ht => Finset.mem_image.2 ⟨t.2, (Finset.mem_product.1 (Finset.mem_filter.1 ht).1).2, rfl⟩)
          rw [hfib]
          refine Finset.sum_congr rfl fun z _ => ?_
          by_cases hxz : x + z ∈ A
          · simp only [if_pos hxz, one_mul, sigma]
            refine Finset.card_bij (fun t _ => t.2) ?_ ?_ ?_
            · intro t ht
              simp only [Finset.mem_filter, Finset.mem_product] at ht ⊢
              exact ⟨ht.1.1.2, ht.2⟩
            · intro t1 ht1 t2 ht2 h2
              simp only [Finset.mem_filter] at ht1 ht2
              have h1 : t1.1 = t2.1 := by linarith [ht1.1.2, ht2.1.2, ht1.2, ht2.2]
              exact Prod.ext h1 h2
            · intro p hp
              simp only [Finset.mem_filter, Finset.mem_product] at hp
              exact ⟨(x + z, p), by simp [hxz, hp.1.1, hp.1.2, hp.2]; linarith [hp.2], rfl⟩
          · simp only [if_neg hxz, zero_mul]
            rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
            intro t ht hsum
            simp only [Finset.mem_filter, Finset.mem_product] at ht
            have : t.1 = x + z := by linarith [ht.2, hsum]
            exact hxz (this ▸ ht.1.1)
        exact le_trans hL (le_of_eq hR)
      calc cs.n ^ 2 * delta P D x
          = ∑ p ∈ (P ×ˢ D).filter (fun q => q.1 - q.2 = x), A.card ^ 2 := hLHS
        _ ≤ 10 * D.card * ∑ p ∈ (P ×ˢ D).filter (fun q => q.1 - q.2 = x), delta A A p.1 := hmid
        _ ≤ 10 * D.card * ∑ z ∈ sumSet A D, (if x + z ∈ A then 1 else 0) * sigma A D z :=
            Nat.mul_le_mul_left _ htriple
    -- Dyadic decomposition of ∑_{z ∈ A + D} 1_A(x + z) * sigma A D z
    have hM : ∀ z ∈ sumSet A D, sigma A D z ≤ cs.n := fun z _ => by
      rw [← hAcard]; exact sigma_le_card_left A D z
    have hdyad := dyadic_sum_decomp (sumSet A D) (sigma A D)
      (fun z => (if x + z ∈ A then 1 else 0) * sigma A D z) cs.n hM (fun z _ h => by simp [h])
    have h2 : ∑ z ∈ sumSet A D, (if x + z ∈ A then 1 else 0) * sigma A D z ≤
        ∑ i ∈ Finset.range Lnat, 2 ^ (i + 1) * delta A (B_buck i) x := by
      rw [hdyad]
      refine Finset.sum_le_sum fun i _ => ?_
      have hcard_eq : delta A (B_buck i) x =
          ∑ z ∈ B_buck i, (if x + z ∈ A then 1 else 0) := by
        rw [delta_eq_card_filter_right, Finset.card_filter]
        refine Finset.sum_congr rfl fun z _ => by simp [add_comm]
      rw [hcard_eq, Finset.mul_sum]
      refine Finset.sum_le_sum fun z hz => ?_
      have hlt : sigma A D z < 2 ^ (i + 1) := (Finset.mem_filter.1 hz).2.2
      by_cases hxz : x + z ∈ A
      · simp [hxz, le_of_lt hlt]
      · simp [hxz]
    exact le_trans h1 (Nat.mul_le_mul_left _ h2)
  -- Cube both sides and sum over x ∈ diffSet P D
  let Rsum : ℕ := ∑ i ∈ Finset.range Lnat, (2 ^ i) ^ 3 * (B_buck i).card ^ 2
  have hE3_bound : cs.n ^ 6 * E3 P D ≤ 8000 * D.card ^ 3 * Lnat ^ 3 * 1728 * cs.n * Rsum := by
    calc cs.n ^ 6 * E3 P D
        = ∑ x ∈ diffSet P D, (cs.n ^ 2 * delta P D x) ^ 3 := by
          unfold E3; rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun x _ => by ring
      _ ≤ ∑ x ∈ diffSet P D,
            (10 * D.card * ∑ i ∈ Finset.range Lnat, 2 ^ (i + 1) * delta A (B_buck i) x) ^ 3 :=
          Finset.sum_le_sum fun x hx => Nat.pow_le_pow_left (hpt x hx) 3
      _ = 1000 * D.card ^ 3 *
            ∑ x ∈ diffSet P D,
              (∑ i ∈ Finset.range Lnat, 2 ^ (i + 1) * delta A (B_buck i) x) ^ 3 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun x _ => by ring
      _ ≤ 1000 * D.card ^ 3 *
            ∑ x ∈ diffSet P D,
              Lnat ^ 2 * ∑ i ∈ Finset.range Lnat, (2 ^ (i + 1) * delta A (B_buck i) x) ^ 3 := by
          refine Nat.mul_le_mul_left _ (Finset.sum_le_sum fun x _ => ?_)
          have := sum_pow_three_le (Finset.range Lnat) (fun i => 2 ^ (i + 1) * delta A (B_buck i) x)
          simpa [Finset.card_range] using this
      _ = 1000 * D.card ^ 3 * Lnat ^ 2 *
            ∑ i ∈ Finset.range Lnat,
              (2 ^ (i + 1)) ^ 3 * ∑ x ∈ diffSet P D, (delta A (B_buck i) x) ^ 3 := by
          rw [← Finset.mul_sum, Finset.sum_comm]
          have : ∑ i ∈ Finset.range Lnat,
              ∑ x ∈ diffSet P D, (2 ^ (i + 1) * delta A (B_buck i) x) ^ 3 =
              ∑ i ∈ Finset.range Lnat,
                (2 ^ (i + 1)) ^ 3 * ∑ x ∈ diffSet P D, (delta A (B_buck i) x) ^ 3 := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun x _ => by ring
          rw [this]; ring
      _ ≤ 1000 * D.card ^ 3 * Lnat ^ 2 *
            ∑ i ∈ Finset.range Lnat,
              (8 * (2 ^ i) ^ 3) * (1728 * Lnat * cs.n * (B_buck i).card ^ 2) := by
          refine Nat.mul_le_mul_left _ (Finset.sum_le_sum fun i _ => ?_)
          have h2 : (2 ^ (i + 1)) ^ 3 = 8 * (2 ^ i) ^ 3 := by ring
          rw [h2]
          exact Nat.mul_le_mul_left _
            (le_trans (sum_delta_pow_le_E3 A (B_buck i) (diffSet P D)) (convex_E3_bound cs (B_buck i)))
      _ = 8000 * D.card ^ 3 * Lnat ^ 3 * 1728 * cs.n * Rsum := by
          have : ∑ i ∈ Finset.range Lnat,
              8 * (2 ^ i) ^ 3 * (1728 * Lnat * cs.n * (B_buck i).card ^ 2) =
              8 * 1728 * Lnat * cs.n * Rsum := by
            unfold Rsum; rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => by ring
          rw [this]; ring
  -- Bound Rsum^2: for each i, ((2^i)^3 * |B_i|^2)^2 = (2^i * |B_i|)^3 * ((2^i)^3 * |B_i|)
  have hterm_sq : ∀ i ∈ Finset.range Lnat,
      ((2 ^ i) ^ 3 * (B_buck i).card ^ 2) ^ 2 ≤ 1728 * Lnat * cs.n ^ 4 * D.card ^ 5 := by
    intro i _
    have hsum1 : 2 ^ i * (B_buck i).card ≤ cs.n * D.card := by
      calc 2 ^ i * (B_buck i).card
          = ∑ _z ∈ B_buck i, 2 ^ i := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
        _ ≤ ∑ z ∈ B_buck i, sigma A D z :=
            Finset.sum_le_sum fun z hz => (Finset.mem_filter.1 hz).2.1
        _ = ∑ z ∈ B_buck i, delta A (D.image Neg.neg) z :=
            Finset.sum_congr rfl fun z _ => sigma_eq_delta_neg A D z
        _ ≤ A.card * (D.image Neg.neg).card := sum_delta_le_mul A (D.image Neg.neg) (B_buck i)
        _ = cs.n * D.card := by rw [hAcard, card_image_neg]
    have hsum3 : (2 ^ i) ^ 3 * (B_buck i).card ≤ 1728 * Lnat * cs.n * D.card ^ 2 := by
      calc (2 ^ i) ^ 3 * (B_buck i).card
          = ∑ _z ∈ B_buck i, (2 ^ i) ^ 3 := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
        _ ≤ ∑ z ∈ B_buck i, (sigma A D z) ^ 3 :=
            Finset.sum_le_sum fun z hz => Nat.pow_le_pow_left (Finset.mem_filter.1 hz).2.1 3
        _ = ∑ z ∈ B_buck i, (delta A (D.image Neg.neg) z) ^ 3 :=
            Finset.sum_congr rfl fun z _ => by rw [sigma_eq_delta_neg]
        _ ≤ E3 A (D.image Neg.neg) := sum_delta_pow_le_E3 A (D.image Neg.neg) (B_buck i)
        _ ≤ 1728 * Lnat * cs.n * (D.image Neg.neg).card ^ 2 := convex_E3_bound cs (D.image Neg.neg)
        _ = 1728 * Lnat * cs.n * D.card ^ 2 := by rw [card_image_neg]
    calc ((2 ^ i) ^ 3 * (B_buck i).card ^ 2) ^ 2
        = (2 ^ i * (B_buck i).card) ^ 3 * ((2 ^ i) ^ 3 * (B_buck i).card) := by ring
      _ ≤ (cs.n * D.card) ^ 3 * (1728 * Lnat * cs.n * D.card ^ 2) := by gcongr
      _ = 1728 * Lnat * cs.n ^ 4 * D.card ^ 5 := by ring
  have hRsum_sq : Rsum ^ 2 ≤ Lnat ^ 2 * (1728 * Lnat * cs.n ^ 4 * D.card ^ 5) := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range Lnat)
      (fun _ => (1 : ℝ)) (fun i => (((2 ^ i) ^ 3 * (B_buck i).card ^ 2 : ℕ) : ℝ))
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hcs
    have hcs_nat : Rsum ^ 2 ≤ Lnat * ∑ i ∈ Finset.range Lnat, ((2 ^ i) ^ 3 * (B_buck i).card ^ 2) ^ 2 := by
      exact_mod_cast hcs
    calc Rsum ^ 2
        ≤ Lnat * ∑ i ∈ Finset.range Lnat, ((2 ^ i) ^ 3 * (B_buck i).card ^ 2) ^ 2 := hcs_nat
      _ ≤ Lnat * ∑ _i ∈ Finset.range Lnat, (1728 * Lnat * cs.n ^ 4 * D.card ^ 5) :=
          Nat.mul_le_mul_left _ (Finset.sum_le_sum hterm_sq)
      _ = Lnat ^ 2 * (1728 * Lnat * cs.n ^ 4 * D.card ^ 5) := by
          rw [Finset.sum_const, Finset.card_range, smul_eq_mul]; ring
  -- Square hE3_bound and cancel n^6
  have hsq : (cs.n : ℝ) ^ 12 * (E3 P D : ℝ) ^ 2 ≤
      64 * (10 : ℝ) ^ 6 * (1728 : ℝ) ^ 3 * L ^ 9 * (D.card : ℝ) ^ 11 * (cs.n : ℝ) ^ 6 := by
    have h1 : ((cs.n ^ 6 * E3 P D : ℕ) : ℝ) ^ 2 ≤
        ((8000 * D.card ^ 3 * Lnat ^ 3 * 1728 * cs.n * Rsum : ℕ) : ℝ) ^ 2 := by
      exact_mod_cast Nat.pow_le_pow_left hE3_bound 2
    have h2 : (Rsum : ℝ) ^ 2 ≤ L ^ 2 * (1728 * L * (cs.n : ℝ) ^ 4 * (D.card : ℝ) ^ 5) := by
      dsimp only [L]; exact_mod_cast hRsum_sq
    calc (cs.n : ℝ) ^ 12 * (E3 P D : ℝ) ^ 2
        = ((cs.n ^ 6 * E3 P D : ℕ) : ℝ) ^ 2 := by push_cast; ring
      _ ≤ ((8000 * D.card ^ 3 * Lnat ^ 3 * 1728 * cs.n * Rsum : ℕ) : ℝ) ^ 2 := h1
      _ = 64 * (10 : ℝ) ^ 6 * (1728 : ℝ) ^ 2 * L ^ 6 * (D.card : ℝ) ^ 6 * (cs.n : ℝ) ^ 2 *
            (Rsum : ℝ) ^ 2 := by push_cast [L, Lnat]; ring
      _ ≤ 64 * (10 : ℝ) ^ 6 * (1728 : ℝ) ^ 2 * L ^ 6 * (D.card : ℝ) ^ 6 * (cs.n : ℝ) ^ 2 *
            (L ^ 2 * (1728 * L * (cs.n : ℝ) ^ 4 * (D.card : ℝ) ^ 5)) := by gcongr
      _ = 64 * (10 : ℝ) ^ 6 * (1728 : ℝ) ^ 3 * L ^ 9 * (D.card : ℝ) ^ 11 * (cs.n : ℝ) ^ 6 := by
          ring
  have hn6_pos : (0 : ℝ) < (cs.n : ℝ) ^ 6 := by positivity
  refine le_of_mul_le_mul_right ?_ hn6_pos
  linarith [show (cs.n : ℝ) ^ 6 * (E3 P D : ℝ) ^ 2 * (cs.n : ℝ) ^ 6 =
      (cs.n : ℝ) ^ 12 * (E3 P D : ℝ) ^ 2 by ring]

/-- Step 4: Bound on `(∑_{x ∈ D} delta T T x)^6` for any `T` with `delta A P x ≥ η`. -/
theorem first_factor_pow6_bound (cs : ConvexSeq) (hn : 1 ≤ cs.n) (T : Finset ℤ) (η : ℕ)
    (hT : ∀ x ∈ T, η ≤ delta cs.toFinset
      ((diffSet cs.toFinset cs.toFinset).filter
        (fun x => cs.toFinset.card ^ 2 ≤
          10 * (diffSet cs.toFinset cs.toFinset).card * delta cs.toFinset cs.toFinset x)) x) :
    let A := cs.toFinset
    let D := diffSet A A
    let L : ℝ := (Nat.log 2 cs.n + 1 : ℕ)
    (cs.n : ℝ) ^ 2 * (η : ℝ) ^ 6 * ((∑ d ∈ D, delta T T d : ℕ) : ℝ) ^ 6 ≤
      64 * (10 : ℝ) ^ 6 * (1728 : ℝ) ^ 4 * L ^ 10 * (T.card : ℝ) ^ 5 * (D.card : ℝ) ^ 11 := by
  intro A D L
  let P := D.filter (fun x => A.card ^ 2 ≤ 10 * D.card * delta A A x)
  have h1 : η * ∑ d ∈ D, delta T T d ≤ ∑ y ∈ diffSet P D, delta P D y * delta A T y := by
    rw [sum_delta_comm T T D]
    calc η * ∑ x ∈ T, delta T D x
        = ∑ x ∈ T, η * delta T D x := Finset.mul_sum _ _ _
      _ ≤ ∑ x ∈ T, delta A P x * delta T D x :=
          Finset.sum_le_sum fun x hx => Nat.mul_le_mul_right _ (hT x hx)
      _ ≤ ∑ y ∈ diffSet A T, delta A T y * delta P D y :=
          sum_delta_mul_delta_le_comm A P T D T
      _ = ∑ y ∈ diffSet A T, delta P D y * delta A T y :=
          Finset.sum_congr rfl fun y _ => mul_comm _ _
      _ ≤ ∑ y ∈ diffSet P D, delta P D y * delta A T y := by
          calc ∑ y ∈ diffSet A T, delta P D y * delta A T y
              = ∑ y ∈ diffSet A T ∩ diffSet P D, delta P D y * delta A T y := by
                symm
                refine Finset.sum_subset Finset.inter_subset_left fun y hy1 hy2 => ?_
                have hnot : y ∉ diffSet P D := fun h => hy2 (Finset.mem_inter.2 ⟨hy1, h⟩)
                simp [delta_eq_zero_of_notMem P D hnot]
            _ ≤ ∑ y ∈ diffSet P D, delta P D y * delta A T y :=
                Finset.sum_le_sum_of_subset Finset.inter_subset_right
  have h6 := convex_sum_mul_delta_pow6 cs T (diffSet P D) (delta P D)
  have hE3PD := E3_PD_sq_bound cs hn
  have hE3PD_eq : ((∑ y ∈ diffSet P D, delta P D y ^ 3 : ℕ) : ℝ) = (E3 P D : ℝ) := rfl
  rw [hE3PD_eq] at h6
  have hcast : ((η * ∑ d ∈ D, delta T T d : ℕ) : ℝ) ^ 6 ≤
      ((∑ y ∈ diffSet P D, delta P D y * delta A T y : ℕ) : ℝ) ^ 6 := by
    exact_mod_cast Nat.pow_le_pow_left h1 6
  have hmul : (cs.n : ℝ) ^ 6 * ((η : ℝ) ^ 6 * ((∑ d ∈ D, delta T T d : ℕ) : ℝ) ^ 6) ≤
      64 * (10 : ℝ) ^ 6 * (1728 : ℝ) ^ 4 * L ^ 10 * (T.card : ℝ) ^ 5 * (D.card : ℝ) ^ 11 *
        (cs.n : ℝ) ^ 4 := by
    calc (cs.n : ℝ) ^ 6 * ((η : ℝ) ^ 6 * ((∑ d ∈ D, delta T T d : ℕ) : ℝ) ^ 6)
        = (cs.n : ℝ) ^ 6 * ((η * ∑ d ∈ D, delta T T d : ℕ) : ℝ) ^ 6 := by push_cast; ring
      _ ≤ (cs.n : ℝ) ^ 6 *
            (1728 * L * (cs.n : ℝ) ^ 4 * (T.card : ℝ) ^ 5 * (E3 P D : ℝ) ^ 2) := by
          gcongr; exact le_trans hcast h6
      _ = 1728 * L * (cs.n : ℝ) ^ 4 * (T.card : ℝ) ^ 5 * ((cs.n : ℝ) ^ 6 * (E3 P D : ℝ) ^ 2) := by
          ring
      _ ≤ 1728 * L * (cs.n : ℝ) ^ 4 * (T.card : ℝ) ^ 5 *
            (64 * (10 : ℝ) ^ 6 * (1728 : ℝ) ^ 3 * L ^ 9 * (D.card : ℝ) ^ 11) := by gcongr
      _ = 64 * (10 : ℝ) ^ 6 * (1728 : ℝ) ^ 4 * L ^ 10 * (T.card : ℝ) ^ 5 * (D.card : ℝ) ^ 11 *
            (cs.n : ℝ) ^ 4 := by ring
  have hn4_pos : (0 : ℝ) < (cs.n : ℝ) ^ 4 := by positivity
  refine le_of_mul_le_mul_right ?_ hn4_pos
  linarith [show (cs.n : ℝ) ^ 2 * (η : ℝ) ^ 6 * ((∑ d ∈ D, delta T T d : ℕ) : ℝ) ^ 6 *
      (cs.n : ℝ) ^ 4 =
      (cs.n : ℝ) ^ 6 * ((η : ℝ) ^ 6 * ((∑ d ∈ D, delta T T d : ℕ) : ℝ) ^ 6) by ring]

/-- Step 5: Bound on `S_AP^54 = (∑_{z ∈ P - P} delta A A z ^ 2 * delta P P z)^54`. -/
theorem second_factor_pow54_bound (cs : ConvexSeq) (hn : 1 ≤ cs.n) :
    let A := cs.toFinset
    let D := diffSet A A
    let P := D.filter (fun x => A.card ^ 2 ≤ 10 * D.card * delta A A x)
    let L : ℝ := (Nat.log 2 cs.n + 1 : ℕ)
    ((∑ z ∈ diffSet P P, delta A A z ^ 2 * delta P P z : ℕ) : ℝ) ^ 54 ≤
      (4096 * (10 : ℝ) ^ 6 * (1728 : ℝ) ^ 3) ^ 9 * (1728 : ℝ) ^ 35 *
        L ^ 116 * (cs.n : ℝ) ^ 60 * (D.card : ℝ) ^ 94 := by
  intro A D P L
  have hAcard : A.card = cs.n := cs.card_toFinset
  have hP_le_D : P.card ≤ D.card := Finset.card_filter_le _ _
  let Lnat : ℕ := Nat.log 2 cs.n + 1
  -- Restrict sum to D (since delta A A z = 0 outside D)
  have hsum_eq : ∑ z ∈ diffSet P P, delta A A z ^ 2 * delta P P z ≤
      ∑ z ∈ D, delta A A z ^ 2 * delta P P z := by
    calc ∑ z ∈ diffSet P P, delta A A z ^ 2 * delta P P z
        = ∑ z ∈ diffSet P P ∩ D, delta A A z ^ 2 * delta P P z := by
          symm
          refine Finset.sum_subset Finset.inter_subset_left fun z hz1 hz2 => ?_
          have hnot : z ∉ D := fun h => hz2 (Finset.mem_inter.2 ⟨hz1, h⟩)
          simp [delta_eq_zero_of_notMem A A hnot]
      _ ≤ ∑ z ∈ D, delta A A z ^ 2 * delta P P z :=
          Finset.sum_le_sum_of_subset Finset.inter_subset_right
  -- Dyadic pigeonhole on D by delta A A z
  have hM : ∀ z ∈ D, delta A A z ≤ cs.n := fun z _ => by
    rw [← hAcard]; exact delta_le_card_left A A z
  have hdyad := dyadic_sum_decomp D (delta A A)
    (fun z => delta A A z ^ 2 * delta P P z) cs.n hM (fun z _ h => by simp [h])
  obtain ⟨j, hjL, hjmax⟩ := exists_dyadic_max Lnat (by omega)
    (fun i => ∑ z ∈ dyadicBucket D (delta A A) i, delta A A z ^ 2 * delta P P z)
  let U : Finset ℤ := dyadicBucket D (delta A A) j
  let u : ℕ := 2 ^ j
  have hU_ge : ∀ x ∈ U, u ≤ delta A A x := fun x hx => (Finset.mem_filter.1 hx).2.1
  have hSAP_le : ∑ z ∈ diffSet P P, delta A A z ^ 2 * delta P P z ≤
      4 * Lnat * u ^ 2 * ∑ x ∈ U, delta P P x := by
    have hbuck : ∑ z ∈ U, delta A A z ^ 2 * delta P P z ≤ 4 * u ^ 2 * ∑ x ∈ U, delta P P x := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun z hz => ?_
      have hlt : delta A A z < 2 * u := by
        simpa [u, pow_succ, mul_comm] using (Finset.mem_filter.1 hz).2.2
      have hsq : delta A A z ^ 2 ≤ 4 * u ^ 2 := by
        calc delta A A z ^ 2 ≤ (2 * u) ^ 2 := Nat.pow_le_pow_left (le_of_lt hlt) 2
          _ = 4 * u ^ 2 := by ring
      exact Nat.mul_le_mul_right _ hsq
    calc ∑ z ∈ diffSet P P, delta A A z ^ 2 * delta P P z
        ≤ ∑ z ∈ D, delta A A z ^ 2 * delta P P z := hsum_eq
      _ = ∑ i ∈ Finset.range Lnat,
            ∑ z ∈ dyadicBucket D (delta A A) i, delta A A z ^ 2 * delta P P z := hdyad
      _ ≤ Lnat * ∑ z ∈ U, delta A A z ^ 2 * delta P P z := hjmax
      _ ≤ Lnat * (4 * u ^ 2 * ∑ x ∈ U, delta P P x) := Nat.mul_le_mul_left _ hbuck
      _ = 4 * Lnat * u ^ 2 * ∑ x ∈ U, delta P P x := by ring
  -- Bound ∑_{x ∈ U} delta P P x via definition of P and sum_delta_mul_delta_le_comm
  have hPU_bound : cs.n ^ 2 * ∑ x ∈ U, delta P P x ≤
      10 * D.card * ∑ y ∈ diffSet A P, delta A P y * delta A U y := by
    rw [sum_delta_comm P P U]
    calc cs.n ^ 2 * ∑ p ∈ P, delta P U p
        = ∑ p ∈ P, A.card ^ 2 * delta P U p := by rw [Finset.mul_sum, hAcard]
      _ ≤ ∑ p ∈ P, (10 * D.card * delta A A p) * delta P U p := by
          refine Finset.sum_le_sum fun p hp =>
            Nat.mul_le_mul_right _ (Finset.mem_filter.1 hp).2
      _ = 10 * D.card * ∑ p ∈ P, delta A A p * delta P U p := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun p _ => by ring
      _ ≤ 10 * D.card * ∑ y ∈ diffSet A P, delta A P y * delta A U y := by
          refine Nat.mul_le_mul_left _ ?_
          exact sum_delta_mul_delta_le_comm A A P U P
  -- Apply 6th power bound
  have h6 := convex_sum_mul_delta_pow6 cs U (diffSet A P) (delta A P)
  have hE3AP_eq : ((∑ y ∈ diffSet A P, delta A P y ^ 3 : ℕ) : ℝ) = (E3 A P : ℝ) := rfl
  rw [hE3AP_eq] at h6
  have hE3AP : (E3 A P : ℝ) ≤ 1728 * L * (cs.n : ℝ) * (D.card : ℝ) ^ 2 := by
    have h := convex_E3_bound cs P
    have h' : (E3 A P : ℝ) ≤ 1728 * L * (cs.n : ℝ) * (P.card : ℝ) ^ 2 := by
      dsimp only [L]; exact_mod_cast h
    have hP : (P.card : ℝ) ≤ (D.card : ℝ) := by exact_mod_cast hP_le_D
    calc (E3 A P : ℝ) ≤ 1728 * L * (cs.n : ℝ) * (P.card : ℝ) ^ 2 := h'
      _ ≤ 1728 * L * (cs.n : ℝ) * (D.card : ℝ) ^ 2 := by gcongr
  have hPU6 : (cs.n : ℝ) ^ 6 * ((∑ x ∈ U, delta P P x : ℕ) : ℝ) ^ 6 ≤
      (10 : ℝ) ^ 6 * (1728 : ℝ) ^ 3 * L ^ 3 * (D.card : ℝ) ^ 10 * (U.card : ℝ) ^ 5 := by
    have hcast0 : (cs.n : ℝ) ^ 2 * ((∑ x ∈ U, delta P P x : ℕ) : ℝ) ≤
        10 * (D.card : ℝ) * ((∑ y ∈ diffSet A P, delta A P y * delta A U y : ℕ) : ℝ) := by
      have h' : ((cs.n ^ 2 * ∑ x ∈ U, delta P P x : ℕ) : ℝ) ≤
          ((10 * D.card * ∑ y ∈ diffSet A P, delta A P y * delta A U y : ℕ) : ℝ) := by
        exact_mod_cast hPU_bound
      simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using h'
    have hcast : ((cs.n : ℝ) ^ 2 * ((∑ x ∈ U, delta P P x : ℕ) : ℝ)) ^ 6 ≤
        (10 * (D.card : ℝ) * ((∑ y ∈ diffSet A P, delta A P y * delta A U y : ℕ) : ℝ)) ^ 6 :=
      pow_le_pow_left₀ (by positivity) hcast0 6
    have h12 : (cs.n : ℝ) ^ 12 * ((∑ x ∈ U, delta P P x : ℕ) : ℝ) ^ 6 ≤
        (10 : ℝ) ^ 6 * (1728 : ℝ) ^ 3 * L ^ 3 * (D.card : ℝ) ^ 10 * (U.card : ℝ) ^ 5 *
          (cs.n : ℝ) ^ 6 := by
      calc (cs.n : ℝ) ^ 12 * ((∑ x ∈ U, delta P P x : ℕ) : ℝ) ^ 6
          = ((cs.n : ℝ) ^ 2 * ((∑ x ∈ U, delta P P x : ℕ) : ℝ)) ^ 6 := by ring
        _ ≤ (10 * (D.card : ℝ) * ((∑ y ∈ diffSet A P, delta A P y * delta A U y : ℕ) : ℝ)) ^ 6 :=
            hcast
        _ = (10 : ℝ) ^ 6 * (D.card : ℝ) ^ 6 *
              ((∑ y ∈ diffSet A P, delta A P y * delta A U y : ℕ) : ℝ) ^ 6 := by ring
        _ ≤ (10 : ℝ) ^ 6 * (D.card : ℝ) ^ 6 *
              (1728 * L * (cs.n : ℝ) ^ 4 * (U.card : ℝ) ^ 5 *
                (1728 * L * (cs.n : ℝ) * (D.card : ℝ) ^ 2) ^ 2) := by
            gcongr
            calc ((∑ y ∈ diffSet A P, delta A P y * delta A U y : ℕ) : ℝ) ^ 6
                ≤ 1728 * L * (cs.n : ℝ) ^ 4 * (U.card : ℝ) ^ 5 * (E3 A P : ℝ) ^ 2 := h6
              _ ≤ 1728 * L * (cs.n : ℝ) ^ 4 * (U.card : ℝ) ^ 5 *
                    (1728 * L * (cs.n : ℝ) * (D.card : ℝ) ^ 2) ^ 2 := by gcongr
        _ = (10 : ℝ) ^ 6 * (1728 : ℝ) ^ 3 * L ^ 3 * (D.card : ℝ) ^ 10 * (U.card : ℝ) ^ 5 *
              (cs.n : ℝ) ^ 6 := by ring
    have hn6_pos : (0 : ℝ) < (cs.n : ℝ) ^ 6 := by positivity
    refine le_of_mul_le_mul_right ?_ hn6_pos
    linarith [show (cs.n : ℝ) ^ 6 * ((∑ x ∈ U, delta P P x : ℕ) : ℝ) ^ 6 * (cs.n : ℝ) ^ 6 =
        (cs.n : ℝ) ^ 12 * ((∑ x ∈ U, delta P P x : ℕ) : ℝ) ^ 6 by ring]
  -- Combine with hSAP_le^6 and raise to 9th power, then plug in prop_ea_integer
  have hSAP6 : (cs.n : ℝ) ^ 6 *
      ((∑ z ∈ diffSet P P, delta A A z ^ 2 * delta P P z : ℕ) : ℝ) ^ 6 ≤
      (4096 * (10 : ℝ) ^ 6 * (1728 : ℝ) ^ 3) * L ^ 9 * (D.card : ℝ) ^ 10 *
        ((u : ℝ) ^ 12 * (U.card : ℝ) ^ 5) := by
    have hcast : ((∑ z ∈ diffSet P P, delta A A z ^ 2 * delta P P z : ℕ) : ℝ) ^ 6 ≤
        ((4 * Lnat * u ^ 2 * ∑ x ∈ U, delta P P x : ℕ) : ℝ) ^ 6 := by
      exact_mod_cast Nat.pow_le_pow_left hSAP_le 6
    calc (cs.n : ℝ) ^ 6 * ((∑ z ∈ diffSet P P, delta A A z ^ 2 * delta P P z : ℕ) : ℝ) ^ 6
        ≤ (cs.n : ℝ) ^ 6 * ((4 * Lnat * u ^ 2 * ∑ x ∈ U, delta P P x : ℕ) : ℝ) ^ 6 := by gcongr
      _ = 4096 * L ^ 6 * (u : ℝ) ^ 12 *
            ((cs.n : ℝ) ^ 6 * ((∑ x ∈ U, delta P P x : ℕ) : ℝ) ^ 6) := by
          push_cast [L, Lnat]; ring
      _ ≤ 4096 * L ^ 6 * (u : ℝ) ^ 12 *
            ((10 : ℝ) ^ 6 * (1728 : ℝ) ^ 3 * L ^ 3 * (D.card : ℝ) ^ 10 * (U.card : ℝ) ^ 5) := by
          gcongr
      _ = (4096 * (10 : ℝ) ^ 6 * (1728 : ℝ) ^ 3) * L ^ 9 * (D.card : ℝ) ^ 10 *
            ((u : ℝ) ^ 12 * (U.card : ℝ) ^ 5) := by ring
  have hpropea := prop_ea_integer cs U u hU_ge
  have h54 : (cs.n : ℝ) ^ 54 *
      ((∑ z ∈ diffSet P P, delta A A z ^ 2 * delta P P z : ℕ) : ℝ) ^ 54 ≤
      (4096 * (10 : ℝ) ^ 6 * (1728 : ℝ) ^ 3) ^ 9 * (1728 : ℝ) ^ 35 *
        L ^ 116 * (cs.n : ℝ) ^ 60 * (D.card : ℝ) ^ 94 * (cs.n : ℝ) ^ 54 := by
    calc (cs.n : ℝ) ^ 54 * ((∑ z ∈ diffSet P P, delta A A z ^ 2 * delta P P z : ℕ) : ℝ) ^ 54
        = ((cs.n : ℝ) ^ 6 * ((∑ z ∈ diffSet P P, delta A A z ^ 2 * delta P P z : ℕ) : ℝ) ^ 6) ^ 9 := by
          ring
      _ ≤ ((4096 * (10 : ℝ) ^ 6 * (1728 : ℝ) ^ 3) * L ^ 9 * (D.card : ℝ) ^ 10 *
            ((u : ℝ) ^ 12 * (U.card : ℝ) ^ 5)) ^ 9 := pow_le_pow_left₀ (by positivity) hSAP6 9
      _ = (4096 * (10 : ℝ) ^ 6 * (1728 : ℝ) ^ 3) ^ 9 * L ^ 81 * (D.card : ℝ) ^ 90 *
            ((u : ℝ) ^ 108 * (U.card : ℝ) ^ 45) := by ring
      _ ≤ (4096 * (10 : ℝ) ^ 6 * (1728 : ℝ) ^ 3) ^ 9 * L ^ 81 * (D.card : ℝ) ^ 90 *
            ((1728 : ℝ) ^ 35 * L ^ 35 * (cs.n : ℝ) ^ 114 * (D.card : ℝ) ^ 4) := by gcongr
      _ = (4096 * (10 : ℝ) ^ 6 * (1728 : ℝ) ^ 3) ^ 9 * (1728 : ℝ) ^ 35 *
            L ^ 116 * (cs.n : ℝ) ^ 60 * (D.card : ℝ) ^ 94 * (cs.n : ℝ) ^ 54 := by ring
  have hn54_pos : (0 : ℝ) < (cs.n : ℝ) ^ 54 := by positivity
  refine le_of_mul_le_mul_right ?_ hn54_pos
  linarith [show ((∑ z ∈ diffSet P P, delta A A z ^ 2 * delta P P z : ℕ) : ℝ) ^ 54 *
      (cs.n : ℝ) ^ 54 =
      (cs.n : ℝ) ^ 54 *
      ((∑ z ∈ diffSet P P, delta A A z ^ 2 * delta P P z : ℕ) : ℝ) ^ 54 by ring]

/-- Pure algebraic combination of Steps 4–8 (using plain real variables for instant elaboration). -/
private lemma cushman_combine_algebra
    (n d t eta e2 s1 s2 L C4 C5 K0 K1 K2 : ℝ)
    (hn : 0 < n) (hd : 0 ≤ d) (ht : 0 ≤ t) (heta : 0 ≤ eta) (he2 : 0 ≤ e2)
    (hs1 : 0 ≤ s1) (hs2 : 0 ≤ s2) (hL : 0 ≤ L)
    (hC4 : 0 < C4) (hC5 : 0 < C5) (hK0 : 0 < K0) (hK1 : 0 < K1) (hK2 : 0 < K2)
    (hE2_le : e2 ≤ 4 * L * (eta ^ 2 * t))
    (hdcs : eta ^ 4 * t ^ 4 ≤ d ^ 2 * s1 * s2)
    (h4 : n ^ 2 * eta ^ 6 * s1 ^ 6 ≤ C4 * L ^ 10 * t ^ 5 * d ^ 11)
    (h5 : s2 ^ 54 ≤ C5 * L ^ 116 * n ^ 60 * d ^ 94)
    (hE3T : eta ^ 3 * t ≤ 1728 * L * n * d ^ 2)
    (hK0_eq : K0 = (1728 : ℝ) ^ 72)
    (hK1_eq : K1 = (4 : ℝ) ^ 243)
    (hK2_eq : K2 = ((6250 : ℝ) / 9 * 1728) ^ 243)
    (hn5 : n ^ 5 ≤ (6250 : ℝ) / 9 * 1728 * L * d * e2) :
    n ^ 1101 ≤ (K2 * K1 * K0 * C4 ^ 9 * C5) * L ^ 764 * d ^ 688 := by
  have hn_nn : 0 ≤ n := le_of_lt hn
  have hC4_nn : 0 ≤ C4 := le_of_lt hC4
  have hC5_nn : 0 ≤ C5 := le_of_lt hC5
  have hK0_nn : 0 ≤ K0 := le_of_lt hK0
  have hK1_nn : 0 ≤ K1 := le_of_lt hK1
  have hK2_nn : 0 ≤ K2 := le_of_lt hK2
  have hstep6 : eta ^ 270 * t ^ 171 ≤ C4 ^ 9 * C5 * L ^ 206 * n ^ 42 * d ^ 301 := by
    rcases eq_or_lt_of_le ht with rfl | ht_pos
    · rw [zero_pow (Nat.succ_ne_zero 170), mul_zero]
      exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hC4_nn 9) hC5_nn)
        (pow_nonneg hL 206)) (pow_nonneg hn_nn 42)) (pow_nonneg hd 301)
    have hpow54 : (eta ^ 4 * t ^ 4) ^ 54 ≤ (d ^ 2 * s1 * s2) ^ 54 :=
      pow_le_pow_left₀ (mul_nonneg (pow_nonneg heta 4) (pow_nonneg ht 4)) hdcs 54
    have h4_9 : (n ^ 2 * eta ^ 6 * s1 ^ 6) ^ 9 ≤ (C4 * L ^ 10 * t ^ 5 * d ^ 11) ^ 9 :=
      pow_le_pow_left₀
        (mul_nonneg (mul_nonneg (pow_nonneg hn_nn 2) (pow_nonneg heta 6)) (pow_nonneg hs1 6))
        h4 9
    have hcomb : n ^ 18 * eta ^ 270 * t ^ 216 ≤
        C4 ^ 9 * C5 * L ^ 206 * n ^ 42 * d ^ 301 * (n ^ 18 * t ^ 45) := by
      have h1 : n ^ 18 * eta ^ 54 * (eta ^ 4 * t ^ 4) ^ 54 ≤
          n ^ 18 * eta ^ 54 * (d ^ 2 * s1 * s2) ^ 54 :=
        mul_le_mul_of_nonneg_left hpow54 (mul_nonneg (pow_nonneg hn_nn 18) (pow_nonneg heta 54))
      have h2 : d ^ 108 * (n ^ 2 * eta ^ 6 * s1 ^ 6) ^ 9 * s2 ^ 54 ≤
          d ^ 108 * (C4 * L ^ 10 * t ^ 5 * d ^ 11) ^ 9 * (C5 * L ^ 116 * n ^ 60 * d ^ 94) :=
        mul_le_mul
          (mul_le_mul_of_nonneg_left h4_9 (pow_nonneg hd 108))
          h5 (pow_nonneg hs2 54)
          (mul_nonneg (pow_nonneg hd 108)
            (pow_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC4_nn (pow_nonneg hL 10))
              (pow_nonneg ht 5)) (pow_nonneg hd 11)) 9))
      calc n ^ 18 * eta ^ 270 * t ^ 216
          = n ^ 18 * eta ^ 54 * (eta ^ 4 * t ^ 4) ^ 54 := by ring
        _ ≤ n ^ 18 * eta ^ 54 * (d ^ 2 * s1 * s2) ^ 54 := h1
        _ = d ^ 108 * (n ^ 2 * eta ^ 6 * s1 ^ 6) ^ 9 * s2 ^ 54 := by ring
        _ ≤ d ^ 108 * (C4 * L ^ 10 * t ^ 5 * d ^ 11) ^ 9 * (C5 * L ^ 116 * n ^ 60 * d ^ 94) := h2
        _ = C4 ^ 9 * C5 * L ^ 206 * n ^ 42 * d ^ 301 * (n ^ 18 * t ^ 45) := by ring
    have hpos_cancel : 0 < n ^ 18 * t ^ 45 := mul_pos (pow_pos hn 18) (pow_pos ht_pos 45)
    refine le_of_mul_le_mul_right ?_ hpos_cancel
    calc eta ^ 270 * t ^ 171 * (n ^ 18 * t ^ 45)
        = n ^ 18 * eta ^ 270 * t ^ 216 := by ring
      _ ≤ C4 ^ 9 * C5 * L ^ 206 * n ^ 42 * d ^ 301 * (n ^ 18 * t ^ 45) := hcomb
  have hpow72 : (eta ^ 3 * t) ^ 72 ≤ K0 * L ^ 72 * n ^ 72 * d ^ 144 := by
    calc (eta ^ 3 * t) ^ 72
        ≤ (1728 * L * n * d ^ 2) ^ 72 :=
          pow_le_pow_left₀ (mul_nonneg (pow_nonneg heta 3) ht) hE3T 72
      _ = (1728 : ℝ) ^ 72 * L ^ 72 * n ^ 72 * d ^ 144 := by
          simp only [mul_pow, ← pow_mul]
      _ = K0 * L ^ 72 * n ^ 72 * d ^ 144 := by rw [hK0_eq]
  have hstep7 : (eta ^ 2 * t) ^ 243 ≤ K0 * C4 ^ 9 * C5 * L ^ 278 * n ^ 114 * d ^ 445 := by
    have hmul : (eta ^ 3 * t) ^ 72 * (eta ^ 270 * t ^ 171) ≤
        (K0 * L ^ 72 * n ^ 72 * d ^ 144) * (C4 ^ 9 * C5 * L ^ 206 * n ^ 42 * d ^ 301) :=
      mul_le_mul hpow72 hstep6
        (mul_nonneg (pow_nonneg heta 270) (pow_nonneg ht 171))
        (mul_nonneg (mul_nonneg (mul_nonneg hK0_nn (pow_nonneg hL 72))
          (pow_nonneg hn_nn 72)) (pow_nonneg hd 144))
    calc (eta ^ 2 * t) ^ 243
        = (eta ^ 3 * t) ^ 72 * (eta ^ 270 * t ^ 171) := by ring
      _ ≤ (K0 * L ^ 72 * n ^ 72 * d ^ 144) * (C4 ^ 9 * C5 * L ^ 206 * n ^ 42 * d ^ 301) := hmul
      _ = K0 * C4 ^ 9 * C5 * L ^ 278 * n ^ 114 * d ^ 445 := by ring
  have hE2_243 : e2 ^ 243 ≤ K1 * K0 * C4 ^ 9 * C5 * L ^ 521 * n ^ 114 * d ^ 445 := by
    calc e2 ^ 243
        ≤ (4 * L * (eta ^ 2 * t)) ^ 243 := pow_le_pow_left₀ he2 hE2_le 243
      _ = K1 * L ^ 243 * (eta ^ 2 * t) ^ 243 := by rw [mul_pow, mul_pow, hK1_eq]
      _ ≤ K1 * L ^ 243 * (K0 * C4 ^ 9 * C5 * L ^ 278 * n ^ 114 * d ^ 445) :=
          mul_le_mul_of_nonneg_left hstep7 (mul_nonneg hK1_nn (pow_nonneg hL 243))
      _ = K1 * K0 * C4 ^ 9 * C5 * L ^ 521 * n ^ 114 * d ^ 445 := by ring
  have hfinal : n ^ 1101 * n ^ 114 ≤
      ((K2 * K1 * K0 * C4 ^ 9 * C5) * L ^ 764 * d ^ 688) * n ^ 114 := by
    calc n ^ 1101 * n ^ 114
        = (n ^ 5) ^ 243 := by ring
      _ ≤ ((6250 : ℝ) / 9 * 1728 * L * d * e2) ^ 243 :=
          pow_le_pow_left₀ (pow_nonneg hn_nn 5) hn5 243
      _ = K2 * L ^ 243 * d ^ 243 * e2 ^ 243 := by
          rw [mul_pow, mul_pow, mul_pow, hK2_eq]
      _ ≤ K2 * L ^ 243 * d ^ 243 * (K1 * K0 * C4 ^ 9 * C5 * L ^ 521 * n ^ 114 * d ^ 445) :=
          mul_le_mul_of_nonneg_left hE2_243
            (mul_nonneg (mul_nonneg hK2_nn (pow_nonneg hL 243)) (pow_nonneg hd 243))
      _ = ((K2 * K1 * K0 * C4 ^ 9 * C5) * L ^ 764 * d ^ 688) * n ^ 114 := by ring
  exact le_of_mul_le_mul_right hfinal (pow_pos hn 114)

/-- Main Cushman convex difference-set theorem in pure integer powers:
    there exists an absolute constant `C > 0` such that every nonempty strictly convex
    sequence `cs` satisfies `n^1101 ≤ C * (Nat.log 2 n + 1)^764 * |A - A|^688`. -/
theorem cushman_convex_diff_poly :
    ∃ C : ℝ, 0 < C ∧ ∀ (cs : ConvexSeq), 1 ≤ cs.n →
      (cs.n : ℝ) ^ 1101 ≤
        C * ((Nat.log 2 cs.n + 1 : ℕ) : ℝ) ^ 764 *
          ((diffSet cs.toFinset cs.toFinset).card : ℝ) ^ 688 := by
  obtain ⟨C4, hC4_pos, hC4_eq⟩ :
      ∃ C4 : ℝ, 0 < C4 ∧ C4 = 64 * (10 : ℝ) ^ 6 * (1728 : ℝ) ^ 4 := ⟨_, by positivity, rfl⟩
  obtain ⟨C5, hC5_pos, hC5_eq⟩ :
      ∃ C5 : ℝ, 0 < C5 ∧
        C5 = (4096 * (10 : ℝ) ^ 6 * (1728 : ℝ) ^ 3) ^ 9 * (1728 : ℝ) ^ 35 :=
    ⟨_, by positivity, rfl⟩
  obtain ⟨K0, hK0_pos, hK0_eq⟩ : ∃ K0 : ℝ, 0 < K0 ∧ K0 = (1728 : ℝ) ^ 72 :=
    ⟨_, by positivity, rfl⟩
  obtain ⟨K1, hK1_pos, hK1_eq⟩ : ∃ K1 : ℝ, 0 < K1 ∧ K1 = (4 : ℝ) ^ 243 :=
    ⟨_, by positivity, rfl⟩
  obtain ⟨K2, hK2_pos, hK2_eq⟩ : ∃ K2 : ℝ, 0 < K2 ∧ K2 = ((6250 : ℝ) / 9 * 1728) ^ 243 :=
    ⟨_, by positivity, rfl⟩
  refine ⟨K2 * K1 * K0 * C4 ^ 9 * C5,
    mul_pos (mul_pos (mul_pos (mul_pos hK2_pos hK1_pos) hK0_pos) (pow_pos hC4_pos 9)) hC5_pos,
    fun cs hn => ?_⟩
  let A := cs.toFinset
  let D := diffSet A A
  let P := D.filter (fun x => A.card ^ 2 ≤ 10 * D.card * delta A A x)
  let Lnat : ℕ := Nat.log 2 cs.n + 1
  let L : ℝ := (Lnat : ℝ)
  have hAcard : A.card = cs.n := cs.card_toFinset
  have hP_le_D : P.card ≤ D.card := Finset.card_filter_le _ _
  have hP_le_D_R : (P.card : ℝ) ≤ (D.card : ℝ) := by exact_mod_cast hP_le_D
  -- Dyadic pigeonhole on E2 A P
  have hM : ∀ x ∈ diffSet A P, delta A P x ≤ cs.n := fun x _ => by
    rw [← hAcard]; exact delta_le_card_left A P x
  have hdyad := dyadic_sum_decomp (diffSet A P) (delta A P)
    (fun x => delta A P x ^ 2) cs.n hM (fun x _ h => by simp [h])
  obtain ⟨j, hjL, hjmax⟩ := exists_dyadic_max Lnat (by omega)
    (fun i => ∑ x ∈ dyadicBucket (diffSet A P) (delta A P) i, delta A P x ^ 2)
  let T : Finset ℤ := dyadicBucket (diffSet A P) (delta A P) j
  let η : ℕ := 2 ^ j
  have hT_ge : ∀ x ∈ T, η ≤ delta A P x := fun x hx => (Finset.mem_filter.1 hx).2.1
  have hE2_le : E2 A P ≤ 4 * Lnat * η ^ 2 * T.card := by
    have hbuck : ∑ x ∈ T, delta A P x ^ 2 ≤ 4 * η ^ 2 * T.card := by
      calc ∑ x ∈ T, delta A P x ^ 2
          ≤ ∑ _x ∈ T, 4 * η ^ 2 := by
            refine Finset.sum_le_sum fun x hx => ?_
            have hlt : delta A P x < 2 * η := by
              simpa [η, pow_succ, mul_comm] using (Finset.mem_filter.1 hx).2.2
            calc delta A P x ^ 2 ≤ (2 * η) ^ 2 := Nat.pow_le_pow_left (le_of_lt hlt) 2
              _ = 4 * η ^ 2 := by ring
        _ = 4 * η ^ 2 * T.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    calc E2 A P
        = ∑ i ∈ Finset.range Lnat,
            ∑ x ∈ dyadicBucket (diffSet A P) (delta A P) i, delta A P x ^ 2 := hdyad
      _ ≤ Lnat * ∑ x ∈ T, delta A P x ^ 2 := hjmax
      _ ≤ Lnat * (4 * η ^ 2 * T.card) := Nat.mul_le_mul_left _ hbuck
      _ = 4 * Lnat * η ^ 2 * T.card := by ring
  have hE2_R : (E2 A P : ℝ) ≤ 4 * L * ((η : ℝ) ^ 2 * (T.card : ℝ)) := by
    have h : (E2 A P : ℝ) ≤ ((4 * Lnat * η ^ 2 * T.card : ℕ) : ℝ) := by exact_mod_cast hE2_le
    push_cast [L, Lnat] at h ⊢; linarith
  have hdcs_R : (η : ℝ) ^ 4 * (T.card : ℝ) ^ 4 ≤
      (D.card : ℝ) ^ 2 * ((∑ d ∈ D, delta T T d : ℕ) : ℝ) *
        ((∑ z ∈ diffSet P P, delta A A z ^ 2 * delta P P z : ℕ) : ℝ) := by
    have h0 : (η : ℝ) ^ 4 * (T.card : ℝ) ^ 4 ≤
        (P.card : ℝ) ^ 2 * ((∑ d ∈ D, delta T T d : ℕ) : ℝ) *
          ((∑ z ∈ diffSet P P, delta A A z ^ 2 * delta P P z : ℕ) : ℝ) := by
      exact_mod_cast double_cs_energy_bound A P T η hT_ge
    have hP2 : (P.card : ℝ) ^ 2 ≤ (D.card : ℝ) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hP_le_D_R 2
    exact le_trans h0 (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hP2 (Nat.cast_nonneg _)) (Nat.cast_nonneg _))
  have h4 : (cs.n : ℝ) ^ 2 * (η : ℝ) ^ 6 * ((∑ d ∈ D, delta T T d : ℕ) : ℝ) ^ 6 ≤
      C4 * L ^ 10 * (T.card : ℝ) ^ 5 * (D.card : ℝ) ^ 11 := by
    rw [hC4_eq]; exact first_factor_pow6_bound cs hn T η hT_ge
  have h5 : ((∑ z ∈ diffSet P P, delta A A z ^ 2 * delta P P z : ℕ) : ℝ) ^ 54 ≤
      C5 * L ^ 116 * (cs.n : ℝ) ^ 60 * (D.card : ℝ) ^ 94 := by
    rw [hC5_eq]; exact second_factor_pow54_bound cs hn
  have hE3AP_T : (η : ℝ) ^ 3 * (T.card : ℝ) ≤ 1728 * L * (cs.n : ℝ) * (D.card : ℝ) ^ 2 := by
    have hnat : η ^ 3 * T.card ≤ E3 A P := by
      calc η ^ 3 * T.card = ∑ _x ∈ T, η ^ 3 := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
        _ ≤ ∑ x ∈ T, delta A P x ^ 3 :=
            Finset.sum_le_sum fun x hx => Nat.pow_le_pow_left (hT_ge x hx) 3
        _ ≤ E3 A P := sum_delta_pow_le_E3 A P T
    have h1 : (η : ℝ) ^ 3 * (T.card : ℝ) ≤ 1728 * L * (cs.n : ℝ) * (P.card : ℝ) ^ 2 := by
      dsimp only [L]; exact_mod_cast le_trans hnat (convex_E3_bound cs P)
    have hP2 : (P.card : ℝ) ^ 2 ≤ (D.card : ℝ) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hP_le_D_R 2
    exact le_trans h1 (mul_le_mul_of_nonneg_left hP2
      (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)))
  have hproj := diff_proj_lemma A
  dsimp only at hproj
  have hP_to_E2 : A.card ^ 2 * ∑ x ∈ P, delta P P x ≤ 10 * D.card * E2 A P := by
    have hE2_eq : E2 A P = ∑ x ∈ diffSet A A, delta A A x * delta P P x := by
      have h := sum_delta_mul_delta_comm A A P P
      rw [h]
      unfold E2
      refine Finset.sum_congr rfl fun y _ => by ring
    calc A.card ^ 2 * ∑ x ∈ P, delta P P x
        = ∑ x ∈ P, A.card ^ 2 * delta P P x := Finset.mul_sum _ _ _
      _ ≤ ∑ x ∈ P, (10 * D.card * delta A A x) * delta P P x :=
          Finset.sum_le_sum fun x hx => Nat.mul_le_mul_right _ (Finset.mem_filter.1 hx).2
      _ = 10 * D.card * ∑ x ∈ P, delta A A x * delta P P x := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun x _ => by ring
      _ ≤ 10 * D.card * ∑ x ∈ D, delta A A x * delta P P x :=
          Nat.mul_le_mul_left _ (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _))
      _ = 10 * D.card * E2 A P := by rw [← hE2_eq]
  have hE3A : (E3 A A : ℝ) ≤ 1728 * L * (cs.n : ℝ) ^ 3 := by
    have h := convex_E3_bound cs A
    rw [hAcard] at h
    have h' : (E3 A A : ℝ) ≤ 1728 * L * (cs.n : ℝ) * (cs.n : ℝ) ^ 2 := by
      dsimp only [L]; exact_mod_cast h
    linarith [show 1728 * L * (cs.n : ℝ) * (cs.n : ℝ) ^ 2 = 1728 * L * (cs.n : ℝ) ^ 3 by ring]
  have hn5 : (cs.n : ℝ) ^ 5 ≤ (6250 : ℝ) / 9 * 1728 * L * (D.card : ℝ) * (E2 A P : ℝ) := by
    have hnat : 9 * cs.n ^ 8 ≤ 6250 * D.card * E3 A A * E2 A P := by
      calc 9 * cs.n ^ 8
          = A.card ^ 2 * (9 * A.card ^ 6) := by rw [hAcard]; ring
        _ ≤ A.card ^ 2 * (625 * E3 A A * ∑ x ∈ P, delta P P x) := Nat.mul_le_mul_left _ hproj
        _ = 625 * E3 A A * (A.card ^ 2 * ∑ x ∈ P, delta P P x) := by ring
        _ ≤ 625 * E3 A A * (10 * D.card * E2 A P) := Nat.mul_le_mul_left _ hP_to_E2
        _ = 6250 * D.card * E3 A A * E2 A P := by ring
    have hR : 9 * (cs.n : ℝ) ^ 8 ≤ 6250 * (D.card : ℝ) * (E3 A A : ℝ) * (E2 A P : ℝ) := by
      exact_mod_cast hnat
    have hmul_E3 : (6250 : ℝ) / 9 * (D.card : ℝ) * (E3 A A : ℝ) * (E2 A P : ℝ) ≤
        (6250 : ℝ) / 9 * (D.card : ℝ) * (1728 * L * (cs.n : ℝ) ^ 3) * (E2 A P : ℝ) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hE3A (mul_nonneg (by norm_num) (Nat.cast_nonneg _)))
        (Nat.cast_nonneg _)
    have hR2 : (cs.n : ℝ) ^ 5 * (cs.n : ℝ) ^ 3 ≤
        ((6250 : ℝ) / 9 * 1728 * L * (D.card : ℝ) * (E2 A P : ℝ)) * (cs.n : ℝ) ^ 3 := by
      calc (cs.n : ℝ) ^ 5 * (cs.n : ℝ) ^ 3 = (cs.n : ℝ) ^ 8 := by ring
        _ ≤ (6250 : ℝ) / 9 * (D.card : ℝ) * (E3 A A : ℝ) * (E2 A P : ℝ) := by linarith
        _ ≤ (6250 : ℝ) / 9 * (D.card : ℝ) * (1728 * L * (cs.n : ℝ) ^ 3) * (E2 A P : ℝ) := hmul_E3
        _ = ((6250 : ℝ) / 9 * 1728 * L * (D.card : ℝ) * (E2 A P : ℝ)) * (cs.n : ℝ) ^ 3 := by ring
    have hn_pos : (0 : ℝ) < (cs.n : ℝ) := by exact_mod_cast (show 0 < cs.n by omega)
    exact le_of_mul_le_mul_right hR2 (pow_pos hn_pos 3)
  exact cushman_combine_algebra (cs.n : ℝ) (D.card : ℝ) (T.card : ℝ) (η : ℝ) (E2 A P : ℝ)
    ((∑ d ∈ D, delta T T d : ℕ) : ℝ)
    ((∑ z ∈ diffSet P P, delta A A z ^ 2 * delta P P z : ℕ) : ℝ)
    L C4 C5 K0 K1 K2
    (by exact_mod_cast (show 0 < cs.n by omega))
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    hC4_pos hC5_pos hK0_pos hK1_pos hK2_pos
    hE2_R hdcs_R h4 h5 hE3AP_T hK0_eq hK1_eq hK2_eq hn5

/- ## Section 6: Transfer to Consecutive Block Sums and Asymptotic Deduction -/

/-- Prefix sums `S(i) = ∑_{l=1}^{i+1} a(l)` form a `ConvexSeq` of length `m` when
    `k ↦ a (k + 1)` is strictly increasing. -/
def prefixSumSeq (a : ℕ → ℕ) (ha : StrictMono (fun k : ℕ => a (k + 1))) (m : ℕ) : ConvexSeq where
  n := m
  val := fun i => ∑ l ∈ Finset.Icc 1 (i + 1), (a l : ℤ)
  strictMono := by
    intro i j hij _
    have hstep : ∀ k, (∑ l ∈ Finset.Icc 1 (k + 1), (a l : ℤ)) <
        ∑ l ∈ Finset.Icc 1 (k + 2), (a l : ℤ) := by
      intro k
      have hsub : Finset.Icc 1 (k + 2) = insert (k + 2) (Finset.Icc 1 (k + 1)) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hsub, Finset.sum_insert (by simp)]
      have ha_pos : 0 < a (k + 2) := by
        have hlt : a 1 < a (k + 2) := ha (show 0 < k + 1 by omega)
        omega
      linarith [show (0 : ℤ) < (a (k + 2) : ℤ) by exact_mod_cast ha_pos]
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hij
    induction d with
    | zero => exact hstep i
    | succ d ih =>
      have h1 := ih (by omega) (by omega)
      have h2 := hstep (i + d + 1)
      have heq : i + (d + 1) + 1 + 1 = i + d + 1 + 2 := by omega
      rw [heq]; linarith
  strictConvex := by
    intro i _
    have hdiff : ∀ k,
        (∑ l ∈ Finset.Icc 1 (k + 2), (a l : ℤ)) -
        (∑ l ∈ Finset.Icc 1 (k + 1), (a l : ℤ)) = (a (k + 2) : ℤ) := by
      intro k
      have hsub : Finset.Icc 1 (k + 2) = insert (k + 2) (Finset.Icc 1 (k + 1)) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hsub, Finset.sum_insert (by simp)]
      ring
    rw [show i + 1 + 1 = i + 2 by omega, show i + 2 + 1 = i + 3 by omega]
    rw [hdiff i, hdiff (i + 1)]
    have hlt := ha (show i + 1 < i + 2 by omega)
    exact_mod_cast hlt

/-- Finite set of consecutive block sums of length ≥ 2 among `a 1, ..., a m`. -/
def blockSumFinset (a : ℕ → ℕ) (m : ℕ) : Finset ℕ :=
  ((Finset.Icc 1 m ×ˢ Finset.Icc 1 m).filter (fun p => p.1 + 1 ≤ p.2)).image
    (fun p => ∑ l ∈ Finset.Icc p.1 p.2, a l)

lemma blockSum_set_eq (a : ℕ → ℕ) (m : ℕ) :
    {s : ℕ | Erdos423.IsConsecutiveBlockSum a (m + 1) s} = (blockSumFinset a m : Set ℕ) := by
  ext s
  simp only [Set.mem_ofPred_eq, Erdos423.IsConsecutiveBlockSum, Finset.mem_coe,
    blockSumFinset, Finset.mem_image, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  constructor
  · rintro ⟨i, j, hi, hij, hjm, rfl⟩
    exact ⟨(i, j), ⟨⟨⟨hi, by omega⟩, ⟨by omega, by omega⟩⟩, hij⟩, rfl⟩
  · rintro ⟨⟨i, j⟩, ⟨⟨⟨hi, _⟩, ⟨_, hjm⟩⟩, hij⟩, rfl⟩
    exact ⟨i, j, hi, hij, by omega, rfl⟩

lemma diffSet_card_le_blockSum (a : ℕ → ℕ) (ha : StrictMono (fun k : ℕ => a (k + 1)))
    (m : ℕ) (hm : 1 ≤ m) :
    let cs := prefixSumSeq a ha m
    (diffSet cs.toFinset cs.toFinset).card ≤ 2 * (blockSumFinset a m).card + 3 * m := by
  intro cs
  let posSet : Finset ℤ :=
    ((blockSumFinset a m).image (fun (s : ℕ) => (s : ℤ))) ∪
      ((Finset.range m).image (fun (i : ℕ) => (a (i + 2) : ℤ)))
  have hsub : diffSet cs.toFinset cs.toFinset ⊆
      insert 0 (posSet ∪ posSet.image Neg.neg) := by
    intro d hd
    simp only [diffSet, ConvexSeq.toFinset, Finset.mem_image, Finset.mem_product,
      Finset.mem_range] at hd
    rcases hd with ⟨⟨x, y⟩, ⟨⟨j, hj, rfl⟩, ⟨i, hi, rfl⟩⟩, rfl⟩
    have hdiff_nat : ∀ u v, u < v → v < m →
        cs.val v - cs.val u = ((∑ l ∈ Finset.Icc (u + 2) (v + 1), a l : ℕ) : ℤ) := by
      intro u v huv _
      simp only [cs, prefixSumSeq, Nat.cast_sum]
      have hdisj : Disjoint (Finset.Icc 1 (u + 1)) (Finset.Icc (u + 2) (v + 1)) := by
        rw [Finset.disjoint_left]
        intro l hl1 hl2
        simp only [Finset.mem_Icc] at hl1 hl2; omega
      have hunion : Finset.Icc 1 (v + 1) =
          Finset.Icc 1 (u + 1) ∪ Finset.Icc (u + 2) (v + 1) := by
        ext l; simp only [Finset.mem_Icc, Finset.mem_union]; omega
      rw [hunion, Finset.sum_union hdisj]
      ring
    have hmem_pos : ∀ u v, u < v → v < m → cs.val v - cs.val u ∈ posSet := by
      intro u v huv hvm
      rw [hdiff_nat u v huv hvm]
      simp only [posSet, Finset.mem_union, Finset.mem_image, Finset.mem_range]
      by_cases hstep : v = u + 1
      · right
        refine ⟨u, by omega, ?_⟩
        subst hstep
        simp [Finset.Icc_self]
      · left
        refine ⟨∑ l ∈ Finset.Icc (u + 2) (v + 1), a l, ?_, rfl⟩
        simp only [blockSumFinset, Finset.mem_image, Finset.mem_filter, Finset.mem_product,
          Finset.mem_Icc]
        exact ⟨(u + 2, v + 1), ⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩, by omega⟩, rfl⟩
    rcases lt_trichotomy i j with hlt | rfl | hgt
    · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (hmem_pos i j hlt hj))
    · simp
    · have hp := hmem_pos j i hgt hi
      have hneg : cs.val j - cs.val i = -(cs.val i - cs.val j) := by ring
      rw [hneg]
      exact Finset.mem_insert_of_mem
        (Finset.mem_union_right _ (Finset.mem_image.2 ⟨_, hp, rfl⟩))
  have hpos_card : posSet.card ≤ (blockSumFinset a m).card + m := by
    calc posSet.card
        ≤ ((blockSumFinset a m).image (fun (s : ℕ) => (s : ℤ))).card +
          ((Finset.range m).image (fun (i : ℕ) => (a (i + 2) : ℤ))).card := Finset.card_union_le _ _
      _ ≤ (blockSumFinset a m).card + (Finset.range m).card :=
          Nat.add_le_add Finset.card_image_le Finset.card_image_le
      _ = (blockSumFinset a m).card + m := by rw [Finset.card_range]
  calc (diffSet cs.toFinset cs.toFinset).card
      ≤ (insert (0 : ℤ) (posSet ∪ posSet.image Neg.neg)).card := Finset.card_le_card hsub
    _ ≤ (posSet ∪ posSet.image Neg.neg).card + 1 := Finset.card_insert_le _ _
    _ ≤ posSet.card + (posSet.image Neg.neg).card + 1 :=
        Nat.add_le_add_right (Finset.card_union_le _ _) 1
    _ = 2 * posSet.card + 1 := by rw [card_image_neg]; ring
    _ ≤ 2 * ((blockSumFinset a m).card + m) + 1 := by omega
    _ ≤ 2 * (blockSumFinset a m).card + 3 * m := by omega

/-- Eventually `(Nat.log 2 m + 1)^764 * K ≤ m^α` for any `K > 0, α > 0`. -/
lemma eventually_log_pow_le_rpow (K α : ℝ) (hK : 0 < K) (hα : 0 < α) :
    ∀ᶠ m : ℕ in atTop, K * ((Nat.log 2 m + 1 : ℕ) : ℝ) ^ 764 ≤ (m : ℝ) ^ α := by
  have hβ : 0 < α / 764 := by positivity
  have hlim : Tendsto (fun x : ℝ => Real.log x / x ^ (α / 764)) atTop (nhds 0) := by
    simpa [Real.rpow_neg] using
      (isLittleO_log_rpow_atTop hβ).tendsto_div_nhds_zero
  have hlim_nat : Tendsto (fun m : ℕ => Real.log (m : ℝ) / (m : ℝ) ^ (α / 764)) atTop (nhds 0) :=
    hlim.comp tendsto_natCast_atTop_atTop
  have hinv_nat : Tendsto (fun m : ℕ => (1 : ℝ) / (m : ℝ) ^ (α / 764)) atTop (nhds 0) :=
    (tendsto_inv_atTop_zero.comp
      ((tendsto_rpow_atTop hβ).comp tendsto_natCast_atTop_atTop)).congr
      (fun m => by simp [Function.comp, one_div])
  have hcomb : Tendsto
      (fun m : ℕ =>
        (Real.log (m : ℝ) / Real.log 2 + 1) / (m : ℝ) ^ (α / 764)) atTop (nhds 0) := by
    have h1 : Tendsto (fun m : ℕ =>
        (1 / Real.log 2) * (Real.log (m : ℝ) / (m : ℝ) ^ (α / 764)) +
        (1 : ℝ) / (m : ℝ) ^ (α / 764)) atTop (nhds ((1 / Real.log 2) * 0 + 0)) :=
      (hlim_nat.const_mul (1 / Real.log 2)).add hinv_nat
    simp only [mul_zero, add_zero] at h1
    refine h1.congr fun m => ?_
    ring
  set ε : ℝ := (1 / K) ^ ((1 : ℝ) / 764)
  have hε : 0 < ε := Real.rpow_pos_of_pos (by positivity) _
  have hev1 : ∀ᶠ m : ℕ in atTop,
      (Real.log (m : ℝ) / Real.log 2 + 1) / (m : ℝ) ^ (α / 764) < ε :=
    (tendsto_order.1 hcomb).2 ε hε
  filter_upwards [hev1, Filter.eventually_ge_atTop 2] with m hm hm2
  have hm_pos : (0 : ℝ) < (m : ℝ) := by positivity
  have hlog2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog_le : ((Nat.log 2 m : ℕ) : ℝ) ≤ Real.log (m : ℝ) / Real.log 2 := by
    rw [le_div_iff₀ hlog2_pos]
    have hpow : (2 : ℝ) ^ (Nat.log 2 m) ≤ (m : ℝ) := by
      exact_mod_cast Nat.pow_log_le_self 2 (by omega)
    have hlog := Real.log_le_log (by positivity) hpow
    rwa [Real.log_pow] at hlog
  have h1 : ((Nat.log 2 m + 1 : ℕ) : ℝ) ≤ ε * (m : ℝ) ^ (α / 764) := by
    have hlt : Real.log (m : ℝ) / Real.log 2 + 1 < ε * (m : ℝ) ^ (α / 764) :=
      (div_lt_iff₀ (Real.rpow_pos_of_pos hm_pos _)).1 hm
    push_cast
    linarith
  have hpow764 : ((Nat.log 2 m + 1 : ℕ) : ℝ) ^ 764 ≤
      (ε * (m : ℝ) ^ (α / 764)) ^ 764 := pow_le_pow_left₀ (by positivity) h1 764
  have hε764 : ε ^ 764 = 1 / K := by
    rw [← Real.rpow_natCast ε 764, ← Real.rpow_mul (by positivity)]
    norm_num
  have hm_rpow : ((m : ℝ) ^ (α / 764)) ^ 764 = (m : ℝ) ^ α := by
    rw [← Real.rpow_natCast _ 764, ← Real.rpow_mul (le_of_lt hm_pos)]
    congr 1; ring
  rw [mul_pow, hε764, hm_rpow] at hpow764
  calc K * ((Nat.log 2 m + 1 : ℕ) : ℝ) ^ 764
      ≤ K * (1 / K * (m : ℝ) ^ α) := mul_le_mul_of_nonneg_left hpow764 (le_of_lt hK)
    _ = (m : ℝ) ^ α := by field_simp [hK.ne']

end Erdos423Cushman

open Erdos423Cushman in
theorem OMA.solution : OMA.R_Erdos423_erdos_423_variants_upper_bound_R1.H1 := by
  intro a ha η hη
  obtain ⟨C, hCpos, hC⟩ := cushman_convex_diff_poly
  refine ⟨1, zero_lt_one, ?_⟩
  let δ : ℝ := min η ((1 : ℝ) / 4)
  have hδ_pos : 0 < δ := lt_min hη (by norm_num)
  have hδ_le_η : δ ≤ η := min_le_left _ _
  have hδ_le_quarter : δ ≤ (1 : ℝ) / 4 := min_le_right _ _
  have hev := eventually_log_pow_le_rpow (C * (6 : ℝ) ^ 688) (688 * δ)
    (by positivity) (by positivity)
  filter_upwards [hev, Filter.eventually_ge_atTop 2] with m hm hm2
  have hm_ge1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (show 1 ≤ m by omega)
  have hm_pos : (0 : ℝ) < (m : ℝ) := by positivity
  let cs := prefixSumSeq a ha m
  have hpoly := hC cs (by change 1 ≤ m; omega)
  change (m : ℝ) ^ 1101 ≤
    C * ((Nat.log 2 m + 1 : ℕ) : ℝ) ^ 764 *
      ((diffSet cs.toFinset cs.toFinset).card : ℝ) ^ 688 at hpoly
  have hD_lb : 6 * (m : ℝ) ^ ((1101 : ℝ) / 688 - δ) ≤
      ((diffSet cs.toFinset cs.toFinset).card : ℝ) := by
    have h688 : (6 * (m : ℝ) ^ ((1101 : ℝ) / 688 - δ)) ^ 688 ≤
        ((diffSet cs.toFinset cs.toFinset).card : ℝ) ^ 688 := by
      have hlhs : (6 * (m : ℝ) ^ ((1101 : ℝ) / 688 - δ)) ^ 688 * (m : ℝ) ^ (688 * δ) =
          (6 : ℝ) ^ 688 * (m : ℝ) ^ 1101 := by
        rw [mul_pow, ← Real.rpow_natCast ((m : ℝ) ^ _) 688,
          ← Real.rpow_mul (le_of_lt hm_pos)]
        rw [mul_assoc, ← Real.rpow_add hm_pos]
        have hexp : ((1101 : ℝ) / 688 - δ) * (688 : ℕ) + 688 * δ = (1101 : ℕ) := by
          push_cast; ring
        rw [hexp, Real.rpow_natCast]
      have h6_nn : (0 : ℝ) ≤ (6 : ℝ) ^ 688 := pow_nonneg (by norm_num) 688
      have hD688_nn : (0 : ℝ) ≤ ((diffSet cs.toFinset cs.toFinset).card : ℝ) ^ 688 :=
        pow_nonneg (Nat.cast_nonneg _) 688
      have hmul : (6 * (m : ℝ) ^ ((1101 : ℝ) / 688 - δ)) ^ 688 * (m : ℝ) ^ (688 * δ) ≤
          ((diffSet cs.toFinset cs.toFinset).card : ℝ) ^ 688 * (m : ℝ) ^ (688 * δ) := by
        rw [hlhs]
        calc (6 : ℝ) ^ 688 * (m : ℝ) ^ 1101
            ≤ (6 : ℝ) ^ 688 * (C * ((Nat.log 2 m + 1 : ℕ) : ℝ) ^ 764 *
                ((diffSet cs.toFinset cs.toFinset).card : ℝ) ^ 688) :=
              mul_le_mul_of_nonneg_left hpoly h6_nn
          _ = (C * (6 : ℝ) ^ 688 * ((Nat.log 2 m + 1 : ℕ) : ℝ) ^ 764) *
                ((diffSet cs.toFinset cs.toFinset).card : ℝ) ^ 688 := by
              rw [← mul_assoc, ← mul_assoc, mul_comm ((6 : ℝ) ^ 688) C]
          _ ≤ (m : ℝ) ^ (688 * δ) *
                ((diffSet cs.toFinset cs.toFinset).card : ℝ) ^ 688 :=
              mul_le_mul_of_nonneg_right hm hD688_nn
          _ = ((diffSet cs.toFinset cs.toFinset).card : ℝ) ^ 688 *
                (m : ℝ) ^ (688 * δ) := mul_comm _ _
      exact le_of_mul_le_mul_right hmul (Real.rpow_pos_of_pos hm_pos _)
    by_contra hlt
    push Not at hlt
    have hstrict : ((diffSet cs.toFinset cs.toFinset).card : ℝ) ^ 688 <
        (6 * (m : ℝ) ^ ((1101 : ℝ) / 688 - δ)) ^ 688 :=
      pow_lt_pow_left₀ hlt (Nat.cast_nonneg _) (Nat.succ_ne_zero 687)
    exact not_le.2 hstrict h688
  have hD_ub : ((diffSet cs.toFinset cs.toFinset).card : ℝ) ≤
      2 * ((blockSumFinset a m).card : ℝ) + 3 * (m : ℝ) := by
    exact_mod_cast diffSet_card_le_blockSum a ha m (by omega)
  have hm_le_rpow : (m : ℝ) ≤ (m : ℝ) ^ ((1101 : ℝ) / 688 - δ) := by
    calc (m : ℝ) = (m : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (m : ℝ) ^ ((1101 : ℝ) / 688 - δ) :=
          Real.rpow_le_rpow_of_exponent_le hm_ge1 (by linarith)
  have hBS_lb : (m : ℝ) ^ ((1101 : ℝ) / 688 - δ) ≤ ((blockSumFinset a m).card : ℝ) := by
    linarith
  have hexp_le : (m : ℝ) ^ ((1101 : ℝ) / 688 - η) ≤ (m : ℝ) ^ ((1101 : ℝ) / 688 - δ) :=
    Real.rpow_le_rpow_of_exponent_le hm_ge1 (by linarith)
  have hncard : ({s : ℕ | Erdos423.IsConsecutiveBlockSum a (m + 1) s}).ncard =
      (blockSumFinset a m).card := by
    rw [blockSum_set_eq, Set.ncard_coe_finset]
  rw [one_mul, hncard]
  exact le_trans hexp_le hBS_lb
