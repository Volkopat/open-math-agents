import OMAReductions.R_Erdos875_erdos_875_variants_deshouillers_freiman_R1
import Mathlib

-- Step H3 of reduction Erdos875.erdos_875.variants.deshouillers_freiman.R1 (Erdos Problem 875):
-- the hole bound for the middle restricted sumset of a dense set.
-- Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)
--
-- Claim: B has n >= 20 elements b_0 < ... < b_(n-1), k = n / 2, g = b_(n-1) - b_0 - (n-1) and
-- 10 g <= n. Then twice the number of integers of [L, M] that are not sums of k elements of B
-- is at most (M - L) - k (n - k) + g.
-- Proof sketch. Work with index sets I (k indices below n) and s(I) = sum of b_i, i in I.
-- A move replaces an index p of I by a free index p + 1. Let D(I) be the set of possible moves.
-- 1. Chains of moves: at least i(I) - i(bottom) + 1 sums are <= s(I), and at least
--    i(top) - i(I) sums are > s(I), where i(I) is the sum of the indices (down_chain, up_chain).
-- 2. If A is a set of moves p of I with b_(p+1) = b_p + 1, then s(I) + |A| is a sum (shift_mem).
--    If |D(I)| >= g + 1, then for each move p at least b_(p+1) - b_p - 1 other moves have
--    step 1, so all integers between s(I) and the sum after the move are sums (fill).
-- 3. If |D(I)| >= R, then some move keeps |D| >= R, or I is the terminal set
--    {d, d - 2, ..., d - 2 (R - 1)} + [d + 2, n) (good_move, terminal_form).
-- 4. Thus there is no hole between s(P) and s(Q), where P = [0, k - g) + {k - g + 1 + 2 u : u < g}
--    and Q is the terminal set for R = g + 1 (phaseB).
-- 5. With a_i = b_i - i (monotone), the number of holes is at most
--    (a(P) - a(bottom)) + (a(top) - a(Q)), and twice this is at most a(top) - a(bottom),
--    by a rotation of the sums and 4 g + 2 <= k (rot, mid, final_ineq, core).

namespace OMA.P_Erdos875_DF_R1_H3

open Finset

/-- Replace `x` by `y` in `I`. -/
def sw (I : Finset ℕ) (x y : ℕ) : Finset ℕ := insert y (I.erase x)

/-- The positions `i` of `I` whose successor is a free index below `n`. -/
def dset (n : ℕ) (I : Finset ℕ) : Finset ℕ := I.filter (fun i => i + 1 < n ∧ i + 1 ∉ I)

lemma sw_sub {n : ℕ} {I : Finset ℕ} {x y : ℕ} (hI : I ⊆ range n) (hy : y < n) :
    sw I x y ⊆ range n := by
  intro z hz
  rcases Finset.mem_insert.mp hz with rfl | hz
  · exact Finset.mem_range.mpr hy
  · exact hI (Finset.mem_of_mem_erase hz)

lemma sw_card {I : Finset ℕ} {x y : ℕ} (hx : x ∈ I) (hy : y ∉ I) :
    (sw I x y).card = I.card := by
  have h1 : y ∉ I.erase x := fun h => hy (Finset.mem_of_mem_erase h)
  have h2 : 0 < I.card := Finset.card_pos.mpr ⟨x, hx⟩
  rw [sw, Finset.card_insert_of_notMem h1, Finset.card_erase_of_mem hx]
  omega

lemma sw_sum {I : Finset ℕ} {x y : ℕ} (hx : x ∈ I) (hy : y ∉ I) (f : ℕ → ℕ) :
    ∑ i ∈ sw I x y, f i + f x = ∑ i ∈ I, f i + f y := by
  have h1 : y ∉ I.erase x := fun h => hy (Finset.mem_of_mem_erase h)
  rw [sw, Finset.sum_insert h1]
  have := Finset.sum_erase_add I f hx
  omega

lemma mem_sw {I : Finset ℕ} {x y z : ℕ} : z ∈ sw I x y ↔ z = y ∨ (z ≠ x ∧ z ∈ I) := by
  simp [sw, Finset.mem_insert, Finset.mem_erase]

lemma mem_dset {n : ℕ} {I : Finset ℕ} {i : ℕ} :
    i ∈ dset n I ↔ i ∈ I ∧ i + 1 < n ∧ i + 1 ∉ I := by
  simp [dset]

/-- Strict growth of `b` along indices below `n`. -/
lemma b_grow {n : ℕ} {b : ℕ → ℕ} (hb : ∀ i, i + 1 < n → b i < b (i + 1)) :
    ∀ i j, i ≤ j → j < n → b i + (j - i) ≤ b j := by
  intro i j hij
  induction j, hij using Nat.le_induction with
  | base => intro _; simp
  | succ j hij ih =>
    intro hj
    have h1 := ih (by omega)
    have h2 := hb j hj
    omega

lemma gap_tele {n : ℕ} {b : ℕ → ℕ} (hb : ∀ i, i + 1 < n → b i < b (i + 1)) :
    ∀ N, N < n → ∑ i ∈ range N, (b (i + 1) - b i - 1) + b 0 + N = b N := by
  intro N
  induction N with
  | zero => intro _; simp
  | succ N ih =>
    intro hN
    have h1 := ih (by omega)
    have h2 := hb N hN
    rw [Finset.sum_range_succ]
    omega

lemma cnt_succ {S : Finset ℕ} {x y : ℕ} (hy : y ∈ S) (hxy : x < y) :
    (S.filter (· ≤ x)).card + 1 ≤ (S.filter (· ≤ y)).card := by
  have hn : y ∉ S.filter (· ≤ x) := by
    intro h
    have := (Finset.mem_filter.mp h).2
    omega
  rw [← Finset.card_insert_of_notMem hn]
  apply Finset.card_le_card
  intro z hz
  rcases Finset.mem_insert.mp hz with rfl | hz
  · exact Finset.mem_filter.mpr ⟨hy, le_refl _⟩
  · have h := Finset.mem_filter.mp hz
    exact Finset.mem_filter.mpr ⟨h.1, by have := h.2; omega⟩

lemma cnt_succ' {S : Finset ℕ} {x y : ℕ} (hy : y ∈ S) (hxy : x < y) :
    (S.filter (y < ·)).card + 1 ≤ (S.filter (x < ·)).card := by
  have hn : y ∉ S.filter (y < ·) := by
    intro h
    have := (Finset.mem_filter.mp h).2
    omega
  rw [← Finset.card_insert_of_notMem hn]
  apply Finset.card_le_card
  intro z hz
  rcases Finset.mem_insert.mp hz with rfl | hz
  · exact Finset.mem_filter.mpr ⟨hy, hxy⟩
  · have h := Finset.mem_filter.mp hz
    exact Finset.mem_filter.mpr ⟨h.1, by have := h.2; omega⟩

lemma cnt_fill {S : Finset ℕ} {x y : ℕ} (hxy : x ≤ y) (h : ∀ v, x < v → v ≤ y → v ∈ S) :
    (S.filter (· ≤ x)).card + y ≤ (S.filter (· ≤ y)).card + x := by
  have hd : Disjoint (S.filter (· ≤ x)) (Finset.Ioc x y) := by
    refine Finset.disjoint_left.mpr fun z hz hz2 => ?_
    have h1 := (Finset.mem_filter.mp hz).2
    have h2 := (Finset.mem_Ioc.mp hz2).1
    omega
  have hsub : S.filter (· ≤ x) ∪ Finset.Ioc x y ⊆ S.filter (· ≤ y) := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · have h1 := Finset.mem_filter.mp hz
      exact Finset.mem_filter.mpr ⟨h1.1, by have := h1.2; omega⟩
    · have h1 := Finset.mem_Ioc.mp hz
      exact Finset.mem_filter.mpr ⟨h z h1.1 h1.2, h1.2⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hd, Nat.card_Ioc] at hc
  omega

/-- If `I` is not the bottom set, an element can move one step down. -/
lemma exists_down {k : ℕ} {I : Finset ℕ} (hk : I.card = k) (hne : I ≠ range k) :
    ∃ i, i ∉ I ∧ i + 1 ∈ I := by
  by_contra hcon
  push Not at hcon
  have h1 : ∃ j, j < k ∧ j ∉ I := by
    by_contra h
    push Not at h
    have hsub : range k ⊆ I := fun j hj => h j (Finset.mem_range.mp hj)
    exact hne (Finset.eq_of_subset_of_card_le hsub (by simp [hk])).symm
  obtain ⟨j, hjk, hj⟩ := h1
  have h2 : ∀ x, j ≤ x → x ∉ I := by
    intro x hx
    induction x, hx using Nat.le_induction with
    | base => exact hj
    | succ x _ ih => exact hcon x ih
  have hsub : I ⊆ range j := by
    intro x hx
    by_contra h
    exact h2 x (by simpa using h) hx
  have := Finset.card_le_card hsub
  simp at this
  omega

/-- If `I` is not the top set, an element can move one step up. -/
lemma exists_up {n k : ℕ} {I : Finset ℕ} (hI : I ⊆ range n) (hk : I.card = k) (hkn : k ≤ n)
    (hne : I ≠ Finset.Ico (n - k) n) : ∃ p, p ∈ dset n I := by
  by_contra hcon
  push Not at hcon
  have hup : ∀ p, p ∈ I → p + 1 < n → p + 1 ∈ I := by
    intro p hp hp1
    by_contra h
    exact hcon p (mem_dset.mpr ⟨hp, hp1, h⟩)
  have h1 : ∃ j, n - k ≤ j ∧ j < n ∧ j ∉ I := by
    by_contra h
    push Not at h
    have hsub : Finset.Ico (n - k) n ⊆ I := fun j hj => by
      have := Finset.mem_Ico.mp hj
      exact h j this.1 this.2
    exact hne (Finset.eq_of_subset_of_card_le hsub (by simp [hk]; omega)).symm
  obtain ⟨j, hj1, hj2, hj⟩ := h1
  have h2 : ∀ d x, x + d = j → x ∉ I := by
    intro d
    induction d with
    | zero => intro x hx; simpa [← hx] using hj
    | succ d ih =>
      intro x hx hxI
      exact ih (x + 1) (by omega) (hup x hxI (by omega))
  have hsub : I ⊆ Finset.Ico (j + 1) n := by
    intro x hx
    have hxn := Finset.mem_range.mp (hI hx)
    refine Finset.mem_Ico.mpr ⟨?_, hxn⟩
    by_contra h
    exact h2 (j - x) x (by omega) hx
  have := Finset.card_le_card hsub
  simp at this
  omega


/-- Every index set lies above the bottom set, and the sums up to it are numerous. -/
lemma down_chain {n k : ℕ} {b : ℕ → ℕ} {S : Finset ℕ} (hb : ∀ i, i + 1 < n → b i < b (i + 1))
    (hS : ∀ I : Finset ℕ, I ⊆ range n → I.card = k → ∑ i ∈ I, b i ∈ S) :
    ∀ m, ∀ I : Finset ℕ, I ⊆ range n → I.card = k → ∑ i ∈ I, i = m →
      (∑ i ∈ range k, b i ≤ ∑ i ∈ I, b i) ∧
      m + 1 ≤ (S.filter (· ≤ ∑ i ∈ I, b i)).card + ∑ i ∈ range k, i := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro I hI hk hm
    by_cases hbot : I = range k
    · subst hbot
      refine ⟨le_refl _, ?_⟩
      have hmem : ∑ i ∈ range k, b i ∈ S.filter (· ≤ ∑ i ∈ range k, b i) :=
        Finset.mem_filter.mpr ⟨hS _ hI hk, le_refl _⟩
      have := Finset.card_pos.mpr ⟨_, hmem⟩
      omega
    · obtain ⟨i, hi, hi1⟩ := exists_down hk hbot
      have hi1n : i + 1 < n := Finset.mem_range.mp (hI hi1)
      have hsub := sw_sub (x := i + 1) hI (show i < n by omega)
      have hcard := (sw_card hi1 hi).trans hk
      have hsum := sw_sum hi1 hi b
      have hsumi := sw_sum hi1 hi (fun j => j)
      have hbi := hb i hi1n
      obtain ⟨h1, h2⟩ := ih (m - 1) (by omega) (sw I (i + 1) i) hsub hcard (by omega)
      have hc := cnt_succ (S := S) (x := ∑ j ∈ sw I (i + 1) i, b j) (y := ∑ j ∈ I, b j)
        (hS I hI hk) (by omega)
      refine ⟨by omega, by omega⟩

/-- Every index set lies below the top set, and the sums above it are numerous. -/
lemma up_chain {n k : ℕ} {b : ℕ → ℕ} {S : Finset ℕ} (hb : ∀ i, i + 1 < n → b i < b (i + 1))
    (hkn : k ≤ n)
    (hS : ∀ I : Finset ℕ, I ⊆ range n → I.card = k → ∑ i ∈ I, b i ∈ S) :
    ∀ m, ∀ I : Finset ℕ, I ⊆ range n → I.card = k → n * k - ∑ i ∈ I, i = m →
      (∑ i ∈ I, b i ≤ ∑ i ∈ Finset.Ico (n - k) n, b i) ∧
      ∑ i ∈ Finset.Ico (n - k) n, i ≤ (S.filter (∑ i ∈ I, b i < ·)).card + ∑ i ∈ I, i := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro I hI hk hm
    by_cases htop : I = Finset.Ico (n - k) n
    · subst htop
      exact ⟨le_refl _, by omega⟩
    · obtain ⟨p, hp⟩ := exists_up hI hk hkn htop
      obtain ⟨hpI, hp1, hp1I⟩ := mem_dset.mp hp
      have hsub := sw_sub (x := p) hI hp1
      have hcard := (sw_card hpI hp1I).trans hk
      have hsum := sw_sum hpI hp1I b
      have hsumi := sw_sum hpI hp1I (fun j => j)
      have hbi := hb p hp1
      have hbound : ∑ i ∈ sw I p (p + 1), i ≤ n * k := by
        calc ∑ i ∈ sw I p (p + 1), i ≤ ∑ _i ∈ sw I p (p + 1), n :=
              Finset.sum_le_sum fun i hi => (Finset.mem_range.mp (hsub hi)).le
          _ = k * n := by simp [hcard]
          _ = n * k := Nat.mul_comm _ _
      obtain ⟨h1, h2⟩ := ih (n * k - ∑ i ∈ sw I p (p + 1), i) (by omega) (sw I p (p + 1))
        hsub hcard rfl
      have hc := cnt_succ' (S := S) (x := ∑ j ∈ I, b j) (y := ∑ j ∈ sw I p (p + 1), b j)
        (hS _ hsub hcard) (by omega)
      refine ⟨by omega, by omega⟩

/-- Shift a set `A` of elements with a free adjacent value: the sum grows by `|A|`. -/
lemma shift_mem {n k : ℕ} {b : ℕ → ℕ} {S : Finset ℕ}
    (hS : ∀ I : Finset ℕ, I ⊆ range n → I.card = k → ∑ i ∈ I, b i ∈ S)
    {I A : Finset ℕ} (hI : I ⊆ range n) (hk : I.card = k) (hA : A ⊆ I)
    (h : ∀ x ∈ A, x + 1 < n ∧ x + 1 ∉ I ∧ b (x + 1) = b x + 1) :
    ∑ i ∈ I, b i + A.card ∈ S := by
  have hinj : Function.Injective (fun x : ℕ => x + 1) := fun x y hxy => by
    simp only at hxy; omega
  have hd : Disjoint (I \ A) (A.image (fun x => x + 1)) := by
    refine Finset.disjoint_left.mpr fun z hz hz2 => ?_
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz2
    exact (h x hx).2.1 (Finset.mem_sdiff.mp hz).1
  have hsub : (I \ A) ∪ A.image (fun x => x + 1) ⊆ range n := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · exact hI (Finset.mem_sdiff.mp hz).1
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
      exact Finset.mem_range.mpr (h x hx).1
  have hcard : ((I \ A) ∪ A.image (fun x => x + 1)).card = k := by
    rw [Finset.card_union_of_disjoint hd, Finset.card_image_of_injective _ hinj,
      Finset.card_sdiff_add_card_eq_card hA, hk]
  have hmem := hS _ hsub hcard
  have hsum : ∑ i ∈ (I \ A) ∪ A.image (fun x => x + 1), b i = ∑ i ∈ I, b i + A.card := by
    rw [Finset.sum_union hd, Finset.sum_image (fun x _ y _ hxy => hinj hxy)]
    have h1 : ∑ x ∈ A, b (x + 1) = ∑ x ∈ A, b x + A.card := by
      rw [Finset.sum_congr rfl (fun x hx => (h x hx).2.2), Finset.sum_add_distrib]
      simp
    have h2 := Finset.sum_sdiff (f := b) hA
    omega
  rw [← hsum]
  exact hmem

/-- A move from a set with many free successors leaves no hole. -/
lemma fill {n k g : ℕ} {b : ℕ → ℕ} {S : Finset ℕ} (hb : ∀ i, i + 1 < n → b i < b (i + 1))
    (hn : 1 ≤ n) (hg : b (n - 1) = b 0 + (n - 1) + g)
    (hS : ∀ I : Finset ℕ, I ⊆ range n → I.card = k → ∑ i ∈ I, b i ∈ S)
    {I : Finset ℕ} (hI : I ⊆ range n) (hk : I.card = k) (hD : g + 1 ≤ (dset n I).card)
    {p : ℕ} (hp : p ∈ dset n I) :
    ∀ v, ∑ i ∈ I, b i < v → v ≤ ∑ i ∈ sw I p (p + 1), b i → v ∈ S := by
  obtain ⟨hpI, hp1, hp1I⟩ := mem_dset.mp hp
  have hsum := sw_sum hpI hp1I b
  have hbp := hb p hp1
  set D := dset n I with hDdef
  have hDsub : D ⊆ range (n - 1) := by
    intro i hi
    have := (mem_dset.mp hi).2.1
    exact Finset.mem_range.mpr (by omega)
  have htot : ∑ i ∈ D, (b (i + 1) - b i - 1) ≤ g := by
    have h1 := Finset.sum_le_sum_of_subset (f := fun i => b (i + 1) - b i - 1) hDsub
    have h2 := gap_tele hb (n - 1) (by omega)
    omega
  have hsplit := Finset.sum_erase_add D (fun i => b (i + 1) - b i - 1) hp
  have hcf := Finset.card_filter_add_card_filter_not (s := D.erase p)
    (fun i => b (i + 1) = b i + 1)
  have hce : (D.erase p).card = D.card - 1 := Finset.card_erase_of_mem hp
  have hbad : ((D.erase p).filter (fun i => ¬ b (i + 1) = b i + 1)).card ≤
      ∑ i ∈ D.erase p, (b (i + 1) - b i - 1) := by
    rw [Finset.card_filter]
    apply Finset.sum_le_sum
    intro i hi
    have hiD := Finset.mem_of_mem_erase hi
    have := hb i (mem_dset.mp hiD).2.1
    split_ifs with hif <;> omega
  have hU : ∀ x ∈ (D.erase p).filter (fun i => b (i + 1) = b i + 1),
      x + 1 < n ∧ x + 1 ∉ I ∧ b (x + 1) = b x + 1 := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := Finset.mem_filter.mp hx
    have hxD := mem_dset.mp (Finset.mem_of_mem_erase hx1)
    exact ⟨hxD.2.1, hxD.2.2, hx2⟩
  have hUI : (D.erase p).filter (fun i => b (i + 1) = b i + 1) ⊆ I := by
    intro x hx
    exact (mem_dset.mp (Finset.mem_of_mem_erase (Finset.mem_filter.mp hx).1)).1
  have hUcard : b (p + 1) - b p - 1 ≤
      ((D.erase p).filter (fun i => b (i + 1) = b i + 1)).card := by omega
  intro v hv1 hv2
  by_cases hlast : v = ∑ i ∈ sw I p (p + 1), b i
  · rw [hlast]
    exact hS _ (sw_sub hI hp1) ((sw_card hpI hp1I).trans hk)
  · have hj : v - ∑ i ∈ I, b i ≤
        ((D.erase p).filter (fun i => b (i + 1) = b i + 1)).card := by omega
    obtain ⟨A, hA⟩ := Finset.powersetCard_nonempty.mpr hj
    obtain ⟨hA1, hA2⟩ := Finset.mem_powersetCard.mp hA
    have := shift_mem hS hI hk (hA1.trans hUI) (fun x hx => hU x (hA1 hx))
    rw [hA2] at this
    have hv : ∑ i ∈ I, b i + (v - ∑ i ∈ I, b i) = v := by omega
    rwa [hv] at this

/-- Either a move keeps at least `R` free successors, or the set is terminal. -/
lemma good_move {n R : ℕ} {I : Finset ℕ} (hR : R ≤ (dset n I).card) (hR1 : 1 ≤ R) :
    (∃ p ∈ dset n I, R ≤ (dset n (sw I p (p + 1))).card) ∨
    ((dset n I).card = R ∧ ∀ p ∈ dset n I, (∀ q, q + 1 = p → q ∉ I) ∧ (p + 2 < n → p + 2 ∈ I)) := by
  have hbase : ∀ p ∈ dset n I, (dset n I).erase p ⊆ dset n (sw I p (p + 1)) := by
    intro p _ i hi
    obtain ⟨hne, hiD⟩ := Finset.mem_erase.mp hi
    obtain ⟨h1, h2, h3⟩ := mem_dset.mp hiD
    refine mem_dset.mpr ⟨mem_sw.mpr (Or.inr ⟨hne, h1⟩), h2, ?_⟩
    intro h
    rcases mem_sw.mp h with h | h
    · omega
    · exact h3 h.2
  by_cases hgt : R < (dset n I).card
  · left
    obtain ⟨p, hp⟩ := Finset.card_pos.mp (show 0 < (dset n I).card by omega)
    refine ⟨p, hp, ?_⟩
    have h1 := Finset.card_le_card (hbase p hp)
    rw [Finset.card_erase_of_mem hp] at h1
    omega
  · have heq : (dset n I).card = R := by omega
    by_cases hex : ∃ p ∈ dset n I, (∃ q, q + 1 = p ∧ q ∈ I) ∨ (p + 2 < n ∧ p + 2 ∉ I)
    · left
      obtain ⟨p, hp, hcase⟩ := hex
      obtain ⟨hpI, hp1, hp1I⟩ := mem_dset.mp hp
      refine ⟨p, hp, ?_⟩
      have key : ∃ x, x ∉ (dset n I).erase p ∧ x ∈ dset n (sw I p (p + 1)) := by
        rcases hcase with ⟨q, hq, hqI⟩ | ⟨h1, h2⟩
        · refine ⟨q, ?_, ?_⟩
          · intro h
            have := (mem_dset.mp (Finset.mem_of_mem_erase h)).2.2
            rw [hq] at this
            exact this hpI
          · refine mem_dset.mpr ⟨mem_sw.mpr (Or.inr ⟨by omega, hqI⟩), by omega, ?_⟩
            intro h
            rcases mem_sw.mp h with h | h
            · omega
            · exact h.1 hq
        · refine ⟨p + 1, ?_, ?_⟩
          · intro h
            exact hp1I (mem_dset.mp (Finset.mem_of_mem_erase h)).1
          · refine mem_dset.mpr ⟨mem_sw.mpr (Or.inl rfl), h1, ?_⟩
            intro h
            rcases mem_sw.mp h with h | h
            · omega
            · exact h2 h.2
      obtain ⟨x, hx1, hx2⟩ := key
      have hsub : insert x ((dset n I).erase p) ⊆ dset n (sw I p (p + 1)) := by
        intro z hz
        rcases Finset.mem_insert.mp hz with rfl | hz
        · exact hx2
        · exact hbase p hp hz
      have h1 := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem hx1, Finset.card_erase_of_mem hp] at h1
      omega
    · right
      refine ⟨heq, fun p hp => ⟨fun q hq hqI => hex ⟨p, hp, Or.inl ⟨q, hq, hqI⟩⟩, fun h1 => ?_⟩⟩
      by_contra h2
      exact hex ⟨p, hp, Or.inr ⟨h1, h2⟩⟩


/-- The explicit form of a terminal set. -/
lemma terminal_form {n k R : ℕ} {I : Finset ℕ} (hI : I ⊆ range n) (hk : I.card = k)
    (hR1 : 1 ≤ R) (hc : (dset n I).card = R)
    (hst : ∀ p ∈ dset n I, (∀ q, q + 1 = p → q ∉ I) ∧ (p + 2 < n → p + 2 ∈ I)) :
    ∃ d, d + 2 + (k - R) = n ∧ R ≤ k ∧
      I = (range R).image (fun i => d - 2 * i) ∪ Finset.Ico (d + 2) n := by
  have hne : (dset n I).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨hdI, hd1, hd1I⟩ := mem_dset.mp (Finset.max'_mem _ hne)
  have hmax : ∀ x ∈ dset n I, x ≤ (dset n I).max' hne := fun x hx => Finset.le_max' _ x hx
  have hdD : (dset n I).max' hne ∈ dset n I := Finset.max'_mem _ hne
  generalize (dset n I).max' hne = d at hdI hd1 hd1I hmax hdD
  -- (1) everything from d + 2 on is in I
  have h1 : ∀ x, d + 2 ≤ x → x < n → x ∈ I := by
    intro x hx
    induction x, hx using Nat.le_induction with
    | base => intro h; exact (hst d hdD).2 h
    | succ x hx ih =>
      intro hxn
      by_contra hcon
      have := hmax x (mem_dset.mpr ⟨ih (by omega), hxn, hcon⟩)
      omega
  -- (2) elements of I outside the set of free-successor positions are at least d + 2
  have h2 : ∀ x ∈ I, x ∉ dset n I → d + 2 ≤ x := by
    intro x hxI hxD
    by_contra hcon
    have hxd : x < d := by
      rcases Nat.lt_or_ge x d with h | h
      · exact h
      · exfalso
        have : x = d ∨ x = d + 1 := by omega
        rcases this with rfl | rfl
        · exact hxD hdD
        · exact hd1I hxI
    have hcl : ∀ t, x + t ≤ d → x + t ∈ I ∧ x + t ∉ dset n I := by
      intro t
      induction t with
      | zero => intro _; exact ⟨hxI, hxD⟩
      | succ t ih =>
        intro ht
        obtain ⟨ha, hb'⟩ := ih (by omega)
        have hin : x + t + 1 ∈ I := by
          by_contra hno
          exact hb' (mem_dset.mpr ⟨ha, by omega, hno⟩)
        refine ⟨hin, fun hD' => ?_⟩
        exact (hst _ hD').1 (x + t) rfl ha
    have := (hcl (d - x) (by omega)).2
    rw [show x + (d - x) = d by omega] at this
    exact this hdD
  -- (3) closure under adding 2 below d
  have h3 : ∀ j, ∀ p ∈ dset n I, p + 2 * j ≤ d → p + 2 * j ∈ dset n I := by
    intro j
    induction j with
    | zero => intro p hp _; simpa using hp
    | succ j ih =>
      intro p hp hle
      have hq := ih p hp (by omega)
      obtain ⟨hq1, hq2, hq3⟩ := mem_dset.mp hq
      have hne1 : p + 2 * j + 1 ≠ d := fun h => hq3 (h ▸ hdI)
      have hin : p + 2 * j + 2 ∈ I := (hst _ hq).2 (by omega)
      have : p + 2 * (j + 1) = p + 2 * j + 2 := by ring
      rw [this]
      by_contra hno
      have := h2 _ hin hno
      omega
  -- (4) every position is d - 2 j with j < R
  have h4 : ∀ p ∈ dset n I, ∃ j, j < R ∧ p + 2 * j = d := by
    intro p hp
    have hpd := hmax p hp
    have hq := h3 ((d - p) / 2) p hp (by omega)
    have heq : p + 2 * ((d - p) / 2) = d := by
      by_contra hne'
      have h5 : p + 2 * ((d - p) / 2) + 1 = d := by omega
      have := (mem_dset.mp hq).2.2
      rw [h5] at this
      exact this hdI
    refine ⟨(d - p) / 2, ?_, heq⟩
    have hinj : Function.Injective (fun i : ℕ => p + 2 * i) := fun x y hxy => by
      simp only at hxy; omega
    have hsub : (range ((d - p) / 2 + 1)).image (fun i => p + 2 * i) ⊆ dset n I := by
      intro z hz
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
      have := Finset.mem_range.mp hi
      exact h3 i p hp (by omega)
    have := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ hinj, Finset.card_range, hc] at this
    omega
  have hDeq : dset n I = (range R).image (fun i => d - 2 * i) := by
    apply Finset.eq_of_subset_of_card_le
    · intro p hp
      obtain ⟨j, hj, hpj⟩ := h4 p hp
      exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, by omega⟩
    · rw [hc]
      exact Finset.card_image_le.trans (by simp)
  have hIeq : I = dset n I ∪ Finset.Ico (d + 2) n := by
    ext x
    constructor
    · intro hx
      by_cases hxD : x ∈ dset n I
      · exact Finset.mem_union_left _ hxD
      · exact Finset.mem_union_right _
          (Finset.mem_Ico.mpr ⟨h2 x hx hxD, Finset.mem_range.mp (hI hx)⟩)
    · intro hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact (mem_dset.mp hx).1
      · have := Finset.mem_Ico.mp hx
        exact h1 x this.1 this.2
  have hdisj : Disjoint (dset n I) (Finset.Ico (d + 2) n) := by
    refine Finset.disjoint_left.mpr fun x hx hx2 => ?_
    have := hmax x hx
    have := (Finset.mem_Ico.mp hx2).1
    omega
  have hcard : k = R + (n - (d + 2)) := by
    have := congrArg Finset.card hIeq
    rw [Finset.card_union_of_disjoint hdisj, hc, hk, Nat.card_Ico] at this
    exact this
  refine ⟨d, by omega, by omega, ?_⟩
  rw [← hDeq]
  exact hIeq

/-- The terminal set with `g + 1` free successors. -/
def qset (n k g : ℕ) : Finset ℕ :=
  (range (g + 1)).image (fun i => (n + g - 1 - k) - 2 * i) ∪ Finset.Ico (n + g + 1 - k) n

/-- Middle phase: from a set with at least `g + 1` free successors up to `qset`, no hole. -/
lemma phaseB {n k g : ℕ} {b : ℕ → ℕ} {S : Finset ℕ} (hb : ∀ i, i + 1 < n → b i < b (i + 1))
    (hn : 1 ≤ n) (hkn : k + 1 ≤ n) (hg : b (n - 1) = b 0 + (n - 1) + g)
    (hS : ∀ I : Finset ℕ, I ⊆ range n → I.card = k → ∑ i ∈ I, b i ∈ S) :
    ∀ m, ∀ I : Finset ℕ, I ⊆ range n → I.card = k → g + 1 ≤ (dset n I).card →
      n * k - ∑ i ∈ I, i = m →
      (S.filter (· ≤ ∑ i ∈ I, b i)).card + ∑ i ∈ qset n k g, b i ≤
        (S.filter (· ≤ ∑ i ∈ qset n k g, b i)).card + ∑ i ∈ I, b i := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro I hI hk hD hm
    rcases good_move hD (by omega) with ⟨p, hp, hp2⟩ | ⟨hc, hst⟩
    · obtain ⟨hpI, hp1, hp1I⟩ := mem_dset.mp hp
      have hsub := sw_sub (x := p) hI hp1
      have hcard := (sw_card hpI hp1I).trans hk
      have hsum := sw_sum hpI hp1I b
      have hsumi := sw_sum hpI hp1I (fun j => j)
      have hbi := hb p hp1
      have hbound : ∑ i ∈ sw I p (p + 1), i ≤ n * k := by
        calc ∑ i ∈ sw I p (p + 1), i ≤ ∑ _i ∈ sw I p (p + 1), n :=
              Finset.sum_le_sum fun i hi => (Finset.mem_range.mp (hsub hi)).le
          _ = k * n := by simp [hcard]
          _ = n * k := Nat.mul_comm _ _
      have h1 := ih (n * k - ∑ i ∈ sw I p (p + 1), i) (by omega) (sw I p (p + 1))
        hsub hcard hp2 rfl
      have h2 := cnt_fill (S := S) (x := ∑ i ∈ I, b i) (y := ∑ i ∈ sw I p (p + 1), b i)
        (by omega) (fill hb hn hg hS hI hk hD hp)
      omega
    · obtain ⟨d, hd1, hd2, hd3⟩ := terminal_form hI hk (by omega) hc hst
      have hd : d = n + g - 1 - k := by omega
      have hd' : d + 2 = n + g + 1 - k := by omega
      have : I = qset n k g := by
        rw [hd3, qset, hd', hd]
      rw [this]


/-- The start set of the middle phase: a bottom run and `g` single elements. -/
def pset (k g : ℕ) : Finset ℕ :=
  range (k - g) ∪ (range g).image (fun u => k - g + 1 + 2 * u)

lemma pset_disj (k g : ℕ) :
    Disjoint (range (k - g)) ((range g).image (fun u => k - g + 1 + 2 * u)) := by
  refine Finset.disjoint_left.mpr fun x hx hx2 => ?_
  obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hx2
  have := Finset.mem_range.mp hx
  omega

lemma pset_inj (k g : ℕ) : Function.Injective (fun u : ℕ => k - g + 1 + 2 * u) := fun x y hxy => by
  simp only at hxy; omega

lemma pset_sum (k g : ℕ) (f : ℕ → ℕ) :
    ∑ i ∈ pset k g, f i = ∑ i ∈ range (k - g), f i + ∑ u ∈ range g, f (k - g + 1 + 2 * u) := by
  rw [pset, Finset.sum_union (pset_disj k g),
    Finset.sum_image (fun x _ y _ hxy => pset_inj k g hxy)]

lemma pset_sub {n k g : ℕ} (h1 : g + 1 ≤ k) (h2 : k + g + 1 ≤ n) : pset k g ⊆ range n := by
  intro x hx
  rcases Finset.mem_union.mp hx with hx | hx
  · have := Finset.mem_range.mp hx
    exact Finset.mem_range.mpr (by omega)
  · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    have := Finset.mem_range.mp hu
    exact Finset.mem_range.mpr (by omega)

lemma pset_card {k g : ℕ} (h1 : g + 1 ≤ k) : (pset k g).card = k := by
  rw [pset, Finset.card_union_of_disjoint (pset_disj k g),
    Finset.card_image_of_injective _ (pset_inj k g), Finset.card_range, Finset.card_range]
  omega

lemma pset_dset {n k g : ℕ} (h1 : g + 1 ≤ k) (h2 : k + g + 1 ≤ n) :
    g + 1 ≤ (dset n (pset k g)).card := by
  have hnot : ∀ x, x ∈ pset k g → x < k - g ∨ ∃ u, u < g ∧ x = k - g + 1 + 2 * u := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact Or.inl (Finset.mem_range.mp hx)
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
      exact Or.inr ⟨u, Finset.mem_range.mp hu, rfl⟩
  have hsub : insert (k - g - 1) ((range g).image (fun u => k - g + 1 + 2 * u)) ⊆
      dset n (pset k g) := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · refine mem_dset.mpr ⟨Finset.mem_union_left _ (Finset.mem_range.mpr (by omega)),
        by omega, fun h => ?_⟩
      rcases hnot _ h with h | ⟨u, _, h⟩ <;> omega
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
      have hu' := Finset.mem_range.mp hu
      refine mem_dset.mpr ⟨Finset.mem_union_right _ (Finset.mem_image.mpr ⟨u, hu, rfl⟩),
        by omega, fun h => ?_⟩
      rcases hnot _ h with h | ⟨u', _, h⟩ <;> omega
  have hni : k - g - 1 ∉ (range g).image (fun u => k - g + 1 + 2 * u) := by
    intro h
    obtain ⟨u, _, hu⟩ := Finset.mem_image.mp h
    omega
  have := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hni, Finset.card_image_of_injective _ (pset_inj k g),
    Finset.card_range] at this
  exact this

lemma qset_disj (n k g : ℕ) (_h1 : g + 1 ≤ k) (h2 : k + g + 1 ≤ n) :
    Disjoint ((range (g + 1)).image (fun i => (n + g - 1 - k) - 2 * i))
      (Finset.Ico (n + g + 1 - k) n) := by
  refine Finset.disjoint_left.mpr fun x hx hx2 => ?_
  obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hx
  have := (Finset.mem_Ico.mp hx2).1
  omega

lemma qset_inj (n k g : ℕ) (h2 : k + g + 1 ≤ n) :
    ∀ x ∈ range (g + 1), ∀ y ∈ range (g + 1),
      (n + g - 1 - k) - 2 * x = (n + g - 1 - k) - 2 * y → x = y := by
  intro x hx y hy hxy
  have := Finset.mem_range.mp hx
  have := Finset.mem_range.mp hy
  omega

lemma qset_sum (n k g : ℕ) (h1 : g + 1 ≤ k) (h2 : k + g + 1 ≤ n) (f : ℕ → ℕ) :
    ∑ i ∈ qset n k g, f i = ∑ i ∈ range (g + 1), f ((n + g - 1 - k) - 2 * i) +
      ∑ i ∈ Finset.Ico (n + g + 1 - k) n, f i := by
  rw [qset, Finset.sum_union (qset_disj n k g h1 h2), Finset.sum_image (qset_inj n k g h2)]

lemma qset_sub {n k g : ℕ} (h1 : g + 1 ≤ k) (h2 : k + g + 1 ≤ n) : qset n k g ⊆ range n := by
  intro x hx
  rcases Finset.mem_union.mp hx with hx | hx
  · obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_range.mpr (by omega)
  · exact Finset.mem_range.mpr (Finset.mem_Ico.mp hx).2

lemma qset_card {n k g : ℕ} (h1 : g + 1 ≤ k) (h2 : k + g + 1 ≤ n) : (qset n k g).card = k := by
  rw [qset, Finset.card_union_of_disjoint (qset_disj n k g h1 h2),
    Finset.card_image_of_injOn (fun x hx y hy hxy => qset_inj n k g h2 x hx y hy hxy),
    Finset.card_range, Nat.card_Ico]
  omega

/-- Rotation bound for two sums of the same length. -/
lemma rot (F G : ℕ → ℕ) (N h X Y : ℕ) (hh : h ≤ N)
    (h1 : ∀ j, j < h → F j ≤ G (N - h + j))
    (h2 : ∀ j, j < N - h → F (h + j) + Y ≤ G j + X) :
    ∑ j ∈ range N, F j + (N - h) * Y ≤ ∑ j ∈ range N, G j + (N - h) * X := by
  have e1 := Finset.sum_range_add F h (N - h)
  rw [show h + (N - h) = N by omega] at e1
  have e2 := Finset.sum_range_add G (N - h) h
  rw [show N - h + h = N by omega] at e2
  have a1 : ∑ j ∈ range h, F j ≤ ∑ j ∈ range h, G (N - h + j) :=
    Finset.sum_le_sum fun j hj => h1 j (Finset.mem_range.mp hj)
  have a2 : ∑ j ∈ range (N - h), (F (h + j) + Y) ≤ ∑ j ∈ range (N - h), (G j + X) :=
    Finset.sum_le_sum fun j hj => h2 j (Finset.mem_range.mp hj)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const,
    Finset.card_range, smul_eq_mul, smul_eq_mul] at a2
  omega

/-- Middle bound for two sums: the middle terms gain a fixed amount. -/
lemma mid (F G : ℕ → ℕ) (g c X Y : ℕ)
    (h0 : ∀ i, i < g + c + g → F i ≤ G i)
    (hm : ∀ j, j < c → F (g + j) + X ≤ G (g + j) + Y) :
    ∑ i ∈ range (g + c + g), F i + c * X ≤ ∑ i ∈ range (g + c + g), G i + c * Y := by
  rw [Finset.sum_range_add F (g + c) g, Finset.sum_range_add G (g + c) g,
    Finset.sum_range_add F g c, Finset.sum_range_add G g c]
  have a1 : ∑ j ∈ range g, F j ≤ ∑ j ∈ range g, G j :=
    Finset.sum_le_sum fun j hj => h0 j (by have := Finset.mem_range.mp hj; omega)
  have a3 : ∑ j ∈ range g, F (g + c + j) ≤ ∑ j ∈ range g, G (g + c + j) :=
    Finset.sum_le_sum fun j hj => h0 _ (by have := Finset.mem_range.mp hj; omega)
  have a2 : ∑ j ∈ range c, (F (g + j) + X) ≤ ∑ j ∈ range c, (G (g + j) + Y) :=
    Finset.sum_le_sum fun j hj => hm j (Finset.mem_range.mp hj)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const,
    Finset.card_range, smul_eq_mul, smul_eq_mul] at a2
  omega

/-- The cost of the two end phases is at most half of the total excess. -/
lemma final_ineq (a : ℕ → ℕ) (n k g : ℕ) (ha : ∀ i j, i ≤ j → j < n → a i ≤ a j)
    (hn : 20 ≤ n) (hk : k = n / 2) (h10 : 10 * g ≤ n) :
    2 * ∑ u ∈ range g, a (k - g + 1 + 2 * u) + 2 * ∑ j ∈ range (g + 1), a (n - k + j) +
        ∑ i ∈ range k, a i ≤
      2 * ∑ u ∈ range g, a (k - g + u) + 2 * ∑ j ∈ range (g + 1), a (n - k - g - 1 + 2 * j) +
        ∑ i ∈ range k, a (n - k + i) := by
  have hlohi : a (n - k - g - 1) ≤ a (n - k + g) := ha _ _ (by omega) (by omega)
  have rA := rot (fun u => a (k - g + 1 + 2 * u)) (fun u => a (k - g + u)) g (g / 2)
    (a (n - k + g)) (a (n - k - g - 1)) (by omega)
    (fun j hj => ha _ _ (by omega) (by omega))
    (fun j hj => by
      have e1 := ha (k - g + 1 + 2 * (g / 2 + j)) (n - k + g) (by omega) (by omega)
      have e2 := ha (n - k - g - 1) (k - g + j) (by omega) (by omega)
      change a (k - g + 1 + 2 * (g / 2 + j)) + a (n - k - g - 1) ≤ a (k - g + j) + a (n - k + g)
      omega)
  have rC := rot (fun j => a (n - k + j)) (fun j => a (n - k - g - 1 + 2 * j)) (g + 1)
    ((g + 1) / 2) (a (n - k + g)) (a (n - k - g - 1)) (by omega)
    (fun j hj => ha _ _ (by omega) (by omega))
    (fun j hj => by
      have e1 := ha (n - k + ((g + 1) / 2 + j)) (n - k + g) (by omega) (by omega)
      have e2 := ha (n - k - g - 1) (n - k - g - 1 + 2 * j) (by omega) (by omega)
      change a (n - k + ((g + 1) / 2 + j)) + a (n - k - g - 1) ≤
        a (n - k - g - 1 + 2 * j) + a (n - k + g)
      omega)
  have rE := mid (fun i => a i) (fun i => a (n - k + i)) g (k - 2 * g)
    (a (n - k + g)) (a (n - k - g - 1))
    (fun i hi => ha _ _ (by omega) (by omega))
    (fun j hj => by
      have e1 := ha (g + j) (n - k - g - 1) (by omega) (by omega)
      have e2 := ha (n - k + g) (n - k + (g + j)) (by omega) (by omega)
      change a (g + j) + a (n - k + g) ≤ a (n - k + (g + j)) + a (n - k - g - 1)
      omega)
  rw [show g + (k - 2 * g) + g = k by omega] at rE
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hlohi
  rw [hd] at rA rC rE
  have hc : 2 * ((g - g / 2) + (g + 1 - (g + 1) / 2)) ≤ k - 2 * g := by omega
  have hc2 := Nat.mul_le_mul_right d hc
  nlinarith [rA, rC, rE, hc2]


/-- The hole bound in index form. -/
theorem core {n k g : ℕ} {b : ℕ → ℕ} {S : Finset ℕ} (hn : 20 ≤ n) (hk : k = n / 2)
    (hb : ∀ i, i + 1 < n → b i < b (i + 1)) (hg : b (n - 1) = b 0 + (n - 1) + g)
    (h10 : 10 * g ≤ n)
    (hS : ∀ I : Finset ℕ, I ⊆ range n → I.card = k → ∑ i ∈ I, b i ∈ S) :
    2 * ((∑ i ∈ Finset.Ico (n - k) n, b i - ∑ i ∈ range k, b i + 1) - S.card) ≤
      (∑ i ∈ Finset.Ico (n - k) n, b i - ∑ i ∈ range k, b i) - k * (n - k) + g := by
  have h1 : g + 1 ≤ k := by omega
  have h2 : k + g + 1 ≤ n := by omega
  have hbi : ∀ i, i < n → i ≤ b i := fun i hi => by
    have := b_grow hb 0 i (Nat.zero_le _) hi
    omega
  have ha : ∀ i j, i ≤ j → j < n → b i - i ≤ b j - j := fun i j hij hj => by
    have := b_grow hb i j hij hj
    have := hbi i (by omega)
    omega
  have hsplit : ∀ I : Finset ℕ, I ⊆ range n →
      ∑ i ∈ I, b i = ∑ i ∈ I, (b i - i) + ∑ i ∈ I, i := by
    intro I hI
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    have := hbi i (Finset.mem_range.mp (hI hi))
    omega
  have hPsub : pset k g ⊆ range n := pset_sub h1 h2
  have hPcard := pset_card h1
  have hQsub : qset n k g ⊆ range n := qset_sub h1 h2
  have hQcard : (qset n k g).card = k := qset_card h1 h2
  have hA := (down_chain hb hS _ (pset k g) hPsub hPcard rfl).2
  have hB := phaseB hb (by omega) (by omega) hg hS _ (pset k g) hPsub hPcard
    (pset_dset h1 h2) rfl
  have hC := (up_chain hb (by omega) hS _ (qset n k g) hQsub hQcard rfl).2
  have hSc : (S.filter (· ≤ ∑ i ∈ qset n k g, b i)).card +
      (S.filter (∑ i ∈ qset n k g, b i < ·)).card = S.card := by
    have := Finset.card_filter_add_card_filter_not (s := S) (fun x => x ≤ ∑ i ∈ qset n k g, b i)
    have he : S.filter (fun x => ¬ x ≤ ∑ i ∈ qset n k g, b i) =
        S.filter (∑ i ∈ qset n k g, b i < ·) :=
      Finset.filter_congr fun x _ => not_le
    rw [he] at this
    exact this
  -- splitting of the four sums
  have sP := hsplit _ hPsub
  have sQ := hsplit _ hQsub
  have sbot := hsplit (range k) (fun x hx => Finset.mem_range.mpr
    (by have := Finset.mem_range.mp hx; omega))
  have stop := hsplit (Finset.Ico (n - k) n) (fun x hx => Finset.mem_range.mpr
    (Finset.mem_Ico.mp hx).2)
  have itop : ∑ i ∈ Finset.Ico (n - k) n, i = ∑ i ∈ range k, i + k * (n - k) := by
    rw [Finset.sum_Ico_eq_sum_range, show n - (n - k) = k by omega, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_range, smul_eq_mul]
    omega
  -- the parts of the sums of `b i - i`
  have aP := pset_sum k g (fun i => b i - i)
  have abot := Finset.sum_range_add (fun i => b i - i) (k - g) g
  rw [show k - g + g = k by omega] at abot
  have aQ := qset_sum n k g h1 h2 (fun i => b i - i)
  have hrefl := Finset.sum_range_reflect (fun j => b (n - k - g - 1 + 2 * j) - (n - k - g - 1 + 2 * j))
    (g + 1)
  have hrefl2 : ∑ j ∈ range (g + 1),
      (b (n - k - g - 1 + 2 * (g + 1 - 1 - j)) - (n - k - g - 1 + 2 * (g + 1 - 1 - j))) =
      ∑ i ∈ range (g + 1), (b ((n + g - 1 - k) - 2 * i) - ((n + g - 1 - k) - 2 * i)) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have := Finset.mem_range.mp hj
    rw [show n - k - g - 1 + 2 * (g + 1 - 1 - j) = (n + g - 1 - k) - 2 * j by omega]
  have atop1 := Finset.sum_Ico_consecutive (fun i => b i - i)
    (show n - k ≤ n + g + 1 - k by omega) (show n + g + 1 - k ≤ n by omega)
  have atop2 := Finset.sum_Ico_eq_sum_range (fun i => b i - i) (n - k) (n + g + 1 - k)
  rw [show n + g + 1 - k - (n - k) = g + 1 by omega] at atop2
  have atop3 := Finset.sum_Ico_eq_sum_range (fun i => b i - i) (n - k) n
  rw [show n - (n - k) = k by omega] at atop3
  have hfin := final_ineq (fun i => b i - i) n k g ha hn hk h10
  simp only at aP abot aQ hrefl atop1 atop2 atop3 hfin
  have eQ : ∑ i ∈ qset n k g, (b i - i) =
      ∑ j ∈ range (g + 1), (b (n - k - g - 1 + 2 * j) - (n - k - g - 1 + 2 * j)) +
        ∑ i ∈ Finset.Ico (n + g + 1 - k) n, (b i - i) := by
    rw [aQ, ← hrefl2, hrefl]
  have etop : ∑ i ∈ Finset.Ico (n - k) n, (b i - i) =
      ∑ j ∈ range (g + 1), (b (n - k + j) - (n - k + j)) +
        ∑ i ∈ Finset.Ico (n + g + 1 - k) n, (b i - i) := by
    rw [← atop1, atop2]
  have key : ∑ i ∈ Finset.Ico (n - k) n, (b i - i) + 2 * ∑ i ∈ pset k g, (b i - i) ≤
      2 * ∑ i ∈ qset n k g, (b i - i) + ∑ i ∈ range k, (b i - i) := by
    have e3 := etop
    rw [atop3] at e3
    rw [eQ, aP, abot, etop]
    omega
  have e1 : ∑ i ∈ pset k g, i + 1 + ∑ i ∈ qset n k g, b i + ∑ i ∈ Finset.Ico (n - k) n, i ≤
      S.card + ∑ i ∈ pset k g, b i + ∑ i ∈ range k, i + ∑ i ∈ qset n k g, i := by
    rw [← hSc]
    omega
  have hSpos : 1 ≤ S.card := Finset.card_pos.mpr ⟨_, hS _ hPsub hPcard⟩
  clear hA hB hC hSc aP abot aQ hrefl hrefl2 atop1 atop2 atop3 hfin eQ etop
  generalize ∑ i ∈ pset k g, i = iP at *
  generalize ∑ i ∈ qset n k g, i = iQ at *
  generalize ∑ i ∈ range k, i = ibot at *
  generalize ∑ i ∈ Finset.Ico (n - k) n, i = itp at *
  generalize ∑ i ∈ pset k g, b i = sP' at *
  generalize ∑ i ∈ qset n k g, b i = sQ' at *
  generalize ∑ i ∈ range k, b i = sbot' at *
  generalize ∑ i ∈ Finset.Ico (n - k) n, b i = stop' at *
  generalize ∑ i ∈ pset k g, (b i - i) = aP' at *
  generalize ∑ i ∈ qset n k g, (b i - i) = aQ' at *
  generalize ∑ i ∈ range k, (b i - i) = abot' at *
  generalize ∑ i ∈ Finset.Ico (n - k) n, (b i - i) = atop' at *
  generalize k * (n - k) = K at *
  omega

end OMA.P_Erdos875_DF_R1_H3

theorem OMA.solution : OMA.R_Erdos875_erdos_875_variants_deshouillers_freiman_R1.H3 := by
  intro B hB h20 L M hLM hL hM h10
  have hpos : 0 < B.card := by omega
  -- the increasing enumeration of `B`
  obtain ⟨b, hbdef⟩ : ∃ b : ℕ → ℕ, ∀ i (h : i < B.card), b i = B.orderEmbOfFin rfl ⟨i, h⟩ :=
    ⟨fun i => if h : i < B.card then (B.orderEmbOfFin rfl ⟨i, h⟩ : ℕ) else 0,
      fun i h => by simp [h]⟩
  have hb : ∀ i, i + 1 < B.card → b i < b (i + 1) := by
    intro i hi
    rw [hbdef i (by omega), hbdef (i + 1) hi]
    exact (B.orderEmbOfFin rfl).strictMono (Fin.mk_lt_mk.mpr (Nat.lt_succ_self i))
  have hmono : ∀ i j, i < j → j < B.card → b i < b j := by
    intro i j hij hj
    have := OMA.P_Erdos875_DF_R1_H3.b_grow hb i j hij.le hj
    omega
  have hinj : ∀ x ∈ Finset.range B.card, ∀ y ∈ Finset.range B.card, b x = b y → x = y := by
    intro x hx y hy hxy
    have hx' := Finset.mem_range.mp hx
    have hy' := Finset.mem_range.mp hy
    rcases Nat.lt_trichotomy x y with h | h | h
    · have := hmono x y h hy'; omega
    · exact h
    · have := hmono y x h hx'; omega
  have hmemB : ∀ i, i < B.card → b i ∈ B := by
    intro i hi
    rw [hbdef i hi]
    exact Finset.orderEmbOfFin_mem B rfl ⟨i, hi⟩
  have hsurj : ∀ x ∈ B, ∃ i, i < B.card ∧ b i = x := by
    intro x hx
    have hr : x ∈ Set.range (B.orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]
      exact hx
    obtain ⟨⟨i, hi⟩, rfl⟩ := hr
    exact ⟨i, hi, hbdef i hi⟩
  have hb0 : b 0 = B.min' hB := by
    rw [hbdef 0 hpos]
    exact Finset.orderEmbOfFin_zero rfl hpos
  have hbn : b (B.card - 1) = B.max' hB := by
    rw [hbdef (B.card - 1) (by omega)]
    exact Finset.orderEmbOfFin_last rfl hpos
  -- sums over index sets are sums of subsets of `B`
  have hS : ∀ I : Finset ℕ, I ⊆ Finset.range B.card → I.card = B.card / 2 →
      ∑ i ∈ I, b i ∈ (B.powersetCard (B.card / 2)).image (fun T => ∑ x ∈ T, x) := by
    intro I hI hk
    have hinjI : ∀ x ∈ I, ∀ y ∈ I, b x = b y → x = y :=
      fun x hx y hy hxy => hinj x (hI hx) y (hI hy) hxy
    refine Finset.mem_image.mpr ⟨I.image b, Finset.mem_powersetCard.mpr ⟨?_, ?_⟩, ?_⟩
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact hmemB i (Finset.mem_range.mp (hI hi))
    · rw [Finset.card_image_of_injOn (fun x hx y hy hxy => hinjI x hx y hy hxy), hk]
    · exact Finset.sum_image hinjI
  have hT : ∀ T ∈ B.powersetCard (B.card / 2), ∃ I : Finset ℕ, I ⊆ Finset.range B.card ∧
      I.card = B.card / 2 ∧ ∑ i ∈ I, b i = ∑ x ∈ T, x := by
    intro T hT
    obtain ⟨hTB, hTc⟩ := Finset.mem_powersetCard.mp hT
    have hI : (Finset.range B.card).filter (fun i => b i ∈ T) ⊆ Finset.range B.card :=
      Finset.filter_subset _ _
    have hinjI : ∀ x ∈ (Finset.range B.card).filter (fun i => b i ∈ T),
        ∀ y ∈ (Finset.range B.card).filter (fun i => b i ∈ T), b x = b y → x = y :=
      fun x hx y hy hxy => hinj x (hI hx) y (hI hy) hxy
    have himg : ((Finset.range B.card).filter (fun i => b i ∈ T)).image b = T := by
      ext x
      constructor
      · intro hx
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
        exact (Finset.mem_filter.mp hi).2
      · intro hx
        obtain ⟨i, hi, rfl⟩ := hsurj x (hTB hx)
        exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, hx⟩, rfl⟩
    refine ⟨_, hI, ?_, ?_⟩
    · have hc := Finset.card_image_of_injOn (s := (Finset.range B.card).filter (fun i => b i ∈ T))
        (f := b) (fun x hx y hy hxy => hinjI x hx y hy hxy)
      rw [himg] at hc
      omega
    · have hs := Finset.sum_image (f := fun x : ℕ => x) hinjI
      rw [himg] at hs
      exact hs.symm
  have hkn : B.card / 2 ≤ B.card := Nat.div_le_self _ _
  -- the two extreme sums
  have hLeq : L = ∑ i ∈ Finset.range (B.card / 2), b i := by
    apply le_antisymm
    · have hsub : Finset.range (B.card / 2) ⊆ Finset.range B.card := fun x hx =>
        Finset.mem_range.mpr (by have := Finset.mem_range.mp hx; omega)
      obtain ⟨T, hT1, hT2⟩ := Finset.mem_image.mp (hS _ hsub (Finset.card_range _))
      rw [← hT2]
      exact (hLM T hT1).1
    · obtain ⟨T, hT1, hT2⟩ := hL
      obtain ⟨I, hI1, hI2, hI3⟩ := hT T hT1
      rw [← hT2, ← hI3]
      exact (OMA.P_Erdos875_DF_R1_H3.down_chain hb hS _ I hI1 hI2 rfl).1
  have hMeq : M = ∑ i ∈ Finset.Ico (B.card - B.card / 2) B.card, b i := by
    apply le_antisymm
    · obtain ⟨T, hT1, hT2⟩ := hM
      obtain ⟨I, hI1, hI2, hI3⟩ := hT T hT1
      rw [← hT2, ← hI3]
      exact (OMA.P_Erdos875_DF_R1_H3.up_chain hb hkn hS _ I hI1 hI2 rfl).1
    · have hsub : Finset.Ico (B.card - B.card / 2) B.card ⊆ Finset.range B.card := fun x hx =>
        Finset.mem_range.mpr (Finset.mem_Ico.mp hx).2
      have hc : (Finset.Ico (B.card - B.card / 2) B.card).card = B.card / 2 := by
        rw [Nat.card_Ico]; omega
      obtain ⟨T, hT1, hT2⟩ := Finset.mem_image.mp (hS _ hsub hc)
      rw [← hT2]
      exact (hLM T hT1).2
  have hgrow := OMA.P_Erdos875_DF_R1_H3.b_grow hb 0 (B.card - 1) (Nat.zero_le _) (by omega)
  have hcore := OMA.P_Erdos875_DF_R1_H3.core (n := B.card) (k := B.card / 2)
    (g := b (B.card - 1) - b 0 - (B.card - 1)) (b := b) h20 rfl hb (by omega)
    (by rw [hb0, hbn]; exact h10) hS
  rw [hLeq, hMeq, ← hb0, ← hbn]
  exact hcore
