import OMAReductions.R_Erdos875_erdos_875_variants_deshouillers_freiman_R1_H1_R1
import Mathlib

-- Step H2 of reduction Erdos875.erdos_875.variants.deshouillers_freiman.R1.H1.R1 (Erdos Problem 875):
-- the fill lemma for sums of s terms of a dense increasing sequence.
-- Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)
--
-- Claim: b_0 < ... < b_(n-1) with g missing integers, g + 1 <= s, s + g + 1 <= n. Then every v
-- with (sum of the s smallest) + 2 (g+1)^2 <= v <= (sum of the s largest) - 2 (g+1)^2 is a sum
-- of s distinct terms.
-- Proof sketch (the middle phase of the proof of step H3 of the parent reduction, in pointwise
-- form). Index sets I of size s; a move replaces an index p by a free index p + 1; D(I) is the
-- set of possible moves. If |D(I)| >= g + 1, a move leaves no hole (fill), and some move keeps
-- |D| >= g + 1 unless I is the terminal set Q (good_move, terminal_form). The start set P (a
-- bottom run and g single elements) has |D(P)| >= g + 1, its sum is at most the least sum plus
-- 2 (g+1)^2, and the sum of Q is at least the largest sum minus 2 (g+1)^2.

namespace OMA.P_Erdos875_DF_Fill

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


/-- Middle phase in pointwise form: every number from the sum of `I` up to the sum of the
terminal set is a sum. -/
lemma phaseB' {n k g : ℕ} {b : ℕ → ℕ} {S : Finset ℕ} (hb : ∀ i, i + 1 < n → b i < b (i + 1))
    (hn : 1 ≤ n) (hg : b (n - 1) = b 0 + (n - 1) + g)
    (hS : ∀ I : Finset ℕ, I ⊆ range n → I.card = k → ∑ i ∈ I, b i ∈ S) :
    ∀ m, ∀ I : Finset ℕ, I ⊆ range n → I.card = k → g + 1 ≤ (dset n I).card →
      n * k - ∑ i ∈ I, i = m →
      ∀ v, ∑ i ∈ I, b i ≤ v → v ≤ ∑ i ∈ qset n k g, b i → v ∈ S := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro I hI hk hD hm v hv1 hv2
    rcases good_move hD (by omega) with ⟨p, hp, hp2⟩ | ⟨hc, hst⟩
    · obtain ⟨hpI, hp1, hp1I⟩ := mem_dset.mp hp
      have hsub := sw_sub (x := p) hI hp1
      have hcard := (sw_card hpI hp1I).trans hk
      have hsumi := sw_sum hpI hp1I (fun j => j)
      have hbound : ∑ i ∈ sw I p (p + 1), i ≤ n * k := by
        calc ∑ i ∈ sw I p (p + 1), i ≤ ∑ _i ∈ sw I p (p + 1), n :=
              Finset.sum_le_sum fun i hi => (Finset.mem_range.mp (hsub hi)).le
          _ = k * n := by simp [hcard]
          _ = n * k := Nat.mul_comm _ _
      by_cases hle : v ≤ ∑ i ∈ sw I p (p + 1), b i
      · by_cases heq : v = ∑ i ∈ I, b i
        · rw [heq]; exact hS I hI hk
        · exact fill hb hn hg hS hI hk hD hp v (by omega) hle
      · exact ih (n * k - ∑ i ∈ sw I p (p + 1), i) (by omega) (sw I p (p + 1))
          hsub hcard hp2 rfl v (by omega) hv2
    · obtain ⟨d, hd1, hd2, hd3⟩ := terminal_form hI hk (by omega) hc hst
      have hd : d = n + g - 1 - k := by omega
      have hd' : d + 2 = n + g + 1 - k := by omega
      have hIq : I = qset n k g := by
        rw [hd3, qset, hd', hd]
      rw [hIq] at hv1
      have : v = ∑ i ∈ qset n k g, b i := by omega
      rw [this, ← hIq]
      exact hS I hI hk

/-- The fill statement. -/
theorem fill_main (n s g : ℕ) (b : ℕ → ℕ) (hb : ∀ i, i + 1 < n → b i < b (i + 1))
    (hg : b (n - 1) = b 0 + (n - 1) + g) (h1 : g + 1 ≤ s) (h2 : s + g + 1 ≤ n) (v : ℕ)
    (hv1 : ∑ i ∈ Finset.range s, b i + 2 * (g + 1) ^ 2 ≤ v)
    (hv2 : v + 2 * (g + 1) ^ 2 ≤ ∑ i ∈ Finset.Ico (n - s) n, b i) :
    ∃ I : Finset ℕ, I ⊆ Finset.range n ∧ I.card = s ∧ ∑ i ∈ I, b i = v := by
  have hgrow := b_grow hb
  have hdiff : ∀ i j, i ≤ j → j < n → b j ≤ b i + (j - i) + g := by
    intro i j hij hj
    have e1 := hgrow 0 i (Nat.zero_le _) (by omega)
    have e2 := hgrow j (n - 1) (by omega) (by omega)
    omega
  have hS : ∀ I : Finset ℕ, I ⊆ range n → I.card = s →
      ∑ i ∈ I, b i ∈ ((range n).powersetCard s).image (fun I => ∑ i ∈ I, b i) :=
    fun I hI hc => Finset.mem_image.mpr ⟨I, Finset.mem_powersetCard.mpr ⟨hI, hc⟩, rfl⟩
  -- the start set is near the bottom
  have hP : ∑ i ∈ pset s g, b i ≤ ∑ i ∈ range s, b i + 2 * (g + 1) ^ 2 := by
    rw [pset_sum]
    have e1 := Finset.sum_range_add b (s - g) g
    rw [show s - g + g = s by omega] at e1
    have e2 : ∑ u ∈ range g, b (s - g + 1 + 2 * u) ≤ ∑ u ∈ range g, (b (s - g + u) + 2 * g) :=
      Finset.sum_le_sum fun u hu => by
        have hu' := Finset.mem_range.mp hu
        have := hdiff (s - g + u) (s - g + 1 + 2 * u) (by omega) (by omega)
        omega
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul] at e2
    have e3 : g * (2 * g) ≤ 2 * (g + 1) ^ 2 := by nlinarith
    omega
  -- the terminal set is near the top
  have hQ : ∑ i ∈ Finset.Ico (n - s) n, b i ≤ ∑ i ∈ qset n s g, b i + 2 * (g + 1) ^ 2 := by
    rw [qset_sum n s g h1 h2]
    have e1 := Finset.sum_Ico_consecutive b (show n - s ≤ n + g + 1 - s by omega)
      (show n + g + 1 - s ≤ n by omega)
    have e2 := Finset.sum_Ico_eq_sum_range b (n - s) (n + g + 1 - s)
    rw [show n + g + 1 - s - (n - s) = g + 1 by omega] at e2
    have e3 := Finset.sum_range_reflect (fun j => b (n - s + j)) (g + 1)
    have e4 : ∑ j ∈ range (g + 1), b (n - s + (g + 1 - 1 - j)) ≤
        ∑ i ∈ range (g + 1), (b ((n + g - 1 - s) - 2 * i) + 2 * (g + 1)) :=
      Finset.sum_le_sum fun j hj => by
        have hj' := Finset.mem_range.mp hj
        have := hdiff ((n + g - 1 - s) - 2 * j) (n - s + (g + 1 - 1 - j)) (by omega) (by omega)
        omega
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul] at e4
    have e5 : (g + 1) * (2 * (g + 1)) = 2 * (g + 1) ^ 2 := by ring
    omega
  have hmem := phaseB' hb (by omega) hg hS _ (pset s g) (pset_sub h1 h2) (pset_card h1)
    (pset_dset h1 h2) rfl v (by omega) (by omega)
  obtain ⟨I, hI, hIs⟩ := Finset.mem_image.mp hmem
  obtain ⟨hI1, hI2⟩ := Finset.mem_powersetCard.mp hI
  exact ⟨I, hI1, hI2, hIs⟩

end OMA.P_Erdos875_DF_Fill

theorem OMA.solution : OMA.R_Erdos875_erdos_875_variants_deshouillers_freiman_R1_H1_R1.H2 :=
  fun n s g b hb hg h1 h2 v hv1 hv2 =>
    OMA.P_Erdos875_DF_Fill.fill_main n s g b hb hg h1 h2 v hv1 hv2
