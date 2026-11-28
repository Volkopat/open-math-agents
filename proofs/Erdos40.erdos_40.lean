import FormalConjectures.ErdosProblems.«40»
import Mathlib.NumberTheory.Bertrand

/-!
# Finite tests for individual denominators in Erdős problem 40

At a fixed representation bound and cutoff, `survivors` enumerates the subsets
of a finite interval meeting prescribed integer lower bounds on their prefixes.
The test counts ordered representations and allows zero in a set, as in the
upstream statement. Only positive elements count toward the density.

The numerical answer uses tables of maximal count vectors that can be computed
before a denominator is supplied. The criterion does not settle whether there
is any divergent denominator satisfying it.

The compactness argument is related to the project reduction for the existential
variant by Nicholas Wierenga. Here the lower bounds may vary at every integer.

A separate Sidon construction rules out fourth-root denominators even when
they drop to a logarithm on each fixed band [s, 2s], with s ranging through
the scales defined below. It also gives a failed denominator agreeing with any
prescribed divergent function on arbitrarily late intervals [M, dM] for every
d. The finite Sidon blocks and their gluing lemma are from @Dugongue's proof
of Erdos329.exists_sidon_pos_density, building on the project's proof of
Erdos44.sidon_set_lower_bound.

Credit: @ubuwaits
-/

namespace Erdos40Windows

open AdditiveCombinatorics Filter Real Set

/-- Number of ordered representations inside a finite set. -/
def pairCount (B : Finset ℕ) (s : ℕ) : ℕ :=
  ((Finset.HasAntidiagonal.antidiagonal s).filter
    (fun p : ℕ × ℕ ↦ p.1 ∈ B ∧ p.2 ∈ B)).card

def prefixCount (B : Finset ℕ) (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).filter (· ∈ B)).card

/-- The cap and the first density index are both `k`. A sum of size at most
`T` has both summands in the prefix, so these tests persist under restriction. -/
def survivors (q : ℕ → ℕ) (k T : ℕ) : Finset (Finset ℕ) :=
  (Finset.range (T + 1)).powerset.filter fun B ↦
    (List.range (T + 1)).all (fun s ↦ decide (pairCount B s ≤ k)) &&
    (List.range (T + 1)).all (fun n ↦ decide (k ≤ n → q n ≤ prefixCount B n))

private theorem mem_survivors {q : ℕ → ℕ} {k T : ℕ} {B : Finset ℕ} :
    B ∈ survivors q k T ↔ B ⊆ Finset.range (T + 1) ∧
      (∀ s ≤ T, pairCount B s ≤ k) ∧
      (∀ n ≤ T, k ≤ n → q n ≤ prefixCount B n) := by
  simp only [survivors, Finset.mem_filter, Finset.mem_powerset, Bool.and_eq_true,
    List.all_eq_true, decide_eq_true_eq, List.mem_range, Nat.lt_succ_iff]

private noncomputable def truncation (A : Set ℕ) (T : ℕ) : Finset ℕ :=
  by classical exact (Finset.range (T + 1)).filter (fun n ↦ n ∈ A)

private theorem mem_truncation {A : Set ℕ} {i T : ℕ} :
    i ∈ truncation A T ↔ i ∈ Finset.range (T + 1) ∧ i ∈ A := by
  classical exact Finset.mem_filter

private theorem pairCount_truncation (A : Set ℕ) {s T : ℕ} (hs : s ≤ T) :
    pairCount (truncation A T) s = sumRep A s := by
  classical
  rw [pairCount, sumRep_def]
  congr 1
  apply Finset.filter_congr
  intro p hp
  have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  have h₁ : p.1 < T + 1 := by omega
  have h₂ : p.2 < T + 1 := by omega
  simp [truncation, h₁, h₂]

private theorem prefixCount_truncation (A : Set ℕ) {n T : ℕ} (hn : n ≤ T) :
    prefixCount (truncation A T) n = (A ∩ Icc 1 n).ncard := by
  classical
  have heq : ↑((Finset.Icc 1 n).filter (· ∈ truncation A T)) = A ∩ Icc 1 n := by
    ext i
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc, truncation,
      Finset.mem_range, Set.mem_inter_iff, Set.mem_Icc]
    exact ⟨fun ⟨hi, _, ha⟩ ↦ ⟨ha, hi⟩,
      fun ⟨ha, hi⟩ ↦ ⟨hi, by omega, ha⟩⟩
  rw [← heq, Set.ncard_coe_finset, prefixCount]

private def Fits (q : ℕ → ℕ) (k T : ℕ) (A : Set ℕ) : Prop :=
  (∀ s ≤ T, sumRep A s ≤ k) ∧
  (∀ n, k ≤ n → n ≤ T → q n ≤ (A ∩ Icc 1 n).ncard)

private theorem truncation_mem (q : ℕ → ℕ) (k T : ℕ) (A : Set ℕ) :
    truncation A T ∈ survivors q k T ↔ Fits q k T A := by
  classical
  have hsub : truncation A T ⊆ Finset.range (T + 1) := Finset.filter_subset _ _
  rw [mem_survivors, and_iff_right hsub]
  constructor
  · rintro ⟨hr, hd⟩
    exact ⟨fun s hs ↦ pairCount_truncation A hs ▸ hr s hs,
      fun n hk hn ↦ prefixCount_truncation A hn ▸ hd n hn hk⟩
  · rintro ⟨hr, hd⟩
    exact ⟨fun s hs ↦ (pairCount_truncation A hs).symm ▸ hr s hs,
      fun n hn hk ↦ (prefixCount_truncation A hn).symm ▸ hd n hk hn⟩

private def decode (f : ℕ → Bool) : Set ℕ := {n | f n = true}

private theorem closed_prefix_test (q : ℕ → ℕ) (k T : ℕ) :
    IsClosed {f : ℕ → Bool | truncation (decode f) T ∈ survivors q k T} := by
  classical
  apply isOpen_compl_iff.mp
  refine isOpen_pi_iff.mpr ?_
  intro f hf
  refine ⟨Finset.range (T + 1), fun i ↦ {f i}, fun i _ ↦ ⟨isOpen_discrete _, by simp⟩, ?_⟩
  intro g hg
  have heq : truncation (decode g) T = truncation (decode f) T := by
    ext i
    simp only [mem_truncation, decode, Set.mem_ofPred_eq]
    by_cases hi : i ∈ Finset.range (T + 1)
    · have hgi : g i = f i := Set.mem_pi.mp hg i hi
      rw [hgi]
    · simp only [hi, false_and]
  change truncation (decode g) T ∉ survivors q k T
  exact heq ▸ hf

/-- Compatible finite witnesses exist whenever every finite test has a survivor. -/
theorem finite_to_infinite (q : ℕ → ℕ) (k : ℕ)
    (h : ∀ T, (survivors q k T).Nonempty) :
    ∃ A : Set ℕ, (∀ s, sumRep A s ≤ k) ∧
      ∀ n, k ≤ n → q n ≤ (A ∩ Icc 1 n).ncard := by
  classical
  let K (T : ℕ) : Set (ℕ → Bool) := {f | truncation (decode f) T ∈ survivors q k T}
  have nested (T : ℕ) : K (T + 1) ⊆ K T := by
    intro f hf
    change truncation (decode f) (T + 1) ∈ survivors q k (T + 1) at hf
    obtain ⟨hr, hd⟩ := (truncation_mem q k (T + 1) (decode f)).mp hf
    exact (truncation_mem q k T (decode f)).mpr
      ⟨fun s hs ↦ hr s (Nat.le_succ_of_le hs),
        fun n hk hn ↦ hd n hk (Nat.le_succ_of_le hn)⟩
  have inhabited (T : ℕ) : (K T).Nonempty := by
    obtain ⟨B, hB⟩ := h T
    refine ⟨fun n ↦ decide (n ∈ B), ?_⟩
    have hsub := (mem_survivors.mp hB).1
    have heq : truncation (decode (fun n ↦ decide (n ∈ B))) T = B := by
      ext i
      simp only [truncation, Finset.mem_filter, decode, Set.mem_ofPred_eq, decide_eq_true_eq]
      exact ⟨And.right, fun hi ↦ ⟨hsub hi, hi⟩⟩
    change truncation (decode (fun n ↦ decide (n ∈ B))) T ∈ survivors q k T
    rwa [heq]
  obtain ⟨f, hf⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    K nested inhabited (closed_prefix_test q k 0).isCompact (closed_prefix_test q k)
  have allFits (T : ℕ) := (truncation_mem q k T (decode f)).mp (Set.mem_iInter.mp hf T)
  exact ⟨decode f, fun s ↦ (allFits s).1 s le_rfl,
    fun n hn ↦ (allFits n).2 n hn le_rfl⟩

/-- The least integer count meeting the density inequality with multiplier `k + 1`. -/
noncomputable def quota (g : ℕ → ℝ) (k n : ℕ) : ℕ :=
  ⌈‖√(n : ℝ) / g n‖ / (↑(k + 1) : ℝ)⌉₊

private theorem quota_le (g : ℕ → ℝ) (k n c : ℕ) :
    quota g k n ≤ c ↔ ‖√(n : ℝ) / g n‖ ≤ (↑(k + 1) : ℝ) * (c : ℝ) := by
  rw [quota, Nat.ceil_le, div_le_iff₀ (by positivity), mul_comm]

private theorem cap_of_limsup_ne_top {A : Set ℕ}
    (h : limsup (fun n ↦ (sumRep A n : ℕ∞)) atTop ≠ ⊤) :
    ∃ k : ℕ, ∀ n, sumRep A n ≤ k := by
  obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.mp h
  have hlt : limsup (fun n ↦ (sumRep A n : ℕ∞)) atTop < (↑(b + 1) : ℕ∞) := by
    rw [← hb]
    exact_mod_cast Nat.lt_succ_self b
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_lt_of_limsup_lt hlt)
  refine ⟨max b ((Finset.range N).sup (sumRep A)), fun n ↦ ?_⟩
  by_cases hn : N ≤ n
  · have hh : sumRep A n < b + 1 := by exact_mod_cast hN n hn
    exact (Nat.le_of_lt_succ hh).trans (le_max_left ..)
  · exact (Finset.le_sup (f := sumRep A) (Finset.mem_range.mpr (by omega : n < N))).trans
      (le_max_right ..)

private theorem ne_limsup_top_of_cap {A : Set ℕ} {k : ℕ} (h : ∀ s, sumRep A s ≤ k) :
    limsup (fun n ↦ (sumRep A n : ℕ∞)) atTop ≠ ⊤ := by
  have hle : limsup (fun n ↦ (sumRep A n : ℕ∞)) atTop ≤ (k : ℕ∞) :=
    limsup_le_of_le (h := Eventually.of_forall (fun n ↦ by exact_mod_cast h n))
  exact (hle.trans_lt (ENat.natCast_lt_top k)).ne

/-- A single finite cutoff must rule out each combination of a fixed cap,
density constant and starting index. Enlarging `k` covers any such triple. -/
theorem erdos40For_iff_finite (g : ℕ → ℝ) :
    Erdos40.Erdos40For g ↔ ∀ k : ℕ, ∃ T ≥ k, survivors (quota g k) k T = ∅ := by
  classical
  constructor
  · intro h k
    by_contra! hnone
    have hne (T : ℕ) : (survivors (quota g k) k T).Nonempty := by
      by_cases hk : k ≤ T
      · exact hnone T hk
      · refine ⟨truncation ∅ T, (truncation_mem _ _ _ _).mpr ⟨?_, ?_⟩⟩
        · simp [sumRep_def]
        · intro n hn hn'
          omega
    obtain ⟨A, hr, hd⟩ := finite_to_infinite _ k hne
    apply ne_limsup_top_of_cap hr
    apply h A
    apply Asymptotics.IsBigO.of_bound (↑(k + 1) : ℝ)
    filter_upwards [eventually_ge_atTop k] with n hn
    simpa only [Real.norm_natCast] using (quota_le g k n _).mp (hd n hn)
  · intro h A hdense
    by_contra hlim
    obtain ⟨r, hr⟩ := cap_of_limsup_ne_top hlim
    obtain ⟨C, hC⟩ := Asymptotics.isBigO_iff.mp hdense
    obtain ⟨L, hL⟩ := eventually_atTop.mp hC
    obtain ⟨c, hc⟩ := exists_nat_ge C
    let k := max r (max c L)
    have hrk : r ≤ k := le_max_left ..
    have hck : c ≤ k := (le_max_left c L).trans (le_max_right ..)
    have hLk : L ≤ k := (le_max_right c L).trans (le_max_right ..)
    have hCk : C ≤ (↑(k + 1) : ℝ) := hc.trans (by exact_mod_cast Nat.le_succ_of_le hck)
    obtain ⟨T, _, hT⟩ := h k
    have hmem : truncation A T ∈ survivors (quota g k) k T := by
      apply (truncation_mem ..).mpr
      refine ⟨fun s _ ↦ (hr s).trans hrk, fun n hn _ ↦ ?_⟩
      apply (quota_le ..).mpr
      have hb := hL n (hLk.trans hn)
      simp only [Real.norm_natCast] at hb
      exact hb.trans (mul_le_mul_of_nonneg_right hCk (Nat.cast_nonneg _))
    simp only [hT, Finset.notMem_empty] at hmem

/-- Each row is the counting function of a prefix satisfying the cap. -/
def profiles (k T : ℕ) : Finset (Fin (T + 1) → ℕ) :=
  (survivors (fun _ ↦ 0) k T).image fun B i ↦ prefixCount B i.val

private def dominated {d : ℕ} (p v : Fin d → ℕ) : Bool :=
  decide (∀ i, p i ≤ v i) && !decide (∀ i, v i ≤ p i)

private theorem dominated_iff {d : ℕ} {p v : Fin d → ℕ} :
    dominated p v = true ↔ p < v := by
  rw [lt_iff_le_not_ge]
  simp only [dominated, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
    decide_eq_false_iff_not, Pi.le_def]

/-- Delete each row dominated coordinatewise by another row. The remaining
table is independent of the denominator and can be shared between tests. -/
def maximalProfiles (k T : ℕ) : Finset (Fin (T + 1) → ℕ) :=
  (profiles k T).filter fun p ↦ ((profiles k T).filter (fun v ↦ dominated p v)) = ∅

private theorem survives_iff_profile (q : ℕ → ℕ) (k T : ℕ) :
    (survivors q k T).Nonempty ↔ ∃ p ∈ maximalProfiles k T,
      ∀ i : Fin (T + 1), k ≤ i.val → q i.val ≤ p i := by
  classical
  constructor
  · rintro ⟨B, hB⟩
    obtain ⟨hsub, hrep, hd⟩ := mem_survivors.mp hB
    have hB0 : B ∈ survivors (fun _ ↦ 0) k T :=
      mem_survivors.mpr ⟨hsub, hrep, fun _ _ _ ↦ Nat.zero_le _⟩
    let p (i : Fin (T + 1)) := prefixCount B i.val
    have hp : p ∈ profiles k T := Finset.mem_image.mpr ⟨B, hB0, rfl⟩
    obtain ⟨v, hpv, hv⟩ := (profiles k T).exists_le_maximal hp
    refine ⟨v, Finset.mem_filter.mpr ⟨hv.1, ?_⟩,
      fun i hi ↦ (hd i.val (Nat.le_of_lt_succ i.isLt) hi).trans (hpv i)⟩
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro w hw
    obtain ⟨hwmem, hlt⟩ := Finset.mem_filter.mp hw
    have hpw := dominated_iff.mp hlt
    exact hpw.not_ge (hv.2 hwmem hpw.le)
  · rintro ⟨p, hp, hd⟩
    have hp' : p ∈ profiles k T := (Finset.mem_filter.mp hp).1
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hp'
    obtain ⟨hsub, hrep, _⟩ := mem_survivors.mp hB
    exact ⟨B, mem_survivors.mpr ⟨hsub, hrep,
      fun n hn hk ↦ hd ⟨n, Nat.lt_succ_of_le hn⟩ hk⟩⟩

/-- In each row, a large enough density demand at one coordinate excludes
that whole row and all profiles below it. -/
theorem finite_iff_profile_obstruction (g : ℕ → ℝ) (k T : ℕ) :
    survivors (quota g k) k T = ∅ ↔ ∀ p ∈ maximalProfiles k T,
      ∃ i : Fin (T + 1), k ≤ i.val ∧
        (↑(k + 1) : ℝ) * (p i : ℝ) < ‖√(i.val : ℝ) / g i.val‖ := by
  classical
  rw [← Finset.not_nonempty_iff_eq_empty, survives_iff_profile]
  push Not
  simp only [← not_le, quota_le]

end Erdos40Windows

/-
Sidon counterexamples for oscillating denominators

Choose a prime between each scale s and 2s. Its block has at least s elements
and finishes before the next scale 32s². These inequalities give square-root
density at the specified peaks and fourth-root density in every sufficiently
large prefix.
-/

namespace Erdos40Peaks

-- Adapted from the accepted open-math-agents proof proofs/Erdos44.sidon_set_lower_bound.lean
-- (lemma bosePrefix_sidon), generalised from the shift 1 to an arbitrary shift t.
/-- The block used for the prime `p`. -/
def blk (p : ℕ) : Finset ℕ :=
  (Finset.range (p - 1 + 1)).image (fun a => 2 * p * a + (a * a) % p + (4 * p * p + 1))

/-- The index of each peak is fixed before the primes or the denominator are chosen. -/
def scale : ℕ → ℕ
  | 0 => 2
  | j + 1 => 32 * scale j ^ 2

private theorem scale_large (j : ℕ) : j + 2 ≤ scale j := by
  induction j with
  | zero => decide
  | succ j ih =>
    rw [scale]
    nlinarith [Nat.le_mul_self (scale j)]

private theorem has_prime (j : ℕ) : ∃ p : ℕ, p.Prime ∧ scale j < p ∧ p ≤ 2 * scale j :=
  Nat.exists_prime_lt_and_le_two_mul _ (by have := scale_large j; omega)

private noncomputable def prime (j : ℕ) := (has_prime j).choose

private noncomputable def stage : ℕ → Finset ℕ
  | 0 => ∅
  | j + 1 => stage j ∪ blk (prime j)

private def peakSet : Set ℕ := ⋃ j, (stage j : Set ℕ)

open Filter Real Set AdditiveCombinatorics

private noncomputable abbrev count (n : ℕ) := (peakSet ∩ Icc 1 n).ncard

private theorem between {n : ℕ} (hn : scale 1 ≤ n) :
    ∃ j, scale (j+1) ≤ n ∧ n < scale (j+2) := by
  have ex : ∃ j, n < scale (j+2) := ⟨n, by have := scale_large (n+2); omega⟩
  refine ⟨Nat.find ex, ?_, Nat.find_spec ex⟩
  cases he : Nat.find ex with
  | zero => exact hn
  | succ i =>
    have hi : i < Nat.find ex := by omega
    exact Nat.le_of_not_gt (Nat.find_min ex hi)

end Erdos40Peaks

open Filter Real Erdos40Windows

/-- A class defined by inequalities against precomputed finite tables. -/
def OMA.answer : Set (ℕ → ℝ) :=
  {g | Tendsto g atTop atTop ∧ ∀ k : ℕ, ∃ T ≥ k, ∀ p ∈ maximalProfiles k T,
    ∃ i : Fin (T + 1), k ≤ i.val ∧
      (↑(k + 1) : ℝ) * (p i : ℝ) < ‖√(i.val : ℝ) / g i.val‖}

theorem OMA.solution : Erdos40.erdos_40.answer = OMA.answer → type_of% @Erdos40.erdos_40 := by
  intro h
  rw [h]
  ext g
  change (_ ∧ Erdos40.Erdos40For g) ↔ (_ ∧ _)
  simp only [erdos40For_iff_finite, finite_iff_profile_obstruction]
