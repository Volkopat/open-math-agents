import FormalConjectures.ErdosProblems.«254»

/-!
# Cassels’ sufficient condition for additive completeness

The stronger Erdős 254 theorem is adapted from Will Blair’s MIT-licensed formalization at
https://github.com/williamjblair/lean-proofs/tree/4f915a323443bfb1709a6805a013812016dca88a/starfleet/erdos-254 .
The final lemmas convert Cassels’ growth and phase hypotheses to its inputs.
-/

/-
MIT License

Copyright (c) 2026 Will Blair

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.

---

NOTICE — third-party files

ErdosProblems/Erdos154.lean is a third-party formalization included as a build
dependency for the 154 sumset proof. It is the Lean formalization of Lindström's
residue-distribution theorem for Sidon sets (formal authors Aristotle and Wouter
van Doorn), hosted via plby/lean-proofs, and is used under its original license
as stated in its file header. Mathlib is licensed under Apache-2.0.
-/

@[local simp] private lemma OMA.cassels_norm_coe (z : Circle) : ‖(z : ℂ)‖ = 1 := Circle.norm_coe z

section
namespace LocalCassels.PiecewiseAssembly

open scoped BigOperators

noncomputable section

/-- `n` is a sum of distinct members of `B` (the empty sum is allowed). -/
def Representable (B : Set ℕ) (n : ℕ) : Prop :=
  ∃ s : Finset ℕ, (∀ b ∈ s, b ∈ B) ∧ ∑ b ∈ s, b = n

lemma representable_add_of_disjoint {B C : Set ℕ} (hBC : Disjoint B C)
    {m n : ℕ} (hm : Representable B m) (hn : Representable C n) :
    Representable (B ∪ C) (m + n) := by
  classical
  obtain ⟨s, hsB, rfl⟩ := hm
  obtain ⟨t, htC, rfl⟩ := hn
  have hst : Disjoint s t := by
    rw [Finset.disjoint_left]
    intro x hxs hxt
    exact Set.disjoint_left.mp hBC (hsB x hxs) (htC x hxt)
  refine ⟨s ∪ t, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_union.mp hx with hxs | hxt
    · exact Or.inl (hsB x hxs)
    · exact Or.inr (htC x hxt)
  · rw [Finset.sum_union hst]

/-- A one-sided set is thick if it contains intervals of every finite length. -/
def IsThick (T : Set ℕ) : Prop :=
  ∀ L : ℕ, ∃ a : ℕ, ∀ k : ℕ, k ≤ L → a + k ∈ T

/-- A finite family of disjoint correction sums which covers every translate
of `good` converts a piecewise-good representability statement into thickness. -/
theorem correction_cover_makes_union_thick
    (B C : Set ℕ) (hBC : Disjoint B C)
    (J : Set ℕ) (good : ℕ → Prop)
    (hJ : IsThick J)
    (hpiece : ∀ n : ℕ, n ∈ J → good n → Representable B n)
    (Q : Finset ℕ) (hQ : ∀ q ∈ Q, Representable C q)
    (N₀ : ℕ)
    (hcover : ∀ n : ℕ, N₀ ≤ n →
      ∃ q ∈ Q, q ≤ n ∧ good (n - q)) :
    IsThick {n | Representable (B ∪ C) n} := by
  intro L
  let M := ∑ q ∈ Q, q
  obtain ⟨a, ha⟩ := hJ (N₀ + M + L)
  refine ⟨a + N₀ + M, ?_⟩
  intro k hk
  let n := a + N₀ + M + k
  have hn0 : N₀ ≤ n := by omega
  obtain ⟨q, hqQ, hqn, hgood⟩ := hcover n hn0
  have hqM : q ≤ M := by
    calc
      q = ∑ x ∈ ({q} : Finset ℕ), x := by simp
      _ ≤ ∑ x ∈ Q, x := Finset.sum_le_sum_of_subset (by simpa using hqQ)
  have hJmem : n - q ∈ J := by
    have heq : n - q = a + (N₀ + M + k - q) := by omega
    rw [heq]
    apply ha
    omega
  have hrepB := hpiece (n - q) hJmem hgood
  have hrep := representable_add_of_disjoint hBC hrepB (hQ q hqQ)
  have hnq : n - q + q = n := by omega
  rw [hnq] at hrep
  simpa [n, Nat.add_assoc] using hrep

/-- Adding a syndetic distinct-subset-sum set to a thick representability set
makes all sufficiently large integers representable, with disjointness ensuring
that no summand is reused. -/
theorem thick_add_syndetic_is_cofinite
    (E D : Set ℕ) (hED : Disjoint E D)
    (hthick : IsThick {n | Representable E n})
    (K : ℕ)
    (hsyndetic : ∀ n : ℕ, ∃ s : ℕ,
      Representable D s ∧ s ≤ n ∧ n ≤ s + K) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → Representable (E ∪ D) n := by
  obtain ⟨a, ha⟩ := hthick K
  refine ⟨a + K, ?_⟩
  intro n hn
  obtain ⟨s, hsD, hslo, hshi⟩ := hsyndetic (n - a)
  let k := n - a - s
  have hk : k ≤ K := by omega
  have htE : Representable E (a + k) := ha k hk
  have heq : a + k + s = n := by omega
  have hadd := representable_add_of_disjoint hED htE hsD
  rwa [heq] at hadd

/-- Fully assembled abstract criterion: piecewise-good sums from `B`, a finite
correction cover from disjoint `C`, and a disjoint syndetic class `D` imply
cofinite distinct subset-sum representability. -/
theorem piecewise_correction_syndetic_assembly
    (B C D : Set ℕ)
    (hBC : Disjoint B C) (hBD : Disjoint B D) (hCD : Disjoint C D)
    (J : Set ℕ) (good : ℕ → Prop)
    (hJ : IsThick J)
    (hpiece : ∀ n : ℕ, n ∈ J → good n → Representable B n)
    (Q : Finset ℕ) (hQ : ∀ q ∈ Q, Representable C q)
    (N₁ : ℕ) (hcover : ∀ n : ℕ, N₁ ≤ n →
      ∃ q ∈ Q, q ≤ n ∧ good (n - q))
    (K : ℕ) (hsyndetic : ∀ n : ℕ, ∃ s : ℕ,
      Representable D s ∧ s ≤ n ∧ n ≤ s + K) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → Representable (B ∪ C ∪ D) n := by
  have hthick := correction_cover_makes_union_thick B C hBC J good hJ hpiece
    Q hQ N₁ hcover
  have hUnionD : Disjoint (B ∪ C) D := hBD.union_left hCD
  simpa [Set.union_assoc] using
    thick_add_syndetic_is_cofinite (B ∪ C) D hUnionD hthick K hsyndetic

end

end LocalCassels.PiecewiseAssembly
end

section
/-
# Erdős Problem 254: canonical formal statement

This file contains only the definitions and the proposition to be proved.  The
independent verification gate in `check_answer/verify.sh` requires this file to
be byte-for-byte identical to `check_answer/Statement.lean`.
-/

namespace LocalCassels

open Filter
open scoped BigOperators

noncomputable section

/-- Distance from a real number to the nearest integer.  Since
`Int.fract x ∈ [0,1)`, the two candidates are the floor and the next integer. -/
def nearestIntegerDistance (x : ℝ) : ℝ :=
  min (Int.fract x) (1 - Int.fract x)

/-- Number of members of `A` in the integer interval `[1,x]`. -/
def countingFunction (A : Set ℕ) (x : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 x).filter (fun n => n ∈ A)).card

/-- The cardinality difference in the first hypothesis. -/
def dyadicIncrement (A : Set ℕ) (x : ℕ) : ℕ :=
  countingFunction A (2 * x) - countingFunction A x

/-- Partial sums, in the natural order, of the nonnegative series appearing in
Problem 254. -/
def phasePartialSum (A : Set ℕ) (θ : ℝ) (N : ℕ) : ℝ := by
  classical
  exact ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n ∈ A),
    nearestIntegerDistance (θ * (n : ℝ))

/-- Every sufficiently large natural number is a sum of distinct members of
`A`; distinctness is encoded by the use of a `Finset`. -/
def IsComplete (A : Set ℕ) : Prop :=
  ∃ N₀ : ℕ, ∀ m : ℕ, N₀ ≤ m →
    ∃ s : Finset ℕ, (↑s : Set ℕ) ⊆ A ∧ ∑ n ∈ s, n = m

/-- Faithful formalization of Erdős Problem 254. -/
def Statement : Prop :=
  ∀ A : Set ℕ,
    Tendsto (dyadicIncrement A) (atTop : Filter ℕ) atTop →
    (∀ θ : ℝ, θ ∈ Set.Ioo 0 1 →
      Tendsto (phasePartialSum A θ) atTop atTop) →
    IsComplete A

end

end LocalCassels
end

section
namespace LocalCassels.CompactCorrectionCover

open scoped BigOperators Topology
open LocalCassels.PiecewiseAssembly

noncomputable section

variable {T : Type*} [TopologicalSpace T] [AddCommGroup T]
  [IsTopologicalAddGroup T] [CompactSpace T]

/-- Density of representable correction phases in a closed orbit subgroup
produces one finite correction family covering every orbit point by a fixed
open target. -/
theorem finite_correction_cover
    (C : Set ℕ) (a : T) (H : AddSubgroup T) (hHclosed : IsClosed (H : Set T))
    (haH : a ∈ H)
    (hcorr : ∀ x ∈ H, ∀ O : Set T, IsOpen O → x ∈ O →
      ∃ q : ℕ, Representable C q ∧ q • a ∈ O)
    (U : Set T) (hUopen : IsOpen U)
    (n₀ : ℕ) (hn₀U : n₀ • a ∈ U) :
    ∃ Q : Finset ℕ, ∃ N₀ : ℕ,
      (∀ q ∈ Q, Representable C q) ∧
      (∀ n : ℕ, N₀ ≤ n →
        ∃ q ∈ Q, q ≤ n ∧ (n - q) • a ∈ U) := by
  let I := {q : ℕ // Representable C q}
  let V : I → Set T := fun q => {x | x - q.1 • a ∈ U}
  have hVopen : ∀ q, IsOpen (V q) := by
    intro q
    exact hUopen.preimage (continuous_id.sub continuous_const)
  have hcover : (H : Set T) ⊆ ⋃ q : I, V q := by
    intro x hxH
    have hyH : x - n₀ • a ∈ H := H.sub_mem hxH (H.nsmul_mem haH n₀)
    let O : Set T := {y | x - y ∈ U}
    have hOopen : IsOpen O := hUopen.preimage (continuous_const.sub continuous_id)
    have hyO : x - n₀ • a ∈ O := by
      change x - (x - n₀ • a) ∈ U
      simpa only [sub_sub_cancel] using hn₀U
    obtain ⟨q, hqC, hqO⟩ := hcorr (x - n₀ • a) hyH O hOopen hyO
    exact Set.mem_iUnion.mpr ⟨⟨q, hqC⟩, hqO⟩
  obtain ⟨F, hFcover⟩ := hHclosed.isCompact.elim_finite_subcover
    V hVopen hcover
  let Q : Finset ℕ := F.map ⟨Subtype.val, Subtype.val_injective⟩
  let N₀ : ℕ := ∑ q ∈ Q, q
  refine ⟨Q, N₀, ?_, ?_⟩
  · intro q hqQ
    change q ∈ F.map ⟨Subtype.val, Subtype.val_injective⟩ at hqQ
    rw [Finset.mem_map] at hqQ
    obtain ⟨r, hrF, rfl⟩ := hqQ
    exact r.2
  · intro n hn
    have hnH : n • a ∈ H := H.nsmul_mem haH n
    obtain ⟨r, hrF, hnr⟩ := Set.mem_iUnion₂.mp (hFcover hnH)
    have hrQ : r.1 ∈ Q := by
      change r.1 ∈ F.map ⟨Subtype.val, Subtype.val_injective⟩
      exact Finset.mem_map.mpr ⟨r, hrF, rfl⟩
    have hrN : r.1 ≤ N₀ := by
      calc
        r.1 = ∑ q ∈ ({r.1} : Finset ℕ), q := by simp
        _ ≤ ∑ q ∈ Q, q := Finset.sum_le_sum_of_subset (by simpa using hrQ)
    have hrn : r.1 ≤ n := hrN.trans hn
    refine ⟨r.1, hrQ, hrn, ?_⟩
    have hphase : (n - r.1) • a = n • a - r.1 • a := by
      apply eq_sub_iff_add_eq.mpr
      rw [← add_nsmul]
      congr 1
      exact Nat.sub_add_cancel hrn
    rw [hphase]
    exact hnr

end

end LocalCassels.CompactCorrectionCover
end

section
namespace LocalCassels.ConditionalBohrCriterion

open scoped Topology
open LocalCassels.PiecewiseAssembly LocalCassels.CompactCorrectionCover

noncomputable section

variable {T : Type*} [TopologicalSpace T] [AddCommGroup T]
  [IsTopologicalAddGroup T] [CompactSpace T]

/-- Formal compact-group core of the Bergelson--Simmons completeness
criterion. All use of summands is explicitly disjoint. -/
theorem conditional_piecewise_bohr_completeness
    (B C D : Set ℕ)
    (hBC : Disjoint B C) (hBD : Disjoint B D) (hCD : Disjoint C D)
    (a : T) (H : AddSubgroup T) (hHclosed : IsClosed (H : Set T))
    (haH : a ∈ H)
    (hcorr : ∀ x ∈ H, ∀ O : Set T, IsOpen O → x ∈ O →
      ∃ q : ℕ, Representable C q ∧ q • a ∈ O)
    (U : Set T) (hUopen : IsOpen U)
    (n₀ : ℕ) (hn₀U : n₀ • a ∈ U)
    (J : Set ℕ) (hJ : IsThick J)
    (hpiece : ∀ n : ℕ, n ∈ J → n • a ∈ U → Representable B n)
    (K : ℕ) (hsyndetic : ∀ n : ℕ, ∃ s : ℕ,
      Representable D s ∧ s ≤ n ∧ n ≤ s + K) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Representable (B ∪ C ∪ D) n := by
  obtain ⟨Q, N₁, hQ, hcover⟩ := finite_correction_cover C a H hHclosed haH
    hcorr U hUopen n₀ hn₀U
  exact piecewise_correction_syndetic_assembly B C D hBC hBD hCD J
    (fun n => n • a ∈ U) hJ hpiece Q hQ N₁ hcover K hsyndetic

end

end LocalCassels.ConditionalBohrCriterion
end

section
namespace LocalCassels.GrowthPartition

noncomputable section

/-- The elements of `s` whose positions in the increasing enumeration are
congruent to `c` modulo four. -/
def balancedPart (s : Finset ℕ) (c : ℕ) : Finset ℕ :=
  ((Finset.univ.filter fun i : Fin s.card => i.val % 4 = c).map
    (s.orderEmbOfFin rfl).toEmbedding)

lemma balancedPart_subset (s : Finset ℕ) (c : ℕ) : balancedPart s c ⊆ s := by
  intro n hn
  rw [balancedPart, Finset.mem_map] at hn
  obtain ⟨i, _, rfl⟩ := hn
  exact s.orderEmbOfFin_mem rfl i

lemma balancedPart_card_ge (s : Finset ℕ) (c K : ℕ) (hc : c < 4)
    (hK : 4 * K ≤ s.card) : K ≤ (balancedPart s c).card := by
  let e : Fin K ↪ Fin s.card :=
    ⟨fun i => ⟨c + 4 * i.val, by
        have hi : i.val < K := i.isLt
        omega⟩,
      by
        intro i j hij
        apply Fin.ext
        have hval := congrArg Fin.val hij
        dsimp at hval
        omega⟩
  have hsub : Finset.univ.map e ⊆
      (Finset.univ.filter fun i : Fin s.card => i.val % 4 = c) := by
    intro i hi
    rw [Finset.mem_map] at hi
    obtain ⟨j, _, rfl⟩ := hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change (c + 4 * (j : ℕ)) % 4 = c
    simp [Nat.add_mod, Nat.mod_eq_of_lt hc]
  calc
    K = (Finset.univ.map e).card := by simp
    _ ≤ (Finset.univ.filter fun i : Fin s.card => i.val % 4 = c).card :=
      Finset.card_le_card hsub
    _ = (balancedPart s c).card := by simp [balancedPart]

lemma balancedPart_pairwise_disjoint (s : Finset ℕ) {c d : ℕ} (hcd : c ≠ d) :
    Disjoint (balancedPart s c) (balancedPart s d) := by
  rw [Finset.disjoint_left]
  intro n hnc hnd
  rw [balancedPart, Finset.mem_map] at hnc hnd
  obtain ⟨i, hi, hin⟩ := hnc
  obtain ⟨j, hj, hjn⟩ := hnd
  have hij : i = j := (s.orderEmbOfFin rfl).injective (hin.trans hjn.symm)
  subst j
  have hic : i.val % 4 = c := (Finset.mem_filter.mp hi).2
  have hid : i.val % 4 = d := (Finset.mem_filter.mp hj).2
  exact hcd (hic.symm.trans hid)

def powerShell (A : Set ℕ) (j : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ioc (2 ^ j) (2 ^ (j + 1))).filter (fun n => n ∈ A)

def countingFunction (A : Set ℕ) (x : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 x).filter (fun n => n ∈ A)).card

def dyadicIncrement (A : Set ℕ) (x : ℕ) : ℕ :=
  countingFunction A (2 * x) - countingFunction A x

def shellCount (A : Set ℕ) (x : ℕ) : ℕ := by
  classical
  exact ((Finset.Ioc x (2 * x)).filter (fun n => n ∈ A)).card

lemma dyadicIncrement_eq_shellCard (A : Set ℕ) (x : ℕ) :
    dyadicIncrement A x = shellCount A x := by
  classical
  let s := (Finset.Icc 1 x).filter (fun n => n ∈ A)
  let t := (Finset.Icc 1 (2 * x)).filter (fun n => n ∈ A)
  have hst : s ⊆ t := by
    intro n hn
    simp only [s, t, Finset.mem_filter, Finset.mem_Icc] at hn ⊢
    exact ⟨⟨hn.1.1, hn.1.2.trans (by omega)⟩, hn.2⟩
  rw [dyadicIncrement, countingFunction, countingFunction]
  change t.card - s.card = _
  rw [← Finset.card_sdiff_of_subset hst]
  apply congrArg Finset.card
  ext n
  simp only [t, s, Finset.mem_sdiff, Finset.mem_filter,
    Finset.mem_Icc, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨hlo, hA⟩, hnot⟩
    refine ⟨⟨?_, hlo.2⟩, hA⟩
    by_contra hnx
    exact hnot ⟨⟨hlo.1, Nat.le_of_not_gt hnx⟩, hA⟩
  · rintro ⟨⟨hxn, hn2x⟩, hA⟩
    refine ⟨⟨⟨by omega, hn2x⟩, hA⟩, ?_⟩
    rintro ⟨⟨_, hnx⟩, _⟩
    omega

/-- Four points of one power-of-two shell already have total sum larger than
any point of the following shell. -/
theorem previous_balancedPart_covers_next
    (A : Set ℕ) (j c n : ℕ) (hc : c < 4)
    (hcard : 16 ≤ (powerShell A j).card)
    (hn : n ∈ powerShell A (j + 1)) :
    n ≤ ∑ m ∈ balancedPart (powerShell A j) c, m := by
  have hpartcard : 4 ≤ (balancedPart (powerShell A j) c).card := by
    apply balancedPart_card_ge
    · exact hc
    · omega
  have hpartsub := balancedPart_subset (powerShell A j) c
  have hlower : ∀ m ∈ balancedPart (powerShell A j) c, 2 ^ j + 1 ≤ m := by
    intro m hm
    have hmshell := hpartsub hm
    simp only [powerShell, Finset.mem_filter, Finset.mem_Ioc] at hmshell
    omega
  have hsum : (2 ^ j + 1) * (balancedPart (powerShell A j) c).card ≤
      ∑ m ∈ balancedPart (powerShell A j) c, m := by
    simpa [nsmul_eq_mul, mul_comm] using
      (Finset.card_nsmul_le_sum (balancedPart (powerShell A j) c)
        (fun m => m) (2 ^ j + 1) hlower)
  have hnupper : n ≤ 2 ^ (j + 2) := by
    simp only [powerShell, Finset.mem_filter, Finset.mem_Ioc] at hn
    simpa [Nat.add_assoc] using hn.1.2
  calc
    n ≤ 2 ^ (j + 2) := hnupper
    _ ≤ (2 ^ j + 1) * (balancedPart (powerShell A j) c).card := by
      rw [show 2 ^ (j + 2) = 4 * 2 ^ j by ring]
      calc
        4 * 2 ^ j ≤ (2 ^ j + 1) * 4 := by omega
        _ ≤ (2 ^ j + 1) * (balancedPart (powerShell A j) c).card :=
          Nat.mul_le_mul_left (2 ^ j + 1) hpartcard
    _ ≤ ∑ m ∈ balancedPart (powerShell A j) c, m := hsum

/-- The global color class obtained by applying `balancedPart` independently
in every power-of-two shell. -/
def colorClass (A : Set ℕ) (c : ℕ) : Set ℕ :=
  {n | ∃ j : ℕ, n ∈ balancedPart (powerShell A j) c}

lemma powerShell_index_unique (A : Set ℕ) {j k n : ℕ}
    (hj : n ∈ powerShell A j) (hk : n ∈ powerShell A k) : j = k := by
  simp only [powerShell, Finset.mem_filter, Finset.mem_Ioc] at hj hk
  rcases lt_trichotomy j k with hjk | rfl | hkj
  · have hp : 2 ^ (j + 1) ≤ 2 ^ k :=
      Nat.pow_le_pow_right (by decide) (by omega)
    omega
  · rfl
  · have hp : 2 ^ (k + 1) ≤ 2 ^ j :=
      Nat.pow_le_pow_right (by decide) (by omega)
    omega

lemma colorClass_pairwise_disjoint (A : Set ℕ) {c d : ℕ} (hcd : c ≠ d) :
    Disjoint (colorClass A c) (colorClass A d) := by
  rw [Set.disjoint_left]
  intro n hnc hnd
  obtain ⟨j, hj⟩ := hnc
  obtain ⟨k, hk⟩ := hnd
  have hjs := balancedPart_subset (powerShell A j) c hj
  have hks := balancedPart_subset (powerShell A k) d hk
  have hjk : j = k := powerShell_index_unique A hjs hks
  subst k
  exact Finset.disjoint_left.mp (balancedPart_pairwise_disjoint (powerShell A j) hcd)
    hj hk

def prefixFinset (B : Set ℕ) (n : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Iio n).filter (fun m => m ∈ B)

def prefixSum (B : Set ℕ) (n : ℕ) : ℕ :=
  ∑ m ∈ prefixFinset B n, m

lemma balancedPart_subset_prefix (A : Set ℕ) (j c n : ℕ)
    (hn : n ∈ powerShell A (j + 1)) :
    balancedPart (powerShell A j) c ⊆
      prefixFinset (colorClass A c) n := by
  intro m hm
  have hms := balancedPart_subset (powerShell A j) c hm
  simp only [powerShell, Finset.mem_filter, Finset.mem_Ioc] at hms hn
  simp only [prefixFinset, Finset.mem_filter, Finset.mem_Iio]
  refine ⟨?_, ⟨j, hm⟩⟩
  omega

lemma colorClass_growth_of_shell_card (A : Set ℕ) (j c n : ℕ) (hc : c < 4)
    (hcard : 16 ≤ (powerShell A j).card)
    (hn : n ∈ powerShell A (j + 1)) :
    n ≤ prefixSum (colorClass A c) n := by
  classical
  apply (previous_balancedPart_covers_next A j c n hc hcard hn).trans
  exact Finset.sum_le_sum_of_subset (balancedPart_subset_prefix A j c n hn)

/-- Once all sufficiently late shells have sixteen points, each global color
class satisfies the subset-sum growth inequality eventually. -/
theorem colorClass_eventual_growth (A : Set ℕ) (c : ℕ) (hc : c < 4)
    (hshell : ∀ᶠ j : ℕ in Filter.atTop, 16 ≤ (powerShell A j).card) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → n ∈ colorClass A c →
      n ≤ prefixSum (colorClass A c) n := by
  classical
  obtain ⟨J, hJ⟩ := Filter.eventually_atTop.1 hshell
  refine ⟨2 ^ (J + 1) + 1, ?_⟩
  intro n hnlarge hnc
  obtain ⟨k, hnkpart⟩ := hnc
  have hnkshell := balancedPart_subset (powerShell A k) c hnkpart
  have hkgt : J < k := by
    by_contra hnot
    have hkle : k ≤ J := Nat.le_of_not_gt hnot
    have hnupper : n ≤ 2 ^ (k + 1) := by
      exact (Finset.mem_Ioc.mp (Finset.mem_filter.mp hnkshell).1).2
    have hp : 2 ^ (k + 1) ≤ 2 ^ (J + 1) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    omega
  let j := k - 1
  have hjk : j + 1 = k := Nat.sub_add_cancel (by omega)
  have hcard : 16 ≤ (powerShell A j).card := hJ j (by omega)
  apply colorClass_growth_of_shell_card A j c n hc hcard
  rwa [hjk]

end

end LocalCassels.GrowthPartition
end

section
namespace LocalCassels.FiniteCoinCover

open scoped BigOperators

/-- The subset sums of `s` have no downward gap larger than `K` throughout
`[0, sum s]`. -/
def HasSubsetSumGapsAtMost (s : Finset ℕ) (K : ℕ) : Prop :=
  ∀ n : ℕ, n ≤ ∑ a ∈ s, a →
    ∃ t : Finset ℕ, t ⊆ s ∧ (∑ a ∈ t, a) ≤ n ∧ n ≤ (∑ a ∈ t, a) + K

lemma empty_hasSubsetSumGapsAtMost (K : ℕ) :
    HasSubsetSumGapsAtMost ∅ K := by
  intro n hn
  refine ⟨∅, by simp, by simp, ?_⟩
  simp at hn ⊢
  omega

/-- Adjoining a coin no larger than the old total plus `K` preserves the
`K`-gap property. -/
lemma insert_hasSubsetSumGapsAtMost {s : Finset ℕ} {a K : ℕ} (ha : a ∉ s)
    (hs : HasSubsetSumGapsAtMost s K)
    (haBound : a ≤ (∑ x ∈ s, x) + K) :
    HasSubsetSumGapsAtMost (insert a s) K := by
  intro n hn
  rw [Finset.sum_insert ha] at hn
  by_cases hnold : n ≤ ∑ x ∈ s, x
  · obtain ⟨t, hts, htlo, hthi⟩ := hs n hnold
    exact ⟨t, hts.trans (Finset.subset_insert a s), htlo, hthi⟩
  by_cases han : a ≤ n
  · have htarget : n - a ≤ ∑ x ∈ s, x := by omega
    obtain ⟨t, hts, htlo, hthi⟩ := hs (n - a) htarget
    refine ⟨insert a t, ?_, ?_, ?_⟩
    · exact Finset.insert_subset (Finset.mem_insert_self _ _) <|
        hts.trans (Finset.subset_insert a s)
    · rw [Finset.sum_insert (fun hat => ha (hts hat))]
      omega
    · rw [Finset.sum_insert (fun hat => ha (hts hat))]
      omega
  · refine ⟨s, Finset.subset_insert a s, Nat.le_of_not_ge hnold, ?_⟩
    omega

/-- If every coin is at most `K` plus the sum of the smaller coins, then all
subset-sum gaps up to the total are at most `K`. -/
theorem finite_prefix_bound_gives_bounded_gaps (s : Finset ℕ) (K : ℕ)
    (hgrowth : ∀ a ∈ s, a ≤ (∑ x ∈ s.filter (fun x => x < a), x) + K) :
    HasSubsetSumGapsAtMost s K := by
  classical
  induction s using Finset.strongInductionOn
  rename_i s ih
  by_cases hs0 : s = ∅
  · subst s
    exact empty_hasSubsetSumGapsAtMost K
  · let a := s.max' (Finset.nonempty_iff_ne_empty.mpr hs0)
    let r := s.erase a
    have haS : a ∈ s := Finset.max'_mem s _
    have har : a ∉ r := by simp [r]
    have hrs : r ⊂ s := Finset.erase_ssubset haS
    have hless : ∀ x ∈ r, x < a := by
      intro x hxr
      have hxS : x ∈ s := (Finset.mem_erase.mp hxr).2
      have hxle : x ≤ a := Finset.le_max' s x hxS
      have hxne : x ≠ a := (Finset.mem_erase.mp hxr).1
      omega
    have hfilter : s.filter (fun x => x < a) = r := by
      ext x
      simp only [Finset.mem_filter]
      change (x ∈ s ∧ x < a) ↔ x ∈ s.erase a
      rw [Finset.mem_erase]
      constructor
      · rintro ⟨hxS, hxa⟩
        exact ⟨by omega, hxS⟩
      · rintro ⟨hxa, hxS⟩
        have hxr : x ∈ r := by
          change x ∈ s.erase a
          exact Finset.mem_erase.mpr ⟨hxa, hxS⟩
        exact ⟨hxS, hless x hxr⟩
    have haBound : a ≤ (∑ x ∈ r, x) + K := by
      rw [← hfilter]
      exact hgrowth a haS
    have hgrowthR : ∀ b ∈ r,
        b ≤ (∑ x ∈ r.filter (fun x => x < b), x) + K := by
      intro b hb
      have hbS : b ∈ s := (Finset.mem_erase.mp hb).2
      have hfilters : r.filter (fun x => x < b) = s.filter (fun x => x < b) := by
        ext x
        simp only [Finset.mem_filter]
        change (x ∈ s.erase a ∧ x < b) ↔ (x ∈ s ∧ x < b)
        rw [Finset.mem_erase]
        constructor
        · rintro ⟨⟨hxa, hxS⟩, hxb⟩
          exact ⟨hxS, hxb⟩
        · rintro ⟨hxS, hxb⟩
          exact ⟨⟨by
            have hba : b < a := hless b hb
            omega, hxS⟩, hxb⟩
      rw [hfilters]
      exact hgrowth b hbS
    have hcoverR : HasSubsetSumGapsAtMost r K := ih r hrs hgrowthR
    have hins := insert_hasSubsetSumGapsAtMost har hcoverR haBound
    simpa [r, Finset.insert_erase haS] using hins

end LocalCassels.FiniteCoinCover
end

section
namespace LocalCassels.InfiniteCoinCover

open scoped BigOperators
open LocalCassels.FiniteCoinCover

noncomputable section

/-- Positive members of `B` not exceeding `M`. -/
def coinsUpTo (B : Set ℕ) (M : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 M).filter (fun b => b ∈ B)

/-- Positive members of `B` strictly smaller than `b`. -/
def smallerCoins (B : Set ℕ) (b : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ico 1 b).filter (fun x => x ∈ B)

lemma coinsUpTo_filter_lt {B : Set ℕ} {M b : ℕ} (hbM : b ≤ M) :
    (coinsUpTo B M).filter (fun x => x < b) = smallerCoins B b := by
  classical
  ext x
  constructor
  · intro hx
    have hxOuter := Finset.mem_filter.mp hx
    have hxCoin := Finset.mem_filter.mp hxOuter.1
    exact Finset.mem_filter.mpr ⟨
      Finset.mem_Ico.mpr ⟨(Finset.mem_Icc.mp hxCoin.1).1, hxOuter.2⟩,
      hxCoin.2⟩
  · intro hx
    have hxSmall := Finset.mem_filter.mp hx
    have hxIco := Finset.mem_Ico.mp hxSmall.1
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hxIco.1, ?_⟩,
      hxSmall.2⟩, hxIco.2⟩
    exact hxIco.2.le.trans hbM

/-- An infinite set of positive natural numbers has unbounded finite-prefix
sum. -/
lemma infinite_prefixSum_unbounded {B : Set ℕ} (hB : B.Infinite) :
    ∀ n : ℕ, ∃ M : ℕ, n ≤ ∑ b ∈ coinsUpTo B M, b := by
  intro n
  obtain ⟨b, hbB, hnb⟩ := hB.exists_gt n
  refine ⟨b, ?_⟩
  have hbmem : b ∈ coinsUpTo B b := by
    simp only [coinsUpTo, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by omega, le_rfl⟩, hbB⟩
  calc
    n ≤ b := Nat.le_of_lt hnb
    _ = ∑ x ∈ ({b} : Finset ℕ), x := by simp
    _ ≤ ∑ x ∈ coinsUpTo B b, x :=
      Finset.sum_le_sum_of_subset (by simpa using hbmem)

/-- The Burr--Erdős prefix-growth condition implies that the distinct subset
sums are syndetic (in the one-sided, downward-gap formulation). -/
theorem infinite_prefix_growth_gives_syndetic_subsetSums
    (B : Set ℕ) (K : ℕ) (hB : B.Infinite)
    (hgrowth : ∀ b ∈ B, 1 ≤ b →
      b ≤ (∑ x ∈ smallerCoins B b, x) + K) :
    ∀ n : ℕ, ∃ t : Finset ℕ,
      (∀ b ∈ t, b ∈ B) ∧
      (∑ b ∈ t, b) ≤ n ∧ n ≤ (∑ b ∈ t, b) + K := by
  classical
  intro n
  obtain ⟨M, hnM⟩ := infinite_prefixSum_unbounded hB n
  let s := coinsUpTo B M
  have hfiniteGrowth : ∀ b ∈ s,
      b ≤ (∑ x ∈ s.filter (fun x => x < b), x) + K := by
    intro b hb
    have hbdata : 1 ≤ b ∧ b ≤ M ∧ b ∈ B := by
      simpa [s, coinsUpTo, and_assoc] using hb
    rw [coinsUpTo_filter_lt hbdata.2.1]
    exact hgrowth b hbdata.2.2 hbdata.1
  obtain ⟨t, hts, htlo, hthi⟩ :=
    finite_prefix_bound_gives_bounded_gaps s K hfiniteGrowth n hnM
  refine ⟨t, ?_, htlo, hthi⟩
  intro b hbt
  have hbs : b ∈ s := hts hbt
  change b ∈ coinsUpTo B M at hbs
  exact (Finset.mem_filter.mp hbs).2

end

end LocalCassels.InfiniteCoinCover
end

section
namespace LocalCassels.FourSyndeticClasses

open scoped BigOperators
open LocalCassels.GrowthPartition LocalCassels.InfiniteCoinCover

noncomputable section

lemma colorClass_elements_gt_one (A : Set ℕ) (c : ℕ) {n : ℕ}
    (hn : n ∈ colorClass A c) : 1 < n := by
  classical
  obtain ⟨j, hj⟩ := hn
  have hjs := balancedPart_subset (powerShell A j) c hj
  have hlo := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hjs).1).1
  have hp : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  omega

lemma colorClass_infinite (A : Set ℕ) (c : ℕ) (hc : c < 4)
    (hshell : ∀ᶠ j : ℕ in Filter.atTop, 16 ≤ (powerShell A j).card) :
    (colorClass A c).Infinite := by
  classical
  apply Set.infinite_of_forall_exists_gt
  intro x
  have hp : ∀ᶠ j : ℕ in Filter.atTop, x < 2 ^ j :=
    (tendsto_pow_atTop_atTop_of_one_lt (r := (2 : ℕ)) (by decide)).eventually
      (Filter.eventually_gt_atTop x)
  obtain ⟨j, hcard, hxj⟩ := (hshell.and hp).exists
  have hpartcard : 4 ≤ (balancedPart (powerShell A j) c).card := by
    exact balancedPart_card_ge (powerShell A j) c 4 hc (by omega)
  have hne : (balancedPart (powerShell A j) c).Nonempty :=
    Finset.card_pos.mp (by omega)
  obtain ⟨n, hn⟩ := hne
  refine ⟨n, ⟨j, hn⟩, ?_⟩
  have hns := balancedPart_subset (powerShell A j) c hn
  have hjn := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hns).1).1
  omega

lemma smallerCoins_colorClass_eq_prefixFinset (A : Set ℕ) (c b : ℕ) :
    smallerCoins (colorClass A c) b = prefixFinset (colorClass A c) b := by
  classical
  ext x
  simp only [smallerCoins, prefixFinset, Finset.mem_filter, Finset.mem_Ico,
    Finset.mem_Iio]
  constructor
  · rintro ⟨⟨hx1, hxb⟩, hxC⟩
    exact ⟨hxb, hxC⟩
  · rintro ⟨hxb, hxC⟩
    exact ⟨⟨(colorClass_elements_gt_one A c hxC).le, hxb⟩, hxC⟩

end

end LocalCassels.FourSyndeticClasses
end

section
namespace LocalCassels.ReserveGrowth

open Filter
open scoped BigOperators
open LocalCassels.GrowthPartition LocalCassels.InfiniteCoinCover

noncomputable section

/-- The set obtained by taking prescribed reserves from every power shell. -/
def reserveSet (R : ℕ → Finset ℕ) : Set ℕ :=
  {n | ∃ j, n ∈ R j}

lemma reserveSet_subset {A : Set ℕ} {R : ℕ → Finset ℕ}
    (hsub : ∀ j, R j ⊆ powerShell A j) : reserveSet R ⊆ A := by
  classical
  intro n hn
  obtain ⟨j, hnj⟩ := hn
  exact (Finset.mem_filter.mp (hsub j hnj)).2

lemma previous_reserve_covers_next {A : Set ℕ} {R : ℕ → Finset ℕ}
    (hsub : ∀ j, R j ⊆ powerShell A j) (j n : ℕ)
    (hcard : 4 ≤ (R j).card) (hn : n ∈ powerShell A (j + 1)) :
    n ≤ ∑ m ∈ R j, m := by
  classical
  have hlower : ∀ m ∈ R j, 2 ^ j + 1 ≤ m := by
    intro m hm
    have hms := hsub j hm
    simp only [powerShell, Finset.mem_filter, Finset.mem_Ioc] at hms
    omega
  have hsum : (2 ^ j + 1) * (R j).card ≤ ∑ m ∈ R j, m := by
    simpa [nsmul_eq_mul, mul_comm] using
      (Finset.card_nsmul_le_sum (R j) (fun m => m) (2 ^ j + 1) hlower)
  have hnupper : n ≤ 2 ^ (j + 2) := by
    simp only [powerShell, Finset.mem_filter, Finset.mem_Ioc] at hn
    simpa [Nat.add_assoc] using hn.1.2
  calc
    n ≤ 2 ^ (j + 2) := hnupper
    _ ≤ (2 ^ j + 1) * (R j).card := by
      rw [show 2 ^ (j + 2) = 4 * 2 ^ j by ring]
      calc
        4 * 2 ^ j ≤ (2 ^ j + 1) * 4 := by omega
        _ ≤ (2 ^ j + 1) * (R j).card := Nat.mul_le_mul_left _ hcard
    _ ≤ _ := hsum

lemma reserve_subset_prefix {A : Set ℕ} {R : ℕ → Finset ℕ}
    (hsub : ∀ j, R j ⊆ powerShell A j) (j n : ℕ)
    (hn : n ∈ powerShell A (j + 1)) :
    R j ⊆ smallerCoins (reserveSet R) n := by
  classical
  intro m hm
  have hms := hsub j hm
  simp only [powerShell, Finset.mem_filter, Finset.mem_Ioc] at hms hn
  simp only [smallerCoins, Finset.mem_filter, Finset.mem_Ico]
  exact ⟨⟨by omega, by omega⟩, ⟨j, hm⟩⟩

lemma reserveSet_infinite {A : Set ℕ} {R : ℕ → Finset ℕ}
    (hsub : ∀ j, R j ⊆ powerShell A j)
    (hcard : Tendsto (fun j => (R j).card) atTop atTop) :
    (reserveSet R).Infinite := by
  classical
  apply Set.infinite_of_forall_exists_gt
  intro x
  have hp : ∀ᶠ j : ℕ in atTop, x < 2 ^ j :=
    (tendsto_pow_atTop_atTop_of_one_lt (r := (2 : ℕ)) (by decide)).eventually
      (eventually_gt_atTop x)
  have hc : ∀ᶠ j : ℕ in atTop, 1 ≤ (R j).card :=
    (tendsto_atTop.1 hcard 1)
  obtain ⟨j, hxj, hcj⟩ := (hp.and hc).exists
  have hne : (R j).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨n, hn⟩ := hne
  refine ⟨n, ⟨j, hn⟩, ?_⟩
  have hns := hsub j hn
  have hjn := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hns).1).1
  omega

/-- Growing reserves in consecutive dyadic shells themselves satisfy the
Burr--Erdős prefix condition and have syndetic distinct subset sums. -/
theorem growing_shell_reserves_are_syndetic
    (A : Set ℕ) (R : ℕ → Finset ℕ)
    (hsub : ∀ j, R j ⊆ powerShell A j)
    (hcard : Tendsto (fun j => (R j).card) atTop atTop) :
    ∃ K : ℕ, ∀ n : ℕ, ∃ t : Finset ℕ,
      (∀ b ∈ t, b ∈ reserveSet R) ∧
      (∑ b ∈ t, b) ≤ n ∧ n ≤ (∑ b ∈ t, b) + K := by
  classical
  have hfour : ∀ᶠ j : ℕ in atTop, 4 ≤ (R j).card := tendsto_atTop.1 hcard 4
  obtain ⟨J, hJ⟩ := eventually_atTop.1 hfour
  let N₀ := 2 ^ (J + 1) + 1
  have hgrowth : ∀ b ∈ reserveSet R, 1 ≤ b →
      b ≤ (∑ x ∈ smallerCoins (reserveSet R) b, x) + N₀ := by
    intro b hbB hb1
    by_cases hbN : N₀ ≤ b
    · obtain ⟨k, hbk⟩ := hbB
      have hbkshell := hsub k hbk
      have hkgt : J < k := by
        by_contra hnot
        have hkle : k ≤ J := Nat.le_of_not_gt hnot
        have hbupper : b ≤ 2 ^ (k + 1) :=
          (Finset.mem_Ioc.mp (Finset.mem_filter.mp hbkshell).1).2
        have hp : 2 ^ (k + 1) ≤ 2 ^ (J + 1) :=
          Nat.pow_le_pow_right (by decide) (by omega)
        have hbJ : b ≤ 2 ^ (J + 1) := hbupper.trans hp
        dsimp [N₀] at hbN
        omega
      let j := k - 1
      have hjk : j + 1 = k := Nat.sub_add_cancel (by omega)
      have hcj : 4 ≤ (R j).card := hJ j (by omega)
      have hcover := previous_reserve_covers_next hsub j b hcj (by rwa [hjk])
      have hsumle : (∑ x ∈ R j, x) ≤
          ∑ x ∈ smallerCoins (reserveSet R) b, x :=
        Finset.sum_le_sum_of_subset (reserve_subset_prefix hsub j b (by rwa [hjk]))
      exact hcover.trans (hsumle.trans (Nat.le_add_right _ _))
    · have hbsmall : b ≤ N₀ := Nat.le_of_lt (Nat.lt_of_not_ge hbN)
      exact hbsmall.trans (Nat.le_add_left N₀ _)
  exact ⟨N₀, infinite_prefix_growth_gives_syndetic_subsetSums
    (reserveSet R) N₀ (reserveSet_infinite hsub hcard) hgrowth⟩

end

end LocalCassels.ReserveGrowth
end

section
namespace LocalCassels

open Filter

noncomputable section

def shellCount (A : Set ℕ) (x : ℕ) : ℕ := by
  classical
  exact ((Finset.Ioc x (2 * x)).filter (fun n => n ∈ A)).card

lemma dyadicIncrement_eq_shellCard (A : Set ℕ) (x : ℕ) :
    dyadicIncrement A x = shellCount A x := by
  classical
  let s := (Finset.Icc 1 x).filter (fun n => n ∈ A)
  let t := (Finset.Icc 1 (2 * x)).filter (fun n => n ∈ A)
  have hst : s ⊆ t := by
    intro n hn
    simp only [s, t, Finset.mem_filter, Finset.mem_Icc] at hn ⊢
    exact ⟨⟨hn.1.1, hn.1.2.trans (by omega)⟩, hn.2⟩
  rw [dyadicIncrement, countingFunction, countingFunction]
  change t.card - s.card = _
  rw [← Finset.card_sdiff_of_subset hst]
  apply congrArg Finset.card
  ext n
  simp only [t, s, Finset.mem_sdiff, Finset.mem_filter,
    Finset.mem_Icc, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨hlo, hA⟩, hnot⟩
    refine ⟨⟨?_, hlo.2⟩, hA⟩
    by_contra hnx
    exact hnot ⟨⟨hlo.1, Nat.le_of_not_gt hnx⟩, hA⟩
  · rintro ⟨⟨hxn, hn2x⟩, hA⟩
    refine ⟨⟨⟨by omega, hn2x⟩, hA⟩, ?_⟩
    rintro ⟨⟨_, hnx⟩, _⟩
    omega

lemma dyadic_tendsto_eventually_many (A : Set ℕ)
    (hdyadic : Tendsto (dyadicIncrement A) atTop atTop) (K : ℕ) :
    ∀ᶠ x : ℕ in atTop, K ≤ shellCount A x := by
  filter_upwards [tendsto_atTop.1 hdyadic K] with x hx
  simpa only [dyadicIncrement_eq_shellCard] using hx

end

end LocalCassels
end

section
namespace LocalCassels

open Filter
open scoped BigOperators

lemma nearestIntegerDistance_nonneg (x : ℝ) :
    0 ≤ nearestIntegerDistance x := by
  apply le_min
  · exact Int.fract_nonneg x
  · exact sub_nonneg.mpr (Int.fract_lt_one x).le

lemma phasePartialSum_monotone (A : Set ℕ) (θ : ℝ) :
    Monotone (phasePartialSum A θ) := by
  intro M N hMN
  classical
  simp only [phasePartialSum]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
    exact ⟨⟨hn.1.1, hn.1.2.trans hMN⟩, hn.2⟩
  · intro n _ _
    exact nearestIntegerDistance_nonneg _

lemma phasePartialSum_tendsto_iff_unbounded (A : Set ℕ) (θ : ℝ) :
    Tendsto (phasePartialSum A θ) atTop atTop ↔
      ∀ B : ℝ, ∃ N : ℕ, B ≤ phasePartialSum A θ N :=
  (phasePartialSum_monotone A θ).tendsto_atTop_atTop_iff

/-- Even finitely many exceptions do not remove the rational obstruction. -/
theorem eventual_rational_phase_obstruction (A : Set ℕ) (q : ℕ) (hq : 2 ≤ q)
    (hevent : ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → n ∈ A → q ∣ n) :
    ¬ (∀ θ : ℝ, θ ∈ Set.Ioo 0 1 →
      Tendsto (phasePartialSum A θ) atTop atTop) := by
  intro hphase
  obtain ⟨N₀, hdiv⟩ := hevent
  let θ : ℝ := 1 / (q : ℝ)
  have hqpos : (0 : ℝ) < (q : ℝ) := by positivity
  have hθpos : (0 : ℝ) < θ := by
    dsimp [θ]
    positivity
  have hθlt : θ < (1 : ℝ) := by
    dsimp [θ]
    rw [div_lt_one hqpos]
    exact_mod_cast (show 1 < q from lt_of_lt_of_le Nat.one_lt_two hq)
  have htend : Tendsto (phasePartialSum A θ) atTop atTop :=
    hphase θ ⟨hθpos, hθlt⟩
  have heq : ∀ N : ℕ, N₀ ≤ N →
      phasePartialSum A θ N = phasePartialSum A θ N₀ := by
    intro N hN
    classical
    simp only [phasePartialSum]
    symm
    apply Finset.sum_subset
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
      exact ⟨⟨hn.1.1, hn.1.2.trans hN⟩, hn.2⟩
    · intro n hnN hn0
      simp only [Finset.mem_filter, Finset.mem_Icc] at hnN
      have hnle : N₀ ≤ n := by
        by_contra hnot
        have hnlt : n < N₀ := Nat.lt_of_not_ge hnot
        apply hn0
        simp only [Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨hnN.1.1, hnlt.le⟩, hnN.2⟩
      obtain ⟨k, rfl⟩ := hdiv n hnle hnN.2
      simp [θ, nearestIntegerDistance, Int.fract, hqpos.ne']
  have hconst : Tendsto (fun _ : ℕ => phasePartialSum A θ N₀) atTop atTop := by
    apply htend.congr'
    filter_upwards [eventually_atTop.2 ⟨N₀, fun N hN => heq N hN⟩] with N hN
    exact hN
  exact not_tendsto_const_atTop (phasePartialSum A θ N₀) atTop hconst

/-- The phase hypothesis forces nonmultiples of every `q ≥ 2` arbitrarily far
out in the set. -/
theorem phase_implies_tail_nonmultiple (A : Set ℕ)
    (hphase : ∀ θ : ℝ, θ ∈ Set.Ioo 0 1 →
      Tendsto (phasePartialSum A θ) atTop atTop)
    (q : ℕ) (hq : 2 ≤ q) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ n ∈ A ∧ ¬ q ∣ n := by
  by_contra hnone
  have hdiv : ∀ n : ℕ, N ≤ n → n ∈ A → q ∣ n := by
    intro n hn hnA
    by_contra hndiv
    exact hnone ⟨n, hn, hnA, hndiv⟩
  exact (eventual_rational_phase_obstruction A q hq ⟨N, hdiv⟩) hphase

end LocalCassels
end

section
namespace LocalCassels.PhaseShellDecomposition

open Filter
open scoped BigOperators
open LocalCassels.GrowthPartition

noncomputable section

/-- Members of `A` strictly above one and at most `2^K`. -/
def powerShellPrefix (A : Set ℕ) (K : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ioc 1 (2 ^ K)).filter (fun n => n ∈ A)

lemma powerShellPrefix_succ (A : Set ℕ) (K : ℕ) :
    powerShellPrefix A (K + 1) =
      powerShellPrefix A K ∪ powerShell A K := by
  classical
  ext n
  simp only [powerShellPrefix, powerShell, Finset.mem_filter, Finset.mem_Ioc,
    Finset.mem_union]
  constructor
  · rintro ⟨⟨h1, hu⟩, hnA⟩
    by_cases hn : n ≤ 2 ^ K
    · exact Or.inl ⟨⟨h1, hn⟩, hnA⟩
    · exact Or.inr ⟨⟨Nat.lt_of_not_ge hn, by simpa [pow_succ] using hu⟩, hnA⟩
  · rintro (⟨⟨h1, hu⟩, hnA⟩ | ⟨⟨hl, hu⟩, hnA⟩)
    · exact ⟨⟨h1, hu.trans (Nat.pow_le_pow_right (by decide) (by omega))⟩, hnA⟩
    · exact ⟨⟨(Nat.one_le_two_pow.trans_lt hl), by simpa [pow_succ] using hu⟩, hnA⟩

lemma powerShellPrefix_disjoint (A : Set ℕ) (K : ℕ) :
    Disjoint (powerShellPrefix A K) (powerShell A K) := by
  classical
  rw [Finset.disjoint_left]
  intro n hnP hnS
  simp only [powerShellPrefix, powerShell, Finset.mem_filter, Finset.mem_Ioc] at hnP hnS
  omega

lemma sum_powerShells_eq_prefix (A : Set ℕ) (f : ℕ → ℝ) (K : ℕ) :
    (∑ j ∈ Finset.range K, ∑ n ∈ powerShell A j, f n) =
      ∑ n ∈ powerShellPrefix A K, f n := by
  classical
  induction K with
  | zero => simp [powerShellPrefix]
  | succ K ih =>
      rw [Finset.sum_range_succ, ih]
      rw [show K + 1 = Nat.succ K by omega, powerShellPrefix_succ]
      exact (Finset.sum_union (powerShellPrefix_disjoint A K)).symm

lemma phasePartialSum_power_le_shells_add_one (A : Set ℕ) (θ : ℝ) (K : ℕ) :
    phasePartialSum A θ (2 ^ K) ≤
      nearestIntegerDistance θ +
        ∑ j ∈ Finset.range K, ∑ n ∈ powerShell A j,
          nearestIntegerDistance (θ * (n : ℝ)) := by
  classical
  let w : ℕ → ℝ := fun n => nearestIntegerDistance (θ * (n : ℝ))
  let P := (Finset.Icc 1 (2 ^ K)).filter (fun n => n ∈ A)
  have hsub : P ⊆ insert 1 (powerShellPrefix A K) := by
    intro n hn
    have hn' := Finset.mem_filter.mp hn
    have hI := Finset.mem_Icc.mp hn'.1
    by_cases hn1 : n = 1
    · subst n
      simp
    · have hgt : 1 < n := by omega
      simp only [Finset.mem_insert]
      exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hgt, hI.2⟩, hn'.2⟩)
  have hnonneg : ∀ n ∈ insert 1 (powerShellPrefix A K), 0 ≤ w n := by
    intro n hn
    exact nearestIntegerDistance_nonneg _
  have hle : (∑ n ∈ P, w n) ≤ ∑ n ∈ insert 1 (powerShellPrefix A K), w n :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun n hnBig hnSmall => hnonneg n hnBig)
  have h1not : 1 ∉ powerShellPrefix A K := by
    simp [powerShellPrefix]
  rw [Finset.sum_insert h1not, ← sum_powerShells_eq_prefix] at hle
  simpa [phasePartialSum, P, w] using hle

/-- Canonical phase divergence implies divergence of the corresponding sums
when regrouped by dyadic power shells. -/
theorem phase_divergence_implies_powerShell_divergence
    (A : Set ℕ) (θ : ℝ)
    (hphase : Tendsto (phasePartialSum A θ) atTop atTop) :
    Tendsto
      (fun K => ∑ j ∈ Finset.range K, ∑ n ∈ powerShell A j,
        nearestIntegerDistance (θ * (n : ℝ))) atTop atTop := by
  have hpow : Tendsto (fun K => phasePartialSum A θ (2 ^ K)) atTop atTop :=
    hphase.comp (tendsto_pow_atTop_atTop_of_one_lt (r := (2 : ℕ)) (by decide))
  rw [tendsto_atTop]
  intro b
  have hp := tendsto_atTop.1 hpow (b + nearestIntegerDistance θ)
  filter_upwards [hp] with K hK
  have hle := phasePartialSum_power_le_shells_add_one A θ K
  linarith

end

end LocalCassels.PhaseShellDecomposition
end

section
namespace LocalCassels.BalancedReservation

open scoped BigOperators

noncomputable section

/-- Among all `r`-subsets of a finite set, one has weight at most the
corresponding fraction of the total weight. -/
theorem exists_subset_card_sum_le_average
    {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℝ)
    (r : ℕ) (hr : r ≤ s.card) :
    ∃ t : Finset α, t ⊆ s ∧ t.card = r ∧
      (s.card : ℝ) * (∑ x ∈ t, f x) ≤
        (r : ℝ) * (∑ x ∈ s, f x) := by
  classical
  let P := s.powersetCard r
  have hP : P.Nonempty := by
    exact Finset.powersetCard_nonempty.mpr hr
  let vals : Finset ℝ := P.image (fun t => ∑ x ∈ t, f x)
  have hvals : vals.Nonempty := hP.image _
  let m := vals.min' hvals
  have hm : m ∈ vals := Finset.min'_mem vals hvals
  change m ∈ P.image (fun t => ∑ x ∈ t, f x) at hm
  rw [Finset.mem_image] at hm
  obtain ⟨t, htP, htSum⟩ := hm
  have hts : t ⊆ s := (Finset.mem_powersetCard.mp htP).1
  have htcard : t.card = r := (Finset.mem_powersetCard.mp htP).2
  have hminimal : ∀ u ∈ P, (∑ x ∈ t, f x) ≤ ∑ x ∈ u, f x := by
    intro u hu
    have huval : (∑ x ∈ u, f x) ∈ vals := Finset.mem_image.mpr ⟨u, hu, rfl⟩
    have hmin := Finset.min'_le vals (∑ x ∈ u, f x) huval
    calc
      (∑ x ∈ t, f x) = m := htSum
      _ ≤ ∑ x ∈ u, f x := hmin
  have hpair : ∀ y ∈ t, ∀ x ∈ s \ t, f y ≤ f x := by
    intro y hyt x hxc
    by_contra hnot
    have hxy : f x < f y := lt_of_not_ge hnot
    let u := insert x (t.erase y)
    have hxt : x ∉ t := (Finset.mem_sdiff.mp hxc).2
    have hyx : x ≠ y := by
      intro h
      subst x
      exact hxt hyt
    have huSub : u ⊆ s := by
      apply Finset.insert_subset
      · exact (Finset.mem_sdiff.mp hxc).1
      · exact (t.erase_subset y).trans hts
    have hxErase : x ∉ t.erase y := by
      intro hx
      exact hxt (Finset.mem_of_mem_erase hx)
    have hucard : u.card = r := by
      change (insert x (t.erase y)).card = r
      have htpos : 0 < t.card := Finset.card_pos.mpr ⟨y, hyt⟩
      rw [Finset.card_insert_of_notMem hxErase,
        Finset.card_erase_of_mem hyt, htcard]
      omega
    have huP : u ∈ P := Finset.mem_powersetCard.mpr ⟨huSub, hucard⟩
    have hsumu : (∑ z ∈ u, f z) = (∑ z ∈ t, f z) - f y + f x := by
      change (∑ z ∈ insert x (t.erase y), f z) = _
      rw [Finset.sum_insert hxErase]
      have herase := Finset.sum_erase_add t f hyt
      calc
        f x + ∑ z ∈ t.erase y, f z =
            (∑ z ∈ t.erase y, f z) + f y - f y + f x := by ring
        _ = (∑ z ∈ t, f z) - f y + f x := by rw [herase]
    have hmin := hminimal u huP
    rw [hsumu] at hmin
    linarith
  let c := s \ t
  have hdouble :
      (c.card : ℝ) * (∑ y ∈ t, f y) ≤
        (t.card : ℝ) * (∑ x ∈ c, f x) := by
    calc
      (c.card : ℝ) * (∑ y ∈ t, f y) =
          ∑ x ∈ c, ∑ y ∈ t, f y := by simp [mul_comm]
      _ ≤ ∑ x ∈ c, ∑ y ∈ t, f x := by
        apply Finset.sum_le_sum
        intro x hxc
        apply Finset.sum_le_sum
        intro y hyt
        exact hpair y hyt x hxc
      _ = (t.card : ℝ) * (∑ x ∈ c, f x) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [Finset.mul_sum]
  have hcCard : c.card + t.card = s.card := by
    change (s \ t).card + t.card = s.card
    rw [Finset.card_sdiff_of_subset hts]
    omega
  have hsumSplit : (∑ x ∈ t, f x) + ∑ x ∈ c, f x = ∑ x ∈ s, f x := by
    change (∑ x ∈ t, f x) + ∑ x ∈ s \ t, f x = ∑ x ∈ s, f x
    have hdis : Disjoint t (s \ t) := Finset.disjoint_sdiff
    have hunion : t ∪ (s \ t) = s := Finset.union_sdiff_of_subset hts
    rw [← Finset.sum_union hdis, hunion]
  have hdoubleR :
      (c.card : ℝ) * (∑ y ∈ t, f y) ≤
        (r : ℝ) * (∑ x ∈ c, f x) := by
    simpa [htcard] using hdouble
  refine ⟨t, hts, htcard, ?_⟩
  rw [← hcCard, Nat.cast_add, htcard, ← hsumSplit]
  calc
    ((c.card : ℝ) + r) * (∑ x ∈ t, f x) =
        (c.card : ℝ) * (∑ x ∈ t, f x) + r * (∑ x ∈ t, f x) := by ring
    _ ≤ r * (∑ x ∈ c, f x) + r * (∑ x ∈ t, f x) := by
      simpa [add_comm] using
        (add_le_add_right hdoubleR (r * (∑ x ∈ t, f x)))
    _ = (r : ℝ) * ((∑ x ∈ t, f x) + ∑ x ∈ c, f x) := by ring

/-- Simultaneous normalized version: reserve `r` elements while taking at most
an `r*d/h` fraction of every one of `d` nonnegative weight coordinates. -/
theorem exists_subset_card_simultaneous_normalized
    {α ι : Type*} [DecidableEq α] [Fintype ι]
    (s : Finset α) (w : ι → α → ℝ)
    (hw : ∀ i x, x ∈ s → 0 ≤ w i x)
    (r : ℕ) (hr : r ≤ s.card) :
    ∃ t : Finset α, t ⊆ s ∧ t.card = r ∧
      ∀ i : ι,
        (s.card : ℝ) * (∑ x ∈ t, w i x) ≤
          (r * Fintype.card ι : ℕ) * (∑ x ∈ s, w i x) := by
  classical
  let W : ι → ℝ := fun i => ∑ x ∈ s, w i x
  let f : α → ℝ := fun x => ∑ i : ι, if W i = 0 then 0 else w i x / W i
  obtain ⟨t, hts, htcard, havg⟩ :=
    exists_subset_card_sum_le_average s f r hr
  refine ⟨t, hts, htcard, ?_⟩
  intro i
  by_cases hWi : W i = 0
  · have hzero : ∀ x ∈ s, w i x = 0 := by
      intro x hx
      have hnonneg := hw i x hx
      have hle : w i x ≤ W i := Finset.single_le_sum
        (fun y hy => hw i y hy) hx
      rw [hWi] at hle
      linarith
    have hzeroT : ∑ x ∈ t, w i x = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      exact hzero x (hts hx)
    rw [hzeroT, mul_zero]
    exact mul_nonneg (Nat.cast_nonneg _)
      (Finset.sum_nonneg fun x hx => hw i x hx)
  · have hWpos : 0 < W i := lt_of_le_of_ne
      (Finset.sum_nonneg fun x hx => hw i x hx) (Ne.symm hWi)
    have hcoord : ∑ x ∈ t, w i x / W i ≤ ∑ x ∈ t, f x := by
      apply Finset.sum_le_sum
      intro x hx
      dsimp [f]
      have hterms : ∀ j ∈ (Finset.univ : Finset ι),
          0 ≤ if W j = 0 then 0 else w j x / W j := by
        intro j hj
        by_cases hWj : W j = 0
        · simp [hWj]
        · simp only [hWj, ↓reduceIte]
          exact div_nonneg (hw j x (hts hx))
            (Finset.sum_nonneg fun y hy => hw j y hy)
      calc
        w i x / W i = (if W i = 0 then 0 else w i x / W i) := by simp [hWi]
        _ ≤ ∑ j : ι, (if W j = 0 then 0 else w j x / W j) :=
          Finset.single_le_sum hterms (Finset.mem_univ i)
    have hsumf : (∑ x ∈ s, f x) ≤ Fintype.card ι := by
      calc
        (∑ x ∈ s, f x) = ∑ i : ι, ∑ x ∈ s,
            (if W i = 0 then 0 else w i x / W i) := by
              simp only [f]
              rw [Finset.sum_comm]
        _ ≤ ∑ _i : ι, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro j hj
          by_cases hWj : W j = 0
          · simp [hWj]
          · simp only [hWj, ↓reduceIte]
            rw [← Finset.sum_div]
            simp [W, hWj]
        _ = Fintype.card ι := by simp
    have hraw : (s.card : ℝ) * (∑ x ∈ t, w i x / W i) ≤
        (r : ℝ) * Fintype.card ι := by
      calc
        _ ≤ (s.card : ℝ) * (∑ x ∈ t, f x) :=
          mul_le_mul_of_nonneg_left hcoord (Nat.cast_nonneg _)
        _ ≤ (r : ℝ) * (∑ x ∈ s, f x) := havg
        _ ≤ (r : ℝ) * Fintype.card ι :=
          mul_le_mul_of_nonneg_left hsumf (Nat.cast_nonneg _)
    rw [← Finset.sum_div] at hraw
    have hmul := mul_le_mul_of_nonneg_right hraw hWpos.le
    calc
      (s.card : ℝ) * (∑ x ∈ t, w i x) =
          ((s.card : ℝ) * ((∑ x ∈ t, w i x) / W i)) * W i := by
            field_simp
      _ ≤ ((r : ℝ) * Fintype.card ι) * W i := hmul
      _ = ((r * Fintype.card ι : ℕ) : ℝ) * (∑ x ∈ s, w i x) := by
        simp only [W, Nat.cast_mul]

end

end LocalCassels.BalancedReservation
end

section
namespace LocalCassels.VariableReservation

open Filter
open scoped BigOperators Topology
open LocalCassels.BalancedReservation

noncomputable section

/-- Countably many divergent nonnegative shell-weight series survive reserving
`r j` points from shell `j`, provided both the number `d j` of protected
coordinates and the reserve size can grow while `r j * d j` remains a small
fraction of the shell. -/
theorem exists_variable_reserves_preserving_countable_divergence
    {α : Type*} [DecidableEq α]
    (S : ℕ → Finset α) (w : ℕ → α → ℝ)
    (hw : ∀ i j x, x ∈ S j → 0 ≤ w i x)
    (r d : ℕ → ℕ) (hrpos : ∀ j, 0 < r j)
    (hr : ∀ j, r j ≤ (S j).card)
    (hd : Tendsto d atTop atTop)
    (hroom : ∀ᶠ j : ℕ in atTop, 2 * (r j * d j) ≤ (S j).card)
    (hdiv : ∀ i : ℕ, Tendsto
      (fun N => ∑ j ∈ Finset.range N, ∑ x ∈ S j, w i x) atTop atTop) :
    ∃ R : ℕ → Finset α,
      (∀ j, R j ⊆ S j ∧ (R j).card = r j) ∧
      (∀ i : ℕ, Tendsto
        (fun N => ∑ j ∈ Finset.range N,
          ((∑ x ∈ S j, w i x) - ∑ x ∈ R j, w i x)) atTop atTop) := by
  classical
  have hchoose : ∀ j, ∃ t : Finset α, t ⊆ S j ∧ t.card = r j ∧
      ∀ i : Fin (d j),
        ((S j).card : ℝ) * (∑ x ∈ t, w i.val x) ≤
          (r j * d j : ℕ) * (∑ x ∈ S j, w i.val x) := by
    intro j
    simpa using exists_subset_card_simultaneous_normalized
      (S j) (fun i : Fin (d j) => w i.val)
      (fun i x hx => hw i.val j x hx) (r j) (hr j)
  choose R hRsub hRcard hRbound using hchoose
  refine ⟨R, fun j => ⟨hRsub j, hRcard j⟩, ?_⟩
  intro i
  let full : ℕ → ℝ := fun j => ∑ x ∈ S j, w i x
  let kept : ℕ → ℝ := fun j => full j - ∑ x ∈ R j, w i x
  have hfullnonneg : ∀ j, 0 ≤ full j := by
    intro j
    exact Finset.sum_nonneg fun x hx => hw i j x hx
  have hreserveNonneg : ∀ j, 0 ≤ ∑ x ∈ R j, w i x := by
    intro j
    exact Finset.sum_nonneg fun x hx => hw i j x (hRsub j hx)
  have hreserveLe : ∀ j, (∑ x ∈ R j, w i x) ≤ full j := by
    intro j
    exact Finset.sum_le_sum_of_subset_of_nonneg (hRsub j)
      (fun x hxS hxR => hw i j x hxS)
  have hkeptNonneg : ∀ j, 0 ≤ kept j := by
    intro j
    exact sub_nonneg.mpr (hreserveLe j)
  have hid : ∀ᶠ j : ℕ in atTop, i < d j :=
    (tendsto_atTop.1 hd (i + 1)).mono fun j hj => by omega
  have hhalf : ∀ᶠ j : ℕ in atTop, full j / 2 ≤ kept j := by
    filter_upwards [hroom, hid] with j hjroom hijd
    have hb := hRbound j ⟨i, hijd⟩
    have hrdpos : (0 : ℝ) < (r j * d j : ℕ) := by
      exact_mod_cast Nat.mul_pos (hrpos j) (by omega)
    have hcard : (2 : ℝ) * (r j * d j : ℕ) ≤ (S j).card := by
      exact_mod_cast hjroom
    have hres0 := hreserveNonneg j
    dsimp [kept, full]
    dsimp [full] at hb hcard
    have hscaled : (2 : ℝ) * (r j * d j : ℕ) *
        (∑ x ∈ R j, w i x) ≤
        (r j * d j : ℕ) * (∑ x ∈ S j, w i x) := by
      calc
        _ ≤ ((S j).card : ℝ) * (∑ x ∈ R j, w i x) :=
          mul_le_mul_of_nonneg_right hcard hres0
        _ ≤ _ := hb
    have htwice : (2 : ℝ) * (∑ x ∈ R j, w i x) ≤
        ∑ x ∈ S j, w i x := by
      exact (mul_le_mul_iff_right₀ hrdpos).mp (by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hscaled)
    linarith
  obtain ⟨J₀, hJ₀⟩ := eventually_atTop.1 hhalf
  rw [tendsto_atTop]
  intro b
  have htarget := tendsto_atTop.1 (hdiv i)
    (2 * max b 0 + ∑ j ∈ Finset.range J₀, full j)
  filter_upwards [htarget, eventually_ge_atTop J₀] with N hN hNJ
  have hdecomp : Finset.range N = Finset.range J₀ ∪ Finset.Ico J₀ N := by
    ext j
    simp
    omega
  have hdis : Disjoint (Finset.range J₀) (Finset.Ico J₀ N) := by
    rw [Finset.disjoint_left]
    intro j hj0 hjI
    simp at hj0 hjI
    omega
  have htailFull : 2 * max b 0 ≤ ∑ j ∈ Finset.Ico J₀ N, full j := by
    rw [hdecomp, Finset.sum_union hdis] at hN
    linarith
  have htailKept : ∑ j ∈ Finset.Ico J₀ N, full j / 2 ≤
      ∑ j ∈ Finset.Ico J₀ N, kept j := by
    apply Finset.sum_le_sum
    intro j hj
    exact hJ₀ j (by simpa using (Finset.mem_Ico.mp hj).1)
  have hhalfSum : (∑ j ∈ Finset.Ico J₀ N, full j) / 2 =
      ∑ j ∈ Finset.Ico J₀ N, full j / 2 := by
    rw [Finset.sum_div]
  have hbTail : b ≤ ∑ j ∈ Finset.Ico J₀ N, kept j := by
    rw [← hhalfSum] at htailKept
    have : b ≤ (∑ j ∈ Finset.Ico J₀ N, full j) / 2 := by
      have hbmax : b ≤ max b 0 := le_max_left _ _
      linarith
    exact this.trans htailKept
  have htailSubset : Finset.Ico J₀ N ⊆ Finset.range N := by
    intro j hj
    simp only [Finset.mem_Ico, Finset.mem_range] at hj ⊢
    exact hj.2
  have htailToAll : (∑ j ∈ Finset.Ico J₀ N, kept j) ≤
      ∑ j ∈ Finset.range N, kept j :=
    Finset.sum_le_sum_of_subset_of_nonneg htailSubset
      (fun j hjN hjI => hkeptNonneg j)
  exact hbTail.trans htailToAll

end

end LocalCassels.VariableReservation
end

section
namespace LocalCassels.GrowingReservation

open Filter
open scoped BigOperators Topology
open LocalCassels.VariableReservation

noncomputable section

lemma sqrt_half_tendsto_atTop {h : ℕ → ℕ} (hh : Tendsto h atTop atTop) :
    Tendsto (fun j => (h j).sqrt / 2) atTop atTop := by
  rw [tendsto_atTop]
  intro b
  have hb := tendsto_atTop.1 hh ((2 * b) * (2 * b))
  filter_upwards [hb] with j hj
  have hs : 2 * b ≤ (h j).sqrt := by
    rw [Nat.le_sqrt]
    exact hj
  omega

lemma sqrt_half_room (n : ℕ) :
    2 * ((n.sqrt / 2) * (n.sqrt / 2)) ≤ n := by
  have hs := Nat.sqrt_le n
  have hh : 2 * (n.sqrt / 2) ≤ n.sqrt := by omega
  calc
    2 * ((n.sqrt / 2) * (n.sqrt / 2)) ≤
        (2 * (n.sqrt / 2)) * (2 * (n.sqrt / 2)) := by nlinarith
    _ ≤ n.sqrt * n.sqrt := Nat.mul_le_mul hh hh
    _ ≤ n := hs

/-- If every shell already has at least four points and shell cardinalities
run to infinity, one can reserve a number of points tending to infinity while
preserving every divergent series in a prescribed countable nonnegative
family on the complements. -/
theorem exists_growing_reserves_preserving_countable_divergence
    {α : Type*} [DecidableEq α]
    (S : ℕ → Finset α) (w : ℕ → α → ℝ)
    (hw : ∀ i j x, x ∈ S j → 0 ≤ w i x)
    (hfour : ∀ j, 4 ≤ (S j).card)
    (hcard : Tendsto (fun j => (S j).card) atTop atTop)
    (hdiv : ∀ i : ℕ, Tendsto
      (fun N => ∑ j ∈ Finset.range N, ∑ x ∈ S j, w i x) atTop atTop) :
    ∃ R : ℕ → Finset α,
      (∀ j, R j ⊆ S j) ∧
      Tendsto (fun j => (R j).card) atTop atTop ∧
      (∀ i : ℕ, Tendsto
        (fun N => ∑ j ∈ Finset.range N,
          ((∑ x ∈ S j, w i x) - ∑ x ∈ R j, w i x)) atTop atTop) := by
  classical
  let k : ℕ → ℕ := fun j => ((S j).card).sqrt / 2
  have hkpos : ∀ j, 0 < k j := by
    intro j
    have hs : 2 ≤ ((S j).card).sqrt := by
      rw [Nat.le_sqrt]
      nlinarith [hfour j]
    dsimp [k]
    omega
  have hkle : ∀ j, k j ≤ (S j).card := by
    intro j
    dsimp [k]
    exact (Nat.div_le_self _ _).trans (Nat.sqrt_le_self _)
  have hkTop : Tendsto k atTop atTop := sqrt_half_tendsto_atTop hcard
  have hroom : ∀ᶠ j : ℕ in atTop,
      2 * (k j * k j) ≤ (S j).card := by
    exact Filter.Eventually.of_forall fun j => sqrt_half_room (S j).card
  obtain ⟨R, hR, hkeep⟩ :=
    exists_variable_reserves_preserving_countable_divergence
      S w hw k k hkpos hkle hkTop hroom hdiv
  refine ⟨R, fun j => (hR j).1, ?_, hkeep⟩
  have heq : (fun j => (R j).card) = k := by
    funext j
    exact (hR j).2
  rw [heq]
  exact hkTop

end

end LocalCassels.GrowingReservation
end

section
namespace LocalCassels.CanonicalCountableReserve

open Filter
open scoped BigOperators
open LocalCassels.GrowthPartition LocalCassels.GrowingReservation LocalCassels.ReserveGrowth

noncomputable section

lemma tendsto_shift_index (J : ℕ) : Tendsto (fun n : ℕ => J + n) atTop atTop := by
  rw [tendsto_atTop]
  intro b
  filter_upwards [eventually_ge_atTop b] with n hn
  omega

lemma divergent_shell_sums_shift
    (f : ℕ → ℝ)
    (h : Tendsto (fun N => ∑ j ∈ Finset.range N, f j) atTop atTop)
    (J : ℕ) :
    Tendsto (fun N => ∑ j ∈ Finset.range N, f (J + j)) atTop atTop := by
  rw [tendsto_atTop]
  intro b
  have ht := tendsto_atTop.1 h
    (b + ∑ j ∈ Finset.range J, f j)
  filter_upwards [(tendsto_shift_index J).eventually ht] with N hN
  rw [Finset.sum_range_add] at hN
  linarith

/-- Canonical dyadic-shell version of F-052/F-053 allowing arbitrary finite
initial shells: after a cutoff one can choose growing shell reserves which are
syndetic and preserve a prescribed countable family of divergent shell sums. -/
theorem exists_eventual_syndetic_reserve_preserving_countable_divergence
    (A : Set ℕ) (w : ℕ → ℕ → ℝ)
    (hw : ∀ i j n, n ∈ powerShell A j → 0 ≤ w i n)
    (hcard : Tendsto (fun j => (powerShell A j).card) atTop atTop)
    (hdiv : ∀ i : ℕ, Tendsto
      (fun N => ∑ j ∈ Finset.range N,
        ∑ n ∈ powerShell A j, w i n) atTop atTop) :
    ∃ R : ℕ → Finset ℕ,
      (∀ j, R j ⊆ powerShell A j) ∧
      Tendsto (fun j => (R j).card) atTop atTop ∧
      (∀ i : ℕ, ∃ J : ℕ, Tendsto
        (fun N => ∑ j ∈ Finset.range N,
          ((∑ n ∈ powerShell A (J + j), w i n) -
            ∑ n ∈ R (J + j), w i n)) atTop atTop) ∧
      (∃ K : ℕ, ∀ n : ℕ, ∃ t : Finset ℕ,
        (∀ b ∈ t, b ∈ reserveSet R) ∧
        (∑ b ∈ t, b) ≤ n ∧ n ≤ (∑ b ∈ t, b) + K) := by
  classical
  have hfour : ∀ᶠ j : ℕ in atTop, 4 ≤ (powerShell A j).card :=
    tendsto_atTop.1 hcard 4
  obtain ⟨J, hJ⟩ := eventually_atTop.1 hfour
  let S : ℕ → Finset ℕ := fun j => powerShell A (J + j)
  have hSfour : ∀ j, 4 ≤ (S j).card := by
    intro j
    exact hJ (J + j) (by omega)
  have hScard : Tendsto (fun j => (S j).card) atTop atTop := by
    exact hcard.comp (tendsto_shift_index J)
  have hSdiv : ∀ i : ℕ, Tendsto
      (fun N => ∑ j ∈ Finset.range N, ∑ n ∈ S j, w i n) atTop atTop := by
    intro i
    exact divergent_shell_sums_shift
      (fun j => ∑ n ∈ powerShell A j, w i n) (hdiv i) J
  obtain ⟨R', hR'sub, hR'card, hR'keep⟩ :=
    exists_growing_reserves_preserving_countable_divergence S w
      (fun i j n hn => hw i (J + j) n hn) hSfour hScard hSdiv
  let R : ℕ → Finset ℕ := fun j => if hj : J ≤ j then R' (j - J) else ∅
  have hRsub : ∀ j, R j ⊆ powerShell A j := by
    intro j
    by_cases hj : J ≤ j
    · simp only [R, dif_pos hj]
      have hs := hR'sub (j - J)
      simpa [S, Nat.add_sub_of_le hj] using hs
    · simp [R, hj]
  have hRcard : Tendsto (fun j => (R j).card) atTop atTop := by
    rw [tendsto_atTop]
    intro b
    obtain ⟨K, hK⟩ := eventually_atTop.1 (tendsto_atTop.1 hR'card b)
    filter_upwards [eventually_ge_atTop (J + K)] with j hj
    have hJj : J ≤ j := by omega
    have hKj : K ≤ j - J := by omega
    simpa [R, hJj] using hK (j - J) hKj
  refine ⟨R, hRsub, hRcard, ?_, ?_⟩
  · intro i
    refine ⟨J, ?_⟩
    simpa [S, R] using hR'keep i
  · exact growing_shell_reserves_are_syndetic A R hRsub hRcard

end

end LocalCassels.CanonicalCountableReserve
end

section
namespace LocalCassels.CountablePhaseSyndeticReserve

open Filter
open scoped BigOperators
open LocalCassels.GrowthPartition
open LocalCassels.CanonicalCountableReserve LocalCassels.PhaseShellDecomposition
open LocalCassels.ReserveGrowth

noncomputable section

end

end LocalCassels.CountablePhaseSyndeticReserve
end

section
namespace LocalCassels.ReserveComplementPhase

open Filter
open scoped BigOperators
open LocalCassels.GrowthPartition LocalCassels.PhaseShellDecomposition
open LocalCassels.ReserveGrowth LocalCassels.CountablePhaseSyndeticReserve

noncomputable section

lemma powerShell_reserve_complement {A : Set ℕ} {R : ℕ → Finset ℕ}
    (hsub : ∀ j, R j ⊆ powerShell A j) (k : ℕ) :
    powerShell A k \ R k = powerShell (A \ reserveSet R) k := by
  classical
  ext n
  constructor
  · intro hn
    have hdata := Finset.mem_sdiff.mp hn
    have hnA := hdata.1
    simp only [powerShell, Finset.mem_filter] at hnA ⊢
    refine ⟨hnA.1, hnA.2, ?_⟩
    intro hnB
    obtain ⟨l, hnl⟩ := hnB
    have hnAl := hsub l hnl
    have hkl : k = l := powerShell_index_unique A hdata.1 hnAl
    subst l
    exact hdata.2 hnl
  · intro hn
    simp only [powerShell, Finset.mem_filter] at hn
    have hnA : n ∈ powerShell A k := by
      simp only [powerShell, Finset.mem_filter]
      exact ⟨hn.1, hn.2.1⟩
    apply Finset.mem_sdiff.mpr
    refine ⟨hnA, ?_⟩
    intro hnR
    exact hn.2.2 ⟨k, hnR⟩

lemma shell_sum_sub_reserve {A : Set ℕ} {R : ℕ → Finset ℕ}
    (hsub : ∀ j, R j ⊆ powerShell A j) (f : ℕ → ℝ) (k : ℕ) :
    (∑ n ∈ powerShell A k, f n) - ∑ n ∈ R k, f n =
      ∑ n ∈ powerShell (A \ reserveSet R) k, f n := by
  classical
  have hs := Finset.sum_sdiff (hsub k) (f := f)
  rw [powerShell_reserve_complement hsub k] at hs
  linarith

lemma shifted_shell_sum_le_phasePartialSum
    (C : Set ℕ) (θ : ℝ) (J N : ℕ) :
    (∑ j ∈ Finset.range N, ∑ n ∈ powerShell C (J + j),
      nearestIntegerDistance (θ * (n : ℝ))) ≤
      phasePartialSum C θ (2 ^ (J + N)) := by
  classical
  let f : ℕ → ℝ := fun n => nearestIntegerDistance (θ * (n : ℝ))
  let g : ℕ → ℝ := fun j => ∑ n ∈ powerShell C j, f n
  have hprefixNonneg : 0 ≤ ∑ j ∈ Finset.range J, g j := by
    apply Finset.sum_nonneg
    intro j hj
    exact Finset.sum_nonneg fun n hn => nearestIntegerDistance_nonneg _
  have hshiftTotal : (∑ j ∈ Finset.range N, g (J + j)) ≤
      ∑ j ∈ Finset.range (J + N), g j := by
    rw [Finset.sum_range_add]
    linarith
  have hprefixSubset : powerShellPrefix C (J + N) ⊆
      (Finset.Icc 1 (2 ^ (J + N))).filter (fun n => n ∈ C) := by
    intro n hn
    simp only [powerShellPrefix, Finset.mem_filter, Finset.mem_Ioc,
      Finset.mem_Icc] at hn ⊢
    exact ⟨⟨hn.1.1.le, hn.1.2⟩, hn.2⟩
  have hsumle : (∑ n ∈ powerShellPrefix C (J + N), f n) ≤
      ∑ n ∈ (Finset.Icc 1 (2 ^ (J + N))).filter (fun n => n ∈ C), f n :=
    Finset.sum_le_sum_of_subset_of_nonneg hprefixSubset
      (fun n hnBig hnSmall => nearestIntegerDistance_nonneg _)
  change (∑ j ∈ Finset.range N, g (J + j)) ≤ _
  calc
    (∑ j ∈ Finset.range N, g (J + j)) ≤
        ∑ j ∈ Finset.range (J + N), g j := hshiftTotal
    _ = ∑ n ∈ powerShellPrefix C (J + N), f n :=
      sum_powerShells_eq_prefix C f (J + N)
    _ ≤ _ := by simpa [phasePartialSum, f] using hsumle

/-- Divergence of the shell-by-shell remainder after deleting reserves is
exactly canonical phase divergence on the set-theoretic complement. -/
theorem complement_phase_diverges_of_shell_remainder
    (A : Set ℕ) (R : ℕ → Finset ℕ)
    (hsub : ∀ j, R j ⊆ powerShell A j)
    (θ : ℝ) (J : ℕ)
    (hrem : Tendsto
      (fun N => ∑ j ∈ Finset.range N,
        ((∑ n ∈ powerShell A (J + j),
            nearestIntegerDistance (θ * (n : ℝ))) -
          ∑ n ∈ R (J + j),
            nearestIntegerDistance (θ * (n : ℝ)))) atTop atTop) :
    Tendsto (phasePartialSum (A \ reserveSet R) θ) atTop atTop := by
  rw [phasePartialSum_tendsto_iff_unbounded]
  intro b
  have hb := tendsto_atTop.1 hrem b
  obtain ⟨N, hN⟩ := hb.exists
  have heq : (∑ j ∈ Finset.range N,
        ((∑ n ∈ powerShell A (J + j),
            nearestIntegerDistance (θ * (n : ℝ))) -
          ∑ n ∈ R (J + j),
            nearestIntegerDistance (θ * (n : ℝ)))) =
      ∑ j ∈ Finset.range N,
        ∑ n ∈ powerShell (A \ reserveSet R) (J + j),
          nearestIntegerDistance (θ * (n : ℝ)) := by
    apply Finset.sum_congr rfl
    intro j hj
    exact shell_sum_sub_reserve hsub
      (fun n => nearestIntegerDistance (θ * (n : ℝ))) (J + j)
  rw [heq] at hN
  refine ⟨2 ^ (J + N), hN.trans ?_⟩
  exact shifted_shell_sum_le_phasePartialSum (A \ reserveSet R) θ J N

end

end LocalCassels.ReserveComplementPhase
end

section
namespace LocalCassels.CountableConvergencePhases

open Filter
open scoped BigOperators
open LocalCassels

noncomputable section

lemma nd_nonneg (x : ℝ) : 0 ≤ nearestIntegerDistance x := by
  apply le_min
  · exact Int.fract_nonneg x
  · exact sub_nonneg.mpr (Int.fract_lt_one x).le

lemma nd_eq_abs_sub_round (x : ℝ) :
    nearestIntegerDistance x = |x - (round x : ℝ)| :=
  (abs_sub_round_eq_min x).symm

lemma nd_le_abs_sub_int (x : ℝ) (z : ℤ) :
    nearestIntegerDistance x ≤ |x - (z : ℝ)| := by
  rw [nd_eq_abs_sub_round]
  exact round_le x z

lemma nd_add_le (x y : ℝ) :
    nearestIntegerDistance (x + y) ≤
      nearestIntegerDistance x + nearestIntegerDistance y := by
  calc
    nearestIntegerDistance (x + y) ≤
        |(x + y) - ((round x + round y : ℤ) : ℝ)| :=
      nd_le_abs_sub_int _ _
    _ = |(x - (round x : ℝ)) + (y - (round y : ℝ))| := by
      rw [Int.cast_add]
      ring_nf
    _ ≤ |x - (round x : ℝ)| + |y - (round y : ℝ)| := abs_add_le _ _
    _ = nearestIntegerDistance x + nearestIntegerDistance y := by
      rw [← nd_eq_abs_sub_round, ← nd_eq_abs_sub_round]

lemma nd_neg (x : ℝ) : nearestIntegerDistance (-x) = nearestIntegerDistance x := by
  apply le_antisymm
  · calc
      nearestIntegerDistance (-x) ≤ |-x - ((-round x : ℤ) : ℝ)| :=
        nd_le_abs_sub_int _ _
      _ = |x - (round x : ℝ)| := by
        rw [Int.cast_neg]
        rw [show -x - -(round x : ℝ) = -(x - (round x : ℝ)) by ring_nf,
          abs_neg]
      _ = nearestIntegerDistance x := (nd_eq_abs_sub_round x).symm
  · simpa only [neg_neg] using
      (show nearestIntegerDistance (-(-x)) ≤ nearestIntegerDistance (-x) by
        calc
          nearestIntegerDistance (-(-x)) ≤
              |-(-x) - ((-round (-x) : ℤ) : ℝ)| := nd_le_abs_sub_int _ _
          _ = |(-x) - (round (-x) : ℝ)| := by
            rw [Int.cast_neg]
            rw [show - -x - -(round (-x) : ℝ) = -((-x) - (round (-x) : ℝ)) by
              ring_nf, abs_neg]
          _ = nearestIntegerDistance (-x) := (nd_eq_abs_sub_round (-x)).symm)

lemma nd_sub_le (x y : ℝ) :
    nearestIntegerDistance (x - y) ≤
      nearestIntegerDistance x + nearestIntegerDistance y := by
  simpa only [sub_eq_add_neg, nd_neg] using nd_add_le x (-y)

lemma nd_eq_self_of_mem (z : ℝ) (hz0 : 0 ≤ z) (hzh : z ≤ 1 / 2) :
    nearestIntegerDistance z = z := by
  have hz1 : z < 1 := hzh.trans_lt (by norm_num)
  rw [nearestIntegerDistance, Int.fract_eq_self.mpr ⟨hz0, hz1⟩]
  exact min_eq_left (by linarith)

lemma shell_phase_lower
    (C : Set ℕ) (x : ℕ) (δ : ℝ)
    (hδ : 0 < δ)
    (hxlo : 1 / 8 ≤ (x : ℝ) * δ)
    (hxhi : (x : ℝ) * δ ≤ 1 / 4) :
    ((shellCount C x : ℝ) / 8) ≤ phasePartialSum C δ (2 * x) := by
  classical
  let S := (Finset.Ioc x (2 * x)).filter (fun n => n ∈ C)
  let P := (Finset.Icc 1 (2 * x)).filter (fun n => n ∈ C)
  have hterm : ∀ n ∈ S, (1 / 8 : ℝ) ≤
      nearestIntegerDistance (δ * (n : ℝ)) := by
    intro n hn
    have hn' := Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1
    have hlo : 1 / 8 ≤ δ * (n : ℝ) := by
      have hxn : (x : ℝ) ≤ n := by exact_mod_cast hn'.1.le
      nlinarith [hxlo]
    have hhi : δ * (n : ℝ) ≤ 1 / 2 := by
      have hn2 : (n : ℝ) ≤ 2 * x := by exact_mod_cast hn'.2
      nlinarith [hxhi]
    rw [nd_eq_self_of_mem _ (by positivity) hhi]
    exact hlo
  have hSP : S ⊆ P := by
    intro n hn
    simp only [S, P, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc] at hn ⊢
    exact ⟨⟨by omega, hn.1.2⟩, hn.2⟩
  calc
    (shellCount C x : ℝ) / 8 = ∑ _n ∈ S, (1 / 8 : ℝ) := by
      simp [shellCount, S]
      ring
    _ ≤ ∑ n ∈ S, nearestIntegerDistance (δ * (n : ℝ)) := by
      exact Finset.sum_le_sum fun n hn => hterm n hn
    _ ≤ ∑ n ∈ P, nearestIntegerDistance (δ * (n : ℝ)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hSP
      intro n hnP hnS
      exact nd_nonneg _
    _ = phasePartialSum C δ (2 * x) := by
      simp only [phasePartialSum, P]

/-- Phases in `[0,1]` whose every partial sum is at most `k`. -/
def boundedPhases (C : Set ℕ) (k : ℕ) : Set ℝ :=
  {θ | θ ∈ Set.Icc (0 : ℝ) 1 ∧
    ∀ N, phasePartialSum C θ N ≤ (k : ℝ)}

lemma finite_of_totallyBounded_separated
    {s : Set ℝ} (htb : TotallyBounded s) {ε : ℝ} (hε : 0 < ε)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → ε ≤ |x - y|) :
    s.Finite := by
  obtain ⟨t, htfin, hcover⟩ := Metric.totallyBounded_iff.mp htb (ε / 2) (by positivity)
  classical
  have hex : ∀ x : s, ∃ y ∈ t, dist x.1 y < ε / 2 := by
    intro x
    have hx := hcover x.2
    simp only [Set.mem_iUnion, Metric.mem_ball] at hx
    obtain ⟨y, hy, hd⟩ := hx
    exact ⟨y, hy, hd⟩
  choose center hcenter_mem hcenter using hex
  let f : s → ℝ := fun x => center x
  have hf_range : Set.range f ⊆ t := by
    rintro y ⟨x, rfl⟩
    exact hcenter_mem x
  have hfrange_fin : (Set.range f).Finite := htfin.subset hf_range
  have hfinj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    by_contra hne
    have hsep' := hsep x.1 x.2 y.1 y.2 hne
    have hxd : dist x.1 (f x) < ε / 2 := hcenter x
    have hyd : dist y.1 (f y) < ε / 2 := hcenter y
    have : |x.1 - y.1| < ε := by
      rw [← Real.dist_eq]
      calc
        dist x.1 y.1 ≤ dist x.1 (f x) + dist (f x) y.1 := dist_triangle _ _ _
        _ = dist x.1 (f x) + dist (f y) y.1 := by rw [hxy]
        _ < ε := by
          have hyd' : dist (f y) y.1 < ε / 2 := by
            rwa [dist_comm]
          linarith
    linarith
  have : Set.Finite (Set.univ : Set s) := by
    apply Set.Finite.of_finite_image (f := f)
    · simpa only [Set.image_univ] using hfrange_fin
    · intro x hx y hy hxy
      exact hfinj hxy
  letI : Finite s := Set.finite_univ_iff.mp this
  exact Set.toFinite s

end

end LocalCassels.CountableConvergencePhases
end

section
namespace LocalCassels.PowerShellCountablePhases

open Filter
open LocalCassels
open LocalCassels.CountableConvergencePhases

noncomputable section

lemma boundedPhases_separated_of_powerShells
    {C : Set ℕ}
    (hpower : Tendsto (fun j : ℕ => shellCount C (2 ^ j)) atTop atTop)
    (k : ℕ) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ θ ∈ boundedPhases C k, ∀ φ ∈ boundedPhases C k,
        θ ≠ φ → ε ≤ |θ - φ| := by
  let M : ℕ := 16 * k + 1
  obtain ⟨J, hJ⟩ := eventually_atTop.1 (tendsto_atTop.1 hpower M)
  let ε : ℝ := min (1 / 8) (1 / (4 * (2 : ℝ) ^ J))
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  refine ⟨ε, hε, ?_⟩
  intro θ hθ φ hφ hne
  by_contra hnot
  have hdist : |θ - φ| < ε := lt_of_not_ge hnot
  let δ : ℝ := |θ - φ|
  have hδ : 0 < δ := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hδ8 : δ < 1 / 8 := hdist.trans_le (min_le_left _ _)
  have hδJ : δ < 1 / (4 * (2 : ℝ) ^ J) :=
    hdist.trans_le (min_le_right _ _)
  have hrone : 1 ≤ 1 / (4 * δ) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  obtain ⟨j, hjlo, hjhi⟩ := exists_nat_pow_near hrone
    (show (1 : ℝ) < 2 by norm_num)
  have hjJ : J ≤ j := by
    by_contra hnotj
    have hjlt : j < J := Nat.lt_of_not_ge hnotj
    have hp : (2 : ℝ) ^ (j + 1) ≤ (2 : ℝ) ^ J := by
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    have hlarge : (2 : ℝ) ^ J < 1 / (4 * δ) := by
      rw [lt_div_iff₀ (by positivity)]
      have hprod : δ * (4 * (2 : ℝ) ^ J) < 1 :=
        (lt_div_iff₀ (by positivity)).mp hδJ
      nlinarith
    linarith
  let x : ℕ := 2 ^ j
  have hxlo : 1 / 8 ≤ (x : ℝ) * δ := by
    have hstrict : 1 / (8 * δ) < (2 : ℝ) ^ j := by
      have hnear := hjhi
      rw [pow_succ] at hnear
      have heq : 1 / (4 * δ) = 2 * (1 / (8 * δ)) := by
        field_simp
        norm_num
      nlinarith
    change 1 / 8 ≤ ((2 ^ j : ℕ) : ℝ) * δ
    rw [Nat.cast_pow, Nat.cast_ofNat]
    calc
      1 / 8 = (1 / (8 * δ)) * δ := by field_simp
      _ ≤ ((2 : ℝ) ^ j) * δ :=
        mul_le_mul_of_nonneg_right hstrict.le hδ.le
  have hxhi : (x : ℝ) * δ ≤ 1 / 4 := by
    change ((2 ^ j : ℕ) : ℝ) * δ ≤ 1 / 4
    rw [Nat.cast_pow, Nat.cast_ofNat]
    have hmul := mul_le_mul_of_nonneg_right hjlo hδ.le
    calc
      ((2 : ℝ) ^ j) * δ ≤ (1 / (4 * δ)) * δ := hmul
      _ = 1 / 4 := by field_simp
  have hlower := shell_phase_lower C x δ hδ hxlo hxhi
  have hcard : M ≤ shellCount C x := by
    dsimp [x]
    exact hJ j hjJ
  have hlower' : (2 * k : ℝ) < phasePartialSum C δ (2 * x) := by
    calc
      (2 * k : ℝ) < (M : ℝ) / 8 := by
        dsimp [M]
        push_cast
        linarith
      _ ≤ (shellCount C x : ℝ) / 8 := by
        apply div_le_div_of_nonneg_right
        · exact_mod_cast hcard
        · norm_num
      _ ≤ phasePartialSum C δ (2 * x) := hlower
  have htri : phasePartialSum C δ (2 * x) ≤
      phasePartialSum C θ (2 * x) + phasePartialSum C φ (2 * x) := by
    classical
    simp only [phasePartialSum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro n hn
    rcases le_total φ θ with hφθ | hθφ
    · have hδeq : δ * (n : ℝ) = θ * (n : ℝ) - φ * (n : ℝ) := by
        dsimp [δ]
        rw [abs_of_nonneg (sub_nonneg.mpr hφθ)]
        ring
      rw [hδeq]
      exact nd_sub_le _ _
    · have hδeq : δ * (n : ℝ) = -(θ * (n : ℝ) - φ * (n : ℝ)) := by
        dsimp [δ]
        rw [abs_of_nonpos (sub_nonpos.mpr hθφ)]
        ring
      rw [hδeq, nd_neg]
      exact nd_sub_le _ _
  have hupp : phasePartialSum C θ (2 * x) +
      phasePartialSum C φ (2 * x) ≤ 2 * k := by
    linarith [hθ.2 (2 * x), hφ.2 (2 * x)]
  linarith

/-- Power-of-two shell multiplicity already suffices for countability of the
nearest-integer convergence-phase set. -/
theorem countable_bounded_phase_set_of_powerShells
    {C : Set ℕ}
    (hpower : Tendsto (fun j : ℕ => shellCount C (2 ^ j)) atTop atTop) :
    {θ : ℝ | θ ∈ Set.Icc (0 : ℝ) 1 ∧
      ∃ B : ℝ, ∀ N, phasePartialSum C θ N ≤ B}.Countable := by
  have hfinite : ∀ k : ℕ, (boundedPhases C k).Finite := by
    intro k
    obtain ⟨ε, hε, hsep⟩ := boundedPhases_separated_of_powerShells hpower k
    apply finite_of_totallyBounded_separated
      ((totallyBounded_Icc (0 : ℝ) 1).subset (fun θ hθ => hθ.1)) hε hsep
  refine (Set.countable_iUnion fun k => (hfinite k).countable).mono ?_
  rintro θ ⟨hθI, B, hB⟩
  obtain ⟨k, hk⟩ := exists_nat_ge B
  refine Set.mem_iUnion.mpr ⟨k, hθI, ?_⟩
  intro N
  exact (hB N).trans (by exact_mod_cast hk)

end

end LocalCassels.PowerShellCountablePhases
end

section
namespace LocalCassels.UniversalCorrectionPartition

open Filter
open scoped BigOperators
open LocalCassels
open LocalCassels.GrowthPartition
open LocalCassels.PhaseShellDecomposition
open LocalCassels.CanonicalCountableReserve
open LocalCassels.ReserveGrowth
open LocalCassels.ReserveComplementPhase
open LocalCassels.CountableConvergencePhases
open LocalCassels.PowerShellCountablePhases

noncomputable section

/-- A fixed quarter of each power shell, selected by increasing rank. -/
def seedCorrection (A : Set ℕ) : Set ℕ := colorClass A 0

/-- Everything outside the seed correction class. -/
def seedReserve (A : Set ℕ) : Set ℕ := A \ seedCorrection A

lemma powerShell_colorClass (A : Set ℕ) (j c : ℕ) (_hc : c < 4) :
    powerShell (colorClass A c) j = balancedPart (powerShell A j) c := by
  classical
  ext n
  constructor
  · intro hn
    have hndata := Finset.mem_filter.mp hn
    obtain ⟨l, hnl⟩ := hndata.2
    have hnAl := balancedPart_subset (powerShell A l) c hnl
    have hnAj : n ∈ powerShell A j := by
      exact Finset.mem_filter.mpr ⟨hndata.1, (Finset.mem_filter.mp hnAl).2⟩
    have hjl : j = l := powerShell_index_unique A hnAj hnAl
    simpa [hjl] using hnl
  · intro hn
    have hnA := balancedPart_subset (powerShell A j) c hn
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hnA).1, ⟨j, hn⟩⟩

lemma shellCount_power_eq_powerShell_card (C : Set ℕ) (j : ℕ) :
    LocalCassels.shellCount C (2 ^ j) = (powerShell C j).card := by
  simp [LocalCassels.shellCount, powerShell, pow_succ, mul_comm]

lemma colorClass_powerShell_card_tendsto
    (A : Set ℕ) (c : ℕ) (hc : c < 4)
    (hdyadic : Tendsto (LocalCassels.dyadicIncrement A) atTop atTop) :
    Tendsto (fun j => (powerShell (colorClass A c) j).card) atTop atTop := by
  classical
  rw [tendsto_atTop]
  intro K
  have hmuch := LocalCassels.dyadic_tendsto_eventually_many A hdyadic (4 * K)
  have hpowers :=
    (tendsto_pow_atTop_atTop_of_one_lt (r := (2 : ℕ)) (by decide)).eventually hmuch
  filter_upwards [hpowers] with j hj
  rw [powerShell_colorClass A j c hc]
  apply balancedPart_card_ge (powerShell A j) c K hc
  simpa [shellCount_power_eq_powerShell_card] using hj

lemma seedCorrection_powerShell_card_tendsto
    (A : Set ℕ)
    (hdyadic : Tendsto (LocalCassels.dyadicIncrement A) atTop atTop) :
    Tendsto (fun j => (powerShell (seedCorrection A) j).card) atTop atTop :=
  colorClass_powerShell_card_tendsto A 0 (by omega) hdyadic

lemma color_one_subset_seedReserve (A : Set ℕ) :
    colorClass A 1 ⊆ seedReserve A := by
  classical
  intro n hn1
  have hnA : n ∈ A := by
    obtain ⟨j, hnj⟩ := hn1
    exact (Finset.mem_filter.mp
      (balancedPart_subset (powerShell A j) 1 hnj)).2
  refine ⟨hnA, ?_⟩
  intro hn0
  exact Set.disjoint_left.mp (colorClass_pairwise_disjoint A (by omega)) hn0 hn1

lemma seedReserve_powerShell_card_tendsto
    (A : Set ℕ)
    (hdyadic : Tendsto (LocalCassels.dyadicIncrement A) atTop atTop) :
    Tendsto (fun j => (powerShell (seedReserve A) j).card) atTop atTop := by
  classical
  have h1 := colorClass_powerShell_card_tendsto A 1 (by omega) hdyadic
  rw [tendsto_atTop] at h1 ⊢
  intro K
  filter_upwards [h1 K] with j hj
  apply hj.trans
  apply Finset.card_le_card
  intro n hn
  have hn1 : n ∈ colorClass A 1 :=
    (Finset.mem_filter.mp hn).2
  have hnR := color_one_subset_seedReserve A hn1
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hn).1, hnR⟩

lemma seedCorrection_canonical_power_tendsto
    (A : Set ℕ)
    (hdyadic : Tendsto (LocalCassels.dyadicIncrement A) atTop atTop) :
    Tendsto (fun j => LocalCassels.shellCount (seedCorrection A) (2 ^ j))
      atTop atTop := by
  simpa only [shellCount_power_eq_powerShell_card] using
    seedCorrection_powerShell_card_tendsto A hdyadic

lemma phasePartialSum_split (A C : Set ℕ) (hCA : C ⊆ A)
    (θ : ℝ) (N : ℕ) :
    phasePartialSum A θ N =
      phasePartialSum C θ N + phasePartialSum (A \ C) θ N := by
  classical
  let I := Finset.Icc 1 N
  let f : ℕ → ℝ := fun n => nearestIntegerDistance (θ * (n : ℝ))
  have hpart := Finset.sum_filter_add_sum_filter_not
    (I.filter fun n => n ∈ A) (fun n => n ∈ C) f
  have hleft : ((I.filter fun n => n ∈ A).filter fun n => n ∈ C) =
      I.filter (fun n => n ∈ C) := by
    ext n
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hnI, hnA⟩, hnC⟩
      exact ⟨hnI, hnC⟩
    · rintro ⟨hnI, hnC⟩
      exact ⟨⟨hnI, hCA hnC⟩, hnC⟩
  have hright : ((I.filter fun n => n ∈ A).filter fun n => n ∉ C) =
      I.filter (fun n => n ∈ A \ C) := by
    ext n
    simp only [Finset.mem_filter, Set.mem_sdiff]
    tauto
  rw [hleft, hright] at hpart
  simpa [phasePartialSum, I, f] using hpart.symm

lemma phase_diverges_on_seedReserve_of_seed_bounded
    (A : Set ℕ) (θ : ℝ)
    (hA : Tendsto (phasePartialSum A θ) atTop atTop)
    (hbound : ∃ B : ℝ, ∀ N,
      phasePartialSum (seedCorrection A) θ N ≤ B) :
    Tendsto (phasePartialSum (seedReserve A) θ) atTop atTop := by
  classical
  obtain ⟨B, hB⟩ := hbound
  rw [tendsto_atTop]
  intro b
  have hlarge := tendsto_atTop.1 hA (b + B)
  filter_upwards [hlarge] with N hN
  have hsplit := phasePartialSum_split A (seedCorrection A)
    (fun n hn => by
      obtain ⟨j, hnj⟩ := hn
      exact (Finset.mem_filter.mp
        (balancedPart_subset (powerShell A j) 0 hnj)).2) θ N
  dsimp [seedReserve]
  linarith [hB N]

lemma phasePartialSum_mono_set {C D : Set ℕ} (hCD : C ⊆ D)
    (θ : ℝ) (N : ℕ) :
    phasePartialSum C θ N ≤ phasePartialSum D θ N := by
  classical
  simp only [phasePartialSum]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    simp only [Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, hCD hn.2⟩
  · intro n hnD hnC
    exact nd_nonneg _

lemma phase_divergence_mono_set {C D : Set ℕ} (hCD : C ⊆ D)
    (θ : ℝ) (hC : Tendsto (phasePartialSum C θ) atTop atTop) :
    Tendsto (phasePartialSum D θ) atTop atTop := by
  rw [tendsto_atTop] at hC ⊢
  intro b
  filter_upwards [hC b] with N hN
  exact hN.trans (phasePartialSum_mono_set hCD θ N)

/-- Core extraction theorem: the original hypotheses yield a growing
power-shell reserve whose actual complement retains phase divergence at every
nonzero phase, not merely at a prescribed list. -/
theorem exists_universally_phase_protected_growing_reserve
    (A : Set ℕ)
    (hdyadic : Tendsto (LocalCassels.dyadicIncrement A) atTop atTop)
    (hphase : ∀ θ : ℝ, θ ∈ Set.Ioo 0 1 →
      Tendsto (phasePartialSum A θ) atTop atTop) :
    ∃ R : ℕ → Finset ℕ,
      (∀ j, R j ⊆ powerShell (seedReserve A) j) ∧
      Tendsto (fun j => (R j).card) atTop atTop ∧
      (∀ θ : ℝ, θ ∈ Set.Ioo 0 1 →
        Tendsto (phasePartialSum (A \ reserveSet R) θ) atTop atTop) ∧
      (∃ K : ℕ, ∀ n : ℕ, ∃ t : Finset ℕ,
        (∀ b ∈ t, b ∈ reserveSet R) ∧
        (∑ b ∈ t, b) ≤ n ∧ n ≤ (∑ b ∈ t, b) + K) := by
  classical
  let C₀ := seedCorrection A
  let B₀ := seedReserve A
  let H : Set ℝ := {θ | θ ∈ Set.Ioo (0 : ℝ) 1 ∧
    ∃ B : ℝ, ∀ N, phasePartialSum C₀ θ N ≤ B}
  have hHcount : H.Countable := by
    refine (countable_bounded_phase_set_of_powerShells
      (seedCorrection_canonical_power_tendsto A hdyadic)).mono ?_
    intro θ hθ
    exact ⟨⟨hθ.1.1.le, hθ.1.2.le⟩, hθ.2⟩
  have hBcard : Tendsto (fun j => (powerShell B₀ j).card) atTop atTop :=
    seedReserve_powerShell_card_tendsto A hdyadic
  by_cases hHne : H.Nonempty
  · obtain ⟨θseq, hθrange⟩ := hHcount.exists_eq_range hHne
    have hθmem : ∀ i, θseq i ∈ H := by
      intro i
      rw [hθrange]
      exact ⟨i, rfl⟩
    let w : ℕ → ℕ → ℝ := fun i n =>
      nearestIntegerDistance (θseq i * (n : ℝ))
    have hw : ∀ i j n, n ∈ powerShell B₀ j → 0 ≤ w i n := by
      intro i j n hn
      exact nd_nonneg _
    have hBphase : ∀ i, Tendsto (phasePartialSum B₀ (θseq i)) atTop atTop := by
      intro i
      exact phase_diverges_on_seedReserve_of_seed_bounded A (θseq i)
        (hphase (θseq i) (hθmem i).1)
        (hθmem i).2
    have hdiv : ∀ i, Tendsto
        (fun N => ∑ j ∈ Finset.range N,
          ∑ n ∈ powerShell B₀ j, w i n) atTop atTop := by
      intro i
      exact phase_divergence_implies_powerShell_divergence B₀ (θseq i)
        (hBphase i)
    obtain ⟨R, hRsub, hRcard, hRkeep, hRsynd⟩ :=
      exists_eventual_syndetic_reserve_preserving_countable_divergence
        B₀ w hw hBcard hdiv
    refine ⟨R, hRsub, hRcard, ?_, hRsynd⟩
    intro θ hθ
    by_cases hθH : θ ∈ H
    · rw [hθrange] at hθH
      obtain ⟨i, hi⟩ := hθH
      subst θ
      obtain ⟨J, hrem⟩ := hRkeep i
      have hBcomp := complement_phase_diverges_of_shell_remainder
        B₀ R hRsub (θseq i) J hrem
      apply phase_divergence_mono_set (C := B₀ \ reserveSet R)
        (D := A \ reserveSet R) _ (θseq i) hBcomp
      intro n hn
      exact ⟨hn.1.1, hn.2⟩
    · have hCdiv : Tendsto (phasePartialSum C₀ θ) atTop atTop := by
        rw [phasePartialSum_tendsto_iff_unbounded]
        intro b
        by_contra hno
        have hbnd : ∀ N, phasePartialSum C₀ θ N ≤ b := by
          intro N
          exact le_of_not_ge fun hb => hno ⟨N, hb⟩
        exact hθH ⟨hθ, b, hbnd⟩
      apply phase_divergence_mono_set (C := C₀)
        (D := A \ reserveSet R) _ θ hCdiv
      intro n hnC
      refine ⟨?_, ?_⟩
      · obtain ⟨j, hnj⟩ := hnC
        exact (Finset.mem_filter.mp
          (balancedPart_subset (powerShell A j) 0 hnj)).2
      · rintro ⟨j, hnR⟩
        have hnB : n ∈ B₀ := (Finset.mem_filter.mp (hRsub j hnR)).2
        exact hnB.2 hnC
  · have hCall : ∀ θ, θ ∈ Set.Ioo (0 : ℝ) 1 →
        Tendsto (phasePartialSum C₀ θ) atTop atTop := by
      intro θ hθ
      rw [phasePartialSum_tendsto_iff_unbounded]
      intro b
      by_contra hno
      have hbnd : ∀ N, phasePartialSum C₀ θ N ≤ b := by
        intro N
        exact le_of_not_ge fun hb => hno ⟨N, hb⟩
      exact hHne ⟨θ, hθ, b, hbnd⟩
    let w : ℕ → ℕ → ℝ := fun _ _ => 1
    have hw : ∀ i j n, n ∈ powerShell B₀ j → 0 ≤ w i n := by
      intro i j n hn
      simp [w]
    have hdiv : ∀ i, Tendsto
        (fun N => ∑ j ∈ Finset.range N,
          ∑ n ∈ powerShell B₀ j, w i n) atTop atTop := by
      intro i
      rw [tendsto_atTop]
      intro b
      obtain ⟨J, hJ⟩ := eventually_atTop.1
        (tendsto_atTop.1 hBcard (Nat.ceil (max b 0)))
      filter_upwards [eventually_ge_atTop (J + 1)] with N hN
      have hcardN : Nat.ceil (max b 0) ≤ (powerShell B₀ (N - 1)).card :=
        hJ (N - 1) (by omega)
      have hlast : N - 1 ∈ Finset.range N := Finset.mem_range.mpr (by omega)
      calc
        b ≤ (Nat.ceil (max b 0) : ℝ) := by
          exact (le_max_left b 0).trans (Nat.le_ceil _)
        _ ≤ ((powerShell B₀ (N - 1)).card : ℝ) := by exact_mod_cast hcardN
        _ = ∑ n ∈ powerShell B₀ (N - 1), w i n := by simp [w]
        _ ≤ ∑ j ∈ Finset.range N, ∑ n ∈ powerShell B₀ j, w i n := by
          exact Finset.single_le_sum
            (fun j hj => Finset.sum_nonneg (fun n hn => by simp [w])) hlast
    obtain ⟨R, hRsub, hRcard, hRkeep, hRsynd⟩ :=
      exists_eventual_syndetic_reserve_preserving_countable_divergence
        B₀ w hw hBcard hdiv
    refine ⟨R, hRsub, hRcard, ?_, hRsynd⟩
    intro θ hθ
    apply phase_divergence_mono_set (C := C₀)
      (D := A \ reserveSet R) _ θ (hCall θ hθ)
    intro n hnC
    refine ⟨?_, ?_⟩
    · obtain ⟨j, hnj⟩ := hnC
      exact (Finset.mem_filter.mp
        (balancedPart_subset (powerShell A j) 0 hnj)).2
    · rintro ⟨j, hnR⟩
      have hnB : n ∈ B₀ := (Finset.mem_filter.mp (hRsub j hnR)).2
      exact hnB.2 hnC

end

end LocalCassels.UniversalCorrectionPartition
end

section
namespace LocalCassels.DisjointCriterionDecomposition

open Filter
open scoped BigOperators
open LocalCassels
open LocalCassels.GrowthPartition LocalCassels.InfiniteCoinCover
open LocalCassels.FourSyndeticClasses LocalCassels.ReserveGrowth
open LocalCassels.UniversalCorrectionPartition

noncomputable section

lemma powerShell_reserveSet_eq
    {A : Set ℕ} {R : ℕ → Finset ℕ}
    (hsub : ∀ j, R j ⊆ powerShell A j) (j : ℕ) :
    powerShell (reserveSet R) j = R j := by
  classical
  ext n
  constructor
  · intro hn
    have hnD := (Finset.mem_filter.mp hn).2
    obtain ⟨k, hnk⟩ := hnD
    have hnkA := hsub k hnk
    have hnjA : n ∈ powerShell A j := by
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hn).1,
        (Finset.mem_filter.mp hnkA).2⟩
    have hjk := powerShell_index_unique A hnjA hnkA
    simpa [hjk] using hnk
  · intro hn
    have hnA := hsub j hn
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hnA).1, ⟨j, hn⟩⟩

lemma reserveSet_subset
    {A : Set ℕ} {R : ℕ → Finset ℕ}
    (hsub : ∀ j, R j ⊆ powerShell A j) :
    reserveSet R ⊆ A := by
  classical
  intro n hn
  obtain ⟨j, hnj⟩ := hn
  exact (Finset.mem_filter.mp (hsub j hnj)).2

/-- Exact Bergelson--Simmons-style disjoint decomposition: three disjoint
classes have syndetic distinct subset sums, while the disjoint remainder
retains every phase divergence. -/
theorem exists_three_syndetic_classes_and_universal_correction
    (A : Set ℕ)
    (hdyadic : Tendsto (LocalCassels.dyadicIncrement A) atTop atTop)
    (hphase : ∀ θ : ℝ, θ ∈ Set.Ioo 0 1 →
      Tendsto (phasePartialSum A θ) atTop atTop) :
    ∃ B : Fin 3 → Set ℕ, ∃ C : Set ℕ,
      (∀ i, B i ⊆ A) ∧ C ⊆ A ∧
      Pairwise (fun i j => Disjoint (B i) (B j)) ∧
      (∀ i, Disjoint (B i) C) ∧
      (A = C ∪ ⋃ i, B i) ∧
      (∀ i, ∃ K : ℕ, ∀ n : ℕ, ∃ t : Finset ℕ,
        (∀ b ∈ t, b ∈ B i) ∧
        (∑ b ∈ t, b) ≤ n ∧ n ≤ (∑ b ∈ t, b) + K) ∧
      (∀ θ : ℝ, θ ∈ Set.Ioo 0 1 →
        Tendsto (phasePartialSum C θ) atTop atTop) := by
  classical
  obtain ⟨R, hRsubSeed, hRcard, hCbasePhase, hRsynd⟩ :=
    exists_universally_phase_protected_growing_reserve A hdyadic hphase
  have hSeedA : seedReserve A ⊆ A := fun n hn => hn.1
  have hRsubA : ∀ j, R j ⊆ powerShell A j := by
    intro j n hn
    have hnSeed := hRsubSeed j hn
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hnSeed).1,
      hSeedA (Finset.mem_filter.mp hnSeed).2⟩
  let D : Set ℕ := reserveSet R
  have hDA : D ⊆ A := reserveSet_subset hRsubA
  have hDcard : Tendsto (fun j => (powerShell D j).card) atTop atTop := by
    simpa only [D, powerShell_reserveSet_eq hRsubA] using hRcard
  have hshell : ∀ᶠ j : ℕ in atTop, 16 ≤ (powerShell D j).card :=
    tendsto_atTop.1 hDcard 16
  let B : Fin 3 → Set ℕ := fun i => colorClass D i.val
  let U : Set ℕ := ⋃ i, B i
  let C : Set ℕ := A \ U
  have hBiD : ∀ i, B i ⊆ D := by
    intro i n hn
    obtain ⟨j, hnj⟩ := hn
    exact (Finset.mem_filter.mp
      (balancedPart_subset (powerShell D j) i.val hnj)).2
  have hBiA : ∀ i, B i ⊆ A := fun i => (hBiD i).trans hDA
  have hpair : Pairwise (fun i j => Disjoint (B i) (B j)) := by
    intro i j hij
    apply colorClass_pairwise_disjoint D
    intro hv
    apply hij
    exact Fin.ext hv
  have hdisC : ∀ i, Disjoint (B i) C := by
    intro i
    rw [Set.disjoint_left]
    intro n hnB hnC
    exact hnC.2 (Set.mem_iUnion.mpr ⟨i, hnB⟩)
  have hcover : A = C ∪ U := by
    apply Set.Subset.antisymm
    · intro n hnA
      by_cases hnU : n ∈ U
      · exact Or.inr hnU
      · exact Or.inl ⟨hnA, hnU⟩
    · intro n hn
      rcases hn with hnC | hnU
      · exact hnC.1
      · obtain ⟨i, hnBi⟩ := Set.mem_iUnion.mp hnU
        exact hBiA i hnBi
  have hsynd : ∀ i, ∃ K : ℕ, ∀ n : ℕ, ∃ t : Finset ℕ,
      (∀ b ∈ t, b ∈ B i) ∧
      (∑ b ∈ t, b) ≤ n ∧ n ≤ (∑ b ∈ t, b) + K := by
    intro i
    obtain ⟨N₀, hgrowth⟩ :=
      colorClass_eventual_growth D i.val (by omega) hshell
    refine ⟨N₀, ?_⟩
    apply infinite_prefix_growth_gives_syndetic_subsetSums
    · exact colorClass_infinite D i.val (by omega) hshell
    · intro b hbB hb1
      by_cases hbN : N₀ ≤ b
      · rw [smallerCoins_colorClass_eq_prefixFinset]
        exact (hgrowth b hbN hbB).trans (Nat.le_add_right _ _)
      · exact (Nat.le_of_lt (Nat.lt_of_not_ge hbN)).trans
          (Nat.le_add_left N₀ _)
  have hbaseSub : A \ D ⊆ C := by
    intro n hn
    refine ⟨hn.1, ?_⟩
    intro hnU
    obtain ⟨i, hnBi⟩ := Set.mem_iUnion.mp hnU
    exact hn.2 (hBiD i hnBi)
  have hCphase : ∀ θ : ℝ, θ ∈ Set.Ioo 0 1 →
      Tendsto (phasePartialSum C θ) atTop atTop := by
    intro θ hθ
    exact phase_divergence_mono_set hbaseSub θ (hCbasePhase θ hθ)
  refine ⟨B, C, hBiA, ?_, hpair, hdisC, ?_, hsynd, hCphase⟩
  · intro n hn
    exact hn.1
  · simpa only [U] using hcover

end

end LocalCassels.DisjointCriterionDecomposition
end

section
namespace LocalCassels.TailSemigroup

open scoped BigOperators Topology

noncomputable section

/-- Finite sums of distinct eligible terms, all beyond a cutoff. -/
def tailSubsetSums {G : Type*} [AddCommMonoid G]
    (A : Set ℕ) (x : ℕ → G) (N : ℕ) : Set G :=
  {g | ∃ s : Finset ℕ,
    (∀ n ∈ s, n ∈ A ∧ N ≤ n) ∧ (∑ n ∈ s, x n) = g}

/-- Points approximable by distinct subset sums beyond every cutoff. -/
def tailLimit {G : Type*} [TopologicalSpace G] [AddCommMonoid G]
    (A : Set ℕ) (x : ℕ → G) : Set G :=
  ⋂ N : ℕ, closure (tailSubsetSums A x N)

lemma tailLimit_isClosed {G : Type*} [TopologicalSpace G] [AddCommMonoid G]
    (A : Set ℕ) (x : ℕ → G) : IsClosed (tailLimit A x) := by
  exact isClosed_iInter (fun N => isClosed_closure)

lemma zero_mem_tailLimit {G : Type*} [TopologicalSpace G] [AddCommMonoid G]
    (A : Set ℕ) (x : ℕ → G) : 0 ∈ tailLimit A x := by
  rw [tailLimit, Set.mem_iInter]
  intro N
  apply subset_closure
  exact ⟨∅, by simp, by simp⟩

/-- In a translation-invariant metric additive group, the tail-limit set is
closed under addition. Distinctness is preserved by putting the second
approximating finset strictly beyond the first. -/
lemma tailLimit_add_mem {G : Type*} [PseudoMetricSpace G] [AddCommGroup G]
    [IsIsometricVAdd G G]
    (A : Set ℕ) (x : ℕ → G) {u v : G}
    (hu : u ∈ tailLimit A x) (hv : v ∈ tailLimit A x) :
    u + v ∈ tailLimit A x := by
  rw [tailLimit, Set.mem_iInter] at hu hv ⊢
  intro N
  rw [Metric.mem_closure_iff]
  intro ε hε
  have huN := hu N
  rw [Metric.mem_closure_iff] at huN
  obtain ⟨a, ha, hua⟩ := huN (ε / 2) (by positivity)
  obtain ⟨s, hs, hsa⟩ := ha
  let K := max N (s.sup (fun k : ℕ => k) + 1)
  have hvK := hv K
  rw [Metric.mem_closure_iff] at hvK
  obtain ⟨b, hb, hvb⟩ := hvK (ε / 2) (by positivity)
  obtain ⟨t, ht, htb⟩ := hb
  have hdisj : Disjoint s t := by
    rw [Finset.disjoint_left]
    intro n hns hnt
    have hnle : n ≤ s.sup (fun k : ℕ => k) :=
      Finset.le_sup (f := fun k : ℕ => k) hns
    have hnK : n < K := by
      dsimp [K]
      omega
    have hKn : K ≤ n := (ht n hnt).2
    omega
  refine ⟨∑ n ∈ s ∪ t, x n, ?_, ?_⟩
  · refine ⟨s ∪ t, ?_, rfl⟩
    intro n hn
    rw [Finset.mem_union] at hn
    rcases hn with hns | hnt
    · exact hs n hns
    · exact ⟨(ht n hnt).1,
        le_trans (le_max_left N (s.sup (fun k : ℕ => k) + 1)) (ht n hnt).2⟩
  · rw [Finset.sum_union hdisj, hsa, htb]
    calc
      dist (u + v) (a + b) ≤ dist (u + v) (a + v) + dist (a + v) (a + b) :=
        dist_triangle _ _ _
      _ = dist u a + dist v b := by
        rw [dist_add_right, dist_add_left]
      _ < ε := by linarith

lemma tailSubsetSums_mono_cutoff {G : Type*} [AddCommMonoid G]
    (A : Set ℕ) (x : ℕ → G) {N M : ℕ} (hNM : N ≤ M) :
    tailSubsetSums A x M ⊆ tailSubsetSums A x N := by
  rintro g ⟨s, hs, rfl⟩
  exact ⟨s, fun n hn => ⟨(hs n hn).1, hNM.trans (hs n hn).2⟩, rfl⟩

/-- If a closed target set meets the actual subset sums beyond every cutoff,
then it meets their common tail-limit set. -/
theorem tailLimit_meets_closed {G : Type*} [TopologicalSpace G]
    [AddCommMonoid G] [CompactSpace G] [T2Space G]
    (A : Set ℕ) (x : ℕ → G) (E : Set G) (hE : IsClosed E)
    (hmeet : ∀ N, (tailSubsetSums A x N ∩ E).Nonempty) :
    (tailLimit A x ∩ E).Nonempty := by
  let K : ℕ → Set G := fun N => closure (tailSubsetSums A x N) ∩ E
  have hKn : ∀ N, (K N).Nonempty := by
    intro N
    obtain ⟨g, hg, hgE⟩ := hmeet N
    exact ⟨g, subset_closure hg, hgE⟩
  have hKclosed : ∀ N, IsClosed (K N) := fun N => isClosed_closure.inter hE
  have hKcompact : ∀ N, IsCompact (K N) := fun N => (hKclosed N).isCompact
  have hKdir : Directed (fun X Y : Set G => X ⊇ Y) K := by
    intro N M
    refine ⟨max N M, ?_, ?_⟩
    · intro g hg
      exact ⟨closure_mono (tailSubsetSums_mono_cutoff A x (le_max_left N M)) hg.1, hg.2⟩
    · intro g hg
      exact ⟨closure_mono (tailSubsetSums_mono_cutoff A x (le_max_right N M)) hg.1, hg.2⟩
  obtain ⟨g, hg⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    K hKdir hKn hKcompact hKclosed
  refine ⟨g, ?_, ?_⟩
  · rw [tailLimit, Set.mem_iInter]
    intro N
    exact (Set.mem_iInter.mp hg N).1
  · exact (Set.mem_iInter.mp hg 0).2

end

end LocalCassels.TailSemigroup
end

section
namespace LocalCassels.CompactSemigroup

/-- A nonempty closed subset of a compact topological additive group which is
closed under addition is the carrier of an additive subgroup. -/
theorem compact_add_subsemigroup_is_addSubgroup
    {G : Type*} [AddCommGroup G] [TopologicalSpace G]
    [CompactSpace G] [T2Space G] [IsTopologicalAddGroup G]
    (S : Set G) (hne : S.Nonempty) (hclosed : IsClosed S)
    (hadd : ∀ x ∈ S, ∀ y ∈ S, x + y ∈ S) :
    ∃ H : AddSubgroup G, (H : Set G) = S := by
  obtain ⟨e, heS, he⟩ := exists_idempotent_in_compact_add_subsemigroup
    (fun r => continuous_id.add continuous_const) S hne hclosed.isCompact hadd
  have he0 : e = 0 := by
    apply add_left_cancel (a := e)
    simpa using he
  have hzero : (0 : G) ∈ S := he0 ▸ heS
  let M : AddSubmonoid G :=
    { carrier := S
      zero_mem' := hzero
      add_mem' := fun hx hy => hadd _ hx _ hy }
  have hneg : ∀ x ∈ S, -x ∈ S := by
    intro x hx
    have hxgen : x ∈ AddSubgroup.closure ({x} : Set G) :=
      AddSubgroup.subset_closure (Set.mem_singleton x)
    have hnxgen : -x ∈ AddSubgroup.closure ({x} : Set G) :=
      (AddSubgroup.closure ({x} : Set G)).neg_mem hxgen
    have hnxclGroup : -x ∈ closure (AddSubgroup.closure ({x} : Set G) : Set G) :=
      subset_closure hnxgen
    have hnxclMonoid : -x ∈ closure (AddSubmonoid.closure ({x} : Set G) : Set G) := by
      rw [closure_addSubmonoidClosure_eq_closure_addSubgroupClosure]
      exact hnxclGroup
    have hmono : (AddSubmonoid.closure ({x} : Set G) : Set G) ⊆ S := by
      intro y hy
      exact (AddSubmonoid.closure_le.mpr (by simpa [M] using hx) :
        AddSubmonoid.closure ({x} : Set G) ≤ M) hy
    exact (closure_minimal hmono hclosed) hnxclMonoid
  let H : AddSubgroup G :=
    { carrier := S
      zero_mem' := hzero
      add_mem' := fun hx hy => hadd _ hx _ hy
      neg_mem' := fun hx => hneg _ hx }
  exact ⟨H, rfl⟩

end LocalCassels.CompactSemigroup
end

section
namespace LocalCassels.TorusCharacterSeparation

open scoped Topology ComplexConjugate ENNReal
open Set MeasureTheory Algebra Submodule

noncomputable section

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable {d : Type*} [Fintype d]

lemma mFourier_add_point (k : d → ℤ) (x y : UnitAddTorus d) :
    UnitAddTorus.mFourier k (x + y) =
      UnitAddTorus.mFourier k x * UnitAddTorus.mFourier k y := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.add_apply]
  calc
    (∏ i, fourier (k i) (x i + y i)) =
        ∏ i, (fourier (k i) (x i) * fourier (k i) (y i)) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [fourier_apply, fourier_apply, fourier_apply, zsmul_add,
        AddCircle.toCircle_add]
      rfl
    _ = (∏ i, fourier (k i) (x i)) * ∏ i, fourier (k i) (y i) :=
      Finset.prod_mul_distrib

lemma integral_mFourier_subgroup_eq_zero (H : AddSubgroup (UnitAddTorus d))
    (μ : Measure H) [μ.IsAddLeftInvariant]
    (k : d → ℤ)
    (hk : ∃ a : H, UnitAddTorus.mFourier k a.1 ≠ 1) :
    ∫ h : H, UnitAddTorus.mFourier k h.1 ∂μ = 0 := by
  obtain ⟨a, ha⟩ := hk
  have htrans := integral_add_left_eq_self
    (μ := μ) (fun h : H => UnitAddTorus.mFourier k h.1) a
  have heq : UnitAddTorus.mFourier k a.1 *
      (∫ h : H, UnitAddTorus.mFourier k h.1 ∂μ) =
      ∫ h : H, UnitAddTorus.mFourier k h.1 ∂μ := by
    calc
      UnitAddTorus.mFourier k a.1 *
          (∫ h : H, UnitAddTorus.mFourier k h.1 ∂μ) =
          ∫ h : H, UnitAddTorus.mFourier k a.1 *
            UnitAddTorus.mFourier k h.1 ∂μ := by rw [integral_const_mul]
      _ = ∫ h : H, UnitAddTorus.mFourier k (a + h).1 ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with h
        exact (mFourier_add_point k a.1 h.1).symm
      _ = ∫ h : H, UnitAddTorus.mFourier k h.1 ∂μ := htrans
  have hmul : (UnitAddTorus.mFourier k a.1 - 1) *
      (∫ h : H, UnitAddTorus.mFourier k h.1 ∂μ) = 0 := by
    calc
      _ = UnitAddTorus.mFourier k a.1 *
          (∫ h : H, UnitAddTorus.mFourier k h.1 ∂μ) -
          ∫ h : H, UnitAddTorus.mFourier k h.1 ∂μ := by ring
      _ = 0 := by rw [heq, sub_self]
  exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr ha)

/-- A point outside a closed torus subgroup is separated from it by an integer
Fourier character. -/
theorem exists_character_separating_point (H : AddSubgroup (UnitAddTorus d))
    (hHclosed : IsClosed (H : Set (UnitAddTorus d)))
    {x : UnitAddTorus d} (hx : x ∉ H) :
    ∃ k : d → ℤ,
      (∀ h ∈ H, UnitAddTorus.mFourier k h = 1) ∧
      UnitAddTorus.mFourier k x ≠ 1 := by
  classical
  by_contra hnone
  have hforce : ∀ k : d → ℤ,
      (∀ h ∈ H, UnitAddTorus.mFourier k h = 1) →
      UnitAddTorus.mFourier k x = 1 := by
    intro k hk
    by_contra hkx
    exact hnone ⟨k, hk, hkx⟩
  letI : IsClosed (H : Set (UnitAddTorus d)) := hHclosed
  letI : CompactSpace H := isCompact_iff_compactSpace.mp hHclosed.isCompact
  let μ : Measure H := Measure.addHaar
  letI : μ.IsAddLeftInvariant := inferInstance
  letI : IsFiniteMeasure μ := inferInstance
  letI : NeZero μ := inferInstance
  let M : ℝ := μ.real Set.univ
  have hM : 0 < M := measureReal_univ_pos
  have hcharShift (k : d → ℤ) :
      (∫ h : H, UnitAddTorus.mFourier k (x + h.1) ∂μ) =
      UnitAddTorus.mFourier k x *
        ∫ h : H, UnitAddTorus.mFourier k h.1 ∂μ := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with h
    exact mFourier_add_point k x h.1
  have hcharEq (k : d → ℤ) :
      (∫ h : H, UnitAddTorus.mFourier k h.1 ∂μ) =
      ∫ h : H, UnitAddTorus.mFourier k (x + h.1) ∂μ := by
    by_cases htriv : ∀ h ∈ H, UnitAddTorus.mFourier k h = 1
    · have hkx := hforce k htriv
      rw [hcharShift, hkx, one_mul]
    · have hex : ∃ a : H, UnitAddTorus.mFourier k a.1 ≠ 1 := by
        push Not at htriv
        obtain ⟨a, haH, ha⟩ := htriv
        exact ⟨⟨a, haH⟩, ha⟩
      have hz := integral_mFourier_subgroup_eq_zero H μ k hex
      rw [hcharShift, hz, mul_zero]
  have hIntegrable0 (f : C(UnitAddTorus d, ℂ)) :
      Integrable (fun h : H => f h.1) μ := by
    refine Integrable.of_bound
      (f.continuous.comp continuous_subtype_val).aestronglyMeasurable ‖f‖ ?_
    filter_upwards [] with h
    exact f.norm_coe_le_norm h.1
  have hIntegrableX (f : C(UnitAddTorus d, ℂ)) :
      Integrable (fun h : H => f (x + h.1)) μ := by
    refine Integrable.of_bound
      (f.continuous.comp (continuous_const.add continuous_subtype_val)).aestronglyMeasurable
      ‖f‖ ?_
    filter_upwards [] with h
    exact f.norm_coe_le_norm (x + h.1)
  let P : C(UnitAddTorus d, ℂ) → Prop := fun f =>
    (∫ h : H, f h.1 ∂μ) = ∫ h : H, f (x + h.1) ∂μ
  have hspan : ∀ f ∈ span ℂ (Set.range UnitAddTorus.mFourier), P f := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
        obtain ⟨k, rfl⟩ := hf
        exact hcharEq k
    | zero => simp [P]
    | add f g hf hg hPf hPg =>
        dsimp [P] at hPf hPg ⊢
        rw [integral_add (hIntegrable0 f) (hIntegrable0 g),
          integral_add (hIntegrableX f) (hIntegrableX g), hPf, hPg]
    | smul c f hf hPf =>
        dsimp [P] at hPf ⊢
        rw [integral_const_mul, integral_const_mul, hPf]
  let gr : C(UnitAddTorus d, ℝ) :=
    ⟨fun y => Metric.infDist y (H : Set (UnitAddTorus d)),
      Metric.continuous_infDist_pt _⟩
  have hgr0 : ∀ h : H, gr h.1 = 0 := fun h => Metric.infDist_zero_of_mem h.2
  have hnotmem : ∀ h : H, x + h.1 ∉ H := by
    intro h hxh
    apply hx
    have := H.sub_mem hxh h.2
    simpa using this
  have hgrXpos : ∀ h : H, 0 < gr (x + h.1) := by
    intro h
    change 0 < Metric.infDist (x + h.1) (H : Set (UnitAddTorus d))
    exact (hHclosed.notMem_iff_infDist_pos ⟨0, H.zero_mem⟩).mp (hnotmem h)
  have hgrXInt : Integrable (fun h : H => gr (x + h.1)) μ := by
    refine Integrable.of_bound
      (gr.continuous.comp (continuous_const.add continuous_subtype_val)).aestronglyMeasurable
      ‖gr‖ ?_
    filter_upwards [] with h
    exact gr.norm_coe_le_norm (x + h.1)
  let c : ℝ := ∫ h : H, gr (x + h.1) ∂μ
  have hc : 0 < c := by
    dsimp [c]
    rw [integral_pos_iff_support_of_nonneg (fun h => (hgrXpos h).le) hgrXInt]
    have hsupp : Function.support (fun h : H => gr (x + h.1)) = Set.univ := by
      ext h
      simp only [Function.mem_support, Set.mem_univ, iff_true]
      exact (hgrXpos h).ne'
    rw [hsupp]
    exact Measure.measure_univ_pos.mpr (NeZero.ne μ)
  let fc : C(UnitAddTorus d, ℂ) :=
    ⟨fun y => (gr y : ℂ), Complex.continuous_ofReal.comp gr.continuous⟩
  have hfcl : fc ∈ closure
      ((span ℂ (Set.range UnitAddTorus.mFourier) :
        Submodule ℂ C(UnitAddTorus d, ℂ)) : Set C(UnitAddTorus d, ℂ)) := by
    change fc ∈ (span ℂ (Set.range UnitAddTorus.mFourier)).topologicalClosure
    rw [UnitAddTorus.span_mFourier_closure_eq_top]
    exact Submodule.mem_top
  rw [Metric.mem_closure_iff] at hfcl
  obtain ⟨p, hpSpan, hdist⟩ := hfcl (c / (4 * M)) (by positivity)
  have hpEq := hspan p hpSpan
  have hpoint : ∀ y, ‖p y - fc y‖ < c / (4 * M) := by
    intro y
    exact (ContinuousMap.norm_coe_le_norm (p - fc) y).trans_lt
      (by simpa [dist_eq_norm, norm_sub_rev] using hdist)
  have hbound0 : ‖∫ h : H, p h.1 ∂μ‖ ≤ c / 4 := by
    have hb := norm_integral_le_of_norm_le_const (μ := μ)
      (Filter.Eventually.of_forall fun h : H => (hpoint h.1).le)
    have hzero : (∫ h : H, fc h.1 ∂μ) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [] with h
      change (gr h.1 : ℂ) = 0
      rw [hgr0 h]
      norm_num
    calc
      ‖∫ h : H, p h.1 ∂μ‖ =
          ‖(∫ h : H, p h.1 ∂μ) - ∫ h : H, fc h.1 ∂μ‖ := by rw [hzero, sub_zero]
      _ = ‖∫ h : H, p h.1 - fc h.1 ∂μ‖ := by
        rw [integral_sub (hIntegrable0 p) (hIntegrable0 fc)]
      _ ≤ (c / (4 * M)) * M := hb
      _ = c / 4 := by field_simp
  have hfcXIntegral : (∫ h : H, fc (x + h.1) ∂μ) = (c : ℂ) := by
    have hmap := Complex.ofRealCLM.integral_comp_comm hgrXInt
    exact hmap
  have hboundX : ‖(∫ h : H, p (x + h.1) ∂μ) - (c : ℂ)‖ ≤ c / 4 := by
    rw [← hfcXIntegral, ← integral_sub (hIntegrableX p) (hIntegrableX fc)]
    have hb := norm_integral_le_of_norm_le_const (μ := μ)
      (Filter.Eventually.of_forall fun h : H => (hpoint (x + h.1)).le)
    calc
      ‖∫ h : H, p (x + h.1) - fc (x + h.1) ∂μ‖ ≤
          (c / (4 * M)) * M := hb
      _ = c / 4 := by field_simp
  have hc_le : c ≤ c / 2 := by
    have htri := norm_le_norm_add_norm_sub
      (∫ h : H, p h.1 ∂μ) (c : ℂ)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc, hpEq] at htri
    have hbound0' : ‖∫ h : H, p (x + h.1) ∂μ‖ ≤ c / 4 := by
      rw [← hpEq]
      exact hbound0
    linarith [hbound0', hboundX]
  linarith

end

end LocalCassels.TorusCharacterSeparation
end

section
namespace LocalCassels.PhaseEscape

open scoped BigOperators

/-- A representative of a real number modulo one in `[-1/2,1/2]`. -/
noncomputable def centeredFraction (x : ℝ) : ℝ :=
  if Int.fract x ≤ 1 / 2 then Int.fract x else Int.fract x - 1

lemma abs_centeredFraction (x : ℝ) :
    |centeredFraction x| = nearestIntegerDistance x := by
  rw [centeredFraction, nearestIntegerDistance]
  split_ifs with h
  · rw [abs_of_nonneg (Int.fract_nonneg x), min_eq_left (by linarith)]
  · have hhalf : 1 / 2 < Int.fract x := lt_of_not_ge h
    have hnonpos : Int.fract x - 1 ≤ 0 := (Int.fract_lt_one x).le |> sub_nonpos.mpr
    rw [abs_of_nonpos hnonpos, min_eq_right (by linarith)]
    ring

lemma centeredFraction_le_half (x : ℝ) : centeredFraction x ≤ 1 / 2 := by
  rw [centeredFraction]
  split_ifs with h
  · exact h
  · have := Int.fract_lt_one x
    linarith

lemma neg_centeredFraction_le_half (x : ℝ) : -centeredFraction x ≤ 1 / 2 := by
  rw [centeredFraction]
  split_ifs with h
  · have := Int.fract_nonneg x
    linarith
  · have hhalf : 1 / 2 < Int.fract x := lt_of_not_ge h
    linarith

/-- If bounded nonnegative weights have total at least `1/4`, some subfamily
has total between `1/4` and `3/4`. -/
lemma exists_subset_sum_quarter {α : Type*} [DecidableEq α]
    (s : Finset α) (w : α → ℝ)
    (hw0 : ∀ a ∈ s, 0 ≤ w a) (hw : ∀ a ∈ s, w a ≤ 1 / 2)
    (hs : 1 / 4 ≤ ∑ a ∈ s, w a) :
    ∃ t : Finset α, t ⊆ s ∧
      1 / 4 ≤ ∑ a ∈ t, w a ∧ ∑ a ∈ t, w a ≤ 3 / 4 := by
  classical
  induction s using Finset.induction with
  | empty =>
      exfalso
      norm_num at hs
  | @insert a s ha ih =>
      by_cases hrest : 1 / 4 ≤ ∑ x ∈ s, w x
      · obtain ⟨t, hts, hlo, hhi⟩ := ih
          (fun x hx => hw0 x (Finset.mem_insert_of_mem hx))
          (fun x hx => hw x (Finset.mem_insert_of_mem hx)) hrest
        exact ⟨t, hts.trans (Finset.subset_insert a s), hlo, hhi⟩
      · refine ⟨insert a s, Finset.Subset.rfl, ?_, ?_⟩
        · exact hs
        · rw [Finset.sum_insert ha]
          have ha' := hw a (Finset.mem_insert_self a s)
          linarith

/-- A finite family with total nearest-integer mass at least `1/2` contains a
subfamily whose sum of centered representatives stays a definite distance
from every integer. -/
theorem finite_phase_escape {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → ℝ)
    (hs : 1 / 2 ≤ ∑ a ∈ s, nearestIntegerDistance (f a)) :
    ∃ t : Finset α, t ⊆ s ∧
      ((1 / 4 ≤ ∑ a ∈ t, centeredFraction (f a) ∧
          ∑ a ∈ t, centeredFraction (f a) ≤ 3 / 4) ∨
       (-3 / 4 ≤ ∑ a ∈ t, centeredFraction (f a) ∧
          ∑ a ∈ t, centeredFraction (f a) ≤ -1 / 4)) := by
  classical
  let p := s.filter (fun a => 0 ≤ centeredFraction (f a))
  let m := s.filter (fun a => centeredFraction (f a) < 0)
  have hsplit : ∑ a ∈ s, nearestIntegerDistance (f a) =
      (∑ a ∈ p, centeredFraction (f a)) +
      (∑ a ∈ m, -centeredFraction (f a)) := by
    change (∑ a ∈ s, nearestIntegerDistance (f a)) =
      (∑ a ∈ s.filter (fun a => 0 ≤ centeredFraction (f a)), centeredFraction (f a)) +
      (∑ a ∈ s.filter (fun a => centeredFraction (f a) < 0), -centeredFraction (f a))
    rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    rw [← abs_centeredFraction]
    by_cases h : 0 ≤ centeredFraction (f a)
    · simp [h, not_lt_of_ge h, abs_of_nonneg h]
    · have hlt : centeredFraction (f a) < 0 := lt_of_not_ge h
      simp [h, hlt, abs_of_neg hlt]
  by_cases hp : 1 / 4 ≤ ∑ a ∈ p, centeredFraction (f a)
  · obtain ⟨t, htp, hlo, hhi⟩ := exists_subset_sum_quarter p
      (fun a => centeredFraction (f a))
      (by intro a ha; exact (Finset.mem_filter.mp ha).2)
      (by intro a ha; exact centeredFraction_le_half (f a)) hp
    exact ⟨t, htp.trans (Finset.filter_subset _ _), Or.inl ⟨hlo, hhi⟩⟩
  · have hm : 1 / 4 ≤ ∑ a ∈ m, -centeredFraction (f a) := by
      rw [hsplit] at hs
      linarith
    obtain ⟨t, htm, hlo, hhi⟩ := exists_subset_sum_quarter m
      (fun a => -centeredFraction (f a))
      (by intro a ha; exact (Finset.mem_filter.mp ha).2.le |> neg_nonneg.mpr)
      (by intro a ha; exact neg_centeredFraction_le_half (f a)) hm
    refine ⟨t, htm.trans (Finset.filter_subset _ _), Or.inr ?_⟩
    simp only [Finset.sum_neg_distrib] at hlo hhi
    constructor <;> linarith

/-- Divergence of a phase series produces a definite subset-sum escape using
members beyond every prescribed cutoff. -/
theorem tail_phase_escape (A : Set ℕ) (θ : ℝ)
    (hdiv : Filter.Tendsto (phasePartialSum A θ)
      (Filter.atTop : Filter ℕ) Filter.atTop)
    (N : ℕ) :
    ∃ s : Finset ℕ,
      (∀ n ∈ s, n ∈ A ∧ N ≤ n) ∧
      ((1 / 4 ≤ ∑ n ∈ s, centeredFraction (θ * (n : ℝ)) ∧
          ∑ n ∈ s, centeredFraction (θ * (n : ℝ)) ≤ 3 / 4) ∨
       (-3 / 4 ≤ ∑ n ∈ s, centeredFraction (θ * (n : ℝ)) ∧
          ∑ n ∈ s, centeredFraction (θ * (n : ℝ)) ≤ -1 / 4)) := by
  classical
  let P : ℕ → Finset ℕ := fun M =>
    (Finset.Icc 1 M).filter (fun n => n ∈ A)
  let base := phasePartialSum A θ (N - 1)
  have hev := Filter.tendsto_atTop.mp hdiv (base + 1 / 2)
  have hevN : ∀ᶠ M : ℕ in Filter.atTop,
      N ≤ M ∧ base + 1 / 2 ≤ phasePartialSum A θ M :=
    (Filter.eventually_ge_atTop N).and hev
  obtain ⟨M, hNM, hM⟩ := hevN.exists
  have hsub : P (N - 1) ⊆ P M := by
    intro n hn
    change n ∈ (Finset.Icc 1 (N - 1)).filter (fun n => n ∈ A) at hn
    change n ∈ (Finset.Icc 1 M).filter (fun n => n ∈ A)
    rw [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
    exact ⟨⟨hn.1.1, by omega⟩, hn.2⟩
  let s := P M \ P (N - 1)
  have hmass : 1 / 2 ≤
      ∑ n ∈ s, nearestIntegerDistance (θ * (n : ℝ)) := by
    have hdiff := Finset.sum_sdiff_eq_sub (f := fun n : ℕ =>
      nearestIntegerDistance (θ * (n : ℝ))) hsub
    change (∑ n ∈ P M \ P (N - 1),
      nearestIntegerDistance (θ * (n : ℝ))) = _ at hdiff
    have hPM : (∑ n ∈ P M, nearestIntegerDistance (θ * (n : ℝ))) =
        phasePartialSum A θ M := by rfl
    have hP0 : (∑ n ∈ P (N - 1), nearestIntegerDistance (θ * (n : ℝ))) =
        base := by rfl
    change 1 / 2 ≤ ∑ n ∈ P M \ P (N - 1),
      nearestIntegerDistance (θ * (n : ℝ))
    rw [hdiff, hPM, hP0]
    linarith
  obtain ⟨t, hts, ht⟩ := finite_phase_escape s
    (fun n => θ * (n : ℝ)) hmass
  refine ⟨t, ?_, ht⟩
  intro n hn
  have hns : n ∈ s := hts hn
  have hnM : n ∈ P M := (Finset.mem_sdiff.mp hns).1
  have hn0 : n ∉ P (N - 1) := (Finset.mem_sdiff.mp hns).2
  change n ∈ (Finset.Icc 1 M).filter (fun n => n ∈ A) at hnM
  rw [Finset.mem_filter, Finset.mem_Icc] at hnM
  have hnA := hnM.2
  refine ⟨hnA, ?_⟩
  by_contra hnot
  have hnle : n ≤ N - 1 := by omega
  apply hn0
  change n ∈ (Finset.Icc 1 (N - 1)).filter (fun n => n ∈ A)
  rw [Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨hnM.1.1, hnle⟩, hnA⟩

end LocalCassels.PhaseEscape
end

section
namespace LocalCassels.CircleEscape

open scoped BigOperators Topology
open LocalCassels.PhaseEscape LocalCassels.TailSemigroup

noncomputable section

private def realEscape : Set ℝ :=
  Set.Icc (1 / 4) (3 / 4) ∪ Set.Icc (-3 / 4) (-1 / 4)

private def circleEscape : Set UnitAddCircle :=
  ((fun z : ℝ => (z : UnitAddCircle)) '' realEscape)

private lemma realEscape_isCompact : IsCompact realEscape := by
  exact isCompact_Icc.union isCompact_Icc

private lemma circleEscape_isClosed : IsClosed circleEscape := by
  exact (realEscape_isCompact.image (AddCircle.continuous_mk' 1)).isClosed

private lemma zero_not_mem_circleEscape : (0 : UnitAddCircle) ∉ circleEscape := by
  rintro ⟨z, hz, hz0⟩
  have hcoe : (z : UnitAddCircle) = 0 := hz0
  obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hcoe
  have hkz : (k : ℝ) = z := by simpa using hk
  rcases hz with hz | hz
  · have hkpos : (0 : ℤ) < k := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 4) (hkz.symm ▸ hz.1))
    have hklt : k < (1 : ℤ) := by
      exact_mod_cast (lt_of_le_of_lt (hkz.symm ▸ hz.2) (by norm_num : (3 / 4 : ℝ) < 1))
    omega
  · have hkgt : (-1 : ℤ) < k := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : (-1 : ℝ) < -3 / 4) (hkz.symm ▸ hz.1))
    have hkneg : k < (0 : ℤ) := by
      exact_mod_cast (lt_of_le_of_lt (hkz.symm ▸ hz.2) (by norm_num : (-1 / 4 : ℝ) < 0))
    omega

private lemma coe_centeredFraction (x : ℝ) :
    (centeredFraction x : UnitAddCircle) = (x : UnitAddCircle) := by
  rw [centeredFraction]
  split_ifs
  · rw [← Int.fract_add_floor x]
    simp
  · rw [← Int.fract_add_floor x]
    simp

/-- If the phase series for `qθ` diverges, the common tail-subset-sum limit of
`θn mod 1` contains a point not killed by multiplication by `q`. -/
theorem tailLimit_has_nonzero_qsmul (A : Set ℕ) (θ : ℝ) (q : ℕ)
    (hdiv : Filter.Tendsto (phasePartialSum A ((q : ℝ) * θ))
      (Filter.atTop : Filter ℕ) Filter.atTop) :
    ∃ g ∈ tailLimit A (fun n => ((θ * (n : ℝ) : ℝ) : UnitAddCircle)),
      q • g ≠ 0 := by
  let x : ℕ → UnitAddCircle := fun n => (θ * (n : ℝ) : UnitAddCircle)
  let E : Set UnitAddCircle := (fun g => q • g) ⁻¹' circleEscape
  have hE : IsClosed E := circleEscape_isClosed.preimage (continuous_nsmul q)
  have hmeet : ∀ N, (tailSubsetSums A x N ∩ E).Nonempty := by
    intro N
    obtain ⟨s, hs, hphase⟩ := tail_phase_escape A ((q : ℝ) * θ) hdiv N
    let z := ∑ n ∈ s, centeredFraction (((q : ℝ) * θ) * (n : ℝ))
    have hz : z ∈ realEscape := by
      rcases hphase with hp | hm
      · exact Or.inl hp
      · exact Or.inr hm
    let g : UnitAddCircle := ∑ n ∈ s, x n
    refine ⟨g, ⟨s, hs, rfl⟩, ?_⟩
    change q • g ∈ circleEscape
    refine ⟨z, hz, ?_⟩
    let Q : ℝ →+ UnitAddCircle :=
      QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))
    have hg : g = Q (∑ n ∈ s, θ * (n : ℝ)) := by
      change (∑ n ∈ s, Q (θ * (n : ℝ))) = Q (∑ n ∈ s, θ * (n : ℝ))
      exact (map_sum Q (fun n : ℕ => θ * (n : ℝ)) s).symm
    have hzcoe : (z : UnitAddCircle) =
        Q (∑ n ∈ s, ((q : ℝ) * θ) * (n : ℝ)) := by
      change Q (∑ n ∈ s, centeredFraction (((q : ℝ) * θ) * (n : ℝ))) = _
      rw [map_sum]
      conv_rhs => rw [map_sum]
      apply Finset.sum_congr rfl
      intro n hn
      exact coe_centeredFraction _
    rw [hg, ← map_nsmul Q]
    change (z : UnitAddCircle) = Q (q • ∑ n ∈ s, θ * (n : ℝ))
    rw [hzcoe]
    congr 1
    simp only [nsmul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    ring
  obtain ⟨g, hg, hgE⟩ := tailLimit_meets_closed A x E hE hmeet
  refine ⟨g, hg, ?_⟩
  intro hqg
  exact zero_not_mem_circleEscape (hqg ▸ hgE)

end

end LocalCassels.CircleEscape
end

section
namespace LocalCassels.CircleDensity

open scoped Topology
open LocalCassels.CompactSemigroup LocalCassels.CircleEscape LocalCassels.TailSemigroup

noncomputable section

/-- If every positive integer multiple of a scalar phase has divergent L1
mass, then distinct subset sums from every tail are dense in the unit circle. -/
theorem tailLimit_eq_univ_of_all_multiples_diverge (A : Set ℕ) (θ : ℝ)
    (hdiv : ∀ q : ℕ, 0 < q →
      Filter.Tendsto (phasePartialSum A ((q : ℝ) * θ))
        (Filter.atTop : Filter ℕ) Filter.atTop) :
    tailLimit A (fun n => ((θ * (n : ℝ) : ℝ) : UnitAddCircle)) = Set.univ := by
  let x : ℕ → UnitAddCircle := fun n => (θ * (n : ℝ) : UnitAddCircle)
  let S := tailLimit A x
  have hSclosed : IsClosed S := tailLimit_isClosed A x
  have hSzero : (0 : UnitAddCircle) ∈ S := zero_mem_tailLimit A x
  have hSadd : ∀ u ∈ S, ∀ v ∈ S, u + v ∈ S := by
    intro u hu v hv
    exact tailLimit_add_mem A x hu hv
  obtain ⟨H, hH⟩ := compact_add_subsemigroup_is_addSubgroup S
    ⟨0, hSzero⟩ hSclosed hSadd
  have hHdense : Dense (H : Set UnitAddCircle) := by
    rw [AddCircle.dense_addSubgroup_iff_ne_zmultiples]
    intro a ha hHa
    let q := addOrderOf a
    have hq : 0 < q := Nat.pos_of_ne_zero ha
    obtain ⟨g, hgS, hqg⟩ := tailLimit_has_nonzero_qsmul A θ q (hdiv q hq)
    have hgH : g ∈ H := by
      change g ∈ (H : Set UnitAddCircle)
      rw [hH]
      exact hgS
    rw [hHa, AddSubgroup.mem_zmultiples_iff] at hgH
    obtain ⟨k, hkg⟩ := hgH
    apply hqg
    rw [← hkg]
    rw [← show ((q : ℤ) • (k • a)) = q • (k • a) by simp]
    rw [smul_smul, mul_comm, ← smul_smul]
    simp [q]
  have hHclosed : IsClosed (H : Set UnitAddCircle) := by
    rw [hH]
    exact hSclosed
  have hHuniv : (H : Set UnitAddCircle) = Set.univ := by
    rw [← hHclosed.closure_eq]
    exact (dense_iff_closure_eq.mp hHdense)
  change S = Set.univ
  exact hH.symm.trans hHuniv

end

end LocalCassels.CircleDensity
end

section
namespace LocalCassels.IrrationalDensity

open LocalCassels.CircleDensity LocalCassels.TailSemigroup

noncomputable section

lemma fract_mul_nat_eq (x : ℝ) (n : ℕ) :
    Int.fract (x * (n : ℝ)) = Int.fract (Int.fract x * (n : ℝ)) := by
  have hx : x * (n : ℝ) = Int.fract x * (n : ℝ) +
      ((Int.floor x * (n : ℤ) : ℤ) : ℝ) := by
    rw [Int.cast_mul, Int.cast_natCast]
    nlinarith [Int.fract_add_floor x]
  rw [hx, Int.fract_add_intCast]

lemma nearestIntegerDistance_mul_eq_fract_mul (x : ℝ) (n : ℕ) :
    nearestIntegerDistance (x * (n : ℝ)) =
      nearestIntegerDistance (Int.fract x * (n : ℝ)) := by
  unfold nearestIntegerDistance
  rw [fract_mul_nat_eq]

lemma phasePartialSum_eq_fract (A : Set ℕ) (x : ℝ) (N : ℕ) :
    phasePartialSum A x N = phasePartialSum A (Int.fract x) N := by
  classical
  unfold phasePartialSum
  apply Finset.sum_congr rfl
  intro n hn
  exact nearestIntegerDistance_mul_eq_fract_mul x n

/-- Under the canonical all-phase hypothesis, every irrational rotation has
full distinct-subset-sum tail limit on the unit circle. -/
theorem irrational_tailLimit_eq_univ (A : Set ℕ)
    (hphase : ∀ θ : ℝ, θ ∈ Set.Ioo 0 1 →
      Filter.Tendsto (phasePartialSum A θ)
        (Filter.atTop : Filter ℕ) Filter.atTop)
    (θ : ℝ) (hθ : Irrational θ) :
    tailLimit A (fun n => ((θ * (n : ℝ) : ℝ) : UnitAddCircle)) = Set.univ := by
  apply tailLimit_eq_univ_of_all_multiples_diverge A θ
  intro q hq
  let φ := Int.fract ((q : ℝ) * θ)
  have hqθ : Irrational ((q : ℝ) * θ) :=
    hθ.natCast_mul (Nat.ne_of_gt hq)
  have hφpos : 0 < φ := by
    change 0 < Int.fract ((q : ℝ) * θ)
    rw [Int.fract_pos]
    exact hqθ.ne_int _
  have hφlt : φ < 1 := Int.fract_lt_one _
  have hlim := hphase φ ⟨hφpos, hφlt⟩
  have heq : phasePartialSum A ((q : ℝ) * θ) = phasePartialSum A φ := by
    funext N
    exact phasePartialSum_eq_fract A ((q : ℝ) * θ) N
  rw [heq]
  exact hlim

end

end LocalCassels.IrrationalDensity
end

section
namespace LocalCassels.TailModularCoverage

noncomputable section

def residueFiber (A : Set ℕ) (q r : ℕ) : Set ℕ :=
  {n | n ∈ A ∧ n % q = r}

def recurringResidues (A : Set ℕ) (q : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range q).filter (fun r => (residueFiber A q r).Infinite)

lemma mem_recurringResidues_iff (A : Set ℕ) (q r : ℕ) :
    r ∈ recurringResidues A q ↔ r < q ∧ (residueFiber A q r).Infinite := by
  classical
  simp [recurringResidues]

lemma nonmultiples_infinite (A : Set ℕ)
    (htail : ∀ d : ℕ, 2 ≤ d → ∀ N : ℕ,
      ∃ n : ℕ, N ≤ n ∧ n ∈ A ∧ ¬ d ∣ n)
    (d : ℕ) (hd : 2 ≤ d) :
    {n : ℕ | n ∈ A ∧ ¬ d ∣ n}.Infinite := by
  intro hfinite
  obtain ⟨M, hM⟩ := hfinite.exists_le
  obtain ⟨n, hnM, hnA, hnd⟩ := htail d hd (M + 1)
  have hnle : n ≤ M := hM n ⟨hnA, hnd⟩
  omega

/-- The residue classes occurring infinitely often in `A` generate the full
cyclic group modulo `q`, expressed as a gcd-one statement. -/
theorem gcd_recurringResidues_eq_one (A : Set ℕ)
    (htail : ∀ d : ℕ, 2 ≤ d → ∀ N : ℕ,
      ∃ n : ℕ, N ≤ n ∧ n ∈ A ∧ ¬ d ∣ n)
    (q : ℕ) (hq : 2 ≤ q) :
    Nat.gcd q ((recurringResidues A q).gcd id) = 1 := by
  let R := recurringResidues A q
  let g := Nat.gcd q (R.gcd id)
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ (by omega)
  change g = 1
  by_contra hgne
  have hg2 : 2 ≤ g := by omega
  have hE : {n : ℕ | n ∈ A ∧ ¬ g ∣ n}.Infinite :=
    nonmultiples_infinite A htail g hg2
  let E : Set ℕ := {n : ℕ | n ∈ A ∧ ¬ g ∣ n}
  let f : E → Fin q := fun n =>
    ⟨n.1 % q, Nat.mod_lt _ (lt_of_lt_of_le Nat.zero_lt_two hq)⟩
  letI : Infinite E := hE.to_subtype
  obtain ⟨r, hr⟩ := Finite.exists_infinite_fiber f
  let P : Set E := f ⁻¹' {r}
  let emb : P → residueFiber A q r.val := fun n => by
    refine ⟨n.1.1, n.1.2.1, ?_⟩
    have hmem := n.2
    change f n.1 ∈ ({r} : Set (Fin q)) at hmem
    have hfr : f n.1 = r := Set.mem_singleton_iff.mp hmem
    exact congrArg Fin.val hfr
  have hemb : Function.Injective emb := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : residueFiber A q r.val => x.1) hab
  letI : Infinite P := hr
  haveI : Infinite (residueFiber A q r.val) := Infinite.of_injective emb hemb
  have hrInf : (residueFiber A q r.val).Infinite := Set.infinite_coe_iff.mp inferInstance
  have hrR : r.val ∈ R := by
    rw [show R = recurringResidues A q by rfl, mem_recurringResidues_iff]
    exact ⟨r.isLt, hrInf⟩
  have hgq : g ∣ q := Nat.gcd_dvd_left _ _
  have hgr : g ∣ r.val :=
    (Nat.gcd_dvd_right q (R.gcd id)).trans (Finset.gcd_dvd hrR)
  let a : P := Classical.arbitrary P
  have haE : a.1.1 ∈ A ∧ ¬ g ∣ a.1.1 := a.1.2
  have hmem := a.2
  change f a.1 ∈ ({r} : Set (Fin q)) at hmem
  have hfa : f a.1 = r := Set.mem_singleton_iff.mp hmem
  have hmod : a.1.1 % q = r.val := congrArg Fin.val hfa
  have hgn : g ∣ a.1.1 := by
    rw [← Nat.dvd_mod_iff hgq, hmod]
    exact hgr
  exact haE.2 hgn

end


private theorem finset_gcd_linear_combination (s : Finset ℕ) :
    ∃ c : ℕ → ℤ, ((s.gcd (fun x => x) : ℕ) : ℤ) =
      ∑ x ∈ s, c x * (x : ℤ) := by
  classical
  induction s using Finset.induction with
  | empty => exact ⟨fun _ => 0, by simp⟩
  | @insert a s ha ih =>
      obtain ⟨c, hc⟩ := ih
      let sg : ℕ := s.gcd (fun x => x)
      let ca := Nat.gcdA a sg
      let cb := Nat.gcdB a sg
      refine ⟨fun x => if x = a then ca else c x * cb, ?_⟩
      rw [Finset.gcd_insert, Finset.sum_insert ha]
      have hsum :
          ∑ x ∈ s, (if x = a then ca else c x * cb) * (x : ℤ) =
            (∑ x ∈ s, c x * (x : ℤ)) * cb := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro x hx
        rw [if_neg (by exact fun hxa => ha (hxa ▸ hx))]
        ring_nf
      rw [hsum, ← hc]
      simp only
      change ((Nat.gcd a sg : ℕ) : ℤ) = ca * (a : ℤ) + (sg : ℤ) * cb
      rw [Nat.gcd_eq_gcd_ab]
      simp only [ca, cb]
      ring_nf

/-- A gcd-one set of natural residues linearly generates one in `ZMod q`. -/
theorem zmod_one_linear_combination (R : Finset ℕ) (q : ℕ)
    (h : Nat.gcd q (R.gcd id) = 1) :
    ∃ z : ℕ → ℤ, (1 : ZMod q) =
      ∑ r ∈ R, (z r : ZMod q) * (r : ZMod q) := by
  classical
  obtain ⟨c, hc⟩ := finset_gcd_linear_combination R
  let rg : ℕ := R.gcd (fun r => r)
  let b : ℤ := Nat.gcdB q rg
  refine ⟨fun r => c r * b, ?_⟩
  have hab := Nat.gcd_eq_gcd_ab q rg
  have hrg : rg = R.gcd id := rfl
  rw [hrg, h] at hab
  have habz := congrArg (fun x : ℤ => (x : ZMod q)) hab
  norm_num at habz
  rw [habz]
  have hcz := congrArg (fun x : ℤ => (x : ZMod q)) hc
  norm_num at hcz
  change ((R.gcd (fun x => x) : ℕ) : ZMod q) *
    ((b : ℤ) : ZMod q) = ∑ r ∈ R, ((c r * b : ℤ) : ZMod q) * (r : ZMod q)
  rw [hcz]
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r hr
  simp only [b]
  push_cast
  ring

/-- With `q` labeled copies of each gcd-one residue, ordinary subset selection
can realize every target residue. -/
theorem zmod_target_as_bounded_repetitions (R : Finset ℕ) (q : ℕ) (hq : 2 ≤ q)
    (h : Nat.gcd q (R.gcd id) = 1) (t : ZMod q) :
    ∃ T : (r : {r // r ∈ R}) → Finset (Fin q),
      t = ∑ r, ∑ _k ∈ T r, (r.1 : ZMod q) := by
  classical
  letI : NeZero q := ⟨by omega⟩
  obtain ⟨z, hz⟩ := zmod_one_linear_combination R q h
  let coeff : {r // r ∈ R} → ℕ := fun r => (t * (z r.1 : ZMod q)).val
  let T : (r : {r // r ∈ R}) → Finset (Fin q) := fun r =>
    Finset.univ.filter (fun k => k.val < coeff r)
  refine ⟨T, ?_⟩
  have hcard : ∀ r, (T r).card = coeff r := by
    intro r
    change (Finset.univ.filter (fun k : Fin q => k.val < coeff r)).card = coeff r
    rw [Fin.card_filter_val_lt]
    exact Nat.min_eq_right (ZMod.val_lt _).le
  calc
    t = t * (1 : ZMod q) := by ring
    _ = t * (∑ r ∈ R, (z r : ZMod q) * (r : ZMod q)) := by rw [← hz]
    _ = ∑ r ∈ R, (t * (z r : ZMod q)) * (r : ZMod q) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      ring
    _ = ∑ r : {r // r ∈ R}, (coeff r : ZMod q) * (r.1 : ZMod q) := by
      rw [Finset.sum_subtype (p := fun r => r ∈ R) (s := R) (by simp)]
      apply Finset.sum_congr rfl
      intro r hr
      rw [show (coeff r : ZMod q) = t * (z r.1 : ZMod q) by
        exact ZMod.natCast_zmod_val _]
    _ = ∑ r, ∑ _k ∈ T r, (r.1 : ZMod q) := by
      apply Finset.sum_congr rfl
      intro r hr
      simp only [Finset.sum_const, hcard, nsmul_eq_mul]


/-- Every residue modulo `q` is a subset sum of arbitrarily far-out distinct
members of `A`. -/
theorem tail_subset_sums_cover_zmod (A : Set ℕ)
    (htail : ∀ d : ℕ, 2 ≤ d → ∀ N : ℕ,
      ∃ n : ℕ, N ≤ n ∧ n ∈ A ∧ ¬ d ∣ n)
    (q : ℕ) (hq : 2 ≤ q) (N : ℕ) (t : ZMod q) :
    ∃ s : Finset ℕ,
      (∀ n ∈ s, n ∈ A ∧ N ≤ n) ∧
      (∑ n ∈ s, (n : ZMod q)) = t := by
  classical
  letI : NeZero q := ⟨by omega⟩
  let R := recurringResidues A q
  have hgen : Nat.gcd q (R.gcd id) = 1 :=
    gcd_recurringResidues_eq_one A htail q hq
  let tailFiber (r : {r // r ∈ R}) : Set ℕ :=
    {n | n ∈ residueFiber A q r.1 ∧ N ≤ n}
  have htailFiber : ∀ r : {r // r ∈ R}, (tailFiber r).Infinite := by
    intro r
    have hrInf : (residueFiber A q r.1).Infinite :=
      (mem_recurringResidues_iff A q r.1).mp r.2 |>.2
    have hd := hrInf.sdiff (Set.finite_Iio N)
    have heq : residueFiber A q r.1 \ Set.Iio N = tailFiber r := by
      ext n
      simp only [Set.mem_sdiff, Set.mem_Iio, tailFiber, Set.mem_setOf_eq]
      constructor
      · rintro ⟨hn, hN⟩
        exact ⟨hn, Nat.le_of_not_gt hN⟩
      · rintro ⟨hn, hN⟩
        exact ⟨hn, Nat.not_lt_of_ge hN⟩
    rw [← heq]
    exact hd
  have hex : ∀ r : {r // r ∈ R}, ∃ W : Finset ℕ,
      (W : Set ℕ) ⊆ tailFiber r ∧ W.card = q := by
    intro r
    exact (htailFiber r).exists_subset_card_eq q
  choose W hWsub hWcard using hex
  let e : (r : {r // r ∈ R}) → Fin q → ℕ := fun r k =>
    ((W r).orderIsoOfFin (hWcard r) k).1
  have he_mem : ∀ r k, e r k ∈ W r := by
    intro r k
    exact ((W r).orderIsoOfFin (hWcard r) k).2
  have he_tail : ∀ r k, e r k ∈ residueFiber A q r.1 ∧ N ≤ e r k := by
    intro r k
    exact hWsub r (he_mem r k)
  have he_inj : ∀ r, Function.Injective (e r) := by
    intro r k l hkl
    apply (W r).orderIsoOfFin (hWcard r) |>.injective
    apply Subtype.ext
    exact hkl
  obtain ⟨T, hT⟩ := zmod_target_as_bounded_repetitions R q hq hgen t
  let U : {r // r ∈ R} → Finset ℕ := fun r => (T r).image (e r)
  have hU_tail : ∀ r n, n ∈ U r →
      n ∈ residueFiber A q r.1 ∧ N ≤ n := by
    intro r n hn
    change n ∈ (T r).image (e r) at hn
    rw [Finset.mem_image] at hn
    obtain ⟨k, hk, rfl⟩ := hn
    exact he_tail r k
  have hdisj : (↑(Finset.univ : Finset {r // r ∈ R}) : Set {r // r ∈ R}).PairwiseDisjoint U := by
    intro r hr r' hr' hne
    change Disjoint (U r) (U r')
    rw [Finset.disjoint_left]
    intro n hn hn'
    have hnmod := (hU_tail r n hn).1.2
    have hnmod' := (hU_tail r' n hn').1.2
    have hv : r.1 = r'.1 := hnmod.symm.trans hnmod'
    exact hne (Subtype.ext hv)
  have hsumU : ∀ r : {r // r ∈ R},
      (∑ n ∈ U r, (n : ZMod q)) =
        ∑ _k ∈ T r, (r.1 : ZMod q) := by
    intro r
    change (∑ n ∈ (T r).image (e r), (n : ZMod q)) =
      ∑ _k ∈ T r, (r.1 : ZMod q)
    rw [Finset.sum_image (he_inj r).injOn]
    apply Finset.sum_congr rfl
    intro k hk
    have hkmod := (he_tail r k).1.2
    rw [← ZMod.natCast_mod (e r k) q, hkmod]
  let s : Finset ℕ := Finset.univ.biUnion U
  refine ⟨s, ?_, ?_⟩
  · intro n hn
    change n ∈ Finset.univ.biUnion U at hn
    rw [Finset.mem_biUnion] at hn
    obtain ⟨r, hr, hnr⟩ := hn
    exact ⟨(hU_tail r n hnr).1.1, (hU_tail r n hnr).2⟩
  · change (∑ n ∈ Finset.univ.biUnion U, (n : ZMod q)) = t
    rw [Finset.sum_biUnion hdisj]
    calc
      (∑ r ∈ (Finset.univ : Finset {r // r ∈ R}),
          ∑ n ∈ U r, (n : ZMod q)) =
          ∑ r, ∑ _k ∈ T r, (r.1 : ZMod q) := by
            apply Finset.sum_congr rfl
            intro r hr
            exact hsumU r
      _ = t := hT.symm

end LocalCassels.TailModularCoverage
end

section
namespace LocalCassels.ScalarOrbit

open scoped BigOperators Topology
open LocalCassels.IrrationalDensity LocalCassels.TailSemigroup

noncomputable section

private lemma rat_mul_circle_eq_of_zmod_eq (r : ℚ) (a b : ℕ)
    (h : (a : ZMod r.den) = (b : ZMod r.den)) :
    (((r : ℝ) * (a : ℝ) : ℝ) : UnitAddCircle) =
      (((r : ℝ) * (b : ℝ) : ℝ) : UnitAddCircle) := by
  letI : NeZero r.den := ⟨r.den_nz⟩
  have hc := congrArg (fun z : ZMod r.den => ZMod.toAddCircle z) h
  rw [ZMod.toAddCircle_natCast, ZMod.toAddCircle_natCast] at hc
  have hnum := congrArg (fun z : UnitAddCircle => r.num • z) hc
  simpa only [← AddCircle.coe_zsmul, zsmul_eq_mul, Rat.cast_def,
    Int.cast_natCast, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hnum

private lemma sum_circle_eq_sum_nat (θ : ℝ) (s : Finset ℕ) :
    (∑ n ∈ s, ((θ * (n : ℝ) : ℝ) : UnitAddCircle)) =
      ((θ * (∑ n ∈ s, n : ℕ) : ℝ) : UnitAddCircle) := by
  let Q : ℝ →+ UnitAddCircle :=
    QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))
  change (∑ n ∈ s, Q (θ * (n : ℝ))) = Q (θ * (∑ n ∈ s, n : ℕ))
  rw [← map_sum Q]
  congr 1
  push_cast
  rw [Finset.mul_sum]

/-- Under the canonical phase hypothesis, every scalar orbit point can be
approximated by a distinct subset sum from every tail. Irrational phases use
F-028; rational phases use F-020 and are attained exactly. -/
theorem scalar_orbit_tail_approximation (A : Set ℕ)
    (hphase : ∀ θ : ℝ, θ ∈ Set.Ioo 0 1 →
      Filter.Tendsto (phasePartialSum A θ)
        (Filter.atTop : Filter ℕ) Filter.atTop)
    (θ : ℝ) (m N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ s : Finset ℕ,
      (∀ n ∈ s, n ∈ A ∧ N ≤ n) ∧
      dist (∑ n ∈ s, ((θ * (n : ℝ) : ℝ) : UnitAddCircle))
        (m • (θ : UnitAddCircle)) < ε := by
  by_cases hθ : Irrational θ
  · have hfull := irrational_tailLimit_eq_univ A hphase θ hθ
    let x : ℕ → UnitAddCircle := fun n => (θ * (n : ℝ) : UnitAddCircle)
    let target : UnitAddCircle := m • (θ : UnitAddCircle)
    have ht : target ∈ tailLimit A x := by
      rw [hfull]
      exact Set.mem_univ _
    have htN : target ∈ closure (tailSubsetSums A x N) := by
      rw [tailLimit, Set.mem_iInter] at ht
      exact ht N
    rw [Metric.mem_closure_iff] at htN
    obtain ⟨g, ⟨s, hs, hsg⟩, hdist⟩ := htN ε hε
    refine ⟨s, hs, ?_⟩
    rw [hsg]
    simpa only [dist_comm] using hdist
  · have hrange : θ ∈ Set.range ((↑) : ℚ → ℝ) := by
      exact Classical.not_not.mp hθ
    obtain ⟨r, rfl⟩ := hrange
    by_cases hden : r.den = 1
    · refine ⟨∅, by simp, ?_⟩
      have hrint : ((r : ℝ) : UnitAddCircle) = 0 := by
        rw [Rat.cast_def, hden]
        norm_num
      simp [hrint, hε]
    · have hdenpos : 0 < r.den := r.den_pos
      have hq2 : 2 ≤ r.den := by omega
      have htail : ∀ d : ℕ, 2 ≤ d → ∀ K : ℕ,
          ∃ n : ℕ, K ≤ n ∧ n ∈ A ∧ ¬ d ∣ n := by
        intro d hd K
        exact phase_implies_tail_nonmultiple A hphase d hd K
      obtain ⟨s, hs, hmod⟩ :=
        TailModularCoverage.tail_subset_sums_cover_zmod A htail r.den hq2 N
          (m : ZMod r.den)
      refine ⟨s, hs, ?_⟩
      have hcast : ((∑ n ∈ s, n : ℕ) : ZMod r.den) = (m : ZMod r.den) := by
        rw [Nat.cast_sum]
        exact hmod
      have hrat := rat_mul_circle_eq_of_zmod_eq r (∑ n ∈ s, n) m hcast
      rw [sum_circle_eq_sum_nat, hrat]
      have hm : ((((r : ℝ) * (m : ℝ) : ℝ)) : UnitAddCircle) =
          m • ((r : ℝ) : UnitAddCircle) := by
        rw [← AddCircle.coe_nsmul]
        congr 1
        simp [nsmul_eq_mul, mul_comm]
      rw [hm, dist_self]
      exact hε

end

end LocalCassels.ScalarOrbit
end

section
namespace LocalCassels.TorusOrbit

open scoped BigOperators Topology
open LocalCassels.TorusCharacterSeparation LocalCassels.ScalarOrbit
open LocalCassels.CompactSemigroup LocalCassels.TailSemigroup

noncomputable section

variable {d : Type*} [Fintype d]

/-- The additive-circle character associated to an integer vector. -/
def torusChar (k : d → ℤ) : UnitAddTorus d →ₜ+ UnitAddCircle := by
  classical
  let f : UnitAddTorus d →+ UnitAddCircle :=
    { toFun := fun y => ∑ i, k i • y i
      map_zero' := by simp
      map_add' := by
        intro x y
        simp only [Pi.add_apply, zsmul_add, Finset.sum_add_distrib] }
  exact ContinuousAddMonoidHom.mk f <| continuous_finsetSum Finset.univ fun i hi =>
    (continuous_apply i).zsmul (k i)

lemma mFourier_eq_torusChar_toCircle (k : d → ℤ) (y : UnitAddTorus d) :
    UnitAddTorus.mFourier k y = ((torusChar k y).toCircle : ℂ) := by
  classical
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, fourier_apply, torusChar]
  have haux : ∀ s : Finset d,
      (∏ i ∈ s, ((k i • y i).toCircle : ℂ)) =
        (((∑ i ∈ s, k i • y i : UnitAddCircle).toCircle) : ℂ) := by
    intro s
    induction s using Finset.induction with
    | empty => simp
    | @insert i s hi ih =>
        rw [Finset.prod_insert hi, Finset.sum_insert hi, AddCircle.toCircle_add,
          Circle.coe_mul, ih]
  exact haux Finset.univ

lemma torusChar_phase (k : d → ℤ) (α : d → ℝ) :
    torusChar k (fun i => (α i : UnitAddCircle)) =
      ((∑ i, (k i : ℝ) * α i : ℝ) : UnitAddCircle) := by
  classical
  let Q : ℝ →+ UnitAddCircle :=
    QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))
  change (∑ i, k i • Q (α i)) = Q (∑ i, (k i : ℝ) * α i)
  calc
    (∑ i, k i • Q (α i)) = ∑ i, Q (k i • α i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (map_zsmul Q (k i) (α i)).symm
    _ = Q (∑ i, k i • α i) := (map_sum Q (fun i => k i • α i) Finset.univ).symm
    _ = Q (∑ i, (k i : ℝ) * α i) := by
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      simp [zsmul_eq_mul]

/-- Under the canonical phase hypothesis, every point of a finite-dimensional
integer rotation orbit is approximable by distinct subset sums from every
tail. -/
theorem torus_orbit_tail_approximation (A : Set ℕ)
    (hphase : ∀ θ : ℝ, θ ∈ Set.Ioo 0 1 →
      Filter.Tendsto (phasePartialSum A θ)
        (Filter.atTop : Filter ℕ) Filter.atTop)
    (α : d → ℝ) (m N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ s : Finset ℕ,
      (∀ n ∈ s, n ∈ A ∧ N ≤ n) ∧
      dist (∑ n ∈ s, n • (fun i => (α i : UnitAddCircle)))
        (m • (fun i => (α i : UnitAddCircle))) < ε := by
  classical
  let a : UnitAddTorus d := fun i => (α i : UnitAddCircle)
  let seq : ℕ → UnitAddTorus d := fun n => n • a
  let S := tailLimit A seq
  have hSclosed : IsClosed S := tailLimit_isClosed A seq
  have hSzero : (0 : UnitAddTorus d) ∈ S := zero_mem_tailLimit A seq
  have hSadd : ∀ u ∈ S, ∀ v ∈ S, u + v ∈ S := by
    intro u hu v hv
    exact tailLimit_add_mem A seq hu hv
  obtain ⟨H, hH⟩ := compact_add_subsemigroup_is_addSubgroup S
    ⟨0, hSzero⟩ hSclosed hSadd
  let target : UnitAddTorus d := m • a
  have htarget : target ∈ H := by
    by_contra htH
    obtain ⟨k, hkH, hkt⟩ := exists_character_separating_point H
      (by rw [hH]; exact hSclosed) htH
    let C := torusChar k
    let φ : ℝ := ∑ i, (k i : ℝ) * α i
    have hCa : C a = (φ : UnitAddCircle) := torusChar_phase k α
    have hCt : C target = m • (φ : UnitAddCircle) := by
      change C (m • a) = _
      rw [map_nsmul, hCa]
    have hCH : ∀ y ∈ H, C y = 0 := by
      intro y hy
      have hfour := hkH y hy
      rw [mFourier_eq_torusChar_toCircle] at hfour
      apply AddCircle.injective_toCircle one_ne_zero
      apply Subtype.ext
      simpa using hfour
    have hCt0 : C target ≠ 0 := by
      intro hzero
      apply hkt
      rw [mFourier_eq_torusChar_toCircle, hzero]
      simp
    have hImageClosure : ∀ K : ℕ,
        C target ∈ closure (C '' tailSubsetSums A seq K) := by
      intro K
      rw [Metric.mem_closure_iff]
      intro δ hδ
      obtain ⟨s, hs, hdist⟩ := scalar_orbit_tail_approximation
        A hphase φ m K δ hδ
      let g : UnitAddTorus d := ∑ n ∈ s, seq n
      have hg : g ∈ tailSubsetSums A seq K := ⟨s, hs, rfl⟩
      refine ⟨C g, ⟨g, hg, rfl⟩, ?_⟩
      have hCg : C g = ∑ n ∈ s, ((φ * (n : ℝ) : ℝ) : UnitAddCircle) := by
        change C (∑ n ∈ s, n • a) = _
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro n hn
        rw [map_nsmul, hCa]
        rw [← AddCircle.coe_nsmul]
        congr 1
        simp [nsmul_eq_mul, mul_comm]
      rw [hCg, hCt]
      simpa only [dist_comm] using hdist
    let E : Set (UnitAddTorus d) := {y | C y = C target}
    have hE : IsClosed E := isClosed_eq C.continuous_toFun continuous_const
    let Kset : ℕ → Set (UnitAddTorus d) := fun K =>
      closure (tailSubsetSums A seq K) ∩ E
    have hKn : ∀ K, (Kset K).Nonempty := by
      intro K
      have himg := hImageClosure K
      have hcompact : IsCompact (closure (tailSubsetSums A seq K)) :=
        isClosed_closure.isCompact
      have hclosedImage : IsClosed (C '' closure (tailSubsetSums A seq K)) :=
        (hcompact.image C.continuous_toFun).isClosed
      have hsub : closure (C '' tailSubsetSums A seq K) ⊆
          C '' closure (tailSubsetSums A seq K) := by
        apply closure_minimal
        · exact Set.image_mono subset_closure
        · exact hclosedImage
      obtain ⟨y, hy, hyC⟩ := hsub himg
      exact ⟨y, hy, hyC⟩
    have hKclosed : ∀ K, IsClosed (Kset K) := fun K => isClosed_closure.inter hE
    have hKcompact : ∀ K, IsCompact (Kset K) := fun K => (hKclosed K).isCompact
    have hKdir : Directed (fun X Y : Set (UnitAddTorus d) => X ⊇ Y) Kset := by
      intro K L
      refine ⟨max K L, ?_, ?_⟩
      · intro y hy
        exact ⟨closure_mono (tailSubsetSums_mono_cutoff A seq (le_max_left K L)) hy.1,
          hy.2⟩
      · intro y hy
        exact ⟨closure_mono (tailSubsetSums_mono_cutoff A seq (le_max_right K L)) hy.1,
          hy.2⟩
    obtain ⟨y, hy⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      Kset hKdir hKn hKcompact hKclosed
    have hyS : y ∈ S := by
      change y ∈ tailLimit A seq
      rw [tailLimit, Set.mem_iInter]
      intro K
      exact (Set.mem_iInter.mp hy K).1
    have hyH : y ∈ H := by
      change y ∈ (H : Set (UnitAddTorus d))
      rw [hH]
      exact hyS
    have hyE : C y = C target := (Set.mem_iInter.mp hy 0).2
    exact hCt0 (hyE ▸ hCH y hyH)
  have htS : target ∈ S := by
    have ht : target ∈ (H : Set (UnitAddTorus d)) := htarget
    rw [hH] at ht
    exact ht
  have htN : target ∈ closure (tailSubsetSums A seq N) := by
    change target ∈ tailLimit A seq at htS
    rw [tailLimit, Set.mem_iInter] at htS
    exact htS N
  rw [Metric.mem_closure_iff] at htN
  obtain ⟨g, ⟨s, hs, hsg⟩, hdist⟩ := htN ε hε
  refine ⟨s, hs, ?_⟩
  change dist (∑ n ∈ s, seq n) target < ε
  rw [hsg]
  simpa only [dist_comm] using hdist

end

end LocalCassels.TorusOrbit
end

section
namespace LocalCassels.TorusCorrectionGroup

open Filter Topology
open scoped BigOperators
open LocalCassels.PiecewiseAssembly LocalCassels.TailSemigroup
open LocalCassels.CompactSemigroup LocalCassels.TorusOrbit

noncomputable section

variable {d : Type*} [Fintype d]

lemma sum_nsmul_coeff {G : Type*} [AddCommMonoid G]
    (s : Finset ℕ) (a : G) :
    (∑ n ∈ s, n • a) = (∑ n ∈ s, n) • a := by
  induction s using Finset.induction with
  | empty => simp
  | @insert n s hn ih => simp [hn, ih, add_nsmul]

/-- Full phase divergence produces one closed compact correction subgroup for
any finite torus rotation, with genuine distinct-support corrections dense at
every point of that subgroup. -/
theorem exists_closed_torus_correction_group
    (C : Set ℕ)
    (hphase : ∀ θ : ℝ, θ ∈ Set.Ioo 0 1 →
      Tendsto (phasePartialSum C θ) atTop atTop)
    (α : d → ℝ) :
    ∃ H : AddSubgroup (UnitAddTorus d),
      IsClosed (H : Set (UnitAddTorus d)) ∧
      (fun i => (α i : UnitAddCircle)) ∈ H ∧
      ∀ x ∈ H, ∀ O : Set (UnitAddTorus d), IsOpen O → x ∈ O →
        ∃ q : ℕ, Representable C q ∧
          q • (fun i => (α i : UnitAddCircle)) ∈ O := by
  classical
  let a : UnitAddTorus d := fun i => (α i : UnitAddCircle)
  let seq : ℕ → UnitAddTorus d := fun n => n • a
  let S := tailLimit C seq
  have hSclosed : IsClosed S := tailLimit_isClosed C seq
  have hSzero : (0 : UnitAddTorus d) ∈ S := zero_mem_tailLimit C seq
  have hSadd : ∀ u ∈ S, ∀ v ∈ S, u + v ∈ S := by
    intro u hu v hv
    exact tailLimit_add_mem C seq hu hv
  obtain ⟨H, hH⟩ := compact_add_subsemigroup_is_addSubgroup S
    ⟨0, hSzero⟩ hSclosed hSadd
  have haS : a ∈ S := by
    change a ∈ tailLimit C seq
    rw [tailLimit, Set.mem_iInter]
    intro N
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨s, hs, hdist⟩ := torus_orbit_tail_approximation
      C hphase α 1 N ε hε
    refine ⟨∑ n ∈ s, seq n, ⟨s, hs, rfl⟩, ?_⟩
    simpa [seq, a, dist_comm] using hdist
  refine ⟨H, ?_, ?_, ?_⟩
  · rw [hH]
    exact hSclosed
  · change a ∈ (H : Set (UnitAddTorus d))
    rw [hH]
    exact haS
  · intro x hx O hOopen hxO
    have hxS : x ∈ S := by
      rw [← hH]
      exact hx
    change x ∈ tailLimit C seq at hxS
    rw [tailLimit, Set.mem_iInter] at hxS
    have hx0 := hxS 0
    rw [mem_closure_iff] at hx0
    obtain ⟨g, hgO, hgTail⟩ := hx0 O hOopen hxO
    obtain ⟨s, hs, rfl⟩ := hgTail
    let q : ℕ := ∑ n ∈ s, n
    refine ⟨q, ?_, ?_⟩
    · exact ⟨s, fun n hn => (hs n hn).1, rfl⟩
    · have hsum : (∑ n ∈ s, seq n) = q • a := by
        simpa [seq, q] using sum_nsmul_coeff s a
      rw [hsum] at hgO
      exact hgO

end

end LocalCassels.TorusCorrectionGroup
end

section
namespace LocalCassels.ConditionalFinalAssembly

open Filter
open scoped Topology BigOperators
open LocalCassels
open LocalCassels.PiecewiseAssembly LocalCassels.ConditionalBohrCriterion
open LocalCassels.DisjointCriterionDecomposition LocalCassels.TorusCorrectionGroup

noncomputable section

/-- The exact Bergelson--Furstenberg--Weiss interface still needed: sums of two
sets with syndetic distinct-subset sums contain a finite-dimensional
piecewise-Bohr return set. -/
def BFWFiniteSumProperty : Prop :=
  ∀ B₀ B₁ : Set ℕ, Disjoint B₀ B₁ →
    (∀ i : Fin 2, ∃ K : ℕ, ∀ n : ℕ, ∃ t : Finset ℕ,
      (∀ b ∈ t, b ∈ (if i = 0 then B₀ else B₁)) ∧
      (∑ b ∈ t, b) ≤ n ∧ n ≤ (∑ b ∈ t, b) + K) →
    ∃ d : ℕ, ∃ α : Fin d → ℝ,
      ∃ U : Set (UnitAddTorus (Fin d)), IsOpen U ∧
      ∃ n₀ : ℕ, n₀ • (fun i => (α i : UnitAddCircle)) ∈ U ∧
      ∃ J : Set ℕ, IsThick J ∧
      ∀ n : ℕ, n ∈ J → n • (fun i => (α i : UnitAddCircle)) ∈ U →
        Representable (B₀ ∪ B₁) n

/-- Once the standard BFW finite-sum property is supplied, F-071 and the
already formal compact correction assembly prove the canonical Erdős statement. -/
theorem bfw_finite_sum_property_implies_statement
    (hBFW : BFWFiniteSumProperty) : LocalCassels.Statement := by
  intro A hdyadic hphase
  obtain ⟨B, C, hBA, hCA, hBpair, hBC, hcover, hBsynd, hCphase⟩ :=
    exists_three_syndetic_classes_and_universal_correction A hdyadic hphase
  let B₀ := B (0 : Fin 3)
  let B₁ := B (1 : Fin 3)
  let D := B (2 : Fin 3)
  have htwo : ∀ i : Fin 2, ∃ K : ℕ, ∀ n : ℕ, ∃ t : Finset ℕ,
      (∀ b ∈ t, b ∈ (if i = 0 then B₀ else B₁)) ∧
      (∑ b ∈ t, b) ≤ n ∧ n ≤ (∑ b ∈ t, b) + K := by
    intro i
    fin_cases i
    · simpa [B₀] using hBsynd (0 : Fin 3)
    · simpa [B₁] using hBsynd (1 : Fin 3)
  have hB01 : Disjoint B₀ B₁ :=
    hBpair (by decide : (0 : Fin 3) ≠ 1)
  obtain ⟨d, α, U, hUopen, n₀, hn₀U, J, hJ, hpiece⟩ :=
    hBFW B₀ B₁ hB01 htwo
  obtain ⟨H, hHclosed, haH, hcorr⟩ :=
    exists_closed_torus_correction_group C hCphase α
  have hB01C : Disjoint (B₀ ∪ B₁) C := by
    rw [Set.disjoint_left]
    intro n hn hnC
    rcases hn with hn0 | hn1
    · exact Set.disjoint_left.mp (hBC (0 : Fin 3)) hn0 hnC
    · exact Set.disjoint_left.mp (hBC (1 : Fin 3)) hn1 hnC
  have hB01D : Disjoint (B₀ ∪ B₁) D := by
    rw [Set.disjoint_left]
    intro n hn hnD
    rcases hn with hn0 | hn1
    · exact Set.disjoint_left.mp (hBpair (by decide : (0 : Fin 3) ≠ 2)) hn0 hnD
    · exact Set.disjoint_left.mp (hBpair (by decide : (1 : Fin 3) ≠ 2)) hn1 hnD
  have hCD : Disjoint C D := (hBC (2 : Fin 3)).symm
  obtain ⟨KD, hDsynd⟩ := hBsynd (2 : Fin 3)
  obtain ⟨N, hN⟩ := conditional_piecewise_bohr_completeness
    (B₀ ∪ B₁) C D hB01C hB01D hCD
    (fun i => (α i : UnitAddCircle)) H hHclosed haH hcorr
    U hUopen n₀ hn₀U J hJ hpiece KD
    (fun n => by
      obtain ⟨t, htD, htlo, hthi⟩ := hDsynd n
      exact ⟨∑ b ∈ t, b, ⟨t, htD, rfl⟩, htlo, hthi⟩)
  refine ⟨N, ?_⟩
  intro m hm
  obtain ⟨s, hs, hsum⟩ := hN m hm
  refine ⟨s, ?_, hsum⟩
  intro x hxs
  have hxUnion := hs x hxs
  rcases hxUnion with hxBC | hxD
  · rcases hxBC with hxB | hxC
    · rcases hxB with hx0 | hx1
      · exact hBA (0 : Fin 3) hx0
      · exact hBA (1 : Fin 3) hx1
    · exact hCA hxC
  · exact hBA (2 : Fin 3) hxD

end

end LocalCassels.ConditionalFinalAssembly
end

section
namespace LocalCassels.GeneralBFWReduction

open scoped Topology BigOperators
open LocalCassels.PiecewiseAssembly LocalCassels.ConditionalFinalAssembly

noncomputable section

/-- Standard set-theoretic BFW theorem in exactly the finite-torus form needed
here. -/
def SyndeticSumsetPiecewiseBohr : Prop :=
  ∀ S₀ S₁ : Set ℕ,
    (∀ i : Fin 2, ∃ K : ℕ, ∀ n : ℕ, ∃ s : ℕ,
      s ∈ (if i = 0 then S₀ else S₁) ∧ s ≤ n ∧ n ≤ s + K) →
    ∃ d : ℕ, ∃ α : Fin d → ℝ,
      ∃ U : Set (UnitAddTorus (Fin d)), IsOpen U ∧
      ∃ n₀ : ℕ, n₀ • (fun i => (α i : UnitAddCircle)) ∈ U ∧
      ∃ J : Set ℕ, IsThick J ∧
      ∀ n : ℕ, n ∈ J → n • (fun i => (α i : UnitAddCircle)) ∈ U →
        ∃ s₀ ∈ S₀, ∃ s₁ ∈ S₁, s₀ + s₁ = n

/-- The standard BFW sumset theorem implies the finite-sum interface, because
representations from two disjoint source classes can be united without reuse. -/
theorem general_bfw_implies_finite_sum_property
    (hBFW : SyndeticSumsetPiecewiseBohr) : BFWFiniteSumProperty := by
  intro B₀ B₁ hBdis hsynd
  let S₀ : Set ℕ := {n | Representable B₀ n}
  let S₁ : Set ℕ := {n | Representable B₁ n}
  have hSsynd : ∀ i : Fin 2, ∃ K : ℕ, ∀ n : ℕ, ∃ s : ℕ,
      s ∈ (if i = 0 then S₀ else S₁) ∧ s ≤ n ∧ n ≤ s + K := by
    intro i
    obtain ⟨K, hK⟩ := hsynd i
    refine ⟨K, fun n => ?_⟩
    obtain ⟨t, ht, htlo, hthi⟩ := hK n
    refine ⟨∑ b ∈ t, b, ?_, htlo, hthi⟩
    fin_cases i
    · exact ⟨t, by simpa using ht, rfl⟩
    · exact ⟨t, by simpa using ht, rfl⟩
  obtain ⟨d, α, U, hU, n₀, hn₀, J, hJ, hpiece⟩ := hBFW S₀ S₁ hSsynd
  refine ⟨d, α, U, hU, n₀, hn₀, J, hJ, ?_⟩
  intro n hnJ hnU
  obtain ⟨s₀, hs₀, s₁, hs₁, hsum⟩ := hpiece n hnJ hnU
  have hrep := representable_add_of_disjoint hBdis hs₀ hs₁
  rwa [hsum] at hrep

end

end LocalCassels.GeneralBFWReduction
end

section
namespace LocalCassels.FiniteEmbeddingPiecewiseBohrOrbit

open Filter Topology
open LocalCassels.PiecewiseAssembly

noncomputable section

/-- Orbit-point strengthening of F-073: if the original open set contains a
forward orbit point, so does the reassembled open set. -/
theorem piecewise_bohr_of_finite_embedding_orbit
    {T : Type*} [TopologicalSpace T] [T2Space T] [AddCommGroup T]
    [IsTopologicalAddGroup T] [CompactSpace T]
    (a : T) (U : Set T) (hUopen : IsOpen U)
    (u₀ : ℕ) (hu₀ : u₀ • a ∈ U)
    (S : Set ℕ)
    (hembed : ∀ F : Finset ℕ,
      (∀ n ∈ F, n • a ∈ U) →
      ∃ r : ℕ, ∀ n ∈ F, n + r ∈ S) :
    ∃ W : Set T, IsOpen W ∧
      ∃ n₀ : ℕ, n₀ • a ∈ W ∧
      ∃ J : Set ℕ, IsThick J ∧
        ∀ n : ℕ, n ∈ J → n • a ∈ W → n ∈ S := by
  classical
  let F : ℕ → Finset ℕ := fun L =>
    (Finset.range (L + 1)).filter (fun n => n • a ∈ U)
  have hF : ∀ L n, n ∈ F L ↔ n ≤ L ∧ n • a ∈ U := by
    intro L n
    simp [F]
  have hr_exists : ∀ L, ∃ r : ℕ, ∀ n : ℕ,
      n ≤ L → n • a ∈ U → n + r ∈ S := by
    intro L
    obtain ⟨r, hr⟩ := hembed (F L) (fun n hn => (hF L n).mp hn |>.2)
    exact ⟨r, fun n hnL hnU => hr n ((hF L n).mpr ⟨hnL, hnU⟩)⟩
  choose r hr using hr_exists
  let p : Ultrafilter ℕ := Ultrafilter.of atTop
  let y : T := Ultrafilter.extend (fun L => r L • a) p
  have hlim : Tendsto (fun L => r L • a) (↑p : Filter ℕ) (𝓝 y) :=
    ultrafilter_extend_eq_iff.mp rfl
  have hsubEventually :
      ∀ᶠ z : T × T in (𝓝 (u₀ • a + y, y)), z.1 - z.2 ∈ U := by
    apply continuous_sub.continuousAt
    simpa using hUopen.mem_nhds hu₀
  rw [nhds_prod_eq] at hsubEventually
  obtain ⟨pW, hpW, pV, hpV, hpWV⟩ :=
    eventually_prod_iff.mp hsubEventually
  obtain ⟨W, hWsub, hWopen, huW⟩ := eventually_nhds_iff.mp hpW
  have hphaseV : ∀ᶠ L in (↑p : Filter ℕ), pV (r L • a) := hlim hpV
  let I : Set ℕ := {L | pV (r L • a)}
  have hIunbounded : ∀ K : ℕ, ∃ L ∈ I, K ≤ L := by
    intro K
    have hge : ∀ᶠ L : ℕ in (↑p : Filter ℕ), K ≤ L :=
      Ultrafilter.of_le atTop (eventually_ge_atTop K)
    obtain ⟨L, hLI, hLK⟩ := (hphaseV.and hge).exists
    exact ⟨L, hLI, hLK⟩
  let J : Set ℕ := {n | ∃ L ∈ I, ∃ k : ℕ, k ≤ L ∧ n = r L + k}
  have hJthick : IsThick J := by
    intro K
    obtain ⟨L, hLI, hKL⟩ := hIunbounded K
    exact ⟨r L, fun k hk => ⟨L, hLI, k, hk.trans hKL, rfl⟩⟩
  have hlimAdd : Tendsto (fun L => u₀ • a + r L • a)
      (↑p : Filter ℕ) (𝓝 (u₀ • a + y)) := tendsto_const_nhds.add hlim
  have hphaseW : ∀ᶠ L in (↑p : Filter ℕ), u₀ • a + r L • a ∈ W :=
    hlimAdd (hWopen.mem_nhds huW)
  obtain ⟨L₀, hL₀⟩ := hphaseW.exists
  refine ⟨W, hWopen, u₀ + r L₀, ?_, J, hJthick, ?_⟩
  · simpa [add_nsmul] using hL₀
  · intro n hnJ hnW
    obtain ⟨L, hLI, k, hkL, rfl⟩ := hnJ
    have hkphase : k • a ∈ U := by
      change pV (r L • a) at hLI
      have hp := hpWV (hWsub _ hnW) hLI
      simpa [add_nsmul] using hp
    simpa [Nat.add_comm] using hr L k hkL hkphase

end

end LocalCassels.FiniteEmbeddingPiecewiseBohrOrbit
end

section
namespace LocalCassels.SyndeticDensityBlocks

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- A backward-gap bound supplies at least one point in each disjoint block of
length `K+1`. -/
theorem card_filter_range_mul_lower
    (S : Set ℕ) (K m : ℕ)
    (hS : ∀ n : ℕ, ∃ s : ℕ, s ∈ S ∧ s ≤ n ∧ n ≤ s + K) :
    m ≤ ((Finset.range (m * (K + 1))).filter (fun n => n ∈ S)).card := by
  let Q := K + 1
  have hex : ∀ i : Fin m, ∃ s : ℕ,
      s ∈ S ∧ i.val * Q ≤ s ∧ s < (i.val + 1) * Q := by
    intro i
    obtain ⟨s, hsS, hslow, hshigh⟩ := hS ((i.val + 1) * Q - 1)
    refine ⟨s, hsS, ?_, ?_⟩
    · dsimp [Q] at hslow hshigh ⊢
      have hpos : 0 < (i.val + 1) * (K + 1) := by positivity
      have heq : (i.val + 1) * (K + 1) =
          i.val * (K + 1) + (K + 1) := by ring
      omega
    · dsimp [Q] at hslow hshigh ⊢
      have hpos : 0 < (i.val + 1) * (K + 1) := by positivity
      omega
  choose s hsS hslo hshi using hex
  have hinj : Function.Injective s := by
    intro i j hij
    apply Fin.ext
    by_contra hne
    rcases lt_or_gt_of_ne hne with hijlt | hjilt
    · have hblocks : (i.val + 1) * Q ≤ j.val * Q :=
        Nat.mul_le_mul_right Q (by omega)
      have hslt : s i < s j := (hshi i).trans_le (hblocks.trans (hslo j))
      exact (ne_of_lt hslt) hij
    · have hblocks : (j.val + 1) * Q ≤ i.val * Q :=
        Nat.mul_le_mul_right Q (by omega)
      have hslt : s j < s i := (hshi j).trans_le (hblocks.trans (hslo i))
      exact (ne_of_gt hslt) hij
  have hmem : ∀ i, s i ∈
      (Finset.range (m * (K + 1))).filter (fun n => n ∈ S) := by
    intro i
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr ?_, hsS i⟩
    have hi : i.val + 1 ≤ m := i.isLt
    have htop : (i.val + 1) * Q ≤ m * Q := Nat.mul_le_mul_right Q hi
    simpa [Q] using (hshi i).trans_le htop
  let emb : Fin m ↪ {n // n ∈
      (Finset.range (m * (K + 1))).filter (fun n => n ∈ S)} :=
    ⟨fun i => ⟨s i, hmem i⟩, fun i j h => hinj (congrArg Subtype.val h)⟩
  simpa using Fintype.card_le_of_injective emb emb.injective

end

end LocalCassels.SyndeticDensityBlocks
end

section
namespace LocalCassels.CrossAlignment

open scoped BigOperators

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Two finite subsets of `[0,L)` have a common exact-sum fiber of size at
least their product divided by `2L`. -/
theorem exists_large_exact_sum_fiber
    (A B : Finset ℕ) (L : ℕ) (hL : 0 < L)
    (hA : ∀ x ∈ A, x < L) (hB : ∀ y ∈ B, y < L) :
    ∃ r : ℕ, r < 2 * L ∧ ∃ C : Finset ℕ,
      A.card * B.card ≤ (2 * L) * C.card ∧
      (∀ x ∈ C, x ∈ A ∧ ∃ y ∈ B, x + y = r) := by
  let pairs := A.product B
  let D : ℕ → Finset (ℕ × ℕ) := fun r =>
    pairs.filter (fun p => p.1 + p.2 = r)
  have hsum : ∑ r ∈ Finset.range (2 * L), (D r).card = pairs.card := by
    dsimp [D]
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm]
    calc
      (∑ x ∈ pairs, ∑ r ∈ Finset.range (2 * L),
          if x.1 + x.2 = r then 1 else 0) = ∑ _x ∈ pairs, 1 := by
        apply Finset.sum_congr rfl
        intro p hp
        have hp' := Finset.mem_product.mp hp
        have hplt : p.1 + p.2 < 2 * L := by
          have hx := hA p.1 hp'.1
          have hy := hB p.2 hp'.2
          omega
        simp [hplt]
      _ = pairs.card := by simp
  have hrange : (Finset.range (2 * L)).Nonempty := by
    simp [hL.ne']
  obtain ⟨r, hrRange, hrmax⟩ :=
    Finset.exists_max_image (Finset.range (2 * L)) (fun r => (D r).card) hrange
  have hlargeD : A.card * B.card ≤ (2 * L) * (D r).card := by
    have havg := Finset.sum_le_card_nsmul (Finset.range (2 * L))
      (fun q => (D q).card) ((D r).card) hrmax
    rw [hsum] at havg
    dsimp [pairs] at havg
    simp only [Finset.card_product, Finset.card_range, nsmul_eq_mul] at havg
    exact havg
  have hfstinj : Set.InjOn Prod.fst (D r : Set (ℕ × ℕ)) := by
    intro p hp q hq hpq
    have hpD := Finset.mem_filter.mp hp
    have hqD := Finset.mem_filter.mp hq
    apply Prod.ext
    · exact hpq
    · have hpsum := hpD.2
      have hqsum := hqD.2
      omega
  let C : Finset ℕ := (D r).image Prod.fst
  have hcardC : C.card = (D r).card := Finset.card_image_iff.mpr hfstinj
  refine ⟨r, Finset.mem_range.mp hrRange, C, ?_, ?_⟩
  · rwa [hcardC]
  · intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨p, hpD, rfl⟩ := hx
    have hp := Finset.mem_filter.mp hpD
    have hpPair := Finset.mem_product.mp hp.1
    exact ⟨hpPair.1, p.2, hpPair.2, hp.2⟩

end

end LocalCassels.CrossAlignment
end

section
namespace LocalCassels.DenseChunk

open scoped BigOperators

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Partition a finite subset of `[0,mR)` into `R` consecutive chunks and
choose one whose translated copy has at least the average cardinality. -/
theorem exists_dense_chunk
    (C : Finset ℕ) (m R : ℕ) (hm : 0 < m) (hR : 0 < R)
    (hC : ∀ x ∈ C, x < m * R) :
    ∃ c : ℕ, c < R ∧ ∃ B : Finset ℕ,
      C.card ≤ R * B.card ∧
      ∀ x ∈ B, x < m ∧ c * m + x ∈ C := by
  let D : ℕ → Finset ℕ := fun c =>
    C.filter (fun x => c * m ≤ x ∧ x < (c + 1) * m)
  have hsum : ∑ c ∈ Finset.range R, (D c).card = C.card := by
    dsimp [D]
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm]
    calc
      (∑ x ∈ C, ∑ c ∈ Finset.range R,
          if c * m ≤ x ∧ x < (c + 1) * m then 1 else 0) =
          ∑ _x ∈ C, 1 := by
        apply Finset.sum_congr rfl
        intro x hx
        have hxlt := hC x hx
        let c := x / m
        have hcR : c < R := by
          dsimp [c]
          exact (Nat.div_lt_iff_lt_mul hm).2 (by simpa [Nat.mul_comm] using hxlt)
        have hclo : c * m ≤ x := Nat.div_mul_le_self x m
        have hchi : x < (c + 1) * m := by
          dsimp [c]
          simpa [Nat.mul_comm] using Nat.lt_mul_div_succ x hm
        rw [Finset.sum_eq_single c]
        · simp [hcR, hclo, hchi]
        · intro b hb hbc
          have hfalse : ¬(b * m ≤ x ∧ x < (b + 1) * m) := by
            rintro ⟨hblo, hbhi⟩
            apply hbc
            dsimp [c]
            exact (Nat.div_eq_of_lt_le hblo hbhi).symm
          simp [hfalse]
        · intro hcnot
          exact (hcnot (Finset.mem_range.mpr hcR)).elim
      _ = C.card := by simp
  have hrange : (Finset.range R).Nonempty := by simp [hR.ne']
  obtain ⟨c, hcRange, hcmax⟩ :=
    Finset.exists_max_image (Finset.range R) (fun c => (D c).card) hrange
  have hlarge : C.card ≤ R * (D c).card := by
    have havg := Finset.sum_le_card_nsmul (Finset.range R)
      (fun b => (D b).card) ((D c).card) hcmax
    rw [hsum] at havg
    simpa using havg
  let B : Finset ℕ := (D c).image (fun x => x - c * m)
  have hinj : Set.InjOn (fun x : ℕ => x - c * m) (D c : Set ℕ) := by
    intro x hx y hy hxy
    have hxlo := (Finset.mem_filter.mp hx).2.1
    have hylo := (Finset.mem_filter.mp hy).2.1
    change x - c * m = y - c * m at hxy
    calc
      x = (x - c * m) + c * m := (Nat.sub_add_cancel hxlo).symm
      _ = (y - c * m) + c * m := by rw [hxy]
      _ = y := Nat.sub_add_cancel hylo
  have hcardB : B.card = (D c).card := Finset.card_image_iff.mpr hinj
  refine ⟨c, Finset.mem_range.mp hcRange, B, ?_, ?_⟩
  · rwa [hcardB]
  · intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨z, hzD, rfl⟩ := hx
    have hz := Finset.mem_filter.mp hzD
    refine ⟨?_, ?_⟩
    · have hzlo := hz.2.1
      rw [Nat.sub_lt_iff_lt_add' hzlo]
      simpa [add_mul, Nat.add_comm] using hz.2.2
    · have hzlo := hz.2.1
      rw [Nat.add_sub_of_le hzlo]
      exact hz.1

end

end LocalCassels.DenseChunk
end

section
namespace LocalCassels.ZModParseval

open Finset AddChar
open scoped BigOperators ComplexConjugate
open ZMod

noncomputable section

variable {N : ℕ} [NeZero N]

private lemma character_sum (t : ZMod N) :
    ∑ k : ZMod N, stdAddChar (t * k) = if t = 0 then (N : ℂ) else 0 := by
  split_ifs with h
  · simp [h]
  · exact sum_eq_zero_of_ne_one (isPrimitive_stdAddChar N h)

/-- Parseval's identity for the unnormalized DFT on `ZMod N`. -/
theorem dft_energy (Φ : ZMod N → ℂ) :
    ∑ k : ZMod N, starRingEnd ℂ (𝓕 Φ k) * 𝓕 Φ k =
      (N : ℂ) * ∑ j : ZMod N, starRingEnd ℂ (Φ j) * Φ j := by
  simp only [dft_apply, map_sum, map_mul, smul_eq_mul]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hchar (x y i : ZMod N) :
      starRingEnd ℂ (stdAddChar (-(y * x))) * stdAddChar (-(i * x)) =
        stdAddChar ((y - i) * x) := by
    rw [← inv_apply_eq_conj, ← map_neg_eq_inv, ← map_add_eq_mul]
    congr 1
    ring
  have hinner (y i : ZMod N) :
      (∑ x : ZMod N,
        starRingEnd ℂ (stdAddChar (-(y * x))) * starRingEnd ℂ (Φ y) *
          (stdAddChar (-(i * x)) * Φ i)) =
        if y = i then (N : ℂ) * (starRingEnd ℂ (Φ y) * Φ i) else 0 := by
    calc
      _ = ∑ x : ZMod N, (starRingEnd ℂ (Φ y) * Φ i) *
          (starRingEnd ℂ (stdAddChar (-(y * x))) * stdAddChar (-(i * x))) := by
        apply Finset.sum_congr rfl
        intro x hx
        ring
      _ = (starRingEnd ℂ (Φ y) * Φ i) *
          ∑ x : ZMod N, stdAddChar ((y - i) * x) := by
        simp_rw [hchar]
        rw [Finset.mul_sum]
      _ = (starRingEnd ℂ (Φ y) * Φ i) *
          (if y - i = 0 then (N : ℂ) else 0) := by
        rw [character_sum]
      _ = if y = i then (N : ℂ) * (starRingEnd ℂ (Φ y) * Φ i) else 0 := by
        simp only [sub_eq_zero]
        by_cases h : y = i <;> simp [h] <;> ring
  have hswap (y : ZMod N) :
      (∑ x : ZMod N, ∑ i : ZMod N,
        starRingEnd ℂ (stdAddChar (-(y * x))) * starRingEnd ℂ (Φ y) *
          (stdAddChar (-(i * x)) * Φ i)) =
      ∑ i : ZMod N,
        if y = i then (N : ℂ) * (starRingEnd ℂ (Φ y) * Φ i) else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    exact hinner y i
  simp_rw [hswap]
  simp

/-- Fourier transform of the DFT energy is cyclic autocorrelation. -/
theorem dft_energy_character (Φ : ZMod N → ℂ) (n : ZMod N) :
    ∑ k : ZMod N,
      (starRingEnd ℂ (𝓕 Φ k) * 𝓕 Φ k) * stdAddChar (k * n) =
      (N : ℂ) * ∑ j : ZMod N, starRingEnd ℂ (Φ j) * Φ (j + n) := by
  simp only [dft_apply, map_sum, map_mul, smul_eq_mul]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_mul]
  have hchar (x y i : ZMod N) :
      (starRingEnd ℂ (stdAddChar (-(y * x))) * stdAddChar (-(i * x))) *
          stdAddChar (x * n) = stdAddChar ((y - i + n) * x) := by
    rw [← inv_apply_eq_conj, ← map_neg_eq_inv, ← map_add_eq_mul,
      ← map_add_eq_mul]
    congr 1
    ring
  have hinner (y i : ZMod N) :
      (∑ x : ZMod N,
        (starRingEnd ℂ (stdAddChar (-(y * x))) * starRingEnd ℂ (Φ y) *
          (stdAddChar (-(i * x)) * Φ i)) * stdAddChar (x * n)) =
        if i = y + n then (N : ℂ) * (starRingEnd ℂ (Φ y) * Φ i) else 0 := by
    calc
      _ = ∑ x : ZMod N, (starRingEnd ℂ (Φ y) * Φ i) *
          ((starRingEnd ℂ (stdAddChar (-(y * x))) * stdAddChar (-(i * x))) *
            stdAddChar (x * n)) := by
        apply Finset.sum_congr rfl
        intro x hx
        ring
      _ = (starRingEnd ℂ (Φ y) * Φ i) *
          ∑ x : ZMod N, stdAddChar ((y - i + n) * x) := by
        simp_rw [hchar]
        rw [Finset.mul_sum]
      _ = (starRingEnd ℂ (Φ y) * Φ i) *
          (if y - i + n = 0 then (N : ℂ) else 0) := by
        rw [character_sum]
      _ = if i = y + n then (N : ℂ) * (starRingEnd ℂ (Φ y) * Φ i) else 0 := by
        have heq : y - i + n = 0 ↔ i = y + n := by
          constructor <;> intro h
          · linear_combination -h
          · rw [h]
            abel
        simp only [heq]
        by_cases h : i = y + n <;> simp [h] <;> ring
  have hswap (y : ZMod N) :
      (∑ x : ZMod N, ∑ i : ZMod N,
        (starRingEnd ℂ (stdAddChar (-(y * x))) * starRingEnd ℂ (Φ y) *
          (stdAddChar (-(i * x)) * Φ i)) * stdAddChar (x * n)) =
      ∑ i : ZMod N,
        if i = y + n then (N : ℂ) * (starRingEnd ℂ (Φ y) * Φ i) else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    exact hinner y i
  simp_rw [hswap]
  simp

/-- Real norm-squared form of Parseval. -/
theorem sum_norm_sq_dft (Φ : ZMod N → ℂ) :
    ∑ k : ZMod N, ‖𝓕 Φ k‖ ^ 2 =
      (N : ℝ) * ∑ j : ZMod N, ‖Φ j‖ ^ 2 := by
  have h := congrArg Complex.re (dft_energy Φ)
  simp only [mul_comm, Complex.mul_conj,
    Complex.normSq_eq_norm_sq] at h
  norm_cast at h

end

end LocalCassels.ZModParseval
end

section
namespace LocalCassels.FiniteCyclicSpectral

open MeasureTheory Finset AddChar
open scoped BigOperators ComplexConjugate
open ZMod
open LocalCassels.ZModParseval

noncomputable section

local instance : MeasurableSpace Circle := borel Circle
local instance : BorelSpace Circle := ⟨rfl⟩

variable {N : ℕ} [NeZero N]

def energy (Φ : ZMod N → ℂ) : ℝ := ∑ j : ZMod N, ‖Φ j‖ ^ 2

def denom (Φ : ZMod N → ℂ) : ℝ := (N : ℝ) * energy Φ

private def spectralWeight (Φ : ZMod N → ℂ) (k : ZMod N) : ℝ :=
  ‖𝓕 Φ k‖ ^ 2 / denom Φ

private lemma sum_spectralWeight (Φ : ZMod N → ℂ) (hE : 0 < energy Φ) :
    ∑ k : ZMod N, spectralWeight Φ k = 1 := by
  rw [show (∑ k : ZMod N, spectralWeight Φ k) =
      (∑ k : ZMod N, ‖𝓕 Φ k‖ ^ 2) / denom Φ by
    simp [spectralWeight, sum_div]]
  rw [sum_norm_sq_dft]
  simp only [denom]
  change ((N : ℝ) * energy Φ) / ((N : ℝ) * energy Φ) = 1
  exact div_self (mul_ne_zero (by exact_mod_cast (NeZero.ne N)) hE.ne')

private def spectralPMF (Φ : ZMod N → ℂ) (hE : 0 < energy Φ) : PMF (ZMod N) :=
  PMF.ofFintype (fun k => ENNReal.ofReal (spectralWeight Φ k)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by
      unfold spectralWeight denom energy
      positivity)]
    rw [sum_spectralWeight Φ hE, ENNReal.ofReal_one])

private lemma spectralPMF_toReal (Φ : ZMod N → ℂ) (hE : 0 < energy Φ)
    (k : ZMod N) :
    ((spectralPMF Φ hE k).toReal) = spectralWeight Φ k := by
  rw [spectralPMF, PMF.ofFintype_apply, ENNReal.toReal_ofReal]
  unfold spectralWeight denom energy
  positivity

private def sourceProbability (Φ : ZMod N → ℂ) (hE : 0 < energy Φ) :
    ProbabilityMeasure (ZMod N) :=
  ⟨(spectralPMF Φ hE).toMeasure, inferInstance⟩

private def spectralProbability (Φ : ZMod N → ℂ) (hE : 0 < energy Φ) :
    ProbabilityMeasure Circle := by
  letI : MeasurableSpace (ZMod N) := ⊤
  exact (sourceProbability Φ hE).map
    (measurable_of_countable (ZMod.toCircle : ZMod N → Circle)).aemeasurable

/-- A nonzero finite cyclic signal has a circle-valued probability spectral
measure. Its Fourier coefficients are normalized cyclic autocorrelations, and
its atom at `1` is the normalized square of the signal sum. -/
theorem exists_cyclic_spectral_probability
    (Φ : ZMod N → ℂ) (hE : 0 < energy Φ) :
    ∃ ν : ProbabilityMeasure Circle,
      (∀ n : ℕ,
        (∫ z : Circle, (z : ℂ) ^ n ∂(ν : Measure Circle)) =
          (energy Φ)⁻¹ • ∑ j : ZMod N,
            starRingEnd ℂ (Φ j) * Φ (j + (n : ZMod N))) ∧
      (ν : Measure Circle).real {(1 : Circle)} =
        ‖∑ j : ZMod N, Φ j‖ ^ 2 / denom Φ := by
  letI : MeasurableSpace (ZMod N) := ⊤
  let p := spectralPMF Φ hE
  let ν₀ := sourceProbability Φ hE
  let ν := spectralProbability Φ hE
  refine ⟨ν, ?_, ?_⟩
  · intro n
    have hpow (k : ZMod N) : ((ZMod.toCircle k : Circle) : ℂ) ^ n =
        stdAddChar (k * (n : ZMod N)) := by
      change (stdAddChar k) ^ n = _
      rw [← stdAddChar.map_nsmul_eq_pow]
      congr 1
      simp [nsmul_eq_mul, mul_comm]
    have hmap : (ν : Measure Circle) =
        Measure.map (ZMod.toCircle : ZMod N → Circle) (p.toMeasure) := rfl
    rw [hmap, integral_map
      (measurable_of_countable (ZMod.toCircle : ZMod N → Circle)).aemeasurable
      (by fun_prop), PMF.integral_eq_sum]
    simp_rw [hpow]
    dsimp only [p]
    simp_rw [spectralPMF_toReal Φ hE]
    have hnorm (k : ZMod N) :
        (((‖𝓕 Φ k‖ ^ 2 : ℝ) : ℂ)) =
          starRingEnd ℂ (𝓕 Φ k) * 𝓕 Φ k := by
      rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
      ring
    have hnum :
        (∑ k : ZMod N, spectralWeight Φ k •
          stdAddChar (k * (n : ZMod N))) =
        (∑ k : ZMod N,
          (starRingEnd ℂ (𝓕 Φ k) * 𝓕 Φ k) *
            stdAddChar (k * (n : ZMod N))) / ((denom Φ : ℝ) : ℂ) := by
      rw [div_eq_mul_inv, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      rw [spectralWeight, Complex.real_smul, Complex.ofReal_div, hnorm]
      ring
    rw [hnum, dft_energy_character]
    rw [Complex.real_smul]
    unfold denom
    push_cast
    field_simp [show (N : ℂ) ≠ 0 by exact_mod_cast (NeZero.ne N), hE.ne']
  · have hmap : (ν : Measure Circle) =
        Measure.map (ZMod.toCircle : ZMod N → Circle) (p.toMeasure) := rfl
    rw [measureReal_def, hmap, Measure.map_apply_of_aemeasurable
      (measurable_of_countable (ZMod.toCircle : ZMod N → Circle)).aemeasurable
      (MeasurableSet.singleton 1)]
    have hpre : (ZMod.toCircle : ZMod N → Circle) ⁻¹' {(1 : Circle)} = {0} := by
      ext k
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro hk
        apply ZMod.injective_toCircle
        simpa using hk
      · rintro rfl
        simp
    rw [hpre, PMF.toMeasure_apply_singleton p 0 (MeasurableSet.singleton 0)]
    rw [spectralPMF_toReal Φ hE]
    simp only [spectralWeight, ZMod.dft_apply_zero]

end

end LocalCassels.FiniteCyclicSpectral
end

section
namespace LocalCassels.CyclicSpectralLimit

open Filter Topology MeasureTheory
open scoped BigOperators ComplexConjugate
open LocalCassels.FiniteCyclicSpectral

noncomputable section

local instance : MeasurableSpace Circle := borel Circle
local instance : BorelSpace Circle := ⟨rfl⟩
local instance (j : ℕ) : NeZero (3 * (j + 1)) := ⟨by omega⟩

abbrev M (j : ℕ) : ℕ := 3 * (j + 1)

def correlation (Φ : ∀ j : ℕ, ZMod (M j) → ℂ) (j n : ℕ) : ℂ :=
  (energy (Φ j))⁻¹ • ∑ k : ZMod (M j),
    starRingEnd ℂ (Φ j k) * Φ j (k + (n : ZMod (M j)))

/-- Shifted finite-embedding variant: if every positive short cyclic correlation
translates by `q j` into `S`, then the positivity set of one limiting spectral
measure is finitely embeddable in `S`. -/
theorem exists_limit_spectral_probability_finitely_embedded
    (Φ : ∀ j : ℕ, ZMod (M j) → ℂ)
    (q : ℕ → ℕ) (S : Set ℕ) (δ : ℝ)
    (hE : ∀ j : ℕ, 0 < energy (Φ j))
    (hatom : ∀ j : ℕ,
      δ ≤ ‖∑ k : ZMod (M j), Φ j k‖ ^ 2 / denom (Φ j))
    (hdetect : ∀ j n : ℕ, n < j + 1 →
      0 < (correlation Φ j n).re → n + q j ∈ S) :
    ∃ μ : ProbabilityMeasure Circle,
      δ ≤ (μ : Measure Circle).real {(1 : Circle)} ∧
      ∀ F : Finset ℕ,
        (∀ n ∈ F, 0 < (∫ z : Circle, (z : ℂ) ^ n ∂(μ : Measure Circle)).re) →
        ∃ r : ℕ, ∀ n ∈ F, n + r ∈ S := by
  choose ν hνcoeff hνatom using fun j =>
    exists_cyclic_spectral_probability (Φ j) (hE j)
  obtain ⟨p, hp⟩ := Ultrafilter.exists_le (atTop : Filter ℕ)
  let μ : ProbabilityMeasure Circle := Ultrafilter.extend ν p
  have hlim : Tendsto ν (p : Filter ℕ) (𝓝 μ) :=
    ultrafilter_extend_eq_iff.mp rfl
  have hatomENN : ∀ j : ℕ,
      ENNReal.ofReal δ ≤ (ν j : Measure Circle) {(1 : Circle)} := by
    intro j
    rw [← ofReal_measureReal]
    apply ENNReal.ofReal_le_ofReal
    rw [hνatom j]
    exact hatom j
  have hport := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto
    hlim (isClosed_singleton : IsClosed ({(1 : Circle)} : Set Circle))
  have hbounded : IsBoundedUnder (· ≤ ·) (p : Filter ℕ)
      (fun j => (ν j : Measure Circle) {(1 : Circle)}) := by
    apply isBoundedUnder_of_eventually_le (a := 1)
    exact Filter.Eventually.of_forall fun j => by
      calc
        (ν j : Measure Circle) {(1 : Circle)} ≤
            (ν j : Measure Circle) Set.univ := measure_mono (by simp)
        _ = 1 := measure_univ
  have hlower : ENNReal.ofReal δ ≤
      (p : Filter ℕ).limsup (fun j => (ν j : Measure Circle) {(1 : Circle)}) := by
    apply Filter.le_limsup_of_frequently_le (hu_le := hbounded)
    exact (Filter.Eventually.of_forall hatomENN).frequently
  have hμatomENN : ENNReal.ofReal δ ≤ (μ : Measure Circle) {(1 : Circle)} :=
    hlower.trans hport
  have hμatom : δ ≤ (μ : Measure Circle).real {(1 : Circle)} := by
    rw [measureReal_def]
    exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp hμatomENN
  have hcoefflim (n : ℕ) : Tendsto (fun j => correlation Φ j n) (p : Filter ℕ)
      (𝓝 (∫ z : Circle, (z : ℂ) ^ n ∂(μ : Measure Circle))) := by
    let f : ContinuousMap Circle ℂ := ⟨fun z => (z : ℂ) ^ n, by fun_prop⟩
    let fb : BoundedContinuousFunction Circle ℂ := BoundedContinuousFunction.mkOfCompact f
    have hall := (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp hlim
    have hint : Tendsto
        (fun j => ∫ z : Circle, (z : ℂ) ^ n ∂(ν j : Measure Circle))
        (p : Filter ℕ)
        (𝓝 (∫ z : Circle, (z : ℂ) ^ n ∂(μ : Measure Circle))) := by
      simpa [fb, f] using hall fb
    apply hint.congr'
    exact Filter.Eventually.of_forall (fun j => hνcoeff j n)
  refine ⟨μ, hμatom, ?_⟩
  intro F hF
  have hpos : ∀ᶠ j : ℕ in (p : Filter ℕ),
      ∀ n ∈ F, 0 < (correlation Φ j n).re := by
    rw [Finset.eventually_all]
    intro n hn
    have hrelim := (Complex.continuous_re.tendsto _).comp (hcoefflim n)
    exact (tendsto_order.1 hrelim).1 0 (hF n hn)
  let R : ℕ := ∑ n ∈ F, n
  have hlong : ∀ᶠ j : ℕ in (p : Filter ℕ), R < j + 1 := by
    apply hp
    exact eventually_atTop.2 ⟨R, by omega⟩
  obtain ⟨j, hjpos, hjlong⟩ := (hpos.and hlong).exists
  refine ⟨q j, ?_⟩
  intro n hn
  apply hdetect j n
  · have hnR : n ≤ R := by
      dsimp [R]
      exact Finset.single_le_sum (s := F) (f := fun m : ℕ => m)
        (fun _ _ => Nat.zero_le _) hn
    omega
  · exact hjpos n hn

end

end LocalCassels.CyclicSpectralLimit
end

section
namespace LocalCassels.IndicatorCyclicLimit

open Filter Topology MeasureTheory
open scoped BigOperators ComplexConjugate
open LocalCassels.FiniteCyclicSpectral LocalCassels.CyclicSpectralLimit

noncomputable section

local instance : MeasurableSpace Circle := borel Circle
local instance : BorelSpace Circle := ⟨rfl⟩
local instance (j : ℕ) : NeZero (M j) := ⟨by simp [M]⟩

/-- Shifted finite-embedding form for cyclic indicators. -/
theorem exists_spectral_probability_of_cyclic_indicators_finitely_embedded
    (P : ∀ j : ℕ, Finset (ZMod (M j)))
    (q : ℕ → ℕ) (S : Set ℕ) (δ : ℝ)
    (hP : ∀ j : ℕ, (P j).Nonempty)
    (hdensity : ∀ j : ℕ, δ ≤ (P j).card / (M j : ℝ))
    (hpair : ∀ j n : ℕ, n < j + 1 →
      ∀ k : ZMod (M j), k ∈ P j → k + (n : ZMod (M j)) ∈ P j →
        n + q j ∈ S) :
    ∃ μ : ProbabilityMeasure Circle,
      δ ≤ (μ : Measure Circle).real {(1 : Circle)} ∧
      ∀ F : Finset ℕ,
        (∀ n ∈ F, 0 < (∫ z : Circle, (z : ℂ) ^ n ∂(μ : Measure Circle)).re) →
        ∃ r : ℕ, ∀ n ∈ F, n + r ∈ S := by
  let Φ : ∀ j : ℕ, ZMod (M j) → ℂ := fun j k => if k ∈ P j then 1 else 0
  have henergy (j : ℕ) : energy (Φ j) = (P j).card := by
    unfold energy
    calc
      (∑ k : ZMod (M j), ‖Φ j k‖ ^ 2) =
          ∑ k : ZMod (M j), if k ∈ P j then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro k hk
        by_cases h : k ∈ P j <;> simp [Φ, h]
      _ = ∑ k ∈ P j, (1 : ℝ) := by
        rw [show (∑ k : ZMod (M j), if k ∈ P j then (1 : ℝ) else 0) =
          ∑ k ∈ Finset.univ, if k ∈ P j then (1 : ℝ) else 0 by rfl]
        rw [Finset.sum_ite_mem]
        simp
      _ = (P j).card := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  have hsum (j : ℕ) : ∑ k : ZMod (M j), Φ j k = ((P j).card : ℂ) := by
    calc
      (∑ k : ZMod (M j), Φ j k) =
          ∑ k : ZMod (M j), if k ∈ P j then (1 : ℂ) else 0 := by rfl
      _ = ∑ k ∈ P j, (1 : ℂ) := by
        rw [show (∑ k : ZMod (M j), if k ∈ P j then (1 : ℂ) else 0) =
          ∑ k ∈ Finset.univ, if k ∈ P j then (1 : ℂ) else 0 by rfl]
        rw [Finset.sum_ite_mem]
        simp
      _ = ((P j).card : ℂ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  have hE : ∀ j : ℕ, 0 < energy (Φ j) := by
    intro j
    rw [henergy]
    exact_mod_cast (P j).card_pos.mpr (hP j)
  have hatom : ∀ j : ℕ,
      δ ≤ ‖∑ k : ZMod (M j), Φ j k‖ ^ 2 / denom (Φ j) := by
    intro j
    rw [hsum]
    unfold denom
    rw [henergy, Complex.norm_natCast]
    have hcard : (0 : ℝ) < (P j).card := by
      exact_mod_cast (P j).card_pos.mpr (hP j)
    calc
      δ ≤ (P j).card / (M j : ℝ) := hdensity j
      _ = ((P j).card : ℝ) ^ 2 /
          ((M j : ℝ) * (P j).card) := by field_simp
  have hdetect : ∀ j n : ℕ, n < j + 1 →
      0 < (correlation Φ j n).re → n + q j ∈ S := by
    intro j n hn hpos
    have hne : (∑ k : ZMod (M j),
        starRingEnd ℂ (Φ j k) * Φ j (k + (n : ZMod (M j)))) ≠ 0 := by
      intro hz
      have : correlation Φ j n = 0 := by
        unfold correlation
        rw [hz, smul_zero]
      rw [this] at hpos
      simp at hpos
    obtain ⟨k, hk, hkne⟩ := Finset.exists_ne_zero_of_sum_ne_zero
      (s := Finset.univ) hne
    simp only [Finset.mem_univ] at hk
    have hkP : k ∈ P j := by
      by_contra h
      simp [Φ, h] at hkne
    have hknP : k + (n : ZMod (M j)) ∈ P j := by
      by_contra h
      simp [Φ, h] at hkne
    exact hpair j n hn k hkP hknP
  exact exists_limit_spectral_probability_finitely_embedded Φ q S δ hE hatom hdetect

end

end LocalCassels.IndicatorCyclicLimit
end

section
namespace LocalCassels.FiniteBlockSpectral

open MeasureTheory
open scoped BigOperators
open LocalCassels.CyclicSpectralLimit LocalCassels.IndicatorCyclicLimit

noncomputable section

local instance : MeasurableSpace Circle := borel Circle
local instance : BorelSpace Circle := ⟨rfl⟩
local instance (j : ℕ) : NeZero (M j) := ⟨by simp [M]⟩

private def embedBlock (j x : ℕ) : ZMod (M j) := (j + 1 + x : ℕ)

/-- Shifted finite-embedding version for ordinary finite blocks. -/
theorem exists_spectral_probability_of_dense_blocks_finitely_embedded
    (B : ℕ → Finset ℕ) (q : ℕ → ℕ) (S : Set ℕ) (δ : ℝ)
    (hBbound : ∀ j x : ℕ, x ∈ B j → x < j + 1)
    (hBnonempty : ∀ j : ℕ, (B j).Nonempty)
    (hdensity : ∀ j : ℕ, δ ≤ (B j).card / (M j : ℝ))
    (hdiff : ∀ j x y n : ℕ,
      x ∈ B j → y ∈ B j → y = x + n → n + q j ∈ S) :
    ∃ μ : ProbabilityMeasure Circle,
      δ ≤ (μ : Measure Circle).real {(1 : Circle)} ∧
      ∀ F : Finset ℕ,
        (∀ n ∈ F, 0 < (∫ z : Circle, (z : ℂ) ^ n ∂(μ : Measure Circle)).re) →
        ∃ r : ℕ, ∀ n ∈ F, n + r ∈ S := by
  let P : ∀ j : ℕ, Finset (ZMod (M j)) := fun j =>
    (B j).image (embedBlock j)
  have hinj (j : ℕ) : Set.InjOn (embedBlock j) (B j : Set ℕ) := by
    intro x hx y hy hxy
    have hxlt : j + 1 + x < M j := by
      have := hBbound j x hx
      simp only [M]
      omega
    have hylt : j + 1 + y < M j := by
      have := hBbound j y hy
      simp only [M]
      omega
    have hv := congrArg ZMod.val hxy
    change ((j + 1 + x : ℕ) : ZMod (M j)).val =
      ((j + 1 + y : ℕ) : ZMod (M j)).val at hv
    rw [ZMod.val_natCast_of_lt hxlt, ZMod.val_natCast_of_lt hylt] at hv
    omega
  have hcard (j : ℕ) : (P j).card = (B j).card := by
    apply Finset.card_image_iff.mpr
    exact hinj j
  have hP : ∀ j : ℕ, (P j).Nonempty := by
    intro j
    obtain ⟨x, hx⟩ := hBnonempty j
    exact ⟨embedBlock j x, Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩
  have hPdensity : ∀ j : ℕ, δ ≤ (P j).card / (M j : ℝ) := by
    intro j
    rw [hcard]
    exact hdensity j
  have hpair : ∀ j n : ℕ, n < j + 1 →
      ∀ k : ZMod (M j), k ∈ P j → k + (n : ZMod (M j)) ∈ P j →
        n + q j ∈ S := by
    intro j n hn k hk hkn
    rw [Finset.mem_image] at hk hkn
    obtain ⟨x, hxB, rfl⟩ := hk
    obtain ⟨y, hyB, hEq⟩ := hkn
    have hxlt := hBbound j x hxB
    have hylt := hBbound j y hyB
    have hleftlt : j + 1 + x + n < M j := by
      simp only [M]
      omega
    have hyembedlt : j + 1 + y < M j := by
      simp only [M]
      omega
    have hcast : ((j + 1 + x + n : ℕ) : ZMod (M j)) =
        ((j + 1 + y : ℕ) : ZMod (M j)) := by
      simpa [embedBlock, Nat.cast_add] using hEq.symm
    have hv := congrArg ZMod.val hcast
    rw [ZMod.val_natCast_of_lt hleftlt,
      ZMod.val_natCast_of_lt hyembedlt] at hv
    apply hdiff j x y n hxB hyB
    omega
  exact exists_spectral_probability_of_cyclic_indicators_finitely_embedded
    P q S δ hP hPdensity hpair

end

end LocalCassels.FiniteBlockSpectral
end

section
namespace LocalCassels.SyndeticCrossSpectralEmbedding

open MeasureTheory
open scoped BigOperators
open LocalCassels.SyndeticDensityBlocks LocalCassels.CrossAlignment LocalCassels.DenseChunk
open LocalCassels.FiniteBlockSpectral LocalCassels.CyclicSpectralLimit

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p
local instance : MeasurableSpace Circle := borel Circle
local instance : BorelSpace Circle := ⟨rfl⟩

/-- Finite cyclic alignment of two syndetic sets, followed by spectral
compactness, produces a positive-trivial-atom spectral measure whose positivity
set is finitely embeddable in their sumset. -/
theorem exists_cross_spectral_finite_embedding
    (S₀ S₁ : Set ℕ)
    (h₀ : ∃ K : ℕ, ∀ n : ℕ, ∃ s : ℕ,
      s ∈ S₀ ∧ s ≤ n ∧ n ≤ s + K)
    (h₁ : ∃ K : ℕ, ∀ n : ℕ, ∃ s : ℕ,
      s ∈ S₁ ∧ s ≤ n ∧ n ≤ s + K) :
    ∃ μ : ProbabilityMeasure Circle,
      0 < (μ : Measure Circle).real {(1 : Circle)} ∧
      ∀ F : Finset ℕ,
        (∀ n ∈ F, 0 < (∫ z : Circle, (z : ℂ) ^ n ∂(μ : Measure Circle)).re) →
        ∃ r : ℕ, ∀ n ∈ F,
          n + r ∈ {x | ∃ s₀ ∈ S₀, ∃ s₁ ∈ S₁, s₀ + s₁ = x} := by
  obtain ⟨K₀, hS₀⟩ := h₀
  obtain ⟨K₁, hS₁⟩ := h₁
  let Q₀ := K₀ + 1
  let Q₁ := K₁ + 1
  let R := Q₀ * Q₁
  have hQ₀ : 0 < Q₀ := by dsimp [Q₀]; omega
  have hQ₁ : 0 < Q₁ := by dsimp [Q₁]; omega
  have hR : 0 < R := mul_pos hQ₀ hQ₁
  have hex : ∀ j : ℕ, ∃ q : ℕ, ∃ B : Finset ℕ,
      (∀ x ∈ B, x < j + 1) ∧ B.Nonempty ∧
      (j + 1 ≤ 2 * R * B.card) ∧
      ∀ x ∈ B, ∀ y ∈ B, ∀ n : ℕ, y = x + n →
        n + q ∈ {z | ∃ s₀ ∈ S₀, ∃ s₁ ∈ S₁, s₀ + s₁ = z} := by
    intro j
    let m := j + 1
    let L := m * R
    let A : Finset ℕ := (Finset.range L).filter (fun x => x ∈ S₀)
    let B₁ : Finset ℕ := (Finset.range L).filter (fun x => x ∈ S₁)
    have hAbound : ∀ x ∈ A, x < L := by
      intro x hx
      exact Finset.mem_range.mp (Finset.mem_filter.mp hx).1
    have hB₁bound : ∀ x ∈ B₁, x < L := by
      intro x hx
      exact Finset.mem_range.mp (Finset.mem_filter.mp hx).1
    have hAcard : m * Q₁ ≤ A.card := by
      have h := card_filter_range_mul_lower S₀ K₀ (m * Q₁) hS₀
      simpa [A, L, R, Q₀, Q₁, Nat.mul_assoc, Nat.mul_left_comm,
        Nat.mul_comm] using h
    have hB₁card : m * Q₀ ≤ B₁.card := by
      have h := card_filter_range_mul_lower S₁ K₁ (m * Q₀) hS₁
      simpa [B₁, L, R, Q₀, Q₁, Nat.mul_assoc, Nat.mul_left_comm,
        Nat.mul_comm] using h
    obtain ⟨q, hq, C, hCcard, hC⟩ :=
      exists_large_exact_sum_fiber A B₁ L (by dsimp [L, m]; positivity)
        hAbound hB₁bound
    have hCbound : ∀ x ∈ C, x < m * R := by
      intro x hx
      have := (hC x hx).1
      exact hAbound x this
    obtain ⟨c, hcR, B, hchunk, hB⟩ :=
      exists_dense_chunk C m R (by dsimp [m]; omega) hR hCbound
    have hmC : m ≤ 2 * C.card := by
      have hlower : (m * Q₁) * (m * Q₀) ≤ A.card * B₁.card :=
        Nat.mul_le_mul hAcard hB₁card
      have htotal : (m * Q₁) * (m * Q₀) ≤ (2 * L) * C.card :=
        hlower.trans hCcard
      have hfactor : 0 < m * R := mul_pos (by dsimp [m]; omega) hR
      apply Nat.le_of_mul_le_mul_left (c := m * R) _ hfactor
      calc
        (m * R) * m = (m * Q₁) * (m * Q₀) := by
          dsimp [R]
          ring
        _ ≤ (2 * L) * C.card := htotal
        _ = (m * R) * (2 * C.card) := by
          dsimp [L]
          ring
    have hmB : m ≤ 2 * R * B.card := by
      exact hmC.trans <| by nlinarith [hchunk]
    have hBnonempty : B.Nonempty := Finset.card_pos.mp (by
      by_contra hnot
      have hc : B.card = 0 := Nat.eq_zero_of_not_pos hnot
      rw [hc] at hmB
      simp at hmB)
    refine ⟨q, B, ?_, hBnonempty, ?_, ?_⟩
    · intro x hx
      exact (hB x hx).1
    · simpa [m] using hmB
    · intro x hx y hy n hyn
      have hxC := (hB x hx).2
      have hyC := (hB y hy).2
      have hxdata := hC (c * m + x) hxC
      have hydata := hC (c * m + y) hyC
      obtain ⟨hxA, b, hbB₁, hxsum⟩ := hxdata
      have hyA := hydata.1
      refine ⟨c * m + y, ?_, b, ?_, ?_⟩
      · exact (Finset.mem_filter.mp hyA).2
      · exact (Finset.mem_filter.mp hbB₁).2
      · omega
  choose q B hBbound hBnonempty hmB hdiff using hex
  let δ : ℝ := 1 / (6 * R)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hdensity : ∀ j : ℕ, δ ≤ (B j).card / (M j : ℝ) := by
    intro j
    have hm := hmB j
    dsimp [δ]
    simp only [M]
    push_cast
    have hm' : ((j + 1 : ℕ) : ℝ) ≤ 2 * R * (B j).card := by exact_mod_cast hm
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hscaled : 3 * ((j + 1 : ℕ) : ℝ) ≤
        6 * R * ((B j).card : ℝ) := by nlinarith [hm']
    simpa [mul_assoc, mul_left_comm, mul_comm] using hscaled
  obtain ⟨μ, hμatom, hembed⟩ :=
    exists_spectral_probability_of_dense_blocks_finitely_embedded
      B q {z | ∃ s₀ ∈ S₀, ∃ s₁ ∈ S₁, s₀ + s₁ = z} δ
      hBbound hBnonempty hdensity
      (fun j x y n hx hy hxy => hdiff j x hx y hy n hxy)
  exact ⟨μ, hδ.trans_le hμatom, hembed⟩

end

end LocalCassels.SyndeticCrossSpectralEmbedding
end

section
namespace LocalCassels.AtomicDecomposition

open MeasureTheory

noncomputable section

local instance : MeasurableSpace Circle := borel Circle
local instance : BorelSpace Circle := ⟨rfl⟩

/-- The points carrying positive mass for a measure. -/
def atomSet (μ : Measure Circle) : Set Circle := {z | μ {z} ≠ 0}

lemma atomSet_countable (μ : Measure Circle) [SFinite μ] :
    (atomSet μ).Countable := by
  have h := Measure.countable_meas_level_set_pos (μ := μ)
    (g := fun z : Circle => z) measurable_id
  simpa [atomSet, pos_iff_ne_zero] using h

lemma atomSet_measurable (μ : Measure Circle) [SFinite μ] :
    MeasurableSet (atomSet μ) := (atomSet_countable μ).measurableSet

/-- The restriction away from all point masses. -/
def continuousPart (μ : Measure Circle) : Measure Circle :=
  μ.restrict (atomSet μ)ᶜ

instance continuousPart_isFinite (μ : Measure Circle) [IsFiniteMeasure μ] :
    IsFiniteMeasure (continuousPart μ) := by
  unfold continuousPart
  infer_instance

instance continuousPart_noAtoms (μ : Measure Circle) [SFinite μ] :
    NullSingletonClass (continuousPart μ) := by
  constructor
  intro z
  change (μ.restrict (atomSet μ)ᶜ) {z} = 0
  rw [Measure.restrict_apply (MeasurableSet.singleton z)]
  by_cases hz : μ {z} = 0
  · exact measure_mono_null Set.inter_subset_left hz
  · have hzA : z ∈ atomSet μ := hz
    have hempty : {z} ∩ (atomSet μ)ᶜ = ∅ := by
      ext x
      change (x = z ∧ x ∉ atomSet μ) ↔ False
      constructor
      · rintro ⟨rfl, hnot⟩
        exact hnot hzA
      · exact False.elim
    rw [hempty, measure_empty]

theorem summable_atom_weights (μ : Measure Circle) [IsFiniteMeasure μ] :
    Summable (fun z : atomSet μ => μ.real {(z : Circle)}) := by
  apply summable_of_sum_le (fun _ => measureReal_nonneg)
  intro s
  apply sum_measureReal_le_measureReal_univ
  · intro z hz
    exact MeasurableSet.singleton _
  · intro z hz w hw hzw
    exact Set.disjoint_singleton.mpr (fun h => hzw (Subtype.ext h))

/-- A finite measure is the sum of its restriction to its point-mass set and
an atomless remainder. The atomic integral is explicitly a countable sum. -/
theorem integral_eq_atomic_add_continuous
    (μ : Measure Circle) [IsFiniteMeasure μ]
    (f : Circle → ℂ) (hf : Integrable f μ) :
    (∫ z, f z ∂μ) =
      (∑' z : atomSet μ, μ.real {(z : Circle)} • f z) +
      ∫ z, f z ∂(continuousPart μ) := by
  have hA := atomSet_measurable μ
  have hsplit := Measure.restrict_add_restrict_compl (μ := μ) hA
  calc
    (∫ z, f z ∂μ) =
        ∫ z, f z ∂(μ.restrict (atomSet μ) + μ.restrict (atomSet μ)ᶜ) := by
      rw [hsplit]
    _ = (∫ z, f z ∂(μ.restrict (atomSet μ))) +
        ∫ z, f z ∂(μ.restrict (atomSet μ)ᶜ) :=
      integral_add_measure hf.restrict hf.restrict
    _ = (∑' z : atomSet μ, μ.real {(z : Circle)} • f z) +
        ∫ z, f z ∂(continuousPart μ) := by
      rw [setIntegral_countable f (atomSet_countable μ) hf.restrict]
      rfl

end

end LocalCassels.AtomicDecomposition
end

section
namespace LocalCassels.CesaroGeometric

open Filter Topology
open scoped BigOperators

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Cesàro averages of the powers of a nontrivial point of the complex unit
circle tend to zero. -/
theorem tendsto_cesaro_powers_circle_zero
    (z : Circle) (hz : (z : ℂ) ≠ 1) :
    Tendsto
      (fun N : ℕ => (N : ℝ)⁻¹ • ∑ n ∈ Finset.range N, (z : ℂ) ^ n)
      atTop (𝓝 0) := by
  have heps : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  apply NormedField.tendsto_zero_smul_of_tendsto_zero_of_bounded heps
  apply isBoundedUnder_of_eventually_le
    (a := 2 / ‖(z : ℂ) - 1‖)
  filter_upwards [] with N
  dsimp only [Function.comp_apply]
  rw [geom_sum_eq hz]
  rw [norm_div]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  calc
    ‖(z : ℂ) ^ N - 1‖ ≤ ‖(z : ℂ) ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by norm_num

/-- The same geometric Cesàro kernel converges to the diagonal indicator. -/
theorem tendsto_cesaro_powers_circle
    (z : Circle) :
    Tendsto
      (fun N : ℕ => (N : ℝ)⁻¹ • ∑ n ∈ Finset.range N, (z : ℂ) ^ n)
      atTop (𝓝 (if z = 1 then 1 else 0)) := by
  by_cases hz : z = 1
  · subst z
    simp only [Circle.coe_one, one_pow, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one]
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    symm
    rw [Complex.real_smul]
    push_cast
    exact inv_mul_cancel₀ (show (N : ℂ) ≠ 0 by exact_mod_cast hN.ne')
  · have hz' : (z : ℂ) ≠ 1 := by
      intro h
      apply hz
      exact Subtype.ext h
    simpa [hz] using tendsto_cesaro_powers_circle_zero z hz'

end

end LocalCassels.CesaroGeometric
end

section
namespace LocalCassels.AtomlessWiener

open Filter Topology MeasureTheory
open scoped BigOperators

noncomputable section

local instance : MeasurableSpace Circle := borel Circle
local instance : BorelSpace Circle := ⟨rfl⟩

private def kernel (N : ℕ) (p : Circle × Circle) : ℂ :=
  (N : ℝ)⁻¹ • ∑ n ∈ Finset.range N, ((p.1⁻¹ * p.2 : Circle) : ℂ) ^ n

private lemma kernel_continuous (N : ℕ) : Continuous (kernel N) := by
  unfold kernel
  fun_prop

private lemma norm_kernel_le_one (N : ℕ) (p : Circle × Circle) :
    ‖kernel N p‖ ≤ 1 := by
  by_cases hN : N = 0
  · subst N
    simp [kernel]
  have hsum : ‖∑ n ∈ Finset.range N, ((p.1⁻¹ * p.2 : Circle) : ℂ) ^ n‖ ≤ N := by
    calc
      ‖∑ n ∈ Finset.range N, ((p.1⁻¹ * p.2 : Circle) : ℂ) ^ n‖ ≤
          ∑ n ∈ Finset.range N, ‖((p.1⁻¹ * p.2 : Circle) : ℂ) ^ n‖ :=
        norm_sum_le _ _
      _ = N := by simp
  rw [kernel, norm_smul]
  calc
    ‖(N : ℝ)⁻¹‖ * ‖∑ n ∈ Finset.range N,
        ((p.1⁻¹ * p.2 : Circle) : ℂ) ^ n‖ ≤ ‖(N : ℝ)⁻¹‖ * N :=
      mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
    _ = 1 := by
      rw [Real.norm_eq_abs, abs_inv, abs_of_nonneg (by positivity)]
      exact inv_mul_cancel₀ (by exact_mod_cast hN)

private def coeff (μ : Measure Circle) (n : ℕ) : ℂ :=
  ∫ z : Circle, (z : ℂ) ^ n ∂μ

private lemma integral_ratio_pow
    (μ : Measure Circle) [IsFiniteMeasure μ] (n : ℕ) :
    (∫ p : Circle × Circle, (((p.1⁻¹ * p.2 : Circle) : ℂ) ^ n) ∂(μ.prod μ)) =
      starRingEnd ℂ (coeff μ n) * coeff μ n := by
  have hfun : (fun p : Circle × Circle =>
      (((p.1⁻¹ * p.2 : Circle) : ℂ) ^ n)) =
      (fun p => starRingEnd ℂ ((p.1 : ℂ) ^ n) * (p.2 : ℂ) ^ n) := by
    funext p
    change (((p.1 : ℂ)⁻¹ * (p.2 : ℂ)) ^ n) = _
    have hz : (p.1 : ℂ)⁻¹ = starRingEnd ℂ (p.1 : ℂ) :=
      Circle.coe_inv_eq_conj p.1
    rw [hz, mul_pow, map_pow]
  rw [hfun]
  have hp := integral_prod_mul (μ := μ) (ν := μ)
    (fun z : Circle => starRingEnd ℂ ((z : ℂ) ^ n))
    (fun z : Circle => (z : ℂ) ^ n)
  rw [integral_conj] at hp
  exact hp

private lemma integral_kernel_eq
    (μ : Measure Circle) [IsFiniteMeasure μ] (N : ℕ) :
    (∫ p : Circle × Circle, kernel N p ∂(μ.prod μ)) =
      (((N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, ‖coeff μ n‖ ^ 2 : ℝ) : ℂ) := by
  unfold kernel
  rw [integral_smul]
  have hint : ∀ n ∈ Finset.range N,
      Integrable (fun p : Circle × Circle =>
        (((p.1⁻¹ * p.2 : Circle) : ℂ) ^ n)) (μ.prod μ) := by
    intro n hn
    apply Integrable.of_bound (by fun_prop) 1
    exact Filter.Eventually.of_forall (by intro p; simp)
  rw [integral_finsetSum _ hint]
  simp_rw [integral_ratio_pow μ]
  rw [Complex.ofReal_mul, Complex.ofReal_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- For an atomless finite measure on the circle, the integral of the Cesàro
geometric kernel on the square tends to zero. This is the dominated-convergence
core of Wiener's lemma. -/
theorem tendsto_integral_cesaro_kernel_atomless
    (μ : Measure Circle) [IsFiniteMeasure μ] [NullSingletonClass μ] :
    Tendsto (fun N : ℕ => ∫ p : Circle × Circle, kernel N p ∂(μ.prod μ))
      atTop (𝓝 0) := by
  have hdiag : (μ.prod μ) (Set.diagonal Circle) = 0 := by
    rw [Measure.prod_apply measurableSet_diagonal]
    simp [Set.diagonal]
  have ht := tendsto_integral_of_dominated_convergence
    (μ := μ.prod μ) (F := kernel) (f := fun _ => (0 : ℂ)) (fun _ => (1 : ℝ))
    (fun N => (kernel_continuous N).aestronglyMeasurable)
    (integrable_const 1)
    (fun N => Filter.Eventually.of_forall (norm_kernel_le_one N))
    (by
      have hne : ∀ᵐ p : Circle × Circle ∂(μ.prod μ), p.1 ≠ p.2 := by
        apply ae_iff.mpr
        simpa [Set.diagonal] using hdiag
      filter_upwards [hne] with p hp
      have hq : p.1⁻¹ * p.2 ≠ (1 : Circle) := by
        intro h
        apply hp
        simpa only [inv_mul_eq_one] using h
      simpa [kernel, hq] using
        LocalCassels.CesaroGeometric.tendsto_cesaro_powers_circle (p.1⁻¹ * p.2))
  simpa using ht

/-- Atomless Wiener's lemma: the squared moduli of the Fourier coefficients of
an atomless finite circle measure have Cesàro mean zero. -/
theorem tendsto_cesaro_sq_fourier_atomless
    (μ : Measure Circle) [IsFiniteMeasure μ] [NullSingletonClass μ] :
    Tendsto
      (fun N : ℕ => (N : ℝ)⁻¹ *
        ∑ n ∈ Finset.range N, ‖∫ z : Circle, (z : ℂ) ^ n ∂μ‖ ^ 2)
      atTop (𝓝 0) := by
  have ht := tendsto_integral_cesaro_kernel_atomless μ
  have hc : Tendsto
      (fun N : ℕ => (((N : ℝ)⁻¹ *
        ∑ n ∈ Finset.range N, ‖coeff μ n‖ ^ 2 : ℝ) : ℂ))
      atTop (𝓝 0) := by
    apply ht.congr'
    exact Filter.Eventually.of_forall (integral_kernel_eq μ)
  have hre := (Complex.continuous_re.tendsto 0).comp hc
  change Tendsto
    (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, ‖coeff μ n‖ ^ 2)
    atTop (𝓝 0) at hre
  simpa [coeff] using hre

end

end LocalCassels.AtomlessWiener
end

section
namespace LocalCassels.SpectralWienerDecomposition

open Filter Topology MeasureTheory
open scoped BigOperators
open LocalCassels.AtomicDecomposition

noncomputable section

local instance : MeasurableSpace Circle := borel Circle
local instance : BorelSpace Circle := ⟨rfl⟩

/-- The pure-point Fourier part of a finite circle measure. -/
def atomicCoeff (μ : Measure Circle) (n : ℕ) : ℂ :=
  ∑' z : atomSet μ, μ.real {(z : Circle)} • ((z : Circle) : ℂ) ^ n

/-- The Fourier coefficient of the atomless remainder. -/
def continuousCoeff (μ : Measure Circle) (n : ℕ) : ℂ :=
  ∫ z : Circle, (z : ℂ) ^ n ∂(continuousPart μ)

private lemma integrable_pow (μ : Measure Circle) [IsFiniteMeasure μ] (n : ℕ) :
    Integrable (fun z : Circle => (z : ℂ) ^ n) μ := by
  apply Integrable.of_bound (by fun_prop) 1
  exact Filter.Eventually.of_forall (by intro z; simp)

lemma coeff_eq_atomic_add_continuous
    (μ : Measure Circle) [IsFiniteMeasure μ] (n : ℕ) :
    (∫ z : Circle, (z : ℂ) ^ n ∂μ) = atomicCoeff μ n + continuousCoeff μ n := by
  simpa [atomicCoeff, continuousCoeff] using
    integral_eq_atomic_add_continuous μ (fun z : Circle => (z : ℂ) ^ n)
      (integrable_pow μ n)

lemma tendsto_cesaro_sq_re_continuousCoeff
    (μ : Measure Circle) [IsFiniteMeasure μ] :
    Tendsto
      (fun N : ℕ => (N : ℝ)⁻¹ *
        ∑ n ∈ Finset.range N, (continuousCoeff μ n).re ^ 2)
      atTop (𝓝 0) := by
  have htop := LocalCassels.AtomlessWiener.tendsto_cesaro_sq_fourier_atomless
    (continuousPart μ)
  apply Filter.Tendsto.squeeze tendsto_const_nhds htop
  · intro N
    positivity
  · intro N
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Finset.sum_le_sum
    intro n hn
    change (continuousCoeff μ n).re ^ 2 ≤ ‖continuousCoeff μ n‖ ^ 2
    rw [sq_le_sq]
    simpa only [abs_of_nonneg (norm_nonneg _)] using
      Complex.abs_re_le_norm (continuousCoeff μ n)

lemma summable_atomic_terms (μ : Measure Circle) [IsFiniteMeasure μ] (n : ℕ) :
    Summable (fun z : atomSet μ =>
      μ.real {(z : Circle)} • ((z : Circle) : ℂ) ^ n) := by
  apply Summable.of_norm
  simpa [norm_smul, Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg] using
    summable_atom_weights μ

lemma atomicCoeff_zero_re (μ : Measure Circle) [IsFiniteMeasure μ] :
    (atomicCoeff μ 0).re = ∑' z : atomSet μ, μ.real {(z : Circle)} := by
  unfold atomicCoeff
  simp only [pow_zero, Complex.real_smul, mul_one]
  change Complex.reCLM (∑' z : atomSet μ,
    ((μ.real {(z : Circle)} : ℝ) : ℂ)) = _
  have hs : Summable (fun z : atomSet μ =>
      ((μ.real {(z : Circle)} : ℝ) : ℂ)) := by
    simpa only [Complex.ofRealCLM_apply] using
      Complex.ofRealCLM.summable (summable_atom_weights μ)
  rw [Complex.reCLM.map_tsum hs]
  simp

lemma singleton_one_mass_le_atomicCoeff_zero
    (μ : Measure Circle) [IsFiniteMeasure μ] :
    μ.real {(1 : Circle)} ≤ (atomicCoeff μ 0).re := by
  rw [atomicCoeff_zero_re]
  by_cases h1 : μ {(1 : Circle)} = 0
  · rw [measureReal_def, h1, ENNReal.toReal_zero]
    exact tsum_nonneg (fun _ => measureReal_nonneg)
  · let z1 : atomSet μ := ⟨1, h1⟩
    exact (summable_atom_weights μ).le_tsum z1
      (fun _ _ => measureReal_nonneg)

/-- The atomic Fourier series is uniformly approximable in the time variable
by one finite set of atoms. -/
theorem exists_finite_atomic_approximation
    (μ : Measure Circle) [IsFiniteMeasure μ]
    (ε : ℝ) (hε : 0 < ε) :
    ∃ F : Finset (atomSet μ), ∀ n : ℕ,
      ‖atomicCoeff μ n -
        ∑ z ∈ F, μ.real {(z : Circle)} • ((z : Circle) : ℂ) ^ n‖ < ε := by
  let w : atomSet μ → ℝ := fun z => μ.real {(z : Circle)}
  have hw : Summable w := summable_atom_weights μ
  have ht := tendsto_tsum_compl_atTop_zero w
  have hevent := (tendsto_order.1 ht).2 ε hε
  obtain ⟨F₀, hF₀⟩ := eventually_atTop.1 hevent
  refine ⟨F₀, ?_⟩
  intro n
  let f : atomSet μ → ℂ := fun z =>
    μ.real {(z : Circle)} • ((z : Circle) : ℂ) ^ n
  have hf : Summable f := summable_atomic_terms μ n
  have hsplit := hf.sum_add_tsum_subtype_compl F₀
  have hatomic : atomicCoeff μ n = ∑' z, f z := by
    unfold atomicCoeff
    congr 1
  have hdiff : atomicCoeff μ n - ∑ z ∈ F₀, f z =
      ∑' z : {z // z ∉ F₀}, f z := by
    rw [hatomic, ← hsplit]
    abel
  rw [show (∑ z ∈ F₀, μ.real {(z : Circle)} •
      ((z : Circle) : ℂ) ^ n) = ∑ z ∈ F₀, f z by rfl, hdiff]
  calc
    ‖∑' z : {z // z ∉ F₀}, f z‖ ≤
        ∑' z : {z // z ∉ F₀}, ‖f z‖ := by
      apply norm_tsum_le_tsum_norm
      exact hf.norm.subtype _
    _ = ∑' z : {z // z ∉ F₀}, w z := by
      apply tsum_congr
      intro z
      simp [f, w, Real.norm_eq_abs,
        abs_of_nonneg measureReal_nonneg]
    _ < ε := hF₀ F₀ le_rfl

end

end LocalCassels.SpectralWienerDecomposition
end

section
namespace LocalCassels.AtomicBohrLower

open MeasureTheory
open scoped BigOperators Topology
open LocalCassels.AtomicDecomposition LocalCassels.SpectralWienerDecomposition

noncomputable section

local instance : MeasurableSpace Circle := borel Circle
local instance : BorelSpace Circle := ⟨rfl⟩

/-- A positive atom at the trivial character gives a finite-dimensional Bohr
neighborhood on which the full atomic Fourier series stays uniformly positive. -/
theorem exists_finite_circle_bohr_atomic_lower
    (μ : Measure Circle) [IsFiniteMeasure μ]
    (δ : ℝ) (hδ : 0 < δ) (hδatom : δ ≤ μ.real {(1 : Circle)}) :
    ∃ d : ℕ, ∃ a : Fin d → Circle, ∃ U : Set (Fin d → Circle),
      IsOpen U ∧ (fun _ => (1 : Circle)) ∈ U ∧
      ∀ n : ℕ, (fun i => a i ^ n) ∈ U → δ / 2 < (atomicCoeff μ n).re := by
  obtain ⟨F, hF⟩ := exists_finite_atomic_approximation μ (δ / 8) (by positivity)
  let e : Fin F.card ≃ {z : atomSet μ // z ∈ F} := F.equivFin.symm
  let a : Fin F.card → Circle := fun i => ((e i : atomSet μ) : Circle)
  let mass : ℝ := ∑ z ∈ F, μ.real {(z : Circle)}
  let g : (Fin F.card → Circle) → ℝ := fun x =>
    (∑ i : Fin F.card,
      ((μ.real {((e i : atomSet μ) : Circle)} : ℝ) : ℂ) * (x i : ℂ)).re
  let U : Set (Fin F.card → Circle) := {x | mass - δ / 8 < g x}
  have hg : Continuous g := by
    dsimp [g]
    fun_prop
  have hUopen : IsOpen U := hg.isOpen_preimage _ isOpen_Ioi
  have hsum_e (q : atomSet μ → ℂ) :
      (∑ i : Fin F.card, q (e i)) = ∑ z ∈ F, q z := by
    calc
      (∑ i : Fin F.card, q (e i)) =
          ∑ z : {z : atomSet μ // z ∈ F}, q z :=
        e.sum_comp (fun z : {z : atomSet μ // z ∈ F} => q z)
      _ = ∑ z ∈ F, q z := Finset.sum_coe_sort F q
  have hg_one : g (fun _ => (1 : Circle)) = mass := by
    dsimp [g, mass]
    simp only [mul_one]
    have hs := hsum_e (fun z : atomSet μ =>
      ((μ.real {(z : Circle)} : ℝ) : ℂ))
    rw [hs]
    simp
  have hone : (fun _ => (1 : Circle)) ∈ U := by
    dsimp [U]
    rw [hg_one]
    linarith [hδ]
  refine ⟨F.card, a, U, hUopen, hone, ?_⟩
  intro n hnU
  have hfinite : g (fun i => a i ^ n) =
      (∑ z ∈ F, μ.real {(z : Circle)} • (((z : atomSet μ) : Circle) : ℂ) ^ n).re := by
    dsimp only [g]
    have hpow (i : Fin F.card) :
        ((a i ^ n : Circle) : ℂ) =
          ((((e i : {z : atomSet μ // z ∈ F}) : atomSet μ) : Circle) : ℂ) ^ n := by
      rw [Circle.coe_pow]
    simp_rw [hpow]
    have hs := hsum_e (fun z : atomSet μ =>
      ((μ.real {(z : Circle)} : ℝ) : ℂ) * (((z : Circle) : ℂ) ^ n))
    rw [hs]
    simp_rw [Complex.real_smul]
  have hclose_n := hF n
  have hclose_zero := hF 0
  have hatom0 : δ ≤ (atomicCoeff μ 0).re :=
    hδatom.trans (singleton_one_mass_le_atomicCoeff_zero μ)
  have hmass : δ - δ / 8 < mass := by
    have hre : |(atomicCoeff μ 0).re - mass| < δ / 8 := by
      have := Complex.abs_re_le_norm
        (atomicCoeff μ 0 - ∑ z ∈ F,
          μ.real {(z : Circle)} • (((z : atomSet μ) : Circle) : ℂ) ^ 0)
      have hsimp :
          (∑ z ∈ F, μ.real {(z : Circle)} •
            (((z : atomSet μ) : Circle) : ℂ) ^ 0).re = mass := by
        dsimp [mass]
        simp
      change |(atomicCoeff μ 0).re -
        (∑ z ∈ F, μ.real {(z : Circle)} •
          (((z : atomSet μ) : Circle) : ℂ) ^ 0).re| ≤ _ at this
      rw [hsimp] at this
      exact this.trans_lt hclose_zero
    nlinarith [hatom0, (abs_lt.mp hre).2]
  have hgLower : mass - δ / 8 < g (fun i => a i ^ n) := hnU
  rw [hfinite] at hgLower
  have hre_n : |(atomicCoeff μ n).re -
      (∑ z ∈ F, μ.real {(z : Circle)} •
        (((z : atomSet μ) : Circle) : ℂ) ^ n).re| < δ / 8 := by
    have hrele := Complex.abs_re_le_norm
      (atomicCoeff μ n - ∑ z ∈ F,
        μ.real {(z : Circle)} • (((z : atomSet μ) : Circle) : ℂ) ^ n)
    change |(atomicCoeff μ n).re -
      (∑ z ∈ F, μ.real {(z : Circle)} •
        (((z : atomSet μ) : Circle) : ℂ) ^ n).re| ≤ _ at hrele
    exact hrele.trans_lt hclose_n
  have hlowerRe := (abs_lt.mp hre_n).1
  linarith

end

end LocalCassels.AtomicBohrLower
end

section
namespace LocalCassels.CesaroErrorThick

open Filter Topology
open scoped BigOperators
open LocalCassels.PiecewiseAssembly

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

lemma card_hits_of_no_empty_block
    (E : Set ℕ) (N L : ℕ)
    (hblock : ∀ a : ℕ, a + L < N → ∃ k : ℕ, k ≤ L ∧ a + k ∈ E) :
    N / (L + 1) ≤ ((Finset.range N).filter (fun n => n ∈ E)).card := by
  classical
  let Q := N / (L + 1)
  have hex : ∀ j : Fin Q, ∃ k : ℕ, k ≤ L ∧ j.val * (L + 1) + k ∈ E := by
    intro j
    apply hblock
    have hj : (j.val + 1) * (L + 1) ≤ N := by
      apply (Nat.le_div_iff_mul_le (by omega)).mp
      exact j.isLt
    calc
      j.val * (L + 1) + L < j.val * (L + 1) + (L + 1) := by omega
      _ = (j.val + 1) * (L + 1) := by ring
      _ ≤ N := hj
  choose k hkL hkE using hex
  let f : Fin Q → ℕ := fun j => j.val * (L + 1) + k j
  have hfinj : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    by_contra hne
    rcases lt_or_gt_of_ne hne with hijlt | hjilt
    · have hiupper : f i < (i.val + 1) * (L + 1) := by
        dsimp [f]
        calc
          i.val * (L + 1) + k i ≤ i.val * (L + 1) + L :=
            Nat.add_le_add_left (hkL i) _
          _ < i.val * (L + 1) + (L + 1) := by omega
          _ = (i.val + 1) * (L + 1) := by ring
      have hjlower : j.val * (L + 1) ≤ f j := by
        dsimp [f]
        exact Nat.le_add_right _ _
      have hblocks : (i.val + 1) * (L + 1) ≤ j.val * (L + 1) :=
        Nat.mul_le_mul_right (L + 1) (by omega)
      exact (not_lt_of_ge hjlower) (hij ▸ hiupper.trans_le hblocks)
    · have hjupper : f j < (j.val + 1) * (L + 1) := by
        dsimp [f]
        calc
          j.val * (L + 1) + k j ≤ j.val * (L + 1) + L :=
            Nat.add_le_add_left (hkL j) _
          _ < j.val * (L + 1) + (L + 1) := by omega
          _ = (j.val + 1) * (L + 1) := by ring
      have hilower : i.val * (L + 1) ≤ f i := by
        dsimp [f]
        exact Nat.le_add_right _ _
      have hblocks : (j.val + 1) * (L + 1) ≤ i.val * (L + 1) :=
        Nat.mul_le_mul_right (L + 1) (by omega)
      exact (not_lt_of_ge hilower) (hij.symm ▸ hjupper.trans_le hblocks)
  have hfmem : ∀ j, f j ∈ (Finset.range N).filter (fun n => n ∈ E) := by
    intro j
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr ?_, hkE j⟩
    have hj : (j.val + 1) * (L + 1) ≤ N := by
      apply (Nat.le_div_iff_mul_le (by omega)).mp
      exact j.isLt
    dsimp [f]
    calc
      j.val * (L + 1) + k j ≤ j.val * (L + 1) + L :=
        Nat.add_le_add_left (hkL j) _
      _ < j.val * (L + 1) + (L + 1) := by omega
      _ = (j.val + 1) * (L + 1) := by ring
      _ ≤ N := hj
  let emb : Fin Q ↪ {n // n ∈ (Finset.range N).filter (fun n => n ∈ E)} :=
    ⟨fun j => ⟨f j, hfmem j⟩, fun i j h => hfinj (congrArg Subtype.val h)⟩
  simpa [Q] using Fintype.card_le_of_injective emb emb.injective

/-- A sequence whose squared Cesàro means tend to zero is below every fixed
positive threshold on arbitrarily long consecutive intervals. -/
theorem small_error_set_is_thick
    (r : ℕ → ℝ)
    (hr : Tendsto
      (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, (r n) ^ 2)
      atTop (𝓝 0))
    (η : ℝ) (hη : 0 < η) :
    IsThick {n | |r n| < η} := by
  intro L
  let Q : ℕ := L + 1
  have hsmall' := (tendsto_order.1 hr).2 (η ^ 2 / (4 * Q)) (by
    dsimp [Q]
    positivity)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hsmall'
  let N := max N₀ (2 * Q)
  have hNavg : (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, (r n) ^ 2 <
      η ^ 2 / (4 * Q) := hN₀ N (le_max_left _ _)
  let E : Set ℕ := {n | η ≤ |r n|}
  by_contra hnot
  have hblock : ∀ a : ℕ, a + L < N → ∃ k : ℕ, k ≤ L ∧ a + k ∈ E := by
    intro a ha
    by_contra hempty
    apply hnot
    refine ⟨a, ?_⟩
    intro k hk
    have : ¬η ≤ |r (a + k)| := by
      intro hkE
      exact hempty ⟨k, hk, hkE⟩
    exact lt_of_not_ge this
  let EN := (Finset.range N).filter (fun n => n ∈ E)
  have hcardLower : N / (L + 1) ≤ EN.card := by
    dsimp only [EN]
    exact card_hits_of_no_empty_block E N L hblock
  have hsumLower : (EN.card : ℝ) * η ^ 2 ≤
      ∑ n ∈ Finset.range N, (r n) ^ 2 := by
    calc
      (EN.card : ℝ) * η ^ 2 = ∑ _n ∈ EN, η ^ 2 := by simp [EN]
      _ ≤ ∑ n ∈ EN, (r n) ^ 2 := by
        apply Finset.sum_le_sum
        intro n hn
        have hnE := (Finset.mem_filter.mp hn).2
        dsimp [E] at hnE
        calc
          η ^ 2 ≤ |r n| ^ 2 := (sq_le_sq₀ hη.le (abs_nonneg _)).2 hnE
          _ = (r n) ^ 2 := sq_abs _
      _ ≤ ∑ n ∈ Finset.range N, (r n) ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro n hn hn'
        positivity
  have hNpos : 0 < N := by dsimp [N, Q]; omega
  have hcardReal : (N : ℝ) / (2 * Q) ≤ EN.card := by
    have hdiv : N / Q ≤ EN.card := by
      simpa [Q, EN] using hcardLower
    have hfloor : (N : ℝ) / (2 * Q) ≤ (N / Q : ℕ) := by
      have hQpos : 0 < Q := by dsimp [Q]; omega
      have hNQ : 2 * Q ≤ N := le_max_right _ _
      have hq2 : 2 ≤ N / Q := (Nat.le_div_iff_mul_le hQpos).2 hNQ
      have hrem : N < (N / Q + 1) * Q := by
        simpa [Nat.mul_comm] using Nat.lt_mul_div_succ N hQpos
      rw [div_le_iff₀]
      · exact_mod_cast (show N ≤ (N / Q) * (2 * Q) by nlinarith)
      · positivity
    exact hfloor.trans (by exact_mod_cast hdiv)
  have hQreal : (0 : ℝ) < Q := by
    dsimp [Q]
    positivity
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hηsq : 0 ≤ η ^ 2 := sq_nonneg η
  have hfirst : η ^ 2 / (2 * Q) =
      (((N : ℝ) / (2 * Q)) * η ^ 2) / N := by
    field_simp
  have hmiddle : (((N : ℝ) / (2 * Q)) * η ^ 2) / N ≤
      ((EN.card : ℝ) * η ^ 2) / N := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcardReal hηsq) hNreal.le
  have hlast : ((EN.card : ℝ) * η ^ 2) / N ≤
      (∑ n ∈ Finset.range N, (r n) ^ 2) / N :=
    div_le_div_of_nonneg_right hsumLower hNreal.le
  have havgLower : η ^ 2 / (2 * Q) ≤
      (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, (r n) ^ 2 := by
    rw [inv_mul_eq_div]
    exact hfirst ▸ hmiddle.trans hlast
  have hsep : η ^ 2 / (4 * Q) < η ^ 2 / (2 * Q) := by
    exact div_lt_div_of_pos_left (sq_pos_of_pos hη) (by positivity)
      (by nlinarith [hQreal])
  exact (not_lt_of_ge havgLower) (hNavg.trans hsep)

end

end LocalCassels.CesaroErrorThick
end

section
namespace LocalCassels.SpectralAlmostBohr

open MeasureTheory
open scoped BigOperators Topology
open LocalCassels.AtomicDecomposition LocalCassels.SpectralWienerDecomposition
open LocalCassels.AtomicBohrLower LocalCassels.CesaroErrorThick
open LocalCassels.PiecewiseAssembly

noncomputable section

local instance : MeasurableSpace Circle := borel Circle
local instance : BorelSpace Circle := ⟨rfl⟩

/-- Spectral Følner principle: if a finite circle measure has positive mass at
the trivial character, then the positivity set of its Fourier coefficients
contains a finite-dimensional Bohr neighborhood intersected with a thick set. -/
theorem spectral_positive_set_contains_piecewise_bohr
    (μ : Measure Circle) [IsFiniteMeasure μ]
    (δ : ℝ) (hδ : 0 < δ) (hδatom : δ ≤ μ.real {(1 : Circle)})
    (S : Set ℕ)
    (hpositive : ∀ n : ℕ, 0 < (∫ z : Circle, (z : ℂ) ^ n ∂μ).re → n ∈ S) :
    ∃ d : ℕ, ∃ a : Fin d → Circle, ∃ U : Set (Fin d → Circle),
      IsOpen U ∧ (fun _ => (1 : Circle)) ∈ U ∧
      ∃ J : Set ℕ, IsThick J ∧
        ∀ n : ℕ, (fun i => a i ^ n) ∈ U → n ∈ J → n ∈ S := by
  obtain ⟨d, a, U, hUopen, hone, hatomic⟩ :=
    exists_finite_circle_bohr_atomic_lower μ δ hδ hδatom
  let r : ℕ → ℝ := fun n => (continuousCoeff μ n).re
  let J : Set ℕ := {n | |r n| < δ / 2}
  have hr : Filter.Tendsto
      (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, (r n) ^ 2)
      Filter.atTop (nhds 0) := by
    simpa [r] using tendsto_cesaro_sq_re_continuousCoeff μ
  have hJ : IsThick J := by
    apply small_error_set_is_thick r hr (δ / 2)
    positivity
  refine ⟨d, a, U, hUopen, hone, J, hJ, ?_⟩
  intro n hnU hnJ
  apply hpositive n
  have ha := hatomic n hnU
  have hrsmall : |r n| < δ / 2 := hnJ
  have hrbelow : -(δ / 2) < r n := neg_lt_of_abs_lt hrsmall
  have hcoeff := coeff_eq_atomic_add_continuous μ n
  have hre := congrArg Complex.re hcoeff
  change (∫ z : Circle, (z : ℂ) ^ n ∂μ).re =
      (atomicCoeff μ n).re + r n at hre
  rw [hre]
  nlinarith

end

end LocalCassels.SpectralAlmostBohr
end

section
namespace LocalCassels.CirclePiecewiseToAddCircle

open scoped Topology
open LocalCassels.PiecewiseAssembly

noncomputable section

private lemma toCircle_arg_div_two_pi (z : Circle) :
    AddCircle.toCircle ((((z : ℂ).arg / (2 * Real.pi) : ℝ) : UnitAddCircle)) = z := by
  rw [AddCircle.toCircle_apply_mk]
  rw [show 2 * Real.pi / (1 : ℝ) * ((z : ℂ).arg / (2 * Real.pi)) =
      (z : ℂ).arg by field_simp [Real.pi_ne_zero]]
  exact Circle.exp_arg z

/-- Translate a multiplicative finite-circle piecewise-Bohr witness into the
additive unit-torus coordinates used by the BFW interface. -/
theorem circle_piecewise_bohr_to_additive
    {d : ℕ} (a : Fin d → Circle) (U : Set (Fin d → Circle))
    (hU : IsOpen U) (hone : (fun _ => (1 : Circle)) ∈ U)
    (J S : Set ℕ) (hJ : IsThick J)
    (hinc : ∀ n : ℕ, (fun i => a i ^ n) ∈ U → n ∈ J → n ∈ S) :
    ∃ α : Fin d → ℝ, ∃ V : Set (UnitAddTorus (Fin d)),
      IsOpen V ∧ (0 : ℕ) • (fun i => (α i : UnitAddCircle)) ∈ V ∧
      IsThick J ∧
      ∀ n : ℕ, n • (fun i => (α i : UnitAddCircle)) ∈ V → n ∈ J → n ∈ S := by
  let α : Fin d → ℝ := fun i => (a i : ℂ).arg / (2 * Real.pi)
  let T : UnitAddTorus (Fin d) → (Fin d → Circle) := fun x i =>
    AddCircle.toCircle (x i)
  let V : Set (UnitAddTorus (Fin d)) := T ⁻¹' U
  have hT : Continuous T := by
    dsimp [T]
    fun_prop
  have hV : IsOpen V := hU.preimage hT
  have hzero : (0 : UnitAddTorus (Fin d)) ∈ V := by
    dsimp [V, T]
    simpa using hone
  refine ⟨α, V, hV, ?_, hJ, ?_⟩
  · simpa using hzero
  · intro n hnV hnJ
    apply hinc n _ hnJ
    have hmap : T (n • (fun i => (α i : UnitAddCircle))) =
        (fun i => a i ^ n) := by
      funext i
      dsimp [T]
      rw [AddCircle.toCircle_nsmul, toCircle_arg_div_two_pi]
    exact hmap ▸ hnV

end

end LocalCassels.CirclePiecewiseToAddCircle
end

section
namespace LocalCassels.BohrReturnSyndetic

open Set Filter Topology
open scoped BigOperators

noncomputable section

/-- Return times of a rotation to an open identity neighborhood in a compact
additive group have uniformly bounded forward gaps. -/
theorem compact_rotation_return_syndetic
    {T : Type*} [TopologicalSpace T] [T2Space T] [AddCommGroup T]
    [IsTopologicalAddGroup T] [CompactSpace T]
    (a : T) (V : Set T) (hVopen : IsOpen V) (hzero : (0 : T) ∈ V) :
    ∃ K : ℕ, ∀ t : ℕ, ∃ q : ℕ, q ≤ K ∧ (t + q) • a ∈ V := by
  let H : Set T := closure (Set.range fun n : ℕ => n • a)
  let O : ℕ → Set T := fun n => {x | x + n • a ∈ V}
  have hOopen : ∀ n : ℕ, IsOpen (O n) := by
    intro n
    exact hVopen.preimage (continuous_id.add continuous_const)
  have hneg {x : T} (hx : x ∈ H) : -x ∈ H := by
    have hxz : x ∈ closure (Set.range fun z : ℤ => z • a) := by
      rw [closure_range_zsmul_eq_nsmul]
      exact hx
    have hxsub : x ∈ (AddSubgroup.zmultiples a).topologicalClosure := by
      change x ∈ ((AddSubgroup.zmultiples a).topologicalClosure : Set T)
      rw [AddSubgroup.topologicalClosure_coe, AddSubgroup.coe_zmultiples]
      exact hxz
    have hnegsub := (AddSubgroup.zmultiples a).topologicalClosure.neg_mem hxsub
    have hnegz : -x ∈ closure (Set.range fun z : ℤ => z • a) := by
      change -x ∈ ((AddSubgroup.zmultiples a).topologicalClosure : Set T) at hnegsub
      rw [AddSubgroup.topologicalClosure_coe, AddSubgroup.coe_zmultiples] at hnegsub
      exact hnegsub
    rw [closure_range_zsmul_eq_nsmul] at hnegz
    exact hnegz
  have hcover : H ⊆ ⋃ n : ℕ, O n := by
    intro x hx
    let W : Set T := {y | x + y ∈ V}
    have hWopen : IsOpen W := hVopen.preimage (continuous_const.add continuous_id)
    have hnegW : -x ∈ W := by
      dsimp [W]
      simpa using hzero
    have hmeet := (mem_closure_iff.mp (hneg hx)) W hWopen hnegW
    obtain ⟨y, hyW, n, rfl⟩ := hmeet
    apply mem_iUnion.mpr
    exact ⟨n, hyW⟩
  have hHcompact : IsCompact H := isClosed_closure.isCompact
  obtain ⟨s, hscover⟩ := hHcompact.elim_finite_subcover O hOopen hcover
  let K : ℕ := ∑ n ∈ s, n
  refine ⟨K, ?_⟩
  intro t
  have htH : t • a ∈ H := subset_closure ⟨t, rfl⟩
  have htcover := hscover htH
  simp only [mem_iUnion] at htcover
  obtain ⟨q, hq⟩ := htcover
  obtain ⟨hqS, hqO⟩ := hq
  refine ⟨q, ?_, ?_⟩
  · dsimp [K]
    exact Finset.single_le_sum (s := s) (f := fun n : ℕ => n)
      (fun _ _ => Nat.zero_le _) hqS
  · change t • a + q • a ∈ V at hqO
    simpa [add_nsmul] using hqO

end

end LocalCassels.BohrReturnSyndetic
end

section
namespace LocalCassels.PiecewiseFiniteEmbedding

open Filter Topology
open scoped BigOperators
open LocalCassels.PiecewiseAssembly LocalCassels.BohrReturnSyndetic

noncomputable section

/-- A piecewise-Bohr return set finitely contains a smaller pure Bohr return
set. Thickness supplies a long interval, while syndeticity of the smaller
return set lets the common translating shift be chosen inside that interval. -/
theorem pure_bohr_finitely_embeds_piecewise
    {T : Type*} [TopologicalSpace T] [T2Space T] [AddCommGroup T]
    [IsTopologicalAddGroup T] [CompactSpace T]
    (a : T) (U : Set T) (hUopen : IsOpen U) (hzero : (0 : T) ∈ U)
    (J Q : Set ℕ) (hJ : IsThick J)
    (hQ : ∀ n : ℕ, n • a ∈ U → n ∈ J → n ∈ Q) :
    ∃ V : Set T, IsOpen V ∧ (0 : T) ∈ V ∧
      ∀ F : Finset ℕ, (∀ n ∈ F, n • a ∈ V) →
        ∃ r : ℕ, ∀ n ∈ F, n + r ∈ Q := by
  obtain ⟨V, hVopen, hVzero, hVV⟩ :=
    exists_open_nhds_zero_half (hUopen.mem_nhds hzero)
  obtain ⟨K, hK⟩ := compact_rotation_return_syndetic a V hVopen hVzero
  refine ⟨V, hVopen, hVzero, ?_⟩
  intro F hF
  let R : ℕ := ∑ n ∈ F, n
  obtain ⟨t, ht⟩ := hJ (K + R)
  obtain ⟨q, hqK, hqphase⟩ := hK t
  refine ⟨t + q, ?_⟩
  intro n hnF
  apply hQ (n + (t + q))
  · have hnphase := hF n hnF
    have hadd := hVV _ hnphase _ hqphase
    simpa [add_nsmul, add_assoc, add_comm, add_left_comm] using hadd
  · have hnR : n ≤ R := by
      dsimp [R]
      exact Finset.single_le_sum (s := F) (f := fun m : ℕ => m)
        (fun _ _ => Nat.zero_le _) hnF
    have hqn : q + n ≤ K + R := Nat.add_le_add hqK hnR
    have := ht (q + n) hqn
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this

end

end LocalCassels.PiecewiseFiniteEmbedding
end

section
namespace LocalCassels.BFWFromSpectral

open MeasureTheory
open scoped Topology
open LocalCassels.PiecewiseAssembly LocalCassels.GeneralBFWReduction
open LocalCassels.FiniteEmbeddingPiecewiseBohrOrbit
open LocalCassels.SyndeticCrossSpectralEmbedding LocalCassels.SpectralAlmostBohr
open LocalCassels.CirclePiecewiseToAddCircle LocalCassels.PiecewiseFiniteEmbedding

noncomputable section

local instance : MeasurableSpace Circle := borel Circle
local instance : BorelSpace Circle := ⟨rfl⟩

/-- The Bergelson--Furstenberg--Weiss piecewise-Bohr sumset theorem, proved by
finite cyclic cross-correlation, compact spectral limits, Wiener's lemma, and
finite-embedding reassembly. -/
theorem general_bfw_from_spectral : SyndeticSumsetPiecewiseBohr := by
  intro S₀ S₁ hsynd
  have h₀ : ∃ K : ℕ, ∀ n : ℕ, ∃ s : ℕ,
      s ∈ S₀ ∧ s ≤ n ∧ n ≤ s + K := by
    simpa using hsynd (0 : Fin 2)
  have h₁ : ∃ K : ℕ, ∀ n : ℕ, ∃ s : ℕ,
      s ∈ S₁ ∧ s ≤ n ∧ n ≤ s + K := by
    simpa using hsynd (1 : Fin 2)
  let S : Set ℕ := {z | ∃ s₀ ∈ S₀, ∃ s₁ ∈ S₁, s₀ + s₁ = z}
  obtain ⟨μ, hμatom, hembedE⟩ :=
    exists_cross_spectral_finite_embedding S₀ S₁ h₀ h₁
  let E : Set ℕ :=
    {n | 0 < (∫ z : Circle, (z : ℂ) ^ n ∂(μ : Measure Circle)).re}
  obtain ⟨d, a, U, hUopen, hone, J, hJ, hpieceE⟩ :=
    spectral_positive_set_contains_piecewise_bohr μ
      ((μ : Measure Circle).real {(1 : Circle)}) hμatom le_rfl E
      (fun n hn => hn)
  obtain ⟨α, V, hVopen, hzeroV, _, hpieceE'⟩ :=
    circle_piecewise_bohr_to_additive a U hUopen hone J E hJ hpieceE
  let avec : UnitAddTorus (Fin d) := fun i => (α i : UnitAddCircle)
  have hzeroV' : (0 : UnitAddTorus (Fin d)) ∈ V := by
    simpa [avec] using hzeroV
  obtain ⟨W, hWopen, hzeroW, hWE⟩ :=
    pure_bohr_finitely_embeds_piecewise avec V hVopen hzeroV' J E hJ
      (fun n hnV hnJ => hpieceE' n hnV hnJ)
  have hWS : ∀ F : Finset ℕ,
      (∀ n ∈ F, n • avec ∈ W) →
      ∃ r : ℕ, ∀ n ∈ F, n + r ∈ S := by
    intro F hF
    obtain ⟨r₁, hr₁⟩ := hWE F hF
    let G : Finset ℕ := F.image (fun n => n + r₁)
    have hGE : ∀ n ∈ G, n ∈ E := by
      intro n hn
      rw [Finset.mem_image] at hn
      obtain ⟨m, hm, rfl⟩ := hn
      exact hr₁ m hm
    obtain ⟨r₂, hr₂⟩ := hembedE G hGE
    refine ⟨r₁ + r₂, ?_⟩
    intro n hn
    have hnG : n + r₁ ∈ G := Finset.mem_image.mpr ⟨n, hn, rfl⟩
    have hthis := hr₂ (n + r₁) hnG
    change ∃ s₀ ∈ S₀, ∃ s₁ ∈ S₁, s₀ + s₁ = n + (r₁ + r₂)
    simpa [Nat.add_assoc] using hthis
  obtain ⟨W', hW'open, n₀, hn₀W', J', hJ', hfinal⟩ :=
    piecewise_bohr_of_finite_embedding_orbit avec W hWopen 0
      (by simpa using hzeroW) S hWS
  refine ⟨d, α, W', hW'open, n₀, hn₀W', J', hJ', ?_⟩
  intro n hnJ hnW
  exact hfinal n hnJ hnW

end

end LocalCassels.BFWFromSpectral
end

section
namespace LocalCassels.FinalProof

open LocalCassels.ConditionalFinalAssembly LocalCassels.GeneralBFWReduction
open LocalCassels.BFWFromSpectral

/-- Canonical Erdős Problem #254 statement. -/
theorem erdos_254 : LocalCassels.Statement :=
  bfw_finite_sum_property_implies_statement
    (general_bfw_implies_finite_sum_property general_bfw_from_spectral)

end LocalCassels.FinalProof
end

namespace OMA.Cassels
open Filter Finset

private theorem count_eq (A : Set ℕ) (n : ℕ) :
    LocalCassels.countingFunction A n = (A ∩ Set.Icc 1 n).ncard := by
  classical
  have he : (A ∩ Set.Icc 1 n) = ((Icc 1 n).filter (fun k => k ∈ A) : Finset ℕ) := by
    ext k
    simp only [Set.mem_inter_iff, Set.mem_Icc, Finset.mem_coe, mem_filter, mem_Icc]
    tauto
  rw [he, Set.ncard_coe_finset]
  rfl

private theorem dyadic_growth (A : Set ℕ)
    (hg : Tendsto (fun n : ℕ =>
      (((A ∩ Set.Icc 1 (2*n)).ncard:ℝ) - ((A ∩ Set.Icc 1 n).ncard:ℝ)) /
        Real.log (Real.log n)) atTop atTop) :
    Tendsto (LocalCassels.dyadicIncrement A) atTop atTop := by
  apply (tendsto_natCast_atTop_iff (R := ℝ)).mp
  have hlog : Tendsto (fun n : ℕ => Real.log (Real.log n)) atTop atTop :=
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).comp tendsto_natCast_atTop_atTop
  apply (hg.atTop_mul_atTop₀ hlog).congr'
  filter_upwards [hlog.eventually_gt_atTop 0] with n hn
  rw [div_mul_cancel₀ _ hn.ne']
  dsimp [LocalCassels.dyadicIncrement]
  have hb : LocalCassels.countingFunction A n ≤ LocalCassels.countingFunction A (2*n) := by
    classical
    unfold LocalCassels.countingFunction
    apply card_le_card
    intro k hk
    obtain ⟨hkn,hA⟩ := mem_filter.mp hk
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨(mem_Icc.mp hkn).1, by have := (mem_Icc.mp hkn).2; omega⟩, hA⟩
  rw [Nat.cast_sub hb, count_eq, count_eq]

private theorem phase_growth (A : Set ℕ) (θ : ℝ)
    (hs : ¬ Summable (fun n : A => distToNearestInt (θ*(n:ℝ))^2)) :
    Tendsto (LocalCassels.phasePartialSum A θ) atTop atTop := by
  classical
  have hne : ¬ Summable (fun n : A => distToNearestInt (θ*(n:ℝ))) := by
    intro hsum
    apply hs
    apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _ hsum
    intro n
    have hp := distToNearestInt_nonneg (θ*(n:ℝ))
    have hu : distToNearestInt (θ*(n:ℝ)) ≤ 1/2 := abs_sub_round _
    nlinarith [mul_nonneg hp (sub_nonneg.mpr hu)]
  have ht := (Erdos254.not_summable_iff_tendsto_partial_sums A θ).mp hne
  apply tendsto_atTop_mono _ ht
  intro n
  let F := fun k : ℕ => A.indicator (fun r : ℕ => distToNearestInt (θ*r)) k
  have hF (k) : 0 ≤ F k := Set.indicator_nonneg (fun i _ => distToNearestInt_nonneg _) k
  have h0 : F 0 = 0 := by by_cases hz : 0 ∈ A <;> simp [F,hz,distToNearestInt]
  change ∑ k ∈ range n, F k ≤ _
  calc
    _ ≤ ∑ k ∈ insert 0 (Icc 1 n), F k := by
      apply sum_le_sum_of_subset_of_nonneg _ (fun k _ _ => hF k)
      intro k hk
      by_cases h : k = 0
      · simp [h]
      · exact mem_insert_of_mem (mem_Icc.mpr ⟨by omega, (mem_range.mp hk).le⟩)
    _ = ∑ k ∈ Icc 1 n, F k := by rw [sum_insert (by simp),h0,zero_add]
    _ = _ := by
      unfold LocalCassels.phasePartialSum LocalCassels.nearestIntegerDistance
      rw [sum_filter]
      apply sum_congr rfl
      intro k _
      by_cases hk : k ∈ A <;> simp [F, hk, distToNearestInt, abs_sub_round_eq_min]

end OMA.Cassels

open OMA.Cassels Filter in
theorem OMA.solution : type_of% @Erdos254.erdos_254.variants.cassels := by
  rintro A ⟨hg,hs⟩
  obtain ⟨N,hN⟩ := LocalCassels.FinalProof.erdos_254 A (dyadic_growth A hg)
    (fun θ hθ => phase_growth A θ (hs θ hθ.1 hθ.2))
  exact eventually_atTop.mpr ⟨N,hN⟩
