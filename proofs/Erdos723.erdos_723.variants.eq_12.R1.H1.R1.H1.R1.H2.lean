import OMAReductions.R_Erdos723_erdos_723_variants_eq_12_R1_H1_R1_H1_R1
import Mathlib

/-!
# Extending a partial projective plane of order twelve from 139 to 140 blocks

Each block has thirteen points, and distinct blocks meet once. The proof uses
the incidence counts and the Euclidean frame of the deficiency-two points to
construct a new block while preserving all 139 given blocks.
-/

namespace Erdos723PartialPlane

/-- A pencil of twelve blocks determines one further block meeting every
old block exactly once. This extension does not require 142 blocks. -/
theorem extend_at_degree_twelve
    {P L : Type*} [Fintype P] [Fintype L] [DecidableEq P]
    (B : L → Finset P) (hp : Fintype.card P = 157)
    (hsize : ∀ l, (B l).card = 13)
    (hmeet : ∀ l m, l ≠ m → (B l ∩ B m).card = 1)
    (p : P) (hdegree : (Finset.univ.filter (fun l => p ∈ B l)).card = 12) :
    ∃ N : Finset P, N.card = 13 ∧ p ∈ N ∧ ∀ l, (N ∩ B l).card = 1 := by
  classical
  let D := Finset.univ.filter fun l => p ∈ B l
  let U := D.biUnion fun l => (B l).erase p
  have hpencil {l : L} (hl : l ∈ D) : p ∈ B l := (Finset.mem_filter.mp hl).2
  have hdisj : (D : Set L).PairwiseDisjoint fun l => (B l).erase p := by
    intro l hl m hm e
    apply Finset.disjoint_left.mpr
    intro z hzl hzm
    have h := Finset.card_eq_one_iff_existsUnique.mp (hmeet l m e)
    exact (Finset.mem_erase.mp hzl).1 (h.unique
      (Finset.mem_inter.mpr ⟨(Finset.mem_erase.mp hzl).2, (Finset.mem_erase.mp hzm).2⟩)
      (Finset.mem_inter.mpr ⟨hpencil hl, hpencil hm⟩))
  have hpU : p ∉ U := by simp [U]
  refine ⟨Finset.univ \ U, ?_, by simpa using hpU, ?_⟩
  · have hu : U.card = 144 := by
      rw [Finset.card_biUnion hdisj]
      have h : ∀ l ∈ D, ((B l).erase p).card = 12 := by
        intro l hl
        rw [Finset.card_erase_of_mem (hpencil hl), hsize]
      calc
        _ = ∑ _l ∈ D, 12 := Finset.sum_congr rfl h
        _ = 144 := by simp [D, hdegree]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, hp, hu]
  · intro l
    have heq : (Finset.univ \ U) ∩ B l = B l \ U := by ext z; simp [and_comm]
    rw [heq]
    by_cases hl : p ∈ B l
    · suffices he : B l \ U = {p} by simp [he]
      ext z
      by_cases e : z = p
      · subst z
        simp [hl, hpU]
      · have hu (hz : z ∈ B l) : z ∈ U := Finset.mem_biUnion.mpr
          ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl⟩, Finset.mem_erase.mpr ⟨e,hz⟩⟩
        simpa [e, Finset.mem_sdiff] using hu
    · have hrestrict : (D : Set L).PairwiseDisjoint fun m => B l ∩ (B m).erase p := by
        intro x hx y hy hxy
        exact (hdisj hx hy hxy).mono Finset.inter_subset_right Finset.inter_subset_right
      have hsum : (B l ∩ U).card = 12 := by
        rw [Finset.inter_biUnion, Finset.card_biUnion hrestrict]
        have heach (m) (hm : m ∈ D) : (B l ∩ (B m).erase p).card = 1 := by
          have e : B l ∩ (B m).erase p = B l ∩ B m := by
            ext z
            by_cases h : z = p
            · subst z
              simp [hl]
            · simp [h]
          rw [e]
          exact hmeet l m (fun e => hl (e ▸ hpencil hm))
        calc
          _ = ∑ _m ∈ D, 1 := Finset.sum_congr rfl heach
          _ = 12 := by simp [D, hdegree]
      have h := Finset.card_sdiff_add_card_inter (B l) U
      rw [hsum, hsize] at h
      omega

end Erdos723PartialPlane

/-!
# Arithmetic in the eighteen-missing-line case

At 139 lines the incidence moments, after ruling out degree 12 points, give
the two displayed equations in `possible_roots`. A root is a point of
deficiency two. The last theorem checks the part-size and profile handoff
for a bipartite representation of the roots' uncovered-pair graph.

The finite bitset representation and the separation of the computed table
from its mathematical interpretation follow OMA.E835 in Open Math Agents
PR 2965, in particular its `pointSet` and `mem_pointSet` helpers.
-/

namespace Order12.Deficit18

private def pointSet (code : ℕ) : Finset ℕ := code.bitIndices.toFinset

private theorem mem_pointSet {code i : ℕ} : i ∈ pointSet code ↔ code.testBit i := by
  simp [pointSet, Nat.mem_bitIndices]

/-- The possible root counts before using the local incidence equations. -/
def rootCounts : Finset ℕ :=
  {81, 86, 87, 90, 91, 92, 93, 95, 96, 97, 98, 99, 100, 101, 102, 104, 105, 108}

private def rootCode : ℕ := 395486176822148727040358007963648

private theorem decode_rootCode : pointSet rootCode = rootCounts := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
set_option synthInstance.maxSize 2048 in
private theorem finiteProfiles :
    ∀ a : Fin 25, ∀ b : Fin 10, ∀ c : Fin 5, ∀ d : Fin 4,
      3*a.val + 8*b.val + 15*c.val + 24*d.val = 72 →
      let r := (234 - (3*a.val + 4*b.val + 5*c.val + 6*d.val)) / 2
      rootCode.testBit r = true ∧
      (r = 81 → a.val = 24 ∧ b.val = 0 ∧ c.val = 0 ∧ d.val = 0) := by
  dsimp only
  decide +kernel

/-- All solutions of the two global incidence moments pass the finite table. -/
theorem possible_roots {r a b c d : ℕ}
    (hexcess : 3*a + 8*b + 15*c + 24*d = 72)
    (hmass : 2*r + 3*a + 4*b + 5*c + 6*d = 234) :
    r ∈ rootCounts ∧ (r = 81 → a = 24 ∧ b = 0 ∧ c = 0 ∧ d = 0) := by
  have hr : (234 - (3*a + 4*b + 5*c + 6*d)) / 2 = r := by omega
  have h := finiteProfiles ⟨a, by omega⟩ ⟨b, by omega⟩
    ⟨c, by omega⟩ ⟨d, by omega⟩ hexcess
  change rootCode.testBit ((234 - (3*a + 4*b + 5*c + 6*d))/2) = true ∧ _ at h
  dsimp only at h
  rw [hr] at h
  exact ⟨decode_rootCode ▸ (mem_pointSet.mpr h.1), h.2⟩

set_option maxRecDepth 20000 in
private theorem finiteParts : ∀ u v : Fin 20,
    u.val + v.val ≤ 19 →
    4 * (u.val * v.val) ≤ 18 * (u.val + v.val) →
    ∀ r ∈ rootCounts, r ≤ u.val * v.val → u.val * v.val ≤ r + 1 →
      u.val = 9 ∧ v.val = 9 ∧ r = 81 := by
  decide +kernel

/-- In the bipartite edge representation the numerical hypotheses force
two parts of size nine, all 81 edges, and 24 points of deficiency three. -/
theorem bipartite_profile {r a b c d u v : ℕ}
    (hexcess : 3*a + 8*b + 15*c + 24*d = 72)
    (hmass : 2*r + 3*a + 4*b + 5*c + 6*d = 234)
    (hsize : u + v ≤ 19)
    (hprojected : 4 * (u * v) ≤ 18 * (u + v))
    (hedges : r ≤ u*v) (hmissing : u*v ≤ r+1) :
    u = 9 ∧ v = 9 ∧ r = u*v ∧ a = 24 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  obtain ⟨hr, ha⟩ := possible_roots hexcess hmass
  obtain ⟨hu, hv, hr81⟩ := finiteParts ⟨u, by omega⟩ ⟨v, by omega⟩
    hsize hprojected r hr hedges hmissing
  change u = 9 at hu
  change v = 9 at hv
  exact ⟨hu, hv, by simpa only [hu, hv] using hr81, ha hr81⟩

/-- If every edge has at most one missing incidence at its two endpoints
in total, then the whole bipartite graph misses at most one edge.
The two parts have no isolated vertices. -/
theorem at_most_one_missing {U V : Type*} [Fintype U] [Fintype V]
    [DecidableEq U] [DecidableEq V] (E : U → V → Prop) [DecidableRel E]
    (hrow : ∀ i, ∃ j, E i j) (hcol : ∀ j, ∃ i, E i j)
    (hlocal : ∀ i j, E i j →
      (Finset.univ.filter (fun b => ¬E i b)).card +
      (Finset.univ.filter (fun a => ¬E a j)).card ≤ 1) :
    (Finset.univ.filter (fun p : U × V => ¬E p.1 p.2)).card ≤ 1 := by
  classical
  have row_unique (i : U) {j l : V} (hj : ¬E i j) (hl : ¬E i l) : j = l := by
    obtain ⟨z, hz⟩ := hrow i
    have h := hlocal i z hz
    apply Finset.card_le_one.mp (show (Finset.univ.filter (fun b => ¬E i b)).card ≤ 1 by omega)
    · simpa using hj
    · simpa using hl
  have col_unique (j : V) {i k : U} (hi : ¬E i j) (hk : ¬E k j) : i = k := by
    obtain ⟨z, hz⟩ := hcol j
    have h := hlocal z j hz
    apply Finset.card_le_one.mp (show (Finset.univ.filter (fun a => ¬E a j)).card ≤ 1 by omega)
    · simpa using hi
    · simpa using hk
  apply Finset.card_le_one.mpr
  rintro ⟨i,j⟩ hij ⟨k,l⟩ hkl
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hij hkl
  by_cases h : j = l
  · subst l
    exact Prod.ext (col_unique j hij hkl) rfl
  have hil : E i l := by
    by_contra hen
    exact h (row_unique i hij hen)
  have hposR : 0 < (Finset.univ.filter (fun b => ¬E i b)).card :=
    Finset.card_pos.mpr ⟨j, by simpa using hij⟩
  have hposC : 0 < (Finset.univ.filter (fun a => ¬E a l)).card :=
    Finset.card_pos.mpr ⟨k, by simpa using hkl⟩
  have hsum := hlocal i l hil
  omega

/-- A bipartite graph realizing the root counts, with the endpoint degree
and projection inequalities of the edge representation, is complete K₉,₉. -/
theorem complete_bipartite_of_moments {u v a b c d : ℕ}
    (E : Fin u → Fin v → Prop) [DecidableRel E]
    (hrow : ∀ i, ∃ j, E i j) (hcol : ∀ j, ∃ i, E i j)
    (hdegree : ∀ i j, E i j →
      18 ≤ (Finset.univ.filter (E i)).card + (Finset.univ.filter (fun a => E a j)).card)
    (hsize : u + v ≤ 19) (hprojected : 4 * (u*v) ≤ 18 * (u+v))
    (hexcess : 3*a + 8*b + 15*c + 24*d = 72)
    (hmass : 2*(Finset.univ.filter (fun p : Fin u × Fin v => E p.1 p.2)).card +
      3*a + 4*b + 5*c + 6*d = 234) :
    u = 9 ∧ v = 9 ∧ (∀ i j, E i j) ∧ a = 24 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  classical
  have hlocal (i : Fin u) (j : Fin v) (hij : E i j) :
      (Finset.univ.filter (fun b => ¬E i b)).card +
      (Finset.univ.filter (fun a => ¬E a j)).card ≤ 1 := by
    have h1 := Finset.card_filter_add_card_filter_not (s := Finset.univ) (p := E i)
    have h2 := Finset.card_filter_add_card_filter_not (s := Finset.univ) (p := fun a => E a j)
    simp only [Finset.card_univ, Fintype.card_fin] at h1 h2
    have h3 := hdegree i j hij
    omega
  have hbound := at_most_one_missing E hrow hcol hlocal
  have htotal := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (p := fun p : Fin u × Fin v => E p.1 p.2)
  simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at htotal
  obtain ⟨hu, hv, hr, hrest⟩ :=
    bipartite_profile hexcess hmass hsize hprojected (by omega) (by omega)
  have hzero : (Finset.univ.filter (fun p : Fin u × Fin v => ¬E p.1 p.2)).card = 0 := by omega
  refine ⟨hu, hv, ?_, hrest⟩
  intro i j
  by_contra h
  have hp : (0 : ℕ) < (Finset.univ.filter (fun p : Fin u × Fin v => ¬E p.1 p.2)).card :=
    Finset.card_pos.mpr ⟨(i,j), by simpa using h⟩
  omega

end Order12.Deficit18

/-!
# Deficit-18 incidence moments, connectedness certificate, and K₉,₉ reflection lemma

Formalizes three major components of the 139-block completion argument in
`order12_deficit18.txt` for a partial projective plane of order 12
(157 points, 139 blocks of size 13, pairwise meeting in one point, no point of degree 12):

1. Exact incidence moments, the hole-neighbor identity
   `∑_{q hole of p} (d q - 2) = d p * (6 - d p)`, and the deficiency bound `d p ≤ 6`.
2. Exact common-hole-neighbor counts by Finset double counting:
   `d p * d q` for covered pairs and `d p * d q + 12 - d p - d q` for hole pairs.
3. Kernel-checked finite certificate for all 23 global moment profiles (`t = 18`),
   eliminating the 4 locally inconsistent budgets and proving connectedness of the
   deficiency-two root graph in all 19 remaining profiles.
4. The `K₉,₉` mod-3 reflection elimination lemma: any `{-1, 0, 1}` assignment supported
   on at most 12 points of degree 10 that sums to `0 (mod 3)` on every old block is zero.
-/

namespace Order12.Deficit18

open Finset

/-! ## Section 1: Kernel-checked 23-profile connectedness certificate -/

def validBudget (n3 n4 n5 n6 d : ℕ) : Bool :=
  let b3 := if 3 * (6 - 3) < d - 2 then 0 else if d = 3 then n3 - 1 else n3
  let b4 := if 4 * (6 - 4) < d - 2 then 0 else if d = 4 then n4 - 1 else n4
  let b5 := if 5 * (6 - 5) < d - 2 then 0 else if d = 5 then n5 - 1 else n5
  let b6 := if 6 * (6 - 6) < d - 2 then 0 else if d = 6 then n6 - 1 else n6
  let target := d * (6 - d)
  (List.range (b3 + 1)).any fun a3 =>
    (List.range (b4 + 1)).any fun a4 =>
      (List.range (b5 + 1)).any fun a5 =>
        (List.range (b6 + 1)).any fun a6 =>
          a3 + 2 * a4 + 3 * a5 + 4 * a6 == target

def maxHighNeighbors2 (n3 n4 n5 n6 : ℕ) : ℕ :=
  (List.range (n3 + 1)).foldl (fun acc a3 =>
    (List.range (n4 + 1)).foldl (fun acc a4 =>
      (List.range (n5 + 1)).foldl (fun acc a5 =>
        (List.range (n6 + 1)).foldl (fun acc a6 =>
          if a3 + 2 * a4 + 3 * a5 + 4 * a6 == 8 then max acc (a3 + a4 + a5 + a6) else acc)
        acc) acc) acc) 0

def minHighNeighbors (n3 n4 n5 n6 d : ℕ) : ℕ :=
  let b3 := if 3 * (6 - 3) < d - 2 then 0 else if d = 3 then n3 - 1 else n3
  let b4 := if 4 * (6 - 4) < d - 2 then 0 else if d = 4 then n4 - 1 else n4
  let b5 := if 5 * (6 - 5) < d - 2 then 0 else if d = 5 then n5 - 1 else n5
  let b6 := if 6 * (6 - 6) < d - 2 then 0 else if d = 6 then n6 - 1 else n6
  let target := d * (6 - d)
  (List.range (b3 + 1)).foldl (fun acc a3 =>
    (List.range (b4 + 1)).foldl (fun acc a4 =>
      (List.range (b5 + 1)).foldl (fun acc a5 =>
        (List.range (b6 + 1)).foldl (fun acc a6 =>
          if a3 + 2 * a4 + 3 * a5 + 4 * a6 == target then min acc (a3 + a4 + a5 + a6) else acc)
        acc) acc) acc) 1000

def profileConnectedCheck (n3 n4 n5 n6 : ℕ) : Bool :=
  if 3 * n3 + 8 * n4 + 15 * n5 + 24 * n6 != 72 then true
  else
    let s := 3 * n3 + 4 * n4 + 5 * n5 + 6 * n6
    if 234 < s || (234 - s) % 2 != 0 then true
    else
      let n2 := (234 - s) / 2
      let okAll :=
        validBudget n3 n4 n5 n6 2 &&
        (n3 == 0 || validBudget n3 n4 n5 n6 3) &&
        (n4 == 0 || validBudget n3 n4 n5 n6 4) &&
        (n5 == 0 || validBudget n3 n4 n5 n6 5) &&
        (n6 == 0 || validBudget n3 n4 n5 n6 6)
      if !okAll then true
      else
        let k := 24 - maxHighNeighbors2 n3 n4 n5 n6
        let z := 1 + k + (k * (k - 13) + 3) / 4
        let u3 := if n3 == 0 then 0 else n3 * ((36 - minHighNeighbors n3 n4 n5 n6 3) ^ 2 / 4)
        let u4 := if n4 == 0 then 0 else n4 * ((48 - minHighNeighbors n3 n4 n5 n6 4) ^ 2 / 4)
        let u5 := if n5 == 0 then 0 else n5 * ((60 - minHighNeighbors n3 n4 n5 n6 5) ^ 2 / 4)
        let u6 := if n6 == 0 then 0 else n6 * ((72 - minHighNeighbors n3 n4 n5 n6 6) ^ 2 / 4)
        decide (16 ≤ k ∧ (2 * z > n2 ∨ u3 + u4 + u5 + u6 < 4 * z * (n2 - z)))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- Kernel-checked finite certificate covering all 23 global moment profiles at `t = 18`:
whenever every occurring deficiency has a nonempty local neighbor budget, the minimum root
degree is at least 16 and the cross-pair bound forces the root graph to be connected. -/
theorem all_23_profiles_connected :
    ∀ n3 : Fin 25, ∀ n4 : Fin 10, ∀ n5 : Fin 5, ∀ n6 : Fin 4,
      profileConnectedCheck n3.val n4.val n5.val n6.val = true := by
  decide +kernel

/-! ## Section 2: Incidence moments, hole-neighbor identity, and deficiency bound -/

section Incidence

variable {P L : Type*} [Fintype P] [Fintype L] [DecidableEq P] [DecidableEq L]

/-- Degree of a point `p` in the block family `B`. -/
def deg (B : L → Finset P) (p : P) : ℕ :=
  (univ.filter fun l => p ∈ B l).card

/-- Deficiency `13 - deg B p` (as an integer, nonnegative once `deg B p ≤ 13`). -/
def defic (B : L → Finset P) (p : P) : ℤ :=
  13 - (deg B p : ℤ)

/-- Two distinct points form a hole if no block contains both. -/
def IsHole (B : L → Finset P) (p q : P) : Prop :=
  p ≠ q ∧ ∀ l, ¬(p ∈ B l ∧ q ∈ B l)

/-- Covered neighbors of `p`: distinct points sharing a block with `p`. -/
def coveredNbrs (B : L → Finset P) (p : P) : Finset P :=
  (univ.filter fun l => p ∈ B l).biUnion fun l => (B l).erase p

/-- Hole neighbors of `p`: distinct points sharing no block with `p`. -/
def holeNbrs (B : L → Finset P) (p : P) : Finset P :=
  (univ.erase p) \ coveredNbrs B p

omit [Fintype P] [DecidableEq L] in
lemma mem_coveredNbrs {B : L → Finset P} {p q : P} :
    q ∈ coveredNbrs B p ↔ q ≠ p ∧ ∃ l, p ∈ B l ∧ q ∈ B l := by
  simp only [coveredNbrs, mem_biUnion, mem_filter, mem_univ, true_and, mem_erase]
  constructor
  · rintro ⟨l, hp, hne, hq⟩; exact ⟨hne, l, hp, hq⟩
  · rintro ⟨hne, l, hp, hq⟩; exact ⟨l, hp, hne, hq⟩

lemma mem_holeNbrs {B : L → Finset P} {p q : P} :
    q ∈ holeNbrs B p ↔ IsHole B p q := by
  simp only [holeNbrs, mem_sdiff, mem_erase, mem_univ, and_true, mem_coveredNbrs, IsHole]
  constructor
  · rintro ⟨hqp, hnc⟩
    refine ⟨hqp.symm, fun l ⟨hp, hq⟩ => hnc ⟨hqp, l, hp, hq⟩⟩
  · rintro ⟨hpq, hnl⟩
    refine ⟨hpq.symm, fun ⟨_, l, hp, hq⟩ => hnl l ⟨hp, hq⟩⟩

omit [Fintype P] [DecidableEq L] in
lemma pencil_pairwiseDisjoint
    (B : L → Finset P)
    (hmeet : ∀ l m, l ≠ m → (B l ∩ B m).card = 1) (p : P) :
    ((univ.filter fun l => p ∈ B l : Finset L) : Set L).PairwiseDisjoint
      fun l => (B l).erase p := by
  intro l hl m hm hlm
  apply Finset.disjoint_left.mpr
  intro z hzl hzm
  have hp1 : p ∈ B l := (mem_filter.mp hl).2
  have hp2 : p ∈ B m := (mem_filter.mp hm).2
  have huniq := card_eq_one_iff_existsUnique.mp (hmeet l m hlm)
  exact (mem_erase.mp hzl).1 (huniq.unique
    (mem_inter.mpr ⟨(mem_erase.mp hzl).2, (mem_erase.mp hzm).2⟩)
    (mem_inter.mpr ⟨hp1, hp2⟩))

lemma card_coveredNbrs
    (B : L → Finset P)
    (hsize : ∀ l, (B l).card = 13)
    (hmeet : ∀ l m, l ≠ m → (B l ∩ B m).card = 1) (p : P) :
    (coveredNbrs B p).card = 12 * deg B p := by
  rw [coveredNbrs, card_biUnion (pencil_pairwiseDisjoint B hmeet p)]
  have heach : ∀ l ∈ univ.filter (fun l => p ∈ B l), ((B l).erase p).card = 12 := by
    intro l hl
    rw [card_erase_of_mem (mem_filter.mp hl).2, hsize l]
  rw [sum_congr rfl heach, sum_const, smul_eq_mul, mul_comm, deg]

lemma deg_le_13
    (B : L → Finset P) (hp : Fintype.card P = 157)
    (hsize : ∀ l, (B l).card = 13)
    (hmeet : ∀ l m, l ≠ m → (B l ∩ B m).card = 1) (p : P) :
    deg B p ≤ 13 := by
  have hsub : coveredNbrs B p ⊆ univ.erase p := by
    intro q hq
    exact mem_erase.mpr ⟨(mem_coveredNbrs.mp hq).1, mem_univ _⟩
  have hc := card_le_card hsub
  rw [card_coveredNbrs B hsize hmeet p, card_erase_of_mem (mem_univ p), card_univ, hp] at hc
  omega

lemma card_holeNbrs
    (B : L → Finset P) (hp : Fintype.card P = 157)
    (hsize : ∀ l, (B l).card = 13)
    (hmeet : ∀ l m, l ≠ m → (B l ∩ B m).card = 1) (p : P) :
    (holeNbrs B p).card = 12 * (13 - deg B p) := by
  have hsub : coveredNbrs B p ⊆ univ.erase p := by
    intro q hq
    exact mem_erase.mpr ⟨(mem_coveredNbrs.mp hq).1, mem_univ _⟩
  rw [holeNbrs, card_sdiff_of_subset hsub, card_erase_of_mem (mem_univ p), card_univ, hp,
    card_coveredNbrs B hsize hmeet p]
  have hd := deg_le_13 B hp hsize hmeet p
  omega

/-- Exact incidence moments for any 139 qualifying blocks on 157 points. -/
theorem moments_of_139
    (B : L → Finset P) (hp : Fintype.card P = 157) (hl : Fintype.card L = 139)
    (hsize : ∀ l, (B l).card = 13)
    (hmeet : ∀ l m, l ≠ m → (B l ∩ B m).card = 1) :
    (∑ p, defic B p = 234) ∧
    (∑ p, defic B p * (defic B p - 2) = 72) ∧
    (∀ l, ∑ p ∈ B l, defic B p = 18) := by
  let w (l : L) (p : P) : ℤ := if p ∈ B l then 1 else 0
  have hr_eq (p : P) : (deg B p : ℤ) = ∑ l, w l p := by
    simp [deg, w, sum_boole]
  have hrow (l : L) : ∑ p, w l p = 13 := by
    simpa [w] using (show ((B l).card : ℤ) = 13 by exact_mod_cast hsize l)
  have hdot (l m : L) : ∑ p, w l p * w m p = 1 + (if l = m then 12 else 0) := by
    have h : ∑ p, w l p * w m p = ((B l ∩ B m).card : ℤ) := by
      calc
        _ = ∑ p : P, (if p ∈ B l ∩ B m then (1 : ℤ) else 0) := by
          apply sum_congr rfl; intro p _
          by_cases h1 : p ∈ B l <;> by_cases h2 : p ∈ B m <;> simp [w, h1, h2]
        _ = _ := by rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter]
    rw [h]
    by_cases e : l = m
    · subst m; simp [hsize]
    · simp [e, hmeet l m e]
  have hw_mul (l : L) (f : P → ℤ) : ∑ p, w l p * f p = ∑ p ∈ B l, f p := by
    calc
      ∑ p, w l p * f p = ∑ p, if p ∈ B l then f p else 0 := by
        apply sum_congr rfl; intro p _; by_cases h : p ∈ B l <;> simp [w, h]
      _ = ∑ p ∈ univ.filter (· ∈ B l), f p := by rw [← Finset.sum_filter]
      _ = ∑ p ∈ B l, f p := by rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
  have hrline (l : L) : ∑ p ∈ B l, (deg B p : ℤ) = 151 := by
    calc
      ∑ p ∈ B l, (deg B p : ℤ) = ∑ p, w l p * (deg B p : ℤ) :=
        (hw_mul l (fun p => (deg B p : ℤ))).symm
      _ = ∑ p, ∑ m, w l p * w m p := by
        apply sum_congr rfl; intro p _; rw [hr_eq p, mul_sum]
      _ = ∑ m, ∑ p, w l p * w m p := sum_comm
      _ = 151 := by simp [hdot, sum_add_distrib, hl]
  have hdline (l : L) : ∑ p ∈ B l, defic B p = 18 := by
    have hsum : ∑ p ∈ B l, defic B p = ∑ p ∈ B l, (13 : ℤ) - ∑ p ∈ B l, (deg B p : ℤ) := by
      simp [defic, sum_sub_distrib]
    rw [hsum, sum_const, hsize l, hrline l]; norm_num
  have hrmass : ∑ p, (deg B p : ℤ) = 1807 := by
    simp_rw [hr_eq]; rw [sum_comm]; simp [hrow, hl]
  have hdmass : ∑ p, defic B p = 234 := by
    simp [defic, sum_sub_distrib, hp, hrmass]
  have hrsq : ∑ p, (deg B p : ℤ) * (deg B p : ℤ) = 20989 := by
    calc
      ∑ p, (deg B p : ℤ) * (deg B p : ℤ)
        = ∑ p, ∑ l, w l p * (deg B p : ℤ) := by
          apply sum_congr rfl; intro p _; rw [← sum_mul, hr_eq p]
      _ = ∑ l, ∑ p, w l p * (deg B p : ℤ) := sum_comm
      _ = ∑ l, ∑ p ∈ B l, (deg B p : ℤ) := by
          apply sum_congr rfl; intro l _; exact hw_mul l (fun p => (deg B p : ℤ))
      _ = 20989 := by simp [hrline, hl]
  have hexcess : ∑ p, defic B p * (defic B p - 2) = 72 := by
    calc
      ∑ p, defic B p * (defic B p - 2)
        = ∑ p, ((143 : ℤ) - 24 * (deg B p : ℤ) + (deg B p : ℤ) * (deg B p : ℤ)) := by
          apply sum_congr rfl; intro p _; dsimp [defic]; ring
      _ = 72 := by
          rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, hrmass, hrsq]
          simp [hp]
  exact ⟨hdmass, hexcess, hdline⟩

/-- Hole-neighbor identity (1) of `order12_deficit18.txt`:
`∑_{q ∈ holeNbrs B p} (defic B q - 2) = defic B p * (6 - defic B p)`. -/
theorem hole_neighbor_budget_139
    (B : L → Finset P) (hp : Fintype.card P = 157) (hl : Fintype.card L = 139)
    (hsize : ∀ l, (B l).card = 13)
    (hmeet : ∀ l m, l ≠ m → (B l ∩ B m).card = 1) (p : P) :
    ∑ q ∈ holeNbrs B p, (defic B q - 2) = defic B p * (6 - defic B p) := by
  obtain ⟨hdmass, _, hdline⟩ := moments_of_139 B hp hl hsize hmeet
  have hcov_sum : ∑ q ∈ coveredNbrs B p, defic B q = (deg B p : ℤ) * (18 - defic B p) := by
    rw [coveredNbrs, sum_biUnion (pencil_pairwiseDisjoint B hmeet p)]
    have heach : ∀ l ∈ univ.filter (fun l => p ∈ B l),
        ∑ q ∈ (B l).erase p, defic B q = 18 - defic B p := by
      intro l hl
      have hmem : p ∈ B l := (mem_filter.mp hl).2
      have h := add_sum_erase (B l) (defic B) hmem
      linarith [hdline l]
    rw [sum_congr rfl heach, sum_const, nsmul_eq_mul, deg]
  have hsub : coveredNbrs B p ⊆ univ.erase p := by
    intro q hq
    exact mem_erase.mpr ⟨(mem_coveredNbrs.mp hq).1, mem_univ _⟩
  have hsplit := sum_sdiff hsub (f := defic B)
  have herase : ∑ q ∈ univ.erase p, defic B q = 234 - defic B p := by
    have h := add_sum_erase univ (defic B) (mem_univ p)
    linarith
  have hhole_sum : ∑ q ∈ holeNbrs B p, defic B q =
      234 - defic B p - (deg B p : ℤ) * (18 - defic B p) := by
    rw [holeNbrs]; linarith
  have hcard : ((holeNbrs B p).card : ℤ) = 12 * defic B p := by
    rw [card_holeNbrs B hp hsize hmeet p]
    have hd := deg_le_13 B hp hsize hmeet p
    dsimp [defic]; omega
  rw [sum_sub_distrib, sum_const, nsmul_eq_mul, hcard, hhole_sum]
  dsimp [defic]; ring

/-- In a 139-block configuration with no degree-12 point, every point has deficiency at most 6. -/
theorem defic_le_6_of_no_deg12
    (B : L → Finset P) (hp : Fintype.card P = 157) (hl : Fintype.card L = 139)
    (hsize : ∀ l, (B l).card = 13)
    (hmeet : ∀ l m, l ≠ m → (B l ∩ B m).card = 1)
    (hno12 : ∀ q, deg B q ≠ 12) (p : P) :
    defic B p ≤ 6 := by
  have hnn : 0 ≤ ∑ q ∈ holeNbrs B p, (defic B q - 2) := by
    apply sum_nonneg
    intro q hq
    have hdeg_le := deg_le_13 B hp hsize hmeet q
    have hdeg_ne12 := hno12 q
    have hdeg_ne13 : deg B q ≠ 13 := by
      intro h13
      have hcard := card_holeNbrs B hp hsize hmeet q
      rw [h13] at hcard
      have hpq : p ∈ holeNbrs B q := by
        rw [mem_holeNbrs]
        have ⟨hne, hnl⟩ := mem_holeNbrs.mp hq
        exact ⟨hne.symm, fun l ⟨hq1, hp1⟩ => hnl l ⟨hp1, hq1⟩⟩
      have hpos := card_pos.mpr ⟨p, hpq⟩
      omega
    dsimp [defic]; omega
  rw [hole_neighbor_budget_139 B hp hl hsize hmeet p] at hnn
  have hdp_nn : 0 ≤ defic B p := by
    have := deg_le_13 B hp hsize hmeet p
    dsimp [defic]; omega
  nlinarith

/-! ## Section 3: Exact common-hole-neighbor counts -/

/-- Two distinct points sharing no old block have `d(p)*d(q) + 12 - d(p) - d(q)` common holes. -/
theorem card_common_holes_of_hole
    (B : L → Finset P) (hp : Fintype.card P = 157)
    (hsize : ∀ l, (B l).card = 13)
    (hmeet : ∀ l m, l ≠ m → (B l ∩ B m).card = 1)
    {p q : P} (h : IsHole B p q) :
    ((holeNbrs B p ∩ holeNbrs B q).card : ℤ) =
      defic B p * defic B q + 12 - defic B p - defic B q := by
  let Dp := univ.filter fun l => p ∈ B l
  let Dq := univ.filter fun l => q ∈ B l
  have hcov_inter : (coveredNbrs B p ∩ coveredNbrs B q).card = deg B p * deg B q := by
    -- Bijection from Dp × Dq to coveredNbrs B p ∩ coveredNbrs B q sending (l, m) to the unique point in B l ∩ B m.
    have hdisj_p := pencil_pairwiseDisjoint B hmeet p
    rw [coveredNbrs, biUnion_inter, card_biUnion]
    · have heach : ∀ l ∈ Dp, ((B l).erase p ∩ coveredNbrs B q).card = deg B q := by
        intro l hl
        have hpl : p ∈ B l := (mem_filter.mp hl).2
        have hql : q ∉ B l := fun hq => h.2 l ⟨hpl, hq⟩
        rw [coveredNbrs, inter_biUnion, card_biUnion]
        · have heach2 : ∀ m ∈ Dq, ((B l).erase p ∩ (B m).erase q).card = 1 := by
            intro m hm
            have hqm : q ∈ B m := (mem_filter.mp hm).2
            have hpm : p ∉ B m := fun hp' => h.2 m ⟨hp', hqm⟩
            have hlm : l ≠ m := fun e => hql (e ▸ hqm)
            have heq : (B l).erase p ∩ (B m).erase q = B l ∩ B m := by
              ext z; simp only [mem_inter, mem_erase]
              constructor
              · rintro ⟨⟨_, h1⟩, ⟨_, h2⟩⟩; exact ⟨h1, h2⟩
              · rintro ⟨h1, h2⟩
                exact ⟨⟨fun ez => hpm (ez ▸ h2), h1⟩, ⟨fun ez => hql (ez ▸ h1), h2⟩⟩
            rw [heq, hmeet l m hlm]
          rw [sum_congr rfl heach2, sum_const, smul_eq_mul, mul_one]; rfl
        · intro m1 hm1 m2 hm2 hm12
          exact (pencil_pairwiseDisjoint B hmeet q hm1 hm2 hm12).mono
            inter_subset_right inter_subset_right
      rw [sum_congr rfl heach, sum_const, smul_eq_mul]; rfl
    · intro l1 hl1 l2 hl2 hl12
      exact (hdisj_p hl1 hl2 hl12).mono inter_subset_left inter_subset_left
  -- Inclusion-exclusion on U = univ \ {p, q} (size 155).
  let U : Finset P := (univ.erase p).erase q
  have hq_not_cov_p : q ∉ coveredNbrs B p := by
    intro hc; obtain ⟨_, l, hp1, hq1⟩ := mem_coveredNbrs.mp hc; exact h.2 l ⟨hp1, hq1⟩
  have hp_not_cov_q : p ∉ coveredNbrs B q := by
    intro hc; obtain ⟨_, l, hq1, hp1⟩ := mem_coveredNbrs.mp hc; exact h.2 l ⟨hp1, hq1⟩
  have hsub_p : coveredNbrs B p ⊆ U := by
    intro z hz
    exact mem_erase.mpr ⟨fun ez => hq_not_cov_p (ez ▸ hz),
      mem_erase.mpr ⟨(mem_coveredNbrs.mp hz).1, mem_univ _⟩⟩
  have hsub_q : coveredNbrs B q ⊆ U := by
    intro z hz
    exact mem_erase.mpr ⟨(mem_coveredNbrs.mp hz).1,
      mem_erase.mpr ⟨fun ez => hp_not_cov_q (ez ▸ hz), mem_univ _⟩⟩
  have hinter_eq : holeNbrs B p ∩ holeNbrs B q = U \ (coveredNbrs B p ∪ coveredNbrs B q) := by
    ext z
    simp only [mem_inter, holeNbrs, mem_sdiff, mem_erase, mem_univ, and_true, mem_union, U]
    tauto
  have hU_card : U.card = 155 := by
    have hq_mem : q ∈ univ.erase p := mem_erase.mpr ⟨h.1.symm, mem_univ _⟩
    rw [card_erase_of_mem hq_mem, card_erase_of_mem (mem_univ p), card_univ, hp]
  have hunion := card_union_add_card_inter (coveredNbrs B p) (coveredNbrs B q)
  rw [hinter_eq, card_sdiff_of_subset (union_subset hsub_p hsub_q), hU_card]
  have hcp := card_coveredNbrs B hsize hmeet p
  have hcq := card_coveredNbrs B hsize hmeet q
  have hdp := deg_le_13 B hp hsize hmeet p
  have hdq := deg_le_13 B hp hsize hmeet q
  have hcast : ((155 - (coveredNbrs B p ∪ coveredNbrs B q).card : ℕ) : ℤ) =
      155 - ((coveredNbrs B p ∪ coveredNbrs B q).card : ℤ) := by
    have hle : (coveredNbrs B p ∪ coveredNbrs B q).card ≤ 155 := by
      simpa [hU_card] using card_le_card (union_subset hsub_p hsub_q)
    omega
  rw [hcast]
  have hunion_z : ((coveredNbrs B p ∪ coveredNbrs B q).card : ℤ) =
      12 * (deg B p : ℤ) + 12 * (deg B q : ℤ) - (deg B p : ℤ) * (deg B q : ℤ) := by
    have hz : ((coveredNbrs B p ∪ coveredNbrs B q).card : ℤ) +
        ((coveredNbrs B p ∩ coveredNbrs B q).card : ℤ) =
        ((coveredNbrs B p).card : ℤ) + ((coveredNbrs B q).card : ℤ) := by
      exact_mod_cast hunion
    rw [hcp, hcq, hcov_inter] at hz
    push_cast at hz
    linarith
  rw [hunion_z]; dsimp [defic]; ring

/-- Two distinct points sharing an old block have `d(p)*d(q)` common hole neighbors. -/
theorem card_common_holes_of_covered
    (B : L → Finset P) (hp : Fintype.card P = 157)
    (hsize : ∀ l, (B l).card = 13)
    (hmeet : ∀ l m, l ≠ m → (B l ∩ B m).card = 1)
    {p q : P} (hne : p ≠ q) {l0 : L} (hp0 : p ∈ B l0) (hq0 : q ∈ B l0) :
    ((holeNbrs B p ∩ holeNbrs B q).card : ℤ) = defic B p * defic B q := by
  have huniq_line : ∀ l, p ∈ B l → q ∈ B l → l = l0 := by
    intro l hpl hql
    by_contra hne_l
    have h1 := card_eq_one_iff_existsUnique.mp (hmeet l l0 hne_l)
    exact hne (h1.unique (mem_inter.mpr ⟨hpl, hp0⟩) (mem_inter.mpr ⟨hql, hq0⟩))
  let Dp' := (univ.filter fun l => p ∈ B l).erase l0
  let Dq' := (univ.filter fun l => q ∈ B l).erase l0
  have hl0_p : l0 ∈ univ.filter fun l => p ∈ B l := mem_filter.mpr ⟨mem_univ _, hp0⟩
  have hl0_q : l0 ∈ univ.filter fun l => q ∈ B l := mem_filter.mpr ⟨mem_univ _, hq0⟩
  have hDp'_card : Dp'.card = deg B p - 1 := by
    rw [card_erase_of_mem hl0_p, deg]
  have hDq'_card : Dq'.card = deg B q - 1 := by
    rw [card_erase_of_mem hl0_q, deg]
  have hdeg_p_pos : 1 ≤ deg B p := card_pos.mpr ⟨l0, hl0_p⟩
  have hdeg_q_pos : 1 ≤ deg B q := card_pos.mpr ⟨l0, hl0_q⟩
  -- Split coveredNbrs B p ∩ coveredNbrs B q into ((B l0).erase p).erase q (size 11)
  -- and the intersections of Dp' with Dq' (size (deg p - 1)*(deg q - 1)).
  let L0' := ((B l0).erase p).erase q
  let Rest := Dp'.biUnion fun l => (B l).erase p ∩ Dq'.biUnion (fun m => (B m).erase q)
  have hcov_split : coveredNbrs B p ∩ coveredNbrs B q = L0' ∪ Rest := by
    ext z
    simp only [mem_inter, mem_coveredNbrs, mem_union, L0', Rest, mem_erase, mem_biUnion,
      mem_filter, mem_univ, true_and, Dp', Dq']
    constructor
    · rintro ⟨⟨hzp, l, hpl, hzl⟩, ⟨hzq, m, hqm, hzm⟩⟩
      by_cases hl : l = l0
      · subst hl; left; exact ⟨hzq, hzp, hzl⟩
      · right
        have hm : m ≠ l0 := by
          intro e; rw [e] at hzm
          have h1 := card_eq_one_iff_existsUnique.mp (hmeet l l0 hl)
          exact hzp (h1.unique (mem_inter.mpr ⟨hzl, hzm⟩) (mem_inter.mpr ⟨hpl, hp0⟩))
        exact ⟨l, ⟨hl, hpl⟩, ⟨hzp, hzl⟩, m, ⟨hm, hqm⟩, hzq, hzm⟩
    · rintro (⟨hzq, hzp, hzl0⟩ | ⟨l, ⟨_, hpl⟩, ⟨hzp, hzl⟩, m, ⟨_, hqm⟩, hzq, hzm⟩)
      · exact ⟨⟨hzp, l0, hp0, hzl0⟩, ⟨hzq, l0, hq0, hzl0⟩⟩
      · exact ⟨⟨hzp, l, hpl, hzl⟩, ⟨hzq, m, hqm, hzm⟩⟩
  have hdisj_LR : Disjoint L0' Rest := by
    rw [Finset.disjoint_left]
    intro z hzL hzR
    simp only [L0', mem_erase] at hzL
    simp only [Rest, mem_biUnion, mem_inter, mem_erase, mem_filter, mem_univ, true_and, Dp'] at hzR
    obtain ⟨l, ⟨hl0, hpl⟩, ⟨hzp, hzl⟩, _⟩ := hzR
    have h1 := card_eq_one_iff_existsUnique.mp (hmeet l l0 hl0)
    exact hzp (h1.unique (mem_inter.mpr ⟨hzl, hzL.2.2⟩) (mem_inter.mpr ⟨hpl, hp0⟩))
  have hL0'_card : L0'.card = 11 := by
    have hq_mem : q ∈ (B l0).erase p := mem_erase.mpr ⟨hne.symm, hq0⟩
    rw [card_erase_of_mem hq_mem, card_erase_of_mem hp0, hsize l0]
  have hRest_card : Rest.card = (deg B p - 1) * (deg B q - 1) := by
    rw [card_biUnion]
    · have heach : ∀ l ∈ Dp', ((B l).erase p ∩ Dq'.biUnion (fun m => (B m).erase q)).card =
          deg B q - 1 := by
        intro l hl
        have hl0 : l ≠ l0 := (mem_erase.mp hl).1
        have hpl : p ∈ B l := (mem_filter.mp (mem_erase.mp hl).2).2
        have hql : q ∉ B l := fun hq' => hl0 (huniq_line l hpl hq')
        rw [inter_biUnion, card_biUnion]
        · have heach2 : ∀ m ∈ Dq', ((B l).erase p ∩ (B m).erase q).card = 1 := by
            intro m hm
            have hm0 : m ≠ l0 := (mem_erase.mp hm).1
            have hqm : q ∈ B m := (mem_filter.mp (mem_erase.mp hm).2).2
            have hpm : p ∉ B m := fun hp' => hm0 (huniq_line m hp' hqm)
            have hlm : l ≠ m := fun e => hql (e ▸ hqm)
            have heq : (B l).erase p ∩ (B m).erase q = B l ∩ B m := by
              ext z; simp only [mem_inter, mem_erase]
              constructor
              · rintro ⟨⟨_, h1⟩, ⟨_, h2⟩⟩; exact ⟨h1, h2⟩
              · rintro ⟨h1, h2⟩
                exact ⟨⟨fun ez => hpm (ez ▸ h2), h1⟩, ⟨fun ez => hql (ez ▸ h1), h2⟩⟩
            rw [heq, hmeet l m hlm]
          rw [sum_congr rfl heach2, sum_const, smul_eq_mul, mul_one, hDq'_card]
        · intro m1 hm1 m2 hm2 hm12
          exact (pencil_pairwiseDisjoint B hmeet q (mem_erase.mp hm1).2 (mem_erase.mp hm2).2 hm12).mono
            inter_subset_right inter_subset_right
      rw [sum_congr rfl heach, sum_const, smul_eq_mul, hDp'_card]
    · intro l1 hl1 l2 hl2 hl12
      exact (pencil_pairwiseDisjoint B hmeet p (mem_erase.mp hl1).2 (mem_erase.mp hl2).2 hl12).mono
        inter_subset_left inter_subset_left
  have hcov_inter : (coveredNbrs B p ∩ coveredNbrs B q).card =
      11 + (deg B p - 1) * (deg B q - 1) := by
    rw [hcov_split, card_union_of_disjoint hdisj_LR, hL0'_card, hRest_card]
  -- Inclusion-exclusion on U = univ \ {p, q} (size 155), noting q ∈ coveredNbrs B p and p ∈ coveredNbrs B q!
  let U : Finset P := (univ.erase p).erase q
  let Cp' := (coveredNbrs B p).erase q
  let Cq' := (coveredNbrs B q).erase p
  have hq_in_cp : q ∈ coveredNbrs B p := mem_coveredNbrs.mpr ⟨hne.symm, l0, hp0, hq0⟩
  have hp_in_cq : p ∈ coveredNbrs B q := mem_coveredNbrs.mpr ⟨hne, l0, hq0, hp0⟩
  have hCp'_card : Cp'.card = 12 * deg B p - 1 := by
    rw [card_erase_of_mem hq_in_cp, card_coveredNbrs B hsize hmeet p]
  have hCq'_card : Cq'.card = 12 * deg B q - 1 := by
    rw [card_erase_of_mem hp_in_cq, card_coveredNbrs B hsize hmeet q]
  have hCp'Cq'_inter : Cp' ∩ Cq' = coveredNbrs B p ∩ coveredNbrs B q := by
    ext z; simp only [Cp', Cq', mem_inter, mem_erase]
    constructor
    · rintro ⟨⟨_, h1⟩, ⟨_, h2⟩⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨(mem_coveredNbrs.mp h2).1, h1⟩, ⟨(mem_coveredNbrs.mp h1).1, h2⟩⟩
  have hsub_p : Cp' ⊆ U := by
    intro z hz
    have ⟨hzq, hzp⟩ := mem_erase.mp hz
    exact mem_erase.mpr ⟨hzq, mem_erase.mpr ⟨(mem_coveredNbrs.mp hzp).1, mem_univ _⟩⟩
  have hsub_q : Cq' ⊆ U := by
    intro z hz
    have ⟨hzp, hzq⟩ := mem_erase.mp hz
    exact mem_erase.mpr ⟨(mem_coveredNbrs.mp hzq).1, mem_erase.mpr ⟨hzp, mem_univ _⟩⟩
  have hinter_eq : holeNbrs B p ∩ holeNbrs B q = U \ (Cp' ∪ Cq') := by
    ext z
    simp only [mem_inter, holeNbrs, mem_sdiff, mem_erase, mem_univ, and_true, mem_union, U, Cp', Cq']
    tauto
  have hU_card : U.card = 155 := by
    have hq_mem : q ∈ univ.erase p := mem_erase.mpr ⟨hne.symm, mem_univ _⟩
    rw [card_erase_of_mem hq_mem, card_erase_of_mem (mem_univ p), card_univ, hp]
  rw [hinter_eq, card_sdiff_of_subset (union_subset hsub_p hsub_q), hU_card]
  have hunion := card_union_add_card_inter Cp' Cq'
  rw [hCp'Cq'_inter, hcov_inter, hCp'_card, hCq'_card] at hunion
  have hle : (Cp' ∪ Cq').card ≤ 155 := by
    simpa [hU_card] using card_le_card (union_subset hsub_p hsub_q)
  have hcast : ((155 - (Cp' ∪ Cq').card : ℕ) : ℤ) = 155 - ((Cp' ∪ Cq').card : ℤ) := by omega
  rw [hcast]
  have hdp := deg_le_13 B hp hsize hmeet p
  have hdq := deg_le_13 B hp hsize hmeet q
  have hz : ((Cp' ∪ Cq').card : ℤ) + (11 + ((deg B p - 1 : ℕ) : ℤ) * ((deg B q - 1 : ℕ) : ℤ)) =
      ((12 * deg B p - 1 : ℕ) : ℤ) + ((12 * deg B q - 1 : ℕ) : ℤ) := by
    exact_mod_cast hunion
  have h1 : ((deg B p - 1 : ℕ) : ℤ) = (deg B p : ℤ) - 1 := by omega
  have h2 : ((deg B q - 1 : ℕ) : ℤ) = (deg B q : ℤ) - 1 := by omega
  have h3 : ((12 * deg B p - 1 : ℕ) : ℤ) = 12 * (deg B p : ℤ) - 1 := by omega
  have h4 : ((12 * deg B q - 1 : ℕ) : ℤ) = 12 * (deg B q : ℤ) - 1 := by omega
  rw [h1, h2, h3, h4] at hz
  dsimp [defic]; nlinarith

/-! ## Section 4: The K₉,₉ mod-3 reflection elimination lemma -/

/-- In the `K₉,₉` case of `order12_deficit18.txt` (lines 167–179), any `{-1, 0, 1}`
reflection sign assignment supported on at most 12 points, each lying on 10 old blocks
and summing to `0 (mod 3)` on every old block, must vanish identically. -/
theorem no_small_mod3_reflection
    (B : L → Finset P)
    (hmeet : ∀ l m, l ≠ m → (B l ∩ B m).card = 1)
    (s : P → ℤ) (hvals : ∀ p, s p = -1 ∨ s p = 0 ∨ s p = 1)
    (hmod : ∀ l, 3 ∣ ∑ p ∈ B l, s p)
    (hdeg10 : ∀ p, s p ≠ 0 → deg B p = 10)
    (hsmall : (univ.filter fun p => s p ≠ 0).card ≤ 12) :
    ∀ p, s p = 0 := by
  let Pos := univ.filter fun p => s p = 1
  let Neg := univ.filter fun p => s p = -1
  have hdisj : Disjoint Pos Neg := by
    rw [Finset.disjoint_left]; intro p hp hn
    have h1 := (mem_filter.mp hp).2
    have h2 := (mem_filter.mp hn).2
    omega
  have hsupp : (univ.filter fun p => s p ≠ 0) = Pos ∪ Neg := by
    ext p; simp only [Pos, Neg, mem_filter, mem_univ, true_and, mem_union]
    rcases hvals p with h | h | h <;> omega
  have hcd : Pos.card + Neg.card ≤ 12 := by
    rw [← card_union_of_disjoint hdisj, ← hsupp]; exact hsmall
  -- Pencil budget at a positive point p: 2 * Neg.card + Pos.card ≥ 21 (and if Neg = ∅, Pos.card ≥ 21).
  have hpos_budget : ∀ p ∈ Pos, 2 * Neg.card + Pos.card ≥ 21 := by
    intro p hp
    have hsp : s p = 1 := (mem_filter.mp hp).2
    have hdp : deg B p = 10 := hdeg10 p (by omega)
    let Dp := univ.filter fun l => p ∈ B l
    have hline_cost : ∀ l ∈ Dp,
        2 * ((B l).erase p ∩ Neg).card + ((B l).erase p ∩ Pos).card ≥ 2 := by
      intro l hl
      have hpl : p ∈ B l := (mem_filter.mp hl).2
      have hdiv := hmod l
      -- Split ∑_{q ∈ B l} s q = 1 + |((B l).erase p) ∩ Pos| - |((B l).erase p) ∩ Neg|
      have hsum_eq : ∑ q ∈ B l, s q =
          1 + (((B l).erase p ∩ Pos).card : ℤ) - (((B l).erase p ∩ Neg).card : ℤ) := by
        rw [← add_sum_erase (B l) s hpl, hsp]
        have hpos_sum : (((B l).erase p ∩ Pos).card : ℤ) =
            ∑ q ∈ (B l).erase p, if s q = 1 then (1 : ℤ) else 0 := by
          rw [sum_boole]; norm_cast; congr 1; ext q; simp [Pos, and_assoc]
        have hneg_sum : (((B l).erase p ∩ Neg).card : ℤ) =
            ∑ q ∈ (B l).erase p, if s q = -1 then (1 : ℤ) else 0 := by
          rw [sum_boole]; norm_cast; congr 1; ext q; simp [Neg, and_assoc]
        rw [hpos_sum, hneg_sum, add_sub_assoc, ← sum_sub_distrib]
        congr 1; apply sum_congr rfl; intro q _
        rcases hvals q with h | h | h <;> simp [h]
      rw [hsum_eq] at hdiv
      omega
    have hsum_neg : ∑ l ∈ Dp, ((B l).erase p ∩ Neg).card ≤ Neg.card := by
      rw [← card_biUnion]
      · exact card_le_card (biUnion_subset.mpr fun _ _ => inter_subset_right)
      · intro l1 hl1 l2 hl2 hl12
        exact (pencil_pairwiseDisjoint B hmeet p hl1 hl2 hl12).mono
          inter_subset_left inter_subset_left
    have hsum_pos : ∑ l ∈ Dp, ((B l).erase p ∩ Pos).card ≤ Pos.card - 1 := by
      rw [← card_biUnion]
      · have hsub : Dp.biUnion (fun l => (B l).erase p ∩ Pos) ⊆ Pos.erase p := by
          refine biUnion_subset.mpr fun l _ => ?_
          intro z hz
          exact mem_erase.mpr ⟨(mem_erase.mp (mem_inter.mp hz).1).1, (mem_inter.mp hz).2⟩
        have hc := card_le_card hsub
        rw [card_erase_of_mem hp] at hc
        exact hc
      · intro l1 hl1 l2 hl2 hl12
        exact (pencil_pairwiseDisjoint B hmeet p hl1 hl2 hl12).mono
          inter_subset_left inter_subset_left
    have htot : 20 ≤ ∑ l ∈ Dp, (2 * ((B l).erase p ∩ Neg).card + ((B l).erase p ∩ Pos).card) := by
      calc
        20 = ∑ _l ∈ Dp, 2 := by simp [Dp, deg] at hdp ⊢; rw [hdp]
        _ ≤ _ := sum_le_sum hline_cost
    rw [sum_add_distrib, ← mul_sum] at htot
    have hp_pos : 1 ≤ Pos.card := card_pos.mpr ⟨p, hp⟩
    omega
  -- Symmetric pencil budget at a negative point p: 2 * Pos.card + Neg.card ≥ 21.
  have hneg_budget : ∀ p ∈ Neg, 2 * Pos.card + Neg.card ≥ 21 := by
    intro p hp
    have hsp : s p = -1 := (mem_filter.mp hp).2
    have hdp : deg B p = 10 := hdeg10 p (by omega)
    let Dp := univ.filter fun l => p ∈ B l
    have hline_cost : ∀ l ∈ Dp,
        2 * ((B l).erase p ∩ Pos).card + ((B l).erase p ∩ Neg).card ≥ 2 := by
      intro l hl
      have hpl : p ∈ B l := (mem_filter.mp hl).2
      have hdiv := hmod l
      have hsum_eq : ∑ q ∈ B l, s q =
          -1 + (((B l).erase p ∩ Pos).card : ℤ) - (((B l).erase p ∩ Neg).card : ℤ) := by
        rw [← add_sum_erase (B l) s hpl, hsp]
        have hpos_sum : (((B l).erase p ∩ Pos).card : ℤ) =
            ∑ q ∈ (B l).erase p, if s q = 1 then (1 : ℤ) else 0 := by
          rw [sum_boole]; norm_cast; congr 1; ext q; simp [Pos, and_assoc]
        have hneg_sum : (((B l).erase p ∩ Neg).card : ℤ) =
            ∑ q ∈ (B l).erase p, if s q = -1 then (1 : ℤ) else 0 := by
          rw [sum_boole]; norm_cast; congr 1; ext q; simp [Neg, and_assoc]
        rw [hpos_sum, hneg_sum, add_sub_assoc, ← sum_sub_distrib]
        congr 1; apply sum_congr rfl; intro q _
        rcases hvals q with h | h | h <;> simp [h]
      rw [hsum_eq] at hdiv
      omega
    have hsum_pos : ∑ l ∈ Dp, ((B l).erase p ∩ Pos).card ≤ Pos.card := by
      rw [← card_biUnion]
      · exact card_le_card (biUnion_subset.mpr fun _ _ => inter_subset_right)
      · intro l1 hl1 l2 hl2 hl12
        exact (pencil_pairwiseDisjoint B hmeet p hl1 hl2 hl12).mono
          inter_subset_left inter_subset_left
    have hsum_neg : ∑ l ∈ Dp, ((B l).erase p ∩ Neg).card ≤ Neg.card - 1 := by
      rw [← card_biUnion]
      · have hsub : Dp.biUnion (fun l => (B l).erase p ∩ Neg) ⊆ Neg.erase p := by
          refine biUnion_subset.mpr fun l _ => ?_
          intro z hz
          exact mem_erase.mpr ⟨(mem_erase.mp (mem_inter.mp hz).1).1, (mem_inter.mp hz).2⟩
        have hc := card_le_card hsub
        rw [card_erase_of_mem hp] at hc
        exact hc
      · intro l1 hl1 l2 hl2 hl12
        exact (pencil_pairwiseDisjoint B hmeet p hl1 hl2 hl12).mono
          inter_subset_left inter_subset_left
    have htot : 20 ≤ ∑ l ∈ Dp, (2 * ((B l).erase p ∩ Pos).card + ((B l).erase p ∩ Neg).card) := by
      calc
        20 = ∑ _l ∈ Dp, 2 := by simp [Dp, deg] at hdp ⊢; rw [hdp]
        _ ≤ _ := sum_le_sum hline_cost
    rw [sum_add_distrib, ← mul_sum] at htot
    have hn_pos : 1 ≤ Neg.card := card_pos.mpr ⟨p, hp⟩
    omega
  intro p
  by_contra hne
  rcases hvals p with h | h | h
  · have hb := hneg_budget p (mem_filter.mpr ⟨mem_univ _, h⟩)
    by_cases hpe : Pos.Nonempty
    · obtain ⟨q, hq⟩ := hpe
      have hb2 := hpos_budget q hq
      omega
    · rw [not_nonempty_iff_eq_empty] at hpe
      simp [hpe] at hb hcd; omega
  · exact hne h
  · have hb := hpos_budget p (mem_filter.mpr ⟨mem_univ _, h⟩)
    by_cases hne' : Neg.Nonempty
    · obtain ⟨q, hq⟩ := hne'
      have hb2 := hneg_budget q hq
      omega
    · rw [not_nonempty_iff_eq_empty] at hne'
      simp [hne'] at hb hcd; omega

/-! ## Section 5: Nonbipartite case — eliminating half-integral and negative coordinates -/

/-- In the nonbipartite case of `order12_deficit18.txt` (lines 117–124), no point
can have strictly half-integral projected coordinates: any such point has deficiency
`4, 5` or `6`, and every old block through it must contain a second such point. -/
theorem nonbipartite_no_half_integral
    (B : L → Finset P) (hp : Fintype.card P = 157) (hl : Fintype.card L = 139)
    (hsize : ∀ l, (B l).card = 13)
    (hmeet : ∀ l m, l ≠ m → (B l ∩ B m).card = 1)
    (hno12 : ∀ q, deg B q ≠ 12)
    (H : Finset P)
    (hdef : ∀ p ∈ H, 4 ≤ defic B p)
    (heven : ∀ p ∈ H, ∀ l, p ∈ B l → ∃ q ∈ H, q ≠ p ∧ q ∈ B l) :
    H = ∅ := by
  by_contra hne
  obtain ⟨p0, hp0⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  obtain ⟨_, hexcess, _⟩ := moments_of_139 B hp hl hsize hmeet
  -- Every point has nonnegative excess d*(d-2) ≥ 0 because d ≠ 1.
  have hnonneg : ∀ q : P, 0 ≤ defic B q * (defic B q - 2) := by
    intro q
    have hle := deg_le_13 B hp hsize hmeet q
    have hne12 := hno12 q
    dsimp [defic]
    have : 13 - (deg B q : ℤ) = 0 ∨ 2 ≤ 13 - (deg B q : ℤ) := by omega
    rcases this with h0 | h2
    · rw [h0]; norm_num
    · nlinarith
  -- Any point p ∈ H gives at least deg B p + 1 points in H via its pencil.
  have hpencil_lb : ∀ p ∈ H, deg B p + 1 ≤ H.card := by
    intro p hpH
    let Dp := univ.filter fun l => p ∈ B l
    have hsub : Dp.biUnion (fun l => (B l).erase p ∩ H) ⊆ H.erase p := by
      refine biUnion_subset.mpr fun l _ => ?_
      intro z hz
      exact mem_erase.mpr ⟨(mem_erase.mp (mem_inter.mp hz).1).1, (mem_inter.mp hz).2⟩
    have hcard_each : ∀ l ∈ Dp, 1 ≤ ((B l).erase p ∩ H).card := by
      intro l hl
      obtain ⟨q, hqH, hqp, hql⟩ := heven p hpH l (mem_filter.mp hl).2
      exact card_pos.mpr ⟨q, mem_inter.mpr ⟨mem_erase.mpr ⟨hqp, hql⟩, hqH⟩⟩
    have hbi : deg B p ≤ (Dp.biUnion (fun l => (B l).erase p ∩ H)).card := by
      rw [card_biUnion]
      · calc
          deg B p = ∑ _l ∈ Dp, 1 := by simp [Dp, deg]
          _ ≤ _ := sum_le_sum hcard_each
      · intro l1 hl1 l2 hl2 hl12
        exact (pencil_pairwiseDisjoint B hmeet p hl1 hl2 hl12).mono
          inter_subset_left inter_subset_left
    have hle := card_le_card hsub
    rw [card_erase_of_mem hpH] at hle
    have hpos : 1 ≤ H.card := card_pos.mpr ⟨p, hpH⟩
    omega
  -- Case split on whether some point of H has deficiency 4 or all have deficiency ≥ 5.
  by_cases h4 : ∃ p ∈ H, defic B p = 4
  · obtain ⟨p, hpH, hdp4⟩ := h4
    have hdeg9 : deg B p = 9 := by dsimp [defic] at hdp4; omega
    have hlb : 10 ≤ H.card := by have := hpencil_lb p hpH; omega
    have hcost : (8 : ℤ) * (H.card : ℤ) ≤ ∑ q ∈ H, defic B q * (defic B q - 2) := by
      calc
        (8 : ℤ) * (H.card : ℤ) = ∑ _q ∈ H, (8 : ℤ) := by simp [mul_comm]
        _ ≤ _ := sum_le_sum fun q hq => by have := hdef q hq; nlinarith
    have hle72 : ∑ q ∈ H, defic B q * (defic B q - 2) ≤ 72 := by
      rw [← hexcess]
      exact sum_le_univ_sum_of_nonneg hnonneg
    omega
  · push Not at h4
    have hge5 : ∀ q ∈ H, 5 ≤ defic B q := by
      intro q hq; have h1 := hdef q hq; have h2 := h4 q hq; omega
    have hle6 := defic_le_6_of_no_deg12 B hp hl hsize hmeet hno12 p0
    have hdeg7 : 7 ≤ deg B p0 := by dsimp [defic] at hle6; omega
    have hlb : 8 ≤ H.card := by have := hpencil_lb p0 hp0; omega
    have hcost : (15 : ℤ) * (H.card : ℤ) ≤ ∑ q ∈ H, defic B q * (defic B q - 2) := by
      calc
        (15 : ℤ) * (H.card : ℤ) = ∑ _q ∈ H, (15 : ℤ) := by simp [mul_comm]
        _ ≤ _ := sum_le_sum fun q hq => by have := hge5 q hq; nlinarith
    have hle72 : ∑ q ∈ H, defic B q * (defic B q - 2) ≤ 72 := by
      rw [← hexcess]
      exact sum_le_univ_sum_of_nonneg hnonneg
    omega

end Incidence

/-- In the nonbipartite integral case of `order12_deficit18.txt` (lines 126–132),
an integral vector `y` of squared norm `≤ 6` whose edge sums are in `{0, 1}` on a
graph with `deg(i) + deg(j) ≥ 18` and `deg(j) ≤ 12` at nonzero coordinates must take
values in `{0, 1}`. -/
theorem nonbipartite_zero_one_of_integral
    {V : Type*} [Fintype V] [DecidableEq V]
    (adj : V → V → Prop) [DecidableRel adj]
    (hnoniso : ∀ i, ∃ j, adj i j)
    (hdeg_sum : ∀ i j, adj i j →
      18 ≤ (univ.filter (adj i)).card + (univ.filter (adj j)).card)
    (y : V → ℤ)
    (hedge : ∀ i j, adj i j → y i + y j = 0 ∨ y i + y j = 1)
    (hnz_deg : ∀ j, y j ≠ 0 → (univ.filter (adj j)).card ≤ 12)
    (hnorm : ∑ i, y i * y i ≤ 6) :
    ∀ i, y i = 0 ∨ y i = 1 := by
  have hnonneg : ∀ i, 0 ≤ y i := by
    intro i
    by_contra hneg
    push Not at hneg
    have hnbr_pos : ∀ j ∈ univ.filter (adj i), 1 ≤ y j := by
      intro j hj
      have hadj : adj i j := (mem_filter.mp hj).2
      rcases hedge i j hadj with h0 | h1 <;> omega
    have hdeg_ge6 : 6 ≤ (univ.filter (adj i)).card := by
      obtain ⟨j, hj⟩ := hnoniso i
      have hj_pos : 1 ≤ y j := hnbr_pos j (mem_filter.mpr ⟨mem_univ _, hj⟩)
      have hj_deg := hnz_deg j (by omega)
      have hsum := hdeg_sum i j hj
      omega
    -- If adj i i then y i + y i ≥ 0 contradicts y i < 0.
    have hirr : i ∉ univ.filter (adj i) := by
      intro hi
      have h := hedge i i (mem_filter.mp hi).2
      omega
    have hsq_ge7 : 7 ≤ ∑ k ∈ insert i (univ.filter (adj i)), y k * y k := by
      rw [sum_insert hirr]
      have hi_sq : 1 ≤ y i * y i := by nlinarith
      have hnbr_sq : ((univ.filter (adj i)).card : ℤ) ≤ ∑ j ∈ univ.filter (adj i), y j * y j := by
        calc
          ((univ.filter (adj i)).card : ℤ) = ∑ _j ∈ univ.filter (adj i), (1 : ℤ) := by simp
          _ ≤ _ := sum_le_sum fun j hj => by have := hnbr_pos j hj; nlinarith
      omega
    have hle6 : ∑ k ∈ insert i (univ.filter (adj i)), y k * y k ≤ 6 := by
      calc
        _ ≤ ∑ k : V, y k * y k := sum_le_univ_sum_of_nonneg fun k => mul_self_nonneg (y k)
        _ ≤ 6 := hnorm
    omega
  intro i
  obtain ⟨j, hj⟩ := hnoniso i
  have hi := hnonneg i
  have hj0 := hnonneg j
  rcases hedge i j hj with h0 | h1 <;> omega

/-- A `{0, 1}` coordinate vector of weight 13 that sums to 1 on every old block
defines a new 13-point block meeting every old block in one point. -/
theorem new_block_of_zero_one_coord
    {P L : Type*} [Fintype P] [DecidableEq P]
    (B : L → Finset P)
    (x : P → ℕ) (h01 : ∀ p, x p = 0 ∨ x p = 1)
    (hcard : ∑ p, x p = 13)
    (hmeet_sum : ∀ l, ∑ p ∈ B l, x p = 1) :
    ∃ N : Finset P, N.card = 13 ∧ ∀ l, (N ∩ B l).card = 1 := by
  let N := univ.filter fun p => x p = 1
  have hboole : ∀ S : Finset P, ∑ p ∈ S, x p = (S ∩ N).card := by
    intro S
    have h : ∑ p ∈ S, x p = ∑ p ∈ S, if p ∈ N then 1 else 0 := by
      apply sum_congr rfl; intro p _
      rcases h01 p with h0 | h1
      · simp [N, h0]
      · simp [N, h1]
    rw [h, Finset.sum_boole, Nat.cast_id, Finset.filter_mem_eq_inter]
  refine ⟨N, ?_, ?_⟩
  · have h1 := hboole univ
    rw [univ_inter] at h1
    omega
  · intro l
    have h1 := hboole (B l)
    have h2 := hmeet_sum l
    rw [inter_comm] at h1
    omega

/-! ## Section 6: Polynomial bound excluding E₆, E₇, E₈ and K₉,₉ matrix classification -/

/-- Spherical two-distance polynomial bound (`order12_deficit18.txt`, lines 92–94):
any `n` vectors in `ℝ^r` with `⟨u i, u i⟩ = 2` and `⟨u i, u j⟩ ∈ {0, 1}` for `i ≠ j`
satisfy `n ≤ r * (r + 3) / 2` (equivalently `2 * n ≤ r * (r + 3)`).
For `r ≤ 8`, this forces `n ≤ 44 < 81`, ruling out `E₆`, `E₇`, and `E₈`. -/
theorem root_two_distance_bound {n r : ℕ}
    (u : Fin n → Fin r → ℝ)
    (hdiag : ∀ i, ∑ a : Fin r, u i a * u i a = 2)
    (hoff : ∀ i j, i ≠ j →
      (∑ a : Fin r, u i a * u j a = 0) ∨ (∑ a : Fin r, u i a * u j a = 1)) :
    2 * n ≤ r * (r + 3) := by
  -- Map each vector u i to the vector of coefficients of the polynomial
  -- f_i(x) = ⟨u i, x⟩ * (⟨u i, x⟩ - 1) in the basis of r linear terms and
  -- r*(r+1)/2 upper-triangular quadratic terms (indexed by {p : Fin r × Fin r // p.1 ≤ p.2}).
  let Q := { p : Fin r × Fin r // p.1 ≤ p.2 }
  let Φ : Fin n → (Fin r ⊕ Q) → ℝ := fun i k =>
    match k with
    | Sum.inl a => -u i a
    | Sum.inr ⟨⟨a, b⟩, _⟩ => if a = b then u i a * u i b else 2 * (u i a * u i b)
  let Ψ : Fin n → (Fin r ⊕ Q) → ℝ := fun j k =>
    match k with
    | Sum.inl a => u j a
    | Sum.inr ⟨⟨a, b⟩, _⟩ => u j a * u j b
  have hpair : ∀ i j : Fin n, ∑ k : Fin r ⊕ Q, Φ i k * Ψ j k =
      (∑ a : Fin r, u i a * u j a) * ((∑ a : Fin r, u i a * u j a) - 1) := by
    intro i j
    rw [Fintype.sum_sum_type]
    have hlin : ∑ a : Fin r, Φ i (Sum.inl a) * Ψ j (Sum.inl a) =
        -(∑ a : Fin r, u i a * u j a) := by
      simp [Φ, Ψ, Finset.sum_neg_distrib]
    have hquad : ∑ q : Q, Φ i (Sum.inr q) * Ψ j (Sum.inr q) =
        (∑ a : Fin r, u i a * u j a) * (∑ b : Fin r, u i b * u j b) := by
      rw [Finset.sum_mul_sum]
      -- Split ∑_{a, b} (u i a * u j a) * (u i b * u j b) into diagonal, upper (a < b), and lower (b < a).
      let g : Fin r × Fin r → ℝ := fun p => (u i p.1 * u i p.2) * (u j p.1 * u j p.2)
      have hsym_g : ∀ a b : Fin r, g (a, b) = g (b, a) := fun a b => by dsimp [g]; ring
      have hfull : (∑ a : Fin r, ∑ b : Fin r, (u i a * u j a) * (u i b * u j b)) =
          ∑ p : Fin r × Fin r, g p := by
        rw [Fintype.sum_prod_type]
        apply sum_congr rfl; intro a _; apply sum_congr rfl; intro b _; dsimp [g]; ring
      rw [hfull]
      have hQsum : ∑ q : Q, Φ i (Sum.inr q) * Ψ j (Sum.inr q) =
          ∑ p ∈ univ.filter (fun p : Fin r × Fin r => p.1 ≤ p.2),
            if p.1 = p.2 then g p else 2 * g p := by
        refine Finset.sum_bij (fun q _ => q.1) ?_ ?_ ?_ ?_
        · intro q _; exact mem_filter.mpr ⟨mem_univ _, q.2⟩
        · intro q1 _ q2 _ h; exact Subtype.ext h
        · intro p hp; exact ⟨⟨p, (mem_filter.mp hp).2⟩, mem_univ _, rfl⟩
        · intro ⟨⟨a, b⟩, _⟩ _
          by_cases e : a = b
          · simp [Φ, Ψ, g, e]
          · simp [Φ, Ψ, g, e]; ring
      rw [hQsum]
      -- Partition Fin r × Fin r into {p.1 = p.2}, {p.1 < p.2}, and {p.2 < p.1}.
      let EqS := univ.filter fun p : Fin r × Fin r => p.1 = p.2
      let LtS := univ.filter fun p : Fin r × Fin r => p.1 < p.2
      let GtS := univ.filter fun p : Fin r × Fin r => p.2 < p.1
      have hLe : univ.filter (fun p : Fin r × Fin r => p.1 ≤ p.2) = EqS ∪ LtS := by
        ext ⟨a, b⟩; simp [EqS, LtS, le_iff_eq_or_lt]
      have hdisj1 : Disjoint EqS LtS := by
        rw [Finset.disjoint_left]; intro ⟨a, b⟩ h1 h2
        simp [EqS, LtS] at h1 h2; omega
      have hAll : (univ : Finset (Fin r × Fin r)) = (EqS ∪ LtS) ∪ GtS := by
        ext ⟨a, b⟩; simp only [mem_univ, mem_union, EqS, LtS, GtS, mem_filter, true_and, true_iff]
        rcases lt_trichotomy a b with h | h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
      have hdisj2 : Disjoint (EqS ∪ LtS) GtS := by
        rw [Finset.disjoint_left]; intro ⟨a, b⟩ h1 h2
        simp [EqS, LtS, GtS] at h1 h2; omega
      have hGt_eq_Lt : ∑ p ∈ GtS, g p = ∑ p ∈ LtS, g p := by
        refine Finset.sum_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_ ?_
        · intro ⟨a, b⟩ hp; simp [GtS, LtS] at hp ⊢; exact hp
        · intro ⟨a1, b1⟩ _ ⟨a2, b2⟩ _ h; simp at h; exact Prod.ext h.2 h.1
        · intro ⟨a, b⟩ hp; refine ⟨(b, a), ?_, rfl⟩; simp [GtS, LtS] at hp ⊢; exact hp
        · intro ⟨a, b⟩ _; exact hsym_g a b
      rw [hLe, sum_union hdisj1, hAll, sum_union hdisj2, sum_union hdisj1, hGt_eq_Lt]
      have hEq_simp : ∑ p ∈ EqS, (if p.1 = p.2 then g p else 2 * g p) = ∑ p ∈ EqS, g p :=
        sum_congr rfl fun p hp => by simp [(mem_filter.mp hp).2]
      have hLt_simp : ∑ p ∈ LtS, (if p.1 = p.2 then g p else 2 * g p) = 2 * ∑ p ∈ LtS, g p := by
        rw [mul_sum]
        exact sum_congr rfl fun p hp => by
          have hlt : p.1 < p.2 := (mem_filter.mp hp).2
          simp [ne_of_lt hlt]
      rw [hEq_simp, hLt_simp]; ring
    rw [hlin, hquad]; ring
  -- Linear independence of Φ : Fin n → ((Fin r ⊕ Q) → ℝ).
  have hli : LinearIndependent ℝ Φ := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have heval : ∑ k : Fin r ⊕ Q, (∑ i : Fin n, c i • Φ i) k * Ψ j k = 0 := by
      rw [hc]; simp
    have hswap : ∑ k : Fin r ⊕ Q, (∑ i : Fin n, c i • Φ i) k * Ψ j k =
        ∑ i : Fin n, c i * ∑ k : Fin r ⊕ Q, Φ i k * Ψ j k := by
      simp_rw [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply sum_congr rfl; intro i _; apply sum_congr rfl; intro k _; ring
    rw [hswap] at heval
    have hterm : ∀ i : Fin n, c i * ∑ k : Fin r ⊕ Q, Φ i k * Ψ j k =
        if i = j then 2 * c j else 0 := by
      intro i
      rw [hpair i j]
      by_cases e : i = j
      · subst e; rw [hdiag i]; simp; ring
      · rcases hoff i j e with h0 | h1
        · rw [h0]; simp [e]
        · rw [h1]; simp [e]
    simp_rw [hterm] at heval
    simp at heval
    exact heval
  have hcard_le : n ≤ Fintype.card (Fin r ⊕ Q) := by
    have h := hli.fintype_card_le_finrank
    simpa [Module.finrank_pi] using h
  -- Compute 2 * card Q = r * (r + 1).
  have hQ_card : 2 * Fintype.card Q = r * (r + 1) := by
    have hQeq : Fintype.card Q = (univ.filter fun p : Fin r × Fin r => p.1 ≤ p.2).card := by
      rw [Fintype.card_subtype]
    let EqS := univ.filter fun p : Fin r × Fin r => p.1 = p.2
    let LtS := univ.filter fun p : Fin r × Fin r => p.1 < p.2
    let GtS := univ.filter fun p : Fin r × Fin r => p.2 < p.1
    have hLe : univ.filter (fun p : Fin r × Fin r => p.1 ≤ p.2) = EqS ∪ LtS := by
      ext ⟨a, b⟩; simp [EqS, LtS, le_iff_eq_or_lt]
    have hdisj1 : Disjoint EqS LtS := by
      rw [Finset.disjoint_left]; intro ⟨a, b⟩ h1 h2; simp [EqS, LtS] at h1 h2; omega
    have hAll : (univ : Finset (Fin r × Fin r)) = (EqS ∪ LtS) ∪ GtS := by
      ext ⟨a, b⟩; simp only [mem_univ, mem_union, EqS, LtS, GtS, mem_filter, true_and, true_iff]
      rcases lt_trichotomy a b with h | h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
    have hdisj2 : Disjoint (EqS ∪ LtS) GtS := by
      rw [Finset.disjoint_left]; intro ⟨a, b⟩ h1 h2; simp [EqS, LtS, GtS] at h1 h2; omega
    have hEq_card : EqS.card = r := by
      have : EqS = univ.image (fun a : Fin r => (a, a)) := by
        ext ⟨a, b⟩; simp [EqS, eq_comm]
      rw [this, card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).1), card_univ, Fintype.card_fin]
    have hGt_card : GtS.card = LtS.card := by
      refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
      · intro ⟨a, b⟩ hp; simp [GtS, LtS] at hp ⊢; exact hp
      · intro ⟨a1, b1⟩ _ ⟨a2, b2⟩ _ h; simp at h; exact Prod.ext h.2 h.1
      · intro ⟨a, b⟩ hp; refine ⟨(b, a), ?_, rfl⟩; simp [GtS, LtS] at hp ⊢; exact hp
    have hprod : r * r = EqS.card + LtS.card + GtS.card := by
      have hc : (univ : Finset (Fin r × Fin r)).card = r * r := by simp
      rw [← hc, hAll, card_union_of_disjoint hdisj2, card_union_of_disjoint hdisj1]
    rw [hQeq, hLe, card_union_of_disjoint hdisj1]
    have hrr : r * (r + 1) = r * r + r := by ring
    omega
  rw [Fintype.card_sum, Fintype.card_fin] at hcard_le
  nlinarith

/-- `K₉,₉` high-point matrix classification (`order12_deficit18.txt`, lines 153–159):
any rank-one additive `9 × 9` `{0, 1}` matrix `M i j = r i + c j` with sum `27`
is constant along rows (marking 3 complete columns) or constant along columns
(marking 3 complete rows). -/
theorem k99_matrix_three_rows_or_cols
    (r c : Fin 9 → ℝ)
    (h01 : ∀ i j, r i + c j = 0 ∨ r i + c j = 1)
    (hsum : ∑ i : Fin 9, ∑ j : Fin 9, (r i + c j) = 27) :
    (∃ R : Finset (Fin 9), R.card = 3 ∧ ∀ i j, r i + c j = if i ∈ R then 1 else 0) ∨
    (∃ C : Finset (Fin 9), C.card = 3 ∧ ∀ i j, r i + c j = if j ∈ C then 1 else 0) := by
  by_cases hrow_const : ∀ i : Fin 9, r i = r 0
  · right
    let C := univ.filter fun j : Fin 9 => r 0 + c j = 1
    have hval : ∀ i j, r i + c j = if j ∈ C then 1 else 0 := by
      intro i j
      rw [hrow_const i]
      rcases h01 0 j with h0 | h1
      · simp [C, h0]
      · simp [C, h1]
    have hcard : C.card = 3 := by
      have hs : ∑ i : Fin 9, ∑ j : Fin 9, (r i + c j) = 9 * (C.card : ℝ) := by
        simp_rw [hval, Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter,
          Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        norm_num
      rw [hs] at hsum
      have : (C.card : ℝ) = 3 := by linarith
      exact_mod_cast this
    exact ⟨C, hcard, hval⟩
  · left
    push Not at hrow_const
    obtain ⟨i1, hi1⟩ := hrow_const
    have hcol_const : ∀ j : Fin 9, c j = c 0 := by
      intro j
      rcases lt_or_gt_of_ne hi1 with hlt | hgt <;>
        rcases h01 0 j with h0j | h0j <;> rcases h01 i1 j with h1j | h1j <;>
        rcases h01 0 0 with h00 | h00 <;> rcases h01 i1 0 with h10 | h10 <;>
        linarith
    let R := univ.filter fun i : Fin 9 => r i + c 0 = 1
    have hval : ∀ i j, r i + c j = if i ∈ R then 1 else 0 := by
      intro i j
      rw [hcol_const j]
      rcases h01 i 0 with h0 | h1
      · simp [R, h0]
      · simp [R, h1]
    have hcard : R.card = 3 := by
      have hs : ∑ i : Fin 9, ∑ j : Fin 9, (r i + c j) = 9 * (R.card : ℝ) := by
        simp_rw [hval, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [← Finset.mul_sum, Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter]
        norm_num
      rw [hs] at hsum
      have : (R.card : ℝ) = 3 := by linarith
      exact_mod_cast this
    exact ⟨R, hcard, hval⟩

end Order12.Deficit18

/-!
# Euclidean frame identities for 139 blocks of size 13 on 157 points

Formalizes the frame construction of `order12_deficit18.txt` (lines 27–44) using
explicit linear operators on `P → ℝ` (no spectral theorem or matrix square root needed,
since `12 + 157 = 169 = 13^2`):

- `T x p = √12 * x p + ((13 - √12) / 157) * ∑ q, x q` satisfies `T^2 = 12 I + J = C`.
- `Tinv x p = (1 / √12) * x p + ((1 / 13 - 1 / √12) / 157) * ∑ q, x q` satisfies `T ∘ Tinv = id`.
- The 139 columns `f l = Tinv (ind (B l))` are orthonormal in `P → ℝ`.
- `proj x = x - ∑ l, dot x (f l) • f l` projects onto an 18-dimensional subspace `imProj`.
- `u p = proj (T (e p))` and `V = proj 1` satisfy:
  * `dot (u p) (u p) = 13 - deg B p`
  * `dot (u p) (u q) = 1` if `p, q` are distinct and share no block, `0` if they share a block
  * `dot V V = 18`, `dot (u p) V = 13 - deg B p`, `∑ p ∈ B l, u p = V`
  * `∑ p, dot (u p) x ^ 2 = 12 * dot x x + dot V x ^ 2` for all `x ∈ imProj`.
- Also proves the general Gram-matrix isometric transfer lemma between two finite families
  with identical Gram matrices.
-/

namespace Order12.Deficit18Frame

open Finset

section Dot

variable {α : Type*} [Fintype α]

/-- Standard Euclidean dot product on `α → ℝ`. -/
def dot (x y : α → ℝ) : ℝ := ∑ a : α, x a * y a

lemma dot_comm (x y : α → ℝ) : dot x y = dot y x := by
  simp only [dot, mul_comm]

lemma dot_add_left (x y z : α → ℝ) : dot (x + y) z = dot x z + dot y z := by
  simp only [dot, Pi.add_apply, add_mul, sum_add_distrib]

lemma dot_add_right (x y z : α → ℝ) : dot x (y + z) = dot x y + dot x z := by
  simp only [dot, Pi.add_apply, mul_add, sum_add_distrib]

lemma dot_sub_left (x y z : α → ℝ) : dot (x - y) z = dot x z - dot y z := by
  simp only [dot, Pi.sub_apply, sub_mul, sum_sub_distrib]

lemma dot_sub_right (x y z : α → ℝ) : dot x (y - z) = dot x y - dot x z := by
  simp only [dot, Pi.sub_apply, mul_sub, sum_sub_distrib]

lemma dot_smul_left (c : ℝ) (x y : α → ℝ) : dot (c • x) y = c * dot x y := by
  simp only [dot, Pi.smul_apply, smul_eq_mul, mul_assoc, mul_sum]

lemma dot_smul_right (c : ℝ) (x y : α → ℝ) : dot x (c • y) = c * dot x y := by
  rw [dot_comm, dot_smul_left, dot_comm]

lemma dot_zero_left (y : α → ℝ) : dot 0 y = 0 := by simp [dot]
lemma dot_zero_right (x : α → ℝ) : dot x 0 = 0 := by simp [dot]

lemma dot_sum_left {ι : Type*} (s : Finset ι) (g : ι → α → ℝ) (y : α → ℝ) :
    dot (∑ i ∈ s, g i) y = ∑ i ∈ s, dot (g i) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [dot_zero_left]
  | insert a s ha ih => rw [sum_insert ha, dot_add_left, ih, sum_insert ha]

lemma dot_sum_right {ι : Type*} (s : Finset ι) (x : α → ℝ) (g : ι → α → ℝ) :
    dot x (∑ i ∈ s, g i) = ∑ i ∈ s, dot x (g i) := by
  rw [dot_comm, dot_sum_left]; apply sum_congr rfl; intro i _; rw [dot_comm]

lemma dot_self_nonneg (x : α → ℝ) : 0 ≤ dot x x :=
  sum_nonneg fun a _ => mul_self_nonneg (x a)

lemma dot_self_eq_zero {x : α → ℝ} : dot x x = 0 ↔ x = 0 := by
  constructor
  · intro h
    ext a
    have hge : ∀ b ∈ (univ : Finset α), 0 ≤ x b * x b := fun b _ => mul_self_nonneg (x b)
    have ha := (sum_eq_zero_iff_of_nonneg hge).mp h a (mem_univ a)
    exact mul_self_eq_zero.mp ha
  · rintro rfl; simp [dot]

lemma dot_basis_left [DecidableEq α] (a : α) (y : α → ℝ) :
    dot (fun b => if b = a then (1 : ℝ) else 0) y = y a := by
  simp [dot]

lemma dot_basis_right [DecidableEq α] (x : α → ℝ) (a : α) :
    dot x (fun b => if b = a then (1 : ℝ) else 0) = x a := by
  rw [dot_comm, dot_basis_left]

/-- Cauchy-Schwarz inequality for `dot`. -/
lemma dot_sq_le (x y : α → ℝ) : dot x y ^ 2 ≤ dot x x * dot y y := by
  by_cases hx : dot x x = 0
  · rw [dot_self_eq_zero.mp hx, dot_zero_left, dot_zero_left]; norm_num
  · have hpos : 0 < dot x x := lt_of_le_of_ne (dot_self_nonneg x) (Ne.symm hx)
    have hnn : 0 ≤ dot (dot x x • y - dot x y • x) (dot x x • y - dot x y • x) :=
      dot_self_nonneg _
    rw [dot_sub_left, dot_sub_right, dot_sub_right, dot_smul_left, dot_smul_right,
      dot_smul_left, dot_smul_right, dot_smul_left, dot_smul_right, dot_smul_left, dot_smul_right,
      dot_comm y x] at hnn
    have hfact : dot x x * (dot x x * dot y y - dot x y ^ 2) ≥ 0 := by linarith
    nlinarith

/-- Bessel's inequality for a finite orthonormal family `r : ι → (α → ℝ)`. -/
lemma bessel_ineq {ι : Type*} [DecidableEq ι] (s : Finset ι) (r : ι → α → ℝ)
    (horth : ∀ i ∈ s, ∀ j ∈ s, dot (r i) (r j) = if i = j then 1 else 0)
    (v : α → ℝ) :
    ∑ i ∈ s, dot v (r i) ^ 2 ≤ dot v v := by
  let w : α → ℝ := v - ∑ i ∈ s, dot v (r i) • r i
  have hnn : 0 ≤ dot w w := dot_self_nonneg w
  have hcross : dot v (∑ i ∈ s, dot v (r i) • r i) = ∑ i ∈ s, dot v (r i) ^ 2 := by
    rw [dot_sum_right]
    apply sum_congr rfl; intro i _
    rw [dot_smul_right]; ring
  have hsq : dot (∑ i ∈ s, dot v (r i) • r i) (∑ i ∈ s, dot v (r i) • r i) =
      ∑ i ∈ s, dot v (r i) ^ 2 := by
    rw [dot_sum_left]
    apply sum_congr rfl; intro i hi
    rw [dot_smul_left, dot_sum_right]
    have hinner : ∑ j ∈ s, dot (r i) (dot v (r j) • r j) = dot v (r i) := by
      have : ∀ j ∈ s, dot (r i) (dot v (r j) • r j) = if j = i then dot v (r i) else 0 := by
        intro j hj
        rw [dot_smul_right, horth i hi j hj]
        by_cases e : j = i
        · subst e; simp
        · have e' : i ≠ j := Ne.symm e
          simp [e, e']
      rw [sum_congr rfl this, sum_ite_eq' s i, if_pos hi]
    rw [hinner]; ring
  have hexp : dot w w = dot v v - ∑ i ∈ s, dot v (r i) ^ 2 := by
    dsimp [w]
    rw [dot_sub_left, dot_sub_right, dot_sub_right, dot_comm (∑ i ∈ s, dot v (r i) • r i) v,
      hcross, hsq]
    ring
  linarith

end Dot

/-! ## General Gram-matrix isometric transfer -/

section GramTransfer

variable {R P V : Type*} [Fintype R] [Fintype P] [Fintype V]

/-- If two finite families `u : R → (P → ℝ)` and `w : R → (V → ℝ)` have identical Gram matrices,
any linear combination vanishes for `u` iff it vanishes for `w`. -/
lemma sum_smul_eq_zero_iff_of_gram
    (u : R → P → ℝ) (w : R → V → ℝ)
    (hgram : ∀ p q, dot (u p) (u q) = dot (w p) (w q))
    (c : R → ℝ) :
    (∑ p, c p • u p = 0) ↔ (∑ p, c p • w p = 0) := by
  have hnorm : dot (∑ p, c p • u p) (∑ p, c p • u p) =
      dot (∑ p, c p • w p) (∑ p, c p • w p) := by
    simp_rw [dot_sum_left, dot_sum_right, dot_smul_left, dot_smul_right, hgram]
  rw [← dot_self_eq_zero, ← dot_self_eq_zero, hnorm]

/-- Isometric linear equivalence between `span (range w)` and `span (range u)` for two
families with the same Gram matrix. -/
noncomputable def gramEquiv
    (u : R → P → ℝ) (w : R → V → ℝ)
    (hgram : ∀ p q, dot (u p) (u q) = dot (w p) (w q)) :
    Submodule.span ℝ (Set.range w) ≃ₗ[ℝ] Submodule.span ℝ (Set.range u) := by
  classical
  have hmem_u : ∀ x : Submodule.span ℝ (Set.range w),
      ∃ c : R → ℝ, ∑ p, c p • w p = x.1 := fun x =>
    (Submodule.mem_span_range_iff_exists_fun ℝ).mp x.2
  have hmem_w : ∀ y : Submodule.span ℝ (Set.range u),
      ∃ c : R → ℝ, ∑ p, c p • u p = y.1 := fun y =>
    (Submodule.mem_span_range_iff_exists_fun ℝ).mp y.2
  let toF : Submodule.span ℝ (Set.range w) → Submodule.span ℝ (Set.range u) := fun x =>
    ⟨∑ p, (hmem_u x).choose p • u p,
      (Submodule.mem_span_range_iff_exists_fun ℝ).mpr ⟨_, rfl⟩⟩
  let invF : Submodule.span ℝ (Set.range u) → Submodule.span ℝ (Set.range w) := fun y =>
    ⟨∑ p, (hmem_w y).choose p • w p,
      (Submodule.mem_span_range_iff_exists_fun ℝ).mpr ⟨_, rfl⟩⟩
  have htoF_spec : ∀ (x : Submodule.span ℝ (Set.range w)) (c : R → ℝ),
      ∑ p, c p • w p = x.1 → (toF x).1 = ∑ p, c p • u p := by
    intro x c hc
    dsimp [toF]
    have hdiff : ∑ p, ((hmem_u x).choose p - c p) • w p = 0 := by
      simp_rw [sub_smul, sum_sub_distrib, (hmem_u x).choose_spec, hc, sub_self]
    have hdiff_u := (sum_smul_eq_zero_iff_of_gram u w hgram _).mpr hdiff
    simp_rw [sub_smul, sum_sub_distrib] at hdiff_u
    exact sub_eq_zero.mp hdiff_u
  have hinvF_spec : ∀ (y : Submodule.span ℝ (Set.range u)) (c : R → ℝ),
      ∑ p, c p • u p = y.1 → (invF y).1 = ∑ p, c p • w p := by
    intro y c hc
    dsimp [invF]
    have hdiff : ∑ p, ((hmem_w y).choose p - c p) • u p = 0 := by
      simp_rw [sub_smul, sum_sub_distrib, (hmem_w y).choose_spec, hc, sub_self]
    have hdiff_w := (sum_smul_eq_zero_iff_of_gram u w hgram _).mp hdiff
    simp_rw [sub_smul, sum_sub_distrib] at hdiff_w
    exact sub_eq_zero.mp hdiff_w
  refine
    { toFun := toF
      invFun := invF
      map_add' := fun x y => by
        apply Subtype.ext
        have hsum : ∑ p, ((hmem_u x).choose p + (hmem_u y).choose p) • w p = (x + y).1 := by
          simp_rw [add_smul, sum_add_distrib, (hmem_u x).choose_spec, (hmem_u y).choose_spec]
          rfl
        rw [htoF_spec (x + y) _ hsum]
        simp_rw [add_smul, sum_add_distrib]
        rfl
      map_smul' := fun a x => by
        apply Subtype.ext
        have hsmul : ∑ p, (a * (hmem_u x).choose p) • w p = (a • x).1 := by
          simp_rw [mul_smul, ← smul_sum, (hmem_u x).choose_spec]
          rfl
        rw [htoF_spec (a • x) _ hsmul]
        simp_rw [mul_smul, ← smul_sum]
        rfl
      left_inv := fun x => by
        apply Subtype.ext
        have h1 : (toF x).1 = ∑ p, (hmem_u x).choose p • u p := rfl
        rw [hinvF_spec (toF x) (hmem_u x).choose h1.symm, (hmem_u x).choose_spec]
      right_inv := fun y => by
        apply Subtype.ext
        have h1 : (invF y).1 = ∑ p, (hmem_w y).choose p • w p := rfl
        rw [htoF_spec (invF y) (hmem_w y).choose h1.symm, (hmem_w y).choose_spec] }

lemma gramEquiv_apply_of_eq
    (u : R → P → ℝ) (w : R → V → ℝ)
    (hgram : ∀ p q, dot (u p) (u q) = dot (w p) (w q))
    (x : Submodule.span ℝ (Set.range w)) (c : R → ℝ)
    (hc : ∑ p, c p • w p = x.1) :
    (gramEquiv u w hgram x).1 = ∑ p, c p • u p := by
  classical
  dsimp [gramEquiv]
  have hmem_u : ∃ c' : R → ℝ, ∑ p, c' p • w p = x.1 :=
    (Submodule.mem_span_range_iff_exists_fun ℝ).mp x.2
  have hdiff : ∑ p, (hmem_u.choose p - c p) • w p = 0 := by
    simp_rw [sub_smul, sum_sub_distrib, hmem_u.choose_spec, hc, sub_self]
  have hdiff_u := (sum_smul_eq_zero_iff_of_gram u w hgram _).mpr hdiff
  simp_rw [sub_smul, sum_sub_distrib] at hdiff_u
  exact sub_eq_zero.mp hdiff_u

lemma gramEquiv_apply_gen
    (u : R → P → ℝ) (w : R → V → ℝ)
    (hgram : ∀ p q, dot (u p) (u q) = dot (w p) (w q))
    (p : R) :
    (gramEquiv u w hgram ⟨w p, Submodule.subset_span ⟨p, rfl⟩⟩).1 = u p := by
  classical
  rw [gramEquiv_apply_of_eq u w hgram _ (fun q => if q = p then 1 else 0) (by simp)]
  simp

lemma gramEquiv_dot
    (u : R → P → ℝ) (w : R → V → ℝ)
    (hgram : ∀ p q, dot (u p) (u q) = dot (w p) (w q))
    (x y : Submodule.span ℝ (Set.range w)) :
    dot (gramEquiv u w hgram x).1 (gramEquiv u w hgram y).1 = dot x.1 y.1 := by
  obtain ⟨cx, hcx⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp x.2
  obtain ⟨cy, hcy⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp y.2
  rw [gramEquiv_apply_of_eq u w hgram x cx hcx, gramEquiv_apply_of_eq u w hgram y cy hcy,
    ← hcx, ← hcy]
  simp_rw [dot_sum_left, dot_sum_right, dot_smul_left, dot_smul_right, hgram]

end GramTransfer

/-! ## Explicit 139-block Euclidean frame -/

section Frame139

variable {P L : Type*} [Fintype P] [Fintype L] [DecidableEq P] [DecidableEq L]

/-- Explicit square root of `C = 12 I + J` on `P → ℝ` (for `|P| = 157`). -/
noncomputable def T (x : P → ℝ) (p : P) : ℝ :=
  Real.sqrt 12 * x p + ((13 - Real.sqrt 12) / 157) * ∑ q : P, x q

/-- Explicit inverse square root `C^(-1/2)` on `P → ℝ` (for `|P| = 157`). -/
noncomputable def Tinv (x : P → ℝ) (p : P) : ℝ :=
  (1 / Real.sqrt 12) * x p + ((1 / 13 - 1 / Real.sqrt 12) / 157) * ∑ q : P, x q

private lemma sq_sqrt12 : Real.sqrt 12 * Real.sqrt 12 = 12 :=
  Real.mul_self_sqrt (by norm_num)

private lemma sqrt12_ne_zero : Real.sqrt 12 ≠ 0 := by
  positivity

lemma T_symm (x y : P → ℝ) : dot (T x) y = dot x (T y) := by
  simp only [dot, T, add_mul, mul_add, sum_add_distrib, ← sum_mul, ← mul_sum]
  have h1 : ∑ a : P, Real.sqrt 12 * x a * y a = ∑ a : P, x a * (Real.sqrt 12 * y a) := by
    apply sum_congr rfl; intro a _; ring
  rw [h1]; ring

lemma Tinv_symm (x y : P → ℝ) : dot (Tinv x) y = dot x (Tinv y) := by
  simp only [dot, Tinv, add_mul, mul_add, sum_add_distrib, ← sum_mul, ← mul_sum]
  have h1 : ∑ a : P, 1 / Real.sqrt 12 * x a * y a = ∑ a : P, x a * (1 / Real.sqrt 12 * y a) := by
    apply sum_congr rfl; intro a _; ring
  rw [h1]; ring

lemma T_sum (hp : Fintype.card P = 157) (x : P → ℝ) :
    ∑ p : P, T x p = 13 * ∑ p : P, x p := by
  simp only [T, sum_add_distrib, ← mul_sum, sum_const, card_univ, hp, nsmul_eq_mul]
  ring

lemma Tinv_sum (hp : Fintype.card P = 157) (x : P → ℝ) :
    ∑ p : P, Tinv x p = (1 / 13) * ∑ p : P, x p := by
  simp only [Tinv, sum_add_distrib, ← mul_sum, sum_const, card_univ, hp, nsmul_eq_mul]
  ring

lemma T_Tinv (hp : Fintype.card P = 157) (x : P → ℝ) : T (Tinv x) = x := by
  ext p
  simp only [T, Tinv_sum hp]
  dsimp [Tinv]
  have hs := sqrt12_ne_zero
  field_simp [hs]
  have hsq : Real.sqrt 12 ^ 2 = 12 := Real.sq_sqrt (by norm_num)
  nlinarith

lemma Tinv_T (hp : Fintype.card P = 157) (x : P → ℝ) : Tinv (T x) = x := by
  ext p
  simp only [Tinv, T_sum hp]
  dsimp [T]
  have hs := sqrt12_ne_zero
  field_simp [hs]
  have hsq : Real.sqrt 12 ^ 2 = 12 := Real.sq_sqrt (by norm_num)
  nlinarith

lemma T_T (hp : Fintype.card P = 157) (x : P → ℝ) (p : P) :
    T (T x) p = 12 * x p + ∑ q : P, x q := by
  rw [T, T_sum hp]
  dsimp [T]
  have hsq : Real.sqrt 12 * Real.sqrt 12 = 12 := sq_sqrt12
  linear_combination (x p - (∑ q : P, x q) / 157) * hsq

lemma Tinv_Tinv (hp : Fintype.card P = 157) (x : P → ℝ) (p : P) :
    Tinv (Tinv x) p = (1 / 12) * x p - (1 / (12 * 169)) * ∑ q : P, x q := by
  rw [Tinv, Tinv_sum hp]
  dsimp [Tinv]
  have hs := sqrt12_ne_zero
  have hsq : Real.sqrt 12 ^ 2 = 12 := Real.sq_sqrt (by norm_num)
  field_simp [hs]
  ring_nf
  rw [hsq]
  ring

lemma T_ones (hp : Fintype.card P = 157) : T (fun _ : P => (1 : ℝ)) = fun _ => 13 := by
  ext p; simp [T, hp]

lemma Tinv_ones (hp : Fintype.card P = 157) : Tinv (fun _ : P => (1 : ℝ)) = fun _ => 1 / 13 := by
  ext p; simp [Tinv, hp]

lemma dot_T_T (hp : Fintype.card P = 157) (x y : P → ℝ) :
    dot (T x) (T y) = 12 * dot x y + (∑ p : P, x p) * (∑ q : P, y q) := by
  rw [T_symm]
  simp only [dot, T_T hp, mul_add, sum_add_distrib, ← mul_sum, ← sum_mul]
  have h1 : ∑ a : P, x a * (12 * y a) = 12 * ∑ a : P, x a * y a := by
    rw [mul_sum]; apply sum_congr rfl; intro a _; ring
  rw [h1]

lemma dot_Tinv_Tinv (hp : Fintype.card P = 157) (x y : P → ℝ) :
    dot (Tinv x) (Tinv y) =
      (1 / 12) * dot x y - (1 / (12 * 169)) * (∑ p : P, x p) * (∑ q : P, y q) := by
  rw [Tinv_symm]
  simp only [dot, Tinv_Tinv hp, mul_sub, sum_sub_distrib, ← mul_sum, ← sum_mul]
  have h1 : ∑ a : P, x a * (1 / 12 * y a) = 1 / 12 * ∑ a : P, x a * y a := by
    rw [mul_sum]; apply sum_congr rfl; intro a _; ring
  rw [h1]; ring

/-- Indicator of a finite point set over `ℝ`. -/
def indR (S : Finset P) (p : P) : ℝ := if p ∈ S then 1 else 0

/-- Standard basis vector `e_p` in `P → ℝ`. -/
def basisE (p : P) (q : P) : ℝ := if q = p then 1 else 0

/-- Orthonormal column vector `f l = C^(-1/2) 1_{B l}` for an old block `l`. -/
noncomputable def colF (B : L → Finset P) (l : L) : P → ℝ := Tinv (indR (B l))

/-- Orthogonal projection `P x = x - ∑ l, ⟨x, f l⟩ f l` off the 139 block columns. -/
noncomputable def proj (B : L → Finset P) (x : P → ℝ) : P → ℝ :=
  x - ∑ l : L, dot x (colF B l) • colF B l

/-- Linear map form of `proj B`. -/
noncomputable def projLin (B : L → Finset P) : (P → ℝ) →ₗ[ℝ] (P → ℝ) where
  toFun := proj B
  map_add' x y := by
    simp only [proj, dot_add_left, add_smul, sum_add_distrib]
    abel
  map_smul' c x := by
    simp only [proj, dot_smul_left, mul_smul, ← smul_sum, smul_sub, RingHom.id_apply]

/-- Projected point vector `u p = P (C^(1/2) e_p)`. -/
noncomputable def uVec (B : L → Finset P) (p : P) : P → ℝ := proj B (T (basisE p))

/-- Projected all-ones vector `V = P 1`. -/
noncomputable def vVec (B : L → Finset P) : P → ℝ := proj B (fun _ => 1)

lemma colF_orthonormal
    (B : L → Finset P) (hp : Fintype.card P = 157)
    (hsize : ∀ l, (B l).card = 13)
    (hmeet : ∀ l m, l ≠ m → (B l ∩ B m).card = 1)
    (l m : L) :
    dot (colF B l) (colF B m) = if l = m then 1 else 0 := by
  dsimp [colF]
  rw [dot_Tinv_Tinv hp]
  have hsum (k : L) : ∑ p : P, indR (B k) p = 13 := by
    simp [indR, sum_boole, filter_mem_eq_inter, hsize k]
  have hdot : dot (indR (B l)) (indR (B m)) = ((B l ∩ B m).card : ℝ) := by
    have : dot (indR (B l)) (indR (B m)) = ∑ p : P, if p ∈ B l ∩ B m then (1 : ℝ) else 0 := by
      dsimp [dot, indR]; apply sum_congr rfl; intro p _
      by_cases h1 : p ∈ B l <;> by_cases h2 : p ∈ B m <;> simp [h1, h2]
    rw [this, sum_boole, filter_mem_eq_inter, univ_inter]
  rw [hsum l, hsum m, hdot]
  by_cases e : l = m
  · subst e; simp [hsize l]; norm_num
  · simp [e, hmeet l m e]; norm_num

lemma proj_colF
    (B : L → Finset P) (hp : Fintype.card P = 157)
    (hsize : ∀ l, (B l).card = 13)
    (hmeet : ∀ l m, l ≠ m → (B l ∩ B m).card = 1) (m : L) :
    proj B (colF B m) = 0 := by
  dsimp [proj]
  have h : ∑ l : L, dot (colF B m) (colF B l) • colF B l = colF B m := by
    have heq : ∀ l : L, dot (colF B m) (colF B l) • colF B l = if l = m then colF B m else 0 := by
      intro l
      rw [colF_orthonormal B hp hsize hmeet m l]
      by_cases e : l = m
      · subst e; simp
      · have e' : m ≠ l := Ne.symm e
        simp [e, e']
    simp_rw [heq]; simp
  rw [h, sub_self]

lemma proj_symm (B : L → Finset P) (x y : P → ℝ) :
    dot (proj B x) y = dot x (proj B y) := by
  simp only [proj, dot_sub_left, dot_sub_right, dot_sum_left, dot_sum_right,
    dot_smul_left, dot_smul_right]
  congr 1; apply sum_congr rfl; intro l _
  rw [dot_comm (colF B l) y]; ring

lemma proj_idem
    (B : L → Finset P) (hp : Fintype.card P = 157)
    (hsize : ∀ l, (B l).card = 13)
    (hmeet : ∀ l m, l ≠ m → (B l ∩ B m).card = 1) (x : P → ℝ) :
    proj B (proj B x) = proj B x := by
  have hlin : proj B (proj B x) =
      proj B x - ∑ l : L, dot x (colF B l) • proj B (colF B l) := by
    change projLin B (x - ∑ l : L, dot x (colF B l) • colF B l) = _
    rw [map_sub, map_sum]
    congr 1; apply sum_congr rfl; intro l _; rw [map_smul]; rfl
  rw [hlin]
  simp [proj_colF B hp hsize hmeet]

lemma dot_proj_proj
    (B : L → Finset P) (hp : Fintype.card P = 157)
    (hsize : ∀ l, (B l).card = 13)
    (hmeet : ∀ l m, l ≠ m → (B l ∩ B m).card = 1) (x y : P → ℝ) :
    dot (proj B x) (proj B y) = dot x y - ∑ l : L, dot x (colF B l) * dot y (colF B l) := by
  rw [proj_symm, proj_idem B hp hsize hmeet]
  simp only [proj, dot_sub_right, dot_sum_right, dot_smul_right]
  congr 1; apply sum_congr rfl; intro l _
  ring

lemma dot_T_basisE_colF
    (B : L → Finset P) (hp : Fintype.card P = 157) (p : P) (l : L) :
    dot (T (basisE p)) (colF B l) = if p ∈ B l then 1 else 0 := by
  dsimp [colF]
  rw [T_symm, T_Tinv hp]
  unfold basisE indR
  rw [dot_basis_left]

lemma dot_ones_colF
    (B : L → Finset P) (hp : Fintype.card P = 157)
    (hsize : ∀ l, (B l).card = 13) (l : L) :
    dot (fun _ : P => (1 : ℝ)) (colF B l) = 1 := by
  dsimp [colF]
  rw [← Tinv_symm, Tinv_ones hp]
  have hsum : ∑ p : P, indR (B l) p = 13 := by
    simp [indR, hsize l]
  simp only [dot, one_div]
  rw [← mul_sum, hsum]
  norm_num

/-- Exact Gram inner product of `uVec B p` and `uVec B q`. -/
theorem dot_uVec
    (B : L → Finset P) (hp : Fintype.card P = 157)
    (hsize : ∀ l, (B l).card = 13)
    (hmeet : ∀ l m, l ≠ m → (B l ∩ B m).card = 1) (p q : P) :
    dot (uVec B p) (uVec B q) =
      (if p = q then 13 else 1) - ((univ.filter fun l => p ∈ B l ∧ q ∈ B l).card : ℝ) := by
  dsimp [uVec]
  rw [dot_proj_proj B hp hsize hmeet, dot_T_T hp]
  have hbe : dot (basisE p) (basisE q) = if p = q then 1 else 0 := by
    unfold basisE
    rw [dot_basis_left]
  have hs (r : P) : ∑ a : P, basisE r a = 1 := by simp [basisE]
  have hcol : ∑ l : L, dot (T (basisE p)) (colF B l) * dot (T (basisE q)) (colF B l) =
      ((univ.filter fun l => p ∈ B l ∧ q ∈ B l).card : ℝ) := by
    simp_rw [dot_T_basisE_colF B hp]
    have h1 : (∑ l : L, (if p ∈ B l then (1 : ℝ) else 0) * (if q ∈ B l then 1 else 0)) =
        ∑ l : L, if p ∈ B l ∧ q ∈ B l then (1 : ℝ) else 0 := by
      apply sum_congr rfl; intro l _
      by_cases h1 : p ∈ B l <;> by_cases h2 : q ∈ B l <;> simp [h1, h2]
    rw [h1, sum_boole]
  rw [hbe, hs p, hs q, hcol]
  by_cases e : p = q <;> simp [e] <;> ring

/-- Squared norm of `uVec B p` equals the deficiency `13 - deg B p`. -/
theorem dot_uVec_self
    (B : L → Finset P) (hp : Fintype.card P = 157)
    (hsize : ∀ l, (B l).card = 13)
    (hmeet : ∀ l m, l ≠ m → (B l ∩ B m).card = 1) (p : P) :
    dot (uVec B p) (uVec B p) = 13 - ((univ.filter fun l => p ∈ B l).card : ℝ) := by
  rw [dot_uVec B hp hsize hmeet p p]
  simp

/-- Distinct points on no common block have inner product 1; on a common block, 0. -/
theorem dot_uVec_ne
    (B : L → Finset P) (hp : Fintype.card P = 157)
    (hsize : ∀ l, (B l).card = 13)
    (hmeet : ∀ l m, l ≠ m → (B l ∩ B m).card = 1) {p q : P} (hne : p ≠ q) :
    dot (uVec B p) (uVec B q) = if (∃ l, p ∈ B l ∧ q ∈ B l) then 0 else 1 := by
  rw [dot_uVec B hp hsize hmeet p q, if_neg hne]
  by_cases h : ∃ l, p ∈ B l ∧ q ∈ B l
  · rw [if_pos h]
    obtain ⟨l0, hp0, hq0⟩ := h
    have hcard : (univ.filter fun l => p ∈ B l ∧ q ∈ B l).card = 1 := by
      refine card_eq_one.mpr ⟨l0, ?_⟩
      ext l; simp only [mem_filter, mem_univ, true_and, mem_singleton]
      constructor
      · rintro ⟨hpl, hql⟩
        by_contra hne_l
        have h1 := card_eq_one_iff_existsUnique.mp (hmeet l l0 hne_l)
        exact hne (h1.unique (mem_inter.mpr ⟨hpl, hp0⟩) (mem_inter.mpr ⟨hql, hq0⟩))
      · rintro rfl; exact ⟨hp0, hq0⟩
    rw [hcard]; norm_num
  · rw [if_neg h]
    have hcard : (univ.filter fun l => p ∈ B l ∧ q ∈ B l).card = 0 := by
      rw [card_eq_zero, filter_eq_empty_iff]
      intro l _; intro hc; exact h ⟨l, hc⟩
    rw [hcard]; norm_num

/-- `‖V‖² = 18` for 139 blocks on 157 points. -/
theorem dot_vVec_self
    (B : L → Finset P) (hp : Fintype.card P = 157) (hl : Fintype.card L = 139)
    (hsize : ∀ l, (B l).card = 13)
    (hmeet : ∀ l m, l ≠ m → (B l ∩ B m).card = 1) :
    dot (vVec B) (vVec B) = 18 := by
  dsimp [vVec]
  rw [dot_proj_proj B hp hsize hmeet]
  simp_rw [dot_ones_colF B hp hsize]
  simp [dot, hp, hl]
  norm_num

/-- `⟨u_p, V⟩ = 13 - deg B p`. -/
theorem dot_uVec_vVec
    (B : L → Finset P) (hp : Fintype.card P = 157)
    (hsize : ∀ l, (B l).card = 13)
    (hmeet : ∀ l m, l ≠ m → (B l ∩ B m).card = 1) (p : P) :
    dot (uVec B p) (vVec B) = 13 - ((univ.filter fun l => p ∈ B l).card : ℝ) := by
  dsimp [uVec, vVec]
  rw [dot_proj_proj B hp hsize hmeet]
  have h1 : dot (T (basisE p)) (fun _ => 1) = 13 := by
    rw [T_symm, T_ones hp]
    simp [dot, basisE]
  simp_rw [dot_T_basisE_colF B hp, dot_ones_colF B hp hsize, mul_one, sum_boole]
  rw [h1]

/-- On every old block `B l`, `∑ p ∈ B l, u_p = V`. -/
theorem sum_uVec_block
    (B : L → Finset P) (hp : Fintype.card P = 157)
    (hsize : ∀ l, (B l).card = 13)
    (hmeet : ∀ l m, l ≠ m → (B l ∩ B m).card = 1) (l : L) :
    ∑ p ∈ B l, uVec B p = vVec B := by
  have hsum_basis : ∑ p ∈ B l, basisE p = indR (B l) := by
    ext q
    simp only [Finset.sum_apply, basisE, indR]
    by_cases hq : q ∈ B l
    · rw [if_pos hq, sum_eq_single q]
      · simp
      · intro p _ hpq; simp [Ne.symm hpq]
      · intro h; exact absurd hq h
    · rw [if_neg hq]
      apply sum_eq_zero; intro p hpB
      have : q ≠ p := fun e => hq (e ▸ hpB)
      simp [this]
  have hT_lin : ∑ p ∈ B l, T (basisE p) = T (indR (B l)) := by
    rw [← hsum_basis]
    ext q
    simp only [Finset.sum_apply, T, sum_add_distrib, ← mul_sum]
    congr 1
    rw [Finset.sum_comm]
  have hT_ind : T (indR (B l)) = (12 : ℝ) • colF B l + fun _ => 1 := by
    have hC : T (T (indR (B l))) = (12 : ℝ) • indR (B l) + (13 : ℝ) • fun _ => 1 := by
      ext q
      rw [T_T hp]
      have hsum : ∑ p : P, indR (B l) p = 13 := by
        simp [indR, sum_boole, filter_mem_eq_inter, hsize l]
      simp [hsum]
    have hinv := congrArg Tinv hC
    rw [Tinv_T hp] at hinv
    rw [hinv]
    ext q
    dsimp [colF]
    have hlin : Tinv ((12 : ℝ) • indR (B l) + (13 : ℝ) • fun _ => 1) q =
        12 * Tinv (indR (B l)) q + 13 * Tinv (fun _ => 1) q := by
      simp only [Tinv, Pi.add_apply, Pi.smul_apply, smul_eq_mul, sum_add_distrib, ← mul_sum]
      ring
    rw [hlin, Tinv_ones hp]
    simp
  have hproj_sum : ∑ p ∈ B l, uVec B p = proj B (∑ p ∈ B l, T (basisE p)) := by
    change ∑ p ∈ B l, projLin B (T (basisE p)) = projLin B (∑ p ∈ B l, T (basisE p))
    rw [map_sum]
  rw [hproj_sum, hT_lin, hT_ind]
  change projLin B ((12 : ℝ) • colF B l + fun _ => 1) = vVec B
  rw [map_add, map_smul]
  change (12 : ℝ) • proj B (colF B l) + vVec B = vVec B
  rw [proj_colF B hp hsize hmeet l, smul_zero, zero_add]

/-- Frame identity: for any `x` with `proj B x = x`,
`∑ p, ⟨u_p, x⟩² = 12 * ‖x‖² + ⟨V, x⟩²`. -/
theorem frame_identity
    (B : L → Finset P) (hp : Fintype.card P = 157)
    (x : P → ℝ) (hx : proj B x = x) :
    ∑ p : P, dot (uVec B p) x ^ 2 = 12 * dot x x + dot (vVec B) x ^ 2 := by
  have h1 : ∀ p : P, dot (uVec B p) x = T x p := by
    intro p
    dsimp [uVec]
    rw [proj_symm, hx, T_symm]
    unfold basisE
    rw [dot_basis_left]
  simp_rw [h1]
  have hlhs : ∑ p : P, T x p ^ 2 = dot (T x) (T x) := by
    simp only [dot, sq]
  rw [hlhs, dot_T_T hp]
  have hV : dot (vVec B) x = ∑ p : P, x p := by
    dsimp [vVec]
    rw [proj_symm, hx]
    simp [dot]
  rw [hV, sq]

/-- The image of `projLin B` has dimension `18 = 157 - 139`. -/
theorem finrank_range_projLin
    (B : L → Finset P) (hp : Fintype.card P = 157) (hl : Fintype.card L = 139)
    (hsize : ∀ l, (B l).card = 13)
    (hmeet : ∀ l m, l ≠ m → (B l ∩ B m).card = 1) :
    Module.finrank ℝ (LinearMap.range (projLin B)) = 18 := by
  have hli : LinearIndependent ℝ (colF B) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc m
    have h0 : dot (∑ l : L, c l • colF B l) (colF B m) = 0 := by rw [hc, dot_zero_left]
    rw [dot_sum_left] at h0
    have hterm : ∀ l : L, dot (c l • colF B l) (colF B m) = if l = m then c m else 0 := by
      intro l
      rw [dot_smul_left, colF_orthonormal B hp hsize hmeet l m]
      by_cases e : l = m
      · subst e; simp
      · simp [e]
    simp_rw [hterm] at h0
    simpa using h0
  have hker : LinearMap.ker (projLin B) = Submodule.span ℝ (Set.range (colF B)) := by
    ext x
    rw [LinearMap.mem_ker, Submodule.mem_span_range_iff_exists_fun]
    constructor
    · intro hx
      refine ⟨fun l => dot x (colF B l), ?_⟩
      have h : x - ∑ l : L, dot x (colF B l) • colF B l = 0 := hx
      exact (sub_eq_zero.mp h).symm
    · rintro ⟨c, rfl⟩
      change projLin B (∑ l : L, c l • colF B l) = 0
      rw [map_sum]
      apply sum_eq_zero; intro l _
      rw [map_smul]
      change c l • proj B (colF B l) = 0
      rw [proj_colF B hp hsize hmeet l, smul_zero]
  have hrank := LinearMap.finrank_range_add_finrank_ker (projLin B)
  rw [Module.finrank_pi, hp, hker, finrank_span_eq_card hli, hl] at hrank
  omega

end Frame139

end Order12.Deficit18Frame

/-!
# Elementary line-graph edge representation for root graphs with `δ ≥ 16`

Self-contained, ADE-free proof that any connected finite graph `H` represented by norm-2
vectors `u : R → (E → ℝ)` with inner products in `{0, 1}` satisfying:
- minimum degree `≥ 16`,
- every adjacent pair has `≤ 12` common neighbors,
- every non-adjacent pair has `≤ 4` common neighbors,

is the line graph `L(G)` of a connected simple graph `G` with endpoint degree sum `≥ 18`
on every edge, giving an exact Gram-matrix match `dot (u p) (u q) = dot (e_{i_p} + e_{j_p}) (e_{i_q} + e_{j_q})`.
-/

namespace Order12.Deficit18LineGraph

open Finset

section DotLocal

variable {α : Type*} [Fintype α]

/-- Local Euclidean dot product on `α → ℝ`. -/
def dot (x y : α → ℝ) : ℝ := ∑ a : α, x a * y a

lemma dot_comm (x y : α → ℝ) : dot x y = dot y x := by
  simp only [dot, mul_comm]

lemma dot_add_left (x y z : α → ℝ) : dot (x + y) z = dot x z + dot y z := by
  simp only [dot, Pi.add_apply, add_mul, sum_add_distrib]

lemma dot_add_right (x y z : α → ℝ) : dot x (y + z) = dot x y + dot x z := by
  simp only [dot, Pi.add_apply, mul_add, sum_add_distrib]

lemma dot_sub_left (x y z : α → ℝ) : dot (x - y) z = dot x z - dot y z := by
  simp only [dot, Pi.sub_apply, sub_mul, sum_sub_distrib]

lemma dot_sub_right (x y z : α → ℝ) : dot x (y - z) = dot x y - dot x z := by
  simp only [dot, Pi.sub_apply, mul_sub, sum_sub_distrib]

lemma dot_smul_left (c : ℝ) (x y : α → ℝ) : dot (c • x) y = c * dot x y := by
  simp only [dot, Pi.smul_apply, smul_eq_mul, mul_assoc, mul_sum]

lemma dot_smul_right (c : ℝ) (x y : α → ℝ) : dot x (c • y) = c * dot x y := by
  rw [dot_comm, dot_smul_left, dot_comm]

lemma dot_neg_left (x y : α → ℝ) : dot (-x) y = -dot x y := by
  simp only [dot, Pi.neg_apply, neg_mul, sum_neg_distrib]

lemma dot_neg_right (x y : α → ℝ) : dot x (-y) = -dot x y := by
  rw [dot_comm, dot_neg_left, dot_comm]

lemma dot_zero_left (y : α → ℝ) : dot 0 y = 0 := by simp [dot]

lemma dot_sum_left {ι : Type*} (s : Finset ι) (g : ι → α → ℝ) (y : α → ℝ) :
    dot (∑ i ∈ s, g i) y = ∑ i ∈ s, dot (g i) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [dot_zero_left]
  | insert a s ha ih => rw [sum_insert ha, dot_add_left, ih, sum_insert ha]

lemma dot_sum_right {ι : Type*} (s : Finset ι) (x : α → ℝ) (g : ι → α → ℝ) :
    dot x (∑ i ∈ s, g i) = ∑ i ∈ s, dot x (g i) := by
  rw [dot_comm, dot_sum_left]; apply sum_congr rfl; intro i _; rw [dot_comm]

lemma dot_self_nonneg (x : α → ℝ) : 0 ≤ dot x x :=
  sum_nonneg fun a _ => mul_self_nonneg (x a)

lemma dot_self_eq_zero {x : α → ℝ} : dot x x = 0 ↔ x = 0 := by
  constructor
  · intro h
    ext a
    have ha := (sum_eq_zero_iff_of_nonneg (fun b _ => mul_self_nonneg (x b))).mp h a (mem_univ a)
    exact mul_self_eq_zero.mp ha
  · rintro rfl; simp [dot]

lemma dot_sq_le (x y : α → ℝ) : dot x y ^ 2 ≤ dot x x * dot y y := by
  by_cases hx : dot x x = 0
  · rw [dot_self_eq_zero.mp hx, dot_zero_left, dot_zero_left]; norm_num
  · have hpos : 0 < dot x x := lt_of_le_of_ne (dot_self_nonneg x) (Ne.symm hx)
    have hnn : 0 ≤ dot (dot x x • y - dot x y • x) (dot x x • y - dot x y • x) :=
      dot_self_nonneg _
    rw [dot_sub_left, dot_sub_right, dot_sub_right, dot_smul_left, dot_smul_right,
      dot_smul_left, dot_smul_right, dot_smul_left, dot_smul_right, dot_smul_left, dot_smul_right,
      dot_comm y x] at hnn
    nlinarith

lemma bessel_ineq {ι : Type*} [DecidableEq ι] (s : Finset ι) (r : ι → α → ℝ)
    (horth : ∀ i ∈ s, ∀ j ∈ s, dot (r i) (r j) = if i = j then 1 else 0)
    (v : α → ℝ) :
    ∑ i ∈ s, dot v (r i) ^ 2 ≤ dot v v := by
  let w : α → ℝ := v - ∑ i ∈ s, dot v (r i) • r i
  have hnn : 0 ≤ dot w w := dot_self_nonneg w
  have hcross : dot v (∑ i ∈ s, dot v (r i) • r i) = ∑ i ∈ s, dot v (r i) ^ 2 := by
    rw [dot_sum_right]
    apply sum_congr rfl; intro i _; rw [dot_smul_right]; ring
  have hsq : dot (∑ i ∈ s, dot v (r i) • r i) (∑ i ∈ s, dot v (r i) • r i) =
      ∑ i ∈ s, dot v (r i) ^ 2 := by
    rw [dot_sum_left]
    apply sum_congr rfl; intro i hi
    rw [dot_smul_left, dot_sum_right]
    have hinner : ∑ j ∈ s, dot (r i) (dot v (r j) • r j) = dot v (r i) := by
      have : ∀ j ∈ s, dot (r i) (dot v (r j) • r j) = if j = i then dot v (r i) else 0 := by
        intro j hj
        rw [dot_smul_right, horth i hi j hj]
        by_cases e : j = i
        · subst e; simp
        · have e' : i ≠ j := Ne.symm e; simp [e, e']
      rw [sum_congr rfl this, sum_ite_eq' s i, if_pos hi]
    rw [hinner]; ring
  have hexp : dot w w = dot v v - ∑ i ∈ s, dot v (r i) ^ 2 := by
    dsimp [w]
    rw [dot_sub_left, dot_sub_right, dot_sub_right, dot_comm (∑ i ∈ s, dot v (r i) • r i) v,
      hcross, hsq]
    ring
  linarith

end DotLocal

/-! ## Elementary bipartite characterization: no induced odd cycle implies 2-colorable -/

section OddCycleBipartite

/-- Cyclic adjacency on `Fin k`: consecutive indices modulo `k`. -/
def cyclicAdj (k : ℕ) (i j : Fin k) : Prop :=
  (i.val + 1) % k = j.val ∨ (j.val + 1) % k = i.val

/-- Walk of length `n` in relation `E` from `a` to `b`. -/
inductive Walk {α : Type*} (E : α → α → Prop) : ℕ → α → α → Prop
  | nil (a : α) : Walk E 0 a a
  | cons {n : ℕ} {a b c : α} (hab : E a b) (w : Walk E n b c) : Walk E (n + 1) a c

lemma Walk.append {α : Type*} {E : α → α → Prop} {m n : ℕ} {a b c : α}
    (w1 : Walk E m a b) (w2 : Walk E n b c) : Walk E (m + n) a c := by
  induction w1 with
  | nil _ => simpa using w2
  | cons hab _ ih =>
    have h := Walk.cons hab (ih w2)
    simpa [Nat.succ_add] using h

lemma Walk.reverse {α : Type*} {E : α → α → Prop} (hsym : Symmetric E)
    {n : ℕ} {a b : α} (w : Walk E n a b) : Walk E n b a := by
  induction w with
  | nil _ => exact Walk.nil _
  | cons hab _ ih =>
    have h := ih.append (Walk.cons (hsym hab) (Walk.nil _))
    simpa using h

/-- Extract vertex `i` (`0 ≤ i ≤ n`) along a walk of length `n`. -/
lemma Walk.toFun {α : Type*} {E : α → α → Prop} {n : ℕ} {a b : α} (w : Walk E n a b) :
    ∃ f : Fin (n + 1) → α, f ⟨0, by omega⟩ = a ∧ f ⟨n, by omega⟩ = b ∧
      ∀ i : Fin n, E (f ⟨i.val, by omega⟩) (f ⟨i.val + 1, by omega⟩) := by
  induction w with
  | nil x =>
    refine ⟨fun _ => x, rfl, rfl, fun i => Fin.elim0 i⟩
  | @cons m x y z hxy w' ih =>
    obtain ⟨g, hg0, hgm, hge⟩ := ih
    let f : Fin (m + 2) → α := fun i =>
      if h : i.val = 0 then x else g ⟨i.val - 1, by omega⟩
    refine ⟨f, by simp [f], ?_, ?_⟩
    · simp [f, hgm]
    · intro i
      by_cases hi : i.val = 0
      · have h1 : f ⟨i.val, by omega⟩ = x := by simp [f, hi]
        have h2 : f ⟨i.val + 1, by omega⟩ = y := by
          simp only [f, hi, Nat.zero_add, Nat.add_eq_zero_iff, one_ne_zero, and_false,
            ↓reduceDIte, Nat.sub_self, hg0]
        rw [h1, h2]; exact hxy
      · have h1 : f ⟨i.val, by omega⟩ = g ⟨i.val - 1, by omega⟩ := by simp [f, hi]
        have h2 : f ⟨i.val + 1, by omega⟩ = g ⟨i.val, by omega⟩ := by simp [f]
        rw [h1, h2]
        have := hge ⟨i.val - 1, by omega⟩
        have heq : (i.val - 1) + 1 = i.val := by omega
        simpa [heq] using this

/-- Build a walk from a function `f` on `Fin (n + 1)` with consecutive edges. -/
lemma Walk.ofFun {α : Type*} {E : α → α → Prop} {n : ℕ} (f : Fin (n + 1) → α)
    (he : ∀ i : Fin n, E (f ⟨i.val, by omega⟩) (f ⟨i.val + 1, by omega⟩)) :
    Walk E n (f ⟨0, by omega⟩) (f ⟨n, by omega⟩) := by
  induction n with
  | zero => exact Walk.nil _
  | succ m ih =>
    let g : Fin (m + 1) → α := fun i => f ⟨i.val + 1, by omega⟩
    have hge : ∀ i : Fin m, E (g ⟨i.val, by omega⟩) (g ⟨i.val + 1, by omega⟩) := fun i =>
      he ⟨i.val + 1, by omega⟩
    exact Walk.cons (he ⟨0, by omega⟩) (ih g hge)

/-- A closed walk of length `k` represented on `Fin k`. -/
def ClosedWalk {α : Type*} (E : α → α → Prop) (k : ℕ) (f : Fin k → α) : Prop :=
  ∀ i : Fin k, E (f i) (f ⟨(i.val + 1) % k, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩)

lemma exists_closedWalk_of_walk {α : Type*} {E : α → α → Prop} {k : ℕ} (hk : 1 ≤ k)
    {a : α} (w : Walk E k a a) :
    ∃ f : Fin k → α, ClosedWalk E k f := by
  obtain ⟨g, hg0, hgk, hge⟩ := w.toFun
  refine ⟨fun i => g ⟨i.val, by omega⟩, fun i => ?_⟩
  by_cases hlast : i.val + 1 = k
  · have hmod : (i.val + 1) % k = 0 := by rw [hlast, Nat.mod_self]
    have he := hge i
    have h1 : g ⟨i.val + 1, by omega⟩ = g ⟨0, by omega⟩ := by
      have : (⟨i.val + 1, by omega⟩ : Fin (k + 1)) = ⟨k, by omega⟩ := Fin.ext hlast
      rw [this, hgk, hg0]
    simpa [hmod, h1] using he
  · have hlt : i.val + 1 < k := by omega
    have hmod : (i.val + 1) % k = i.val + 1 := Nat.mod_eq_of_lt hlt
    simpa [hmod] using hge i

/-- An odd closed walk of minimum length in a symmetric irreflexive graph is an induced odd cycle. -/
lemma exists_induced_odd_cycle_of_odd_walk
    {α : Type*} {E : α → α → Prop} (hsym : Symmetric E) (hirr : Irreflexive E)
    {n : ℕ} (hodd : n % 2 = 1) {a : α} (w : Walk E n a a) :
    ∃ k : ℕ, k % 2 = 1 ∧ 3 ≤ k ∧ ∃ f : Fin k → α,
      Function.Injective f ∧ ∀ i j : Fin k, i ≠ j → (E (f i) (f j) ↔ cyclicAdj k i j) := by
  classical
  have hex : ∃ m : ℕ, m % 2 = 1 ∧ ∃ x : α, Walk E m x x := ⟨n, hodd, a, w⟩
  let k := Nat.find hex
  have hk_spec : k % 2 = 1 ∧ ∃ x : α, Walk E k x x := Nat.find_spec hex
  have hk_min : ∀ m < k, m % 2 = 1 → ∀ x : α, ¬ Walk E m x x := fun m hm hmo x hx =>
    Nat.find_min hex hm ⟨hmo, x, hx⟩
  have hk_ge3 : 3 ≤ k := by
    rcases hk_spec with ⟨hko, x, wx⟩
    by_contra hlt
    have hk1 : k = 1 := by omega
    rw [hk1] at wx
    cases wx with
    | cons hxx w0 =>
      cases w0
      exact hirr x hxx
  obtain ⟨x0, wx0⟩ := hk_spec.2
  obtain ⟨f, hf⟩ := exists_closedWalk_of_walk (by omega : 1 ≤ k) wx0
  -- Helper: walk along f from index s of length d.
  have hwalk_seg : ∀ (s d : ℕ), Walk E d (f ⟨s % k, Nat.mod_lt _ (by omega)⟩)
      (f ⟨(s + d) % k, Nat.mod_lt _ (by omega)⟩) := by
    intro s d
    refine Walk.ofFun (fun t : Fin (d + 1) => f ⟨(s + t.val) % k, Nat.mod_lt _ (by omega)⟩) ?_
    intro t
    have hstep := hf ⟨(s + t.val) % k, Nat.mod_lt _ (by omega)⟩
    have hmod : ((s + t.val) % k + 1) % k = (s + (t.val + 1)) % k := by
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]; ring_nf
    simpa [hmod] using hstep
  have hwalk_idx : ∀ (i j : Fin k), Walk E ((j.val + k - i.val) % k) (f i) (f j) := by
    intro i j
    have hseg := hwalk_seg i.val ((j.val + k - i.val) % k)
    have h1 : i.val % k = i.val := Nat.mod_eq_of_lt i.isLt
    have h2 : (i.val + (j.val + k - i.val) % k) % k = j.val := by
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
      have : i.val + (j.val + k - i.val) = j.val + k := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt j.isLt]
    simpa [h1, h2] using hseg
  -- Step 1: f is injective.
  have hinj : Function.Injective f := by
    intro i j hij
    by_contra hne
    let d1 := (j.val + k - i.val) % k
    let d2 := (i.val + k - j.val) % k
    have hd1_pos : 0 < d1 := by
      dsimp [d1]
      have : i.val ≠ j.val := fun e => hne (Fin.ext e)
      by_cases hlt : i.val < j.val
      · have : (j.val + k - i.val) % k = j.val - i.val := by
          have : j.val + k - i.val = (j.val - i.val) + k := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        omega
      · have : (j.val + k - i.val) % k = j.val + k - i.val := Nat.mod_eq_of_lt (by omega)
        omega
    have hd2_pos : 0 < d2 := by
      dsimp [d2]
      have : j.val ≠ i.val := fun e => hne (Fin.ext e.symm)
      by_cases hlt : j.val < i.val
      · have : (i.val + k - j.val) % k = i.val - j.val := by
          have : i.val + k - j.val = (i.val - j.val) + k := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        omega
      · have : (i.val + k - j.val) % k = i.val + k - j.val := Nat.mod_eq_of_lt (by omega)
        omega
    have hdsum : d1 + d2 = k := by
      dsimp [d1, d2]
      have : i.val ≠ j.val := fun e => hne (Fin.ext e)
      by_cases hlt : i.val < j.val
      · have h1 : (j.val + k - i.val) % k = j.val - i.val := by
          have : j.val + k - i.val = (j.val - i.val) + k := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        have h2 : (i.val + k - j.val) % k = i.val + k - j.val := Nat.mod_eq_of_lt (by omega)
        omega
      · have h1 : (j.val + k - i.val) % k = j.val + k - i.val := Nat.mod_eq_of_lt (by omega)
        have h2 : (i.val + k - j.val) % k = i.val - j.val := by
          have : i.val + k - j.val = (i.val - j.val) + k := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        omega
    have w1 : Walk E d1 (f i) (f i) := by rw [hij]; exact (hij ▸ hwalk_idx i j)
    have w2 : Walk E d2 (f j) (f j) := by rw [← hij]; exact (hij.symm ▸ hwalk_idx j i)
    by_cases h1odd : d1 % 2 = 1
    · exact hk_min d1 (by omega) h1odd (f i) w1
    · exact hk_min d2 (by omega) (by omega) (f j) w2
  -- Step 2: no chords.
  refine ⟨k, hk_spec.1, hk_ge3, f, hinj, fun i j hne => ?_⟩
  constructor
  · intro he
    by_contra hnotcyc
    let d1 := (j.val + k - i.val) % k
    let d2 := (i.val + k - j.val) % k
    have hdsum : d1 + d2 = k := by
      dsimp [d1, d2]
      have : i.val ≠ j.val := fun e => hne (Fin.ext e)
      by_cases hlt : i.val < j.val
      · have h1 : (j.val + k - i.val) % k = j.val - i.val := by
          have : j.val + k - i.val = (j.val - i.val) + k := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        have h2 : (i.val + k - j.val) % k = i.val + k - j.val := Nat.mod_eq_of_lt (by omega)
        omega
      · have h1 : (j.val + k - i.val) % k = j.val + k - i.val := Nat.mod_eq_of_lt (by omega)
        have h2 : (i.val + k - j.val) % k = i.val - j.val := by
          have : i.val + k - j.val = (i.val - j.val) + k := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        omega
    have hd1_ne1 : d1 ≠ 1 := by
      intro h1; apply hnotcyc; left
      dsimp [d1] at h1
      have : (i.val + 1) % k = j.val := by
        rw [← h1, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
        have : i.val + (j.val + k - i.val) = j.val + k := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt j.isLt]
      exact this
    have hd2_ne1 : d2 ≠ 1 := by
      intro h2; apply hnotcyc; right
      dsimp [d2] at h2
      have : (j.val + 1) % k = i.val := by
        rw [← h2, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
        have : j.val + (i.val + k - j.val) = i.val + k := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]
      exact this
    have hd1_pos : 0 < d1 := by
      have : i.val ≠ j.val := fun e => hne (Fin.ext e)
      dsimp [d1]
      by_cases hlt : i.val < j.val
      · have : (j.val + k - i.val) % k = j.val - i.val := by
          have : j.val + k - i.val = (j.val - i.val) + k := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        omega
      · have : (j.val + k - i.val) % k = j.val + k - i.val := Nat.mod_eq_of_lt (by omega)
        omega
    have hd2_pos : 0 < d2 := by
      have : i.val ≠ j.val := fun e => hne (Fin.ext e)
      dsimp [d2]
      by_cases hlt : j.val < i.val
      · have : (i.val + k - j.val) % k = i.val - j.val := by
          have : i.val + k - j.val = (i.val - j.val) + k := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        omega
      · have : (i.val + k - j.val) % k = i.val + k - j.val := Nat.mod_eq_of_lt (by omega)
        omega
    have w1 : Walk E (d1 + 1) (f i) (f i) :=
      (hwalk_idx i j).append (Walk.cons (hsym he) (Walk.nil _))
    have w2 : Walk E (d2 + 1) (f j) (f j) :=
      (hwalk_idx j i).append (Walk.cons he (Walk.nil _))
    by_cases h1odd : (d1 + 1) % 2 = 1
    · exact hk_min (d1 + 1) (by omega) h1odd (f i) w1
    · exact hk_min (d2 + 1) (by omega) (by omega) (f j) w2
  · rintro (h1 | h2)
    · have := hf i
      have hfin : (⟨(i.val + 1) % k, Nat.mod_lt _ (by omega)⟩ : Fin k) = j := Fin.ext h1
      simpa [hfin] using this
    · have := hf j
      have hfin : (⟨(j.val + 1) % k, Nat.mod_lt _ (by omega)⟩ : Fin k) = i := Fin.ext h2
      exact hsym (by simpa [hfin] using this)

/-- A symmetric irreflexive graph with no induced odd cycle is 2-colorable (bipartite). -/
lemma bipartite_of_no_induced_odd_cycle
    {α : Type*} (E : α → α → Prop) (hsym : Symmetric E) (hirr : Irreflexive E)
    (hno : ∀ k : ℕ, k % 2 = 1 → 3 ≤ k → ∀ f : Fin k → α,
      Function.Injective f → (∀ i j : Fin k, i ≠ j → (E (f i) (f j) ↔ cyclicAdj k i j)) → False) :
    ∃ color : α → Bool, ∀ a b, E a b → color a ≠ color b := by
  classical
  have hno_odd : ∀ m : ℕ, m % 2 = 1 → ∀ a : α, ¬ Walk E m a a := by
    intro m hm a w
    obtain ⟨k, hko, hk3, f, hinj, hiff⟩ := exists_induced_odd_cycle_of_odd_walk hsym hirr hm w
    exact hno k hko hk3 f hinj hiff
  let Reach : α → α → Prop := fun a b => ∃ m, Walk E m a b
  have hReach_refl : ∀ a, Reach a a := fun a => ⟨0, Walk.nil a⟩
  have hReach_symm : ∀ {a b}, Reach a b → Reach b a := fun ⟨m, w⟩ => ⟨m, w.reverse hsym⟩
  have hReach_trans : ∀ {a b c}, Reach a b → Reach b c → Reach a c :=
    fun ⟨m, w1⟩ ⟨n, w2⟩ => ⟨m + n, w1.append w2⟩
  -- Canonical representative per connected component via Setoid.quotient.
  let setoid : Setoid α := ⟨Reach, ⟨hReach_refl, @hReach_symm, @hReach_trans⟩⟩
  let rep : α → α := fun a => (Quotient.exists_rep (Quotient.mk setoid a)).choose
  have hrep_eq : ∀ {a b}, Reach a b → rep a = rep b := by
    intro a b hab
    have hq : Quotient.mk setoid a = Quotient.mk setoid b := Quotient.sound hab
    dsimp [rep]; rw [hq]
  have hrep_reach : ∀ a, Reach (rep a) a := by
    intro a
    have hq : Quotient.mk setoid (rep a) = Quotient.mk setoid a :=
      (Quotient.exists_rep (Quotient.mk setoid a)).choose_spec
    exact Quotient.exact hq
  let color : α → Bool := fun a => decide (∃ m, m % 2 = 1 ∧ Walk E m (rep a) a)
  refine ⟨color, fun a b hab => ?_⟩
  have hrc : rep a = rep b := hrep_eq ⟨1, Walk.cons hab (Walk.nil b)⟩
  dsimp [color]
  rw [← hrc]
  intro heq
  have hiff : (∃ m, m % 2 = 1 ∧ Walk E m (rep a) a) ↔ (∃ m, m % 2 = 1 ∧ Walk E m (rep a) b) := by
    simpa using congrArg (· = true) heq
  obtain ⟨ma, wma⟩ := hrep_reach a
  by_cases hma : ma % 2 = 1
  · obtain ⟨mb, hmb, wmb⟩ := hiff.mp ⟨ma, hma, wma⟩
    have wloop : Walk E (ma + 1 + mb) (rep a) (rep a) :=
      (wma.append (Walk.cons hab (Walk.nil b))).append (wmb.reverse hsym)
    exact hno_odd (ma + 1 + mb) (by omega) (rep a) wloop
  · have hodd_b : ∃ m, m % 2 = 1 ∧ Walk E m (rep a) b :=
      ⟨ma + 1, by omega, wma.append (Walk.cons hab (Walk.nil b))⟩
    obtain ⟨ma', hma', wma'⟩ := hiff.mpr hodd_b
    have wloop : Walk E (ma + ma') (rep a) (rep a) := wma.append (wma'.reverse hsym)
    exact hno_odd (ma + ma') (by omega) (rep a) wloop

end OddCycleBipartite

/-! ## The 5-step elementary edge-representation proof -/

section MainProof

variable {R E : Type*} [Fintype R] [Fintype E] [DecidableEq R]

/-- Neighborhood of `p` in `adj`. -/
def nbrs (adj : R → R → Prop) [DecidableRel adj] (p : R) : Finset R :=
  univ.filter (adj p)

private lemma adj_symm_of_gram (u : R → E → ℝ) (adj : R → R → Prop)
    (hadj : ∀ p q, adj p q ↔ p ≠ q ∧ dot (u p) (u q) = 1) :
    Symmetric adj := by
  intro p q hpq
  have ⟨hne, hd⟩ := (hadj p q).mp hpq
  exact (hadj q p).mpr ⟨hne.symm, by rw [dot_comm]; exact hd⟩

private lemma adj_irrefl_of_gram (u : R → E → ℝ) (adj : R → R → Prop)
    (hadj : ∀ p q, adj p q ↔ p ≠ q ∧ dot (u p) (u q) = 1) :
    Irreflexive adj := by
  intro p hp
  exact ((hadj p p).mp hp).1 rfl

private lemma dot_zero_of_not_adj (u : R → E → ℝ) (adj : R → R → Prop)
    (hgram : ∀ p q, p ≠ q → dot (u p) (u q) = 0 ∨ dot (u p) (u q) = 1)
    (hadj : ∀ p q, adj p q ↔ p ≠ q ∧ dot (u p) (u q) = 1)
    {p q : R} (hne : p ≠ q) (hnot : ¬ adj p q) :
    dot (u p) (u q) = 0 := by
  rcases hgram p q hne with h0 | h1
  · exact h0
  · exact absurd ((hadj p q).mpr ⟨hne, h1⟩) hnot

/-- Step 1: Any vertex outside a clique `C` of size `≥ 9` (not adjacent to all of `C`)
has at most `2` neighbors in `C`. -/
theorem det_clique_outside
    (u : R → E → ℝ) (adj : R → R → Prop) [DecidableRel adj]
    (hnorm : ∀ p, dot (u p) (u p) = 2)
    (hgram : ∀ p q, p ≠ q → dot (u p) (u q) = 0 ∨ dot (u p) (u q) = 1)
    (hadj : ∀ p q, adj p q ↔ p ≠ q ∧ dot (u p) (u q) = 1)
    (hcomm_nonadj : ∀ p q, p ≠ q → ¬ adj p q → (nbrs adj p ∩ nbrs adj q).card ≤ 4)
    (C : Finset R) (hclique : ∀ a ∈ C, ∀ b ∈ C, a ≠ b → adj a b)
    (hCcard : 9 ≤ C.card)
    (x : R) (hxC : x ∉ C) (hnotall : ∃ z ∈ C, ¬ adj x z) :
    (nbrs adj x ∩ C).card ≤ 2 := by
  have hsym := adj_symm_of_gram u adj hadj
  let A := C.filter (adj x)
  let B := C.filter fun z => ¬ adj x z
  have hA_eq : A = nbrs adj x ∩ C := by
    ext y; simp [A, nbrs, and_comm]
  rw [← hA_eq]
  have hAB_card : A.card + B.card = C.card := card_filter_add_card_filter_not (adj x)
  obtain ⟨z0, hz0C, hz0n⟩ := hnotall
  have hB_pos : 1 ≤ B.card := card_pos.mpr ⟨z0, mem_filter.mpr ⟨hz0C, hz0n⟩⟩
  -- Bound A.card ≤ 4 via common neighbors of x and z0.
  have hA_le4 : A.card ≤ 4 := by
    have hxz0 : x ≠ z0 := fun e => hxC (e ▸ hz0C)
    have hsub : A ⊆ nbrs adj x ∩ nbrs adj z0 := by
      intro y hy
      have ⟨hyC, hxy⟩ := mem_filter.mp hy
      have hyz0 : y ≠ z0 := fun e => hz0n (e ▸ hxy)
      exact mem_inter.mpr ⟨mem_filter.mpr ⟨mem_univ _, hxy⟩,
        mem_filter.mpr ⟨mem_univ _, hsym (hclique y hyC z0 hz0C hyz0)⟩⟩
    exact (card_le_card hsub).trans (hcomm_nonadj x z0 hxz0 hz0n)
  -- Gram bound on sumA, sumB, u x.
  let sumA : E → ℝ := ∑ y ∈ A, u y
  let sumB : E → ℝ := ∑ z ∈ B, u z
  let a : ℝ := (A.card : ℝ)
  let b : ℝ := (B.card : ℝ)
  have hdot_clique : ∀ S : Finset R, S ⊆ C →
      dot (∑ y ∈ S, u y) (∑ y ∈ S, u y) = (S.card : ℝ) * ((S.card : ℝ) + 1) := by
    intro S hSC
    rw [dot_sum_left]
    have hinner : ∀ y ∈ S, dot (u y) (∑ y' ∈ S, u y') = (S.card : ℝ) + 1 := by
      intro y hy
      rw [dot_sum_right]
      have hterm : ∀ y' ∈ S, dot (u y) (u y') = (1 : ℝ) + if y' = y then 1 else 0 := by
        intro y' hy'
        by_cases e : y' = y
        · rw [e, hnorm y]; simp; norm_num
        · have h1 := ((hadj y y').mp (hclique y (hSC hy) y' (hSC hy') (Ne.symm e))).2
          simp [e, h1]
      rw [sum_congr rfl hterm, sum_add_distrib, sum_const, nsmul_eq_mul, mul_one,
        sum_ite_eq' S y, if_pos hy]
    rw [sum_congr rfl hinner, sum_const, nsmul_eq_mul]
  have hAA : dot sumA sumA = a * (a + 1) := hdot_clique A (filter_subset _ _)
  have hBB : dot sumB sumB = b * (b + 1) := hdot_clique B (filter_subset _ _)
  have hAB : dot sumA sumB = a * b := by
    dsimp [sumA, sumB]
    rw [dot_sum_left]
    have hinner : ∀ y ∈ A, dot (u y) (∑ z ∈ B, u z) = b := by
      intro y hy
      rw [dot_sum_right]
      have hterm : ∀ z ∈ B, dot (u y) (u z) = 1 := by
        intro z hz
        have ⟨hyC, hxy⟩ := mem_filter.mp hy
        have ⟨hzC, hxz⟩ := mem_filter.mp hz
        have hyz : y ≠ z := fun e => hxz (e ▸ hxy)
        exact ((hadj y z).mp (hclique y hyC z hzC hyz)).2
      rw [sum_congr rfl hterm, sum_const, nsmul_eq_mul, mul_one]
    rw [sum_congr rfl hinner, sum_const, nsmul_eq_mul]
  have hAx : dot sumA (u x) = a := by
    dsimp [sumA]; rw [dot_sum_left]
    have hterm : ∀ y ∈ A, dot (u y) (u x) = 1 := fun y hy =>
      ((hadj y x).mp (hsym (mem_filter.mp hy).2)).2
    rw [sum_congr rfl hterm, sum_const, nsmul_eq_mul, mul_one]
  have hBx : dot sumB (u x) = 0 := by
    dsimp [sumB]; rw [dot_sum_left]
    apply sum_eq_zero; intro z hz
    have ⟨hzC, hxz⟩ := mem_filter.mp hz
    have hzx : z ≠ x := fun e => hxC (e ▸ hzC)
    exact dot_zero_of_not_adj u adj hgram hadj hzx (fun h => hxz (hsym h))
  let w : E → ℝ := (2 * (b + 1)) • sumA - (2 * a) • sumB - (a * (b + 1)) • u x
  have hnn : 0 ≤ dot w w := dot_self_nonneg w
  have hexp : dot w w = 2 * a * (b + 1) * (4 - (a - 2) * (b - 1)) := by
    dsimp [w]
    simp only [dot_sub_left, dot_sub_right, dot_smul_left, dot_smul_right]
    rw [dot_comm sumB sumA, dot_comm (u x) sumA, dot_comm (u x) sumB,
      hAA, hBB, hAB, hAx, hBx, hnorm x]
    ring
  rw [hexp] at hnn
  by_contra hgt
  have h34 : A.card = 3 ∨ A.card = 4 := by omega
  rcases h34 with h3 | h4
  · have ha : a = 3 := by dsimp [a]; exact_mod_cast h3
    have hb : 6 ≤ b := by dsimp [b]; exact_mod_cast (show 6 ≤ B.card by omega)
    rw [ha] at hnn; nlinarith
  · have ha : a = 4 := by dsimp [a]; exact_mod_cast h4
    have hb : 5 ≤ b := by dsimp [b]; exact_mod_cast (show 5 ≤ B.card by omega)
    rw [ha] at hnn; nlinarith

/-- Step 2: The root graph `H` is claw-free (`K_{1,3}`-free). -/
theorem claw_free
    (u : R → E → ℝ) (adj : R → R → Prop) [DecidableRel adj]
    (hnorm : ∀ p, dot (u p) (u p) = 2)
    (hgram : ∀ p q, p ≠ q → dot (u p) (u q) = 0 ∨ dot (u p) (u q) = 1)
    (hadj : ∀ p q, adj p q ↔ p ≠ q ∧ dot (u p) (u q) = 1)
    (hdeg : ∀ p, 16 ≤ (nbrs adj p).card)
    (hcomm_adj : ∀ p q, adj p q → (nbrs adj p ∩ nbrs adj q).card ≤ 12)
    (hcomm_nonadj : ∀ p q, p ≠ q → ¬ adj p q → (nbrs adj p ∩ nbrs adj q).card ≤ 4)
    (p : R) (x : Fin 3 → R)
    (hx : ∀ i : Fin 3, adj p (x i))
    (hnon : ∀ i j : Fin 3, i ≠ j → x i ≠ x j ∧ ¬ adj (x i) (x j)) :
    False := by
  have hsym := adj_symm_of_gram u adj hadj
  have hirr := adj_irrefl_of_gram u adj hadj
  have hdot_px : ∀ i : Fin 3, dot (u p) (u (x i)) = 1 := fun i => ((hadj p (x i)).mp (hx i)).2
  have hdot_xx : ∀ i j : Fin 3, dot (u (x i)) (u (x j)) = if i = j then 2 else 0 := by
    intro i j
    by_cases e : i = j
    · subst e; simp [hnorm]
    · simp only [e, ↓reduceIte]
      have ⟨hne, hna⟩ := hnon i j e
      exact dot_zero_of_not_adj u adj hgram hadj hne hna
  let e0 : E → ℝ := u p - (1 / 2 : ℝ) • ∑ i : Fin 3, u (x i)
  have he0_x : ∀ i : Fin 3, dot e0 (u (x i)) = 0 := by
    intro i
    dsimp [e0]
    rw [dot_sub_left, dot_smul_left, dot_sum_left, hdot_px i]
    have hs : ∑ j : Fin 3, dot (u (x j)) (u (x i)) = 2 := by
      simp_rw [hdot_xx]; simp
    rw [hs]; ring
  have he0_norm : dot e0 e0 = 1 / 2 := by
    dsimp [e0]
    rw [dot_sub_right, dot_smul_right, dot_sum_right]
    have h0 : ∑ i : Fin 3, dot (u p - (1 / 2 : ℝ) • ∑ j : Fin 3, u (x j)) (u (x i)) = 0 :=
      sum_eq_zero fun i _ => he0_x i
    rw [h0, mul_zero, sub_zero, dot_sub_left, dot_smul_left, dot_sum_left, hnorm p]
    have hs : ∑ i : Fin 3, dot (u (x i)) (u p) = 3 := by
      have : ∀ i : Fin 3, dot (u (x i)) (u p) = 1 := fun i => by rw [dot_comm]; exact hdot_px i
      simp [this]
    rw [hs]; ring
  let W : Fin 3 → Finset R := fun i => (nbrs adj (x i)).filter fun v => v ≠ p ∧ ¬ adj p v
  let S : Fin 3 → Finset R := fun i =>
    (nbrs adj p).filter fun y => y ≠ x i ∧ adj (x i) y ∧ ∀ j : Fin 3, j ≠ i → ¬ adj (x j) y
  -- Lower bound |W i| ≥ 3.
  have hW_ge3 : ∀ i : Fin 3, 3 ≤ (W i).card := by
    intro i
    have hsub : nbrs adj (x i) ⊆ insert p (W i ∪ (nbrs adj p ∩ nbrs adj (x i))) := by
      intro v hv
      by_cases hvp : v = p
      · simp [hvp]
      · refine mem_insert_of_mem ?_
        by_cases hpv : adj p v
        · exact mem_union_right _ (mem_inter.mpr ⟨mem_filter.mpr ⟨mem_univ _, hpv⟩, hv⟩)
        · exact mem_union_left _ (mem_filter.mpr ⟨hv, hvp, hpv⟩)
    have hc1 := card_le_card hsub
    have hc2 := card_insert_le p (W i ∪ (nbrs adj p ∩ nbrs adj (x i)))
    have hc3 := card_union_le (W i) (nbrs adj p ∩ nbrs adj (x i))
    have hc4 := hcomm_adj p (x i) (hx i)
    have hd := hdeg (x i)
    omega
  -- Degree decomposition: 16 ≤ 7 + |W i| + |S i|.
  have hdeg_split : ∀ i : Fin 3, 16 ≤ 7 + (W i).card + (S i).card := by
    intro i
    -- Two other indices j1, j2 ≠ i.
    let others := (univ : Finset (Fin 3)).erase i
    have hsub : nbrs adj (x i) ⊆
        insert p (W i ∪ S i ∪ others.biUnion fun j => (nbrs adj (x i) ∩ nbrs adj (x j)).erase p) := by
      intro v hv
      by_cases hvp : v = p
      · simp [hvp]
      · refine mem_insert_of_mem ?_
        by_cases hpv : adj p v
        · by_cases hother : ∃ j : Fin 3, j ≠ i ∧ adj (x j) v
          · obtain ⟨j, hji, hjv⟩ := hother
            refine mem_union_right _ (mem_biUnion.mpr ⟨j, mem_erase.mpr ⟨hji, mem_univ _⟩, ?_⟩)
            exact mem_erase.mpr ⟨hvp, mem_inter.mpr ⟨hv, mem_filter.mpr ⟨mem_univ _, hjv⟩⟩⟩
          · push Not at hother
            refine mem_union_left _ (mem_union_right _ ?_)
            have hne_xi : v ≠ x i := fun e => hirr (x i) (e ▸ (mem_filter.mp hv).2)
            exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, hpv⟩, hne_xi, (mem_filter.mp hv).2, hother⟩
        · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hv, hvp, hpv⟩))
    have hbi_le : (others.biUnion fun j => (nbrs adj (x i) ∩ nbrs adj (x j)).erase p).card ≤ 6 := by
      calc
        _ ≤ ∑ j ∈ others, ((nbrs adj (x i) ∩ nbrs adj (x j)).erase p).card := card_biUnion_le
        _ ≤ ∑ _j ∈ others, 3 := by
          apply sum_le_sum; intro j hj
          have hji : j ≠ i := (mem_erase.mp hj).1
          have ⟨hne, hna⟩ := hnon i j (Ne.symm hji)
          have hp_in : p ∈ nbrs adj (x i) ∩ nbrs adj (x j) :=
            mem_inter.mpr ⟨mem_filter.mpr ⟨mem_univ _, hsym (hx i)⟩,
              mem_filter.mpr ⟨mem_univ _, hsym (hx j)⟩⟩
          rw [card_erase_of_mem hp_in]
          have := hcomm_nonadj (x i) (x j) hne hna
          omega
        _ = 6 := by
          rw [sum_const, card_erase_of_mem (mem_univ i), card_univ, Fintype.card_fin]
          norm_num
    have hc1 := card_le_card hsub
    have hc2 := card_insert_le p (W i ∪ S i ∪ others.biUnion fun j => (nbrs adj (x i) ∩ nbrs adj (x j)).erase p)
    have hc3 := card_union_le (W i ∪ S i) (others.biUnion fun j => (nbrs adj (x i) ∩ nbrs adj (x j)).erase p)
    have hc4 := card_union_le (W i) (S i)
    have hd := hdeg (x i)
    omega
  -- For every v ∈ W i and j ≠ i, ¬ adj (x j) v (and v ≠ x j).
  have hW_orth : ∀ (i : Fin 3), ∀ v ∈ W i, ∀ j : Fin 3, j ≠ i → v ≠ x j ∧ ¬ adj (x j) v := by
    intro i v hv j hji
    have ⟨hvxi, hvp, hnpv⟩ := mem_filter.mp hv
    have hv_xi_adj : adj (x i) v := (mem_filter.mp hvxi).2
    have hne_xj : v ≠ x j := fun e => hnpv (e ▸ hx j)
    refine ⟨hne_xj, fun hjv => ?_⟩
    -- Project u v onto span(e0, u(x 0), u(x 1), u(x 2)).
    let a : Fin 3 → ℝ := fun k => dot (u v) (u (x k))
    have ha_bin : ∀ k : Fin 3, a k = 0 ∨ a k = 1 := by
      intro k
      have hne_k : v ≠ x k := fun e => hnpv (e ▸ hx k)
      exact hgram v (x k) hne_k
    have hai : a i = 1 := ((hadj v (x i)).mp (hsym hv_xi_adj)).2
    have haj : a j = 1 := ((hadj v (x j)).mp (hsym hjv)).2
    have hv_p0 : dot (u v) (u p) = 0 :=
      dot_zero_of_not_adj u adj hgram hadj hvp (fun h => hnpv (hsym h))
    let s : ℝ := ∑ k : Fin 3, a k
    have hs_ge2 : 2 ≤ s := by
      have hnn : ∀ k : Fin 3, 0 ≤ a k := fun k => by rcases ha_bin k with h | h <;> linarith
      have hpair : a i + a j ≤ ∑ k : Fin 3, a k := by
        have hsub : ({i, j} : Finset (Fin 3)) ⊆ univ := subset_univ _
        have := sum_le_sum_of_subset_of_nonneg hsub fun k _ _ => hnn k
        rw [sum_pair (Ne.symm hji)] at this
        exact this
      dsimp [s]; linarith
    have hv_e0 : dot (u v) e0 = -(1 / 2 : ℝ) * s := by
      dsimp [e0, s, a]
      rw [dot_sub_right, dot_smul_right, dot_sum_right, hv_p0]; ring
    let projv : E → ℝ := (2 * dot (u v) e0) • e0 + (1 / 2 : ℝ) • ∑ k : Fin 3, a k • u (x k)
    have hnn : 0 ≤ dot (u v - projv) (u v - projv) := dot_self_nonneg _
    have hdot_up : dot (u v) projv = (1 / 2 : ℝ) * s ^ 2 + (1 / 2 : ℝ) * s := by
      dsimp [projv]
      rw [dot_add_right, dot_smul_right, dot_smul_right, dot_sum_right, hv_e0]
      have hsum_sq : ∑ k : Fin 3, dot (u v) (a k • u (x k)) = s := by
        have hterm : ∀ k : Fin 3, dot (u v) (a k • u (x k)) = a k := by
          intro k; rw [dot_smul_right]
          change a k * a k = a k
          rcases ha_bin k with h | h <;> rw [h] <;> ring
        simp_rw [hterm]; rfl
      rw [hsum_sq]; ring
    have hdot_pp : dot projv projv = (1 / 2 : ℝ) * s ^ 2 + (1 / 2 : ℝ) * s := by
      dsimp [projv]
      rw [dot_add_left, dot_add_right, dot_add_right, dot_smul_left, dot_smul_right,
        dot_smul_left, dot_smul_right, dot_smul_left, dot_smul_right, dot_smul_left, dot_smul_right]
      have hcross : dot e0 (∑ k : Fin 3, a k • u (x k)) = 0 := by
        rw [dot_sum_right]
        exact sum_eq_zero fun k _ => by rw [dot_smul_right, he0_x k, mul_zero]
      have hcross' : dot (∑ k : Fin 3, a k • u (x k)) e0 = 0 := by rw [dot_comm]; exact hcross
      have hsum_sq : dot (∑ k : Fin 3, a k • u (x k)) (∑ k : Fin 3, a k • u (x k)) = 2 * s := by
        rw [dot_sum_left]
        have h1 : ∀ k : Fin 3, dot (a k • u (x k)) (∑ m : Fin 3, a m • u (x m)) = 2 * a k := by
          intro k
          rw [dot_smul_left, dot_sum_right]
          have h2 : ∀ m : Fin 3, dot (u (x k)) (a m • u (x m)) = if m = k then 2 * a k else 0 := by
            intro m
            rw [dot_smul_right, hdot_xx k m]
            by_cases e : m = k
            · subst e; simp; ring
            · have e' : k ≠ m := Ne.symm e; simp [e, e']
          simp_rw [h2]
          rw [sum_ite_eq' univ k, if_pos (mem_univ k)]
          rcases ha_bin k with h | h <;> rw [h] <;> ring
        simp_rw [h1]; rw [← mul_sum]
      rw [he0_norm, hv_e0, hcross, hcross', hsum_sq]; ring
    rw [dot_sub_left, dot_sub_right, dot_sub_right, dot_comm projv (u v),
      hnorm v, hdot_up, hdot_pp] at hnn
    nlinarith
  -- Remainder vectors remW and remS.
  let remW : Fin 3 → R → E → ℝ := fun i v => u v + e0 - (1 / 2 : ℝ) • u (x i)
  let remS : Fin 3 → R → E → ℝ := fun i y => u y - e0 - (1 / 2 : ℝ) • u (x i)
  have hW_dots : ∀ (i : Fin 3), ∀ v ∈ W i,
      dot (u v) (u (x i)) = 1 ∧ dot (u v) e0 = -(1 / 2 : ℝ) := by
    intro i v hv
    have ⟨hvxi, hvp, hnpv⟩ := mem_filter.mp hv
    have hv_xi : dot (u v) (u (x i)) = 1 := ((hadj v (x i)).mp (hsym (mem_filter.mp hvxi).2)).2
    have hv_p : dot (u v) (u p) = 0 :=
      dot_zero_of_not_adj u adj hgram hadj hvp (fun h => hnpv (hsym h))
    refine ⟨hv_xi, ?_⟩
    dsimp [e0]
    rw [dot_sub_right, dot_smul_right, dot_sum_right, hv_p]
    have hsum : ∑ k : Fin 3, dot (u v) (u (x k)) = 1 := by
      have hterm : ∀ k : Fin 3, dot (u v) (u (x k)) = if k = i then 1 else 0 := by
        intro k
        by_cases e : k = i
        · subst e; simp [hv_xi]
        · simp only [e, ↓reduceIte]
          have ⟨hne, hna⟩ := hW_orth i v hv k e
          exact dot_zero_of_not_adj u adj hgram hadj hne (fun h => hna (hsym h))
      simp_rw [hterm]; simp
    rw [hsum]; ring
  have hS_dots : ∀ (i : Fin 3), ∀ y ∈ S i,
      dot (u y) (u (x i)) = 1 ∧ dot (u y) e0 = 1 / 2 := by
    intro i y hy
    have ⟨hyp, hyxi, hxiy, hoth⟩ := mem_filter.mp hy
    have hy_p : dot (u y) (u p) = 1 := ((hadj y p).mp (hsym (mem_filter.mp hyp).2)).2
    have hy_xi : dot (u y) (u (x i)) = 1 := ((hadj y (x i)).mp (hsym hxiy)).2
    refine ⟨hy_xi, ?_⟩
    dsimp [e0]
    rw [dot_sub_right, dot_smul_right, dot_sum_right, hy_p]
    have hsum : ∑ k : Fin 3, dot (u y) (u (x k)) = 1 := by
      have hterm : ∀ k : Fin 3, dot (u y) (u (x k)) = if k = i then 1 else 0 := by
        intro k
        by_cases e : k = i
        · subst e; simp [hy_xi]
        · simp only [e, ↓reduceIte]
          have hna : ¬ adj (x k) y := hoth k e
          have hne : y ≠ x k := fun eq => by
            have := (hnon i k (Ne.symm e)).2
            exact this (eq ▸ hxiy)
          exact dot_zero_of_not_adj u adj hgram hadj hne (fun h => hna (hsym h))
      simp_rw [hterm]; simp
    rw [hsum]; ring
  have hremW_dot : ∀ (i : Fin 3), ∀ v ∈ W i, ∀ v' ∈ W i,
      dot (remW i v) (remW i v') = dot (u v) (u v') - 1 := by
    intro i v hv v' hv'
    obtain ⟨hv1, hv0⟩ := hW_dots i v hv
    obtain ⟨hv'1, hv'0⟩ := hW_dots i v' hv'
    dsimp [remW]
    simp only [dot_sub_left, dot_sub_right, dot_add_left, dot_add_right,
      dot_smul_left, dot_smul_right]
    rw [dot_comm e0 (u v'), dot_comm (u (x i)) (u v'), dot_comm (u (x i)) e0,
      hv1, hv0, hv'1, hv'0, he0_x i, he0_norm, hnorm (x i)]
    ring
  have hremS_dot : ∀ (i : Fin 3), ∀ y ∈ S i, ∀ y' ∈ S i,
      dot (remS i y) (remS i y') = dot (u y) (u y') - 1 := by
    intro i y hy y' hy'
    obtain ⟨hy1, hy0⟩ := hS_dots i y hy
    obtain ⟨hy'1, hy'0⟩ := hS_dots i y' hy'
    dsimp [remS]
    simp only [dot_sub_left, dot_sub_right, dot_smul_left, dot_smul_right]
    rw [dot_comm e0 (u y'), dot_comm (u (x i)) (u y'), dot_comm (u (x i)) e0,
      hy1, hy0, hy'1, hy'0, he0_x i, he0_norm, hnorm (x i)]
    ring
  have hremSW_dot : ∀ (i j : Fin 3), j ≠ i → ∀ y ∈ S i, ∀ v ∈ W j,
      dot (remS i y) (remW j v) = 1 / 2 := by
    intro i j hji y hy v hv
    obtain ⟨hy1, hy0⟩ := hS_dots i y hy
    obtain ⟨hv1, hv0⟩ := hW_dots j v hv
    have hy_xj : dot (u y) (u (x j)) = 0 := by
      have ⟨_, _, hxiy, hoth⟩ := mem_filter.mp hy
      have hna := hoth j hji
      have hne : y ≠ x j := fun eq => (hnon i j (Ne.symm hji)).2 (eq ▸ hxiy)
      exact dot_zero_of_not_adj u adj hgram hadj hne (fun h => hna (hsym h))
    have hv_xi : dot (u v) (u (x i)) = 0 := by
      have ⟨hne, hna⟩ := hW_orth j v hv i (Ne.symm hji)
      exact dot_zero_of_not_adj u adj hgram hadj hne (fun h => hna (hsym h))
    have hcalc : dot (remS i y) (remW j v) = dot (u y) (u v) + 1 / 2 := by
      dsimp [remS, remW]
      simp only [dot_sub_left, dot_sub_right, dot_add_right, dot_smul_left, dot_smul_right]
      rw [dot_comm e0 (u v), dot_comm (u (x i)) (u v), dot_comm (u (x i)) e0,
        dot_comm (u (x i)) (u (x j)), hdot_xx j i, if_neg hji,
        hy0, hv0, hy_xj, hv_xi, he0_x i, he0_x j, he0_norm]
      ring
    have hyv_ne : y ≠ v := fun eq => by
      have h1 := (mem_filter.mp (mem_filter.mp hy).1).2
      have h2 := (mem_filter.mp hv).2.2
      exact h2 (eq ▸ h1)
    have hcs := dot_sq_le (remS i y) (remW j v)
    rw [hremS_dot i y hy y hy, hnorm y, hremW_dot j v hv v hv, hnorm v, hcalc] at hcs
    rcases hgram y v hyv_ne with h0 | h1
    · rw [hcalc, h0]; ring
    · rw [h1] at hcs; norm_num at hcs
  -- Bound |S i| ≤ 4 for every i.
  have hS_le4 : ∀ i : Fin 3, (S i).card ≤ 4 := by
    intro i
    let j : Fin 3 := ⟨(i.val + 1) % 3, Nat.mod_lt _ (by omega)⟩
    have hji : j ≠ i := by intro e; have := congrArg Fin.val e; dsimp [j] at this; omega
    obtain ⟨v0, hv0⟩ := card_pos.mp (by have := hW_ge3 j; omega : 0 < (W j).card)
    have horth : ∀ y ∈ S i, ∀ y' ∈ S i, dot (remS i y) (remS i y') = if y = y' then 1 else 0 := by
      intro y hy y' hy'
      rw [hremS_dot i y hy y' hy']
      by_cases e : y = y'
      · subst e; rw [hnorm y]; simp; norm_num
      · simp only [e, ↓reduceIte]
        rcases hgram y y' e with h0 | h1
        · exfalso
          have hzero : dot (remS i y + remS i y') (remS i y + remS i y') = 0 := by
            rw [dot_add_left, dot_add_right, dot_add_right, dot_comm (remS i y') (remS i y),
              hremS_dot i y hy y hy, hremS_dot i y' hy' y' hy', hremS_dot i y hy y' hy',
              hnorm y, hnorm y', h0]
            ring
          have hsum0 : remS i y + remS i y' = 0 := dot_self_eq_zero.mp hzero
          have hdot0 : dot (remS i y + remS i y') (remW j v0) = 0 := by rw [hsum0, dot_zero_left]
          rw [dot_add_left, hremSW_dot i j hji y hy v0 hv0, hremSW_dot i j hji y' hy' v0 hv0] at hdot0
          norm_num at hdot0
        · rw [h1]; ring
    have hbes := bessel_ineq (S i) (remS i) horth (remW j v0)
    have hlhs : ∑ y ∈ S i, dot (remW j v0) (remS i y) ^ 2 = ((S i).card : ℝ) * (1 / 4) := by
      have hterm : ∀ y ∈ S i, dot (remW j v0) (remS i y) ^ 2 = 1 / 4 := by
        intro y hy; rw [dot_comm, hremSW_dot i j hji y hy v0 hv0]; norm_num
      rw [sum_congr rfl hterm, sum_const, nsmul_eq_mul]
    rw [hlhs, hremW_dot j v0 hv0 v0 hv0, hnorm v0] at hbes
    have hcast : ((S i).card : ℝ) ≤ 4 := by linarith
    exact_mod_cast hcast
  -- Bound |W i| ≤ 4 whenever S j is nonempty for some j ≠ i.
  have hW_le4_of_S : ∀ (i j : Fin 3), j ≠ i → (S j).Nonempty → (W i).card ≤ 4 := by
    intro i j hji ⟨y0, hy0⟩
    have horth : ∀ v ∈ W i, ∀ v' ∈ W i, dot (remW i v) (remW i v') = if v = v' then 1 else 0 := by
      intro v hv v' hv'
      rw [hremW_dot i v hv v' hv']
      by_cases e : v = v'
      · subst e; rw [hnorm v]; simp; norm_num
      · simp only [e, ↓reduceIte]
        rcases hgram v v' e with h0 | h1
        · exfalso
          have hzero : dot (remW i v + remW i v') (remW i v + remW i v') = 0 := by
            rw [dot_add_left, dot_add_right, dot_add_right, dot_comm (remW i v') (remW i v),
              hremW_dot i v hv v hv, hremW_dot i v' hv' v' hv', hremW_dot i v hv v' hv',
              hnorm v, hnorm v', h0]
            ring
          have hsum0 : remW i v + remW i v' = 0 := dot_self_eq_zero.mp hzero
          have hdot0 : dot (remS j y0) (remW i v + remW i v') = 0 := by
            rw [hsum0, dot_comm, dot_zero_left]
          rw [dot_add_right, hremSW_dot j i (Ne.symm hji) y0 hy0 v hv,
            hremSW_dot j i (Ne.symm hji) y0 hy0 v' hv'] at hdot0
          norm_num at hdot0
        · rw [h1]; ring
    have hbes := bessel_ineq (W i) (remW i) horth (remS j y0)
    have hlhs : ∑ v ∈ W i, dot (remS j y0) (remW i v) ^ 2 = ((W i).card : ℝ) * (1 / 4) := by
      have hterm : ∀ v ∈ W i, dot (remS j y0) (remW i v) ^ 2 = 1 / 4 := by
        intro v hv; rw [hremSW_dot j i (Ne.symm hji) y0 hy0 v hv]; norm_num
      rw [sum_congr rfl hterm, sum_const, nsmul_eq_mul]
    rw [hlhs, hremS_dot j y0 hy0 y0 hy0, hnorm y0] at hbes
    have hcast : ((W i).card : ℝ) ≤ 4 := by linarith
    exact_mod_cast hcast
  -- Bound |W i| ≤ 5 unconditionally.
  have hW_le5 : ∀ i : Fin 3, (W i).card ≤ 5 := by
    intro i
    by_cases hnonadj : ∃ v ∈ W i, ∃ v' ∈ W i, v ≠ v' ∧ ¬ adj v v'
    · obtain ⟨v, hv, v', hv', hvv', hna⟩ := hnonadj
      have h0 : dot (u v) (u v') = 0 := dot_zero_of_not_adj u adj hgram hadj hvv' hna
      have hsum0 : remW i v + remW i v' = 0 := by
        apply dot_self_eq_zero.mp
        rw [dot_add_left, dot_add_right, dot_add_right, dot_comm (remW i v') (remW i v),
          hremW_dot i v hv v hv, hremW_dot i v' hv' v' hv', hremW_dot i v hv v' hv',
          hnorm v, hnorm v', h0]
        ring
      have hsub : insert (x i) (((W i).erase v).erase v') ⊆ nbrs adj v ∩ nbrs adj v' := by
        intro w hw
        rcases mem_insert.mp hw with rfl | hw'
        · exact mem_inter.mpr ⟨mem_filter.mpr ⟨mem_univ _, hsym (mem_filter.mp (mem_filter.mp hv).1).2⟩,
            mem_filter.mpr ⟨mem_univ _, hsym (mem_filter.mp (mem_filter.mp hv').1).2⟩⟩
        · have ⟨hwv', hw1⟩ := mem_erase.mp hw'
          have ⟨hwv, hwW⟩ := mem_erase.mp hw1
          have hadj_vw : adj v w := by
            by_contra hnv
            have h0' := dot_zero_of_not_adj u adj hgram hadj (Ne.symm hwv) hnv
            have hsum' : remW i v + remW i w = 0 := by
              apply dot_self_eq_zero.mp
              rw [dot_add_left, dot_add_right, dot_add_right, dot_comm (remW i w) (remW i v),
                hremW_dot i v hv v hv, hremW_dot i w hwW w hwW, hremW_dot i v hv w hwW,
                hnorm v, hnorm w, h0']
              ring
            have hdiff : remW i w = remW i v' := by
              have : remW i w - remW i v' = (remW i v + remW i w) - (remW i v + remW i v') := by abel
              rw [hsum', hsum0, sub_self] at this
              exact sub_eq_zero.mp this
            have hd1 : dot (remW i w) (remW i v') = 1 := by
              rw [hdiff, hremW_dot i v' hv' v' hv', hnorm v']; ring
            rw [hremW_dot i w hwW v' hv'] at hd1
            rcases hgram w v' hwv' with h | h <;> linarith
          have hdot_vw : dot (remW i v) (remW i w) = 0 := by
            rw [hremW_dot i v hv w hwW, ((hadj v w).mp hadj_vw).2]; ring
          have hdot_v'w : dot (remW i v') (remW i w) = 0 := by
            have h0sum : dot (remW i v + remW i v') (remW i w) = 0 := by rw [hsum0, dot_zero_left]
            rw [dot_add_left, hdot_vw, zero_add] at h0sum
            exact h0sum
          have hadj_v'w : adj v' w := by
            rw [hremW_dot i v' hv' w hwW] at hdot_v'w
            exact (hadj v' w).mpr ⟨Ne.symm hwv', by linarith⟩
          exact mem_inter.mpr ⟨mem_filter.mpr ⟨mem_univ _, hadj_vw⟩,
            mem_filter.mpr ⟨mem_univ _, hadj_v'w⟩⟩
      have hxi_not : x i ∉ ((W i).erase v).erase v' := by
        intro hmem
        have hW := (mem_erase.mp (mem_erase.mp hmem).2).2
        exact hirr (x i) (mem_filter.mp (mem_filter.mp hW).1).2
      have hc := card_le_card hsub
      rw [card_insert_of_notMem hxi_not, card_erase_of_mem (mem_erase.mpr ⟨Ne.symm hvv', hv'⟩),
        card_erase_of_mem hv] at hc
      have h4 := hcomm_nonadj v v' hvv' hna
      have h3 := hW_ge3 i
      omega
    · push Not at hnonadj
      let j : Fin 3 := ⟨(i.val + 1) % 3, Nat.mod_lt _ (by omega)⟩
      have hji : j ≠ i := by intro e; have := congrArg Fin.val e; dsimp [j] at this; omega
      obtain ⟨w0, hw0⟩ := card_pos.mp (by have := hW_ge3 j; omega : 0 < (W j).card)
      have horth : ∀ v ∈ W i, ∀ v' ∈ W i, dot (remW i v) (remW i v') = if v = v' then 1 else 0 := by
        intro v hv v' hv'
        rw [hremW_dot i v hv v' hv']
        by_cases e : v = v'
        · subst e; rw [hnorm v]; simp; norm_num
        · simp only [e, ↓reduceIte]
          rw [((hadj v v').mp (hnonadj v hv v' hv' e)).2]; ring
      have hsq_quarter : ∀ v ∈ W i, dot (remW j w0) (remW i v) ^ 2 = 1 / 4 := by
        intro v hv
        obtain ⟨hv1, hv0⟩ := hW_dots i v hv
        obtain ⟨hw1, hw0'⟩ := hW_dots j w0 hw0
        have hv_xj : dot (u v) (u (x j)) = 0 := by
          have ⟨hne, hna⟩ := hW_orth i v hv j hji
          exact dot_zero_of_not_adj u adj hgram hadj hne (fun h => hna (hsym h))
        have hw_xi : dot (u w0) (u (x i)) = 0 := by
          have ⟨hne, hna⟩ := hW_orth j w0 hw0 i (Ne.symm hji)
          exact dot_zero_of_not_adj u adj hgram hadj hne (fun h => hna (hsym h))
        have hcalc : dot (remW j w0) (remW i v) = dot (u w0) (u v) - 1 / 2 := by
          dsimp [remW]
          simp only [dot_sub_left, dot_sub_right, dot_add_left, dot_add_right,
            dot_smul_left, dot_smul_right]
          rw [dot_comm e0 (u v), dot_comm (u (x j)) (u v), dot_comm (u (x j)) e0,
            dot_comm (u (x j)) (u (x i)), hdot_xx i j, if_neg (Ne.symm hji),
            hv0, hw0', hv_xj, hw_xi, he0_x i, he0_x j, he0_norm]
          ring
        have hne : w0 ≠ v := fun eq => by
          have := (hW_orth j w0 hw0 i (Ne.symm hji)).2
          exact this (eq ▸ (mem_filter.mp (mem_filter.mp hv).1).2)
        rw [hcalc]
        rcases hgram w0 v hne with h0 | h0 <;> rw [h0] <;> norm_num
      have hbes := bessel_ineq (W i) (remW i) horth (remW j w0)
      rw [sum_congr rfl hsq_quarter, sum_const, nsmul_eq_mul,
        hremW_dot j w0 hw0 w0 hw0, hnorm w0] at hbes
      have hcast : ((W i).card : ℝ) ≤ 4 := by linarith
      have hle4 : (W i).card ≤ 4 := by exact_mod_cast hcast
      omega
  -- Finish: either some S i = ∅ (giving deg ≤ 12) or all S i nonempty (giving deg ≤ 15).
  by_cases hempty : ∃ i : Fin 3, S i = ∅
  · obtain ⟨i, hi⟩ := hempty
    have h1 := hdeg_split i
    have h2 := hW_le5 i
    rw [hi, card_empty] at h1
    omega
  · push Not at hempty
    have hS1 : (S 1).Nonempty := hempty 1
    have h1 := hdeg_split 0
    have h2 := hW_le4_of_S 0 1 (by decide) hS1
    have h3 := hS_le4 0
    omega

private lemma claw_free3
    (u : R → E → ℝ) (adj : R → R → Prop) [DecidableRel adj]
    (hnorm : ∀ p, dot (u p) (u p) = 2)
    (hgram : ∀ p q, p ≠ q → dot (u p) (u q) = 0 ∨ dot (u p) (u q) = 1)
    (hadj : ∀ p q, adj p q ↔ p ≠ q ∧ dot (u p) (u q) = 1)
    (hdeg : ∀ p, 16 ≤ (nbrs adj p).card)
    (hcomm_adj : ∀ p q, adj p q → (nbrs adj p ∩ nbrs adj q).card ≤ 12)
    (hcomm_nonadj : ∀ p q, p ≠ q → ¬ adj p q → (nbrs adj p ∩ nbrs adj q).card ≤ 4)
    (p x0 x1 x2 : R)
    (h0 : adj p x0) (h1 : adj p x1) (h2 : adj p x2)
    (h01 : x0 ≠ x1 ∧ ¬ adj x0 x1) (h02 : x0 ≠ x2 ∧ ¬ adj x0 x2) (h12 : x1 ≠ x2 ∧ ¬ adj x1 x2) :
    False := by
  have hsym := adj_symm_of_gram u adj hadj
  let x : Fin 3 → R := fun i => match i.val with | 0 => x0 | 1 => x1 | _ => x2
  refine claw_free u adj hnorm hgram hadj hdeg hcomm_adj hcomm_nonadj p x ?_ ?_
  · intro i; fin_cases i
    · exact h0
    · exact h1
    · exact h2
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact h01
    · exact h02
    · exact ⟨h01.1.symm, fun h => h01.2 (hsym h)⟩
    · exact absurd rfl hij
    · exact h12
    · exact ⟨h02.1.symm, fun h => h02.2 (hsym h)⟩
    · exact ⟨h12.1.symm, fun h => h12.2 (hsym h)⟩
    · exact absurd rfl hij

private lemma bool5_adj_true (b : Fin 5 → Bool)
    (h : ∀ i : Fin 5, b i = true ∨ b ⟨(i.val + 1) % 5, Nat.mod_lt _ (by omega)⟩ = true) :
    ∃ i : Fin 5, b i = true ∧ b ⟨(i.val + 1) % 5, Nat.mod_lt _ (by omega)⟩ = true := by
  by_contra hnone
  push Not at hnone
  have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3; have h4 := h 4
  have n0 := hnone 0; have n1 := hnone 1; have n2 := hnone 2; have n3 := hnone 3; have n4 := hnone 4
  cases hb0 : b 0 <;> cases hb1 : b 1 <;> cases hb2 : b 2 <;> cases hb3 : b 3 <;> cases hb4 : b 4 <;>
    simp_all

private lemma odd_iff7 {P0 P1 P2 P3 P4 P5 P6 : Prop}
    (e0 : P0 ↔ ¬ P1) (e1 : P1 ↔ ¬ P2) (e2 : P2 ↔ ¬ P3) (e3 : P3 ↔ ¬ P4)
    (e4 : P4 ↔ ¬ P5) (e5 : P5 ↔ ¬ P6) (e6 : P6 ↔ ¬ P0) : False := by
  by_cases h0 : P0
  · have h1 : ¬ P1 := e0.mp h0
    have h2 : P2 := by by_contra hn; exact h1 (e1.mpr hn)
    have h3 : ¬ P3 := e2.mp h2
    have h4 : P4 := by by_contra hn; exact h3 (e3.mpr hn)
    have h5 : ¬ P5 := e4.mp h4
    have h6 : P6 := by by_contra hn; exact h5 (e5.mpr hn)
    exact e6.mp h6 h0
  · have h6 : P6 := e6.mpr h0
    have h5 : ¬ P5 := fun h => e5.mp h h6
    have h4 : P4 := e4.mpr h5
    have h3 : ¬ P3 := fun h => e3.mp h h4
    have h2 : P2 := e2.mpr h3
    have h1 : ¬ P1 := fun h => e1.mp h h2
    exact h0 (e0.mpr h1)

set_option maxHeartbeats 800000 in
/-- Step 3: For every `p : R`, the complement graph on `nbrs adj p` is connected and bipartite,
yielding a unique unordered partition `nbrs adj p = A ⊔ B` into two disjoint cliques with
`|A| ≥ 3` and `|B| ≥ 3`. -/
theorem nbrhd_bipartite_connected
    (u : R → E → ℝ) (adj : R → R → Prop) [DecidableRel adj]
    (hnorm : ∀ p, dot (u p) (u p) = 2)
    (hgram : ∀ p q, p ≠ q → dot (u p) (u q) = 0 ∨ dot (u p) (u q) = 1)
    (hadj : ∀ p q, adj p q ↔ p ≠ q ∧ dot (u p) (u q) = 1)
    (hdeg : ∀ p, 16 ≤ (nbrs adj p).card)
    (hcomm_adj : ∀ p q, adj p q → (nbrs adj p ∩ nbrs adj q).card ≤ 12)
    (hcomm_nonadj : ∀ p q, p ≠ q → ¬ adj p q → (nbrs adj p ∩ nbrs adj q).card ≤ 4)
    (p : R) :
    ∃ col : R → Bool,
      (∀ x ∈ nbrs adj p, ∀ y ∈ nbrs adj p, x ≠ y → ¬ adj x y → col x ≠ col y) ∧
      (∀ x ∈ nbrs adj p, 3 ≤ ((nbrs adj p).filter fun y => y ≠ x ∧ ¬ adj x y).card) ∧
      (∀ (x : R) (hx : x ∈ nbrs adj p) (y : R) (hy : y ∈ nbrs adj p),
        ∃ m, Walk (fun a b : {z : R // z ∈ nbrs adj p} => a ≠ b ∧ ¬ adj a.1 b.1)
          m ⟨x, hx⟩ ⟨y, hy⟩) := by
  classical
  have hsym := adj_symm_of_gram u adj hadj
  have hirr := adj_irrefl_of_gram u adj hadj
  let N := { z : R // z ∈ nbrs adj p }
  let compE : N → N → Prop := fun a b => a ≠ b ∧ ¬ adj a.1 b.1
  have hcomp_sym : Symmetric compE := fun a b ⟨hne, hna⟩ => ⟨hne.symm, fun h => hna (hsym h)⟩
  have hcomp_irr : Irreflexive compE := fun a ⟨hne, _⟩ => hne rfl
  -- Minimum degree in compE is ≥ 3.
  have hmin_comp : ∀ x ∈ nbrs adj p,
      3 ≤ ((nbrs adj p).filter fun y => y ≠ x ∧ ¬ adj x y).card := by
    intro x hx
    have hsplit : (nbrs adj p).erase x =
        ((nbrs adj p).filter fun y => y ≠ x ∧ ¬ adj x y) ∪ (nbrs adj p ∩ nbrs adj x) := by
      ext y
      simp only [mem_erase, mem_union, mem_filter, mem_inter, nbrs, mem_univ, true_and]
      constructor
      · rintro ⟨hyx, hpy⟩
        by_cases hxy : adj x y
        · exact Or.inr ⟨hpy, hxy⟩
        · exact Or.inl ⟨hpy, hyx, hxy⟩
      · rintro (⟨hpy, hyx, _⟩ | ⟨hpy, hxy⟩)
        · exact ⟨hyx, hpy⟩
        · exact ⟨fun e => hirr x (e ▸ hxy), hpy⟩
    have hdisj : Disjoint ((nbrs adj p).filter fun y => y ≠ x ∧ ¬ adj x y)
        (nbrs adj p ∩ nbrs adj x) := by
      apply Finset.disjoint_left.mpr
      intro y h1 h2
      exact (mem_filter.mp h1).2.2 (mem_filter.mp (mem_inter.mp h2).2).2
    have hc := congrArg Finset.card hsplit
    rw [card_erase_of_mem hx, card_union_of_disjoint hdisj] at hc
    have h1 := hdeg p
    have h2 := hcomm_adj p x (mem_filter.mp hx).2
    omega
  -- No induced odd cycle in compE.
  have hno_odd : ∀ k : ℕ, k % 2 = 1 → 3 ≤ k → ∀ f : Fin k → N,
      Function.Injective f →
      (∀ i j : Fin k, i ≠ j → (compE (f i) (f j) ↔ cyclicAdj k i j)) → False := by
    intro k hko hk3 f hinj hiff
    have hfi_adj_p : ∀ i : Fin k, adj p (f i).1 := fun i => (mem_filter.mp (f i).2).2
    have hfi_inj : Function.Injective (fun i => (f i).1) := fun i j h => hinj (Subtype.ext h)
    have hcyc_not_adj : ∀ i j : Fin k, i ≠ j → cyclicAdj k i j → ¬ adj (f i).1 (f j).1 :=
      fun i j hne hc => ((hiff i j hne).mpr hc).2
    have hnoncyc_adj : ∀ i j : Fin k, i ≠ j → ¬ cyclicAdj k i j → adj (f i).1 (f j).1 := by
      intro i j hne hnc
      by_contra hna
      have hcomp : compE (f i) (f j) := ⟨fun e => hne (hinj e), hna⟩
      exact hnc ((hiff i j hne).mp hcomp)
    by_cases hk3' : k = 3
    · subst hk3'
      refine claw_free u adj hnorm hgram hadj hdeg hcomm_adj hcomm_nonadj p (fun i => (f i).1)
        hfi_adj_p fun i j hne => ⟨fun e => hne (hfi_inj e), hcyc_not_adj i j hne ?_⟩
      fin_cases i <;> fin_cases j <;> simp_all [cyclicAdj]
    · by_cases hk5 : k = 5
      · subst hk5
        let img : Finset R := univ.image fun i : Fin 5 => (f i).1
        have himg_card : img.card = 5 := by
          rw [card_image_of_injective _ hfi_inj, card_univ, Fintype.card_fin]
        let out := nbrs adj p \ img
        -- Every y ∈ out hits some adjacent pair (f i, f (i+1)).
        have hout_sub : out ⊆ univ.biUnion fun i : Fin 5 =>
            out.filter fun y => adj y (f i).1 ∧ adj y (f ⟨(i.val + 1) % 5, Nat.mod_lt _ (by omega)⟩).1 := by
          intro y hy
          have ⟨hyp, hyout⟩ := mem_sdiff.mp hy
          let b : Fin 5 → Bool := fun i => decide (adj y (f i).1)
          have hb : ∀ i : Fin 5, b i = true ∨ b ⟨(i.val + 1) % 5, Nat.mod_lt _ (by omega)⟩ = true := by
            intro i
            by_contra hboth
            push Not at hboth
            have h1 : ¬ adj y (f i).1 := by simpa [b] using hboth.1
            let j : Fin 5 := ⟨(i.val + 1) % 5, Nat.mod_lt _ (by omega)⟩
            have h2 : ¬ adj y (f j).1 := by simpa [b, j] using hboth.2
            have hij : i ≠ j := by intro e; have := congrArg Fin.val e; dsimp [j] at this; omega
            have h12 : ¬ adj (f i).1 (f j).1 := hcyc_not_adj i j hij (Or.inl rfl)
            have hyi : y ≠ (f i).1 := fun e => hyout (e ▸ mem_image_of_mem _ (mem_univ i))
            have hyj : y ≠ (f j).1 := fun e => hyout (e ▸ mem_image_of_mem _ (mem_univ j))
            exact claw_free3 u adj hnorm hgram hadj hdeg hcomm_adj hcomm_nonadj p
              y (f i).1 (f j).1 (mem_filter.mp hyp).2 (hfi_adj_p i) (hfi_adj_p j)
              ⟨hyi, h1⟩ ⟨hyj, h2⟩ ⟨fun e => hij (hfi_inj e), h12⟩
          obtain ⟨i, hi1, hi2⟩ := bool5_adj_true b hb
          refine mem_biUnion.mpr ⟨i, mem_univ _, mem_filter.mpr ⟨hy, ?_, ?_⟩⟩
          · simpa [b] using hi1
          · simpa [b] using hi2
        have hbi_le : (univ.biUnion fun i : Fin 5 =>
            out.filter fun y => adj y (f i).1 ∧ adj y (f ⟨(i.val + 1) % 5, Nat.mod_lt _ (by omega)⟩).1).card ≤ 10 := by
          calc
            _ ≤ ∑ i : Fin 5, (out.filter fun y =>
                  adj y (f i).1 ∧ adj y (f ⟨(i.val + 1) % 5, Nat.mod_lt _ (by omega)⟩).1).card :=
                card_biUnion_le
            _ ≤ ∑ _i : Fin 5, 2 := by
              apply sum_le_sum; intro i _
              let j : Fin 5 := ⟨(i.val + 1) % 5, Nat.mod_lt _ (by omega)⟩
              let m : Fin 5 := ⟨(i.val + 3) % 5, Nat.mod_lt _ (by omega)⟩
              have hij : i ≠ j := by intro e; have := congrArg Fin.val e; dsimp [j] at this; omega
              have him : i ≠ m := by intro e; have := congrArg Fin.val e; dsimp [m] at this; omega
              have hjm : j ≠ m := by intro e; have := congrArg Fin.val e; dsimp [j, m] at this; omega
              have hnc_im : ¬ cyclicAdj 5 i m := by
                dsimp [cyclicAdj, m]; omega
              have hnc_jm : ¬ cyclicAdj 5 j m := by
                dsimp [cyclicAdj, j, m]; omega
              have hsub2 : out.filter (fun y => adj y (f i).1 ∧ adj y (f j).1) ⊆
                  ((nbrs adj (f i).1 ∩ nbrs adj (f j).1).erase p).erase (f m).1 := by
                intro y hy
                have ⟨hyout', hyi, hyj⟩ := mem_filter.mp hy
                have ⟨hyp', hyimg⟩ := mem_sdiff.mp hyout'
                refine mem_erase.mpr ⟨fun e => hyimg (e ▸ mem_image_of_mem _ (mem_univ m)),
                  mem_erase.mpr ⟨fun e => hirr p (e ▸ (mem_filter.mp hyp').2),
                    mem_inter.mpr ⟨mem_filter.mpr ⟨mem_univ _, hsym hyi⟩,
                      mem_filter.mpr ⟨mem_univ _, hsym hyj⟩⟩⟩⟩
              have hp_in : p ∈ nbrs adj (f i).1 ∩ nbrs adj (f j).1 :=
                mem_inter.mpr ⟨mem_filter.mpr ⟨mem_univ _, hsym (hfi_adj_p i)⟩,
                  mem_filter.mpr ⟨mem_univ _, hsym (hfi_adj_p j)⟩⟩
              have hm_in : (f m).1 ∈ (nbrs adj (f i).1 ∩ nbrs adj (f j).1).erase p :=
                mem_erase.mpr ⟨by intro e; have h := hfi_adj_p m; rw [e] at h; exact hirr p h,
                  mem_inter.mpr ⟨mem_filter.mpr ⟨mem_univ _, hnoncyc_adj i m him hnc_im⟩,
                    mem_filter.mpr ⟨mem_univ _, hnoncyc_adj j m hjm hnc_jm⟩⟩⟩
              have hc := card_le_card hsub2
              rw [card_erase_of_mem hm_in, card_erase_of_mem hp_in] at hc
              have h4 := hcomm_nonadj (f i).1 (f j).1 (fun e => hij (hfi_inj e))
                (hcyc_not_adj i j hij (Or.inl rfl))
              change (out.filter fun y => adj y (f i).1 ∧ adj y (f j).1).card ≤ 2
              omega
            _ = 10 := by simp
        have himg_sub : img ⊆ nbrs adj p := by
          intro x hx; obtain ⟨i, _, rfl⟩ := mem_image.mp hx; exact (f i).2
        have hsd : out.card = (nbrs adj p).card - img.card := card_sdiff_of_subset himg_sub
        rw [himg_card] at hsd
        have hc := card_le_card hout_sub
        have hd := hdeg p
        omega
      · by_cases hk7 : k = 7
        · subst hk7
          let img : Finset R := univ.image fun i : Fin 7 => (f i).1
          have himg_card : img.card = 7 := by
            rw [card_image_of_injective _ hfi_inj, card_univ, Fintype.card_fin]
          have himg_sub : img ⊆ nbrs adj p := by
            intro x hx; obtain ⟨i, _, rfl⟩ := mem_image.mp hx; exact (f i).2
          have hne_out : (nbrs adj p \ img).Nonempty := by
            apply card_pos.mp
            rw [card_sdiff_of_subset himg_sub, himg_card]
            have := hdeg p; omega
          obtain ⟨y, hy⟩ := hne_out
          have ⟨hyp, hyimg⟩ := mem_sdiff.mp hy
          have halt : ∀ i : Fin 7,
              adj y (f i).1 ↔ ¬ adj y (f ⟨(i.val + 1) % 7, Nat.mod_lt _ (by omega)⟩).1 := by
            intro i
            let j : Fin 7 := ⟨(i.val + 1) % 7, Nat.mod_lt _ (by omega)⟩
            have hij : i ≠ j := by intro e; have := congrArg Fin.val e; dsimp [j] at this; omega
            constructor
            · intro hyi hyj
              let m1 : Fin 7 := ⟨(i.val + 3) % 7, Nat.mod_lt _ (by omega)⟩
              let m2 : Fin 7 := ⟨(i.val + 4) % 7, Nat.mod_lt _ (by omega)⟩
              let m3 : Fin 7 := ⟨(i.val + 5) % 7, Nat.mod_lt _ (by omega)⟩
              let S5 : Finset R := {p, y, (f m1).1, (f m2).1, (f m3).1}
              have hS5_sub : S5 ⊆ nbrs adj (f i).1 ∩ nbrs adj (f j).1 := by
                intro z hz
                simp only [S5, mem_insert, mem_singleton] at hz
                rcases hz with rfl | rfl | rfl | rfl | rfl
                · exact mem_inter.mpr ⟨mem_filter.mpr ⟨mem_univ _, hsym (hfi_adj_p i)⟩,
                    mem_filter.mpr ⟨mem_univ _, hsym (hfi_adj_p j)⟩⟩
                · exact mem_inter.mpr ⟨mem_filter.mpr ⟨mem_univ _, hsym hyi⟩,
                    mem_filter.mpr ⟨mem_univ _, hsym hyj⟩⟩
                · exact mem_inter.mpr
                    ⟨mem_filter.mpr ⟨mem_univ _, hnoncyc_adj i m1 (by intro e; have := congrArg Fin.val e; dsimp [m1] at this; omega) (by dsimp [cyclicAdj, m1]; omega)⟩,
                     mem_filter.mpr ⟨mem_univ _, hnoncyc_adj j m1 (by intro e; have := congrArg Fin.val e; dsimp [j, m1] at this; omega) (by dsimp [cyclicAdj, j, m1]; omega)⟩⟩
                · exact mem_inter.mpr
                    ⟨mem_filter.mpr ⟨mem_univ _, hnoncyc_adj i m2 (by intro e; have := congrArg Fin.val e; dsimp [m2] at this; omega) (by dsimp [cyclicAdj, m2]; omega)⟩,
                     mem_filter.mpr ⟨mem_univ _, hnoncyc_adj j m2 (by intro e; have := congrArg Fin.val e; dsimp [j, m2] at this; omega) (by dsimp [cyclicAdj, j, m2]; omega)⟩⟩
                · exact mem_inter.mpr
                    ⟨mem_filter.mpr ⟨mem_univ _, hnoncyc_adj i m3 (by intro e; have := congrArg Fin.val e; dsimp [m3] at this; omega) (by dsimp [cyclicAdj, m3]; omega)⟩,
                     mem_filter.mpr ⟨mem_univ _, hnoncyc_adj j m3 (by intro e; have := congrArg Fin.val e; dsimp [j, m3] at this; omega) (by dsimp [cyclicAdj, j, m3]; omega)⟩⟩
              have hS5_card : S5.card = 5 := by
                have hp_ne_y : p ≠ y := fun e => hirr p (e ▸ (mem_filter.mp hyp).2)
                have hp_ne_f : ∀ m : Fin 7, p ≠ (f m).1 := by
                  intro m e; have h := hfi_adj_p m; rw [← e] at h; exact hirr p h
                have hy_ne_f : ∀ m : Fin 7, y ≠ (f m).1 := fun m e =>
                  hyimg (e ▸ mem_image_of_mem _ (mem_univ m))
                have hm12 : (f m1).1 ≠ (f m2).1 := fun e => by
                  have := congrArg Fin.val (hfi_inj e); dsimp [m1, m2] at this; omega
                have hm13 : (f m1).1 ≠ (f m3).1 := fun e => by
                  have := congrArg Fin.val (hfi_inj e); dsimp [m1, m3] at this; omega
                have hm23 : (f m2).1 ≠ (f m3).1 := fun e => by
                  have := congrArg Fin.val (hfi_inj e); dsimp [m2, m3] at this; omega
                dsimp [S5]
                rw [card_insert_of_notMem (by simp [hp_ne_y, hp_ne_f]),
                  card_insert_of_notMem (by simp [hy_ne_f]),
                  card_insert_of_notMem (by simp [hm12, hm13]),
                  card_insert_of_notMem (by simp [hm23]), card_singleton]
              have hc := card_le_card hS5_sub
              have h4 := hcomm_nonadj (f i).1 (f j).1 (fun e => hij (hfi_inj e))
                (hcyc_not_adj i j hij (Or.inl rfl))
              omega
            · intro hnyj
              by_contra hnyi
              have h12 := hcyc_not_adj i j hij (Or.inl rfl)
              have hyi : y ≠ (f i).1 := fun e => hyimg (e ▸ mem_image_of_mem _ (mem_univ i))
              have hyj : y ≠ (f j).1 := fun e => hyimg (e ▸ mem_image_of_mem _ (mem_univ j))
              exact claw_free3 u adj hnorm hgram hadj hdeg hcomm_adj hcomm_nonadj p
                y (f i).1 (f j).1 (mem_filter.mp hyp).2 (hfi_adj_p i) (hfi_adj_p j)
                ⟨hyi, hnyi⟩ ⟨hyj, hnyj⟩ ⟨fun e => hij (hfi_inj e), h12⟩
          have h01 : adj y (f 0).1 ↔ ¬ adj y (f 1).1 := halt 0
          have h12 : adj y (f 1).1 ↔ ¬ adj y (f 2).1 := halt 1
          have h23 : adj y (f 2).1 ↔ ¬ adj y (f 3).1 := halt 2
          have h34 : adj y (f 3).1 ↔ ¬ adj y (f 4).1 := halt 3
          have h45 : adj y (f 4).1 ↔ ¬ adj y (f 5).1 := halt 4
          have h56 : adj y (f 5).1 ↔ ¬ adj y (f 6).1 := halt 5
          have h60 : adj y (f 6).1 ↔ ¬ adj y (f 0).1 := halt 6
          exact odd_iff7 h01 h12 h23 h34 h45 h56 h60
        · -- k ≥ 9: f 0 and f 1 already have ≥ (k - 4) + 1 ≥ 6 > 4 common neighbors.
          have hk9 : 9 ≤ k := by omega
          let i0 : Fin k := ⟨0, by omega⟩
          let i1 : Fin k := ⟨1, by omega⟩
          let mid : Finset (Fin k) := univ.filter fun m => 3 ≤ m.val ∧ m.val ≤ k - 2
          have hmid_card : k - 4 ≤ mid.card := by
            have hbi : (Finset.Icc 3 (k - 2)).card ≤ mid.card := by
              refine Finset.card_le_card_of_injOn (fun n => if h : n < k then ⟨n, h⟩ else i0) ?_ ?_
              · intro n hn
                simp only [Finset.mem_coe, mem_Icc] at hn
                have hlt : n < k := by omega
                simp [hlt, mid, hn.1, hn.2]
              · intro n1 hn1 n2 hn2 heq
                simp only [Finset.mem_coe, mem_Icc] at hn1 hn2
                have h1 : n1 < k := by omega
                have h2 : n2 < k := by omega
                simp only [h1, h2, ↓reduceDIte] at heq
                exact congrArg Fin.val heq
            rw [Nat.card_Icc] at hbi
            omega
          let Sbig : Finset R := mid.image fun m => (f m).1
          have hSbig_sub : Sbig ⊆ nbrs adj (f i0).1 ∩ nbrs adj (f i1).1 := by
            intro z hz
            obtain ⟨m, hm, rfl⟩ := mem_image.mp hz
            have ⟨hm3, hmk⟩ := (mem_filter.mp hm).2
            have hi0m : i0 ≠ m := by intro e; have := congrArg Fin.val e; dsimp [i0] at this; omega
            have hi1m : i1 ≠ m := by intro e; have := congrArg Fin.val e; dsimp [i1] at this; omega
            have hnc0 : ¬ cyclicAdj k i0 m := by
              dsimp [cyclicAdj, i0]
              have hmod1 : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
              have hmod2 : (m.val + 1) % k = m.val + 1 := Nat.mod_eq_of_lt (by omega)
              omega
            have hnc1 : ¬ cyclicAdj k i1 m := by
              dsimp [cyclicAdj, i1]
              have hmod1 : 2 % k = 2 := Nat.mod_eq_of_lt (by omega)
              have hmod2 : (m.val + 1) % k = m.val + 1 := Nat.mod_eq_of_lt (by omega)
              omega
            exact mem_inter.mpr
              ⟨mem_filter.mpr ⟨mem_univ _, hnoncyc_adj i0 m hi0m hnc0⟩,
               mem_filter.mpr ⟨mem_univ _, hnoncyc_adj i1 m hi1m hnc1⟩⟩
          have hSbig_card : Sbig.card = mid.card := card_image_of_injective _ hfi_inj
          have hc := card_le_card hSbig_sub
          have hi01 : i0 ≠ i1 := by intro e; have := congrArg Fin.val e; dsimp [i0, i1] at this; omega
          have hcyc01 : cyclicAdj k i0 i1 := by
            left; dsimp [i0, i1]; exact Nat.mod_eq_of_lt (by omega)
          have h4 := hcomm_nonadj (f i0).1 (f i1).1 (fun e => hi01 (hfi_inj e))
            (hcyc_not_adj i0 i1 hi01 hcyc01)
          omega
  -- Bipartite coloring of compE on N.
  obtain ⟨colN, hcolN⟩ := bipartite_of_no_induced_odd_cycle compE hcomp_sym hcomp_irr hno_odd
  let col : R → Bool := fun x => if h : x ∈ nbrs adj p then colN ⟨x, h⟩ else false
  -- Connectedness of compE on N.
  have hconn : ∀ (x : R) (hx : x ∈ nbrs adj p) (y : R) (hy : y ∈ nbrs adj p),
      ∃ m, Walk compE m ⟨x, hx⟩ ⟨y, hy⟩ := by
    intro x hx y hy
    by_contra hnot
    -- Let C1 be the component of x in compE; then C1 and N \ C1 both have ≥ 6 elements!
    let C1 : Finset R := (nbrs adj p).filter fun z =>
      ∃ hz : z ∈ nbrs adj p, ∃ m, Walk compE m ⟨x, hx⟩ ⟨z, hz⟩
    let C2 : Finset R := (nbrs adj p) \ C1
    have hxC1 : x ∈ C1 := mem_filter.mpr ⟨hx, hx, 0, Walk.nil _⟩
    have hyC2 : y ∈ C2 := mem_sdiff.mpr ⟨hy, fun hc => hnot (mem_filter.mp hc).2.2⟩
    -- Every vertex in C1 has all its ≥ 3 compE-neighbors in C1, and similarly for C2.
    have hcomp_closed1 : ∀ a ∈ C1, ∀ b ∈ nbrs adj p, b ≠ a → ¬ adj a b → b ∈ C1 := by
      intro a ha b hb hba hna
      obtain ⟨haN, m, wm⟩ := (mem_filter.mp ha).2
      refine mem_filter.mpr ⟨hb, hb, m + 1, wm.append (Walk.cons ⟨fun e => hba (congrArg Subtype.val e).symm, hna⟩ (Walk.nil _))⟩
    have hcomp_closed2 : ∀ a ∈ C2, ∀ b ∈ nbrs adj p, b ≠ a → ¬ adj a b → b ∈ C2 := by
      intro a ha b hb hba hna
      have ⟨haN, ha_not⟩ := mem_sdiff.mp ha
      refine mem_sdiff.mpr ⟨hb, fun hb1 => ha_not ?_⟩
      exact hcomp_closed1 b hb1 a haN hba.symm (fun h => hna (hsym h))
    -- Pick an edge (a, b) in compE inside C1 (a = x, b some compE-neighbor of x).
    have hxnbrs := hmin_comp x hx
    obtain ⟨b, hb⟩ := card_pos.mp (by omega : 0 < ((nbrs adj p).filter fun z => z ≠ x ∧ ¬ adj x z).card)
    have ⟨hbN, hbx, hnxb⟩ := mem_filter.mp hb
    -- Every vertex of C2 is adjacent in H to BOTH x and b!
    have hC2_size : 6 ≤ C2.card := by
      have hynbrs := hmin_comp y hy
      obtain ⟨y', hy'⟩ := card_pos.mp (by omega : 0 < ((nbrs adj p).filter fun z => z ≠ y ∧ ¬ adj y z).card)
      have ⟨hy'N, hy'y, hnyy'⟩ := mem_filter.mp hy'
      have hy'C2 : y' ∈ C2 := hcomp_closed2 y hyC2 y' hy'N hy'y hnyy'
      let Ny := (nbrs adj p).filter fun z => z ≠ y ∧ ¬ adj y z
      let Ny' := (nbrs adj p).filter fun z => z ≠ y' ∧ ¬ adj y' z
      -- Ny and Ny' are disjoint because compE is bipartite (y and y' have opposite colors!).
      have hdisj : Disjoint Ny Ny' := by
        apply Finset.disjoint_left.mpr
        intro z hz1 hz2
        have ⟨hzN, hzy, hnyz⟩ := mem_filter.mp hz1
        have ⟨_, hzy', hny'z⟩ := mem_filter.mp hz2
        have hc1 := hcolN ⟨y, hy⟩ ⟨y', hy'N⟩ ⟨fun e => hy'y (congrArg Subtype.val e).symm, hnyy'⟩
        have hc2 := hcolN ⟨y, hy⟩ ⟨z, hzN⟩ ⟨fun e => hzy (congrArg Subtype.val e).symm, hnyz⟩
        have hc3 := hcolN ⟨y', hy'N⟩ ⟨z, hzN⟩ ⟨fun e => hzy' (congrArg Subtype.val e).symm, hny'z⟩
        have hbool3 : ∀ a b c : Bool, a ≠ b → a ≠ c → b ≠ c → False := by decide
        exact hbool3 _ _ _ hc1 hc2 hc3
      have hsub : Ny ∪ Ny' ⊆ C2 := union_subset
        (fun z hz => by
          have ⟨hzN, hzy, hnyz⟩ := mem_filter.mp hz
          exact hcomp_closed2 y hyC2 z hzN hzy hnyz)
        (fun z hz => by
          have ⟨hzN, hzy', hny'z⟩ := mem_filter.mp hz
          exact hcomp_closed2 y' hy'C2 z hzN hzy' hny'z)
      have hc := card_le_card hsub
      rw [card_union_of_disjoint hdisj] at hc
      have h1 : 3 ≤ Ny.card := hmin_comp y hy
      have h2 : 3 ≤ Ny'.card := hmin_comp y' hy'N
      omega
    have hC2_common : C2 ⊆ nbrs adj x ∩ nbrs adj b := by
      intro z hz
      have ⟨hzN, hz_not⟩ := mem_sdiff.mp hz
      have hzx : z ≠ x := fun e => hz_not (e ▸ hxC1)
      have hbC1 : b ∈ C1 := hcomp_closed1 x hxC1 b hbN hbx hnxb
      have hzb : z ≠ b := fun e => hz_not (e ▸ hbC1)
      have hax : adj x z := by
        by_contra hna; exact hz_not (hcomp_closed1 x hxC1 z hzN hzx hna)
      have hab : adj b z := by
        by_contra hna; exact hz_not (hcomp_closed1 b hbC1 z hzN hzb hna)
      exact mem_inter.mpr ⟨mem_filter.mpr ⟨mem_univ _, hax⟩, mem_filter.mpr ⟨mem_univ _, hab⟩⟩
    have hc := card_le_card hC2_common
    have h4 := hcomm_nonadj x b hbx.symm hnxb
    omega
  refine ⟨col, ?_, hmin_comp, fun x hx y hy => hconn x hx y hy⟩
  intro x hx y hy hxy hna
  dsimp [col]
  rw [dif_pos hx, dif_pos hy]
  exact hcolN ⟨x, hx⟩ ⟨y, hy⟩ ⟨fun e => hxy (congrArg Subtype.val e), hna⟩

/-- Step 4: Clique consistency across every edge `p ∼ q`. If `N(p) = A_p ⊔ B_p` and
`N(q) = A_q ⊔ B_q` are clique partitions with min complement degree `≥ 3`, and `q ∈ A_p`, `p ∈ A_q`,
then `insert p A_p = insert q A_q`. -/
theorem clique_consistency
    (u : R → E → ℝ) (adj : R → R → Prop) [DecidableRel adj]
    (hnorm : ∀ p, dot (u p) (u p) = 2)
    (hgram : ∀ p q, p ≠ q → dot (u p) (u q) = 0 ∨ dot (u p) (u q) = 1)
    (hadj : ∀ p q, adj p q ↔ p ≠ q ∧ dot (u p) (u q) = 1)
    (hdeg : ∀ p, 16 ≤ (nbrs adj p).card)
    (hcomm_nonadj : ∀ p q, p ≠ q → ¬ adj p q → (nbrs adj p ∩ nbrs adj q).card ≤ 4)
    {p q : R} (hpq : adj p q)
    (Ap Bp Aq Bq : Finset R)
    (hp_part : Ap ∪ Bp = nbrs adj p) (hp_disj : Disjoint Ap Bp)
    (hp_clA : ∀ a ∈ Ap, ∀ b ∈ Ap, a ≠ b → adj a b)
    (hp_clB : ∀ a ∈ Bp, ∀ b ∈ Bp, a ≠ b → adj a b)
    (hp_min : ∀ x ∈ nbrs adj p, 3 ≤ ((nbrs adj p).filter fun y => y ≠ x ∧ ¬ adj x y).card)
    (hq_part : Aq ∪ Bq = nbrs adj q) (hq_disj : Disjoint Aq Bq)
    (hq_clA : ∀ a ∈ Aq, ∀ b ∈ Aq, a ≠ b → adj a b)
    (hq_clB : ∀ a ∈ Bq, ∀ b ∈ Bq, a ≠ b → adj a b)
    (hq_min : ∀ x ∈ nbrs adj q, 3 ≤ ((nbrs adj q).filter fun y => y ≠ x ∧ ¬ adj x y).card)
    (hq_in : q ∈ Ap) (hp_in : p ∈ Aq) :
    insert p Ap = insert q Aq := by
  have hsym := adj_symm_of_gram u adj hadj
  have hirr := adj_irrefl_of_gram u adj hadj
  -- Half-inclusion: Ap \ {q} ⊆ Aq \ {p}.
  have hhalf : ∀ {p q : R} (hpq : adj p q)
      (Ap Bp Aq Bq : Finset R),
      Ap ∪ Bp = nbrs adj p → Disjoint Ap Bp →
      (∀ a ∈ Ap, ∀ b ∈ Ap, a ≠ b → adj a b) →
      (∀ a ∈ Bp, ∀ b ∈ Bp, a ≠ b → adj a b) →
      (∀ x ∈ nbrs adj p, 3 ≤ ((nbrs adj p).filter fun y => y ≠ x ∧ ¬ adj x y).card) →
      Aq ∪ Bq = nbrs adj q → Disjoint Aq Bq →
      (∀ a ∈ Aq, ∀ b ∈ Aq, a ≠ b → adj a b) →
      (∀ a ∈ Bq, ∀ b ∈ Bq, a ≠ b → adj a b) →
      (∀ x ∈ nbrs adj q, 3 ≤ ((nbrs adj q).filter fun y => y ≠ x ∧ ¬ adj x y).card) →
      q ∈ Ap → p ∈ Aq → ∀ z ∈ Ap, z ≠ q → z ∈ Aq := by
    intro p q hpq Ap Bp Aq Bq hp_part hp_disj hp_clA hp_clB hp_min
      hq_part hq_disj hq_clA hq_clB hq_min hq_in hp_in z hzA hzq
    have hz_in_Nq : z ∈ nbrs adj q := mem_filter.mpr ⟨mem_univ _, hsym (hp_clA z hzA q hq_in hzq)⟩
    have hz_union : z ∈ Aq ∪ Bq := by rwa [hq_part]
    rcases mem_union.mp hz_union with hzAq | hzBq
    · exact hzAq
    · exfalso
      have hzp : z ≠ p := by
        intro e; have h := (mem_filter.mp (hp_part ▸ mem_union_left _ hzA)).2
        rw [e] at h; exact hirr p h
      -- Non-neighbors of z in N(q) all lie in Aq \ {p} and in Bp!
      let W := (nbrs adj q).filter fun w => w ≠ z ∧ ¬ adj z w
      have hW_ge3 : 3 ≤ W.card := hq_min z hz_in_Nq
      have hW_sub_Aq : W ⊆ Aq.erase p := by
        intro w hw
        have ⟨hwNq, hwz, hnzw⟩ := mem_filter.mp hw
        have hwp : w ≠ p := fun e => hnzw (e ▸ hsym (mem_filter.mp (hp_part ▸ mem_union_left _ hzA)).2)
        have hwAq : w ∈ Aq := by
          rcases mem_union.mp (hq_part ▸ hwNq) with h | h
          · exact h
          · exact absurd (hq_clB z hzBq w h (Ne.symm hwz)) hnzw
        exact mem_erase.mpr ⟨hwp, hwAq⟩
      have hW_sub_Bp : W ⊆ Bp := by
        intro w hw
        have ⟨hwp, hwAq⟩ := mem_erase.mp (hW_sub_Aq hw)
        have ⟨_, hwz, hnzw⟩ := mem_filter.mp hw
        have hpw : adj p w := hq_clA p hp_in w hwAq (Ne.symm hwp)
        have hwNp : w ∈ nbrs adj p := mem_filter.mpr ⟨mem_univ _, hpw⟩
        rcases mem_union.mp (hp_part ▸ hwNp) with hwAp | hwBp
        · exact absurd (hp_clA z hzA w hwAp (Ne.symm hwz)) hnzw
        · exact hwBp
      -- Non-neighbors of p in N(q) all lie in Bq \ {z}!
      let V := (nbrs adj q).filter fun v => v ≠ p ∧ ¬ adj p v
      have hV_ge3 : 3 ≤ V.card := hq_min p (hq_part ▸ mem_union_left _ hp_in)
      have hV_sub_Bq : V ⊆ Bq.erase z := by
        intro v hv
        have ⟨hvNq, hvp, hnpv⟩ := mem_filter.mp hv
        have hvz : v ≠ z := fun e => hnpv (e ▸ (mem_filter.mp (hp_part ▸ mem_union_left _ hzA)).2)
        have hvBq : v ∈ Bq := by
          rcases mem_union.mp (hq_part ▸ hvNq) with h | h
          · exact absurd (hq_clA p hp_in v h (Ne.symm hvp)) hnpv
          · exact h
        exact mem_erase.mpr ⟨hvz, hvBq⟩
      obtain ⟨w1, hw1⟩ := card_pos.mp (by omega : 0 < W.card)
      obtain ⟨v1, hv1⟩ := card_pos.mp (by omega : 0 < V.card)
      have ⟨hw1Nq, hw1z, hnzw1⟩ := mem_filter.mp hw1
      have ⟨hw1p, hw1Aq⟩ := mem_erase.mp (hW_sub_Aq hw1)
      have ⟨hv1Nq, hv1p, hnpv1⟩ := mem_filter.mp hv1
      have ⟨hv1z, hv1Bq⟩ := mem_erase.mp (hV_sub_Bq hv1)
      -- Every x ∈ (Ap.erase q).erase z lies in Aq (common nbr of z ≁ w1) or Bq (common nbr of p ≁ v1).
      let Rem := (Ap.erase q).erase z
      have hRem_split : Rem ⊆
          (((nbrs adj z ∩ nbrs adj w1).erase p).erase q) ∪
          (((nbrs adj p ∩ nbrs adj v1).erase q).erase z) := by
        intro x hx
        have ⟨hxz, hx1⟩ := mem_erase.mp hx
        have ⟨hxq, hxAp⟩ := mem_erase.mp hx1
        have hxp : x ≠ p := by
          intro e; have h := (mem_filter.mp (hp_part ▸ mem_union_left _ hxAp)).2
          rw [e] at h; exact hirr p h
        have hxNq : x ∈ nbrs adj q := mem_filter.mpr ⟨mem_univ _, hsym (hp_clA x hxAp q hq_in hxq)⟩
        rcases mem_union.mp (hq_part ▸ hxNq) with hxAq | hxBq
        · refine mem_union_left _ ?_
          have hxw1 : x ≠ w1 := fun e =>
            Finset.disjoint_left.mp hp_disj hxAp (e ▸ hW_sub_Bp hw1)
          refine mem_erase.mpr ⟨hxq, mem_erase.mpr ⟨hxp, mem_inter.mpr
            ⟨mem_filter.mpr ⟨mem_univ _, hp_clA z hzA x hxAp (Ne.symm hxz)⟩,
             mem_filter.mpr ⟨mem_univ _, hq_clA w1 hw1Aq x hxAq (Ne.symm hxw1)⟩⟩⟩⟩
        · refine mem_union_right _ ?_
          have hxv1 : x ≠ v1 := fun e => hnpv1 (e ▸ (mem_filter.mp (hp_part ▸ mem_union_left _ hxAp)).2)
          refine mem_erase.mpr ⟨hxz, mem_erase.mpr ⟨hxq, mem_inter.mpr
            ⟨mem_filter.mpr ⟨mem_univ _, (mem_filter.mp (hp_part ▸ mem_union_left _ hxAp)).2⟩,
             mem_filter.mpr ⟨mem_univ _, hq_clB v1 hv1Bq x hxBq (Ne.symm hxv1)⟩⟩⟩⟩
      have hzw1_le2 : (((nbrs adj z ∩ nbrs adj w1).erase p).erase q).card ≤ 2 := by
        have hp_in' : p ∈ nbrs adj z ∩ nbrs adj w1 :=
          mem_inter.mpr ⟨mem_filter.mpr ⟨mem_univ _, hsym (mem_filter.mp (hp_part ▸ mem_union_left _ hzA)).2⟩,
            mem_filter.mpr ⟨mem_univ _, hq_clA w1 hw1Aq p hp_in hw1p⟩⟩
        have hq_in' : q ∈ (nbrs adj z ∩ nbrs adj w1).erase p :=
          mem_erase.mpr ⟨fun e => hirr p (e ▸ hpq),
            mem_inter.mpr ⟨mem_filter.mpr ⟨mem_univ _, hsym (mem_filter.mp hz_in_Nq).2⟩,
              mem_filter.mpr ⟨mem_univ _, hsym (mem_filter.mp hw1Nq).2⟩⟩⟩
        rw [card_erase_of_mem hq_in', card_erase_of_mem hp_in']
        have h4 := hcomm_nonadj z w1 (Ne.symm hw1z) hnzw1
        omega
      have hpv1_le2 : (((nbrs adj p ∩ nbrs adj v1).erase q).erase z).card ≤ 2 := by
        have hq_in' : q ∈ nbrs adj p ∩ nbrs adj v1 :=
          mem_inter.mpr ⟨mem_filter.mpr ⟨mem_univ _, hpq⟩,
            mem_filter.mpr ⟨mem_univ _, hsym (mem_filter.mp hv1Nq).2⟩⟩
        have hz_in' : z ∈ (nbrs adj p ∩ nbrs adj v1).erase q :=
          mem_erase.mpr ⟨hzq,
            mem_inter.mpr ⟨mem_filter.mpr ⟨mem_univ _, (mem_filter.mp (hp_part ▸ mem_union_left _ hzA)).2⟩,
              mem_filter.mpr ⟨mem_univ _, hq_clB v1 hv1Bq z hzBq hv1z⟩⟩⟩
        rw [card_erase_of_mem hz_in', card_erase_of_mem hq_in']
        have h4 := hcomm_nonadj p v1 (Ne.symm hv1p) hnpv1
        omega
      have hAp_le6 : Ap.card ≤ 6 := by
        have hc := (card_le_card hRem_split).trans (card_union_le _ _)
        dsimp [Rem] at hc
        rw [card_erase_of_mem (mem_erase.mpr ⟨hzq, hzA⟩), card_erase_of_mem hq_in] at hc
        have h2 : 2 ≤ Ap.card := by
          have : ({q, z} : Finset R) ⊆ Ap := insert_subset_iff.mpr ⟨hq_in, singleton_subset_iff.mpr hzA⟩
          have := card_le_card this
          rw [card_pair (Ne.symm hzq)] at this; exact this
        omega
      -- Now C = insert p Bp is a clique of size ≥ 11 ≥ 9 not containing q, and q misses ≥ 3 of Bp.
      have hBp_ge10 : 10 ≤ Bp.card := by
        have hsum : Ap.card + Bp.card = (nbrs adj p).card := by
          rw [← card_union_of_disjoint hp_disj, hp_part]
        have := hdeg p; omega
      let C := insert p Bp
      have hp_not_Bp : p ∉ Bp := fun h => hirr p (mem_filter.mp (hp_part ▸ mem_union_right _ h)).2
      have hC_card : 9 ≤ C.card := by rw [card_insert_of_notMem hp_not_Bp]; omega
      have hC_clique : ∀ a ∈ C, ∀ b ∈ C, a ≠ b → adj a b := by
        intro a ha b hb hab
        rcases mem_insert.mp ha with rfl | haB <;> rcases mem_insert.mp hb with rfl | hbB
        · exact absurd rfl hab
        · exact (mem_filter.mp (hp_part ▸ mem_union_right _ hbB)).2
        · exact hsym (mem_filter.mp (hp_part ▸ mem_union_right _ haB)).2
        · exact hp_clB a haB b hbB hab
      have hq_not_C : q ∉ C := by
        intro hqC
        rcases mem_insert.mp hqC with hqp | hqB
        · exact hirr p (hqp ▸ hpq)
        · exact Finset.disjoint_left.mp hp_disj hq_in hqB
      have hq_notall : ∃ u0 ∈ C, ¬ adj q u0 := by
        have hq_min3 := hp_min q (hp_part ▸ mem_union_left _ hq_in)
        obtain ⟨u0, hu0⟩ := card_pos.mp (by omega : 0 < ((nbrs adj p).filter fun y => y ≠ q ∧ ¬ adj q y).card)
        have ⟨hu0Np, hu0q, hnq⟩ := mem_filter.mp hu0
        have hu0B : u0 ∈ Bp := by
          rcases mem_union.mp (hp_part ▸ hu0Np) with hu0A | hu0B
          · exact absurd (hp_clA q hq_in u0 hu0A (Ne.symm hu0q)) hnq
          · exact hu0B
        exact ⟨u0, mem_insert_of_mem hu0B, hnq⟩
      have hle2 := det_clique_outside u adj hnorm hgram hadj hcomm_nonadj C hC_clique hC_card q hq_not_C hq_notall
      -- Contradiction: insert p W ⊆ nbrs adj q ∩ C has size ≥ 4!
      have hW_in : insert p W ⊆ nbrs adj q ∩ C := by
        intro x hx
        rcases mem_insert.mp hx with hxp | hxW
        · rw [hxp]
          exact mem_inter.mpr ⟨mem_filter.mpr ⟨mem_univ _, hsym hpq⟩, mem_insert_self p Bp⟩
        · exact mem_inter.mpr ⟨(mem_filter.mp hxW).1, mem_insert_of_mem (hW_sub_Bp hxW)⟩
      have hp_not_W : p ∉ W := fun hpW => (mem_erase.mp (hW_sub_Aq hpW)).1 rfl
      have hge4 : 4 ≤ (nbrs adj q ∩ C).card := by
        have hc := card_le_card hW_in
        rw [card_insert_of_notMem hp_not_W] at hc
        omega
      omega
  ext z
  simp only [mem_insert]
  constructor
  · rintro (rfl | hzA)
    · exact Or.inr hp_in
    · by_cases hzq : z = q
      · exact Or.inl hzq
      · exact Or.inr (hhalf hpq Ap Bp Aq Bq hp_part hp_disj hp_clA hp_clB hp_min
          hq_part hq_disj hq_clA hq_clB hq_min hq_in hp_in z hzA hzq)
  · rintro (rfl | hzA)
    · exact Or.inr hq_in
    · by_cases hzp : z = p
      · exact Or.inl hzp
      · exact Or.inr (hhalf (hsym hpq) Aq Bq Ap Bp hq_part hq_disj hq_clA hq_clB hq_min
          hp_part hp_disj hp_clA hp_clB hp_min hp_in hq_in z hzA hzp)

/-- Step 5: Complete elementary edge-representation theorem.
Produces a finite simple graph `G` on `V` (the set of star cliques) with endpoint maps
`e1, e2 : R → V` such that `e1 p ≠ e2 p`, every edge satisfies `deg_G(i) + deg_G(j) ≥ 18`,
`G` is connected (when `H` is connected), and the edge vectors `w p = e_{e1 p} + e_{e2 p}`
have the EXACT SAME Gram matrix as `u`. -/
theorem exists_edge_rep
    (u : R → E → ℝ) (adj : R → R → Prop) [DecidableRel adj]
    (hnorm : ∀ p, dot (u p) (u p) = 2)
    (hgram : ∀ p q, p ≠ q → dot (u p) (u q) = 0 ∨ dot (u p) (u q) = 1)
    (hadj : ∀ p q, adj p q ↔ p ≠ q ∧ dot (u p) (u q) = 1)
    (hdeg : ∀ p, 16 ≤ (nbrs adj p).card)
    (hcomm_adj : ∀ p q, adj p q → (nbrs adj p ∩ nbrs adj q).card ≤ 12)
    (hcomm_nonadj : ∀ p q, p ≠ q → ¬ adj p q → (nbrs adj p ∩ nbrs adj q).card ≤ 4)
    (hconnH : ∀ p q : R, ∃ m, Walk adj m p q) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (e1 e2 : R → V),
      (∀ p, e1 p ≠ e2 p) ∧
      (∀ p q : R, ({e1 p, e2 p} : Finset V) = {e1 q, e2 q} ↔ p = q) ∧
      (∀ p q : R, dot (u p) (u q) =
        dot (fun v : V => (if v = e1 p then (1 : ℝ) else 0) + (if v = e2 p then 1 else 0))
            (fun v : V => (if v = e1 q then (1 : ℝ) else 0) + (if v = e2 q then 1 else 0))) ∧
      (∀ v : V, ∃ p : R, e1 p = v ∨ e2 p = v) ∧
      (∀ p : R,
        18 ≤ (univ.filter fun q : R => e1 q = e1 p ∨ e2 q = e1 p).card +
             (univ.filter fun q : R => e1 q = e2 p ∨ e2 q = e2 p).card) ∧
      (∀ v1 v2 : V, ∃ m, Walk (fun a b : V => ∃ p : R, (e1 p = a ∧ e2 p = b) ∨ (e1 p = b ∧ e2 p = a)) m v1 v2) := by
  classical
  have hsym := adj_symm_of_gram u adj hadj
  have hirr := adj_irrefl_of_gram u adj hadj
  -- For each p, choose a valid 2-coloring of complement(nbrs adj p).
  have hchoice : ∀ p : R, ∃ col : R → Bool,
      (∀ x ∈ nbrs adj p, ∀ y ∈ nbrs adj p, x ≠ y → ¬ adj x y → col x ≠ col y) ∧
      (∀ x ∈ nbrs adj p, 3 ≤ ((nbrs adj p).filter fun y => y ≠ x ∧ ¬ adj x y).card) := by
    intro p
    obtain ⟨col, h1, h2, _⟩ := nbrhd_bipartite_connected u adj hnorm hgram hadj hdeg hcomm_adj hcomm_nonadj p
    exact ⟨col, h1, h2⟩
  let col : R → R → Bool := fun p => (hchoice p).choose
  have hcol_valid : ∀ p, ∀ x ∈ nbrs adj p, ∀ y ∈ nbrs adj p, x ≠ y → ¬ adj x y → col p x ≠ col p y :=
    fun p => (hchoice p).choose_spec.1
  have hcol_min : ∀ p, ∀ x ∈ nbrs adj p, 3 ≤ ((nbrs adj p).filter fun y => y ≠ x ∧ ¬ adj x y).card :=
    fun p => (hchoice p).choose_spec.2
  let A : R → Finset R := fun p => (nbrs adj p).filter fun y => col p y = false
  let B : R → Finset R := fun p => (nbrs adj p).filter fun y => col p y = true
  have hpart : ∀ p, A p ∪ B p = nbrs adj p := by
    intro p; ext y; simp only [A, B, mem_union, mem_filter]
    cases col p y <;> simp
  have hdisj : ∀ p, Disjoint (A p) (B p) := by
    intro p; apply Finset.disjoint_left.mpr; intro y h1 h2
    have c1 := (mem_filter.mp h1).2; have c2 := (mem_filter.mp h2).2
    rw [c1] at c2; exact Bool.false_ne_true c2
  have hclA : ∀ p, ∀ a ∈ A p, ∀ b ∈ A p, a ≠ b → adj a b := by
    intro p a ha b hb hab
    by_contra hna
    have := hcol_valid p a (mem_filter.mp ha).1 b (mem_filter.mp hb).1 hab hna
    rw [(mem_filter.mp ha).2, (mem_filter.mp hb).2] at this; exact this rfl
  have hclB : ∀ p, ∀ a ∈ B p, ∀ b ∈ B p, a ≠ b → adj a b := by
    intro p a ha b hb hab
    by_contra hna
    have := hcol_valid p a (mem_filter.mp ha).1 b (mem_filter.mp hb).1 hab hna
    rw [(mem_filter.mp ha).2, (mem_filter.mp hb).2] at this; exact this rfl
  let C0 : R → Finset R := fun p => insert p (A p)
  let C1 : R → Finset R := fun p => insert p (B p)
  have hp_not_A : ∀ p, p ∉ A p := fun p h => hirr p (mem_filter.mp (mem_filter.mp h).1).2
  have hp_not_B : ∀ p, p ∉ B p := fun p h => hirr p (mem_filter.mp (mem_filter.mp h).1).2
  have hA_nonempty : ∀ p, (A p).Nonempty := by
    intro p
    obtain ⟨x, hx⟩ := card_pos.mp (by have := hdeg p; omega : 0 < (nbrs adj p).card)
    rcases mem_union.mp (hpart p ▸ hx) with hxA | hxB
    · exact ⟨x, hxA⟩
    · have hm := hcol_min p x hx
      obtain ⟨y, hy⟩ := card_pos.mp (by omega : 0 < ((nbrs adj p).filter fun y => y ≠ x ∧ ¬ adj x y).card)
      have ⟨hyN, hyx, hnxy⟩ := mem_filter.mp hy
      rcases mem_union.mp (hpart p ▸ hyN) with hyA | hyB
      · exact ⟨y, hyA⟩
      · exact absurd (hclB p x hxB y hyB (Ne.symm hyx)) hnxy
  have hC0_ne_C1 : ∀ p, C0 p ≠ C1 p := by
    intro p heq
    obtain ⟨x, hxA⟩ := hA_nonempty p
    have hxC1 : x ∈ C1 p := heq ▸ mem_insert_of_mem hxA
    rcases mem_insert.mp hxC1 with hxp | hxB
    · exact hp_not_A p (hxp ▸ hxA)
    · exact Finset.disjoint_left.mp (hdisj p) hxA hxB
  -- Consistency: if q ∈ A p, then C0 p = C0 q or C0 p = C1 q (and similarly for B p).
  have hcons0 : ∀ p q, q ∈ A p → C0 p = C0 q ∨ C0 p = C1 q := by
    intro p q hqA
    have hpq : adj p q := (mem_filter.mp (mem_filter.mp hqA).1).2
    have hpNq : p ∈ nbrs adj q := mem_filter.mpr ⟨mem_univ _, hsym hpq⟩
    rcases mem_union.mp (hpart q ▸ hpNq) with hpAq | hpBq
    · left
      exact clique_consistency u adj hnorm hgram hadj hdeg hcomm_nonadj hpq
        (A p) (B p) (A q) (B q) (hpart p) (hdisj p) (hclA p) (hclB p) (hcol_min p)
        (hpart q) (hdisj q) (hclA q) (hclB q) (hcol_min q) hqA hpAq
    · right
      exact clique_consistency u adj hnorm hgram hadj hdeg hcomm_nonadj hpq
        (A p) (B p) (B q) (A q) (hpart p) (hdisj p) (hclA p) (hclB p) (hcol_min p)
        (by rw [union_comm, hpart q]) (hdisj q).symm (hclB q) (hclA q) (hcol_min q) hqA hpBq
  have hcons1 : ∀ p q, q ∈ B p → C1 p = C0 q ∨ C1 p = C1 q := by
    intro p q hqB
    have hpq : adj p q := (mem_filter.mp (mem_filter.mp hqB).1).2
    have hpNq : p ∈ nbrs adj q := mem_filter.mpr ⟨mem_univ _, hsym hpq⟩
    rcases mem_union.mp (hpart q ▸ hpNq) with hpAq | hpBq
    · left
      exact clique_consistency u adj hnorm hgram hadj hdeg hcomm_nonadj hpq
        (B p) (A p) (A q) (B q) (by rw [union_comm, hpart p]) (hdisj p).symm (hclB p) (hclA p) (hcol_min p)
        (hpart q) (hdisj q) (hclA q) (hclB q) (hcol_min q) hqB hpAq
    · right
      exact clique_consistency u adj hnorm hgram hadj hdeg hcomm_nonadj hpq
        (B p) (A p) (B q) (A q) (by rw [union_comm, hpart p]) (hdisj p).symm (hclB p) (hclA p) (hcol_min p)
        (by rw [union_comm, hpart q]) (hdisj q).symm (hclB q) (hclA q) (hcol_min q) hqB hpBq
  -- Define V as Fin (Cliques.card) so V : Type (universe 0)!
  let Cliques : Finset (Finset R) := univ.image C0 ∪ univ.image C1
  let eEquiv : { c : Finset R // c ∈ Cliques } ≃ Fin Cliques.card :=
    Fintype.equivFinOfCardEq (Fintype.card_coe Cliques)
  let V := Fin Cliques.card
  let toV : ∀ c : Finset R, c ∈ Cliques → V := fun c hc => eEquiv ⟨c, hc⟩
  have hC0_mem : ∀ p, C0 p ∈ Cliques := fun p => mem_union_left _ (mem_image_of_mem _ (mem_univ p))
  have hC1_mem : ∀ p, C1 p ∈ Cliques := fun p => mem_union_right _ (mem_image_of_mem _ (mem_univ p))
  let e1 : R → V := fun p => toV (C0 p) (hC0_mem p)
  let e2 : R → V := fun p => toV (C1 p) (hC1_mem p)
  have he1_eq : ∀ p c hc, e1 p = toV c hc ↔ C0 p = c := fun p c hc => by
    dsimp [e1, toV]
    rw [Equiv.apply_eq_iff_eq, Subtype.mk.injEq]
  have he2_eq : ∀ p c hc, e2 p = toV c hc ↔ C1 p = c := fun p c hc => by
    dsimp [e2, toV]
    rw [Equiv.apply_eq_iff_eq, Subtype.mk.injEq]
  -- Membership characterization: q ∈ c ↔ e1 q = toV c hc ∨ e2 q = toV c hc!
  have hmem_iff : ∀ (q : R) (c : Finset R) (hc : c ∈ Cliques),
      q ∈ c ↔ e1 q = toV c hc ∨ e2 q = toV c hc := by
    intro q c hc
    rw [he1_eq, he2_eq]
    constructor
    · intro hqc
      rcases mem_union.mp hc with hc0 | hc1
      · obtain ⟨p, _, rfl⟩ := mem_image.mp hc0
        rcases mem_insert.mp hqc with rfl | hqA
        · exact Or.inl rfl
        · rcases hcons0 p q hqA with h | h <;> [exact Or.inl h.symm; exact Or.inr h.symm]
      · obtain ⟨p, _, rfl⟩ := mem_image.mp hc1
        rcases mem_insert.mp hqc with rfl | hqB
        · exact Or.inr rfl
        · rcases hcons1 p q hqB with h | h <;> [exact Or.inl h.symm; exact Or.inr h.symm]
    · rintro (h | h)
      · rw [← h]; exact mem_insert_self q (A q)
      · rw [← h]; exact mem_insert_self q (B q)
  have he1_ne_e2 : ∀ p, e1 p ≠ e2 p := fun p h => hC0_ne_C1 p ((he1_eq p (C1 p) (hC1_mem p)).mp h)
  have hC0_C1_inter : ∀ p, C0 p ∩ C1 p = {p} := by
    intro p; ext x; simp only [C0, C1, mem_inter, mem_insert, mem_singleton]
    constructor
    · rintro ⟨hxp | hxA, hxp' | hxB⟩
      · exact hxp
      · exact hxp
      · exact hxp'
      · exact absurd hxB (Finset.disjoint_left.mp (hdisj p) hxA)
    · rintro rfl; exact ⟨Or.inl rfl, Or.inl rfl⟩
  -- Unordered pair uniqueness: {e1 p, e2 p} = {e1 q, e2 q} ↔ p = q.
  have hpair_uniq : ∀ p q : R, ({e1 p, e2 p} : Finset V) = {e1 q, e2 q} ↔ p = q := by
    intro p q
    constructor
    · intro h
      have h1 : e1 q ∈ ({e1 p, e2 p} : Finset V) := h ▸ mem_insert_self _ _
      have h2 : e2 q ∈ ({e1 p, e2 p} : Finset V) := h ▸ mem_insert_of_mem (mem_singleton_self _)
      have hq0 : q ∈ C0 p := by
        rw [hmem_iff q (C0 p) (hC0_mem p)]
        have : e1 p ∈ ({e1 q, e2 q} : Finset V) := h.symm ▸ mem_insert_self _ _
        simp only [mem_insert, mem_singleton] at this
        rcases this with h' | h'
        · exact Or.inl h'.symm
        · exact Or.inr h'.symm
      have hq1 : q ∈ C1 p := by
        rw [hmem_iff q (C1 p) (hC1_mem p)]
        have : e2 p ∈ ({e1 q, e2 q} : Finset V) := h.symm ▸ mem_insert_of_mem (mem_singleton_self _)
        simp only [mem_insert, mem_singleton] at this
        rcases this with h' | h'
        · exact Or.inl h'.symm
        · exact Or.inr h'.symm
      have hq_inter : q ∈ C0 p ∩ C1 p := mem_inter.mpr ⟨hq0, hq1⟩
      rw [hC0_C1_inter p, mem_singleton] at hq_inter
      exact hq_inter.symm
    · rintro rfl; rfl
  -- Exact Gram match.
  have hgram_match : ∀ p q : R, dot (u p) (u q) =
      dot (fun v : V => (if v = e1 p then (1 : ℝ) else 0) + (if v = e2 p then 1 else 0))
          (fun v : V => (if v = e1 q then (1 : ℝ) else 0) + (if v = e2 q then 1 else 0)) := by
    intro p q
    have hrhs : dot (fun v : V => (if v = e1 p then (1 : ℝ) else 0) + (if v = e2 p then 1 else 0))
        (fun v : V => (if v = e1 q then (1 : ℝ) else 0) + (if v = e2 q then 1 else 0)) =
        (if e1 p = e1 q then (1 : ℝ) else 0) + (if e1 p = e2 q then 1 else 0) +
        (if e2 p = e1 q then 1 else 0) + (if e2 p = e2 q then 1 else 0) := by
      simp only [dot, add_mul, mul_add, sum_add_distrib]
      have hite (a b : V) :
          ∑ v : V, (if v = a then (1 : ℝ) else 0) * (if v = b then 1 else 0) =
            if a = b then 1 else 0 := by
        rw [sum_eq_single a]
        · simp
        · intro v _ hva; simp [hva]
        · intro h; exact absurd (mem_univ a) h
      simp_rw [hite]; ring
    rw [hrhs]
    by_cases hpq_eq : p = q
    · subst hpq_eq
      rw [hnorm p, if_pos rfl, if_neg (he1_ne_e2 p), if_neg (Ne.symm (he1_ne_e2 p)), if_pos rfl]
      ring
    · by_cases hpq_adj : adj p q
      · rw [((hadj p q).mp hpq_adj).2]
        have hqNp : q ∈ nbrs adj p := mem_filter.mpr ⟨mem_univ _, hpq_adj⟩
        rcases mem_union.mp (hpart p ▸ hqNp) with hqA | hqB
        · have hq_in0 : q ∈ C0 p := mem_insert_of_mem hqA
          have hq_not1 : q ∉ C1 p := by
            intro h; rcases mem_insert.mp h with rfl | hqB
            · exact hpq_eq rfl
            · exact Finset.disjoint_left.mp (hdisj p) hqA hqB
          have h1 := (hmem_iff q (C0 p) (hC0_mem p)).mp hq_in0
          have h2 : ¬ (e1 q = e2 p ∨ e2 q = e2 p) := fun h => hq_not1 ((hmem_iff q (C1 p) (hC1_mem p)).mpr h)
          push Not at h2
          rcases h1 with h11 | h12
          · have h12' : e1 p ≠ e2 q := fun e => he1_ne_e2 q (h11.trans e)
            rw [if_pos h11.symm, if_neg h12', if_neg (Ne.symm h2.1), if_neg (Ne.symm h2.2)]; ring
          · have h11' : e1 p ≠ e1 q := fun e => he1_ne_e2 q (e.symm.trans h12.symm)
            rw [if_neg h11', if_pos h12.symm, if_neg (Ne.symm h2.1), if_neg (Ne.symm h2.2)]; ring
        · have hq_in1 : q ∈ C1 p := mem_insert_of_mem hqB
          have hq_not0 : q ∉ C0 p := by
            intro h; rcases mem_insert.mp h with rfl | hqA
            · exact hpq_eq rfl
            · exact Finset.disjoint_left.mp (hdisj p) hqA hqB
          have h1 := (hmem_iff q (C1 p) (hC1_mem p)).mp hq_in1
          have h2 : ¬ (e1 q = e1 p ∨ e2 q = e1 p) := fun h => hq_not0 ((hmem_iff q (C0 p) (hC0_mem p)).mpr h)
          push Not at h2
          rcases h1 with h21 | h22
          · have h22' : e2 p ≠ e2 q := fun e => he1_ne_e2 q (h21.trans e)
            rw [if_neg (Ne.symm h2.1), if_neg (Ne.symm h2.2), if_pos h21.symm, if_neg h22']; ring
          · have h21' : e2 p ≠ e1 q := fun e => he1_ne_e2 q (e.symm.trans h22.symm)
            rw [if_neg (Ne.symm h2.1), if_neg (Ne.symm h2.2), if_neg h21', if_pos h22.symm]; ring
      · rw [dot_zero_of_not_adj u adj hgram hadj hpq_eq hpq_adj]
        have hq_not0 : q ∉ C0 p := by
          intro h; rcases mem_insert.mp h with rfl | hqA
          · exact hpq_eq rfl
          · exact hpq_adj (mem_filter.mp (mem_filter.mp hqA).1).2
        have hq_not1 : q ∉ C1 p := by
          intro h; rcases mem_insert.mp h with rfl | hqB
          · exact hpq_eq rfl
          · exact hpq_adj (mem_filter.mp (mem_filter.mp hqB).1).2
        have h1 : ¬ (e1 q = e1 p ∨ e2 q = e1 p) := fun h => hq_not0 ((hmem_iff q (C0 p) (hC0_mem p)).mpr h)
        have h2 : ¬ (e1 q = e2 p ∨ e2 q = e2 p) := fun h => hq_not1 ((hmem_iff q (C1 p) (hC1_mem p)).mpr h)
        push Not at h1 h2
        rw [if_neg (Ne.symm h1.1), if_neg (Ne.symm h1.2), if_neg (Ne.symm h2.1), if_neg (Ne.symm h2.2)]
        ring
  -- Every v ∈ V is incident to some p ∈ R.
  have hnoniso : ∀ v : V, ∃ p : R, e1 p = v ∨ e2 p = v := by
    intro v
    obtain ⟨⟨c, hc⟩, rfl⟩ := eEquiv.surjective v
    rcases mem_union.mp hc with hc0 | hc1
    · obtain ⟨p, _, rfl⟩ := mem_image.mp hc0
      exact ⟨p, Or.inl rfl⟩
    · obtain ⟨p, _, rfl⟩ := mem_image.mp hc1
      exact ⟨p, Or.inr rfl⟩
  -- Endpoint degree sum ≥ 18.
  have hdeg_sum : ∀ p : R,
      18 ≤ (univ.filter fun q : R => e1 q = e1 p ∨ e2 q = e1 p).card +
           (univ.filter fun q : R => e1 q = e2 p ∨ e2 q = e2 p).card := by
    intro p
    have h1 : (univ.filter fun q : R => e1 q = e1 p ∨ e2 q = e1 p) = C0 p := by
      ext q; simp only [mem_filter, mem_univ, true_and]
      exact (hmem_iff q (C0 p) (hC0_mem p)).symm
    have h2 : (univ.filter fun q : R => e1 q = e2 p ∨ e2 q = e2 p) = C1 p := by
      ext q; simp only [mem_filter, mem_univ, true_and]
      exact (hmem_iff q (C1 p) (hC1_mem p)).symm
    rw [h1, h2, card_insert_of_notMem (hp_not_A p), card_insert_of_notMem (hp_not_B p)]
    have hsum : (A p).card + (B p).card = (nbrs adj p).card := by
      rw [← card_union_of_disjoint (hdisj p), hpart p]
    have := hdeg p
    omega
  -- Connectedness of G from connectedness of H.
  let adjG : V → V → Prop := fun a b => ∃ p : R, (e1 p = a ∧ e2 p = b) ∨ (e1 p = b ∧ e2 p = a)
  have hconnG : ∀ v1 v2 : V, ∃ m, Walk adjG m v1 v2 := by
    intro v1 v2
    obtain ⟨p1, hp1⟩ := hnoniso v1
    obtain ⟨p2, hp2⟩ := hnoniso v2
    obtain ⟨m, wm⟩ := hconnH p1 p2
    have hedge_step : ∀ {p q : R}, adj p q → ∃ k, Walk adjG k (e1 p) (e1 q) := by
      intro p q hpq
      -- Both e1 p and e2 p are connected by 1 step (via p), and {e1 p, e2 p} meets {e1 q, e2 q}.
      have hstep_p : Walk adjG 1 (e1 p) (e2 p) := Walk.cons ⟨p, Or.inl ⟨rfl, rfl⟩⟩ (Walk.nil _)
      have hstep_q : Walk adjG 1 (e2 q) (e1 q) := Walk.cons ⟨q, Or.inr ⟨rfl, rfl⟩⟩ (Walk.nil _)
      have hqNp : q ∈ nbrs adj p := mem_filter.mpr ⟨mem_univ _, hpq⟩
      rcases mem_union.mp (hpart p ▸ hqNp) with hqA | hqB
      · rcases (hmem_iff q (C0 p) (hC0_mem p)).mp (mem_insert_of_mem hqA) with h | h
        · change e1 q = e1 p at h
          exact ⟨0, by rw [h]; exact Walk.nil _⟩
        · change e2 q = e1 p at h
          exact ⟨1, by rw [← h]; exact hstep_q⟩
      · rcases (hmem_iff q (C1 p) (hC1_mem p)).mp (mem_insert_of_mem hqB) with h | h
        · change e1 q = e2 p at h
          exact ⟨1, by rw [h]; exact hstep_p⟩
        · change e2 q = e2 p at h
          exact ⟨2, by rw [← h] at hstep_p; exact hstep_p.append hstep_q⟩
    have hwalk_e1 : ∀ {n : ℕ} {a b : R}, Walk adj n a b → ∃ k, Walk adjG k (e1 a) (e1 b) := by
      intro n a b w
      induction w with
      | nil _ => exact ⟨0, Walk.nil _⟩
      | cons hab _ ih =>
        obtain ⟨k1, w1⟩ := hedge_step hab
        obtain ⟨k2, w2⟩ := ih
        exact ⟨k1 + k2, w1.append w2⟩
    obtain ⟨k, wk⟩ := hwalk_e1 wm
    have hv1 : ∃ k1, Walk adjG k1 v1 (e1 p1) := by
      rcases hp1 with rfl | rfl
      · exact ⟨0, Walk.nil _⟩
      · exact ⟨1, Walk.cons ⟨p1, Or.inr ⟨rfl, rfl⟩⟩ (Walk.nil _)⟩
    have hv2 : ∃ k2, Walk adjG k2 (e1 p2) v2 := by
      rcases hp2 with rfl | rfl
      · exact ⟨0, Walk.nil _⟩
      · exact ⟨1, Walk.cons ⟨p2, Or.inl ⟨rfl, rfl⟩⟩ (Walk.nil _)⟩
    obtain ⟨k1, w1⟩ := hv1
    obtain ⟨k2, w2⟩ := hv2
    exact ⟨k1 + k + k2, (w1.append wk).append w2⟩
  exact ⟨V, inferInstance, inferInstance, e1, e2, he1_ne_e2, hpair_uniq,
    hgram_match, hnoniso, hdeg_sum, hconnG⟩

end MainProof

end Order12.Deficit18LineGraph

/-!
# Complete 139-block extension theorem for the projective plane of order 12

Proves `new_block_of_139`: any 139 subsets of size 13 on a 157-point set that meet
pairwise in exactly one point admit a 140th subset of size 13 meeting every old block
in exactly one point (and hence distinct from all 139 old blocks).

Composes:
- `Order12DegreeTwelve` (handles any degree-12 point),
- `Order12Deficit18Core` (moments, hole-neighbor budgets, 23-profile kernel certificate,
  nonbipartite elimination, `K_{9,9}` matrix classification & mod-3 reflection lemma),
- `Order12Deficit18Profile` (`complete_bipartite_of_moments`),
- `Order12Deficit18Frame` (explicit `T = √12 I + ((13 - √12)/157) J` Euclidean frame),
- `Order12Deficit18LineGraph` (elementary ADE-free line-graph representation theorem).
-/

namespace Order12.Deficit18Complete

open Finset
open Order12.Deficit18
open Order12.Deficit18Frame
open Order12.Deficit18LineGraph

/-! ## Section 1: Monotonicity bridges for the 23-profile kernel certificate -/

private lemma foldl_ge_init {α : Type*} (l : List α) (f : ℕ → α → ℕ) (init : ℕ)
    (hmono : ∀ acc x, acc ≤ f acc x) :
    init ≤ l.foldl f init := by
  induction l generalizing init with
  | nil => exact le_refl _
  | cons a t ih => exact (hmono init a).trans (ih (f init a))

private lemma le_foldl_of_mem {α : Type*} (l : List α) (f : ℕ → α → ℕ) (init k : ℕ)
    (hmono : ∀ acc x, acc ≤ f acc x)
    (x : α) (hx : x ∈ l) (hval : ∀ acc, k ≤ f acc x) :
    k ≤ l.foldl f init := by
  induction l generalizing init with
  | nil => cases hx
  | cons a t ih =>
    rcases List.mem_cons.mp hx with rfl | hxt
    · exact (hval init).trans (foldl_ge_init t f (f init x) hmono)
    · exact ih (f init a) hxt

private lemma foldl_le_init {α : Type*} (l : List α) (f : ℕ → α → ℕ) (init : ℕ)
    (hanti : ∀ acc x, f acc x ≤ acc) :
    l.foldl f init ≤ init := by
  induction l generalizing init with
  | nil => exact le_refl _
  | cons a t ih => exact (ih (f init a)).trans (hanti init a)

private lemma foldl_le_of_mem {α : Type*} (l : List α) (f : ℕ → α → ℕ) (init k : ℕ)
    (hanti : ∀ acc x, f acc x ≤ acc)
    (x : α) (hx : x ∈ l) (hval : ∀ acc, f acc x ≤ k) :
    l.foldl f init ≤ k := by
  induction l generalizing init with
  | nil => cases hx
  | cons a t ih =>
    rcases List.mem_cons.mp hx with rfl | hxt
    · exact (foldl_le_init t f (f init x) hanti).trans (hval init)
    · exact ih (f init a) hxt

private lemma validBudget_of_witness {n3 n4 n5 n6 d a3 a4 a5 a6 : ℕ}
    (h3 : a3 ≤ if 3 * (6 - 3) < d - 2 then 0 else if d = 3 then n3 - 1 else n3)
    (h4 : a4 ≤ if 4 * (6 - 4) < d - 2 then 0 else if d = 4 then n4 - 1 else n4)
    (h5 : a5 ≤ if 5 * (6 - 5) < d - 2 then 0 else if d = 5 then n5 - 1 else n5)
    (h6 : a6 ≤ if 6 * (6 - 6) < d - 2 then 0 else if d = 6 then n6 - 1 else n6)
    (hsum : a3 + 2 * a4 + 3 * a5 + 4 * a6 = d * (6 - d)) :
    validBudget n3 n4 n5 n6 d = true := by
  unfold validBudget
  refine List.any_eq_true.mpr ⟨a3, List.mem_range.mpr (by omega), ?_⟩
  refine List.any_eq_true.mpr ⟨a4, List.mem_range.mpr (by omega), ?_⟩
  refine List.any_eq_true.mpr ⟨a5, List.mem_range.mpr (by omega), ?_⟩
  refine List.any_eq_true.mpr ⟨a6, List.mem_range.mpr (by omega), ?_⟩
  simp [hsum]

private lemma le_maxHighNeighbors2 {n3 n4 n5 n6 a3 a4 a5 a6 : ℕ}
    (h3 : a3 ≤ n3) (h4 : a4 ≤ n4) (h5 : a5 ≤ n5) (h6 : a6 ≤ n6)
    (hsum : a3 + 2 * a4 + 3 * a5 + 4 * a6 = 8) :
    a3 + a4 + a5 + a6 ≤ maxHighNeighbors2 n3 n4 n5 n6 := by
  unfold maxHighNeighbors2
  have hm6 : ∀ b3 b4 b5 acc b6,
      acc ≤ (if b3 + 2 * b4 + 3 * b5 + 4 * b6 == 8 then max acc (b3 + b4 + b5 + b6) else acc) := by
    intro b3 b4 b5 acc b6; split_ifs <;> omega
  have hm5 : ∀ b3 b4 acc b5, acc ≤ (List.range (n6 + 1)).foldl
      (fun acc b6 => if b3 + 2 * b4 + 3 * b5 + 4 * b6 == 8 then max acc (b3 + b4 + b5 + b6) else acc)
      acc := fun b3 b4 acc b5 => foldl_ge_init _ _ _ (hm6 b3 b4 b5)
  have hm4 : ∀ b3 acc b4, acc ≤ (List.range (n5 + 1)).foldl
      (fun acc b5 => (List.range (n6 + 1)).foldl
        (fun acc b6 => if b3 + 2 * b4 + 3 * b5 + 4 * b6 == 8 then max acc (b3 + b4 + b5 + b6) else acc)
        acc) acc := fun b3 acc b4 => foldl_ge_init _ _ _ (hm5 b3 b4)
  have hm3 : ∀ acc b3, acc ≤ (List.range (n4 + 1)).foldl
      (fun acc b4 => (List.range (n5 + 1)).foldl
        (fun acc b5 => (List.range (n6 + 1)).foldl
          (fun acc b6 => if b3 + 2 * b4 + 3 * b5 + 4 * b6 == 8 then max acc (b3 + b4 + b5 + b6) else acc)
          acc) acc) acc := fun acc b3 => foldl_ge_init _ _ _ (hm4 b3)
  refine le_foldl_of_mem _ _ _ _ hm3 a3 (List.mem_range.mpr (by omega)) fun acc3 => ?_
  refine le_foldl_of_mem _ _ _ _ (hm4 a3) a4 (List.mem_range.mpr (by omega)) fun acc4 => ?_
  refine le_foldl_of_mem _ _ _ _ (hm5 a3 a4) a5 (List.mem_range.mpr (by omega)) fun acc5 => ?_
  refine le_foldl_of_mem _ _ _ _ (hm6 a3 a4 a5) a6 (List.mem_range.mpr (by omega)) fun acc6 => ?_
  simp [hsum]

private lemma minHighNeighbors_le {n3 n4 n5 n6 d a3 a4 a5 a6 : ℕ}
    (h3 : a3 ≤ if 3 * (6 - 3) < d - 2 then 0 else if d = 3 then n3 - 1 else n3)
    (h4 : a4 ≤ if 4 * (6 - 4) < d - 2 then 0 else if d = 4 then n4 - 1 else n4)
    (h5 : a5 ≤ if 5 * (6 - 5) < d - 2 then 0 else if d = 5 then n5 - 1 else n5)
    (h6 : a6 ≤ if 6 * (6 - 6) < d - 2 then 0 else if d = 6 then n6 - 1 else n6)
    (hsum : a3 + 2 * a4 + 3 * a5 + 4 * a6 = d * (6 - d)) :
    minHighNeighbors n3 n4 n5 n6 d ≤ a3 + a4 + a5 + a6 := by
  unfold minHighNeighbors
  dsimp only
  let B3 := if 3 * (6 - 3) < d - 2 then 0 else if d = 3 then n3 - 1 else n3
  let B4 := if 4 * (6 - 4) < d - 2 then 0 else if d = 4 then n4 - 1 else n4
  let B5 := if 5 * (6 - 5) < d - 2 then 0 else if d = 5 then n5 - 1 else n5
  let B6 := if 6 * (6 - 6) < d - 2 then 0 else if d = 6 then n6 - 1 else n6
  have hm6 : ∀ b3 b4 b5 acc b6,
      (if b3 + 2 * b4 + 3 * b5 + 4 * b6 == d * (6 - d) then min acc (b3 + b4 + b5 + b6) else acc) ≤ acc := by
    intro b3 b4 b5 acc b6; split_ifs <;> omega
  have hm5 : ∀ b3 b4 acc b5, (List.range (B6 + 1)).foldl
      (fun acc b6 => if b3 + 2 * b4 + 3 * b5 + 4 * b6 == d * (6 - d) then min acc (b3 + b4 + b5 + b6) else acc)
      acc ≤ acc := fun b3 b4 acc b5 => foldl_le_init _ _ _ (hm6 b3 b4 b5)
  have hm4 : ∀ b3 acc b4, (List.range (B5 + 1)).foldl
      (fun acc b5 => (List.range (B6 + 1)).foldl
        (fun acc b6 => if b3 + 2 * b4 + 3 * b5 + 4 * b6 == d * (6 - d) then min acc (b3 + b4 + b5 + b6) else acc)
        acc) acc ≤ acc := fun b3 acc b4 => foldl_le_init _ _ _ (hm5 b3 b4)
  have hm3 : ∀ acc b3, (List.range (B4 + 1)).foldl
      (fun acc b4 => (List.range (B5 + 1)).foldl
        (fun acc b5 => (List.range (B6 + 1)).foldl
          (fun acc b6 => if b3 + 2 * b4 + 3 * b5 + 4 * b6 == d * (6 - d) then min acc (b3 + b4 + b5 + b6) else acc)
          acc) acc) acc ≤ acc := fun acc b3 => foldl_le_init _ _ _ (hm4 b3)
  change (List.range (B3 + 1)).foldl _ 1000 ≤ a3 + a4 + a5 + a6
  refine foldl_le_of_mem _ _ _ _ hm3 a3 (List.mem_range.mpr (by omega)) fun acc3 => ?_
  refine foldl_le_of_mem _ _ _ _ (hm4 a3) a4 (List.mem_range.mpr (by omega)) fun acc4 => ?_
  refine foldl_le_of_mem _ _ _ _ (hm5 a3 a4) a5 (List.mem_range.mpr (by omega)) fun acc5 => ?_
  refine foldl_le_of_mem _ _ _ _ (hm6 a3 a4 a5) a6 (List.mem_range.mpr (by omega)) fun acc6 => ?_
  simp [hsum]

/-! ## Section 2: Finite-dimensional orthogonal complement helpers -/

private lemma exists_nonzero_ortho {α : Type*} [Fintype α]
    (S T : Submodule ℝ (α → ℝ)) (_hST : S ≤ T)
    (hlt : Module.finrank ℝ S < Module.finrank ℝ T) :
    ∃ v : α → ℝ, v ∈ T ∧ v ≠ 0 ∧ ∀ s ∈ S, Order12.Deficit18Frame.dot v s = 0 := by
  let d := Module.finrank ℝ S
  let b := Module.finBasis ℝ S
  let ψ : T →ₗ[ℝ] (Fin d → ℝ) :=
    { toFun := fun x k => Order12.Deficit18Frame.dot x.1 (b k).1
      map_add' := fun x y => by ext k; exact Order12.Deficit18Frame.dot_add_left _ _ _
      map_smul' := fun c x => by ext k; exact Order12.Deficit18Frame.dot_smul_left _ _ _ }
  have hrank := LinearMap.finrank_range_add_finrank_ker ψ
  have hrle : Module.finrank ℝ (LinearMap.range ψ) ≤ d := by
    calc
      Module.finrank ℝ (LinearMap.range ψ) ≤ Module.finrank ℝ (Fin d → ℝ) := Submodule.finrank_le _
      _ = d := by simp
  have hker_pos : 0 < Module.finrank ℝ (LinearMap.ker ψ) := by omega
  have hker_ne : LinearMap.ker ψ ≠ ⊥ := by
    intro h; rw [h, finrank_bot] at hker_pos; omega
  obtain ⟨x, hx_ker, hx_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker_ne
  refine ⟨x.1, x.2, fun h => hx_ne (Subtype.ext h), fun s hs => ?_⟩
  have hrep : (⟨s, hs⟩ : S) = ∑ k : Fin d, (b.repr ⟨s, hs⟩ k) • b k := (b.sum_repr ⟨s, hs⟩).symm
  have hs_eq : s = ∑ k : Fin d, (b.repr ⟨s, hs⟩ k) • (b k).1 := by
    have h1 : s = (∑ k : Fin d, (b.repr ⟨s, hs⟩ k) • b k).1 := congrArg Subtype.val hrep
    have h2 : (∑ k : Fin d, (b.repr ⟨s, hs⟩ k) • b k).1 =
        ∑ k : Fin d, (b.repr ⟨s, hs⟩ k) • (b k).1 := by
      change (Submodule.subtype S) (∑ k : Fin d, (b.repr ⟨s, hs⟩ k) • b k) = _
      rw [map_sum]
      exact sum_congr rfl fun k _ => map_smul (Submodule.subtype S) _ _
    exact h1.trans h2
  rw [hs_eq, Order12.Deficit18Frame.dot_sum_right]
  apply sum_eq_zero; intro k _
  rw [Order12.Deficit18Frame.dot_smul_right]
  have hk : ψ x k = 0 := congrFun (LinearMap.mem_ker.mp hx_ker) k
  dsimp [ψ] at hk
  rw [hk, mul_zero]

private lemma eq_of_le_of_ortho_zero {α : Type*} [Fintype α]
    (S T : Submodule ℝ (α → ℝ)) (hST : S ≤ T)
    (huniq : ∀ v ∈ T, (∀ s ∈ S, Order12.Deficit18Frame.dot v s = 0) → v = 0) :
    S = T := by
  refine Submodule.eq_of_le_of_finrank_eq hST (le_antisymm (Submodule.finrank_mono hST) ?_)
  by_contra hlt
  push Not at hlt
  obtain ⟨v, hvT, hv0, horth⟩ := exists_nonzero_ortho S T hST hlt
  exact hv0 (huniq v hvT horth)

/-! ## Section 3: Root graph connectedness and minimum degree ≥ 16 -/

private instance instDecIsHole {P L : Type*} [Fintype L] [DecidableEq P]
    (B : L → Finset P) (p q : P) : Decidable (IsHole B p q) := by
  unfold IsHole; infer_instance

section RootGraph

variable {P L : Type*} [Fintype P] [Fintype L] [DecidableEq P] [DecidableEq L]

set_option maxHeartbeats 1200000 in
/-- Wires `all_23_profiles_connected` to the actual root graph of a 139-block configuration
with no degree-12 point: gives `n2 ≥ 81`, exact moment equations, min root degree `≥ 16`,
common-neighbor bounds `≤ 12` / `≤ 4`, and connectedness of the root graph `H`. -/
theorem root_graph_properties
    (B : L → Finset P) (hp : Fintype.card P = 157) (hl : Fintype.card L = 139)
    (hsize : ∀ l, (B l).card = 13)
    (hmeet : ∀ l m, l ≠ m → (B l ∩ B m).card = 1)
    (hno12 : ∀ p, deg B p ≠ 12) :
    let R := univ.filter fun p => defic B p = 2
    let n3 := (univ.filter fun p => defic B p = 3).card
    let n4 := (univ.filter fun p => defic B p = 4).card
    let n5 := (univ.filter fun p => defic B p = 5).card
    let n6 := (univ.filter fun p => defic B p = 6).card
    let adjR : {p : P // p ∈ R} → {p : P // p ∈ R} → Prop := fun a b => IsHole B a.1 b.1
    (3 * n3 + 8 * n4 + 15 * n5 + 24 * n6 = 72) ∧
    (2 * R.card + 3 * n3 + 4 * n4 + 5 * n5 + 6 * n6 = 234) ∧
    (81 ≤ R.card) ∧
    (∀ p : {p : P // p ∈ R}, 16 ≤ (univ.filter (adjR p)).card) ∧
    (∀ p q : {p : P // p ∈ R}, adjR p q →
      (univ.filter (adjR p) ∩ univ.filter (adjR q)).card ≤ 12) ∧
    (∀ p q : {p : P // p ∈ R}, p ≠ q → ¬ adjR p q →
      (univ.filter (adjR p) ∩ univ.filter (adjR q)).card ≤ 4) ∧
    (∀ p q : {p : P // p ∈ R}, ∃ m, Walk adjR m p q) := by
  classical
  intro R n3 n4 n5 n6 adjR
  obtain ⟨hdmass, hexcess, _⟩ := moments_of_139 B hp hl hsize hmeet
  -- Every point has deficiency in {0, 2, 3, 4, 5, 6}.
  have hdef_cases : ∀ p : P, defic B p = 0 ∨ defic B p = 2 ∨ defic B p = 3 ∨
      defic B p = 4 ∨ defic B p = 5 ∨ defic B p = 6 := by
    intro p
    have hle13 := deg_le_13 B hp hsize hmeet p
    have hne12 := hno12 p
    have hle6 := defic_le_6_of_no_deg12 B hp hl hsize hmeet hno12 p
    dsimp [defic] at hle6 ⊢
    omega
  -- Sum by deficiency class.
  let D : ℤ → Finset P := fun k => univ.filter fun p => defic B p = k
  have hsum_by_def : ∀ (f : ℤ → ℤ),
      ∑ p : P, f (defic B p) =
        ((D 0).card : ℤ) * f 0 + ((D 2).card : ℤ) * f 2 + ((D 3).card : ℤ) * f 3 +
        ((D 4).card : ℤ) * f 4 + ((D 5).card : ℤ) * f 5 + ((D 6).card : ℤ) * f 6 := by
    intro f
    have hpart : ∀ p : P, f (defic B p) =
        (if defic B p = 0 then f 0 else 0) + (if defic B p = 2 then f 2 else 0) +
        (if defic B p = 3 then f 3 else 0) + (if defic B p = 4 then f 4 else 0) +
        (if defic B p = 5 then f 5 else 0) + (if defic B p = 6 then f 6 else 0) := by
      intro p
      rcases hdef_cases p with h | h | h | h | h | h <;> simp [h]
    simp_rw [hpart, sum_add_distrib]
    have hite (k : ℤ) : ∑ p : P, (if defic B p = k then f k else 0) = ((D k).card : ℤ) * f k := by
      rw [← sum_filter, sum_const, nsmul_eq_mul]
    simp_rw [hite]
  have hmass_nat : 2 * R.card + 3 * n3 + 4 * n4 + 5 * n5 + 6 * n6 = 234 := by
    have h := hsum_by_def (fun d => d)
    rw [hdmass] at h
    have : (2 * R.card + 3 * n3 + 4 * n4 + 5 * n5 + 6 * n6 : ℤ) = 234 := by
      change (2 * ((D 2).card : ℤ) + 3 * ((D 3).card : ℤ) + 4 * ((D 4).card : ℤ) +
        5 * ((D 5).card : ℤ) + 6 * ((D 6).card : ℤ)) = 234
      linarith
    exact_mod_cast this
  have hexcess_nat : 3 * n3 + 8 * n4 + 15 * n5 + 24 * n6 = 72 := by
    have h := hsum_by_def (fun d => d * (d - 2))
    rw [hexcess] at h
    have : (3 * n3 + 8 * n4 + 15 * n5 + 24 * n6 : ℤ) = 72 := by
      change (3 * ((D 3).card : ℤ) + 8 * ((D 4).card : ℤ) + 15 * ((D 5).card : ℤ) +
        24 * ((D 6).card : ℤ)) = 72
      linarith
    exact_mod_cast this
  have hn2_ge81 : 81 ≤ R.card := by omega
  -- Every hole neighbor of any point has deficiency in {2, 3, 4, 5, 6}.
  have hhole_pos : ∀ p q : P, q ∈ holeNbrs B p → 2 ≤ defic B q := by
    intro p q hq
    rcases hdef_cases q with h0 | h2 | h3 | h4 | h5 | h6
    · exfalso
      have hdeg13 : deg B q = 13 := by dsimp [defic] at h0; omega
      have hcard := card_holeNbrs B hp hsize hmeet q
      rw [hdeg13] at hcard
      have hpq : p ∈ holeNbrs B q := by
        rw [mem_holeNbrs]; have ⟨hne, hnl⟩ := mem_holeNbrs.mp hq
        exact ⟨hne.symm, fun l ⟨hq1, hp1⟩ => hnl l ⟨hp1, hq1⟩⟩
      have hpos := card_pos.mpr ⟨p, hpq⟩
      omega
    all_goals omega
  -- For any point p with deficiency d ∈ {2,3,4,5,6}, its high hole-neighbor counts satisfy the budget!
  have hlocal_budget : ∀ (p : P) (d : ℕ), defic B p = (d : ℤ) → 2 ≤ d → d ≤ 6 →
      let a3 := ((holeNbrs B p).filter fun q => defic B q = 3).card
      let a4 := ((holeNbrs B p).filter fun q => defic B q = 4).card
      let a5 := ((holeNbrs B p).filter fun q => defic B q = 5).card
      let a6 := ((holeNbrs B p).filter fun q => defic B q = 6).card
      (a3 + 2 * a4 + 3 * a5 + 4 * a6 = d * (6 - d)) ∧
      (a3 ≤ if 3 * (6 - 3) < d - 2 then 0 else if d = 3 then n3 - 1 else n3) ∧
      (a4 ≤ if 4 * (6 - 4) < d - 2 then 0 else if d = 4 then n4 - 1 else n4) ∧
      (a5 ≤ if 5 * (6 - 5) < d - 2 then 0 else if d = 5 then n5 - 1 else n5) ∧
      (a6 ≤ if 6 * (6 - 6) < d - 2 then 0 else if d = 6 then n6 - 1 else n6) ∧
      ((holeNbrs B p ∩ R).card + (a3 + a4 + a5 + a6) = 12 * d) := by
    intro p d hdp hd2 hd6
    dsimp only
    let A : ℤ → Finset P := fun j => (holeNbrs B p).filter fun q => defic B q = j
    have hsplit : ∀ q ∈ holeNbrs B p, defic B q - 2 =
        (if defic B q = 3 then 1 else 0) + (if defic B q = 4 then 2 else 0) +
        (if defic B q = 5 then 3 else 0) + (if defic B q = 6 then 4 else 0) := by
      intro q hq
      have h2 := hhole_pos p q hq
      rcases hdef_cases q with h | h | h | h | h | h <;> simp_all
    have hbud := hole_neighbor_budget_139 B hp hl hsize hmeet p
    have hsum_eq : ∑ q ∈ holeNbrs B p, (defic B q - 2) =
        ((A 3).card : ℤ) + 2 * ((A 4).card : ℤ) + 3 * ((A 5).card : ℤ) + 4 * ((A 6).card : ℤ) := by
      rw [sum_congr rfl hsplit]
      simp only [sum_add_distrib]
      have hite (j c : ℤ) :
          ∑ q ∈ holeNbrs B p, (if defic B q = j then c else 0) = ((A j).card : ℤ) * c := by
        rw [← sum_filter, sum_const, nsmul_eq_mul]
      rw [hite 3 1, hite 4 2, hite 5 3, hite 6 4]; ring
    have hbud_nat : (A 3).card + 2 * (A 4).card + 3 * (A 5).card + 4 * (A 6).card = d * (6 - d) := by
      have : (((A 3).card + 2 * (A 4).card + 3 * (A 5).card + 4 * (A 6).card : ℕ) : ℤ) =
          ((d * (6 - d) : ℕ) : ℤ) := by
        push_cast
        rw [← hsum_eq, hbud, hdp]
        have : ((6 - d : ℕ) : ℤ) = 6 - (d : ℤ) := by omega
        rw [this]
      exact_mod_cast this
    have hbound_j : ∀ (j : ℕ), 3 ≤ j → j ≤ 6 →
        (A j).card ≤ if j * (6 - j) < d - 2 then 0 else if d = j then (D j).card - 1 else (D j).card := by
      intro j hj3 hj6
      split_ifs with hlt heq
      · rw [Nat.le_zero, card_eq_zero, filter_eq_empty_iff]
        intro q hq hqj
        have hp_in_q : p ∈ holeNbrs B q := by
          rw [mem_holeNbrs]; have ⟨hne, hnl⟩ := mem_holeNbrs.mp hq
          exact ⟨hne.symm, fun l ⟨h1, h2⟩ => hnl l ⟨h2, h1⟩⟩
        have hqbud := hole_neighbor_budget_139 B hp hl hsize hmeet q
        have hterm_le : defic B p - 2 ≤ ∑ r ∈ holeNbrs B q, (defic B r - 2) :=
          Finset.single_le_sum (f := fun r => defic B r - 2)
            (fun r hr => by have := hhole_pos q r hr; omega) hp_in_q
        rw [hqbud, hqj, hdp] at hterm_le
        have hmul_z : ((j * (6 - j) : ℕ) : ℤ) = (j : ℤ) * (6 - (j : ℤ)) := by
          have : ((6 - j : ℕ) : ℤ) = 6 - (j : ℤ) := by omega
          push_cast; rw [this]
        have hlt_z : ((j * (6 - j) : ℕ) : ℤ) < (d : ℤ) - 2 := by omega
        omega
      · have hsub : A j ⊆ (D j).erase p := by
          intro q hq
          have ⟨hqh, hqj⟩ := mem_filter.mp hq
          have hqp : q ≠ p := (mem_holeNbrs.mp hqh).1.symm
          exact mem_erase.mpr ⟨hqp, mem_filter.mpr ⟨mem_univ _, hqj⟩⟩
        have hp_in_D : p ∈ D j := mem_filter.mpr ⟨mem_univ _, by omega⟩
        have hc := card_le_card hsub
        rw [card_erase_of_mem hp_in_D] at hc
        exact hc
      · have hsub : A j ⊆ D j := fun q hq => mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hq).2⟩
        exact card_le_card hsub
    have htot_hole : (holeNbrs B p ∩ R).card + ((A 3).card + (A 4).card + (A 5).card + (A 6).card) = 12 * d := by
      have hcard := card_holeNbrs B hp hsize hmeet p
      have hcard_d : (holeNbrs B p).card = 12 * d := by
        have hle := deg_le_13 B hp hsize hmeet p
        dsimp [defic] at hdp; omega
      have hcount : ∑ q ∈ holeNbrs B p, (1 : ℕ) =
          (holeNbrs B p ∩ R).card + (A 3).card + (A 4).card + (A 5).card + (A 6).card := by
        have h1 : ∀ q ∈ holeNbrs B p, (1 : ℕ) =
            (if defic B q = 2 then 1 else 0) + (if defic B q = 3 then 1 else 0) +
            (if defic B q = 4 then 1 else 0) + (if defic B q = 5 then 1 else 0) +
            (if defic B q = 6 then 1 else 0) := by
          intro q hq
          have h2 := hhole_pos p q hq
          rcases hdef_cases q with h | h | h | h | h | h <;> simp_all
        rw [sum_congr rfl h1]
        simp only [sum_add_distrib, sum_boole, Nat.cast_id]
        have hR : (holeNbrs B p).filter (fun q => defic B q = 2) = holeNbrs B p ∩ R := by
          ext q; simp [R]
        rw [hR]
      simp only [sum_const, smul_eq_mul, mul_one, hcard_d] at hcount
      omega
    exact ⟨hbud_nat, hbound_j 3 (by omega) (by omega), hbound_j 4 (by omega) (by omega),
      hbound_j 5 (by omega) (by omega), hbound_j 6 (by omega) (by omega), htot_hole⟩
  -- Invoke the kernel-checked 23-profile connectedness certificate!
  have hcert := all_23_profiles_connected ⟨n3, by omega⟩ ⟨n4, by omega⟩ ⟨n5, by omega⟩ ⟨n6, by omega⟩
  dsimp only [profileConnectedCheck] at hcert
  have hne72 : (3 * n3 + 8 * n4 + 15 * n5 + 24 * n6 != 72) = false := by simp [hexcess_nat]
  have hs_le : (234 < 3 * n3 + 4 * n4 + 5 * n5 + 6 * n6 ||
      (234 - (3 * n3 + 4 * n4 + 5 * n5 + 6 * n6)) % 2 != 0) = false := by
    have h1 : ¬ 234 < 3 * n3 + 4 * n4 + 5 * n5 + 6 * n6 := by omega
    have h2 : (234 - (3 * n3 + 4 * n4 + 5 * n5 + 6 * n6)) % 2 = 0 := by omega
    simp [h1, h2]
  have hvb2 : validBudget n3 n4 n5 n6 2 = true := by
    obtain ⟨p0, hp0⟩ := card_pos.mp (by omega : 0 < R.card)
    have ⟨hsum, h3, h4, h5, h6, _⟩ := hlocal_budget p0 2 (mem_filter.mp hp0).2 (by omega) (by omega)
    exact validBudget_of_witness h3 h4 h5 h6 hsum
  have hvb_j : ∀ j : ℕ, 3 ≤ j → j ≤ 6 → ((D j).card == 0 || validBudget n3 n4 n5 n6 j) = true := by
    intro j hj3 hj6
    by_cases h0 : (D j).card = 0
    · simp [h0]
    · obtain ⟨p0, hp0⟩ := card_pos.mp (by omega : 0 < (D j).card)
      have ⟨hsum, h3, h4, h5, h6, _⟩ := hlocal_budget p0 j (mem_filter.mp hp0).2 (by omega) (by omega)
      simp [validBudget_of_witness h3 h4 h5 h6 hsum]
  have hokAll : (validBudget n3 n4 n5 n6 2 &&
      (n3 == 0 || validBudget n3 n4 n5 n6 3) &&
      (n4 == 0 || validBudget n3 n4 n5 n6 4) &&
      (n5 == 0 || validBudget n3 n4 n5 n6 5) &&
      (n6 == 0 || validBudget n3 n4 n5 n6 6)) = true := by
    have h3 : (n3 == 0 || validBudget n3 n4 n5 n6 3) = true := hvb_j 3 (by omega) (by omega)
    have h4 : (n4 == 0 || validBudget n3 n4 n5 n6 4) = true := hvb_j 4 (by omega) (by omega)
    have h5 : (n5 == 0 || validBudget n3 n4 n5 n6 5) = true := hvb_j 5 (by omega) (by omega)
    have h6 : (n6 == 0 || validBudget n3 n4 n5 n6 6) = true := hvb_j 6 (by omega) (by omega)
    rw [hvb2, h3, h4, h5, h6]
    rfl
  simp only [hne72, Bool.false_eq_true, ↓reduceIte, hs_le] at hcert
  rw [hokAll] at hcert
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq] at hcert
  have hn2_div : (234 - (3 * n3 + 4 * n4 + 5 * n5 + 6 * n6)) / 2 = R.card := by omega
  rw [hn2_div] at hcert
  set k := 24 - maxHighNeighbors2 n3 n4 n5 n6
  set z := 1 + k + (k * (k - 13) + 3) / 4
  set u3 := if n3 == 0 then 0 else n3 * ((36 - minHighNeighbors n3 n4 n5 n6 3) ^ 2 / 4)
  set u4 := if n4 == 0 then 0 else n4 * ((48 - minHighNeighbors n3 n4 n5 n6 4) ^ 2 / 4)
  set u5 := if n5 == 0 then 0 else n5 * ((60 - minHighNeighbors n3 n4 n5 n6 5) ^ 2 / 4)
  set u6 := if n6 == 0 then 0 else n6 * ((72 - minHighNeighbors n3 n4 n5 n6 6) ^ 2 / 4)
  have hk16 : 16 ≤ k := hcert.1
  have hconn_ineq : 2 * z > R.card ∨ u3 + u4 + u5 + u6 < 4 * z * (R.card - z) := hcert.2
  -- Translate root-graph neighborhoods between R and {p // p ∈ R}.
  have hdeg_root : ∀ p : {p : P // p ∈ R}, k ≤ (univ.filter (adjR p)).card := by
    intro p
    have hcard_eq : (univ.filter (adjR p)).card = (holeNbrs B p.1 ∩ R).card := by
      refine Finset.card_bij (fun q _ => q.1) ?_ ?_ ?_
      · intro q hq
        exact mem_inter.mpr ⟨mem_holeNbrs.mpr (mem_filter.mp hq).2, q.2⟩
      · intro q1 _ q2 _ h; exact Subtype.ext h
      · intro q hq
        have ⟨hqh, hqR⟩ := mem_inter.mp hq
        exact ⟨⟨q, hqR⟩, mem_filter.mpr ⟨mem_univ _, mem_holeNbrs.mp hqh⟩, rfl⟩
    rw [hcard_eq]
    have ⟨hsum, h3, h4, h5, h6, htot⟩ := hlocal_budget p.1 2 (mem_filter.mp p.2).2 (by omega) (by omega)
    simp only [Nat.sub_self, Nat.not_lt_zero, ↓reduceIte] at h3 h4 h5 h6
    have hle_max := le_maxHighNeighbors2
      (by simpa using h3) (by simpa using h4) (by simpa using h5) (by simpa using h6)
      (by simpa using hsum)
    omega
  have hcomm_adj : ∀ p q : {p : P // p ∈ R}, adjR p q →
      (univ.filter (adjR p) ∩ univ.filter (adjR q)).card ≤ 12 := by
    intro p q hpq
    have hle : (univ.filter (adjR p) ∩ univ.filter (adjR q)).card ≤
        (holeNbrs B p.1 ∩ holeNbrs B q.1).card := by
      refine Finset.card_le_card_of_injOn Subtype.val ?_ (fun _ _ _ _ h => Subtype.ext h)
      intro r hr
      have ⟨hr1, hr2⟩ := mem_inter.mp hr
      exact mem_inter.mpr ⟨mem_holeNbrs.mpr (mem_filter.mp hr1).2, mem_holeNbrs.mpr (mem_filter.mp hr2).2⟩
    have h12 := card_common_holes_of_hole B hp hsize hmeet hpq
    rw [(mem_filter.mp p.2).2, (mem_filter.mp q.2).2] at h12
    omega
  have hcomm_nonadj : ∀ p q : {p : P // p ∈ R}, p ≠ q → ¬ adjR p q →
      (univ.filter (adjR p) ∩ univ.filter (adjR q)).card ≤ 4 := by
    intro p q hpq hna
    have hle : (univ.filter (adjR p) ∩ univ.filter (adjR q)).card ≤
        (holeNbrs B p.1 ∩ holeNbrs B q.1).card := by
      refine Finset.card_le_card_of_injOn Subtype.val ?_ (fun _ _ _ _ h => Subtype.ext h)
      intro r hr
      have ⟨hr1, hr2⟩ := mem_inter.mp hr
      exact mem_inter.mpr ⟨mem_holeNbrs.mpr (mem_filter.mp hr1).2, mem_holeNbrs.mpr (mem_filter.mp hr2).2⟩
    have hne : p.1 ≠ q.1 := fun e => hpq (Subtype.ext e)
    have hcov : ∃ l0, p.1 ∈ B l0 ∧ q.1 ∈ B l0 := by
      by_contra hno; push Not at hno; exact hna ⟨hne, fun l ⟨h1, h2⟩ => hno l h1 h2⟩
    obtain ⟨l0, hp0, hq0⟩ := hcov
    have h4 := card_common_holes_of_covered B hp hsize hmeet hne hp0 hq0
    rw [(mem_filter.mp p.2).2, (mem_filter.mp q.2).2] at h4
    omega
  -- Connectedness of adjR.
  have hadjR_sym : ∀ a b : {p : P // p ∈ R}, adjR a b → adjR b a := fun a b ⟨hne, hnl⟩ =>
    ⟨hne.symm, fun l ⟨h1, h2⟩ => hnl l ⟨h2, h1⟩⟩
  have hconnR : ∀ p q : {p : P // p ∈ R}, ∃ m, Walk adjR m p q := by
    -- Lower bound z ≤ C.card for any nonempty edge-closed subset C of {p // p ∈ R}.
    have hcomp_lb : ∀ (C : Finset {p : P // p ∈ R}), C.Nonempty →
        (∀ a ∈ C, ∀ b, adjR a b → b ∈ C) → z ≤ C.card := by
      intro C ⟨p0, hp0C⟩ hclosed
      let N := univ.filter (adjR p0)
      have hN_sub : N ⊆ C := fun q hq => hclosed p0 hp0C q (mem_filter.mp hq).2
      have hp0_not_N : p0 ∉ N := fun h => (mem_filter.mp h).2.1 rfl
      let D2 := C \ insert p0 N
      have hD2_card : D2.card + (1 + N.card) = C.card := by
        have hsub : insert p0 N ⊆ C := insert_subset_iff.mpr ⟨hp0C, hN_sub⟩
        have hle := card_le_card hsub
        rw [card_insert_of_notMem hp0_not_N] at hle
        dsimp only [D2]
        rw [card_sdiff_of_subset hsub, card_insert_of_notMem hp0_not_N]
        omega
      -- Double count edges between N and D2.
      have hdouble : ∑ q ∈ N, (univ.filter (adjR q) ∩ D2).card =
          ∑ w ∈ D2, (univ.filter (adjR w) ∩ N).card := by
        have hlhs : ∑ q ∈ N, (univ.filter (adjR q) ∩ D2).card =
            ∑ q ∈ N, ∑ w ∈ D2, if adjR q w then 1 else 0 := by
          apply sum_congr rfl; intro q _
          rw [sum_boole, Nat.cast_id]; congr 1; ext w; simp [and_comm]
        have hrhs : ∑ w ∈ D2, (univ.filter (adjR w) ∩ N).card =
            ∑ w ∈ D2, ∑ q ∈ N, if adjR q w then 1 else 0 := by
          apply sum_congr rfl; intro w _
          rw [sum_boole, Nat.cast_id]; congr 1; ext q
          simp only [mem_inter, mem_filter, mem_univ, true_and]
          exact ⟨fun ⟨h1, h2⟩ => ⟨h2, hadjR_sym w q h1⟩, fun ⟨h1, h2⟩ => ⟨hadjR_sym q w h2, h1⟩⟩
        rw [hlhs, hrhs, Finset.sum_comm]
      have hlb_sum : k * (k - 13) ≤ ∑ q ∈ N, (univ.filter (adjR q) ∩ D2).card := by
        have heach : ∀ q ∈ N, k - 13 ≤ (univ.filter (adjR q) ∩ D2).card := by
          intro q hqN
          have hsub : univ.filter (adjR q) ⊆ insert p0 ((univ.filter (adjR q) ∩ N) ∪ (univ.filter (adjR q) ∩ D2)) := by
            intro w hw
            by_cases hwp : w = p0
            · simp [hwp]
            · refine mem_insert_of_mem ?_
              by_cases hwN : w ∈ N
              · exact mem_union_left _ (mem_inter.mpr ⟨hw, hwN⟩)
              · exact mem_union_right _ (mem_inter.mpr ⟨hw, mem_sdiff.mpr ⟨hclosed q (hN_sub hqN) w (mem_filter.mp hw).2, by simp [hwp, hwN]⟩⟩)
          have hc1 := card_le_card hsub
          have hc2 := card_insert_le p0 ((univ.filter (adjR q) ∩ N) ∪ (univ.filter (adjR q) ∩ D2))
          have hc3 := card_union_le (univ.filter (adjR q) ∩ N) (univ.filter (adjR q) ∩ D2)
          have h12 : (univ.filter (adjR q) ∩ N).card ≤ 12 := by
            rw [inter_comm]; exact hcomm_adj p0 q (mem_filter.mp hqN).2
          have hdq := hdeg_root q
          omega
        calc
          k * (k - 13) ≤ N.card * (k - 13) := Nat.mul_le_mul_right _ (hdeg_root p0)
          _ = ∑ _q ∈ N, (k - 13) := by simp
          _ ≤ _ := sum_le_sum heach
      have hub_sum : ∑ w ∈ D2, (univ.filter (adjR w) ∩ N).card ≤ 4 * D2.card := by
        have heach : ∀ w ∈ D2, (univ.filter (adjR w) ∩ N).card ≤ 4 := by
          intro w hwD2
          have hw_not := (mem_sdiff.mp hwD2).2
          have hwp : p0 ≠ w := fun e => hw_not (e ▸ mem_insert_self _ _)
          have hna : ¬ adjR p0 w := fun h => hw_not (mem_insert_of_mem (mem_filter.mpr ⟨mem_univ _, h⟩))
          rw [inter_comm]; exact hcomm_nonadj p0 w hwp hna
        calc
          _ ≤ ∑ _w ∈ D2, 4 := sum_le_sum heach
          _ = 4 * D2.card := by simp [mul_comm]
      have h4D2 : k * (k - 13) ≤ 4 * D2.card := by omega
      have hceil : (k * (k - 13) + 3) / 4 ≤ D2.card := by omega
      have hNk : k ≤ N.card := hdeg_root p0
      dsimp only [z]
      omega
    intro p0 q0
    by_contra hnot
    let C1 : Finset {p : P // p ∈ R} := univ.filter fun x => ∃ m, Walk adjR m p0 x
    let C2 : Finset {p : P // p ∈ R} := univ \ C1
    have hp0C1 : p0 ∈ C1 := mem_filter.mpr ⟨mem_univ _, 0, Walk.nil _⟩
    have hq0C2 : q0 ∈ C2 := mem_sdiff.mpr ⟨mem_univ _, fun h => hnot (mem_filter.mp h).2⟩
    have hcl1 : ∀ a ∈ C1, ∀ b, adjR a b → b ∈ C1 := by
      intro a ha b hab
      obtain ⟨m, wm⟩ := (mem_filter.mp ha).2
      exact mem_filter.mpr ⟨mem_univ _, m + 1, wm.append (Walk.cons hab (Walk.nil _))⟩
    have hcl2 : ∀ a ∈ C2, ∀ b, adjR a b → b ∈ C2 := by
      intro a ha b hab
      refine mem_sdiff.mpr ⟨mem_univ _, fun hb1 => (mem_sdiff.mp ha).2 ?_⟩
      exact hcl1 b hb1 a (hadjR_sym a b hab)
    have hz1 : z ≤ C1.card := hcomp_lb C1 ⟨p0, hp0C1⟩ hcl1
    have hz2 : z ≤ C2.card := hcomp_lb C2 ⟨q0, hq0C2⟩ hcl2
    have hsum12 : C1.card + C2.card = R.card := by
      have htot : (univ : Finset {p : P // p ∈ R}).card = R.card := by simp
      have hle : C1.card ≤ R.card := by rw [← htot]; exact card_le_card (subset_univ C1)
      dsimp only [C2]
      rw [card_sdiff_of_subset (subset_univ C1), htot]
      omega
    let C := if C1.card ≤ C2.card then C1 else C2
    let C' := if C1.card ≤ C2.card then C2 else C1
    have hx_ge_z : z ≤ C.card := by dsimp [C]; split_ifs <;> omega
    have h2x_le : 2 * C.card ≤ R.card := by dsimp [C]; split_ifs <;> omega
    have hC'_card : C'.card = R.card - C.card := by dsimp [C, C']; split_ifs <;> omega
    have hno_cross : ∀ a ∈ C, ∀ b ∈ C', ¬ adjR a b := by
      intro a ha b hb hab
      dsimp [C, C'] at ha hb
      split_ifs at ha hb
      · exact (mem_sdiff.mp hb).2 (hcl1 a ha b hab)
      · exact (mem_sdiff.mp ha).2 (hcl1 b hb a (hadjR_sym a b hab))
    have hdisj_CC' : Disjoint C C' := by
      dsimp [C, C']; split_ifs
      · exact disjoint_sdiff_self_right
      · exact disjoint_sdiff_self_left
    -- Eliminate first disjunct 2 * z > R.card.
    have hnot_2z : ¬ (2 * z > R.card) := by omega
    have hstrict : u3 + u4 + u5 + u6 < 4 * z * (R.card - z) := hconn_ineq.resolve_left hnot_2z
    -- Quad bound z*(n2 - z) ≤ x*(n2 - x).
    have hquad : z * (R.card - z) ≤ C.card * (R.card - C.card) := by
      have hz_le_n : z ≤ R.card := by omega
      have hx_le_n : C.card ≤ R.card := by omega
      have hdiff : ((C.card : ℤ) - z) * ((R.card : ℤ) - C.card - z) ≥ 0 := by nlinarith
      have : ((z * (R.card - z) : ℕ) : ℤ) ≤ ((C.card * (R.card - C.card) : ℕ) : ℤ) := by
        have h1 : ((R.card - z : ℕ) : ℤ) = (R.card : ℤ) - z := by omega
        have h2 : ((R.card - C.card : ℕ) : ℤ) = (R.card : ℤ) - C.card := by omega
        push_cast; rw [h1, h2]; linarith
      exact_mod_cast this
    -- Double-count cross pairs through High = D 3 ∪ D 4 ∪ D 5 ∪ D 6.
    let High := univ.filter fun h : P => 3 ≤ defic B h
    let CP := C.image Subtype.val
    let CP' := C'.image Subtype.val
    have hCP_card : CP.card = C.card := card_image_of_injective _ Subtype.val_injective
    have hCP'_card : CP'.card = C'.card := card_image_of_injective _ Subtype.val_injective
    have hCP_disj : Disjoint CP CP' := by
      apply Finset.disjoint_left.mpr
      intro x hx1 hx2
      obtain ⟨a, ha, rfl⟩ := mem_image.mp hx1
      obtain ⟨b, hb, hab⟩ := mem_image.mp hx2
      have : a = b := Subtype.ext hab.symm
      exact Finset.disjoint_left.mp hdisj_CC' ha (this ▸ hb)
    have hCP_sub_R : CP ∪ CP' ⊆ R := union_subset
      (fun x hx => by obtain ⟨a, _, rfl⟩ := mem_image.mp hx; exact a.2)
      (fun x hx => by obtain ⟨a, _, rfl⟩ := mem_image.mp hx; exact a.2)
    have h4cross : 4 * (C.card * C'.card) =
        ∑ h ∈ High, (holeNbrs B h ∩ CP).card * (holeNbrs B h ∩ CP').card := by
      have hlhs : 4 * (C.card * C'.card) =
          ∑ a ∈ C, ∑ b ∈ C', (holeNbrs B a.1 ∩ holeNbrs B b.1 ∩ High).card := by
        have heach : ∀ a ∈ C, ∀ b ∈ C', (holeNbrs B a.1 ∩ holeNbrs B b.1 ∩ High).card = 4 := by
          intro a ha b hb
          have hab_ne : a ≠ b := fun e => Finset.disjoint_left.mp hdisj_CC' ha (e ▸ hb)
          have hna : ¬ adjR a b := hno_cross a ha b hb
          have hsub_high : holeNbrs B a.1 ∩ holeNbrs B b.1 ⊆ High := by
            intro h hh
            have ⟨hha, hhb⟩ := mem_inter.mp hh
            have h2 := hhole_pos a.1 h hha
            by_cases hR : defic B h = 2
            · exfalso
              have hhR : h ∈ R := mem_filter.mpr ⟨mem_univ _, hR⟩
              have ha_adj : adjR a ⟨h, hhR⟩ := mem_holeNbrs.mp hha
              have hb_adj : adjR b ⟨h, hhR⟩ := mem_holeNbrs.mp hhb
              dsimp [C, C'] at ha hb
              split_ifs at ha hb
              · exact (mem_sdiff.mp hb).2 (hcl1 ⟨h, hhR⟩ (hcl1 a ha ⟨h, hhR⟩ ha_adj) b (hadjR_sym b ⟨h, hhR⟩ hb_adj))
              · exact (mem_sdiff.mp ha).2 (hcl1 ⟨h, hhR⟩ (hcl1 b hb ⟨h, hhR⟩ hb_adj) a (hadjR_sym a ⟨h, hhR⟩ ha_adj))
            · exact mem_filter.mpr ⟨mem_univ _, by omega⟩
          rw [inter_eq_left.mpr hsub_high]
          have hcov : ∃ l0, a.1 ∈ B l0 ∧ b.1 ∈ B l0 := by
            by_contra hno; push Not at hno
            exact hna ⟨fun e => hab_ne (Subtype.ext e), fun l ⟨h1, h2⟩ => hno l h1 h2⟩
          obtain ⟨l0, ha0, hb0⟩ := hcov
          have h4 := card_common_holes_of_covered B hp hsize hmeet (fun e => hab_ne (Subtype.ext e)) ha0 hb0
          rw [(mem_filter.mp a.2).2, (mem_filter.mp b.2).2] at h4
          omega
        calc
          4 * (C.card * C'.card) = ∑ _a ∈ C, ∑ _b ∈ C', 4 := by simp; ring
          _ = _ := sum_congr rfl fun a ha => sum_congr rfl fun b hb => (heach a ha b hb).symm
      rw [hlhs]
      have hswap : ∑ a ∈ C, ∑ b ∈ C', (holeNbrs B a.1 ∩ holeNbrs B b.1 ∩ High).card =
          ∑ h ∈ High, ∑ a ∈ C, ∑ b ∈ C', if h ∈ holeNbrs B a.1 ∧ h ∈ holeNbrs B b.1 then 1 else 0 := by
        have hstep1 : ∀ a ∈ C, ∀ b ∈ C', (holeNbrs B a.1 ∩ holeNbrs B b.1 ∩ High).card =
            ∑ h ∈ High, if h ∈ holeNbrs B a.1 ∧ h ∈ holeNbrs B b.1 then 1 else 0 := by
          intro a _ b _
          rw [sum_boole, Nat.cast_id]; congr 1; ext h; simp [and_comm, and_assoc]
        calc
          _ = ∑ a ∈ C, ∑ b ∈ C', ∑ h ∈ High, if h ∈ holeNbrs B a.1 ∧ h ∈ holeNbrs B b.1 then 1 else 0 :=
            sum_congr rfl fun a ha => sum_congr rfl fun b hb => hstep1 a ha b hb
          _ = ∑ a ∈ C, ∑ h ∈ High, ∑ b ∈ C', if h ∈ holeNbrs B a.1 ∧ h ∈ holeNbrs B b.1 then 1 else 0 :=
            sum_congr rfl fun _ _ => Finset.sum_comm
          _ = _ := Finset.sum_comm
      rw [hswap]
      apply sum_congr rfl; intro h _
      have hfac : (∑ a ∈ C, ∑ b ∈ C', if h ∈ holeNbrs B a.1 ∧ h ∈ holeNbrs B b.1 then 1 else 0) =
          (∑ a ∈ C, if h ∈ holeNbrs B a.1 then 1 else 0) *
          (∑ b ∈ C', if h ∈ holeNbrs B b.1 then 1 else 0) := by
        rw [Finset.sum_mul_sum]
        apply sum_congr rfl; intro a _; apply sum_congr rfl; intro b _
        by_cases h1 : h ∈ holeNbrs B a.1 <;> by_cases h2 : h ∈ holeNbrs B b.1 <;> simp [h1, h2]
      rw [hfac]
      have hbij (S : Finset {p : P // p ∈ R}) :
          (∑ a ∈ S, if h ∈ holeNbrs B a.1 then 1 else 0) = (holeNbrs B h ∩ S.image Subtype.val).card := by
        rw [sum_boole, Nat.cast_id]
        refine Finset.card_bij (fun a _ => a.1) ?_ (fun _ _ _ _ e => Subtype.ext e) ?_
        · intro a ha
          have ⟨haS, hah⟩ := mem_filter.mp ha
          have hha : a.1 ∈ holeNbrs B h := by
            rw [mem_holeNbrs]; have ⟨hne, hnl⟩ := mem_holeNbrs.mp hah
            exact ⟨hne.symm, fun l ⟨h1, h2⟩ => hnl l ⟨h2, h1⟩⟩
          exact mem_inter.mpr ⟨hha, mem_image_of_mem _ haS⟩
        · intro x hx
          have ⟨hxh, hxS⟩ := mem_inter.mp hx
          obtain ⟨a, haS, rfl⟩ := mem_image.mp hxS
          have hah : h ∈ holeNbrs B a.1 := by
            rw [mem_holeNbrs]; have ⟨hne, hnl⟩ := mem_holeNbrs.mp hxh
            exact ⟨hne.symm, fun l ⟨h1, h2⟩ => hnl l ⟨h2, h1⟩⟩
          exact ⟨a, mem_filter.mpr ⟨haS, hah⟩, rfl⟩
      rw [hbij C, hbij C']
    -- Upper bound each high point's contribution by (12j - m_j)^2 / 4.
    have hhigh_ub : ∑ h ∈ High, (holeNbrs B h ∩ CP).card * (holeNbrs B h ∩ CP').card ≤
        u3 + u4 + u5 + u6 := by
      have hpartH : ∀ h ∈ High,
          (holeNbrs B h ∩ CP).card * (holeNbrs B h ∩ CP').card ≤
            (if defic B h = 3 then (36 - minHighNeighbors n3 n4 n5 n6 3) ^ 2 / 4 else 0) +
            (if defic B h = 4 then (48 - minHighNeighbors n3 n4 n5 n6 4) ^ 2 / 4 else 0) +
            (if defic B h = 5 then (60 - minHighNeighbors n3 n4 n5 n6 5) ^ 2 / 4 else 0) +
            (if defic B h = 6 then (72 - minHighNeighbors n3 n4 n5 n6 6) ^ 2 / 4 else 0) := by
        intro h hh
        have h3ge := (mem_filter.mp hh).2
        have hsum_root : (holeNbrs B h ∩ CP).card + (holeNbrs B h ∩ CP').card ≤ (holeNbrs B h ∩ R).card := by
          rw [← card_union_of_disjoint (hCP_disj.mono inter_subset_right inter_subset_right), ← inter_union_distrib_left]
          exact card_le_card (inter_subset_inter_left hCP_sub_R)
        have hmul_le (a b s : ℕ) (hab : a + b ≤ s) : a * b ≤ s ^ 2 / 4 := by
          have h4z : (4 * (a * b) : ℤ) ≤ (s : ℤ) ^ 2 := by
            have habz : (a : ℤ) + b ≤ s := by exact_mod_cast hab
            nlinarith [sq_nonneg ((a : ℤ) - b)]
          have h4 : 4 * (a * b) ≤ s ^ 2 := by exact_mod_cast h4z
          omega
        have hclass (j : ℕ) (hj3 : 3 ≤ j) (hj6 : j ≤ 6) (hdj : defic B h = (j : ℤ)) :
            (holeNbrs B h ∩ CP).card * (holeNbrs B h ∩ CP').card ≤
              (12 * j - minHighNeighbors n3 n4 n5 n6 j) ^ 2 / 4 := by
          have ⟨hsum, hb3, hb4, hb5, hb6, htot⟩ := hlocal_budget h j hdj (by omega) (by omega)
          have hmin := minHighNeighbors_le hb3 hb4 hb5 hb6 hsum
          exact hmul_le _ _ _ (by omega)
        rcases hdef_cases h with h0 | h2 | h3 | h4 | h5 | h6
        · omega
        · omega
        · simpa [h3] using hclass 3 (by omega) (by omega) h3
        · simpa [h4] using hclass 4 (by omega) (by omega) h4
        · simpa [h5] using hclass 5 (by omega) (by omega) h5
        · simpa [h6] using hclass 6 (by omega) (by omega) h6
      have hsum_le := sum_le_sum hpartH
      simp only [sum_add_distrib] at hsum_le
      have hite (j : ℤ) (hj3 : 3 ≤ j) (v : ℕ) :
          ∑ h ∈ High, (if defic B h = j then v else 0) =
            if (D j).card == 0 then 0 else (D j).card * v := by
        rw [← sum_filter, sum_const, smul_eq_mul]
        have hfilt : High.filter (fun h => defic B h = j) = D j := by
          ext h; simp only [High, D, mem_filter, mem_univ, true_and]
          exact ⟨fun ⟨_, e⟩ => e, fun e => ⟨by omega, e⟩⟩
        rw [hfilt]
        by_cases h0 : (D j).card = 0 <;> simp [h0]
      rw [hite 3 (by omega), hite 4 (by omega), hite 5 (by omega), hite 6 (by omega)] at hsum_le
      exact hsum_le
    have h4z : 4 * z * (R.card - z) ≤ 4 * (C.card * (R.card - C.card)) := by
      rw [mul_assoc]; exact Nat.mul_le_mul_left 4 hquad
    rw [hC'_card] at h4cross
    omega
  exact ⟨hexcess_nat, hmass_nat, hn2_ge81, fun p => hk16.trans (hdeg_root p),
    hcomm_adj, hcomm_nonadj, hconnR⟩

end RootGraph

/-! ## Section 4: Complete 139-block completion theorem (`new_block_of_139`) -/

section Main139

variable {P L : Type*} [Fintype P] [Fintype L] [DecidableEq P] [DecidableEq L]

private lemma bool_true_of_ne_false {a b : Bool} (hne : a ≠ b) (ha : a = false) : b = true := by
  cases b
  · exact absurd ha hne
  · rfl

private lemma bool_false_of_ne_true {a b : Bool} (hne : a ≠ b) (ha : a = true) : b = false := by
  cases b
  · rfl
  · exact absurd ha hne

private lemma bool_eq_true_of_ne_false {a : Bool} (ha : a ≠ false) : a = true := by
  cases a
  · exact absurd rfl ha
  · rfl

/-- Standalone `K_{9,9}` completion lemma: given the 81-root `K_{9,9}` orthonormal frame
`E σ i`, `F σ j` (for `σ ∈ {1, -1}`), classifies all 24 deficit-3 high points, eliminates
reflections via `no_small_mod3_reflection`, and extracts the 140th block. -/
private theorem new_block_of_139_k99
    (B : L → Finset P) (hp : Fintype.card P = 157) (hl : Fintype.card L = 139)
    (hsize : ∀ l, (B l).card = 13)
    (hmeet : ∀ l m, l ≠ m → (B l ∩ B m).card = 1)
    (h12 : ∀ p, deg B p ≠ 12)
    (hn3_24 : (univ.filter fun p => defic B p = 3).card = 24)
    (hn4_0 : (univ.filter fun p => defic B p = 4).card = 0)
    (hn5_0 : (univ.filter fun p => defic B p = 5).card = 0)
    (hn6_0 : (univ.filter fun p => defic B p = 6).card = 0)
    (rootOf : Fin 9 → Fin 9 → { p : P // p ∈ univ.filter fun p => defic B p = 2 })
    (hrootOf_bij : ∀ p : { p : P // p ∈ univ.filter fun p => defic B p = 2 },
      ∃! ij : Fin 9 × Fin 9, rootOf ij.1 ij.2 = p)
    (e0 : P → ℝ) (Ei0 Fj0 : Fin 9 → P → ℝ)
    (he0_norm : Order12.Deficit18Frame.dot e0 e0 = 1)
    (hEi0_e0 : ∀ i, Order12.Deficit18Frame.dot (Ei0 i) e0 = 0)
    (hFj0_e0 : ∀ j, Order12.Deficit18Frame.dot (Fj0 j) e0 = 0)
    (E F : ℝ → Fin 9 → P → ℝ)
    (hE_def : ∀ σ i, E σ i = Ei0 i + (σ / Real.sqrt 18) • e0)
    (hF_def : ∀ σ j, F σ j = Fj0 j - (σ / Real.sqrt 18) • e0)
    (hEF_edge : ∀ σ i j, E σ i + F σ j = uVec B (rootOf i j).1)
    (hEF_mem : ∀ σ, (∀ i, E σ i ∈ LinearMap.range (projLin B)) ∧
      (∀ j, F σ j ∈ LinearMap.range (projLin B)))
    (hEF_orth : ∀ σ, σ ^ 2 = 1 →
      (∀ i i', Order12.Deficit18Frame.dot (E σ i) (E σ i') = if i = i' then 1 else 0) ∧
      (∀ j j', Order12.Deficit18Frame.dot (F σ j) (F σ j') = if j = j' then 1 else 0) ∧
      (∀ i j, Order12.Deficit18Frame.dot (E σ i) (F σ j) = 0))
    (hEF_V : ∀ σ i, Order12.Deficit18Frame.dot (vVec B) (E σ i) = 1)
    (hparseval_orth : ∀ x ∈ LinearMap.range (projLin B),
      (∀ i j : Fin 9, Order12.Deficit18Frame.dot x (uVec B (rootOf i j).1) = 0) →
      x = Order12.Deficit18Frame.dot x e0 • e0) :
    ∃ N : Finset P, N.card = 13 ∧ ∀ l, (N ∩ B l).card = 1 := by
  classical
  let R := univ.filter fun p => defic B p = 2
  let RSub := { p : P // p ∈ R }
  have hsqrt18_ne : Real.sqrt 18 ≠ 0 := by positivity
  have hsq18 : Real.sqrt 18 ^ 2 = 18 := Real.sq_sqrt (by norm_num)
  have hproj_of_range : ∀ x ∈ LinearMap.range (projLin B), proj B x = x := by
    rintro _ ⟨y, rfl⟩; exact proj_idem B hp hsize hmeet y
  let High3 := univ.filter fun p : P => defic B p = 3
  have hall_def : ∀ p : P, defic B p = 0 ∨ defic B p = 2 ∨ defic B p = 3 := by
    intro p
    have hle13 := deg_le_13 B hp hsize hmeet p
    have hne12 := h12 p
    have hle6 := defic_le_6_of_no_deg12 B hp hl hsize hmeet h12 p
    have hne4 : defic B p ≠ 4 := fun h => by
      have : 0 < (univ.filter fun q => defic B q = 4).card := card_pos.mpr ⟨p, mem_filter.mpr ⟨mem_univ _, h⟩⟩
      omega
    have hne5 : defic B p ≠ 5 := fun h => by
      have : 0 < (univ.filter fun q => defic B q = 5).card := card_pos.mpr ⟨p, mem_filter.mpr ⟨mem_univ _, h⟩⟩
      omega
    have hne6 : defic B p ≠ 6 := fun h => by
      have : 0 < (univ.filter fun q => defic B q = 6).card := card_pos.mpr ⟨p, mem_filter.mpr ⟨mem_univ _, h⟩⟩
      omega
    dsimp [defic] at hle6 hne4 hne5 hne6 ⊢; omega
  have horth1 := hEF_orth 1 (by norm_num)
  have hhigh_class : ∀ h ∈ High3,
      (∃ Rh : Finset (Fin 9), Rh.card = 3 ∧
        (uVec B h = ∑ i ∈ Rh, E 1 i ∨ uVec B h = ∑ i ∈ Rh, E (-1) i)) ∨
      (∃ Ch : Finset (Fin 9), Ch.card = 3 ∧
        (uVec B h = ∑ j ∈ Ch, F 1 j ∨ uVec B h = ∑ j ∈ Ch, F (-1) j)) := by
    intro h hh
    have hd3 : defic B h = 3 := (mem_filter.mp hh).2
    have hdeg10 : deg B h = 10 := by dsimp [defic] at hd3; omega
    have hroot_cnt : (holeNbrs B h ∩ R).card = 27 := by
      have htot := card_holeNbrs B hp hsize hmeet h
      rw [hdeg10] at htot
      have hbud := hole_neighbor_budget_139 B hp hl hsize hmeet h
      rw [hd3] at hbud
      have hsplit_h : ∀ q ∈ holeNbrs B h, defic B q = 2 ∨ defic B q = 3 := by
        intro q hq
        rcases hall_def q with h0 | h2 | h3
        · exfalso
          have hdeg13 : deg B q = 13 := by dsimp [defic] at h0; omega
          have hc := card_holeNbrs B hp hsize hmeet q
          rw [hdeg13] at hc
          have hhq : h ∈ holeNbrs B q := by
            rw [mem_holeNbrs]; have ⟨hne, hnl⟩ := mem_holeNbrs.mp hq
            exact ⟨hne.symm, fun l ⟨h1, h2⟩ => hnl l ⟨h2, h1⟩⟩
          have := card_pos.mpr ⟨h, hhq⟩; omega
        · exact Or.inl h2
        · exact Or.inr h3
      have ha3 : ((holeNbrs B h).filter fun q => defic B q = 3).card = 9 := by
        have : ∑ q ∈ holeNbrs B h, (defic B q - 2) =
            (((holeNbrs B h).filter fun q => defic B q = 3).card : ℤ) := by
          have h1 : ∀ q ∈ holeNbrs B h, defic B q - 2 = if defic B q = 3 then (1 : ℤ) else 0 := by
            intro q hq; rcases hsplit_h q hq with h2 | h2 <;> simp [h2]
          rw [sum_congr rfl h1, sum_boole]
        rw [this] at hbud; omega
      have hpart : (holeNbrs B h ∩ R).card + ((holeNbrs B h).filter fun q => defic B q = 3).card = 36 := by
        have hdisj : Disjoint (holeNbrs B h ∩ R) ((holeNbrs B h).filter fun q => defic B q = 3) := by
          apply Finset.disjoint_left.mpr; intro q h1 h2
          have c1 := (mem_filter.mp (mem_inter.mp h1).2).2
          have c2 := (mem_filter.mp h2).2
          omega
        have hunion : (holeNbrs B h ∩ R) ∪ ((holeNbrs B h).filter fun q => defic B q = 3) = holeNbrs B h := by
          ext q; simp only [mem_union, mem_inter, mem_filter, mem_univ, true_and, R]
          constructor
          · rintro (⟨hq, _⟩ | ⟨hq, _⟩) <;> exact hq
          · intro hq; rcases hsplit_h q hq with h2 | h3
            · exact Or.inl ⟨hq, h2⟩
            · exact Or.inr ⟨hq, h3⟩
        rw [← card_union_of_disjoint hdisj, hunion, htot]
      omega
    let r : Fin 9 → ℝ := fun i => Order12.Deficit18Frame.dot (uVec B h) (E 1 i)
    let c : Fin 9 → ℝ := fun j => Order12.Deficit18Frame.dot (uVec B h) (F 1 j)
    have hrc_dot : ∀ i j : Fin 9, r i + c j = Order12.Deficit18Frame.dot (uVec B h) (uVec B (rootOf i j).1) := by
      intro i j; dsimp [r, c]; rw [← Order12.Deficit18Frame.dot_add_right, hEF_edge 1 i j]
    have hrc_01 : ∀ i j : Fin 9, r i + c j = 0 ∨ r i + c j = 1 := by
      intro i j; rw [hrc_dot i j]
      have hne : h ≠ (rootOf i j).1 := fun e => by
        have h2 := (mem_filter.mp (rootOf i j).2).2; rw [← e, hd3] at h2; omega
      rw [dot_uVec_ne B hp hsize hmeet hne]; split_ifs <;> simp
    have hrc_sum : ∑ i : Fin 9, ∑ j : Fin 9, (r i + c j) = 27 := by
      simp_rw [hrc_dot]
      rw [← Fintype.sum_prod_type']
      have hsum_R : ∑ ij : Fin 9 × Fin 9, Order12.Deficit18Frame.dot (uVec B h) (uVec B (rootOf ij.1 ij.2).1) =
          ∑ p : RSub, Order12.Deficit18Frame.dot (uVec B h) (uVec B p.1) := by
        refine Finset.sum_bij (fun ij _ => rootOf ij.1 ij.2) (fun _ _ => mem_univ _) ?_ ?_ (fun _ _ => rfl)
        · intro ij1 _ ij2 _ heq
          exact (hrootOf_bij (rootOf ij2.1 ij2.2)).unique heq rfl
        · intro p _
          obtain ⟨ij, hij, _⟩ := hrootOf_bij p
          exact ⟨ij, mem_univ _, hij⟩
      rw [hsum_R]
      have hterm : ∀ p : RSub, Order12.Deficit18Frame.dot (uVec B h) (uVec B p.1) =
          if p.1 ∈ holeNbrs B h then 1 else 0 := by
        intro p
        have hne : h ≠ p.1 := fun e => by have h2 := (mem_filter.mp p.2).2; rw [← e, hd3] at h2; omega
        rw [dot_uVec_ne B hp hsize hmeet hne]
        by_cases hcov : ∃ l, h ∈ B l ∧ p.1 ∈ B l
        · rw [if_pos hcov, if_neg]
          intro hh'; obtain ⟨l, h1, h2⟩ := hcov; exact (mem_holeNbrs.mp hh').2 l ⟨h1, h2⟩
        · rw [if_neg hcov, if_pos]
          exact mem_holeNbrs.mpr ⟨hne, fun l h12 => hcov ⟨l, h12⟩⟩
      simp_rw [hterm, sum_boole]
      have hcard : (univ.filter fun p : RSub => p.1 ∈ holeNbrs B h).card = (holeNbrs B h ∩ R).card := by
        refine Finset.card_bij (fun p _ => p.1) ?_ (fun _ _ _ _ e => Subtype.ext e) ?_
        · intro p hp; exact mem_inter.mpr ⟨(mem_filter.mp hp).2, p.2⟩
        · intro q hq; have ⟨hq1, hq2⟩ := mem_inter.mp hq
          exact ⟨⟨q, hq2⟩, mem_filter.mpr ⟨mem_univ _, hq1⟩, rfl⟩
      rw [hcard, hroot_cnt]; norm_num
    have hnorm_h : Order12.Deficit18Frame.dot (uVec B h) (uVec B h) = 3 := by
      rw [dot_uVec_self B hp hsize hmeet h]; dsimp [deg] at hdeg10; rw [hdeg10]; norm_num
    rcases k99_matrix_three_rows_or_cols r c hrc_01 hrc_sum with ⟨Rh, hRh_card, hRh_val⟩ | ⟨Ch, hCh_card, hCh_val⟩
    · left; refine ⟨Rh, hRh_card, ?_⟩
      let v1 := ∑ i ∈ Rh, E 1 i
      have hv1_mem : v1 ∈ LinearMap.range (projLin B) := Submodule.sum_mem _ fun i _ => (hEF_mem 1).1 i
      have hv1_norm : Order12.Deficit18Frame.dot v1 v1 = 3 := by
        dsimp [v1]; rw [Order12.Deficit18Frame.dot_sum_left]
        have h1 : ∀ i ∈ Rh, Order12.Deficit18Frame.dot (E 1 i) (∑ i' ∈ Rh, E 1 i') = 1 := by
          intro i hi; rw [Order12.Deficit18Frame.dot_sum_right]
          simp [horth1.1, hi]
        rw [sum_congr rfl h1, sum_const, hRh_card]; norm_num
      have hv1_e0 : Order12.Deficit18Frame.dot v1 e0 = 3 / Real.sqrt 18 := by
        dsimp [v1]; rw [Order12.Deficit18Frame.dot_sum_left]
        have h1 : ∀ i ∈ Rh, Order12.Deficit18Frame.dot (E 1 i) e0 = 1 / Real.sqrt 18 := by
          intro i _; rw [hE_def 1 i, Order12.Deficit18Frame.dot_add_left,
            Order12.Deficit18Frame.dot_smul_left, hEi0_e0 i, he0_norm]; ring
        rw [sum_congr rfl h1, sum_const, hRh_card, nsmul_eq_mul]; ring
      have hdiff_perp : ∀ i j : Fin 9,
          Order12.Deficit18Frame.dot (uVec B h - v1) (uVec B (rootOf i j).1) = 0 := by
        intro i j
        rw [Order12.Deficit18Frame.dot_sub_left, ← hrc_dot i j, hRh_val i j, ← hEF_edge 1 i j]
        dsimp [v1]
        rw [Order12.Deficit18Frame.dot_add_right, Order12.Deficit18Frame.dot_sum_left,
          Order12.Deficit18Frame.dot_sum_left]
        have h1 : ∑ k ∈ Rh, Order12.Deficit18Frame.dot (E 1 k) (E 1 i) = if i ∈ Rh then 1 else 0 := by
          simp [horth1.1]
        have h2 : ∑ k ∈ Rh, Order12.Deficit18Frame.dot (E 1 k) (F 1 j) = 0 :=
          sum_eq_zero fun k _ => horth1.2.2 k j
        rw [h1, h2]; ring
      have hlam := hparseval_orth (uVec B h - v1)
        (Submodule.sub_mem _ ⟨T (basisE h), rfl⟩ hv1_mem) hdiff_perp
      set lam := Order12.Deficit18Frame.dot (uVec B h - v1) e0
      have huh_eq : uVec B h = v1 + lam • e0 := by
        ext p; have := congrFun hlam p
        simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this ⊢; linarith
      have hquad_lam : lam * (lam + 6 / Real.sqrt 18) = 0 := by
        have h3 := hnorm_h
        rw [huh_eq, Order12.Deficit18Frame.dot_add_left, Order12.Deficit18Frame.dot_add_right,
          Order12.Deficit18Frame.dot_add_right, Order12.Deficit18Frame.dot_smul_left,
          Order12.Deficit18Frame.dot_smul_right, Order12.Deficit18Frame.dot_smul_left,
          Order12.Deficit18Frame.dot_smul_right, Order12.Deficit18Frame.dot_comm e0 v1,
          hv1_norm, hv1_e0, he0_norm] at h3
        linear_combination h3
      rcases mul_eq_zero.mp hquad_lam with h0 | hneg
      · left; rw [huh_eq, h0, zero_smul, add_zero]
      · right
        have hlam_val : lam = -(6 / Real.sqrt 18) := by linarith
        rw [huh_eq, hlam_val]
        have hdiff_E : ∑ i ∈ Rh, E (-1) i = v1 + (-(6 / Real.sqrt 18)) • e0 := by
          dsimp [v1]; simp_rw [hE_def]
          ext p
          simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          rw [sum_add_distrib, sum_add_distrib, sum_const, sum_const, hRh_card, nsmul_eq_mul, nsmul_eq_mul]
          ring
        exact hdiff_E.symm
    · right; refine ⟨Ch, hCh_card, ?_⟩
      let v1 := ∑ j ∈ Ch, F 1 j
      have hv1_mem : v1 ∈ LinearMap.range (projLin B) := Submodule.sum_mem _ fun j _ => (hEF_mem 1).2 j
      have hv1_norm : Order12.Deficit18Frame.dot v1 v1 = 3 := by
        dsimp [v1]; rw [Order12.Deficit18Frame.dot_sum_left]
        have h1 : ∀ j ∈ Ch, Order12.Deficit18Frame.dot (F 1 j) (∑ j' ∈ Ch, F 1 j') = 1 := by
          intro j hj; rw [Order12.Deficit18Frame.dot_sum_right]
          simp [horth1.2.1, hj]
        rw [sum_congr rfl h1, sum_const, hCh_card]; norm_num
      have hv1_e0 : Order12.Deficit18Frame.dot v1 e0 = -(3 / Real.sqrt 18) := by
        dsimp [v1]; rw [Order12.Deficit18Frame.dot_sum_left]
        have h1 : ∀ j ∈ Ch, Order12.Deficit18Frame.dot (F 1 j) e0 = -(1 / Real.sqrt 18) := by
          intro j _; rw [hF_def 1 j, Order12.Deficit18Frame.dot_sub_left,
            Order12.Deficit18Frame.dot_smul_left, hFj0_e0 j, he0_norm]; ring
        rw [sum_congr rfl h1, sum_const, hCh_card, nsmul_eq_mul]; ring
      have hdiff_perp : ∀ i j : Fin 9,
          Order12.Deficit18Frame.dot (uVec B h - v1) (uVec B (rootOf i j).1) = 0 := by
        intro i j
        rw [Order12.Deficit18Frame.dot_sub_left, ← hrc_dot i j, hCh_val i j, ← hEF_edge 1 i j]
        dsimp [v1]
        rw [Order12.Deficit18Frame.dot_add_right, Order12.Deficit18Frame.dot_sum_left,
          Order12.Deficit18Frame.dot_sum_left]
        have h1 : ∑ k ∈ Ch, Order12.Deficit18Frame.dot (F 1 k) (E 1 i) = 0 :=
          sum_eq_zero fun k _ => by rw [Order12.Deficit18Frame.dot_comm]; exact horth1.2.2 i k
        have h2 : ∑ k ∈ Ch, Order12.Deficit18Frame.dot (F 1 k) (F 1 j) = if j ∈ Ch then 1 else 0 := by
          simp [horth1.2.1]
        rw [h1, h2]; ring
      have hlam := hparseval_orth (uVec B h - v1)
        (Submodule.sub_mem _ ⟨T (basisE h), rfl⟩ hv1_mem) hdiff_perp
      set lam := Order12.Deficit18Frame.dot (uVec B h - v1) e0
      have huh_eq : uVec B h = v1 + lam • e0 := by
        ext p; have := congrFun hlam p
        simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this ⊢; linarith
      have hquad_lam : lam * (lam - 6 / Real.sqrt 18) = 0 := by
        have h3 := hnorm_h
        rw [huh_eq, Order12.Deficit18Frame.dot_add_left, Order12.Deficit18Frame.dot_add_right,
          Order12.Deficit18Frame.dot_add_right, Order12.Deficit18Frame.dot_smul_left,
          Order12.Deficit18Frame.dot_smul_right, Order12.Deficit18Frame.dot_smul_left,
          Order12.Deficit18Frame.dot_smul_right, Order12.Deficit18Frame.dot_comm e0 v1,
          hv1_norm, hv1_e0, he0_norm] at h3
        linear_combination h3
      rcases mul_eq_zero.mp hquad_lam with h0 | hpos
      · left; rw [huh_eq, h0, zero_smul, add_zero]
      · right
        have hlam_val : lam = 6 / Real.sqrt 18 := by linarith
        rw [huh_eq, hlam_val]
        have hdiff_F : ∑ j ∈ Ch, F (-1) j = v1 + (6 / Real.sqrt 18) • e0 := by
          dsimp [v1]; simp_rw [hF_def]
          ext p
          simp only [Finset.sum_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
          rw [sum_sub_distrib, sum_sub_distrib, sum_const, sum_const, hCh_card, nsmul_eq_mul, nsmul_eq_mul]
          ring
        exact hdiff_F.symm
  -- Choose σ ∈ {1, -1} so at most 12 of the 24 high points are reflected.
  let isUnrefl : ℝ → P → Prop := fun σ h =>
    (∃ Rh : Finset (Fin 9), Rh.card = 3 ∧ uVec B h = ∑ i ∈ Rh, E σ i) ∨
    (∃ Ch : Finset (Fin 9), Ch.card = 3 ∧ uVec B h = ∑ j ∈ Ch, F σ j)
  have hsplit_high : ∀ h ∈ High3, isUnrefl 1 h ∨ isUnrefl (-1) h := by
    intro h hh
    rcases hhigh_class h hh with ⟨Rh, hc, h1 | h2⟩ | ⟨Ch, hc, h1 | h2⟩
    · exact Or.inl (Or.inl ⟨Rh, hc, h1⟩)
    · exact Or.inr (Or.inl ⟨Rh, hc, h2⟩)
    · exact Or.inl (Or.inr ⟨Ch, hc, h1⟩)
    · exact Or.inr (Or.inr ⟨Ch, hc, h2⟩)
  let U1set := High3.filter (isUnrefl 1)
  let σ : ℝ := if U1set.card ≥ 12 then 1 else -1
  have hσ2 : σ ^ 2 = 1 := by dsimp [σ]; split_ifs <;> norm_num
  have hrefl_le12 : (High3.filter fun h => ¬ isUnrefl σ h).card ≤ 12 := by
    dsimp [σ]
    split_ifs with hge12
    · have hc := card_filter_add_card_filter_not (s := High3) (p := isUnrefl 1)
      have h24 : High3.card = 24 := hn3_24
      dsimp [U1set] at hge12; omega
    · have hsub : High3.filter (fun h => ¬ isUnrefl (-1) h) ⊆ U1set := by
        intro h hh
        have ⟨hhH, hnot⟩ := mem_filter.mp hh
        exact mem_filter.mpr ⟨hhH, (hsplit_high h hhH).resolve_right hnot⟩
      have hc := card_le_card hsub
      omega
  have horth_σ := hEF_orth σ hσ2
  have hE_neg_dot : ∀ i : Fin 9,
      Order12.Deficit18Frame.dot (E (-σ) i) (E σ 0) = (if i = 0 then 1 else 0) - 1 / 9 := by
    intro i
    have hdiff : E (-σ) i = E σ i - (2 * σ / Real.sqrt 18) • e0 := by
      rw [hE_def, hE_def]; ext p; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [hdiff, Order12.Deficit18Frame.dot_sub_left, Order12.Deficit18Frame.dot_smul_left, horth_σ.1 i 0]
    have hd_e0 : Order12.Deficit18Frame.dot e0 (E σ 0) = σ / Real.sqrt 18 := by
      rw [hE_def, Order12.Deficit18Frame.dot_add_right, Order12.Deficit18Frame.dot_smul_right,
        Order12.Deficit18Frame.dot_comm e0 (Ei0 0), hEi0_e0 0, he0_norm]; ring
    rw [hd_e0]
    have hfrac : 2 * σ / Real.sqrt 18 * (σ / Real.sqrt 18) = 1 / 9 := by
      field_simp [hsqrt18_ne]; rw [hσ2, hsq18]; ring
    linarith
  have hF_neg_dot : ∀ j : Fin 9,
      Order12.Deficit18Frame.dot (F (-σ) j) (E σ 0) = 1 / 9 := by
    intro j
    have hdiff : F (-σ) j = F σ j + (2 * σ / Real.sqrt 18) • e0 := by
      rw [hF_def, hF_def]; ext p; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [hdiff, Order12.Deficit18Frame.dot_add_left, Order12.Deficit18Frame.dot_smul_left,
      Order12.Deficit18Frame.dot_comm (F σ j) (E σ 0), horth_σ.2.2 0 j, zero_add]
    have hd_e0 : Order12.Deficit18Frame.dot e0 (E σ 0) = σ / Real.sqrt 18 := by
      rw [hE_def, Order12.Deficit18Frame.dot_add_right, Order12.Deficit18Frame.dot_smul_right,
        Order12.Deficit18Frame.dot_comm e0 (Ei0 0), hEi0_e0 0, he0_norm]; ring
    rw [hd_e0]
    field_simp [hsqrt18_ne]; rw [hσ2, hsq18]; ring
  have hq_form : ∀ q : P,
      (Order12.Deficit18Frame.dot (uVec B q) (E σ 0) = 0 ∨
       Order12.Deficit18Frame.dot (uVec B q) (E σ 0) = 1) ∨
      (q ∈ High3 ∧ ¬ isUnrefl σ q ∧
       ∃ (m : ℤ) (t : ℤ), (t = -1 ∨ t = 1) ∧
         Order12.Deficit18Frame.dot (uVec B q) (E σ 0) = (m : ℝ) + (t : ℝ) / 3) := by
    intro q
    rcases hall_def q with h0 | h2 | h3
    · left; left
      have hu0 : uVec B q = 0 := by
        apply Order12.Deficit18Frame.dot_self_eq_zero.mp
        rw [dot_uVec_self B hp hsize hmeet q]
        dsimp [defic, deg] at h0
        have : (univ.filter fun l => q ∈ B l).card = 13 := by omega
        rw [this]; norm_num
      rw [hu0, Order12.Deficit18Frame.dot_zero_left]
    · left
      have hqR : q ∈ R := mem_filter.mpr ⟨mem_univ _, h2⟩
      obtain ⟨⟨i, j⟩, hij, _⟩ := hrootOf_bij ⟨q, hqR⟩
      have huq : uVec B q = E σ i + F σ j := by rw [hEF_edge σ i j, hij]
      rw [huq, Order12.Deficit18Frame.dot_add_left, horth_σ.1 i 0,
        Order12.Deficit18Frame.dot_comm (F σ j) (E σ 0), horth_σ.2.2 0 j, add_zero]
      by_cases e : i = 0 <;> simp [e]
    · have hqH : q ∈ High3 := mem_filter.mpr ⟨mem_univ _, h3⟩
      by_cases hu : isUnrefl σ q
      · left
        rcases hu with ⟨Rh, _, heq⟩ | ⟨Ch, _, heq⟩
        · rw [heq, Order12.Deficit18Frame.dot_sum_left]
          simp [horth_σ.1]
          exact (Classical.em ((0 : Fin 9) ∈ Rh)).symm
        · left
          rw [heq, Order12.Deficit18Frame.dot_sum_left]
          exact sum_eq_zero fun j _ => by rw [Order12.Deficit18Frame.dot_comm]; exact horth_σ.2.2 0 j
      · right
        have hrefl : isUnrefl (-σ) q := by
          dsimp [σ] at hu ⊢
          split_ifs at hu ⊢
          · exact (hsplit_high q hqH).resolve_left hu
          · simpa using (hsplit_high q hqH).resolve_right hu
        refine ⟨hqH, hu, ?_⟩
        rcases hrefl with ⟨Rh, hRh_card, heq⟩ | ⟨Ch, hCh_card, heq⟩
        · rw [heq, Order12.Deficit18Frame.dot_sum_left]
          simp_rw [hE_neg_dot]
          rw [sum_sub_distrib, sum_ite_eq', sum_const, hRh_card, nsmul_eq_mul]
          refine ⟨if (0 : Fin 9) ∈ Rh then 1 else 0, -1, Or.inl rfl, ?_⟩
          by_cases h0 : (0 : Fin 9) ∈ Rh <;> simp [h0] <;> ring
        · rw [heq, Order12.Deficit18Frame.dot_sum_left]
          simp_rw [hF_neg_dot, sum_const, hCh_card, nsmul_eq_mul]
          refine ⟨0, 1, Or.inr rfl, ?_⟩; ring
  -- Define reflection sign sR : P → ℤ cleanly without Prop-to-Type elimination.
  let sR : P → ℤ := fun q =>
    if ∃ m : ℤ, Order12.Deficit18Frame.dot (uVec B q) (E σ 0) = (m : ℝ) + 1 / 3 then 1
    else if ∃ m : ℤ, Order12.Deficit18Frame.dot (uVec B q) (E σ 0) = (m : ℝ) + (-1 : ℝ) / 3 then -1
    else 0
  have hno_int_third : ∀ (z m : ℤ) (t : ℤ), (t = -1 ∨ t = 1) →
      (z : ℝ) ≠ (m : ℝ) + (t : ℝ) / 3 := by
    intro z m t ht h
    rcases ht with rfl | rfl
    · have h3 : ((3 * (z - m) : ℤ) : ℝ) = ((-1 : ℤ) : ℝ) := by push_cast; linarith
      have h3z : 3 * (z - m) = -1 := by exact_mod_cast h3
      omega
    · have h3 : ((3 * (z - m) : ℤ) : ℝ) = ((1 : ℤ) : ℝ) := by push_cast; linarith
      have h3z : 3 * (z - m) = 1 := by exact_mod_cast h3
      omega
  have hno_pos_neg_third : ∀ (m1 m2 : ℤ),
      (m1 : ℝ) + 1 / 3 ≠ (m2 : ℝ) + (-1 : ℝ) / 3 := by
    intro m1 m2 h
    have h3 : ((3 * (m1 - m2) : ℤ) : ℝ) = ((-2 : ℤ) : ℝ) := by push_cast; linarith
    have h3z : 3 * (m1 - m2) = -2 := by exact_mod_cast h3
    omega
  have hsR_spec : ∀ q : P, (sR q = -1 ∨ sR q = 0 ∨ sR q = 1) ∧
      ∃ m : ℤ, Order12.Deficit18Frame.dot (uVec B q) (E σ 0) = (m : ℝ) + (sR q : ℝ) / 3 := by
    intro q
    dsimp [sR]
    split_ifs with h1 h2
    · obtain ⟨m, hm⟩ := h1
      exact ⟨Or.inr (Or.inr rfl), m, by simpa using hm⟩
    · obtain ⟨m, hm⟩ := h2
      exact ⟨Or.inl rfl, m, by simpa using hm⟩
    · refine ⟨Or.inr (Or.inl rfl), ?_⟩
      rcases hq_form q with (h0 | h1') | ⟨_, _, m, t, ht, heq⟩
      · exact ⟨0, by simp [h0]⟩
      · exact ⟨1, by simp [h1']⟩
      · rcases ht with rfl | rfl
        · exact absurd ⟨m, by simpa using heq⟩ h2
        · exact absurd ⟨m, by simpa using heq⟩ h1
  have hsR_supp : ∀ q : P, sR q ≠ 0 → q ∈ High3 ∧ ¬ isUnrefl σ q := by
    intro q hne
    rcases hq_form q with (h0 | h1') | ⟨hqH, hu, _⟩
    · exfalso; apply hne; dsimp [sR]
      rw [if_neg (fun ⟨m, hm⟩ => hno_int_third 0 m 1 (Or.inr rfl) (by push_cast; linarith)),
        if_neg (fun ⟨m, hm⟩ => hno_int_third 0 m (-1) (Or.inl rfl) (by push_cast; linarith))]
    · exfalso; apply hne; dsimp [sR]
      rw [if_neg (fun ⟨m, hm⟩ => hno_int_third 1 m 1 (Or.inr rfl) (by push_cast; linarith)),
        if_neg (fun ⟨m, hm⟩ => hno_int_third 1 m (-1) (Or.inl rfl) (by push_cast; linarith))]
    · exact ⟨hqH, hu⟩
  have hsR_zero : ∀ q : P, sR q = 0 := by
    refine no_small_mod3_reflection B hmeet sR (fun q => (hsR_spec q).1) ?_ ?_ ?_
    · intro l
      have hline : ∑ q ∈ B l, Order12.Deficit18Frame.dot (uVec B q) (E σ 0) = 1 := by
        rw [← Order12.Deficit18Frame.dot_sum_left, sum_uVec_block B hp hsize hmeet l, hEF_V σ 0]
      let m : P → ℤ := fun q => (hsR_spec q).2.choose
      have hm : ∀ q, Order12.Deficit18Frame.dot (uVec B q) (E σ 0) = (m q : ℝ) + (sR q : ℝ) / 3 :=
        fun q => (hsR_spec q).2.choose_spec
      simp_rw [hm, sum_add_distrib, ← sum_div] at hline
      have h3 : ((∑ q ∈ B l, sR q : ℤ) : ℝ) = ((3 * (1 - ∑ q ∈ B l, m q) : ℤ) : ℝ) := by
        push_cast; linarith
      have h3z : ∑ q ∈ B l, sR q = 3 * (1 - ∑ q ∈ B l, m q) := by exact_mod_cast h3
      exact ⟨1 - ∑ q ∈ B l, m q, h3z⟩
    · intro q hqne
      have hd3 := (mem_filter.mp (hsR_supp q hqne).1).2
      dsimp [defic] at hd3; omega
    · have hsub : univ.filter (fun q : P => sR q ≠ 0) ⊆ High3.filter (fun h => ¬ isUnrefl σ h) := by
        intro q hq
        have ⟨h1, h2⟩ := hsR_supp q (mem_filter.mp hq).2
        exact mem_filter.mpr ⟨h1, h2⟩
      exact (card_le_card hsub).trans hrefl_le12
  have hfinal_01 : ∀ q : P,
      Order12.Deficit18Frame.dot (uVec B q) (E σ 0) = 0 ∨
      Order12.Deficit18Frame.dot (uVec B q) (E σ 0) = 1 := by
    intro q
    rcases hq_form q with h01 | ⟨_, _, m, t, ht, heq⟩
    · exact h01
    · exfalso
      have h0 := hsR_zero q
      dsimp [sR] at h0
      rcases ht with rfl | rfl
      · rw [if_neg (fun ⟨m1, hm1⟩ => hno_pos_neg_third m1 m (by linarith)),
          if_pos ⟨m, by simpa using heq⟩] at h0
        omega
      · rw [if_pos ⟨m, by simpa using heq⟩] at h0
        omega
  let x : P → ℕ := fun q => if Order12.Deficit18Frame.dot (uVec B q) (E σ 0) = 1 then 1 else 0
  refine new_block_of_zero_one_coord B x (fun q => by dsimp [x]; split_ifs <;> simp) ?_ ?_
  · have h13 : ∑ q : P, Order12.Deficit18Frame.dot (uVec B q) (E σ 0) ^ 2 = 13 := by
      rw [frame_identity B hp (E σ 0) (hproj_of_range (E σ 0) ((hEF_mem σ).1 0)),
        horth_σ.1 0 0, if_pos rfl, hEF_V σ 0]
      norm_num
    have hsq : ∑ q : P, Order12.Deficit18Frame.dot (uVec B q) (E σ 0) ^ 2 = ((∑ q : P, x q : ℕ) : ℝ) := by
      push_cast; apply sum_congr rfl; intro q _
      rcases hfinal_01 q with h0 | h0 <;> simp [x, h0]
    rw [hsq] at h13
    exact_mod_cast h13
  · intro l
    have h1 : ∑ q ∈ B l, Order12.Deficit18Frame.dot (uVec B q) (E σ 0) = 1 := by
      rw [← Order12.Deficit18Frame.dot_sum_left, sum_uVec_block B hp hsize hmeet l, hEF_V σ 0]
    have hsum : ∑ q ∈ B l, Order12.Deficit18Frame.dot (uVec B q) (E σ 0) = ((∑ q ∈ B l, x q : ℕ) : ℝ) := by
      push_cast; apply sum_congr rfl; intro q _
      rcases hfinal_01 q with h0 | h0 <;> simp [x, h0]
    rw [hsum] at h1
    exact_mod_cast h1

set_option maxHeartbeats 4000000 in
/-- **Main Theorem:** Any 139 blocks of size 13 on 157 points that meet pairwise in
exactly one point admit a 140th block of size 13 meeting every old block in one point
(and automatically distinct from all 139 old blocks). -/
theorem new_block_of_139
    (B : L → Finset P) (hp : Fintype.card P = 157) (hl : Fintype.card L = 139)
    (hsize : ∀ l, (B l).card = 13)
    (hmeet : ∀ l m, l ≠ m → (B l ∩ B m).card = 1) :
    ∃ N : Finset P, N.card = 13 ∧ ∀ l, (N ∩ B l).card = 1 := by
  classical
  -- If some point has degree 12, extend immediately via Order12DegreeTwelve.
  by_cases h12 : ∃ p : P, deg B p = 12
  · obtain ⟨p, hp12⟩ := h12
    obtain ⟨N, hNcard, _, hNmeet⟩ := Erdos723PartialPlane.extend_at_degree_twelve B hp hsize hmeet p hp12
    exact ⟨N, hNcard, hNmeet⟩
  push Not at h12
  -- Otherwise no point has degree 12; invoke the deficit-18 root graph properties.
  have hrg := root_graph_properties B hp hl hsize hmeet h12
  set R := univ.filter fun p => defic B p = 2
  set n3 := (univ.filter fun p => defic B p = 3).card
  set n4 := (univ.filter fun p => defic B p = 4).card
  set n5 := (univ.filter fun p => defic B p = 5).card
  set n6 := (univ.filter fun p => defic B p = 6).card
  let RSub := { p : P // p ∈ R }
  let adjR : RSub → RSub → Prop := fun a b => IsHole B a.1 b.1
  obtain ⟨hexcess_nat, hmass_nat, hn2_ge81, hdeg16, hcomm12, hcomm4, hconnR⟩ := hrg
  -- Restrict uVec to RSub and apply the elementary line-graph edge representation!
  let uR : RSub → P → ℝ := fun p => uVec B p.1
  have huR_norm : ∀ p : RSub, Order12.Deficit18LineGraph.dot (uR p) (uR p) = 2 := by
    intro p
    change Order12.Deficit18Frame.dot (uVec B p.1) (uVec B p.1) = 2
    rw [dot_uVec_self B hp hsize hmeet p.1]
    have h2 : defic B p.1 = 2 := (mem_filter.mp p.2).2
    dsimp [defic, deg] at h2
    have hdeg11 : (univ.filter fun l => p.1 ∈ B l).card = 11 := by omega
    rw [hdeg11]; norm_num
  have huR_gram : ∀ p q : RSub, p ≠ q →
      Order12.Deficit18LineGraph.dot (uR p) (uR q) = 0 ∨
      Order12.Deficit18LineGraph.dot (uR p) (uR q) = 1 := by
    intro p q hpq
    change Order12.Deficit18Frame.dot (uVec B p.1) (uVec B q.1) = 0 ∨
      Order12.Deficit18Frame.dot (uVec B p.1) (uVec B q.1) = 1
    rw [dot_uVec_ne B hp hsize hmeet (fun e => hpq (Subtype.ext e))]
    split_ifs <;> simp
  have huR_adj : ∀ p q : RSub, adjR p q ↔ p ≠ q ∧ Order12.Deficit18LineGraph.dot (uR p) (uR q) = 1 := by
    intro p q
    constructor
    · intro h
      have hne : p ≠ q := fun e => h.1 (congrArg Subtype.val e)
      refine ⟨hne, ?_⟩
      change Order12.Deficit18Frame.dot (uVec B p.1) (uVec B q.1) = 1
      rw [dot_uVec_ne B hp hsize hmeet h.1]
      have hno : ¬ ∃ l, p.1 ∈ B l ∧ q.1 ∈ B l := fun ⟨l, h1, h2⟩ => h.2 l ⟨h1, h2⟩
      rw [if_neg hno]
    · rintro ⟨hne, hdot⟩
      have hne' : p.1 ≠ q.1 := fun e => hne (Subtype.ext e)
      change Order12.Deficit18Frame.dot (uVec B p.1) (uVec B q.1) = 1 at hdot
      rw [dot_uVec_ne B hp hsize hmeet hne'] at hdot
      refine ⟨hne', fun l ⟨h1, h2⟩ => ?_⟩
      have hex : ∃ l, p.1 ∈ B l ∧ q.1 ∈ B l := ⟨l, h1, h2⟩
      rw [if_pos hex] at hdot
      norm_num at hdot
  obtain ⟨V, instFinV, instDecV, e1, e2, he12_ne, hpair_uniq, hgram_match, hnoniso, hdegG_sum, hconnG⟩ :=
    exists_edge_rep uR adjR huR_norm huR_gram huR_adj hdeg16 hcomm12 hcomm4 hconnR
  let adjG : V → V → Prop := fun a b => ∃ p : RSub, (e1 p = a ∧ e2 p = b) ∨ (e1 p = b ∧ e2 p = a)
  have hadjG_sym : Symmetric adjG := fun a b ⟨p, h⟩ =>
    ⟨p, h.elim (fun ⟨h1, h2⟩ => Or.inr ⟨h1, h2⟩) (fun ⟨h1, h2⟩ => Or.inl ⟨h1, h2⟩)⟩
  have hadjG_irr : Irreflexive adjG := fun a ⟨p, h⟩ => by
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> exact he12_ne p (h1.trans h2.symm)
  -- Edge indicator vectors w : RSub → (V → ℝ) with exact Gram match to uR.
  let w : RSub → V → ℝ := fun p v => (if v = e1 p then 1 else 0) + (if v = e2 p then 1 else 0)
  have hgram_eq : ∀ p q : RSub,
      Order12.Deficit18Frame.dot (uR p) (uR q) = Order12.Deficit18Frame.dot (w p) (w q) :=
    hgram_match
  have hdot_w : ∀ (p : RSub) (z : V → ℝ), Order12.Deficit18Frame.dot z (w p) = z (e1 p) + z (e2 p) := by
    intro p z
    simp only [Order12.Deficit18Frame.dot, w, mul_add, sum_add_distrib]
    simp
  have hdegG_eq_card : ∀ i : V,
      (univ.filter (adjG i)).card = (univ.filter fun q : RSub => e1 q = i ∨ e2 q = i).card := by
    intro i
    refine Finset.card_bij (fun j _ => Classical.choose (mem_filter.mp ‹j ∈ univ.filter (adjG i)›).2) ?_ ?_ ?_
    · intro j hj
      have hspec := Classical.choose_spec (mem_filter.mp hj).2
      refine mem_filter.mpr ⟨mem_univ _, ?_⟩
      rcases hspec with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact Or.inl h1
      · exact Or.inr h2
    · intro j1 hj1 j2 hj2 heq
      have h1 := Classical.choose_spec (mem_filter.mp hj1).2
      have h2 := Classical.choose_spec (mem_filter.mp hj2).2
      rw [heq] at h1
      rcases h1 with ⟨ha1, hb1⟩ | ⟨ha1, hb1⟩ <;> rcases h2 with ⟨ha2, hb2⟩ | ⟨ha2, hb2⟩
      · exact hb1.symm.trans hb2
      · exfalso; exact he12_ne _ (ha1.trans hb2.symm)
      · exfalso; exact he12_ne _ (ha2.trans hb1.symm)
      · exact ha1.symm.trans ha2
    · intro q hq
      have hq' := (mem_filter.mp hq).2
      let j := if e1 q = i then e2 q else e1 q
      have hij : adjG i j := by
        dsimp [j]; split_ifs with h
        · exact ⟨q, Or.inl ⟨h, rfl⟩⟩
        · exact ⟨q, Or.inr ⟨rfl, hq'.resolve_left h⟩⟩
      refine ⟨j, mem_filter.mpr ⟨mem_univ _, hij⟩, ?_⟩
      have hspec := Classical.choose_spec hij
      let q' := Classical.choose hij
      change q' = q
      have hpair : ({e1 q', e2 q'} : Finset V) = {e1 q, e2 q} := by
        have h1 : ({e1 q', e2 q'} : Finset V) = {i, j} := by
          rcases hspec with ⟨ha, hb⟩ | ⟨ha, hb⟩
          · rw [ha, hb]
          · rw [ha, hb, pair_comm]
        have h2 : ({e1 q, e2 q} : Finset V) = {i, j} := by
          dsimp [j]; split_ifs with h
          · rw [h]
          · rw [hq'.resolve_left h, pair_comm]
        exact h1.trans h2.symm
      exact (hpair_uniq q' q).mp hpair
  have hdegG_sum_adj : ∀ i j : V, adjG i j →
      18 ≤ (univ.filter (adjG i)).card + (univ.filter (adjG j)).card := by
    intro i j ⟨p, hpij⟩
    rw [hdegG_eq_card i, hdegG_eq_card j]
    have h18 := hdegG_sum p
    rcases hpij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h18
    · omega
  have hnoniso_adj : ∀ i : V, ∃ j : V, adjG i j := by
    intro i
    obtain ⟨p, hp1 | hp2⟩ := hnoniso i
    · exact ⟨e2 p, p, Or.inl ⟨hp1, rfl⟩⟩
    · exact ⟨e1 p, p, Or.inr ⟨rfl, hp2⟩⟩
  -- Every uR p lies in range (projLin B).
  have hspan_uR_le : Submodule.span ℝ (Set.range uR) ≤ LinearMap.range (projLin B) := by
    rw [Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    exact ⟨T (basisE p.1), rfl⟩
  have hproj_of_range : ∀ x ∈ LinearMap.range (projLin B), proj B x = x := by
    rintro _ ⟨y, rfl⟩; exact proj_idem B hp hsize hmeet y
  -- Split into Nonbipartite (G has an odd closed walk) vs Bipartite (G is 2-colorable)!
  by_cases hodd_G : ∃ (m : ℕ) (a0 : V), m % 2 = 1 ∧ Walk adjG m a0 a0
  · -- Case 1: G is NONBIPARTITE
    obtain ⟨m0, a0, hm0_odd, wa0⟩ := hodd_G
    -- Step 1a: Any z : V → ℝ with z a + z b = 0 on all edges of G is identically 0.
    have hwalk_sign : ∀ (z : V → ℝ), (∀ a b, adjG a b → z a + z b = 0) →
        ∀ {n : ℕ} {a b : V}, Walk adjG n a b → z b = (-1 : ℝ) ^ n * z a := by
      intro z hz n a b walk
      induction walk with
      | nil x => simp
      | @cons k x y t hxy _ ih =>
        have hxy' : z y = -z x := by linarith [hz x y hxy]
        rw [ih, hxy', pow_succ]; ring
    have horth_zero : ∀ z : V → ℝ, (∀ p : RSub, Order12.Deficit18Frame.dot z (w p) = 0) → z = 0 := by
      intro z hz
      have hz_edge : ∀ a b, adjG a b → z a + z b = 0 := by
        intro a b ⟨p, hpab⟩
        have h0 := hz p; rw [hdot_w] at h0
        rcases hpab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> linarith
      have hza0 : z a0 = 0 := by
        have h := hwalk_sign z hz_edge wa0
        have hpow : (-1 : ℝ) ^ m0 = -1 := Odd.neg_one_pow (Nat.odd_iff.mpr hm0_odd)
        rw [hpow] at h; linarith
      ext v
      obtain ⟨k, wk⟩ := hconnG a0 v
      rw [hwalk_sign z hz_edge wk, hza0, mul_zero]; rfl
    have hspan_w_top : Submodule.span ℝ (Set.range w) = ⊤ := by
      refine eq_of_le_of_ortho_zero _ ⊤ le_top fun z _ hz => horth_zero z fun p => ?_
      exact hz (w p) (Submodule.subset_span ⟨p, rfl⟩)
    -- Step 1b: Build orthonormal coordinate vectors E : V → (P → ℝ) inside range (projLin B).
    let basisV : V → V → ℝ := fun i j => if j = i then 1 else 0
    let Φ := gramEquiv uR w hgram_eq
    let E : V → P → ℝ := fun i => (Φ ⟨basisV i, hspan_w_top ▸ Submodule.mem_top⟩).1
    have hE_mem : ∀ i : V, E i ∈ LinearMap.range (projLin B) := fun i =>
      hspan_uR_le (Φ ⟨basisV i, hspan_w_top ▸ Submodule.mem_top⟩).2
    have hE_proj : ∀ i : V, proj B (E i) = E i := fun i => hproj_of_range (E i) (hE_mem i)
    have hE_orth : ∀ i j : V, Order12.Deficit18Frame.dot (E i) (E j) = if i = j then 1 else 0 := by
      intro i j
      dsimp [E]
      rw [gramEquiv_dot]
      unfold basisV
      rw [dot_basis_left]
    have hE_edge : ∀ p : RSub, E (e1 p) + E (e2 p) = uVec B p.1 := by
      intro p
      have hsum : (⟨basisV (e1 p), hspan_w_top ▸ Submodule.mem_top⟩ : Submodule.span ℝ (Set.range w)) +
          ⟨basisV (e2 p), hspan_w_top ▸ Submodule.mem_top⟩ =
          ⟨w p, Submodule.subset_span ⟨p, rfl⟩⟩ := by
        apply Subtype.ext; ext v; simp [basisV, w]
      have hmap := congrArg Subtype.val (map_add Φ
        ⟨basisV (e1 p), hspan_w_top ▸ Submodule.mem_top⟩
        ⟨basisV (e2 p), hspan_w_top ▸ Submodule.mem_top⟩)
      rw [hsum, gramEquiv_apply_gen] at hmap
      exact hmap.symm
    -- Step 1c: ⟨V, E i⟩ = 1, line sums = 1, and frame norm ∑ q, ⟨u_q, E i⟩² = 13.
    have hE_V : ∀ i : V, Order12.Deficit18Frame.dot (vVec B) (E i) = 1 := by
      have hz0 : (fun i : V => Order12.Deficit18Frame.dot (vVec B) (E i) - 1) = 0 := by
        refine horth_zero _ fun p => ?_
        rw [hdot_w]
        have hsum : Order12.Deficit18Frame.dot (vVec B) (E (e1 p)) +
            Order12.Deficit18Frame.dot (vVec B) (E (e2 p)) = 2 := by
          rw [← Order12.Deficit18Frame.dot_add_right, hE_edge p, Order12.Deficit18Frame.dot_comm,
            dot_uVec_vVec B hp hsize hmeet p.1]
          have h2 : defic B p.1 = 2 := (mem_filter.mp p.2).2
          dsimp [defic, deg] at h2
          have : (univ.filter fun l => p.1 ∈ B l).card = 11 := by omega
          rw [this]; norm_num
        linarith
      intro i
      have := congrFun hz0 i
      dsimp at this; linarith
    let coord : P → V → ℝ := fun q i => Order12.Deficit18Frame.dot (uVec B q) (E i)
    have hcoord_line : ∀ (l : L) (i : V), ∑ q ∈ B l, coord q i = 1 := by
      intro l i
      dsimp [coord]
      rw [← Order12.Deficit18Frame.dot_sum_left, sum_uVec_block B hp hsize hmeet l, hE_V i]
    have hcoord_sq_sum : ∀ i : V, ∑ q : P, coord q i ^ 2 = 13 := by
      intro i
      dsimp [coord]
      rw [frame_identity B hp (E i) (hE_proj i), hE_orth i i, if_pos rfl, hE_V i]
      norm_num
    have hcoord_root : ∀ (p : RSub) (i : V),
        coord p.1 i = (if i = e1 p then 1 else 0) + (if i = e2 p then 1 else 0) := by
      intro p i
      dsimp [coord]
      rw [← hE_edge p, Order12.Deficit18Frame.dot_add_left, hE_orth, hE_orth]
      simp [eq_comm]
    -- Degree bound deg_G i ≤ 13, hence |V| ≥ 13.
    have hdegG_le13 : ∀ i : V, (univ.filter (adjG i)).card ≤ 13 := by
      intro i
      rw [hdegG_eq_card i]
      have h13 := hcoord_sq_sum i
      have hsub : (univ.filter fun q : RSub => e1 q = i ∨ e2 q = i).image Subtype.val ⊆ univ := subset_univ _
      have hsum_le : (((univ.filter fun q : RSub => e1 q = i ∨ e2 q = i).image Subtype.val).card : ℝ) ≤
          ∑ q : P, coord q i ^ 2 := by
        calc
          _ = ∑ _q ∈ (univ.filter fun q : RSub => e1 q = i ∨ e2 q = i).image Subtype.val, (1 : ℝ) := by simp
          _ ≤ ∑ q ∈ (univ.filter fun q : RSub => e1 q = i ∨ e2 q = i).image Subtype.val, coord q i ^ 2 := by
            apply sum_le_sum; intro q hq
            obtain ⟨r, hr, rfl⟩ := mem_image.mp hq
            have hr' := (mem_filter.mp hr).2
            rw [hcoord_root r i]
            rcases hr' with h1 | h2
            · rw [if_pos h1.symm, if_neg (fun e => he12_ne r (h1.trans e))]; norm_num
            · rw [if_neg (fun e => he12_ne r (e.symm.trans h2.symm)), if_pos h2.symm]; norm_num
          _ ≤ ∑ q : P, coord q i ^ 2 := sum_le_univ_sum_of_nonneg fun q => sq_nonneg _
      rw [card_image_of_injective _ Subtype.val_injective, h13] at hsum_le
      exact_mod_cast hsum_le
    have hV_ge13 : 13 ≤ Fintype.card V := by
      have hsum_deg : ∑ i : V, (univ.filter fun q : RSub => e1 q = i ∨ e2 q = i).card = 2 * R.card := by
        have h1 : ∀ i : V, (univ.filter fun q : RSub => e1 q = i ∨ e2 q = i).card =
            ∑ q : RSub, (if e1 q = i then 1 else 0) + ∑ q : RSub, (if e2 q = i then 1 else 0) := by
          intro i
          rw [← sum_add_distrib]
          have h2 : ∀ q : RSub, (if e1 q = i then 1 else 0) + (if e2 q = i then 1 else 0) =
              if e1 q = i ∨ e2 q = i then 1 else 0 := by
            intro q
            by_cases h1 : e1 q = i <;> by_cases h2 : e2 q = i
            · exact absurd (h1.trans h2.symm) (he12_ne q)
            · simp [h1, h2]
            · simp [h1, h2]
            · simp [h1, h2]
          simp_rw [h2, sum_boole, Nat.cast_id]
        simp_rw [h1, sum_add_distrib]
        rw [Finset.sum_comm, Finset.sum_comm (f := fun i q => if e2 q = i then 1 else 0)]
        simp [RSub]; omega
      have hle : ∑ i : V, (univ.filter fun q : RSub => e1 q = i ∨ e2 q = i).card ≤ 13 * Fintype.card V := by
        calc
          _ ≤ ∑ _i : V, 13 := sum_le_sum fun i _ => by rw [← hdegG_eq_card i]; exact hdegG_le13 i
          _ = 13 * Fintype.card V := by simp [mul_comm]
      omega
    -- Step 1d: For every q : P, either all coord q i are integers or all are half-integers.
    have hcoord_edge_int : ∀ (q : P) (a b : V), adjG a b → ∃ k : ℤ, coord q a + coord q b = (k : ℝ) := by
      intro q a b ⟨p, hpab⟩
      have hsum : coord q a + coord q b = Order12.Deficit18Frame.dot (uVec B q) (uVec B p.1) := by
        dsimp [coord]
        rw [← Order12.Deficit18Frame.dot_add_right]
        rcases hpab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rw [hE_edge p]
        · rw [add_comm, hE_edge p]
      rw [hsum]
      by_cases hqp : q = p.1
      · subst hqp
        refine ⟨2, ?_⟩
        exact huR_norm p
      · rw [dot_uVec_ne B hp hsize hmeet hqp]
        split_ifs
        · exact ⟨0, by norm_num⟩
        · exact ⟨1, by norm_num⟩
    have hwalk_int : ∀ (q : P) {n : ℕ} {a b : V}, Walk adjG n a b →
        ∃ k : ℤ, coord q b = (-1 : ℝ) ^ n * coord q a + (k : ℝ) := by
      intro q n a b walk
      induction walk with
      | nil x => exact ⟨0, by simp⟩
      | @cons k x y t hxy _ ih =>
        obtain ⟨k1, hk1⟩ := hcoord_edge_int q x y hxy
        obtain ⟨k2, hk2⟩ := ih
        refine ⟨(-1 : ℤ) ^ k * k1 + k2, ?_⟩
        have hy : coord q y = -coord q x + (k1 : ℝ) := by linarith
        rw [hk2, hy, pow_succ]
        push_cast; ring
    have hhalf_or_int : ∀ q : P,
        (∀ i : V, ∃ z : ℤ, coord q i = (z : ℝ)) ∨
        (∀ i : V, ∃ z : ℤ, coord q i = (z : ℝ) + 1 / 2) := by
      intro q
      obtain ⟨k0, hk0⟩ := hwalk_int q wa0
      have hpow : (-1 : ℝ) ^ m0 = -1 := Odd.neg_one_pow (Nat.odd_iff.mpr hm0_odd)
      rw [hpow] at hk0
      have h2a0 : 2 * coord q a0 = (k0 : ℝ) := by linarith
      by_cases heven : k0 % 2 = 0
      · left
        intro i
        obtain ⟨d, wd⟩ := hconnG a0 i
        obtain ⟨ki, hki⟩ := hwalk_int q wd
        have ha0_eq : coord q a0 = ((k0 / 2 : ℤ) : ℝ) := by
          have : (k0 : ℝ) = 2 * ((k0 / 2 : ℤ) : ℝ) := by
            have hk : k0 = 2 * (k0 / 2) := by omega
            exact_mod_cast hk
          linarith
        refine ⟨(-1 : ℤ) ^ d * (k0 / 2) + ki, ?_⟩
        rw [hki, ha0_eq]; push_cast; ring
      · right
        intro i
        obtain ⟨d, wd⟩ := hconnG a0 i
        obtain ⟨ki, hki⟩ := hwalk_int q wd
        have ha0_eq : coord q a0 = (((k0 - 1) / 2 : ℤ) : ℝ) + 1 / 2 := by
          have : (k0 : ℝ) = 2 * (((k0 - 1) / 2 : ℤ) : ℝ) + 1 := by
            have hk : k0 = 2 * ((k0 - 1) / 2) + 1 := by omega
            exact_mod_cast hk
          linarith
        have hhalf_sign : (-1 : ℝ) ^ d * (1 / 2) = (if d % 2 = 0 then (0 : ℤ) else -1 : ℤ) + 1 / 2 := by
          rcases Nat.even_or_odd d with ⟨r, rfl⟩ | ⟨r, rfl⟩
          · have hmod : (r + r) % 2 = 0 := by omega
            have hp1 : (-1 : ℝ) ^ (r + r) = 1 := Even.neg_one_pow ⟨r, rfl⟩
            simp [hmod, hp1]
          · have hp1 : (-1 : ℝ) ^ (2 * r + 1) = -1 := Odd.neg_one_pow ⟨r, rfl⟩
            simp [hp1]; ring
        refine ⟨(-1 : ℤ) ^ d * ((k0 - 1) / 2) + (if d % 2 = 0 then 0 else -1) + ki, ?_⟩
        rw [hki, ha0_eq]
        calc
          (-1 : ℝ) ^ d * (↑((k0 - 1) / 2) + 1 / 2) + ↑ki
            = (-1 : ℝ) ^ d * ↑((k0 - 1) / 2) + (-1 : ℝ) ^ d * (1 / 2) + ↑ki := by ring
          _ = _ := by rw [hhalf_sign]; push_cast; ring
    -- Step 1e: Eliminate all half-integral points via nonbipartite_no_half_integral!
    let H := univ.filter fun q : P => ∀ i : V, ∃ z : ℤ, coord q i = (z : ℝ) + 1 / 2
    have hH_empty : H = ∅ := by
      refine nonbipartite_no_half_integral B hp hl hsize hmeet h12 H ?_ ?_
      · intro q hqH
        have hbes := Order12.Deficit18Frame.bessel_ineq (univ : Finset V) E (fun i _ j _ => hE_orth i j) (uVec B q)
        have hlb : (Fintype.card V : ℝ) / 4 ≤ ∑ i : V, coord q i ^ 2 := by
          calc
            (Fintype.card V : ℝ) / 4 = ∑ _i : V, (1 / 4 : ℝ) := by simp; ring
            _ ≤ ∑ i : V, coord q i ^ 2 := by
              apply sum_le_sum; intro i _
              obtain ⟨z, hz⟩ := (mem_filter.mp hqH).2 i
              rw [hz]
              have hsq : ((z : ℝ) + 1 / 2) ^ 2 = ((2 * z + 1 : ℤ) : ℝ) ^ 2 / 4 := by push_cast; ring
              rw [hsq]
              have hne0 : (2 * z + 1 : ℤ) ≠ 0 := by omega
              have hge1 : (1 : ℤ) ≤ (2 * z + 1) ^ 2 := by
                rcases lt_or_gt_of_ne hne0 with h | h <;> nlinarith
              have hge1r : (1 : ℝ) ≤ ((2 * z + 1 : ℤ) : ℝ) ^ 2 := by exact_mod_cast hge1
              linarith
        have hnorm_q : Order12.Deficit18Frame.dot (uVec B q) (uVec B q) = (defic B q : ℝ) := by
          rw [dot_uVec_self B hp hsize hmeet q]; dsimp [defic, deg]; push_cast; rfl
        rw [hnorm_q] at hbes
        have hV13r : (13 : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hV_ge13
        have hgt3 : (3 : ℝ) < (defic B q : ℝ) := by linarith
        have hgt3z : (3 : ℤ) < defic B q := by exact_mod_cast hgt3
        omega
      · intro q hqH l hql
        by_contra hno_other
        push Not at hno_other
        -- Every r ∈ (B l).erase q is integral at a0!
        have hint_other : ∀ r ∈ (B l).erase q, ∃ z : ℤ, coord r a0 = (z : ℝ) := by
          intro r hr
          have ⟨hrq, hrl⟩ := mem_erase.mp hr
          rcases hhalf_or_int r with hint | hhalf
          · exact hint a0
          · exfalso; exact hno_other r (mem_filter.mpr ⟨mem_univ _, hhalf⟩) hrq hrl
        have hsum_int : ∃ Z : ℤ, ∑ r ∈ (B l).erase q, coord r a0 = (Z : ℝ) := by
          have : ∀ s : Finset P, (∀ r ∈ s, ∃ z : ℤ, coord r a0 = (z : ℝ)) →
              ∃ Z : ℤ, ∑ r ∈ s, coord r a0 = (Z : ℝ) := by
            intro s
            induction s using Finset.induction_on with
            | empty => intro _; exact ⟨0, by simp⟩
            | insert a s ha ih =>
              intro hall
              obtain ⟨z1, hz1⟩ := hall a (mem_insert_self a s)
              obtain ⟨z2, hz2⟩ := ih fun r hr => hall r (mem_insert_of_mem hr)
              exact ⟨z1 + z2, by rw [sum_insert ha, hz1, hz2]; push_cast; ring⟩
          exact this ((B l).erase q) hint_other
        obtain ⟨Z, hZ⟩ := hsum_int
        obtain ⟨zq, hzq⟩ := (mem_filter.mp hqH).2 a0
        have hline := hcoord_line l a0
        rw [← add_sum_erase (B l) (fun r => coord r a0) hql, hzq, hZ] at hline
        have h2 : ((2 * (zq + Z) + 1 : ℤ) : ℝ) = (2 : ℤ) := by push_cast; linarith
        have h2z : 2 * (zq + Z) + 1 = 2 := by exact_mod_cast h2
        omega
    -- Step 1f: Every point has {0, 1} coordinates via nonbipartite_zero_one_of_integral!
    have hcoord_01 : ∀ (q : P) (i : V), coord q i = 0 ∨ coord q i = 1 := by
      intro q
      by_cases hqR : q ∈ R
      · intro i
        let r : RSub := ⟨q, hqR⟩
        rw [show coord q i = coord r.1 i from rfl, hcoord_root r i]
        by_cases h1 : i = e1 r <;> by_cases h2 : i = e2 r
        · exact absurd (h1.symm.trans h2) (he12_ne r)
        · rw [if_pos h1, if_neg h2]; norm_num
        · rw [if_neg h1, if_pos h2]; norm_num
        · rw [if_neg h1, if_neg h2]; norm_num
      · have hint_q : ∀ i : V, ∃ z : ℤ, coord q i = (z : ℝ) := by
          rcases hhalf_or_int q with hint | hhalf
          · exact hint
          · exfalso
            have : q ∈ H := mem_filter.mpr ⟨mem_univ _, hhalf⟩
            rw [hH_empty] at this; exact notMem_empty q this
        let y : V → ℤ := fun i => (hint_q i).choose
        have hy_eq : ∀ i : V, coord q i = (y i : ℝ) := fun i => (hint_q i).choose_spec
        have hy_01 : ∀ i : V, y i = 0 ∨ y i = 1 := by
          refine nonbipartite_zero_one_of_integral adjG hnoniso_adj hdegG_sum_adj y ?_ ?_ ?_
          · intro i j hij
            obtain ⟨p, hpij⟩ := hij
            have hsum : (y i + y j : ℝ) = Order12.Deficit18Frame.dot (uVec B q) (uVec B p.1) := by
              rw [← hy_eq i, ← hy_eq j]
              dsimp [coord]
              rw [← Order12.Deficit18Frame.dot_add_right]
              rcases hpij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · rw [hE_edge p]
              · rw [add_comm, hE_edge p]
            have hqp : q ≠ p.1 := fun e => hqR (e ▸ p.2)
            rw [dot_uVec_ne B hp hsize hmeet hqp] at hsum
            split_ifs at hsum
            · left; have : ((y i + y j : ℤ) : ℝ) = (0 : ℤ) := by push_cast; linarith
              exact_mod_cast this
            · right; have : ((y i + y j : ℤ) : ℝ) = (1 : ℤ) := by push_cast; linarith
              exact_mod_cast this
          · intro j hyj
            rw [hdegG_eq_card j]
            let Sdeg := (univ.filter fun r : RSub => e1 r = j ∨ e2 r = j).image Subtype.val
            have hq_not_S : q ∉ Sdeg := by
              intro hmem; obtain ⟨r, _, rfl⟩ := mem_image.mp hmem; exact hqR r.2
            have hsum_le : ((Sdeg.card + 1 : ℕ) : ℝ) ≤ ∑ r : P, coord r j ^ 2 := by
              calc
                ((Sdeg.card + 1 : ℕ) : ℝ) = ∑ _r ∈ insert q Sdeg, (1 : ℝ) := by
                  rw [sum_const, card_insert_of_notMem hq_not_S, nsmul_eq_mul, mul_one]
                _ ≤ ∑ r ∈ insert q Sdeg, coord r j ^ 2 := by
                  apply sum_le_sum; intro r hr
                  rcases mem_insert.mp hr with rfl | hrS
                  · rw [hy_eq j]
                    have h1 : (1 : ℤ) ≤ y j * y j := by rcases lt_or_gt_of_ne hyj with h | h <;> nlinarith
                    have : (1 : ℝ) ≤ (y j : ℝ) * (y j : ℝ) := by exact_mod_cast h1
                    nlinarith
                  · obtain ⟨p, hpS, rfl⟩ := mem_image.mp hrS
                    have hp' := (mem_filter.mp hpS).2
                    rw [hcoord_root p j]
                    rcases hp' with h1 | h2
                    · rw [if_pos h1.symm, if_neg (fun e => he12_ne p (h1.trans e))]; norm_num
                    · rw [if_neg (fun e => he12_ne p (e.symm.trans h2.symm)), if_pos h2.symm]; norm_num
                _ ≤ ∑ r : P, coord r j ^ 2 := sum_le_univ_sum_of_nonneg fun r => sq_nonneg _
            rw [hcoord_sq_sum j, card_image_of_injective _ Subtype.val_injective] at hsum_le
            have hnat : (univ.filter fun r : RSub => e1 r = j ∨ e2 r = j).card + 1 ≤ 13 := by
              exact_mod_cast hsum_le
            omega
          · have hbes := Order12.Deficit18Frame.bessel_ineq (univ : Finset V) E (fun i _ j _ => hE_orth i j) (uVec B q)
            have hnorm_q : Order12.Deficit18Frame.dot (uVec B q) (uVec B q) = (defic B q : ℝ) := by
              rw [dot_uVec_self B hp hsize hmeet q]; dsimp [defic, deg]; push_cast; rfl
            have hle6 := defic_le_6_of_no_deg12 B hp hl hsize hmeet h12 q
            rw [hnorm_q] at hbes
            have hlhs : ∑ i : V, coord q i ^ 2 = ((∑ i : V, y i * y i : ℤ) : ℝ) := by
              push_cast; apply sum_congr rfl; intro i _; rw [hy_eq i, sq]
            rw [hlhs] at hbes
            have h6r : ((∑ i : V, y i * y i : ℤ) : ℝ) ≤ (6 : ℤ) := by
              have : (defic B q : ℝ) ≤ (6 : ℤ) := by exact_mod_cast hle6
              linarith
            exact_mod_cast h6r
        intro i; rcases hy_01 i with h0 | h0 <;> rw [hy_eq i, h0] <;> norm_num
    -- Step 1g: Pick any i0 : V and extract the 140th block via new_block_of_zero_one_coord!
    obtain ⟨r0, hr0⟩ := card_pos.mp (by omega : 0 < R.card)
    let i0 : V := e1 ⟨r0, hr0⟩
    let x : P → ℕ := fun q => if coord q i0 = 1 then 1 else 0
    have hx_eq : ∀ q : P, coord q i0 = (x q : ℝ) := by
      intro q; rcases hcoord_01 q i0 with h0 | h0 <;> simp [x, h0]
    refine new_block_of_zero_one_coord B x (fun q => by dsimp [x]; split_ifs <;> simp) ?_ ?_
    · have h13 := hcoord_sq_sum i0
      have hsq : ∑ q : P, coord q i0 ^ 2 = ((∑ q : P, x q : ℕ) : ℝ) := by
        push_cast; apply sum_congr rfl; intro q _
        rcases hcoord_01 q i0 with h0 | h0 <;> simp [x, h0]
      rw [hsq] at h13
      exact_mod_cast h13
    · intro l
      have h1 := hcoord_line l i0
      have hsum : ∑ q ∈ B l, coord q i0 = ((∑ q ∈ B l, x q : ℕ) : ℝ) := by
        push_cast; apply sum_congr rfl; intro q _; exact hx_eq q
      rw [hsum] at h1
      exact_mod_cast h1
  · -- Case 2: G is BIPARTITE
    -- G has no odd closed walk, hence no induced odd cycle, hence is 2-colorable!
    have hno_odd_G : ∀ k : ℕ, k % 2 = 1 → 3 ≤ k → ∀ f : Fin k → V,
        Function.Injective f →
        (∀ i j : Fin k, i ≠ j → (adjG (f i) (f j) ↔ cyclicAdj k i j)) → False := by
      intro k hko hk3 f _ hiff
      apply hodd_G
      have hcw : ∀ i : Fin k, adjG (f i) (f ⟨(i.val + 1) % k, Nat.mod_lt _ (by omega)⟩) := by
        intro i
        let j : Fin k := ⟨(i.val + 1) % k, Nat.mod_lt _ (by omega)⟩
        have hij : i ≠ j := by
          intro e
          have hval := congrArg Fin.val e
          dsimp [j] at hval
          have hlt := i.isLt
          by_cases hlast : i.val + 1 = k
          · rw [hlast, Nat.mod_self] at hval; omega
          · rw [Nat.mod_eq_of_lt (by omega)] at hval; omega
        exact (hiff i j hij).mpr (Or.inl rfl)
      let g : Fin (k + 1) → V := fun t => f ⟨t.val % k, Nat.mod_lt _ (by omega)⟩
      have hwalk : Walk adjG k (g ⟨0, by omega⟩) (g ⟨k, by omega⟩) :=
        Walk.ofFun g fun t => by
          have h1 := hcw ⟨t.val % k, Nat.mod_lt _ (by omega)⟩
          have hmod : (t.val % k + 1) % k = (t.val + 1) % k := by
            rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
          simpa [g, hmod] using h1
      have h0k : g ⟨k, by omega⟩ = g ⟨0, by omega⟩ := by simp [g]
      rw [h0k] at hwalk
      exact ⟨k, g ⟨0, by omega⟩, hko, hwalk⟩
    obtain ⟨col, hcol⟩ := bipartite_of_no_induced_odd_cycle adjG hadjG_sym hadjG_irr hno_odd_G
    let U1 := univ.filter fun v : V => col v = false
    let U2 := univ.filter fun v : V => col v = true
    have hU12_disj : Disjoint U1 U2 := by
      apply Finset.disjoint_left.mpr; intro v h1 h2
      have c1 := (mem_filter.mp h1).2; have c2 := (mem_filter.mp h2).2
      rw [c1] at c2; exact Bool.false_ne_true c2
    have hU12_union : U1 ∪ U2 = univ := by
      ext v; simp only [U1, U2, mem_union, mem_filter, mem_univ, true_and]
      cases col v <;> simp
    have hU12_card : U1.card + U2.card = Fintype.card V := by
      rw [← card_union_of_disjoint hU12_disj, hU12_union, card_univ]
    -- Signed part vector s : V → ℝ (+1 on U1, -1 on U2).
    let s : V → ℝ := fun v => if col v = false then 1 else -1
    have hs_edge : ∀ p : RSub, Order12.Deficit18Frame.dot s (w p) = 0 := by
      intro p
      rw [hdot_w]
      have hne := hcol (e1 p) (e2 p) ⟨p, Or.inl ⟨rfl, rfl⟩⟩
      dsimp [s]
      cases hc1 : col (e1 p) <;> cases hc2 : col (e2 p) <;> simp_all
    -- Step 2a: span(range w) = {z | dot z s = 0} has finrank = |V| - 1 ≤ 18.
    let sLin : (V → ℝ) →ₗ[ℝ] ℝ :=
      { toFun := fun z : V → ℝ => Order12.Deficit18Frame.dot z s
        map_add' := fun x y => Order12.Deficit18Frame.dot_add_left x y s
        map_smul' := fun c x => Order12.Deficit18Frame.dot_smul_left c x s }
    let sPerp : Submodule ℝ (V → ℝ) := LinearMap.ker sLin
    have hspan_w_eq : Submodule.span ℝ (Set.range w) = sPerp := by
      have hle : Submodule.span ℝ (Set.range w) ≤ sPerp := by
        rw [Submodule.span_le]
        rintro _ ⟨p, rfl⟩
        change Order12.Deficit18Frame.dot (w p) s = 0
        rw [Order12.Deficit18Frame.dot_comm]; exact hs_edge p
      refine eq_of_le_of_ortho_zero _ sPerp hle fun z hz_perp hz_orth => ?_
      have hz_edge : ∀ a b, adjG a b → z a + z b = 0 := by
        intro a b ⟨p, hpab⟩
        have h0 : Order12.Deficit18Frame.dot z (w p) = 0 := hz_orth (w p) (Submodule.subset_span ⟨p, rfl⟩)
        rw [hdot_w] at h0
        rcases hpab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> linarith
      obtain ⟨r0, hr0⟩ := card_pos.mp (by omega : 0 < R.card)
      let v0 : V := e1 ⟨r0, hr0⟩
      -- Every vertex v satisfies z v = (z v0 * s v0) * s v!
      have hz_prop : ∀ v : V, z v = (z v0 * s v0) * s v := by
        have hwalk_s : ∀ {n : ℕ} {a b : V}, Walk adjG n a b → z b * s b = z a * s a := by
          intro n a b walk
          induction walk with
          | nil _ => rfl
          | @cons k x y t hxy _ ih =>
            have h1 := hz_edge x y hxy
            have h2 := hcol x y hxy
            have hstep : z y * s y = z x * s x := by
              dsimp [s]
              cases hx : col x <;> cases hy : col y
              · exact absurd (hx.trans hy.symm) h2
              · simp; linarith
              · simp; linarith
              · exact absurd (hx.trans hy.symm) h2
            rw [ih, hstep]
        intro v
        obtain ⟨k, wk⟩ := hconnG v0 v
        have h1 := hwalk_s wk
        have hs2 : s v * s v = 1 := by dsimp [s]; cases col v <;> norm_num
        calc
          z v = (z v * s v) * s v := by rw [mul_assoc, hs2, mul_one]
          _ = (z v0 * s v0) * s v := by rw [h1]
      have hdot_zs : Order12.Deficit18Frame.dot z s = 0 := LinearMap.mem_ker.mp hz_perp
      have hdot_ss : Order12.Deficit18Frame.dot s s = (Fintype.card V : ℝ) := by
        simp only [Order12.Deficit18Frame.dot, s]
        have : ∀ v : V, (if col v = false then (1 : ℝ) else -1) * (if col v = false then 1 else -1) = 1 := by
          intro v; cases col v <;> norm_num
        simp_rw [this]; simp
      have hVpos : (0 : ℝ) < (Fintype.card V : ℝ) := by
        have : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨v0⟩
        exact_mod_cast this
      have hc0 : z v0 * s v0 = 0 := by
        have hzs : Order12.Deficit18Frame.dot z s = (z v0 * s v0) * Order12.Deficit18Frame.dot s s := by
          have hz_eq : z = (z v0 * s v0) • s := by ext v; exact hz_prop v
          conv_lhs => rw [hz_eq]
          rw [Order12.Deficit18Frame.dot_smul_left]
        rw [hzs, hdot_ss] at hdot_zs
        nlinarith
      ext v; rw [hz_prop v, hc0, zero_mul]; rfl
    have hV_pos_nat : 1 ≤ Fintype.card V := by
      obtain ⟨r0, hr0⟩ := card_pos.mp (by omega : 0 < R.card)
      exact Fintype.card_pos_iff.mpr ⟨e1 ⟨r0, hr0⟩⟩
    have hfinrank_w : Module.finrank ℝ (Submodule.span ℝ (Set.range w)) = Fintype.card V - 1 := by
      rw [hspan_w_eq]
      let φ : (V → ℝ) →ₗ[ℝ] ℝ :=
        { toFun := fun z => Order12.Deficit18Frame.dot z s
          map_add' := fun x y => Order12.Deficit18Frame.dot_add_left x y s
          map_smul' := fun c x => Order12.Deficit18Frame.dot_smul_left c x s }
      have hrank := LinearMap.finrank_range_add_finrank_ker φ
      have hsurj : LinearMap.range φ = ⊤ := by
        rw [eq_top_iff]; intro y _
        have hdot_ss : Order12.Deficit18Frame.dot s s = (Fintype.card V : ℝ) := by
          simp only [Order12.Deficit18Frame.dot, s]
          have : ∀ v : V, (if col v = false then (1 : ℝ) else -1) * (if col v = false then 1 else -1) = 1 := by
            intro v; cases col v <;> norm_num
          simp_rw [this]; simp
        have hne0 : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast (by omega : Fintype.card V ≠ 0)
        refine ⟨(y / (Fintype.card V : ℝ)) • s, ?_⟩
        change Order12.Deficit18Frame.dot ((y / (Fintype.card V : ℝ)) • s) s = y
        rw [Order12.Deficit18Frame.dot_smul_left, hdot_ss]
        field_simp [hne0]
      rw [hsurj, finrank_top, Module.finrank_self, Module.finrank_pi] at hrank
      change Module.finrank ℝ (LinearMap.ker φ) = Fintype.card V - 1
      omega
    let Φ := gramEquiv uR w hgram_eq
    have hfinrank_uR : Module.finrank ℝ (Submodule.span ℝ (Set.range uR)) = Fintype.card V - 1 := by
      rw [← Φ.finrank_eq, hfinrank_w]
    have hV_le19 : U1.card + U2.card ≤ 19 := by
      have hle18 : Module.finrank ℝ (Submodule.span ℝ (Set.range uR)) ≤ 18 := by
        rw [← finrank_range_projLin B hp hl hsize hmeet]
        exact Submodule.finrank_mono hspan_uR_le
      omega
    -- Step 2b: Projected V inequality 4 * (U1.card * U2.card) ≤ 18 * (U1.card + U2.card).
    let mR : ℝ := (Fintype.card V : ℝ)
    have hmR_pos : 0 < mR := by dsimp [mR]; exact_mod_cast (by omega : 0 < Fintype.card V)
    let zV : V → ℝ := fun x =>
      if col x = false then 2 * (U2.card : ℝ) / mR else 2 * (U1.card : ℝ) / mR
    have hzV_mem : zV ∈ Submodule.span ℝ (Set.range w) := by
      rw [hspan_w_eq]
      change Order12.Deficit18Frame.dot zV s = 0
      simp only [Order12.Deficit18Frame.dot, zV, s]
      have h1 : ∀ x : V,
          (if col x = false then 2 * (U2.card : ℝ) / mR else 2 * (U1.card : ℝ) / mR) *
          (if col x = false then 1 else -1) =
          (if col x = false then 2 * (U2.card : ℝ) / mR else 0) +
          (if col x = true then -(2 * (U1.card : ℝ) / mR) else 0) := by
        intro x; cases col x <;> simp
      simp_rw [h1, sum_add_distrib, ← sum_filter, sum_const, nsmul_eq_mul]
      change (U1.card : ℝ) * (2 * (U2.card : ℝ) / mR) + (U2.card : ℝ) * -(2 * (U1.card : ℝ) / mR) = 0
      ring
    let Z : P → ℝ := (Φ ⟨zV, hzV_mem⟩).1
    have hZ_norm : Order12.Deficit18Frame.dot Z Z = 4 * (U1.card : ℝ) * (U2.card : ℝ) / mR := by
      dsimp [Z]; rw [gramEquiv_dot]
      simp only [Order12.Deficit18Frame.dot, zV]
      have h1 : ∀ x : V,
          (if col x = false then 2 * (U2.card : ℝ) / mR else 2 * (U1.card : ℝ) / mR) *
          (if col x = false then 2 * (U2.card : ℝ) / mR else 2 * (U1.card : ℝ) / mR) =
          (if col x = false then (2 * (U2.card : ℝ) / mR) ^ 2 else 0) +
          (if col x = true then (2 * (U1.card : ℝ) / mR) ^ 2 else 0) := by
        intro x; cases col x <;> simp [sq]
      simp_rw [h1, sum_add_distrib, ← sum_filter, sum_const, nsmul_eq_mul]
      have hm_eq : (U1.card : ℝ) + (U2.card : ℝ) = mR := by dsimp [mR]; exact_mod_cast hU12_card
      change (U1.card : ℝ) * (2 * (U2.card : ℝ) / mR) ^ 2 + (U2.card : ℝ) * (2 * (U1.card : ℝ) / mR) ^ 2 = _
      have hm_ne : mR ≠ 0 := ne_of_gt hmR_pos
      field_simp [hm_ne]
      linear_combination 4 * (U1.card : ℝ) * (U2.card : ℝ) * hm_eq
    have hZ_V : Order12.Deficit18Frame.dot Z (vVec B) = 4 * (U1.card : ℝ) * (U2.card : ℝ) / mR := by
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hzV_mem
      have hZeq : Z = ∑ p : RSub, c p • uR p := gramEquiv_apply_of_eq uR w hgram_eq ⟨zV, hzV_mem⟩ c hc
      rw [hZeq, Order12.Deficit18Frame.dot_sum_left]
      have hterm : ∀ p : RSub, Order12.Deficit18Frame.dot (c p • uR p) (vVec B) =
          Order12.Deficit18Frame.dot (c p • w p) (fun _ => 1) := by
        intro p
        rw [Order12.Deficit18Frame.dot_smul_left, Order12.Deficit18Frame.dot_smul_left]
        congr 1
        dsimp [uR]
        rw [dot_uVec_vVec B hp hsize hmeet p.1]
        have h2 : defic B p.1 = 2 := (mem_filter.mp p.2).2
        dsimp [defic, deg] at h2
        have h11 : (univ.filter fun l => p.1 ∈ B l).card = 11 := by omega
        rw [h11, Order12.Deficit18Frame.dot_comm, hdot_w]
        norm_num
      simp_rw [hterm]
      rw [← Order12.Deficit18Frame.dot_sum_left, hc]
      simp only [Order12.Deficit18Frame.dot, zV, mul_one]
      have h1 : ∀ x : V,
          (if col x = false then 2 * (U2.card : ℝ) / mR else 2 * (U1.card : ℝ) / mR) =
          (if col x = false then 2 * (U2.card : ℝ) / mR else 0) +
          (if col x = true then 2 * (U1.card : ℝ) / mR else 0) := by
        intro x; cases col x <;> simp
      simp_rw [h1, sum_add_distrib, ← sum_filter, sum_const, nsmul_eq_mul]
      change (U1.card : ℝ) * (2 * (U2.card : ℝ) / mR) + (U2.card : ℝ) * (2 * (U1.card : ℝ) / mR) = _
      ring
    have hproj_ineq : 4 * (U1.card * U2.card) ≤ 18 * (U1.card + U2.card) := by
      have hnn : 0 ≤ Order12.Deficit18Frame.dot (vVec B - Z) (vVec B - Z) :=
        Order12.Deficit18Frame.dot_self_nonneg _
      rw [Order12.Deficit18Frame.dot_sub_left, Order12.Deficit18Frame.dot_sub_right,
        Order12.Deficit18Frame.dot_sub_right, Order12.Deficit18Frame.dot_comm (vVec B) Z,
        dot_vVec_self B hp hl hsize hmeet, hZ_norm, hZ_V] at hnn
      have hle : 4 * (U1.card : ℝ) * (U2.card : ℝ) / mR ≤ 18 := by linarith
      have hmul : 4 * (U1.card : ℝ) * (U2.card : ℝ) ≤ 18 * mR := (div_le_iff₀ hmR_pos).mp hle
      have hm_eq : mR = (U1.card : ℝ) + (U2.card : ℝ) := by dsimp [mR]; exact_mod_cast hU12_card.symm
      rw [hm_eq] at hmul
      have : ((4 * (U1.card * U2.card) : ℕ) : ℝ) ≤ ((18 * (U1.card + U2.card) : ℕ) : ℝ) := by
        push_cast; linarith
      exact_mod_cast this
    -- Step 2c: Apply complete_bipartite_of_moments (Order12Deficit18Profile.lean)!
    let eqU1 : Fin U1.card ≃ { x : V // x ∈ U1 } := (Fintype.equivFinOfCardEq (Fintype.card_coe U1)).symm
    let eqU2 : Fin U2.card ≃ { x : V // x ∈ U2 } := (Fintype.equivFinOfCardEq (Fintype.card_coe U2)).symm
    let E_bip : Fin U1.card → Fin U2.card → Prop := fun i j => adjG (eqU1 i).1 (eqU2 j).1
    have hU1_nbrs : ∀ i : Fin U1.card,
        (univ.filter (E_bip i)).card = (univ.filter (adjG (eqU1 i).1)).card := by
      intro i
      refine Finset.card_bij (fun j _ => (eqU2 j).1) ?_ ?_ ?_
      · intro j hj; exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hj).2⟩
      · intro j1 _ j2 _ h; exact eqU2.injective (Subtype.ext h)
      · intro y hy
        have hcol_y : col y = true := by
          have h1 := (mem_filter.mp (eqU1 i).2).2
          have h2 := hcol (eqU1 i).1 y (mem_filter.mp hy).2
          cases hyc : col y <;> simp_all
        let j := eqU2.symm ⟨y, mem_filter.mpr ⟨mem_univ _, hcol_y⟩⟩
        refine ⟨j, mem_filter.mpr ⟨mem_univ _, ?_⟩, ?_⟩
        · dsimp [E_bip, j]; rw [Equiv.apply_symm_apply]; exact (mem_filter.mp hy).2
        · dsimp [j]; rw [Equiv.apply_symm_apply]
    have hU2_nbrs : ∀ j : Fin U2.card,
        (univ.filter fun i : Fin U1.card => E_bip i j).card = (univ.filter (adjG (eqU2 j).1)).card := by
      intro j
      refine Finset.card_bij (fun i _ => (eqU1 i).1) ?_ ?_ ?_
      · intro i hi; exact mem_filter.mpr ⟨mem_univ _, hadjG_sym (mem_filter.mp hi).2⟩
      · intro i1 _ i2 _ h; exact eqU1.injective (Subtype.ext h)
      · intro x hx
        have hcol_x : col x = false := by
          have h1 := (mem_filter.mp (eqU2 j).2).2
          have h2 := hcol (eqU2 j).1 x (mem_filter.mp hx).2
          cases hxc : col x <;> simp_all
        let i := eqU1.symm ⟨x, mem_filter.mpr ⟨mem_univ _, hcol_x⟩⟩
        refine ⟨i, mem_filter.mpr ⟨mem_univ _, ?_⟩, ?_⟩
        · dsimp [E_bip, i]; rw [Equiv.apply_symm_apply]; exact hadjG_sym (mem_filter.mp hx).2
        · dsimp [i]; rw [Equiv.apply_symm_apply]
    have hbip_edges : (univ.filter fun p : Fin U1.card × Fin U2.card => E_bip p.1 p.2).card = R.card := by
      have hRcard : R.card = (univ : Finset RSub).card := by simp [RSub]
      rw [hRcard]
      symm
      refine Finset.card_bij
        (fun (q : RSub) _ =>
          if h1 : col (e1 q) = false then
            (eqU1.symm ⟨e1 q, mem_filter.mpr ⟨mem_univ _, h1⟩⟩,
             eqU2.symm ⟨e2 q, mem_filter.mpr ⟨mem_univ _,
               bool_true_of_ne_false (hcol (e1 q) (e2 q) ⟨q, Or.inl ⟨rfl, rfl⟩⟩) h1⟩⟩)
          else
            (eqU1.symm ⟨e2 q, mem_filter.mpr ⟨mem_univ _,
               bool_false_of_ne_true (hcol (e1 q) (e2 q) ⟨q, Or.inl ⟨rfl, rfl⟩⟩)
                 (bool_eq_true_of_ne_false h1)⟩⟩,
             eqU2.symm ⟨e1 q, mem_filter.mpr ⟨mem_univ _, bool_eq_true_of_ne_false h1⟩⟩))
        ?_ ?_ ?_
      · intro q _
        refine mem_filter.mpr ⟨mem_univ _, ?_⟩
        split_ifs with h1
        · dsimp [E_bip]; rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
          exact ⟨q, Or.inl ⟨rfl, rfl⟩⟩
        · dsimp [E_bip]; rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
          exact ⟨q, Or.inr ⟨rfl, rfl⟩⟩
      · intro q1 _ q2 _ heq
        have hfst := congrArg (fun p : Fin U1.card × Fin U2.card => (eqU1 p.1).1) heq
        have hsnd := congrArg (fun p : Fin U1.card × Fin U2.card => (eqU2 p.2).1) heq
        split_ifs at hfst hsnd with h1 h2 h2
        · simp only [Equiv.apply_symm_apply] at hfst hsnd
          exact (hpair_uniq q1 q2).mp (by rw [hfst, hsnd])
        · simp only [Equiv.apply_symm_apply] at hfst hsnd
          exact (hpair_uniq q1 q2).mp (by rw [hfst, hsnd, pair_comm])
        · simp only [Equiv.apply_symm_apply] at hfst hsnd
          exact (hpair_uniq q1 q2).mp (by rw [hfst, hsnd, pair_comm])
        · simp only [Equiv.apply_symm_apply] at hfst hsnd
          exact (hpair_uniq q1 q2).mp (by rw [hfst, hsnd])
      · intro p hp
        obtain ⟨q, hq⟩ := (mem_filter.mp hp).2
        refine ⟨q, mem_univ _, ?_⟩
        have hcol_p1 : col (eqU1 p.1).1 = false := (mem_filter.mp (eqU1 p.1).2).2
        have hcol_p2 : col (eqU2 p.2).1 = true := (mem_filter.mp (eqU2 p.2).2).2
        rcases hq with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · have hc1 : col (e1 q) = false := by rw [h1]; exact hcol_p1
          rw [dif_pos hc1]
          exact Prod.ext (eqU1.injective (by simp [h1])) (eqU2.injective (by simp [h2]))
        · have hc1 : col (e1 q) ≠ false := by rw [h1, hcol_p2]; decide
          rw [dif_neg hc1]
          exact Prod.ext (eqU1.injective (by simp [h2])) (eqU2.injective (by simp [h1]))
    have hrow : ∀ i : Fin U1.card, ∃ j : Fin U2.card, E_bip i j := by
      intro i
      obtain ⟨y, hy⟩ := hnoniso_adj (eqU1 i).1
      have hcol_y : col y = true :=
        bool_true_of_ne_false (hcol (eqU1 i).1 y hy) (mem_filter.mp (eqU1 i).2).2
      refine ⟨eqU2.symm ⟨y, mem_filter.mpr ⟨mem_univ _, hcol_y⟩⟩, ?_⟩
      dsimp [E_bip]; rw [Equiv.apply_symm_apply]; exact hy
    have hcol_ex : ∀ j : Fin U2.card, ∃ i : Fin U1.card, E_bip i j := by
      intro j
      obtain ⟨x, hx⟩ := hnoniso_adj (eqU2 j).1
      have hcol_x : col x = false :=
        bool_false_of_ne_true (hcol (eqU2 j).1 x hx) (mem_filter.mp (eqU2 j).2).2
      refine ⟨eqU1.symm ⟨x, mem_filter.mpr ⟨mem_univ _, hcol_x⟩⟩, ?_⟩
      dsimp [E_bip]; rw [Equiv.apply_symm_apply]; exact hadjG_sym hx
    have hdeg_bip : ∀ i j, E_bip i j →
        18 ≤ (univ.filter (E_bip i)).card + (univ.filter fun a => E_bip a j).card := by
      intro i j hij
      rw [hU1_nbrs i, hU2_nbrs j]
      exact hdegG_sum_adj _ _ hij
    obtain ⟨hU1_9, hU2_9, hK99, hn3_24, hn4_0, hn5_0, hn6_0⟩ :=
      complete_bipartite_of_moments E_bip hrow hcol_ex hdeg_bip hV_le19 hproj_ineq
        hexcess_nat (by rw [hbip_edges]; exact hmass_nat)
    -- Step 2d: K_{9,9} orthonormal basis {E σ i, F σ j} of range (projLin B)!
    have hV_18 : Fintype.card V = 18 := by omega
    have hfinrank_17 : Module.finrank ℝ (Submodule.span ℝ (Set.range uR)) = 17 := by omega
    -- Pick a unit vector e0 ∈ range (projLin B) orthogonal to span (range uR).
    obtain ⟨v_raw, hv_mem, hv_ne, hv_orth⟩ := exists_nonzero_ortho
      (Submodule.span ℝ (Set.range uR)) (LinearMap.range (projLin B)) hspan_uR_le
      (by rw [hfinrank_17, finrank_range_projLin B hp hl hsize hmeet]; omega)
    have hv_pos : 0 < Order12.Deficit18Frame.dot v_raw v_raw :=
      lt_of_le_of_ne (Order12.Deficit18Frame.dot_self_nonneg v_raw)
        (fun h => hv_ne (Order12.Deficit18Frame.dot_self_eq_zero.mp h.symm))
    let e0 : P → ℝ := (1 / Real.sqrt (Order12.Deficit18Frame.dot v_raw v_raw)) • v_raw
    have he0_mem : e0 ∈ LinearMap.range (projLin B) := Submodule.smul_mem _ _ hv_mem
    have he0_norm : Order12.Deficit18Frame.dot e0 e0 = 1 := by
      dsimp [e0]
      rw [Order12.Deficit18Frame.dot_smul_left, Order12.Deficit18Frame.dot_smul_right]
      have hsq : Real.sqrt (Order12.Deficit18Frame.dot v_raw v_raw) ^ 2 =
          Order12.Deficit18Frame.dot v_raw v_raw := Real.sq_sqrt (le_of_lt hv_pos)
      have hne : Real.sqrt (Order12.Deficit18Frame.dot v_raw v_raw) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hv_pos)
      field_simp [hne]; linarith
    have he0_orth : ∀ x ∈ Submodule.span ℝ (Set.range uR), Order12.Deficit18Frame.dot e0 x = 0 := by
      intro x hx; dsimp [e0]; rw [Order12.Deficit18Frame.dot_smul_left, hv_orth x hx, mul_zero]
    -- Also vVec B = Z ∈ span (range uR), so dot e0 (vVec B) = 0!
    have hV_eq_Z : vVec B = Z := by
      apply sub_eq_zero.mp
      apply Order12.Deficit18Frame.dot_self_eq_zero.mp
      rw [Order12.Deficit18Frame.dot_sub_left, Order12.Deficit18Frame.dot_sub_right,
        Order12.Deficit18Frame.dot_sub_right, Order12.Deficit18Frame.dot_comm (vVec B) Z,
        dot_vVec_self B hp hl hsize hmeet, hZ_norm, hZ_V]
      have hm18 : mR = 18 := by dsimp [mR]; exact_mod_cast hV_18
      rw [hU1_9, hU2_9, hm18]; norm_num
    have he0_V : Order12.Deficit18Frame.dot e0 (vVec B) = 0 := by
      rw [hV_eq_Z]; exact he0_orth _ (Φ ⟨zV, hzV_mem⟩).2
    -- Index U1 and U2 by Fin 9.
    let u1 : Fin 9 → V := fun i => (eqU1 (i.cast hU1_9.symm)).1
    let u2 : Fin 9 → V := fun j => (eqU2 (j.cast hU2_9.symm)).1
    have hu1_col : ∀ i : Fin 9, col (u1 i) = false := fun i => (mem_filter.mp (eqU1 _).2).2
    have hu2_col : ∀ j : Fin 9, col (u2 j) = true := fun j => (mem_filter.mp (eqU2 _).2).2
    have hu1_inj : Function.Injective u1 := fun i1 i2 h => by
      have := eqU1.injective (Subtype.ext h); exact Fin.ext (by simpa using congrArg Fin.val this)
    have hu2_inj : Function.Injective u2 := fun j1 j2 h => by
      have := eqU2.injective (Subtype.ext h); exact Fin.ext (by simpa using congrArg Fin.val this)
    have hu1_ne_u2 : ∀ i j : Fin 9, u1 i ≠ u2 j := fun i j h => by
      have h1 := hu1_col i; rw [h, hu2_col j] at h1; exact Bool.false_ne_true h1.symm
    -- For every (i, j) : Fin 9 × Fin 9, rootOf i j : RSub is the edge between u1 i and u2 j.
    have hedge_exists : ∀ i j : Fin 9, adjG (u1 i) (u2 j) := fun i j =>
      hK99 (i.cast hU1_9.symm) (j.cast hU2_9.symm)
    let rootOf : Fin 9 → Fin 9 → RSub := fun i j => Classical.choose (hedge_exists i j)
    have hrootOf_w : ∀ i j : Fin 9, w (rootOf i j) =
        (fun v : V => (if v = u1 i then 1 else 0) + (if v = u2 j then 1 else 0)) := by
      intro i j
      have hspec := Classical.choose_spec (hedge_exists i j)
      ext v; dsimp [w]
      rcases hspec with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]
      · rw [h1, h2, add_comm]
    have hrootOf_bij : ∀ p : RSub, ∃! ij : Fin 9 × Fin 9, rootOf ij.1 ij.2 = p := by
      intro p
      have hcol_p := hcol (e1 p) (e2 p) ⟨p, Or.inl ⟨rfl, rfl⟩⟩
      have hex : ∃ ij : Fin 9 × Fin 9, rootOf ij.1 ij.2 = p := by
        by_cases h1f : col (e1 p) = false
        · have h2t : col (e2 p) = true := bool_true_of_ne_false hcol_p h1f
          let i : Fin 9 := (eqU1.symm ⟨e1 p, mem_filter.mpr ⟨mem_univ _, h1f⟩⟩).cast hU1_9
          let j : Fin 9 := (eqU2.symm ⟨e2 p, mem_filter.mpr ⟨mem_univ _, h2t⟩⟩).cast hU2_9
          refine ⟨(i, j), ?_⟩
          have hspec := Classical.choose_spec (hedge_exists i j)
          have hu1i : u1 i = e1 p := by dsimp [u1, i]; simp
          have hu2j : u2 j = e2 p := by dsimp [u2, j]; simp
          have hpair : ({e1 (rootOf i j), e2 (rootOf i j)} : Finset V) = {e1 p, e2 p} := by
            rcases hspec with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · rw [h1, h2, hu1i, hu2j]
            · rw [h1, h2, hu1i, hu2j, pair_comm]
          exact (hpair_uniq _ _).mp hpair
        · have h1t : col (e1 p) = true := bool_eq_true_of_ne_false h1f
          have h2f : col (e2 p) = false := bool_false_of_ne_true hcol_p h1t
          let i : Fin 9 := (eqU1.symm ⟨e2 p, mem_filter.mpr ⟨mem_univ _, h2f⟩⟩).cast hU1_9
          let j : Fin 9 := (eqU2.symm ⟨e1 p, mem_filter.mpr ⟨mem_univ _, h1t⟩⟩).cast hU2_9
          refine ⟨(i, j), ?_⟩
          have hspec := Classical.choose_spec (hedge_exists i j)
          have hu1i : u1 i = e2 p := by dsimp [u1, i]; simp
          have hu2j : u2 j = e1 p := by dsimp [u2, j]; simp
          have hpair : ({e1 (rootOf i j), e2 (rootOf i j)} : Finset V) = {e1 p, e2 p} := by
            rcases hspec with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · rw [h1, h2, hu1i, hu2j, pair_comm]
            · rw [h1, h2, hu1i, hu2j]
          exact (hpair_uniq _ _).mp hpair
      obtain ⟨⟨i0, j0⟩, h0⟩ := hex
      refine ⟨(i0, j0), h0, ?_⟩
      rintro ⟨i1, j1⟩ h1
      have hEqW : w (rootOf i1 j1) = w (rootOf i0 j0) := by rw [h1, h0]
      have hu1_eq : u1 i1 = u1 i0 := by
        have hval := congrFun hEqW (u1 i1)
        rw [hrootOf_w, hrootOf_w] at hval
        simp only [↓reduceIte, hu1_ne_u2, add_zero] at hval
        by_contra hne
        rw [if_neg hne] at hval; norm_num at hval
      have hu2_eq : u2 j1 = u2 j0 := by
        have hval := congrFun hEqW (u2 j1)
        rw [hrootOf_w, hrootOf_w] at hval
        simp only [↓reduceIte, (hu1_ne_u2 _ _).symm, zero_add] at hval
        by_contra hne
        rw [if_neg hne] at hval; norm_num at hval
      exact Prod.ext (hu1_inj hu1_eq) (hu2_inj hu2_eq)
    -- Build Ei0, Fj0 ∈ span (range uR) and E σ i, F σ j ∈ range (projLin B).
    let basisV : V → V → ℝ := fun a b => if b = a then 1 else 0
    have hdot_ss18 : Order12.Deficit18Frame.dot s s = 18 := by
      simp only [Order12.Deficit18Frame.dot, s]
      have : ∀ v : V, (if col v = false then (1 : ℝ) else -1) * (if col v = false then 1 else -1) = 1 := by
        intro v; cases col v <;> norm_num
      simp_rw [this]; simp [hV_18]
    have hEi0_mem : ∀ i : Fin 9, basisV (u1 i) - (1 / 18 : ℝ) • s ∈ Submodule.span ℝ (Set.range w) := by
      intro i; rw [hspan_w_eq]
      change Order12.Deficit18Frame.dot (basisV (u1 i) - (1 / 18 : ℝ) • s) s = 0
      rw [Order12.Deficit18Frame.dot_sub_left, Order12.Deficit18Frame.dot_smul_left, hdot_ss18]
      unfold basisV; rw [dot_basis_left]; simp [s, hu1_col i]
    have hFj0_mem : ∀ j : Fin 9, basisV (u2 j) + (1 / 18 : ℝ) • s ∈ Submodule.span ℝ (Set.range w) := by
      intro j; rw [hspan_w_eq]
      change Order12.Deficit18Frame.dot (basisV (u2 j) + (1 / 18 : ℝ) • s) s = 0
      rw [Order12.Deficit18Frame.dot_add_left, Order12.Deficit18Frame.dot_smul_left, hdot_ss18]
      unfold basisV; rw [dot_basis_left]; simp [s, hu2_col j]
    let Ei0 : Fin 9 → P → ℝ := fun i => (Φ ⟨basisV (u1 i) - (1 / 18 : ℝ) • s, hEi0_mem i⟩).1
    let Fj0 : Fin 9 → P → ℝ := fun j => (Φ ⟨basisV (u2 j) + (1 / 18 : ℝ) • s, hFj0_mem j⟩).1
    let E : ℝ → Fin 9 → P → ℝ := fun σ i => Ei0 i + (σ / Real.sqrt 18) • e0
    let F : ℝ → Fin 9 → P → ℝ := fun σ j => Fj0 j - (σ / Real.sqrt 18) • e0
    have hsqrt18_ne : Real.sqrt 18 ≠ 0 := by positivity
    have hsq18 : Real.sqrt 18 ^ 2 = 18 := Real.sq_sqrt (by norm_num)
    have hEF_edge : ∀ (σ : ℝ) (i j : Fin 9), E σ i + F σ j = uVec B (rootOf i j).1 := by
      intro σ i j
      have h1 : E σ i + F σ j = Ei0 i + Fj0 j := by dsimp [E, F]; abel
      rw [h1]
      have hsum : (⟨basisV (u1 i) - (1 / 18 : ℝ) • s, hEi0_mem i⟩ : Submodule.span ℝ (Set.range w)) +
          ⟨basisV (u2 j) + (1 / 18 : ℝ) • s, hFj0_mem j⟩ =
          ⟨w (rootOf i j), Submodule.subset_span ⟨rootOf i j, rfl⟩⟩ := by
        apply Subtype.ext; ext v
        simp only [Submodule.coe_add, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
          hrootOf_w, basisV]
        ring
      have hmap := congrArg Subtype.val (map_add Φ
        ⟨basisV (u1 i) - (1 / 18 : ℝ) • s, hEi0_mem i⟩
        ⟨basisV (u2 j) + (1 / 18 : ℝ) • s, hFj0_mem j⟩)
      rw [hsum, gramEquiv_apply_gen] at hmap
      exact hmap.symm
    have hEF_mem : ∀ (σ : ℝ), (∀ i, E σ i ∈ LinearMap.range (projLin B)) ∧
        (∀ j, F σ j ∈ LinearMap.range (projLin B)) := fun σ =>
      ⟨fun i => Submodule.add_mem _ (hspan_uR_le (Φ _).2) (Submodule.smul_mem _ _ he0_mem),
       fun j => Submodule.sub_mem _ (hspan_uR_le (Φ _).2) (Submodule.smul_mem _ _ he0_mem)⟩
    have hEF_orth : ∀ (σ : ℝ), σ ^ 2 = 1 →
        (∀ i i', Order12.Deficit18Frame.dot (E σ i) (E σ i') = if i = i' then 1 else 0) ∧
        (∀ j j', Order12.Deficit18Frame.dot (F σ j) (F σ j') = if j = j' then 1 else 0) ∧
        (∀ i j, Order12.Deficit18Frame.dot (E σ i) (F σ j) = 0) := by
      intro σ hσ2
      have hEi0_e0 : ∀ i, Order12.Deficit18Frame.dot (Ei0 i) e0 = 0 := fun i => by
        rw [Order12.Deficit18Frame.dot_comm]; exact he0_orth _ (Φ _).2
      have hFj0_e0 : ∀ j, Order12.Deficit18Frame.dot (Fj0 j) e0 = 0 := fun j => by
        rw [Order12.Deficit18Frame.dot_comm]; exact he0_orth _ (Φ _).2
      have hfrac : (σ / Real.sqrt 18) * (σ / Real.sqrt 18) = 1 / 18 := by
        field_simp [hsqrt18_ne]; rw [hσ2, hsq18]; ring
      refine ⟨?_, ?_, ?_⟩
      · intro i i'
        dsimp [E]
        rw [Order12.Deficit18Frame.dot_add_left, Order12.Deficit18Frame.dot_add_right,
          Order12.Deficit18Frame.dot_add_right,
          Order12.Deficit18Frame.dot_smul_left (σ / Real.sqrt 18),
          Order12.Deficit18Frame.dot_smul_right (σ / Real.sqrt 18),
          Order12.Deficit18Frame.dot_smul_left (σ / Real.sqrt 18),
          Order12.Deficit18Frame.dot_smul_right (σ / Real.sqrt 18),
          Order12.Deficit18Frame.dot_comm e0 (Ei0 i'),
          hEi0_e0 i, hEi0_e0 i', he0_norm]
        have hd0 : Order12.Deficit18Frame.dot (Ei0 i) (Ei0 i') = (if i = i' then 1 else 0) - 1 / 18 := by
          dsimp [Ei0]; rw [gramEquiv_dot]
          rw [Order12.Deficit18Frame.dot_sub_left, Order12.Deficit18Frame.dot_sub_right,
            Order12.Deficit18Frame.dot_sub_right, Order12.Deficit18Frame.dot_smul_left,
            Order12.Deficit18Frame.dot_smul_right, Order12.Deficit18Frame.dot_smul_left,
            Order12.Deficit18Frame.dot_smul_right, Order12.Deficit18Frame.dot_comm s (basisV (u1 i')),
            hdot_ss18]
          unfold basisV
          rw [dot_basis_left, dot_basis_left, dot_basis_left]
          simp only [s, hu1_col i, hu1_col i', ↓reduceIte, hu1_inj.eq_iff]
          by_cases e : i = i' <;> simp [e]
        rw [hd0]; linarith
      · intro j j'
        dsimp [F]
        rw [Order12.Deficit18Frame.dot_sub_left, Order12.Deficit18Frame.dot_sub_right,
          Order12.Deficit18Frame.dot_sub_right,
          Order12.Deficit18Frame.dot_smul_left (σ / Real.sqrt 18),
          Order12.Deficit18Frame.dot_smul_right (σ / Real.sqrt 18),
          Order12.Deficit18Frame.dot_smul_left (σ / Real.sqrt 18),
          Order12.Deficit18Frame.dot_smul_right (σ / Real.sqrt 18),
          Order12.Deficit18Frame.dot_comm e0 (Fj0 j'),
          hFj0_e0 j, hFj0_e0 j', he0_norm]
        have hd0 : Order12.Deficit18Frame.dot (Fj0 j) (Fj0 j') = (if j = j' then 1 else 0) - 1 / 18 := by
          dsimp [Fj0]; rw [gramEquiv_dot]
          rw [Order12.Deficit18Frame.dot_add_left, Order12.Deficit18Frame.dot_add_right,
            Order12.Deficit18Frame.dot_add_right, Order12.Deficit18Frame.dot_smul_left,
            Order12.Deficit18Frame.dot_smul_right, Order12.Deficit18Frame.dot_smul_left,
            Order12.Deficit18Frame.dot_smul_right, Order12.Deficit18Frame.dot_comm s (basisV (u2 j')),
            hdot_ss18]
          unfold basisV
          rw [dot_basis_left, dot_basis_left, dot_basis_left]
          simp only [s, hu2_col j, hu2_col j', Bool.true_eq_false, ↓reduceIte, hu2_inj.eq_iff]
          by_cases e : j = j' <;> simp [e]
          ring
        rw [hd0]; linarith
      · intro i j
        dsimp [E, F]
        rw [Order12.Deficit18Frame.dot_add_left, Order12.Deficit18Frame.dot_sub_right,
          Order12.Deficit18Frame.dot_sub_right,
          Order12.Deficit18Frame.dot_smul_left (σ / Real.sqrt 18),
          Order12.Deficit18Frame.dot_smul_right (σ / Real.sqrt 18),
          Order12.Deficit18Frame.dot_smul_left (σ / Real.sqrt 18),
          Order12.Deficit18Frame.dot_smul_right (σ / Real.sqrt 18),
          Order12.Deficit18Frame.dot_comm e0 (Fj0 j),
          hEi0_e0 i, hFj0_e0 j, he0_norm]
        have hd0 : Order12.Deficit18Frame.dot (Ei0 i) (Fj0 j) = 1 / 18 := by
          dsimp [Ei0, Fj0]; rw [gramEquiv_dot]
          rw [Order12.Deficit18Frame.dot_sub_left, Order12.Deficit18Frame.dot_add_right,
            Order12.Deficit18Frame.dot_add_right, Order12.Deficit18Frame.dot_smul_left,
            Order12.Deficit18Frame.dot_smul_right, Order12.Deficit18Frame.dot_smul_left,
            Order12.Deficit18Frame.dot_smul_right, Order12.Deficit18Frame.dot_comm s (basisV (u2 j)),
            hdot_ss18]
          unfold basisV
          rw [dot_basis_left, dot_basis_left, dot_basis_left]
          simp only [s, hu1_col i, hu2_col j, hu1_ne_u2 i j, Bool.true_eq_false, ↓reduceIte]
          ring
        rw [hd0]; linarith
    -- Dot with V: dot (vVec B) (E σ i) = 1 and dot (vVec B) (F σ j) = 1!
    have hEF_V : ∀ (σ : ℝ) (i : Fin 9), Order12.Deficit18Frame.dot (vVec B) (E σ i) = 1 := by
      intro σ i
      dsimp [E]
      rw [Order12.Deficit18Frame.dot_add_right, Order12.Deficit18Frame.dot_smul_right,
        Order12.Deficit18Frame.dot_comm (vVec B) e0, he0_V, mul_zero, add_zero, hV_eq_Z]
      dsimp [Z, Ei0]; rw [gramEquiv_dot]
      change Order12.Deficit18Frame.dot zV (basisV (u1 i) - (1 / 18 : ℝ) • s) = 1
      have hzV1 : zV = fun _ => 1 := by
        ext v; dsimp [zV, mR]; rw [hU1_9, hU2_9, hV_18]; split_ifs <;> norm_num
      rw [hzV1, Order12.Deficit18Frame.dot_sub_right, Order12.Deficit18Frame.dot_smul_right]
      have h1s : Order12.Deficit18Frame.dot (fun _ : V => 1) s = 0 := by
        simp only [Order12.Deficit18Frame.dot, one_mul, s]
        have hsp : ∀ v : V, (if col v = false then (1 : ℝ) else -1) =
            (if col v = false then 1 else 0) + (if col v = true then -1 else 0) := by
          intro v; cases col v <;> simp
        simp_rw [hsp, sum_add_distrib, ← sum_filter, sum_const, nsmul_eq_mul]
        change (U1.card : ℝ) * 1 + (U2.card : ℝ) * (-1) = 0
        rw [hU1_9, hU2_9]; norm_num
      rw [h1s, mul_zero, sub_zero, Order12.Deficit18Frame.dot_comm]
      unfold basisV; rw [dot_basis_left]
    -- Parseval in range (projLin B): any x ∈ range (projLin B) orthogonal to all E 1 i + F 1 j is a multiple of e0!
    have hparseval_orth : ∀ x ∈ LinearMap.range (projLin B),
        (∀ i j : Fin 9, Order12.Deficit18Frame.dot x (uVec B (rootOf i j).1) = 0) →
        x = Order12.Deficit18Frame.dot x e0 • e0 := by
      intro x hx hperp
      let y := x - Order12.Deficit18Frame.dot x e0 • e0
      have hy_mem : y ∈ LinearMap.range (projLin B) := Submodule.sub_mem _ hx (Submodule.smul_mem _ _ he0_mem)
      have hy_e0 : Order12.Deficit18Frame.dot y e0 = 0 := by
        dsimp [y]; rw [Order12.Deficit18Frame.dot_sub_left, Order12.Deficit18Frame.dot_smul_left, he0_norm]; ring
      have hy_uR : ∀ r : RSub, Order12.Deficit18Frame.dot y (uR r) = 0 := by
        intro r
        obtain ⟨⟨i, j⟩, rfl, _⟩ := hrootOf_bij r
        dsimp [y]
        rw [Order12.Deficit18Frame.dot_sub_left, Order12.Deficit18Frame.dot_smul_left,
          hperp i j, he0_orth _ (Submodule.subset_span ⟨rootOf i j, rfl⟩)]; ring
      -- Show span(range uR) ⊔ span{e0} = range (projLin B), so y is orthogonal to itself!
      let S18 := Submodule.span ℝ (Set.range uR) ⊔ Submodule.span ℝ {e0}
      have hS18_le : S18 ≤ LinearMap.range (projLin B) :=
        sup_le hspan_uR_le (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr he0_mem))
      have hdisj : Disjoint (Submodule.span ℝ (Set.range uR)) (Submodule.span ℝ {e0}) := by
        rw [Submodule.disjoint_def]
        intro a ha1 ha2
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ha2
        have h0 := he0_orth (c • e0) ha1
        rw [Order12.Deficit18Frame.dot_smul_right, he0_norm, mul_one] at h0
        rw [h0, zero_smul]
      have hfin_e0 : Module.finrank ℝ (Submodule.span ℝ {e0}) = 1 :=
        finrank_span_singleton (fun h => by rw [h, Order12.Deficit18Frame.dot_zero_left] at he0_norm; norm_num at he0_norm)
      have hfin_S18 : Module.finrank ℝ S18 = 18 := by
        have h := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span ℝ (Set.range uR)) (Submodule.span ℝ {e0})
        rw [hdisj.eq_bot, finrank_bot, add_zero, hfinrank_17, hfin_e0] at h
        exact h
      have hS18_eq : S18 = LinearMap.range (projLin B) :=
        Submodule.eq_of_le_of_finrank_eq hS18_le (by rw [hfin_S18, finrank_range_projLin B hp hl hsize hmeet])
      have hy_S18 : y ∈ S18 := hS18_eq ▸ hy_mem
      have hy_orth_S18 : ∀ z ∈ S18, Order12.Deficit18Frame.dot y z = 0 := by
        intro z hz
        obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hz
        rw [Order12.Deficit18Frame.dot_add_right]
        have ha0 : Order12.Deficit18Frame.dot y a = 0 := by
          obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp ha
          rw [← hc, Order12.Deficit18Frame.dot_sum_right]
          exact sum_eq_zero fun r _ => by rw [Order12.Deficit18Frame.dot_smul_right, hy_uR r, mul_zero]
        have hb0 : Order12.Deficit18Frame.dot y b = 0 := by
          obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hb
          rw [Order12.Deficit18Frame.dot_smul_right, hy_e0, mul_zero]
        linarith
      exact sub_eq_zero.mp (Order12.Deficit18Frame.dot_self_eq_zero.mp (hy_orth_S18 y hy_S18))
    exact new_block_of_139_k99 B hp hl hsize hmeet h12
      hn3_24 hn4_0 hn5_0 hn6_0
      rootOf hrootOf_bij e0 Ei0 Fj0 he0_norm
      (fun i => by rw [Order12.Deficit18Frame.dot_comm]; exact he0_orth _ (Φ _).2)
      (fun j => by rw [Order12.Deficit18Frame.dot_comm]; exact he0_orth _ (Φ _).2)
      E F (fun _ _ => rfl) (fun _ _ => rfl)
      hEF_edge hEF_mem hEF_orth hEF_V hparseval_orth

/-- Corollary: `N` from `new_block_of_139` is distinct from all 139 old blocks, so
any 139 qualifying blocks on `Fin 157` extend to 140 qualifying blocks. -/
theorem extend_139_to_140
    (S : Finset (Finset (Fin 157))) (hcard : S.card = 139)
    (hsize : ∀ b ∈ S, b.card = 13)
    (hmeet : ∀ b ∈ S, ∀ c ∈ S, b ≠ c → (b ∩ c).card = 1) :
    ∃ T : Finset (Finset (Fin 157)), S ⊆ T ∧ T.card = 140 ∧
      (∀ b ∈ T, b.card = 13) ∧ (∀ b ∈ T, ∀ c ∈ T, b ≠ c → (b ∩ c).card = 1) := by
  let B : { b : Finset (Fin 157) // b ∈ S } → Finset (Fin 157) := Subtype.val
  have hl : Fintype.card { b : Finset (Fin 157) // b ∈ S } = 139 := by simp [hcard]
  obtain ⟨N, hNcard, hNmeet⟩ := new_block_of_139 B (by simp) hl
    (fun l => hsize l.1 l.2) (fun l m hlm => hmeet l.1 l.2 m.1 m.2 (fun e => hlm (Subtype.ext e)))
  have hN_not_S : N ∉ S := by
    intro hNS
    have h1 := hNmeet ⟨N, hNS⟩
    simp [B, hNcard] at h1
  refine ⟨insert N S, subset_insert N S, ?_, ?_, ?_⟩
  · rw [card_insert_of_notMem hN_not_S, hcard]
  · intro b hb
    rcases mem_insert.mp hb with rfl | hbS
    · exact hNcard
    · exact hsize b hbS
  · intro b hb c hc hbc
    rcases mem_insert.mp hb with rfl | hbS <;> rcases mem_insert.mp hc with rfl | hcS
    · exact absurd rfl hbc
    · exact hNmeet ⟨c, hcS⟩
    · rw [inter_comm]; exact hNmeet ⟨b, hbS⟩
    · exact hmeet b hbS c hcS hbc

end Main139

end Order12.Deficit18Complete

theorem OMA.solution : OMA.R_Erdos723_erdos_723_variants_eq_12_R1_H1_R1_H1_R1.H2 := by
  intro S hcard hsize hmeet
  have hinter : ∀ b ∈ S, ∀ c ∈ S, b ≠ c → (b ∩ c).card = 1 := by
    intro b hb c hc hbc
    apply Finset.card_eq_one_iff_existsUnique.mpr
    simpa using hmeet b hb c hc hbc
  obtain ⟨T, hST, hTcard, hTsize, hTmeet⟩ :=
    Order12.Deficit18Complete.extend_139_to_140 S hcard hsize hinter
  refine ⟨T, hST, hTcard, hTsize, ?_⟩
  intro b hb c hc hbc
  simpa using Finset.card_eq_one_iff_existsUnique.mp (hTmeet b hb c hc hbc)
