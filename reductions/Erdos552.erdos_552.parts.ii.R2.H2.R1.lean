import OMAReductions.R_Erdos552_erdos_552_parts_ii_R2
import Mathlib

/-!
# Saturated quadrilateral-free graphs in the quadrilateral versus star problem

Burr, Erdős, Faudree, Rousseau and Schelp asked whether the deficit below the
square-root bound is unbounded. The preceding reduction uses a star size and
a degree threshold. Here one only chooses the number of vertices. The graphs
to be tested are saturated: adding any missing edge closes a four-cycle.
The reverse implication below shows that the new order criterion is necessary
as well as sufficient. The affine polarity graph, with adjacency given by
y + y' = x x', supplies explicit obstructions to candidate orders near the
square of a prime power. This is the finite-field construction described in
Verstraëte, Extremal problems for cycles in graphs, section 4.2. Parsons
used polarity graphs for star versus quadrilateral Ramsey numbers
(Trans. Amer. Math. Soc. 209 (1975), 33–44).

Lean formalization by @KoaOkano.
-/

namespace OMA.R_Erdos552_erdos_552_parts_ii_R2_H2_R1

open SimpleGraph

/-- Complete a quadrilateral-free graph until every nonedge is the pair of
endpoints of a path of length three with four distinct vertices. -/
def H1 : Prop :=
  ∀ (N : ℕ) (G : SimpleGraph (Fin N)), ¬ (cycleGraph 4).IsContained G →
    ∃ S : SimpleGraph (Fin N), G ≤ S ∧ ¬ (cycleGraph 4).IsContained S ∧
      ∀ x y, x ≠ y → ¬ S.Adj x y →
        ∃ a b, a ≠ y ∧ b ≠ x ∧ S.Adj x a ∧ S.Adj a b ∧ S.Adj b y

/-- At some order every saturated quadrilateral-free graph has a vertex
whose degree falls at least k below the integer square root of the order. -/
def H2 : Prop :=
  ∀ k : ℕ, ∃ N : ℕ, k ≤ N.sqrt ∧
    ∀ (S : SimpleGraph (Fin N)) [DecidableRel S.Adj], ¬ (cycleGraph 4).IsContained S →
      (∀ x y, x ≠ y → ¬ S.Adj x y →
        ∃ a b, a ≠ y ∧ b ≠ x ∧ S.Adj x a ∧ S.Adj a b ∧ S.Adj b y) →
      ∃ v, S.degree v + k ≤ N.sqrt

open Finset in
/-- Restrict an affine polarity graph over a finite field to exactly N points.
Each complete vertical column contributes one candidate neighbor to every
point. Only a loop can be lost. -/
theorem affineFieldGraph (F : Type*) [Field F] [Fintype F] {q N : ℕ}
    (cardF : Fintype.card F = q) (cap : N ≤ q ^ 2) :
    ∃ G : SimpleGraph (Fin N), ¬ (cycleGraph 4).IsContained G ∧
      ∀ [DecidableRel G.Adj] (v : Fin N), N / q ≤ G.degree v + 1 := by
  classical
  have qpos : 0 < q := cardF ▸ Fintype.card_pos
  have rows : N / q ≤ (univ : Finset F).card := by
    rw [card_univ, cardF]
    have h : N / q ≤ q ^ 2 / q := Nat.div_le_div_right cap
    simpa [pow_two, Nat.mul_div_cancel, qpos] using h
  obtain ⟨A, _, hA⟩ := exists_subset_card_eq rows
  let slab := A ×ˢ (univ : Finset F)
  have slabSize : slab.card ≤ N := by
    simpa [slab, hA, cardF] using Nat.div_mul_le_self N q
  have room : N ≤ (univ : Finset (F × F)).card := by
    simpa [Fintype.card_prod, cardF, pow_two] using cap
  obtain ⟨T, included, _, hT⟩ := exists_subsuperset_card_eq (subset_univ slab) slabSize room
  let e := T.equivFinOfCardEq hT
  let pt : Fin N → F × F := fun i => (e.symm i).val
  have inj : Function.Injective pt := fun _ _ h => e.symm.injective (Subtype.ext h)
  have onto (z : F × F) (hz : z ∈ T) : ∃ i, pt i = z :=
    ⟨e ⟨z, hz⟩, by simp [pt]⟩
  let G : SimpleGraph (Fin N) := fromRel fun i j =>
    (pt i).2 + (pt j).2 = (pt i).1 * (pt j).1
  have adj (i j : Fin N) : G.Adj i j ↔ i ≠ j ∧
      (pt i).2 + (pt j).2 = (pt i).1 * (pt j).1 := by
    refine ⟨fun h => ⟨h.1, ?_⟩, fun h => ⟨h.1, Or.inl h.2⟩⟩
    rcases h.2 with h | h
    · exact h
    · simpa only [add_comm (pt j).2 (pt i).2, mul_comm (pt j).1 (pt i).1] using h
  refine ⟨G, ?_, ?_⟩
  · rintro ⟨φ⟩
    have rel (i j : Fin 4) (h : (cycleGraph 4).Adj i j) :
        (pt (φ i)).2 + (pt (φ j)).2 = (pt (φ i)).1 * (pt (φ j)).1 :=
      ((adj _ _).mp (φ.toHom.map_adj h)).2
    have e01 := rel 0 1 (by decide)
    have e21 := rel 2 1 (by decide)
    have e03 := rel 0 3 (by decide)
    have e23 := rel 2 3 (by decide)
    have prod : ((pt (φ 0)).1 - (pt (φ 2)).1) * ((pt (φ 1)).1 - (pt (φ 3)).1) = 0 := by
      linear_combination -e01 + e21 + e03 - e23
    rcases mul_eq_zero.mp prod with h | h
    · have hx := sub_eq_zero.mp h
      have hy : (pt (φ 0)).2 = (pt (φ 2)).2 := by
        apply add_right_cancel (b := (pt (φ 1)).2)
        rw [e01, e21, hx]
      exact (by decide : (0 : Fin 4) ≠ 2) (φ.injective (inj (Prod.ext hx hy)))
    · have hx := sub_eq_zero.mp h
      have hy : (pt (φ 1)).2 = (pt (φ 3)).2 := by
        apply add_left_cancel (a := (pt (φ 0)).2)
        rw [e01, e03, hx]
      exact (by decide : (1 : Fin 4) ≠ 3) (φ.injective (inj (Prod.ext hx hy)))
  · intro _ v
    let hit (x : F) := (x, (pt v).1 * x - (pt v).2)
    let hits := A.image hit
    have hitInj : Function.Injective hit := fun _ _ h => congrArg Prod.fst h
    have count : hits.card = N / q := by
      rw [show hits.card = A.card from card_image_of_injective _ hitInj, hA]
    have cover : hits.erase (pt v) ⊆ (G.neighborFinset v).image pt := by
      intro z hz
      obtain ⟨neq, mem⟩ := mem_erase.mp hz
      obtain ⟨x, hx, rfl⟩ := mem_image.mp mem
      have ht : hit x ∈ T := included (mem_product.mpr ⟨hx, mem_univ _⟩)
      obtain ⟨i, hi⟩ := onto _ ht
      refine mem_image.mpr ⟨i, (G.mem_neighborFinset v i).mpr ((adj v i).mpr ⟨?_, ?_⟩), hi⟩
      · intro h
        exact neq (hi.symm.trans (congrArg pt h.symm))
      · rw [hi]
        dsimp [hit]
        ring
    have smaller := card_le_card cover
    rw [card_image_of_injective _ inj, card_neighborFinset_eq_degree] at smaller
    have drop := pred_card_le_card_erase (s := hits) (a := pt v)
    omega

/-- A witness to a degree deficit cannot lie just below the square of a
finite-field order. If q² covers N, its distance above ⌊√N⌋ is at least k−1. -/
theorem fieldOrderGap (complete : H1) (F : Type*) [Field F] [Fintype F] {k N q : ℕ}
    (cardF : Fintype.card F = q) (cap : N ≤ q ^ 2)
    (witness : ∀ (S : SimpleGraph (Fin N)) [DecidableRel S.Adj],
      ¬ (cycleGraph 4).IsContained S →
      (∀ x y, x ≠ y → ¬ S.Adj x y →
        ∃ a b, a ≠ y ∧ b ≠ x ∧ S.Adj x a ∧ S.Adj a b ∧ S.Adj b y) →
      ∃ v, S.degree v + k ≤ N.sqrt) :
    N.sqrt + k ≤ q + 1 := by
  classical
  obtain ⟨G, free, dense⟩ := affineFieldGraph F cardF cap
  obtain ⟨S, sub, sf, sat⟩ := complete N G free
  obtain ⟨v, hv⟩ := witness S sf sat
  have d := dense v
  have mono : G.degree v ≤ S.degree v := G.degree_le_of_le sub
  have qpos : 0 < q := cardF ▸ Fintype.card_pos
  have square : N.sqrt ^ 2 ≤ N := Nat.le_sqrt'.mp le_rfl
  have arith : 2 * N.sqrt ≤ q + N / q := by
    have bound : 2 * N.sqrt * q ≤ q * q + N := by
      zify at square ⊢
      nlinarith [sq_nonneg ((N.sqrt : ℤ) - (q : ℤ))]
    have divBound : 2 * N.sqrt * q / q ≤ (q * q + N) / q := Nat.div_le_div_right bound
    simpa [Nat.mul_add_div qpos, qpos] using divBound
  omega

/-- In particular, all prime powers supply excluded orders for large deficits. -/
theorem primePowerGap (complete : H1) {p e k N : ℕ} (hp : p.Prime) (he : e ≠ 0)
    (cap : N ≤ (p ^ e) ^ 2)
    (witness : ∀ (S : SimpleGraph (Fin N)) [DecidableRel S.Adj],
      ¬ (cycleGraph 4).IsContained S →
      (∀ x y, x ≠ y → ¬ S.Adj x y →
        ∃ a b, a ≠ y ∧ b ≠ x ∧ S.Adj x a ∧ S.Adj a b ∧ S.Adj b y) →
      ∃ v, S.degree v + k ≤ N.sqrt) :
    N.sqrt + k ≤ p ^ e + 1 := by
  classical
  let _ : Fact p.Prime := ⟨hp⟩
  let _ : NeZero e := ⟨he⟩
  let _ : Fintype (GaloisField p e) := Fintype.ofFinite _
  exact fieldOrderGap complete (GaloisField p e)
    (by rw [← Nat.card_eq_fintype_card, GaloisField.card p e he]) cap witness

/-- Two nontrivial coprime factors cannot multiply to a prime power. -/
private theorem notPrimePowerOfCoprime {a b : ℕ} (ha : 1 < a) (hb : 1 < b)
    (cop : a.Coprime b) : ¬ IsPrimePow (a * b) := by
  intro power
  obtain ⟨p, e, hp, _, eq⟩ := (isPrimePow_nat_iff _).mp power
  have divides {t : ℕ} (ht : 1 < t) (h : t ∣ a * b) : p ∣ t := by
    rw [← eq] at h
    obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow hp).mp h
    have nz : j ≠ 0 := by
      intro zero
      simp [zero] at hj
      omega
    rw [hj]
    exact dvd_pow_self _ nz
  have common := Nat.dvd_gcd (divides ha (dvd_mul_right a b))
    (divides hb (dvd_mul_left b a))
  rw [cop.gcd_eq_one] at common
  exact hp.not_dvd_one common

/-- The arithmetic obstruction still leaves arbitrarily large candidate
intervals. Each integer M+j has two nontrivial coprime factors because M is
a multiple of j². This does not assert the graph deficit at those orders. -/
theorem primePowerFreeIntervals (length lower : ℕ) :
    ∃ r > lower, ∀ q ∈ Set.Ico r (r + length), ¬ IsPrimePow q := by
  let L := (length + 2).factorial
  let M := (lower + 1) * L ^ 2
  have positive : 0 < L := Nat.factorial_pos _
  have rises : lower + 1 ≤ M := Nat.le_mul_of_pos_right _ (pow_pos positive 2)
  refine ⟨M + 2, by omega, ?_⟩
  intro q hq
  obtain ⟨lo, hi⟩ := hq
  let j := q - M
  have lowj : 2 ≤ j := by dsimp [j]; omega
  have highj : j ≤ length + 2 := by dsimp [j]; omega
  obtain ⟨a, ha⟩ : j ∣ L := Nat.dvd_factorial (by omega) highj
  have apos : 0 < a := by
    by_contra! zero
    have az : a = 0 := by omega
    simp [az] at ha
    omega
  have factor : q = j * (j * ((lower + 1) * a ^ 2) + 1) := by
    have eq : q = M + j := by dsimp [j]; omega
    rw [eq]
    dsimp only [M]
    rw [ha]
    ring
  rw [factor]
  apply notPrimePowerOfCoprime (by omega)
  · have pos : 0 < j * ((lower + 1) * a ^ 2) := by positivity
    omega
  · simp

/-- Square orders with arbitrarily large lower endpoints pass every finite-field
exclusion above. They are explicit candidates for the remaining graph test. -/
theorem candidateSquares (k lower : ℕ) :
    ∃ N > lower, ∀ p e : ℕ, p.Prime → e ≠ 0 → N ≤ (p ^ e) ^ 2 →
      N.sqrt + k ≤ p ^ e + 1 := by
  obtain ⟨r, hr, gap⟩ := primePowerFreeIntervals k lower
  have rp : 0 < r := by omega
  refine ⟨r ^ 2, hr.trans_le (by nlinarith), ?_⟩
  intro p e prime nonzero covers
  rw [Nat.sqrt_eq' (n := r)]
  have left : r ≤ p ^ e := by
    by_contra! h
    exact (Nat.pow_lt_pow_left h (by decide : (2 : ℕ) ≠ 0)).not_ge covers
  have right : r + k ≤ p ^ e := by
    by_contra! h
    exact gap (p ^ e) ⟨left, h⟩ ((isPrimePow_nat_iff _).mpr ⟨p, e, prime, Nat.pos_of_ne_zero nonzero, rfl⟩)
  omega

/-- Every obstruction from the parent problem already gives a witness to the
single-order criterion, even before the saturation restriction is imposed. -/
theorem necessary (obstruction : OMA.R_Erdos552_erdos_552_parts_ii_R2.H2) : H2 := by
  intro k
  obtain ⟨n, d, hsq, hdeg⟩ := obstruction k
  have hroot : d + k ≤ (n + d).sqrt := Nat.le_sqrt'.mpr (hsq.trans (by omega))
  refine ⟨n + d, by omega, ?_⟩
  intro S _ hfree _
  obtain ⟨v, hv⟩ := hdeg S hfree
  exact ⟨v, by omega⟩

theorem main : H1 → H2 → OMA.R_Erdos552_erdos_552_parts_ii_R2.H2 := by
  classical
  intro complete deficient k
  obtain ⟨N, room, sparse⟩ := deficient (k + 2)
  let r := N.sqrt
  let d := r - (k + 2) + 1
  let n := N - d
  change k + 2 ≤ r at room
  have hr : r ≤ N := Nat.sqrt_le_self N
  have hd : d ≤ r := by dsimp [d]; omega
  have sum : n + d = N := Nat.sub_add_cancel (hd.trans hr)
  have ds : d + k = r - 1 := by dsimp [d]; omega
  have square : r ^ 2 ≤ N := Nat.le_sqrt'.mp (le_refl N.sqrt)
  have slack : (r - 1) ^ 2 + r ≤ r ^ 2 := by
    obtain ⟨t, ht⟩ : ∃ t, r = t + 1 := ⟨r - 1, by omega⟩
    rw [ht, Nat.add_sub_cancel]
    nlinarith
  refine ⟨n, d, ?_, ?_⟩
  · rw [ds]
    dsimp [n]
    omega
  · rw [sum]
    intro G _ hfree
    obtain ⟨S, hsub, hS, hsaturated⟩ := complete N G hfree
    obtain ⟨v, hv⟩ := sparse S hS hsaturated
    have mono : G.degree v ≤ S.degree v := G.degree_le_of_le hsub
    change S.degree v + (k + 2) ≤ r at hv
    exact ⟨v, by dsimp [d]; omega⟩

end OMA.R_Erdos552_erdos_552_parts_ii_R2_H2_R1
