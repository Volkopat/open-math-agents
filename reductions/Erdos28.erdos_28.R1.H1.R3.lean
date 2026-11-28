import OMAReductions.R_Erdos28_erdos_28_R1
import Mathlib.Combinatorics.Additive.CauchyDavenport

/-!
# Erdős–Turán finite obstructions via common translates

An ordered sum fiber in a translation pattern P amplifies any nonempty fiber
in the common overlap of the translates by P. Consequently, once a finite
obstruction is known at a lower cap, a candidate at a higher cap can be
discarded if any suitable common overlap covers the old obstruction interval.
The induction asks for an obstruction only among the surviving prefixes.

The starting cap-seven instance is the published computational case of
Borwein, Choi and Chu, Math. Comp. 75 (2006), DOI 10.1090/S0025-5718-05-01777-1.
Their Table 1 gives maximum degree 328 for globally capped finite bases;
the degree-to-prefix transfer in R1.H1.R1 gives cutoff 2*328+1. H1 leaves
this finite computation to be certified in Lean rather than assuming it
as an axiom. H2 is still an open induction step.

Credit: @caa1982.
-/

namespace OMA.R_Erdos28_erdos_28_R1_H1_R3

open Finset AdditiveCombinatorics
open scoped Pointwise

/-- The published cap-seven base case at the prefix cutoff 657. -/
def H1 : Prop := ∀ S : Finset ℕ, S ⊆ Iic 657 →
  (∀ n ≤ 657, ∃ a ∈ S, ∃ b ∈ S, a + b = n) →
  ∃ n ≤ 657, 7 < sumRep (S : Set ℕ) n

/-- Advance one cap using only prefixes whose common translates fail every
available lower-cap obstruction test. -/
def H2 : Prop :=
  let obstruction := fun (g L : ℕ) => ∀ S : Finset ℕ, S ⊆ Iic L →
    (∀ n ≤ L, ∃ a ∈ S, ∃ b ∈ S, a + b = n) → ∃ n ≤ L, g < sumRep (S : Set ℕ) n
  ∀ g D : ℕ, 7 ≤ g → obstruction g D → ∃ L ≥ D, ∀ S : Finset ℕ, S ⊆ Iic L →
    (∀ n ≤ L, ∃ a ∈ S, ∃ b ∈ S, a + b = n) →
    (∀ b M : ℕ, b ≤ g → obstruction b M → ∀ (P : Finset ℕ) (s : ℕ),
      g + 2 - b ≤ sumRep (P : Set ℕ) s → M + s ≤ L →
      ∃ n ≤ M, ¬ ∃ x y : ℕ, (∀ p ∈ P, x + p ∈ S) ∧
        (∀ p ∈ P, y + p ∈ S) ∧ x + y = n) →
    ∃ n ≤ L, g + 1 < sumRep (S : Set ℕ) n

theorem first_coordinate_fiber (A : Set ℕ) (n : ℕ) :
    ∃ F : Finset ℕ, F.card = sumRep A n ∧
      ∀ a, a ∈ F ↔ ∃ b ∈ A, a ∈ A ∧ a + b = n := by
  classical
  let R := (antidiagonal n).filter (fun p : ℕ × ℕ => p.1 ∈ A ∧ p.2 ∈ A)
  have memR (p : ℕ × ℕ) : p ∈ R ↔ p.1 + p.2 = n ∧ p.1 ∈ A ∧ p.2 ∈ A := by
    simp only [R, mem_filter, Finset.HasAntidiagonal.mem_antidiagonal]
  refine ⟨R.image Prod.fst, ?_, ?_⟩
  · rw [sumRep_def]
    change (R.image Prod.fst).card = R.card
    apply card_image_iff.mpr
    intro a ha b hb hab
    have ha' := ((memR a).mp ha).1
    have hb' := ((memR b).mp hb).1
    exact Prod.ext hab (by omega)
  · intro a
    simp only [mem_image, Prod.exists, memR]
    constructor
    · rintro ⟨a', b, ⟨hs, ha, hb⟩, rfl⟩
      exact ⟨b, hb, ha, hs⟩
    · rintro ⟨b, hb, ha, hs⟩
      exact ⟨a, b, ⟨hs, ha, hb⟩, rfl⟩

/-- Add the two first-coordinate fibers. Cancellativity and the order on
the naturals give the required lower bound on the size of their sumset. -/
theorem add_fiber_bound {A B C : Set ℕ} (h : B + C ⊆ A) {n m : ℕ}
    (hn : 0 < sumRep B n) (hm : 0 < sumRep C m) :
    sumRep B n + sumRep C m - 1 ≤ sumRep A (n + m) := by
  classical
  obtain ⟨U, hU, memU⟩ := first_coordinate_fiber B n
  obtain ⟨V, hV, memV⟩ := first_coordinate_fiber C m
  obtain ⟨W, hW, memW⟩ := first_coordinate_fiber A (n + m)
  have hU' : U.Nonempty := card_pos.mp (hU ▸ hn)
  have hV' : V.Nonempty := card_pos.mp (hV ▸ hm)
  have sub : U + V ⊆ W := by
    intro a ha
    obtain ⟨b, hb, c, hc, rfl⟩ := Finset.mem_add.mp ha
    obtain ⟨b', hb', hb, hs⟩ := (memU b).mp hb
    obtain ⟨c', hc', hc, ht⟩ := (memV c).mp hc
    exact (memW _).mpr ⟨b' + c', h (Set.add_mem_add hb' hc'),
      h (Set.add_mem_add hb hc), by omega⟩
  have bound := (cauchy_davenport_add_of_linearOrder_isCancelAdd hU' hV').trans (card_le_card sub)
  rwa [hU, hV, hW] at bound

/-- An earlier obstruction and the cap of S prevent a prefix cover inside
an overlap whose translation pattern has a large enough representation fiber. -/
theorem missing_overlap (S P : Finset ℕ) (G b M s L : ℕ) (hb : b ≤ G)
    (cap : ∀ n ≤ L, sumRep (S : Set ℕ) n ≤ G)
    (obstruction : ∀ T : Finset ℕ, T ⊆ Iic M →
      (∀ n ≤ M, ∃ a ∈ T, ∃ b ∈ T, a + b = n) → ∃ n ≤ M, b < sumRep (T : Set ℕ) n)
    (pattern : G + 1 - b ≤ sumRep (P : Set ℕ) s) (hs : M + s ≤ L) :
    ∃ n ≤ M, ¬ ∃ x y : ℕ, (∀ p ∈ P, x + p ∈ S) ∧
      (∀ p ∈ P, y + p ∈ S) ∧ x + y = n := by
  classical
  let T := (Iic M).filter (fun x => ∀ p ∈ P, x + p ∈ S)
  by_contra h
  have cover (n : ℕ) (hn : n ≤ M) : ∃ x ∈ T, ∃ y ∈ T, x + y = n := by
    have hex : ∃ x y : ℕ, (∀ p ∈ P, x + p ∈ S) ∧
        (∀ p ∈ P, y + p ∈ S) ∧ x + y = n := by
      by_contra absent
      exact h ⟨n, hn, absent⟩
    obtain ⟨x, y, hx, hy, hxy⟩ := hex
    exact ⟨x, mem_filter.mpr ⟨mem_Iic.mpr (by omega), hx⟩,
      y, mem_filter.mpr ⟨mem_Iic.mpr (by omega), hy⟩, hxy⟩
  obtain ⟨n, hn, hlarge⟩ := obstruction T (filter_subset _ _) cover
  have inclusion : (T : Set ℕ) + (P : Set ℕ) ⊆ (S : Set ℕ) := by
    rintro _ ⟨x, hx, p, hp, rfl⟩
    exact (mem_filter.mp hx).2 p hp
  have gain := add_fiber_bound inclusion (n := n) (m := s)
    (show 0 < sumRep (T : Set ℕ) n by omega) (show 0 < sumRep (P : Set ℕ) s by omega)
  have bound := cap (n + s) (by omega)
  omega

theorem main : H1 → H2 → OMA.R_Erdos28_erdos_28_R1.H1 := by
  classical
  intro base step
  have all (j : ℕ) : ∃ L : ℕ, ∀ S : Finset ℕ, S ⊆ Iic L →
      (∀ n ≤ L, ∃ a ∈ S, ∃ b ∈ S, a + b = n) →
      ∃ n ≤ L, 7 + j < sumRep (S : Set ℕ) n := by
    induction j with
    | zero => exact ⟨657, base⟩
    | succ j ih =>
      obtain ⟨D, hD⟩ := ih
      obtain ⟨L, _, test⟩ := step (7 + j) D (by omega) hD
      refine ⟨L, fun S sub cover => ?_⟩
      by_contra! cap
      have overlaps (b M : ℕ) (hb : b ≤ 7 + j)
          (obs : ∀ T : Finset ℕ, T ⊆ Iic M →
            (∀ n ≤ M, ∃ a ∈ T, ∃ b ∈ T, a + b = n) → ∃ n ≤ M, b < sumRep (T : Set ℕ) n)
          (P : Finset ℕ) (s : ℕ) (pat : 7 + j + 2 - b ≤ sumRep (P : Set ℕ) s)
          (hs : M + s ≤ L) :
          ∃ n ≤ M, ¬ ∃ x y : ℕ, (∀ p ∈ P, x + p ∈ S) ∧
            (∀ p ∈ P, y + p ∈ S) ∧ x + y = n := by
        exact missing_overlap S P (7 + (j + 1)) b M s L (by omega) cap obs
          (by simpa only [Nat.add_assoc] using pat) hs
      obtain ⟨n, hn, above⟩ := test S sub cover overlaps
      have bound := cap n hn
      omega
  intro g
  obtain ⟨L, cert⟩ := all (g - 7)
  refine ⟨L, fun S sub cover => ?_⟩
  obtain ⟨n, hn, hg⟩ := cert S sub cover
  exact ⟨n, hn, by omega⟩

end OMA.R_Erdos28_erdos_28_R1_H1_R3
