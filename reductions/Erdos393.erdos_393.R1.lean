import FormalConjectures.ErdosProblems.«393»
import Mathlib

/-! Erdős and Graham ask whether f(n) tends to infinity. If f n = m, translating the factors of a
minimal factorisation of n! gives n! = (a + i_1) ... (a + i_t) with t at least 2 and every shift
in {0, ..., m}; this is H3. So it suffices that each of the finitely many equations
(a + i_1) ... (a + i_t) = n! with fixed distinct shifts has only finitely many solutions n. H1 is
the case of two factors, a (a + m) = n!, i.e. the Brocard type equation (2a + m)^2 = 4 n! + m^2;
Erdős and Graham note that even a (a + 1) = n! is open. H2 is the case of three or more factors.
Luca (2002) proved both under the abc conjecture; Berend and Osgood (1992) proved density zero. -/

namespace OMA.R_Erdos393_erdos_393_R1

open Finset Filter Erdos393
open scoped Nat Topology

private lemma two_factors
    (h1 : ∀ m : ℕ, 1 ≤ m → {n : ℕ | ∃ a : ℕ, a * (a + m) = n !}.Finite) (T : Finset ℕ)
    (hT : T.card = 2) : {n : ℕ | ∃ a : ℕ, ∏ i ∈ T, (a + i) = n !}.Finite := by
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hT
  rcases lt_or_gt_of_ne hxy with hlt | hlt
  · refine (h1 (y - x) (by omega)).subset ?_
    rintro n ⟨a, ha⟩
    refine ⟨a + x, ?_⟩
    rw [Finset.prod_pair hxy] at ha
    rw [← ha, show a + x + (y - x) = a + y by omega]
  · refine (h1 (x - y) (by omega)).subset ?_
    rintro n ⟨a, ha⟩
    refine ⟨a + y, ?_⟩
    rw [Finset.prod_pair hxy] at ha
    rw [← ha, show a + y + (x - y) = a + x by omega, mul_comm]

/-- Two factors: a (a + m) = n! has finitely many solutions n. -/
def H1 : Prop := ∀ m : ℕ, 1 ≤ m → {n : ℕ | ∃ a : ℕ, a * (a + m) = n !}.Finite

/-- Three or more factors: for fixed distinct shifts T, the product of a + i over i in T equals
n! for only finitely many n. -/
def H2 : Prop := ∀ T : Finset ℕ, 3 ≤ T.card →
  {n : ℕ | ∃ a : ℕ, ∏ i ∈ T, (a + i) = n !}.Finite

/-- A minimal factorisation of n!, translated, is a product of shifts of a by at least two
distinct elements of {0, ..., f n}. -/
def H3 : Prop := ∀ n : ℕ, 2 ≤ n →
  ∃ T ⊆ Finset.range (f n + 1), 2 ≤ T.card ∧ ∃ a : ℕ, ∏ i ∈ T, (a + i) = n !

theorem main : H1 → H2 → H3 → type_of% @Erdos393.erdos_393 := by
  intro h1 h2 h3
  classical
  have fib : ∀ m : ℕ, {n : ℕ | f n = m}.Finite := by
    intro m
    let U := (Finset.range (m + 1)).powerset.filter (fun T => 2 ≤ T.card)
    have hU : (⋃ T ∈ U, {n : ℕ | ∃ a : ℕ, ∏ i ∈ T, (a + i) = n !}).Finite := by
      refine Set.Finite.biUnion U.finite_toSet fun T hT => ?_
      have hc := (Finset.mem_filter.mp hT).2
      rcases Nat.lt_or_ge T.card 3 with hlt | hge
      · exact two_factors h1 T (by omega)
      · exact h2 T hge
    refine ((Set.toFinite ({0, 1} : Set ℕ)).union hU).subset ?_
    intro n hn
    change f n = m at hn
    by_cases hn2 : n < 2
    · left
      interval_cases n <;> simp
    · right
      obtain ⟨T, hTs, hT2, a, ha⟩ := h3 n (by omega)
      rw [hn] at hTs
      simp only [Set.mem_iUnion]
      exact ⟨T, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hTs, hT2⟩, a, ha⟩
  rw [tendsto_atTop]
  intro b
  have hfin : {n : ℕ | f n < b}.Finite := by
    refine (Set.Finite.biUnion (Finset.range b).finite_toSet fun m _ => fib m).subset ?_
    intro n hn
    simp only [Set.mem_iUnion]
    exact ⟨f n, Finset.mem_coe.mpr (Finset.mem_range.mpr hn), rfl⟩
  rw [← Nat.cofinite_eq_atTop]
  filter_upwards [hfin.eventually_cofinite_notMem] with n hn
  exact not_lt.mp hn

end OMA.R_Erdos393_erdos_393_R1
