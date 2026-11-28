import OMAStatements.S_oeis_a119706
import Mathlib

-- Problem: A119706: Total length of longest runs of 1's in all bitstrings of length n.
-- Upstream: formal-conjectures statements/oeis-a119706.lean:0 (declaration OMA.S_oeis_a119706.main)
-- Credit: @npnelson (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

-- Proof. For a bitstring w let R w be the list of lengths of its maximal runs of 1's, as cut out
-- by the 0's (so R w = (w.splitOn false).map length). The map w |-> (R w).map (+1) sends
-- bitstrings of length n injectively to compositions of n + 1, and both sets have 2^n elements,
-- so it is a bijection. The largest part of the image is the longest run plus one, hence
-- A102712(n+1) = a(n) + 2^n.

namespace Runs119706Proof
open OMA.S_oeis_a119706

def R : List Bool → List ℕ
  | [] => [0]
  | false :: w => 0 :: R w
  | true :: w => ((R w).headD 0 + 1) :: (R w).tail

lemma R_ne : ∀ w : List Bool, R w ≠ []
  | [] => by simp [R]
  | false :: w => by simp [R]
  | true :: w => by simp [R]

lemma R_eq (w : List Bool) : (w.splitOn false).map List.length = R w := by
  induction w with
  | nil => simp [R]
  | cons b w ih =>
    have hne : w.splitOn false ≠ [] := List.splitOnP_ne_nil _ _
    cases b with
    | false =>
      have h : (false :: w).splitOn false = [] :: w.splitOn false := by
        simp [List.splitOn, List.splitOnP_cons_eq_if_modifyHead]
      rw [h]
      simp [R, ih]
    | true =>
      have h : (true :: w).splitOn false = (w.splitOn false).modifyHead (List.cons true) := by
        simp [List.splitOn, List.splitOnP_cons_eq_if_modifyHead]
      rw [h]
      cases hS : w.splitOn false with
      | nil => exact absurd hS hne
      | cons r rs =>
        rw [hS] at ih
        simp [R, ← ih]

lemma R_sum : ∀ w : List Bool, (R w).sum + (R w).length = w.length + 1
  | [] => by simp [R]
  | false :: w => by
      have h := R_sum w
      simp [R]
      omega
  | true :: w => by
      have h := R_sum w
      have hne := R_ne w
      cases hR : R w with
      | nil => exact absurd hR hne
      | cons a t =>
        rw [hR] at h
        simp [R, hR] at h ⊢
        omega

lemma R_inj : ∀ w w' : List Bool, R w = R w' → w = w'
  | [], [], _ => rfl
  | [], false :: w', h => by
      simp [R] at h
      exact absurd h (R_ne w')
  | [], true :: w', h => by simp [R] at h
  | false :: w, [], h => by
      simp [R] at h
      exact absurd h (R_ne w)
  | true :: w, [], h => by simp [R] at h
  | false :: w, false :: w', h => by
      simp [R] at h
      rw [R_inj w w' h]
  | false :: w, true :: w', h => by simp [R] at h
  | true :: w, false :: w', h => by simp [R] at h
  | true :: w, true :: w', h => by
      have h1 := R_ne w
      have h2 := R_ne w'
      cases hR : R w with
      | nil => exact absurd hR h1
      | cons a t =>
        cases hR' : R w' with
        | nil => exact absurd hR' h2
        | cons a' t' =>
          simp [R, hR, hR'] at h
          have hRR : R w = R w' := by rw [hR, hR', h.1, h.2]
          rw [R_inj w w' hRR]

lemma foldr_max_succ : ∀ l : List ℕ, l ≠ [] →
    (l.map (· + 1)).foldr max 0 = l.foldr max 0 + 1
  | [], h => absurd rfl h
  | [x], _ => by simp
  | x :: y :: t, _ => by
      have ih := foldr_max_succ (y :: t) (by simp)
      simp only [List.map_cons, List.foldr_cons] at ih ⊢
      rw [ih]
      omega

lemma sum_map_succ : ∀ l : List ℕ, (l.map (· + 1)).sum = l.sum + l.length
  | [] => by simp
  | x :: t => by
      have ih := sum_map_succ t
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      omega

def toComp (n : ℕ) (v : List.Vector Bool n) : Composition (n + 1) where
  blocks := (R v.toList).map (· + 1)
  blocks_pos := by
    intro i hi
    rw [List.mem_map] at hi
    obtain ⟨x, _, rfl⟩ := hi
    omega
  blocks_sum := by
    have h := R_sum v.toList
    have hl : v.toList.length = n := v.2
    rw [sum_map_succ]
    omega

theorem key (n : ℕ) : A102712 (n + 1) = a n + 2 ^ n := by
  have hinj : Function.Injective (toComp n) := by
    intro v v' h
    have hb : (R v.toList).map (· + 1) = (R v'.toList).map (· + 1) :=
      congrArg Composition.blocks h
    have hR : R v.toList = R v'.toList :=
      List.map_injective_iff.mpr (fun x y hxy => by simpa using hxy) hb
    exact Subtype.ext (R_inj _ _ hR)
  have hcard : Fintype.card (List.Vector Bool n) = Fintype.card (Composition (n + 1)) := by
    rw [card_vector, composition_card]
    simp
  have hbij : Function.Bijective (toComp n) :=
    (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, hcard⟩
  have hterm : ∀ v : List.Vector Bool n,
      largestPart (toComp n v) = longestRun v.toList + 1 := by
    intro v
    unfold largestPart longestRun
    show ((R v.toList).map (· + 1)).foldr max 0 =
      ((v.toList.splitOn false).map List.length).foldr max 0 + 1
    rw [R_eq, foldr_max_succ _ (R_ne _)]
  unfold A102712 a
  rw [← hbij.sum_comp]
  simp only [hterm, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, card_vector]
  simp

end Runs119706Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a119706.main := by
  intro n _
  rw [Runs119706Proof.key]
  omega
