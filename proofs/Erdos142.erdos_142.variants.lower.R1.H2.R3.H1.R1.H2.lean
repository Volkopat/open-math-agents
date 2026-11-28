import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R1
import Mathlib

-- Step Erdos142.erdos_142.variants.lower.R1.H2.R3.H1.R1.H2: hypothesis H2 of reduction Erdos142.erdos_142.variants.lower.R1.H2.R3.H1.R1 (@eilamc14)
-- Credit: @MattGaiser. The two bridge lemmas apFree_iff and exists_maximizer are copied from the merged reduction
-- Erdos142.erdos_142.variants.lower.R3 (credit @mucoucah).
-- Idea: Bertrand gives a prime p with 2N < p <= 4N; embed an extremal set S of [1, N] in ZMod p. A k-term progression
-- mod p with nonzero step gives x_i + x_(i+2) = 2 x_(i+1) mod p, hence in the integers since both sides are below p,
-- so the lifts form an integer progression with nonzero step inside S (reverse it if the step is negative).

namespace E142step

noncomputable abbrev r := Set.IsAPOfLengthFree.maxCard

lemma apFree_iff {A : Set ℕ} {k : ℕ} (hk : 1 < k) :
    A.IsAPOfLengthFree k ↔ ¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ A := by
  have hk' : (1 : ℕ∞) < (k : ℕ∞) := by exact_mod_cast hk
  constructor
  · rintro hA ⟨a, d, hd, hterms⟩
    let f (i : ℕ) := a + i * d
    let T := (Finset.range k).image f
    have hf : Function.Injective f := fun i j hij =>
      Nat.eq_of_mul_eq_mul_right hd (Nat.add_left_cancel hij)
    have hT : ((T : Finset ℕ) : Set ℕ) = {a + n • d | (n : ℕ) (_ : n < (k : ℕ∞))} := by
      ext x
      simp [T, f]
    have hcard : T.card = k := by simp [T, Finset.card_image_of_injective _ hf]
    have hsub : (T : Set ℕ) ⊆ A := by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact hterms i (Finset.mem_range.mp hi)
    exact hk'.not_ge (hA _ hsub ⟨a, d, by simp [hcard], hT⟩)
  · intro hno T hsub hT
    obtain ⟨a, d, hcard, hterms⟩ := hT
    have hmem (i : ℕ) (hi : i < k) : a + i * d ∈ T := by
      rw [hterms]
      exact ⟨i, by exact_mod_cast hi, by simp⟩
    have hd : 0 < d := by
      by_contra! h
      have he : d = 0 := Nat.eq_zero_of_le_zero h
      have hs : T = {a} := by
        apply Set.Subset.antisymm
        · rw [hterms, he]
          rintro _ ⟨i, -, rfl⟩
          simp
        · apply Set.singleton_subset_iff.mpr
          simpa using hmem 0 (by omega)
      rw [hs] at hcard
      exact hk'.ne (by simpa using hcard)
    exact (hno ⟨a, d, hd, fun i hi => hsub (hmem i hi)⟩).elim

lemma exists_maximizer {k : ℕ} (hk : 1 < k) (N : ℕ) :
    ∃ S : Finset ℕ, S ⊆ Finset.Icc 1 N ∧ (S : Set ℕ).IsAPOfLengthFree k ∧
      r k N = S.card := by
  let C : Set ℕ := {m | ∃ S : Finset ℕ, ∃ _ : S ⊆ Finset.Icc 1 N,
    ∃ _ : (S : Set ℕ).IsAPOfLengthFree k, S.card = m}
  have hz : 0 ∈ C := by
    refine ⟨∅, Finset.empty_subset _, (apFree_iff hk).mpr ?_, rfl⟩
    rintro ⟨a, d, -, h⟩
    simpa using h 0 (by omega)
  have hb : BddAbove C := by
    refine ⟨N, ?_⟩
    rintro _ ⟨S, hS, -, rfl⟩
    simpa using Finset.card_le_card hS
  obtain ⟨S, hS, hf, he⟩ := Nat.sSup_mem ⟨0, hz⟩ hb
  exact ⟨S, hS, hf, he.symm⟩

end E142step

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R1.H2 := by
  intro k N hk hN
  classical
  obtain ⟨p, hp, hlo, hhi⟩ := Nat.exists_prime_lt_and_le_two_mul (2 * N) (by omega)
  obtain ⟨S, hS, hf, hc⟩ := E142step.exists_maximizer (k := k) (by omega) N
  have hfree := (E142step.apFree_iff (A := (S : Set ℕ)) (k := k) (by omega)).mp hf
  refine ⟨p, hp, S.image (fun x : ℕ => (x : ZMod p)), hlo, by omega, ?_, ?_⟩
  · rw [Finset.card_image_of_injOn]
    · exact hc
    · intro x hx y hy hxy
      have hx' := (Finset.mem_Icc.mp (hS hx)).2
      have hy' := (Finset.mem_Icc.mp (hS hy)).2
      have h := (ZMod.natCast_eq_natCast_iff' x y p).mp hxy
      rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h
  · intro a d h
    by_contra hd
    have hex : ∀ i : ℕ, ∃ x : ℕ, i < k → (x ∈ S ∧ (x : ZMod p) = a + (i : ZMod p) * d) := by
      intro i
      by_cases hi : i < k
      · obtain ⟨x, hx, e⟩ := Finset.mem_image.mp (h ⟨i, hi⟩)
        exact ⟨x, fun _ => ⟨hx, e⟩⟩
      · exact ⟨0, fun h' => absurd h' hi⟩
    choose y hy using hex
    have hb : ∀ i, i < k → 1 ≤ y i ∧ y i ≤ N := fun i hi =>
      Finset.mem_Icc.mp (hS (hy i hi).1)
    have step : ∀ i, i + 2 < k → y i + y (i + 2) = 2 * y (i + 1) := by
      intro i hi
      have e : ((y i + y (i + 2) : ℕ) : ZMod p) = ((2 * y (i + 1) : ℕ) : ZMod p) := by
        push_cast
        rw [(hy i (by omega)).2, (hy (i + 2) (by omega)).2, (hy (i + 1) (by omega)).2]
        push_cast
        ring
      have h0 := hb i (by omega)
      have h1 := hb (i + 1) (by omega)
      have h2 := hb (i + 2) (by omega)
      have h3 := (ZMod.natCast_eq_natCast_iff' _ _ p).mp e
      rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h3
    have lin : ∀ i, (i < k → (y i : ℤ) = y 0 + (i : ℤ) * ((y 1 : ℤ) - y 0)) ∧
        (i + 1 < k → (y (i + 1) : ℤ) = y 0 + ((i : ℤ) + 1) * ((y 1 : ℤ) - y 0)) := by
      intro i
      induction i with
      | zero => exact ⟨fun _ => by simp, fun _ => by simp⟩
      | succ j ih =>
        refine ⟨fun hj => ?_, fun hj => ?_⟩
        · have := ih.2 hj
          push_cast
          exact this
        · have h1 := ih.1 (by omega)
          have h2 := ih.2 (by omega)
          have h3 : (y j : ℤ) + y (j + 1 + 1) = 2 * y (j + 1) := by exact_mod_cast step j hj
          push_cast
          linear_combination h3 + 2 * h2 - h1
    have hne : y 1 ≠ y 0 := by
      intro e
      apply hd
      have e1 := (hy 1 (by omega)).2
      have e0 := (hy 0 (by omega)).2
      rw [e, e0] at e1
      push_cast at e1
      linear_combination -e1
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · apply hfree
      refine ⟨y (k - 1), y 0 - y 1, by omega, fun i hi => ?_⟩
      obtain ⟨m, hm⟩ : ∃ m, k - 1 = m + i := ⟨k - 1 - i, by omega⟩
      rw [hm]
      have h1 := (lin (m + i)).1 (by omega)
      have h2 := (lin m).1 (by omega)
      have e : y (m + i) + i * (y 0 - y 1) = y m := by
        have : ((y (m + i) + i * (y 0 - y 1) : ℕ) : ℤ) = y m := by
          push_cast [Nat.cast_sub hlt.le] at h1 ⊢
          linear_combination h1 - h2
        exact_mod_cast this
      rw [e]
      exact Finset.mem_coe.mpr (hy m (by omega)).1
    · apply hfree
      refine ⟨y 0, y 1 - y 0, by omega, fun i hi => ?_⟩
      have h1 := (lin i).1 hi
      have e : y 0 + i * (y 1 - y 0) = y i := by
        have : ((y 0 + i * (y 1 - y 0) : ℕ) : ℤ) = y i := by
          push_cast [Nat.cast_sub hlt.le]
          linear_combination -h1
        exact_mod_cast this
      rw [e]
      exact Finset.mem_coe.mpr (hy i hi).1
