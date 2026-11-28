import OMAStatements.S_oeis_a400792

-- Proof credit: @pmaster (Codex); independently audited and assembled by @CubeJerry.
-- uses note #107724
-- @pmaster's DONE note dated 2026-11-28 08:15 UTC.
-- Original proof: https://github.com/pmaster/open-math-agents/blob/455e2f5ba55123c2d22d07fa635a680a5c019ae9/proofs/oeis-a400792.lean

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Tactic.ByContra

/-!
# Every positive integer occurs in A400792

Conjecture by Paolo Xausa and Michael De Vlieger. Proof by @pmaster with Codex.

For an unused integer k, count the smaller coprime terms and subtract the
number of larger terms sharing a factor with k. The difference starts at one.
It cannot drop from one to zero: the newly chosen value would be larger than
k while k itself was eligible. If k never occurs, only finitely many larger
terms can therefore share a factor with it.

Every new record after 2 is even. An odd record would have at least two
smaller coprime predecessors, 1 and 2, and no larger predecessor. Distinct
terms force records of unbounded size. Consequently every positive even k
occurs, since infinitely many larger even records share a factor with k.
For any k > 1 the positive even multiples of k now give the same contradiction.
-/

open OMA.S_oeis_a400792

namespace A400792Proof

def observed : Set ℕ := {k | ∃ t, k ∈ seen t}

lemma seen_mono : Monotone seen := by
  apply monotone_nat_of_le_succ
  intro t
  exact Finset.subset_insert _ _

lemma one_mem (t : ℕ) : 1 ∈ seen t :=
  seen_mono (Nat.zero_le t) (by simp [seen])

lemma has_candidate (s : Finset ℕ) (h1 : 1 ∈ s) :
    ∃ k, eligible s k := by
  let m := s.sup id + 2
  let k := m.factorial
  have lt_k (x : ℕ) (hx : x ∈ s) : x < k := by
    have h : x ≤ s.sup id := Finset.le_sup (f := id) hx
    have hm : m ≤ k := Nat.self_le_factorial m
    dsimp [m] at hm
    omega
  have hgood : (s.filter fun x => x < k ∧ Nat.Coprime x k) = {1} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hx, _, hc⟩
      by_cases hz : x = 0
      · subst x
        have hk := lt_k 1 h1
        simp at hc
        omega
      · have hxm : x ≤ m := by
          have : x ≤ s.sup id := Finset.le_sup (f := id) hx
          dsimp [m]
          omega
        have hd : x ∣ k := Nat.dvd_factorial (Nat.pos_of_ne_zero hz) hxm
        simpa [Nat.coprime_iff_gcd_eq_one, Nat.gcd_eq_left hd] using hc
    · rintro rfl
      exact ⟨h1, lt_k 1 h1, Nat.coprime_one_left _⟩
  have hbad : (s.filter fun x => k < x ∧ ¬ Nat.Coprime x k) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro x hx h
    exact (lt_k x hx).asymm h.1
  refine ⟨k, Nat.factorial_pos _, fun h => (lt_k k h).false, ?_⟩
  simp [good, bad, hgood, hbad]

lemma pick_ok (t : ℕ) : eligible (seen t) (pick (seen t)) :=
  Nat.sInf_mem (s := {k | eligible (seen t) k}) (has_candidate _ (one_mem t))

lemma pick_min (t k : ℕ) (h : eligible (seen t) k) : pick (seen t) ≤ k :=
  Nat.sInf_le (s := {j | eligible (seen t) j}) h

lemma seen_card (t : ℕ) : (seen t).card = t + 1 := by
  induction t with
  | zero => simp [seen]
  | succ t ih => simp [seen, Finset.card_insert_of_notMem (pick_ok t).2.1, ih]

lemma pick_first : pick (seen 0) = 2 := by
  have hu := pick_ok 0
  have hlo := hu.1
  have hne : pick (seen 0) ≠ 1 := by simpa [seen] using hu.2.1
  have hhi := pick_min 0 2 (by unfold eligible good bad; decide)
  omega

lemma term_mem (t : ℕ) : a t ∈ seen t := by
  cases t with
  | zero => simp [a, seen]
  | succ t => simp [a, seen]

lemma observed_range : observed = Set.range a := by
  ext x
  constructor
  · rintro ⟨t, hx⟩
    induction t with
    | zero =>
      have : x = 1 := by simpa [seen] using hx
      exact ⟨0, this.symm⟩
    | succ t ih =>
      rcases Finset.mem_insert.mp hx with h | h
      · exact ⟨t+1, h.symm⟩
      · exact ih h
  · rintro ⟨t, rfl⟩
    exact ⟨t, term_mem t⟩

lemma term_injective : Function.Injective a := by
  have hlt : ∀ i j : ℕ, i < j → a i ≠ a j := by
    intro i j hij
    obtain ⟨t,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    intro heq
    apply (pick_ok t).2.1
    change a i = pick (seen t) at heq
    exact heq ▸ (seen_mono (by omega : i ≤ t) (term_mem i))
  intro i j hij
  rcases lt_trichotomy i j with h | h | h
  · exact False.elim (hlt i j h hij)
  · exact h
  · exact False.elim (hlt j i h hij.symm)

lemma missing_score_pos {k : ℕ} (hk : 0 < k) (hm : k ∉ observed) (t : ℕ) :
    bad (seen t) k < good (seen t) k := by
  have hmiss (n : ℕ) : k ∉ seen n := fun h => hm ⟨n, h⟩
  induction t with
  | zero =>
    have hne : k ≠ 1 := by
      intro h
      subst k
      exact hmiss 0 (by simp [seen])
    have hlt : 1 < k := by omega
    simp [seen, good, bad, Finset.filter_singleton, hlt, Nat.not_lt_of_ge hlt.le]
  | succ t ih =>
    let z := pick (seen t)
    have hg : good (seen t) k ≤ good (seen (t + 1)) k :=
      Finset.card_le_card (Finset.filter_subset_filter _ (seen_mono (Nat.le_succ t)))
    by_cases hbad : k < z ∧ ¬ Nat.Coprime z k
    · have hgap : good (seen t) k ≠ bad (seen t) k + 1 := by
        intro he
        exact (Nat.not_le_of_lt hbad.1) (pick_min t k ⟨hk, hmiss t, he⟩)
      have hfresh : z ∉ (seen t).filter (fun x => k < x ∧ ¬ Nat.Coprime x k) :=
        fun h => (pick_ok t).2.1 (Finset.mem_filter.mp h).1
      have hb : bad (seen (t + 1)) k = bad (seen t) k + 1 := by
        change ((insert z (seen t)).filter _).card = _
        rw [Finset.filter_insert, if_pos hbad, Finset.card_insert_of_notMem hfresh]
        rfl
      omega
    · have hb : bad (seen (t + 1)) k = bad (seen t) k := by
        change ((insert z (seen t)).filter _).card = _
        rw [Finset.filter_insert, if_neg hbad]
        rfl
      omega

lemma finite_bad_of_missing {k : ℕ} (hk : 0 < k) (hm : k ∉ observed) :
    {x : ℕ | x ∈ observed ∧ k < x ∧ ¬ Nat.Coprime x k}.Finite := by
  let B (t : ℕ) := (seen t).filter (fun x => k < x ∧ ¬ Nat.Coprime x k)
  have hB : Monotone B := fun i j hij => Finset.filter_subset_filter _ (seen_mono hij)
  have bound (t : ℕ) : (B t).card ≤ k := by
    have hs : (seen t).filter (fun x => x < k ∧ Nat.Coprime x k) ⊆ Finset.range k :=
      fun x hx => Finset.mem_range.mpr (Finset.mem_filter.mp hx).2.1
    have hgood : good (seen t) k ≤ k := by
      simpa only [good, Finset.card_range] using Finset.card_le_card hs
    exact (missing_score_pos hk hm t).le.trans hgood
  let counts := Set.range (fun t => (B t).card)
  have hfin : counts.Finite := (Set.finite_Iic k).subset (by
    rintro _ ⟨t, rfl⟩
    exact bound t)
  obtain ⟨_, ⟨T, rfl⟩, hmax⟩ :=
    Set.exists_max_image counts id hfin ⟨_, ⟨0, rfl⟩⟩
  refine (B T).finite_toSet.subset ?_
  rintro x ⟨⟨t, hx⟩, hbad⟩
  have heq : B T = B (max T t) := Finset.eq_of_subset_of_card_le
    (hB (le_max_left _ _)) (hmax _ ⟨max T t, rfl⟩)
  change x ∈ B T
  rw [heq]
  exact hB (le_max_right T t) (Finset.mem_filter.mpr ⟨hx, hbad⟩)

lemma even_unbounded (B : ℕ) : ∃ x ∈ observed, B < x ∧ 2 ∣ x := by
  classical
  by_contra! h
  let L := max B 2
  have hB : B ≤ L := le_max_left _ _
  have h2 : 2 ≤ L := le_max_right _ _
  have bound (t : ℕ) : ∀ x ∈ seen t, x ≤ L := by
    induction t with
    | zero =>
      intro x hx
      have := Finset.mem_singleton.mp (show x ∈ ({1} : Finset ℕ) from hx)
      omega
    | succ t ih =>
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · by_contra! hbig
        let k := pick (seen t)
        have hk : L < k := hbig
        have hseen : k ∈ observed := ⟨t + 1, Finset.mem_insert_self _ _⟩
        have hodd : Odd k := Nat.not_even_iff_odd.mp fun he => h k hseen (lt_of_le_of_lt hB hk) he.two_dvd
        have ht : 1 ≤ t := by
          by_contra! ht
          have ht0 : t = 0 := by omega
          have hk2 : k = 2 := by simpa only [k, ht0] using pick_first
          omega
        have htwo : 2 ∈ seen t := by
          apply seen_mono ht
          change 2 ∈ insert (pick (seen 0)) (seen 0)
          rw [pick_first]
          exact Finset.mem_insert_self _ _
        have hone : 1 < k := by omega
        have htwo_lt : 2 < k := by omega
        have lower : 2 ≤ good (seen t) k := by
          have hs : ({1, 2} : Finset ℕ) ⊆ (seen t).filter (fun x => x < k ∧ Nat.Coprime x k) := by
            intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl
            · exact Finset.mem_filter.mpr ⟨one_mem t, hone, Nat.coprime_one_left _⟩
            · exact Finset.mem_filter.mpr ⟨htwo, htwo_lt, hodd.coprime_two_left⟩
          simpa [good] using Finset.card_le_card hs
        have upper : bad (seen t) k = 0 := by
          unfold bad
          apply Finset.card_eq_zero.mpr
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro x hx
          obtain ⟨hxt, hxk, _⟩ := Finset.mem_filter.mp hx
          have := ih x hxt
          omega
        have hscore : good (seen t) k = bad (seen t) k + 1 := (pick_ok t).2.2
        omega
      · exact ih x hx
  have hsub : seen (L + 1) ⊆ Finset.range (L + 1) := by
    intro x hx
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (bound _ _ hx))
  have hc := Finset.card_le_card hsub
  rw [seen_card, Finset.card_range] at hc
  omega

lemma not_coprime_of_common {d x k : ℕ} (hd : 1 < d) (hx : d ∣ x) (hk : d ∣ k) :
    ¬ Nat.Coprime x k := by
  intro hc
  have h := Nat.dvd_gcd hx hk
  rw [hc.gcd_eq_one] at h
  have := Nat.le_of_dvd Nat.zero_lt_one h
  omega

lemma even_observed {k : ℕ} (hk : 0 < k) (he : 2 ∣ k) : k ∈ observed := by
  by_contra hm
  obtain ⟨B, hB⟩ := (finite_bad_of_missing hk hm).bddAbove
  obtain ⟨x, hx, hlarge, hx2⟩ := even_unbounded (max k B)
  have hkx : k < x := lt_of_le_of_lt (le_max_left _ _) hlarge
  have hb : x ≤ B := hB (show x ∈ {x : ℕ | x ∈ observed ∧ k < x ∧ ¬ Nat.Coprime x k} from
    ⟨hx, hkx, not_coprime_of_common (by decide : 1 < 2) hx2 he⟩)
  omega

lemma positive_observed {k : ℕ} (hk : 0 < k) : k ∈ observed := by
  by_cases h : k = 1
  · exact h ▸ (show (1 : ℕ) ∈ observed from ⟨0, one_mem 0⟩)
  by_contra hm
  obtain ⟨B, hB⟩ := (finite_bad_of_missing hk hm).bddAbove
  let x := 2 * k * (B + k + 1)
  have hl : B + k + 1 ≤ x := by
    have hl := Nat.mul_le_mul_right (B+k+1) (show 1 ≤ 2*k by omega)
    simpa [x] using hl
  have hx₂ : 2 ∣ x := by dsimp [x]; exact dvd_mul_of_dvd_left (dvd_mul_right 2 k) _
  have hxk : k ∣ x := by dsimp [x]; exact dvd_mul_of_dvd_left (dvd_mul_left k 2) _
  have hx := even_observed (show 0 < x by omega) hx₂
  have hb : x ≤ B := hB (show x ∈ {x : ℕ | x ∈ observed ∧ k < x ∧ ¬ Nat.Coprime x k} from
    ⟨hx, by omega, not_coprime_of_common (by omega : 1 < k) hxk (dvd_refl k)⟩)
  omega

end A400792Proof

open A400792Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a400792.main := by
  refine ⟨term_injective, Set.Subset.antisymm ?_ ?_⟩
  · rintro x ⟨t, rfl⟩
    cases t with
    | zero => decide
    | succ t => exact (pick_ok t).1
  · intro k hk
    rw [← observed_range]
    exact positive_observed hk
