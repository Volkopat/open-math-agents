import OMAStatements.S_oeis_a006093
import Mathlib

/-!
The unshifted reciprocal prime powers distinguish finite prime sets.
This leaves Sun's shift-minus-one case and the positive shifts.
Source: https://oeis.org/A006093
-/

open scoped BigOperators
open OMA.S_oeis_a006093

namespace OMA.R_oeis_a006093_R1

private lemma oeis_a006093_subset_of_sum_eq {m : ℕ} (hm : 0 < m)
    {A B : Finset ℕ} (hA : ∀ q ∈ A, q.Prime) (hB : ∀ q ∈ B, q.Prime)
    (hsum : (∑ q ∈ A, (1 : ℚ) / (q : ℚ)^m) = ∑ q ∈ B, (1 : ℚ) / (q : ℚ)^m) :
    A ⊆ B := by
  classical
  intro p hpA
  by_contra hpB
  let U := A ∪ B
  have hpU : p ∈ U := Finset.mem_union_left _ hpA
  have hU (q : ℕ) (hq : q ∈ U) : q.Prime := by
    rcases Finset.mem_union.mp hq with hq | hq
    · exact hA q hq
    · exact hB q hq
  have hclear (S : Finset ℕ) (hSU : S ⊆ U) :
      (∏ q ∈ U, (q : ℚ)^m) * (∑ q ∈ S, (1 : ℚ) / (q : ℚ)^m) =
        ((∑ q ∈ S, ∏ a ∈ U.erase q, a^m : ℕ) : ℚ) := by
    rw [Finset.mul_sum]
    push_cast
    apply Finset.sum_congr rfl
    intro q hq
    have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast (hU q (hSU hq)).ne_zero
    rw [← Finset.prod_erase_mul U (fun a => (a : ℚ)^m) (hSU hq), mul_assoc,
      mul_one_div_cancel (pow_ne_zero _ hq0), mul_one]
  have hn : (∑ q ∈ A, ∏ a ∈ U.erase q, a^m) = ∑ q ∈ B, ∏ a ∈ U.erase q, a^m := by
    have hleft := hclear A (fun a ha => Finset.mem_union_left B ha)
    have hright := hclear B (fun a ha => Finset.mem_union_right A ha)
    rw [hsum, hright] at hleft
    exact_mod_cast hleft.symm
  have hpPrime : Fact p.Prime := ⟨hA p hpA⟩
  have hz := congrArg (fun n : ℕ => (n : ZMod p)) hn
  push_cast at hz
  have hzero (q : ℕ) (hqp : q ≠ p) : (∏ a ∈ U.erase q, (a : ZMod p)^m) = 0 := by
    apply Finset.prod_eq_zero (i := p) (Finset.mem_erase.mpr ⟨hqp.symm, hpU⟩)
    simp [hm.ne']
  have hleft : (∑ q ∈ A, ∏ a ∈ U.erase q, (a : ZMod p)^m) =
      ∏ a ∈ U.erase p, (a : ZMod p)^m := by
    rw [Finset.sum_eq_single p]
    · intro q _ hqp
      exact hzero q hqp
    · exact fun h => (h hpA).elim
  have hright : (∑ q ∈ B, ∏ a ∈ U.erase q, (a : ZMod p)^m) = 0 := by
    refine Finset.sum_eq_zero fun q hq => hzero q ?_
    rintro rfl
    exact hpB hq
  rw [hleft, hright] at hz
  refine (Finset.prod_ne_zero_iff.mpr ?_) hz
  intro a ha
  apply pow_ne_zero _
  intro hcast
  have hdiv := (ZMod.natCast_eq_zero_iff a p).mp hcast
  have haPrime := hU a (Finset.mem_of_mem_erase ha)
  have hpa := (Nat.dvd_prime_two_le haPrime (hA p hpA).two_le).mp hdiv
  exact (Finset.mem_erase.mp ha).1 hpa.symm

/-- Positive reciprocal powers of distinct primes distinguish all finite sets. -/
theorem oeis_a006093_unshifted_prime_sets {m : ℕ} (hm : 0 < m)
    {A B : Finset ℕ} (hA : ∀ q ∈ A, q.Prime) (hB : ∀ q ∈ B, q.Prime)
    (hsum : (∑ q ∈ A, (1 : ℚ) / (q : ℚ)^m) = ∑ q ∈ B, (1 : ℚ) / (q : ℚ)^m) : A = B := by
  apply Finset.Subset.antisymm
  · exact oeis_a006093_subset_of_sum_eq hm hA hB hsum
  · exact oeis_a006093_subset_of_sum_eq hm hB hA hsum.symm

private theorem intervalSum_zero_injective {m i j s t : ℕ} (hm : 0 < m)
    (hi : 0 < i) (hij : i ≤ j) (hs : 0 < s) (hst : s ≤ t)
    (hsum : intervalSum 0 m i j = intervalSum 0 m s t) : (i, j) = (s, t) := by
  let p (k : ℕ) := Nat.nth Nat.Prime (k - 1)
  have hprime (k : ℕ) : (p k).Prime :=
    Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime _
  have hinj : Set.InjOn p (Set.Ioi 0) := by
    intro a ha b hb hab
    have hsub := Nat.nth_injective Nat.infinite_setOfPred_prime hab
    have ha' : 0 < a := ha
    have hb' : 0 < b := hb
    omega
  have hIinj {a b : ℕ} (ha : 0 < a) : Set.InjOn p ↑(Finset.Icc a b) :=
    hinj.mono fun _ hk => ha.trans_le (Finset.mem_Icc.mp hk).1
  have himagePrime (A : Finset ℕ) (q : ℕ) (hq : q ∈ A.image p) : q.Prime := by
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hq
    exact hprime k
  have himageSum {a b : ℕ} (ha : 0 < a) :
      (∑ q ∈ (Finset.Icc a b).image p, (1 : ℚ) / (q : ℚ) ^ m) = intervalSum 0 m a b := by
    rw [Finset.sum_image (hIinj ha)]
    simp only [intervalSum, Int.cast_zero, add_zero, p]
  have heq := oeis_a006093_unshifted_prime_sets hm (himagePrime (Finset.Icc i j))
    (himagePrime (Finset.Icc s t)) ((himageSum hi).trans (hsum.trans (himageSum hs).symm))
  have hinterval : Finset.Icc i j = Finset.Icc s t :=
    (Finset.image_eq_image_iff_of_injOn (s := Finset.Icc 1 (max j t)) (hIinj Nat.one_pos)
      (Finset.Icc_subset_Icc hi (le_max_left j t))
      (Finset.Icc_subset_Icc hs (le_max_right j t))).mp heq
  have hi' := Finset.left_mem_Icc.mpr hij
  have hj' := Finset.right_mem_Icc.mpr hij
  have hs' := Finset.left_mem_Icc.mpr hst
  have ht' := Finset.right_mem_Icc.mpr hst
  rw [hinterval] at hi' hj'
  rw [← hinterval] at hs' ht'
  exact Prod.ext (le_antisymm (Finset.mem_Icc.mp hs').1 (Finset.mem_Icc.mp hi').1)
    (le_antisymm (Finset.mem_Icc.mp hj').2 (Finset.mem_Icc.mp ht').2)


def H1 : Prop := ∀ m i j s t : ℕ, 0 < m →
    0 < i → i ≤ j → 0 < s → s ≤ t →
    intervalSum (-1) m i j = intervalSum (-1) m s t → (i, j) = (s, t)

def H2 : Prop := ∀ (d : ℤ) (m i j s t : ℕ), 0 < d → 0 < m →
    0 < i → i ≤ j → 0 < s → s ≤ t →
    intervalSum d m i j = intervalSum d m s t →
      (i, j) = (s, t) ∨ (d = 1 ∧ m = 1 ∧ ExceptionalIntervals (i, j) (s, t))

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a006093.main := by
  intro hnegative hpositive d m i j s t hd hm hi hij hs hst heq
  rcases lt_trichotomy d 0 with hneg | hzero | hpos
  · have h : d = -1 := by omega
    subst d
    exact Or.inl (hnegative m i j s t hm hi hij hs hst heq)
  · subst d
    exact Or.inl (intervalSum_zero_injective hm hi hij hs hst heq)
  · exact hpositive d m i j s t hpos hm hi hij hs hst heq

end OMA.R_oeis_a006093_R1
