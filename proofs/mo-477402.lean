import OMAStatements.S_mo_477402

-- Problem: Poisson binomial conjecture
-- Credit: @sobrien032

/-
Aryeh Kontorovich posed the conjecture. David Ganz formalized the board statement.
Adapted from Christopher D. Long, The exact Poisson-binomial comparison in every dimension.
https://github.com/long-mathematics/poisson-binomial-comparison
Revision b34cde620016c85e5c7d5461630c0fde3f098d4b.

MIT License

Copyright (c) 2026 long-mathematics

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the 'Software'), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED 'AS IS', WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

-- Basic
namespace PoissonBinomialComparison

open scoped BigOperators
open Finset

noncomputable section

variable {ι : Type*} [DecidableEq ι]

def bernoulliWeight (p : ι → ℝ) (s A : Finset ι) : ℝ :=
  (∏ i ∈ A, p i) * ∏ i ∈ s \ A, (1 - p i)

def pbMassOn (p : ι → ℝ) (s : Finset ι) (k : ℕ) : ℝ :=
  ∑ A ∈ s.powersetCard k, bernoulliWeight p s A

def pbTailOn (p : ι → ℝ) (s : Finset ι) (k : ℕ) : ℝ :=
  ∑ A ∈ s.powerset, if k ≤ A.card then bernoulliWeight p s A else 0

def pbMass {n : ℕ} (p : Fin n → ℝ) (k : ℕ) : ℝ :=
  pbMassOn p univ k

def pbTail {n : ℕ} (p : Fin n → ℝ) (k : ℕ) : ℝ :=
  pbTailOn p univ k

def meanGap {n : ℕ} (p q : Fin n → ℝ) : ℝ :=
  (∑ i, p i) - ∑ i, q i

def tailDiff {n : ℕ} (p q : Fin n → ℝ) (k : ℕ) : ℝ :=
  pbTail p k - pbTail q k

theorem pbMassOn_eq_sum_powerset (p : ι → ℝ) (s : Finset ι) (k : ℕ) :
    pbMassOn p s k =
      ∑ A ∈ s.powerset, if A.card = k then bernoulliWeight p s A else 0 := by
  simp only [pbMassOn, powersetCard_eq_filter, sum_filter]

theorem bernoulliWeight_nonneg {p : ι → ℝ} {s A : Finset ι}
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) (hA : A ⊆ s) :
    0 ≤ bernoulliWeight p s A := by
  apply mul_nonneg
  · exact prod_nonneg fun i hi ↦ (hp i (hA hi)).1
  · exact prod_nonneg fun i hi ↦ sub_nonneg.mpr (hp i (mem_sdiff.mp hi).1).2

theorem pbMassOn_nonneg {p : ι → ℝ} {s : Finset ι}
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) (k : ℕ) :
    0 ≤ pbMassOn p s k := by
  exact sum_nonneg fun A hA ↦ bernoulliWeight_nonneg hp (mem_powersetCard.mp hA).1

theorem sum_bernoulliWeight (p : ι → ℝ) (s : Finset ι) :
    ∑ A ∈ s.powerset, bernoulliWeight p s A = 1 := by
  simpa [bernoulliWeight] using (prod_add p (fun i ↦ 1 - p i) s).symm

theorem sum_pbMassOn (p : ι → ℝ) (s : Finset ι) :
    ∑ k ∈ range (s.card + 1), pbMassOn p s k = 1 := by
  simp only [pbMassOn]
  rw [← sum_powerset s (bernoulliWeight p s)]
  exact sum_bernoulliWeight p s

theorem pbTailOn_eq_sum_mass (p : ι → ℝ) (s : Finset ι) (k : ℕ) :
    pbTailOn p s k = ∑ j ∈ Icc k s.card, pbMassOn p s j := by
  have hinterval : Icc k s.card = (range (s.card + 1)).filter (k ≤ ·) := by
    ext j
    simp only [mem_Icc, mem_filter, mem_range]
    omega
  rw [pbTailOn, sum_powerset, hinterval, sum_filter]
  apply sum_congr rfl
  intro j hj
  by_cases hkj : k ≤ j
  · rw [if_pos hkj]
    apply sum_congr rfl
    intro A hA
    simp [(mem_powersetCard.mp hA).2, hkj]
  · rw [if_neg hkj]
    apply sum_eq_zero
    intro A hA
    simp [(mem_powersetCard.mp hA).2, hkj]

@[simp] theorem pbMassOn_zero (p : ι → ℝ) (s : Finset ι) :
    pbMassOn p s 0 = ∏ i ∈ s, (1 - p i) := by
  simp [pbMassOn, bernoulliWeight]

theorem pbMassOn_eq_zero_of_card_lt (p : ι → ℝ) {s : Finset ι} {k : ℕ}
    (hk : s.card < k) : pbMassOn p s k = 0 := by
  simp [pbMassOn, powersetCard_eq_empty.mpr hk]

@[simp] theorem pbTailOn_zero (p : ι → ℝ) (s : Finset ι) :
    pbTailOn p s 0 = 1 := by
  simpa [pbTailOn] using sum_bernoulliWeight p s

theorem pbTailOn_eq_zero_of_card_lt (p : ι → ℝ) {s : Finset ι} {k : ℕ}
    (hk : s.card < k) : pbTailOn p s k = 0 := by
  rw [pbTailOn_eq_sum_mass, Icc_eq_empty_of_lt hk, sum_empty]

private theorem bernoulliWeight_insert_failure (p : ι → ℝ) {s A : Finset ι}
    {i : ι} (hi : i ∉ s) (hA : A ⊆ s) :
    bernoulliWeight p (insert i s) A = (1 - p i) * bernoulliWeight p s A := by
  have hiA : i ∉ A := fun h ↦ hi (hA h)
  simp [bernoulliWeight, insert_sdiff_of_notMem s hiA, prod_insert,
    hi, mul_left_comm]

private theorem bernoulliWeight_insert_success (p : ι → ℝ) {s A : Finset ι}
    {i : ι} (hi : i ∉ s) (hA : A ⊆ s) :
    bernoulliWeight p (insert i s) (insert i A) = p i * bernoulliWeight p s A := by
  have hiA : i ∉ A := fun h ↦ hi (hA h)
  simp [bernoulliWeight, insert_sdiff_insert, sdiff_insert_of_notMem hi,
    prod_insert, hiA, mul_assoc]

theorem pbMassOn_insert_succ (p : ι → ℝ) {s : Finset ι} {i : ι}
    (hi : i ∉ s) (k : ℕ) :
    pbMassOn p (insert i s) (k + 1) =
      (1 - p i) * pbMassOn p s (k + 1) + p i * pbMassOn p s k := by
  simp only [pbMassOn_eq_sum_powerset, sum_powerset_insert hi, mul_sum]
  congr 1
  · apply sum_congr rfl
    intro A hA
    rw [bernoulliWeight_insert_failure p hi (mem_powerset.mp hA)]
    simp only [mul_ite, mul_zero]
  · apply sum_congr rfl
    intro A hA
    have hAs := mem_powerset.mp hA
    have hiA : i ∉ A := fun h ↦ hi (hAs h)
    rw [card_insert_of_notMem hiA, bernoulliWeight_insert_success p hi hAs]
    simp only [Nat.add_right_cancel_iff, mul_ite, mul_zero]

theorem pbMassOn_insert_zero (p : ι → ℝ) {s : Finset ι} {i : ι}
    (hi : i ∉ s) :
    pbMassOn p (insert i s) 0 = (1 - p i) * pbMassOn p s 0 := by
  simp [prod_insert, hi]

theorem pbTailOn_insert_succ (p : ι → ℝ) {s : Finset ι} {i : ι}
    (hi : i ∉ s) (k : ℕ) :
    pbTailOn p (insert i s) (k + 1) =
      (1 - p i) * pbTailOn p s (k + 1) + p i * pbTailOn p s k := by
  simp only [pbTailOn, sum_powerset_insert hi, mul_sum]
  congr 1
  · apply sum_congr rfl
    intro A hA
    rw [bernoulliWeight_insert_failure p hi (mem_powerset.mp hA)]
    simp only [mul_ite, mul_zero]
  · apply sum_congr rfl
    intro A hA
    have hAs := mem_powerset.mp hA
    have hiA : i ∉ A := fun h ↦ hi (hAs h)
    rw [card_insert_of_notMem hiA, bernoulliWeight_insert_success p hi hAs]
    simp only [Nat.add_le_add_iff_right, mul_ite, mul_zero]

variable {n : ℕ}

theorem pbMass_eq_sum_subsets (p : Fin n → ℝ) (k : ℕ) :
    pbMass p k = ∑ A ∈ (univ : Finset (Fin n)).powersetCard k,
      (∏ i ∈ A, p i) * ∏ i ∈ univ \ A, (1 - p i) := rfl

theorem pbMass_nonneg {p : Fin n → ℝ} (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (k : ℕ) : 0 ≤ pbMass p k :=
  pbMassOn_nonneg (fun i _ ↦ hp i) k

theorem sum_pbMass (p : Fin n → ℝ) : ∑ k ∈ range (n + 1), pbMass p k = 1 := by
  simpa [pbMass] using sum_pbMassOn p univ

theorem pbTail_eq_sum_mass (p : Fin n → ℝ) (k : ℕ) :
    pbTail p k = ∑ j ∈ Icc k n, pbMass p j := by
  simpa [pbTail, pbMass] using pbTailOn_eq_sum_mass p univ k

@[simp] theorem pbMass_zero (p : Fin n → ℝ) : pbMass p 0 = ∏ i, (1 - p i) :=
  pbMassOn_zero p univ

theorem pbMass_eq_zero_of_lt (p : Fin n → ℝ) {k : ℕ} (hk : n < k) :
    pbMass p k = 0 :=
  pbMassOn_eq_zero_of_card_lt p (by simpa using hk)

@[simp] theorem pbTail_zero (p : Fin n → ℝ) : pbTail p 0 = 1 :=
  pbTailOn_zero p univ

theorem pbTail_eq_zero_of_lt (p : Fin n → ℝ) {k : ℕ} (hk : n < k) :
    pbTail p k = 0 :=
  pbTailOn_eq_zero_of_card_lt p (by simpa using hk)

theorem pbMass_delete_succ (p : Fin n → ℝ) (i : Fin n) (k : ℕ) :
    pbMass p (k + 1) =
      (1 - p i) * pbMassOn p (univ.erase i) (k + 1) +
        p i * pbMassOn p (univ.erase i) k := by
  simpa [pbMass] using pbMassOn_insert_succ p (notMem_erase i univ) k

theorem pbMass_delete_zero (p : Fin n → ℝ) (i : Fin n) :
    pbMass p 0 = (1 - p i) * pbMassOn p (univ.erase i) 0 := by
  simpa [pbMass] using pbMassOn_insert_zero p (notMem_erase i univ)

theorem pbTail_delete_succ (p : Fin n → ℝ) (i : Fin n) (k : ℕ) :
    pbTail p (k + 1) =
      (1 - p i) * pbTailOn p (univ.erase i) (k + 1) +
        p i * pbTailOn p (univ.erase i) k := by
  simpa [pbTail] using pbTailOn_insert_succ p (notMem_erase i univ) k

theorem meanGap_eq_sum (p q : Fin n → ℝ) : meanGap p q = ∑ i, (p i - q i) := by
  exact (sum_sub_distrib p q).symm

theorem tailDiff_eq_sum_mass (p q : Fin n → ℝ) (k : ℕ) :
    tailDiff p q k = ∑ j ∈ Icc k n, (pbMass p j - pbMass q j) := by
  simp only [tailDiff, pbTail_eq_sum_mass, sum_sub_distrib]

end

end PoissonBinomialComparison

-- Tail
namespace PoissonBinomialComparison

open scoped BigOperators
open Finset

noncomputable section

variable {ι : Type*}

def ValidParameters (p : ι → ℝ) : Prop :=
  ∀ i, 0 ≤ p i ∧ p i ≤ 1

def AdmissiblePair (p q : ι → ℝ) : Prop :=
  ValidParameters p ∧ ValidParameters q ∧ q ≤ p

theorem admissiblePair_iff (p q : ι → ℝ) :
    AdmissiblePair p q ↔ ∀ i, 0 ≤ q i ∧ q i ≤ p i ∧ p i ≤ 1 := by
  constructor
  · rintro ⟨hp, hq, hqp⟩ i
    exact ⟨(hq i).1, hqp i, (hp i).2⟩
  · intro h
    exact ⟨fun i ↦ ⟨(h i).1.trans (h i).2.1, (h i).2.2⟩,
      fun i ↦ ⟨(h i).1, (h i).2.1.trans (h i).2.2⟩, fun i ↦ (h i).2.1⟩

theorem sum_pbTailOn [DecidableEq ι] (p : ι → ℝ) (s : Finset ι) :
    ∑ k ∈ range s.card, pbTailOn p s (k + 1) = ∑ i ∈ s, p i := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [card_insert_of_notMem hi, pbTailOn_insert_succ p hi,
      sum_add_distrib, ← mul_sum]
    rw [sum_range_succ (fun k ↦ pbTailOn p s (k + 1)),
      pbTailOn_eq_zero_of_card_lt p (Nat.lt_succ_self s.card), add_zero,
      sum_range_succ' (pbTailOn p s), pbTailOn_zero, ih, sum_insert hi]
    ring

variable {n : ℕ}

theorem sum_pbTail_range (p : Fin n → ℝ) :
    ∑ k ∈ range n, pbTail p (k + 1) = ∑ i, p i := by
  simpa [pbTail] using sum_pbTailOn p univ

theorem sum_pbTail (p : Fin n → ℝ) :
    ∑ k ∈ Icc 1 n, pbTail p k = ∑ i, p i := by
  rw [← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range]
  simpa [Nat.add_comm] using sum_pbTail_range p

theorem sum_tailDiff (p q : Fin n → ℝ) :
    ∑ k ∈ Icc 1 n, tailDiff p q k = meanGap p q := by
  simp only [tailDiff, sum_sub_distrib, sum_pbTail, meanGap]

def tailObjective (p q : Fin n → ℝ) : ℝ :=
  if hn : 0 < n then
    (Icc 1 n).sup' (nonempty_Icc.mpr hn) (tailDiff p q)
  else 0

theorem tailObjective_eq_sup' (p q : Fin n → ℝ) (hn : 0 < n) :
    tailObjective p q = (Icc 1 n).sup' (nonempty_Icc.mpr hn) (tailDiff p q) := by
  simp only [tailObjective, dif_pos hn]

@[simp] theorem tailObjective_zero (p q : Fin 0 → ℝ) : tailObjective p q = 0 := by
  simp [tailObjective]

theorem tailDiff_le_tailObjective (p q : Fin n → ℝ) {k : ℕ}
    (hk : k ∈ Icc 1 n) : tailDiff p q k ≤ tailObjective p q := by
  have hn : 0 < n := (mem_Icc.mp hk).1.trans (mem_Icc.mp hk).2
  rw [tailObjective_eq_sup' p q hn]
  exact le_sup' (tailDiff p q) hk

theorem tailObjective_le_iff (p q : Fin n → ℝ) (hn : 0 < n) (a : ℝ) :
    tailObjective p q ≤ a ↔ ∀ k ∈ Icc 1 n, tailDiff p q k ≤ a := by
  rw [tailObjective_eq_sup' p q hn, sup'_le_iff]

theorem tailObjective_attained (p q : Fin n → ℝ) (hn : 0 < n) :
    ∃ k ∈ Icc 1 n, tailObjective p q = tailDiff p q k := by
  rw [tailObjective_eq_sup' p q hn]
  exact exists_mem_eq_sup' (nonempty_Icc.mpr hn) (tailDiff p q)

end

end PoissonBinomialComparison

-- Coordinate
namespace PoissonBinomialComparison

open scoped BigOperators
open Finset

noncomputable section

variable {ι : Type*} [DecidableEq ι]

theorem bernoulliWeight_congr {p q : ι → ℝ} {s A : Finset ι}
    (h : ∀ i ∈ s, p i = q i) (hA : A ⊆ s) :
    bernoulliWeight p s A = bernoulliWeight q s A := by
  unfold bernoulliWeight
  congr 1
  · exact prod_congr rfl fun i hi ↦ h i (hA hi)
  · exact prod_congr rfl fun i hi ↦ congrArg (1 - ·) (h i (mem_sdiff.mp hi).1)

theorem pbMassOn_congr {p q : ι → ℝ} {s : Finset ι}
    (h : ∀ i ∈ s, p i = q i) (k : ℕ) :
    pbMassOn p s k = pbMassOn q s k := by
  exact sum_congr rfl fun A hA ↦ bernoulliWeight_congr h (mem_powersetCard.mp hA).1

theorem pbTailOn_congr {p q : ι → ℝ} {s : Finset ι}
    (h : ∀ i ∈ s, p i = q i) (k : ℕ) :
    pbTailOn p s k = pbTailOn q s k := by
  unfold pbTailOn
  apply sum_congr rfl
  intro A hA
  rw [bernoulliWeight_congr h (mem_powerset.mp hA)]

theorem pbTailOn_sub_succ (p : ι → ℝ) (s : Finset ι) (k : ℕ) :
    pbTailOn p s k - pbTailOn p s (k + 1) = pbMassOn p s k := by
  rw [pbTailOn, pbTailOn, ← sum_sub_distrib, pbMassOn_eq_sum_powerset]
  apply sum_congr rfl
  intro A _
  by_cases h : A.card = k
  · simp [h]
  · by_cases hk : k ≤ A.card
    · have hk' : k + 1 ≤ A.card := by omega
      simp [h, hk, hk']
    · have hk' : ¬k + 1 ≤ A.card := by omega
      simp [h, hk, hk']

theorem pbMassOn_update_of_notMem (p : ι → ℝ) {s : Finset ι} {i : ι}
    (hi : i ∉ s) (a : ℝ) (k : ℕ) :
    pbMassOn (Function.update p i a) s k = pbMassOn p s k := by
  apply pbMassOn_congr
  intro j hj
  have hji : j ≠ i := by
    intro h
    subst j
    exact hi hj
  exact Function.update_of_ne hji a p

theorem pbTailOn_update_of_notMem (p : ι → ℝ) {s : Finset ι} {i : ι}
    (hi : i ∉ s) (a : ℝ) (k : ℕ) :
    pbTailOn (Function.update p i a) s k = pbTailOn p s k := by
  apply pbTailOn_congr
  intro j hj
  have hji : j ≠ i := by
    intro h
    subst j
    exact hi hj
  exact Function.update_of_ne hji a p

theorem pbTailOn_update_sub (p : ι → ℝ) {s : Finset ι} {i : ι}
    (hi : i ∉ s) (a b : ℝ) (k : ℕ) :
    pbTailOn (Function.update p i b) (insert i s) (k + 1) -
      pbTailOn (Function.update p i a) (insert i s) (k + 1) =
        (b - a) * pbMassOn p s k := by
  rw [pbTailOn_insert_succ _ hi, pbTailOn_insert_succ _ hi]
  simp only [Function.update_self, pbTailOn_update_of_notMem p hi]
  rw [← pbTailOn_sub_succ p s k]
  ring

theorem pbTailOn_update_mono (p : ι → ℝ) {s : Finset ι} {i : ι}
    (hi : i ∉ s) (hp : ∀ j ∈ s, 0 ≤ p j ∧ p j ≤ 1)
    {a b : ℝ} (hab : a ≤ b) (k : ℕ) :
    pbTailOn (Function.update p i a) (insert i s) (k + 1) ≤
      pbTailOn (Function.update p i b) (insert i s) (k + 1) := by
  apply sub_nonneg.mp
  rw [pbTailOn_update_sub p hi]
  exact mul_nonneg (sub_nonneg.mpr hab) (pbMassOn_nonneg hp k)

theorem pbTailOn_mono {p q : ι → ℝ} (s : Finset ι)
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1)
    (hq : ∀ i ∈ s, 0 ≤ q i ∧ q i ≤ 1)
    (hpq : ∀ i ∈ s, p i ≤ q i) (k : ℕ) :
    pbTailOn p s k ≤ pbTailOn q s k := by
  induction s using Finset.induction_on generalizing k with
  | empty => simp [pbTailOn, bernoulliWeight]
  | @insert i s hi ih =>
    have hps : ∀ j ∈ s, 0 ≤ p j ∧ p j ≤ 1 :=
      fun j hj ↦ hp j (mem_insert_of_mem hj)
    have hqs : ∀ j ∈ s, 0 ≤ q j ∧ q j ≤ 1 :=
      fun j hj ↦ hq j (mem_insert_of_mem hj)
    have hpqs : ∀ j ∈ s, p j ≤ q j :=
      fun j hj ↦ hpq j (mem_insert_of_mem hj)
    cases k with
    | zero => simp
    | succ k =>
      rw [pbTailOn_insert_succ _ hi, pbTailOn_insert_succ _ hi]
      calc
        (1 - p i) * pbTailOn p s (k + 1) + p i * pbTailOn p s k ≤
            (1 - p i) * pbTailOn q s (k + 1) + p i * pbTailOn q s k :=
          add_le_add
            (mul_le_mul_of_nonneg_left (ih hps hqs hpqs (k + 1))
              (sub_nonneg.mpr (hp i (mem_insert_self i s)).2))
            (mul_le_mul_of_nonneg_left (ih hps hqs hpqs k)
              (hp i (mem_insert_self i s)).1)
        _ ≤ (1 - q i) * pbTailOn q s (k + 1) + q i * pbTailOn q s k := by
          apply sub_nonneg.mp
          have heq :
              (1 - q i) * pbTailOn q s (k + 1) + q i * pbTailOn q s k -
                ((1 - p i) * pbTailOn q s (k + 1) + p i * pbTailOn q s k) =
                  (q i - p i) * pbMassOn q s k := by
            rw [← pbTailOn_sub_succ q s k]
            ring
          rw [heq]
          exact mul_nonneg (sub_nonneg.mpr (hpq i (mem_insert_self i s)))
            (pbMassOn_nonneg hqs k)

variable {n : ℕ}

theorem pbTail_sub_succ (p : Fin n → ℝ) (k : ℕ) :
    pbTail p k - pbTail p (k + 1) = pbMass p k :=
  pbTailOn_sub_succ p univ k

theorem pbTail_update_sub (p : Fin n → ℝ) (i : Fin n) (a b : ℝ) (k : ℕ) :
    pbTail (Function.update p i b) (k + 1) -
      pbTail (Function.update p i a) (k + 1) =
        (b - a) * pbMassOn p (univ.erase i) k := by
  simpa [pbTail] using pbTailOn_update_sub p (notMem_erase i univ) a b k

theorem pbTail_update_mono (p : Fin n → ℝ) (hp : ValidParameters p)
    (i : Fin n) {a b : ℝ} (hab : a ≤ b) (k : ℕ) :
    pbTail (Function.update p i a) k ≤ pbTail (Function.update p i b) k := by
  cases k with
  | zero => simp
  | succ k =>
    simpa [pbTail] using
      pbTailOn_update_mono p (notMem_erase i univ) (fun j _ ↦ hp j) hab k

theorem pbTail_mono {p q : Fin n → ℝ} (hp : ValidParameters p)
    (hq : ValidParameters q) (hpq : p ≤ q) (k : ℕ) :
    pbTail p k ≤ pbTail q k :=
  pbTailOn_mono univ (fun i _ ↦ hp i) (fun i _ ↦ hq i) (fun i _ ↦ hpq i) k

theorem tailDiff_nonneg {p q : Fin n → ℝ} (h : AdmissiblePair p q) (k : ℕ) :
    0 ≤ tailDiff p q k :=
  sub_nonneg.mpr (pbTail_mono h.2.1 h.1 h.2.2 k)

end

end PoissonBinomialComparison

-- LogConcavity
namespace PoissonBinomialComparison

open scoped BigOperators
open Finset

noncomputable section

def MassCrossInequalities (f : ℤ → ℝ) : Prop :=
  ∀ i j : ℤ, i ≤ j → f (i - 1) * f (j + 1) ≤ f i * f j

def StrictMassLogConcavity (f : ℤ → ℝ) : Prop :=
  ∀ k : ℤ, 0 < f k → f (k - 1) * f (k + 1) < (f k) ^ 2

theorem MassCrossInequalities.mixed {f : ℤ → ℝ} (h : MassCrossInequalities f)
    (i j : ℤ) (hij : i ≤ j) :
    f (i - 2) * f (j + 1) ≤ f i * f (j - 1) := by
  by_cases heq : i = j
  · subst j
    simpa [show i - 1 - 1 = i - 2 by omega, mul_comm] using
      h (i - 1) i (by omega)
  · have h1 := h (i - 1) j (by omega)
    have h2 := h i (j - 1) (by omega)
    simp only [show i - 1 - 1 = i - 2 by omega,
      show j - 1 + 1 = j by omega] at h1 h2
    exact h1.trans h2

theorem MassCrossInequalities.convolve {f : ℤ → ℝ} (h : MassCrossInequalities f)
    {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    MassCrossInequalities (fun k ↦ v * f k + u * f (k - 1)) := by
  intro i j hij
  have h1 := mul_nonneg (sq_nonneg v) (sub_nonneg.mpr (h i j hij))
  have h2 := mul_nonneg (sq_nonneg u)
    (sub_nonneg.mpr (h (i - 1) (j - 1) (by omega)))
  have h3 := mul_nonneg (mul_nonneg hu hv) (sub_nonneg.mpr (h.mixed i j hij))
  simp only [show i - 1 - 1 = i - 2 by omega,
    show j - 1 + 1 = j by omega] at h2
  simp only [show i - 1 - 1 = i - 2 by omega,
    show j + 1 - 1 = j by omega]
  nlinarith

theorem StrictMassLogConcavity.convolve {f : ℤ → ℝ}
    (hf : ∀ k, 0 ≤ f k) (hc : MassCrossInequalities f)
    (hs : StrictMassLogConcavity f) {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    StrictMassLogConcavity (fun k ↦ v * f k + u * f (k - 1)) := by
  intro k hk
  have hc0 := hc k k le_rfl
  have hc1 := hc (k - 1) (k - 1) le_rfl
  have hmix := hc.mixed k k le_rfl
  simp only [show k - 1 - 1 = k - 2 by omega,
    show k - 1 + 1 = k by omega] at hc1
  have hvweak := mul_nonneg (sq_nonneg v) (sub_nonneg.mpr hc0)
  have huweak := mul_nonneg (sq_nonneg u) (sub_nonneg.mpr hc1)
  have hmixed := mul_nonneg (mul_nonneg hu hv) (sub_nonneg.mpr hmix)
  simp only [show k - 1 - 1 = k - 2 by omega,
    show k + 1 - 1 = k by omega]
  by_cases hpos : 0 < v * f k
  · have hvpos := pos_of_mul_pos_left hpos (hf k)
    have hfpos := pos_of_mul_pos_right hpos hv
    have hstrict := mul_pos (sq_pos_of_pos hvpos) (sub_pos.mpr (hs k hfpos))
    nlinarith
  · have hup : 0 < u * f (k - 1) := by linarith
    have hupos := pos_of_mul_pos_left hup (hf (k - 1))
    have hfpos := pos_of_mul_pos_right hup hu
    have hstrict := mul_pos (sq_pos_of_pos hupos) (sub_pos.mpr (hs (k - 1) hfpos))
    simp only [show k - 1 - 1 = k - 2 by omega,
      show k - 1 + 1 = k by omega] at hstrict
    nlinarith

theorem MassCrossInequalities.positive_between {f : ℤ → ℝ}
    (h : MassCrossInequalities f) (hf : ∀ k, 0 ≤ f k)
    {i j k : ℤ} (hij : i ≤ j) (hjk : j ≤ k)
    (hi : 0 < f i) (hk : 0 < f k) : 0 < f j := by
  by_cases hji : j = i
  · simpa [hji] using hi
  by_cases hjk' : j = k
  · simpa [hjk'] using hk
  have hcross : f i * f k ≤ f (i + 1) * f (k - 1) := by
    simpa using h (i + 1) (k - 1) (by omega)
  have hprod := (mul_pos hi hk).trans_le hcross
  have hi' := pos_of_mul_pos_left hprod (hf (k - 1))
  exact MassCrossInequalities.positive_between h hf (i := i + 1) (by omega) hjk hi' hk
termination_by (j - i).toNat
decreasing_by omega

variable {ι : Type*} [DecidableEq ι]

def pbMassIntOn (p : ι → ℝ) (s : Finset ι) (k : ℤ) : ℝ :=
  if 0 ≤ k then pbMassOn p s k.toNat else 0

@[simp] theorem pbMassIntOn_natCast (p : ι → ℝ) (s : Finset ι) (k : ℕ) :
    pbMassIntOn p s k = pbMassOn p s k := by
  simp [pbMassIntOn]

theorem pbMassIntOn_of_neg (p : ι → ℝ) (s : Finset ι) {k : ℤ} (hk : k < 0) :
    pbMassIntOn p s k = 0 := by
  simp [pbMassIntOn, not_le.mpr hk]

theorem pbMassIntOn_nonneg {p : ι → ℝ} {s : Finset ι}
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) (k : ℤ) :
    0 ≤ pbMassIntOn p s k := by
  unfold pbMassIntOn
  split
  · exact pbMassOn_nonneg hp _
  · exact le_rfl

theorem pbMassIntOn_insert (p : ι → ℝ) {s : Finset ι} {i : ι}
    (hi : i ∉ s) (k : ℤ) :
    pbMassIntOn p (insert i s) k =
      (1 - p i) * pbMassIntOn p s k + p i * pbMassIntOn p s (k - 1) := by
  by_cases hk : 0 ≤ k
  · lift k to ℕ using hk
    cases k with
    | zero => simp [pbMassIntOn, pbMassOn_insert_zero p hi]
    | succ k =>
      have hcast : ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) := by omega
      simp only [hcast, pbMassIntOn_natCast]
      exact pbMassOn_insert_succ p hi k
  · have hk' : ¬0 ≤ k - 1 := by omega
    simp only [pbMassIntOn, hk, hk', ite_false, mul_zero, add_zero]

@[simp] theorem pbMassIntOn_empty (p : ι → ℝ) (k : ℤ) :
    pbMassIntOn p ∅ k = if k = 0 then 1 else 0 := by
  by_cases hk : 0 ≤ k
  · lift k to ℕ using hk
    by_cases hk0 : k = 0
    · subst k
      simp [pbMassIntOn]
    · simp [pbMassOn_eq_sum_powerset, bernoulliWeight, hk0, Ne.symm hk0]
  · have hk' : k ≠ 0 := by omega
    simp [pbMassIntOn, hk, hk']

theorem pbMassIntOn_cross {p : ι → ℝ} (s : Finset ι)
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) :
    MassCrossInequalities (pbMassIntOn p s) := by
  induction s using Finset.induction_on with
  | empty =>
    intro i j hij
    by_cases hi : i - 1 = 0
    · have hj : j + 1 ≠ 0 := by omega
      simp only [pbMassIntOn_empty, hi, hj, ite_false, ite_true, mul_zero]
      positivity
    · simp only [pbMassIntOn_empty, hi, ite_false, zero_mul]
      positivity
  | @insert i s hi ih =>
    have hps : ∀ j ∈ s, 0 ≤ p j ∧ p j ≤ 1 :=
      fun j hj ↦ hp j (mem_insert_of_mem hj)
    have hpi := hp i (mem_insert_self i s)
    have heq : pbMassIntOn p (insert i s) =
        (fun k ↦ (1 - p i) * pbMassIntOn p s k + p i * pbMassIntOn p s (k - 1)) :=
      funext (pbMassIntOn_insert p hi)
    rw [heq]
    exact (ih hps).convolve hpi.1 (sub_nonneg.mpr hpi.2)

theorem pbMassIntOn_strictLogConcavity {p : ι → ℝ} (s : Finset ι)
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) :
    StrictMassLogConcavity (pbMassIntOn p s) := by
  induction s using Finset.induction_on with
  | empty =>
    intro k hk
    have hk0 : k = 0 := by
      by_contra h
      simp [h] at hk
    subst k
    norm_num
  | @insert i s hi ih =>
    have hps : ∀ j ∈ s, 0 ≤ p j ∧ p j ≤ 1 :=
      fun j hj ↦ hp j (mem_insert_of_mem hj)
    have hpi := hp i (mem_insert_self i s)
    have heq : pbMassIntOn p (insert i s) =
        (fun k ↦ (1 - p i) * pbMassIntOn p s k + p i * pbMassIntOn p s (k - 1)) :=
      funext (pbMassIntOn_insert p hi)
    rw [heq]
    exact (ih hps).convolve (pbMassIntOn_nonneg hps) (pbMassIntOn_cross s hps)
      hpi.1 (sub_nonneg.mpr hpi.2)

theorem pbMassIntOn_positive_between {p : ι → ℝ} (s : Finset ι)
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1)
    {i j k : ℤ} (hij : i ≤ j) (hjk : j ≤ k)
    (hi : 0 < pbMassIntOn p s i) (hk : 0 < pbMassIntOn p s k) :
    0 < pbMassIntOn p s j :=
  (pbMassIntOn_cross s hp).positive_between (pbMassIntOn_nonneg hp) hij hjk hi hk

theorem pbMassOn_logConcave {p : ι → ℝ} (s : Finset ι)
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) (k : ℕ) :
    pbMassOn p s k * pbMassOn p s (k + 2) ≤ (pbMassOn p s (k + 1)) ^ 2 := by
  have h := pbMassIntOn_cross s hp ((k + 1 : ℕ) : ℤ) ((k + 1 : ℕ) : ℤ) le_rfl
  have h0 : ((k + 1 : ℕ) : ℤ) - 1 = k := by omega
  have h2 : ((k + 1 : ℕ) : ℤ) + 1 = ((k + 2 : ℕ) : ℤ) := by omega
  simpa only [h0, h2, pbMassIntOn_natCast, pow_two] using h

theorem pbMassOn_strictLogConcave {p : ι → ℝ} (s : Finset ι)
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) (k : ℕ)
    (hk : 0 < pbMassOn p s (k + 1)) :
    pbMassOn p s k * pbMassOn p s (k + 2) < (pbMassOn p s (k + 1)) ^ 2 := by
  have hpos : 0 < pbMassIntOn p s ((k + 1 : ℕ) : ℤ) := by
    rw [pbMassIntOn_natCast]
    exact hk
  have h := pbMassIntOn_strictLogConcavity s hp ((k + 1 : ℕ) : ℤ) hpos
  have h0 : ((k + 1 : ℕ) : ℤ) - 1 = k := by omega
  have h2 : ((k + 1 : ℕ) : ℤ) + 1 = ((k + 2 : ℕ) : ℤ) := by omega
  simpa only [h0, h2, pbMassIntOn_natCast] using h

theorem pbMassOn_positive_between {p : ι → ℝ} (s : Finset ι)
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1)
    {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k)
    (hi : 0 < pbMassOn p s i) (hk : 0 < pbMassOn p s k) :
    0 < pbMassOn p s j := by
  have h := pbMassIntOn_positive_between s hp
    (i := (i : ℤ)) (j := (j : ℤ)) (k := (k : ℤ))
    (by exact_mod_cast hij) (by exact_mod_cast hjk) (by simpa using hi) (by simpa using hk)
  simpa using h

variable {n : ℕ}

theorem pbMass_logConcave {p : Fin n → ℝ} (hp : ValidParameters p) (k : ℕ) :
    pbMass p k * pbMass p (k + 2) ≤ (pbMass p (k + 1)) ^ 2 :=
  pbMassOn_logConcave univ (fun i _ ↦ hp i) k

theorem pbMass_strictLogConcave {p : Fin n → ℝ} (hp : ValidParameters p) (k : ℕ)
    (hk : 0 < pbMass p (k + 1)) :
    pbMass p k * pbMass p (k + 2) < (pbMass p (k + 1)) ^ 2 :=
  pbMassOn_strictLogConcave univ (fun i _ ↦ hp i) k hk

theorem pbMass_positive_between {p : Fin n → ℝ} (hp : ValidParameters p)
    {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k)
    (hi : 0 < pbMass p i) (hk : 0 < pbMass p k) : 0 < pbMass p j :=
  pbMassOn_positive_between univ (fun i _ ↦ hp i) hij hjk hi hk

end

end PoissonBinomialComparison

-- LikelihoodRatio
namespace PoissonBinomialComparison

open scoped BigOperators
open Finset

noncomputable section

def LikelihoodRatioLE (f g : ℤ → ℝ) : Prop :=
  ∀ i j : ℤ, i ≤ j → g i * f j ≤ g j * f i

def bernoulliConvolve (f : ℤ → ℝ) (t : ℝ) (k : ℤ) : ℝ :=
  (1 - t) * f k + t * f (k - 1)

theorem LikelihoodRatioLE.refl (f : ℤ → ℝ) : LikelihoodRatioLE f f := by
  intro i j _
  exact le_of_eq (mul_comm _ _)

theorem LikelihoodRatioLE.trans {f g h : ℤ → ℝ}
    (hfg : LikelihoodRatioLE f g) (hgh : LikelihoodRatioLE g h)
    (hf : ∀ k, 0 ≤ f k) (hh : ∀ k, 0 ≤ h k)
    (hgne : ∃ k, 0 < g k) : LikelihoodRatioLE f h := by
  intro i j hij
  by_cases hpos : 0 < h i * f j
  · have hip := pos_of_mul_pos_left hpos (hf j)
    have fjp := pos_of_mul_pos_right hpos (hh i)
    obtain ⟨k, hkp⟩ := hgne
    have gip : 0 < g i := by
      rcases le_total k i with hki | hik
      · have gjp := pos_of_mul_pos_left
          ((mul_pos hkp fjp).trans_le (hfg k j (hki.trans hij))) (hf k)
        exact pos_of_mul_pos_right ((mul_pos hip gjp).trans_le (hgh i j hij)) (hh j)
      · exact pos_of_mul_pos_right ((mul_pos hip hkp).trans_le (hgh i k hik)) (hh k)
    have gjp := pos_of_mul_pos_left
      ((mul_pos gip fjp).trans_le (hfg i j hij)) (hf i)
    apply (mul_le_mul_iff_right₀ gjp).mp
    have h1 := mul_le_mul_of_nonneg_right (hgh i j hij) (hf j)
    have h2 := mul_le_mul_of_nonneg_left (hfg i j hij) (hh j)
    nlinarith
  · exact (le_of_not_gt hpos).trans (mul_nonneg (hh j) (hf i))

theorem LikelihoodRatioLE.convolve {f g : ℤ → ℝ}
    (h : LikelihoodRatioLE f g) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    LikelihoodRatioLE (bernoulliConvolve f t) (bernoulliConvolve g t) := by
  intro i j hij
  by_cases heq : i = j
  · subst j
    exact le_rfl
  have h1 := mul_le_mul_of_nonneg_left (h i j hij) (sq_nonneg (1 - t))
  have h2 := mul_le_mul_of_nonneg_left (h (i - 1) (j - 1) (by omega)) (sq_nonneg t)
  have h3 := mul_le_mul_of_nonneg_left (h (i - 1) j (by omega))
    (mul_nonneg ht0 (sub_nonneg.mpr ht1))
  have h4 := mul_le_mul_of_nonneg_left (h i (j - 1) (by omega))
    (mul_nonneg ht0 (sub_nonneg.mpr ht1))
  unfold bernoulliConvolve
  nlinarith

theorem bernoulliConvolve_determinant (f : ℤ → ℝ) (a b : ℝ) (i j : ℤ) :
    bernoulliConvolve f b j * bernoulliConvolve f a i -
      bernoulliConvolve f b i * bernoulliConvolve f a j =
        (b - a) * (f i * f (j - 1) - f (i - 1) * f j) := by
  unfold bernoulliConvolve
  ring

theorem bernoulliConvolve_likelihoodRatio {f : ℤ → ℝ}
    (hf : MassCrossInequalities f) {a b : ℝ} (hab : a ≤ b) :
    LikelihoodRatioLE (bernoulliConvolve f a) (bernoulliConvolve f b) := by
  intro i j hij
  by_cases heq : i = j
  · subst j
    exact le_rfl
  apply sub_nonneg.mp
  rw [bernoulliConvolve_determinant]
  apply mul_nonneg (sub_nonneg.mpr hab)
  apply sub_nonneg.mpr
  simpa using hf i (j - 1) (by omega)

theorem bernoulliConvolve_middle_pos {f : ℤ → ℝ}
    (hf : ∀ k, 0 ≤ f k) (hc : MassCrossInequalities f)
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (k : ℤ)
    (h0 : 0 < bernoulliConvolve f a k)
    (h1 : 0 < bernoulliConvolve f a (k + 1)) : 0 < f k := by
  by_contra hnot
  have hk : f k = 0 := le_antisymm (le_of_not_gt hnot) (hf k)
  have hleft : 0 < a * f (k - 1) := by simpa [bernoulliConvolve, hk] using h0
  have hright : 0 < (1 - a) * f (k + 1) := by
    simpa [bernoulliConvolve, hk] using h1
  have hl := pos_of_mul_pos_right hleft ha0
  have hr := pos_of_mul_pos_right hright (sub_nonneg.mpr ha1)
  have hcross := hc k k le_rfl
  rw [hk, zero_mul] at hcross
  exact (not_lt_of_ge hcross) (mul_pos hl hr)

theorem bernoulliConvolve_strict_adjacent {f : ℤ → ℝ}
    (hf : ∀ k, 0 ≤ f k) (hc : MassCrossInequalities f)
    (hs : StrictMassLogConcavity f) {a b : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hab : a < b) (k : ℤ)
    (h0 : 0 < bernoulliConvolve f a k)
    (h1 : 0 < bernoulliConvolve f a (k + 1)) :
    bernoulliConvolve f b k * bernoulliConvolve f a (k + 1) <
      bernoulliConvolve f b (k + 1) * bernoulliConvolve f a k := by
  apply sub_pos.mp
  rw [bernoulliConvolve_determinant]
  have hstrict := hs k (bernoulliConvolve_middle_pos hf hc ha0 ha1 k h0 h1)
  simp only [add_sub_cancel_right]
  exact mul_pos (sub_pos.mpr hab) (by nlinarith)

theorem bernoulliConvolve_nonneg {f : ℤ → ℝ} (hf : ∀ k, 0 ≤ f k)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (k : ℤ) :
    0 ≤ bernoulliConvolve f t k :=
  add_nonneg (mul_nonneg (sub_nonneg.mpr ht1) (hf k)) (mul_nonneg ht0 (hf (k - 1)))

theorem bernoulliConvolve_exists_pos {f : ℤ → ℝ} (hf : ∀ k, 0 ≤ f k)
    (hne : ∃ k, 0 < f k) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∃ k, 0 < bernoulliConvolve f t k := by
  obtain ⟨k, hk⟩ := hne
  by_cases ht : t = 1
  · exact ⟨k + 1, by simpa [bernoulliConvolve, ht] using hk⟩
  · refine ⟨k, ?_⟩
    exact add_pos_of_pos_of_nonneg
      (mul_pos (sub_pos.mpr (lt_of_le_of_ne ht1 ht)) hk) (mul_nonneg ht0 (hf (k - 1)))

theorem LikelihoodRatioLE.strict_adjacent_trans {f g h : ℤ → ℝ}
    (hgh : LikelihoodRatioLE g h) (hf : ∀ k, 0 ≤ f k) (hg : ∀ k, 0 ≤ g k)
    (k : ℤ) (hstrict : g k * f (k + 1) < g (k + 1) * f k)
    (hh : 0 < h (k + 1)) :
    h k * f (k + 1) < h (k + 1) * f k := by
  have hgp : 0 < g (k + 1) := pos_of_mul_pos_left
    ((mul_nonneg (hg k) (hf (k + 1))).trans_lt hstrict) (hf k)
  apply (mul_lt_mul_iff_right₀ hgp).mp
  have h1 := mul_lt_mul_of_pos_left hstrict hh
  have h2 := mul_le_mul_of_nonneg_right (hgh k (k + 1) (by omega)) (hf (k + 1))
  nlinarith

variable {ι : Type*} [DecidableEq ι]

theorem pbMassIntOn_congr {p q : ι → ℝ} {s : Finset ι}
    (h : ∀ i ∈ s, p i = q i) (k : ℤ) :
    pbMassIntOn p s k = pbMassIntOn q s k := by
  unfold pbMassIntOn
  split
  · exact pbMassOn_congr h _
  · rfl

theorem pbMassIntOn_update_of_notMem (p : ι → ℝ) {s : Finset ι} {i : ι}
    (hi : i ∉ s) (a : ℝ) (k : ℤ) :
    pbMassIntOn (Function.update p i a) s k = pbMassIntOn p s k := by
  unfold pbMassIntOn
  split
  · exact pbMassOn_update_of_notMem p hi a _
  · rfl

theorem pbMassIntOn_update_insert (p : ι → ℝ) {s : Finset ι} {i : ι}
    (hi : i ∉ s) (a : ℝ) :
    pbMassIntOn (Function.update p i a) (insert i s) =
      bernoulliConvolve (pbMassIntOn p s) a := by
  funext k
  rw [pbMassIntOn_insert _ hi]
  simp only [Function.update_self, pbMassIntOn_update_of_notMem p hi, bernoulliConvolve]

theorem pbMassIntOn_exists_pos {p : ι → ℝ} (s : Finset ι)
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) : ∃ k : ℤ, 0 < pbMassIntOn p s k := by
  have hsum : 0 < ∑ k ∈ range (s.card + 1), pbMassOn p s k := by
    rw [sum_pbMassOn]
    norm_num
  obtain ⟨k, _, hk⟩ := (sum_pos_iff_of_nonneg (fun k _ ↦ pbMassOn_nonneg hp k)).mp hsum
  exact ⟨k, by simpa using hk⟩

theorem pbMassIntOn_update_likelihoodRatio (p : ι → ℝ) {s : Finset ι} {i : ι}
    (hi : i ∉ s) (hp : ∀ j ∈ s, 0 ≤ p j ∧ p j ≤ 1) {a b : ℝ} (hab : a ≤ b) :
    LikelihoodRatioLE (pbMassIntOn (Function.update p i a) (insert i s))
      (pbMassIntOn (Function.update p i b) (insert i s)) := by
  rw [pbMassIntOn_update_insert p hi a, pbMassIntOn_update_insert p hi b]
  exact bernoulliConvolve_likelihoodRatio (pbMassIntOn_cross s hp) hab

theorem pbMassIntOn_likelihoodRatio {p q : ι → ℝ} (s : Finset ι)
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1)
    (hq : ∀ i ∈ s, 0 ≤ q i ∧ q i ≤ 1)
    (hpq : ∀ i ∈ s, p i ≤ q i) :
    LikelihoodRatioLE (pbMassIntOn p s) (pbMassIntOn q s) := by
  induction s using Finset.induction_on with
  | empty =>
    intro i j hij
    simp only [pbMassIntOn_empty]
    exact le_of_eq (mul_comm _ _)
  | @insert i s hi ih =>
    have hps : ∀ j ∈ s, 0 ≤ p j ∧ p j ≤ 1 :=
      fun j hj ↦ hp j (mem_insert_of_mem hj)
    have hqs : ∀ j ∈ s, 0 ≤ q j ∧ q j ≤ 1 :=
      fun j hj ↦ hq j (mem_insert_of_mem hj)
    have hpqs : ∀ j ∈ s, p j ≤ q j := fun j hj ↦ hpq j (mem_insert_of_mem hj)
    have hpi := hp i (mem_insert_self i s)
    have hqi := hq i (mem_insert_self i s)
    have heqp : pbMassIntOn p (insert i s) = bernoulliConvolve (pbMassIntOn p s) (p i) :=
      funext (pbMassIntOn_insert p hi)
    have heqq : pbMassIntOn q (insert i s) = bernoulliConvolve (pbMassIntOn q s) (q i) :=
      funext (pbMassIntOn_insert q hi)
    rw [heqp, heqq]
    exact ((ih hps hqs hpqs).convolve hpi.1 hpi.2).trans
      (bernoulliConvolve_likelihoodRatio (pbMassIntOn_cross s hqs) (hpq i (mem_insert_self i s)))
      (bernoulliConvolve_nonneg (pbMassIntOn_nonneg hps) hpi.1 hpi.2)
      (bernoulliConvolve_nonneg (pbMassIntOn_nonneg hqs) hqi.1 hqi.2)
      (bernoulliConvolve_exists_pos (pbMassIntOn_nonneg hqs) (pbMassIntOn_exists_pos s hqs)
        hpi.1 hpi.2)

theorem pbMassIntOn_update_strict_adjacent (p : ι → ℝ) {s : Finset ι} {i : ι}
    (hi : i ∉ s) (hp : ∀ j ∈ s, 0 ≤ p j ∧ p j ≤ 1)
    {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hab : a < b) (k : ℤ)
    (h0 : 0 < pbMassIntOn (Function.update p i a) (insert i s) k)
    (h1 : 0 < pbMassIntOn (Function.update p i a) (insert i s) (k + 1)) :
    pbMassIntOn (Function.update p i b) (insert i s) k *
        pbMassIntOn (Function.update p i a) (insert i s) (k + 1) <
      pbMassIntOn (Function.update p i b) (insert i s) (k + 1) *
        pbMassIntOn (Function.update p i a) (insert i s) k := by
  rw [pbMassIntOn_update_insert p hi a] at h0 h1
  rw [pbMassIntOn_update_insert p hi a, pbMassIntOn_update_insert p hi b]
  exact bernoulliConvolve_strict_adjacent (pbMassIntOn_nonneg hp) (pbMassIntOn_cross s hp)
    (pbMassIntOn_strictLogConcavity s hp) ha0 ha1 hab k h0 h1

theorem pbMassIntOn_strict_adjacent {p q : ι → ℝ} (s : Finset ι)
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1)
    (hq : ∀ i ∈ s, 0 ≤ q i ∧ q i ≤ 1)
    (hpq : ∀ i ∈ s, p i ≤ q i) (hstrict : ∃ i ∈ s, p i < q i) (k : ℤ)
    (hp0 : 0 < pbMassIntOn p s k) (hp1 : 0 < pbMassIntOn p s (k + 1))
    (hq1 : 0 < pbMassIntOn q s (k + 1)) :
    pbMassIntOn q s k * pbMassIntOn p s (k + 1) <
      pbMassIntOn q s (k + 1) * pbMassIntOn p s k := by
  obtain ⟨i, hi, hpi⟩ := hstrict
  let r := Function.update p i (q i)
  have hr : ∀ j ∈ s, 0 ≤ r j ∧ r j ≤ 1 := by
    intro j hj
    by_cases hji : j = i
    · subst j
      simpa [r] using hq i hi
    · simpa [r, Function.update_of_ne hji] using hp j hj
  have hrq : ∀ j ∈ s, r j ≤ q j := by
    intro j hj
    by_cases hji : j = i
    · subst j
      simp [r]
    · simpa [r, Function.update_of_ne hji] using hpq j hj
  have hpr : pbMassIntOn r s k * pbMassIntOn p s (k + 1) <
      pbMassIntOn r s (k + 1) * pbMassIntOn p s k := by
    have hd := pbMassIntOn_update_strict_adjacent p (notMem_erase i s)
      (fun j hj ↦ hp j (mem_erase.mp hj).2) (hp i hi).1 (hp i hi).2 hpi k
    simpa [Function.update_eq_self, insert_erase hi, r] using hd
      (by simpa [Function.update_eq_self, insert_erase hi] using hp0)
      (by simpa [Function.update_eq_self, insert_erase hi] using hp1)
  exact (pbMassIntOn_likelihoodRatio s hr hq hrq).strict_adjacent_trans
    (pbMassIntOn_nonneg hp) (pbMassIntOn_nonneg hr) k hpr hq1

theorem pbMassIntOn_adjoin_likelihoodRatio (p : ι → ℝ) {s : Finset ι} {i : ι}
    (hi : i ∉ s) (hp : ∀ j ∈ s, 0 ≤ p j ∧ p j ≤ 1) (hpi : 0 ≤ p i) :
    LikelihoodRatioLE (pbMassIntOn p s) (pbMassIntOn p (insert i s)) := by
  have h := bernoulliConvolve_likelihoodRatio (pbMassIntOn_cross s hp) hpi
  have hzero : bernoulliConvolve (pbMassIntOn p s) 0 = pbMassIntOn p s := by
    funext k
    simp [bernoulliConvolve]
  have heq : pbMassIntOn p (insert i s) = bernoulliConvolve (pbMassIntOn p s) (p i) :=
    funext (pbMassIntOn_insert p hi)
  rwa [hzero, ← heq] at h

theorem pbMassIntOn_adjoin_strict_adjacent (p : ι → ℝ) {s : Finset ι} {i : ι}
    (hi : i ∉ s) (hp : ∀ j ∈ s, 0 ≤ p j ∧ p j ≤ 1) (hpi : 0 < p i) (k : ℤ)
    (h0 : 0 < pbMassIntOn p s k) (h1 : 0 < pbMassIntOn p s (k + 1)) :
    pbMassIntOn p (insert i s) k * pbMassIntOn p s (k + 1) <
      pbMassIntOn p (insert i s) (k + 1) * pbMassIntOn p s k := by
  have hzero : bernoulliConvolve (pbMassIntOn p s) 0 = pbMassIntOn p s := by
    funext j
    simp [bernoulliConvolve]
  have heq : pbMassIntOn p (insert i s) = bernoulliConvolve (pbMassIntOn p s) (p i) :=
    funext (pbMassIntOn_insert p hi)
  have h := bernoulliConvolve_strict_adjacent (pbMassIntOn_nonneg hp)
    (pbMassIntOn_cross s hp) (pbMassIntOn_strictLogConcavity s hp)
    (a := 0) (by norm_num) (by norm_num) hpi k (by rwa [hzero]) (by rwa [hzero])
  simpa only [hzero, ← heq] using h

theorem pbMassIntOn_equal_adjacent_increase {p q : ι → ℝ} (s : Finset ι)
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1)
    (hq : ∀ i ∈ s, 0 ≤ q i ∧ q i ≤ 1)
    (hpq : ∀ i ∈ s, p i ≤ q i) (hstrict : ∃ i ∈ s, p i < q i) (k : ℤ)
    (heq : pbMassIntOn p s k = pbMassIntOn p s (k + 1))
    (hp1 : 0 < pbMassIntOn p s (k + 1)) (hq1 : 0 < pbMassIntOn q s (k + 1)) :
    pbMassIntOn q s k < pbMassIntOn q s (k + 1) := by
  have h := pbMassIntOn_strict_adjacent s hp hq hpq hstrict k (by rwa [heq]) hp1 hq1
  rw [heq] at h
  exact (mul_lt_mul_iff_left₀ hp1).mp h

theorem pbMassIntOn_adjacent_disappear {p q : ι → ℝ} (s : Finset ι)
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1)
    (hq : ∀ i ∈ s, 0 ≤ q i ∧ q i ≤ 1)
    (hpq : ∀ i ∈ s, p i ≤ q i) (k : ℤ)
    (hp1 : 0 < pbMassIntOn p s (k + 1)) (hq1 : pbMassIntOn q s (k + 1) = 0) :
    pbMassIntOn q s k = 0 := by
  have h := pbMassIntOn_likelihoodRatio s hp hq hpq k (k + 1) (by omega)
  rw [hq1, zero_mul] at h
  apply le_antisymm _ (pbMassIntOn_nonneg hq k)
  by_contra hnot
  exact (not_lt_of_ge h) (mul_pos (lt_of_not_ge hnot) hp1)

theorem pbMassIntOn_adjacent_sign_preserved {p q : ι → ℝ} (s : Finset ι)
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1)
    (hq : ∀ i ∈ s, 0 ≤ q i ∧ q i ≤ 1)
    (hpq : ∀ i ∈ s, p i ≤ q i) (hstrict : ∃ i ∈ s, p i < q i) (k : ℤ)
    (hp0 : 0 < pbMassIntOn p s k) (hp1 : 0 < pbMassIntOn p s (k + 1))
    (horder : pbMassIntOn p s k ≤ pbMassIntOn p s (k + 1))
    (hq1 : 0 < pbMassIntOn q s (k + 1)) :
    pbMassIntOn q s k < pbMassIntOn q s (k + 1) := by
  have h := pbMassIntOn_strict_adjacent s hp hq hpq hstrict k hp0 hp1 hq1
  exact (mul_lt_mul_iff_left₀ hp1).mp
    (h.trans_le (mul_le_mul_of_nonneg_left horder hq1.le))

variable {n : ℕ}

theorem pbMass_likelihoodRatio {p q : Fin n → ℝ} (h : AdmissiblePair p q)
    (i j : ℕ) (hij : i ≤ j) :
    pbMass p i * pbMass q j ≤ pbMass p j * pbMass q i := by
  have h' := pbMassIntOn_likelihoodRatio univ (fun i _ ↦ h.2.1 i)
    (fun i _ ↦ h.1 i) (fun i _ ↦ h.2.2 i) (i : ℤ) (j : ℤ) (by omega)
  simpa [pbMass] using h'

theorem pbMass_strict_adjacent_likelihoodRatio {p q : Fin n → ℝ}
    (h : AdmissiblePair p q) (hstrict : ∃ i, q i < p i) (k : ℕ)
    (hq0 : 0 < pbMass q k) (hq1 : 0 < pbMass q (k + 1))
    (hp1 : 0 < pbMass p (k + 1)) :
    pbMass p k * pbMass q (k + 1) < pbMass p (k + 1) * pbMass q k := by
  have hs : ∃ i ∈ (univ : Finset (Fin n)), q i < p i := by simpa using hstrict
  have hc : (k : ℤ) + 1 = ((k + 1 : ℕ) : ℤ) := by omega
  have h' := pbMassIntOn_strict_adjacent univ (fun i _ ↦ h.2.1 i)
    (fun i _ ↦ h.1 i) (fun i _ ↦ h.2.2 i) hs (k : ℤ)
    (by simpa only [pbMassIntOn_natCast, pbMass] using hq0)
    (by simpa only [hc, pbMassIntOn_natCast, pbMass] using hq1)
    (by simpa only [hc, pbMassIntOn_natCast, pbMass] using hp1)
  simpa only [hc, pbMassIntOn_natCast, pbMass] using h'

theorem pbMass_equal_adjacent_increase {p q : Fin n → ℝ}
    (h : AdmissiblePair p q) (hstrict : ∃ i, q i < p i) (k : ℕ)
    (heq : pbMass q k = pbMass q (k + 1))
    (hq1 : 0 < pbMass q (k + 1)) (hp1 : 0 < pbMass p (k + 1)) :
    pbMass p k < pbMass p (k + 1) := by
  have h' := pbMass_strict_adjacent_likelihoodRatio h hstrict k (by rwa [heq]) hq1 hp1
  rw [heq] at h'
  exact (mul_lt_mul_iff_left₀ hq1).mp h'

theorem pbMass_adjacent_disappear {p q : Fin n → ℝ} (h : AdmissiblePair p q)
    (k : ℕ) (hq1 : 0 < pbMass q (k + 1)) (hp1 : pbMass p (k + 1) = 0) :
    pbMass p k = 0 := by
  have h' := pbMass_likelihoodRatio h k (k + 1) (by omega)
  rw [hp1, zero_mul] at h'
  apply le_antisymm _ (pbMass_nonneg h.1 k)
  by_contra hnot
  exact (not_lt_of_ge h') (mul_pos (lt_of_not_ge hnot) hq1)

theorem pbMass_adjacent_sign_preserved {p q : Fin n → ℝ}
    (h : AdmissiblePair p q) (hstrict : ∃ i, q i < p i) (k : ℕ)
    (hq0 : 0 < pbMass q k) (hq1 : 0 < pbMass q (k + 1))
    (horder : pbMass q k ≤ pbMass q (k + 1)) (hp1 : 0 < pbMass p (k + 1)) :
    pbMass p k < pbMass p (k + 1) := by
  have h' := pbMass_strict_adjacent_likelihoodRatio h hstrict k hq0 hq1 hp1
  exact (mul_lt_mul_iff_left₀ hq1).mp
    (h'.trans_le (mul_le_mul_of_nonneg_left horder hp1.le))

end

end PoissonBinomialComparison

-- Endpoints
namespace PoissonBinomialComparison

open scoped BigOperators
open Finset

noncomputable section

variable {n : ℕ} {p q : Fin n → ℝ}

theorem meanGap_nonneg (h : AdmissiblePair p q) : 0 ≤ meanGap p q := by
  rw [meanGap_eq_sum]
  exact sum_nonneg fun i _ ↦ sub_nonneg.mpr (h.2.2 i)

theorem meanGap_le_dimension (h : AdmissiblePair p q) : meanGap p q ≤ n := by
  rw [meanGap_eq_sum]
  calc
    ∑ i, (p i - q i) ≤ ∑ _i : Fin n, (1 : ℝ) := by
      apply sum_le_sum
      intro i _
      have hp := (h.1 i).2
      have hq := (h.2.1 i).1
      linarith
    _ = n := by simp

theorem meanGap_eq_zero_iff (h : AdmissiblePair p q) :
    meanGap p q = 0 ↔ p = q := by
  constructor
  · intro hz
    rw [meanGap_eq_sum] at hz
    have hall := (sum_eq_zero_iff_of_nonneg
      (fun i (_ : i ∈ (univ : Finset (Fin n))) ↦ sub_nonneg.mpr (h.2.2 i))).mp hz
    funext i
    exact sub_eq_zero.mp (hall i (mem_univ i))
  · rintro rfl
    simp [meanGap]

theorem meanGap_eq_dimension_iff (h : AdmissiblePair p q) :
    meanGap p q = n ↔ p = (fun _ ↦ 1) ∧ q = (fun _ ↦ 0) := by
  constructor
  · intro hn
    have hz : ∑ i, (1 - (p i - q i)) = (0 : ℝ) := by
      simp only [sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
        mul_one]
      change (n : ℝ) - meanGap p q = 0
      linarith
    have hall := (sum_eq_zero_iff_of_nonneg
      (fun i (_ : i ∈ (univ : Finset (Fin n))) ↦ show 0 ≤ 1 - (p i - q i) by
        have hp := (h.1 i).2
        have hq := (h.2.1 i).1
        linarith)).mp hz
    constructor
    · funext i
      have hi := hall i (mem_univ i)
      have hp := (h.1 i).2
      have hq := (h.2.1 i).1
      linarith
    · funext i
      have hi := hall i (mem_univ i)
      have hp := (h.1 i).2
      have hq := (h.2.1 i).1
      linarith
  · rintro ⟨rfl, rfl⟩
    simp [meanGap]

private theorem pbTailOn_const_zero {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (k : ℕ) :
    pbTailOn (fun _ ↦ (0 : ℝ)) s k = if k = 0 then 1 else 0 := by
  induction s using Finset.induction_on generalizing k with
  | empty =>
    cases k <;> simp [pbTailOn, bernoulliWeight]
  | @insert i s hi ih =>
    cases k with
    | zero => simp
    | succ k => simp [pbTailOn_insert_succ _ hi, ih]

private theorem pbTailOn_const_one {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (k : ℕ) :
    pbTailOn (fun _ ↦ (1 : ℝ)) s k = if k ≤ s.card then 1 else 0 := by
  induction s using Finset.induction_on generalizing k with
  | empty =>
    cases k <;> simp [pbTailOn, bernoulliWeight]
  | @insert i s hi ih =>
    cases k with
    | zero => simp
    | succ k => simp [pbTailOn_insert_succ _ hi, ih, card_insert_of_notMem hi]

theorem pbTail_const_zero (k : ℕ) :
    pbTail (fun _ : Fin n ↦ (0 : ℝ)) k = if k = 0 then 1 else 0 :=
  pbTailOn_const_zero univ k

theorem pbTail_const_one (k : ℕ) :
    pbTail (fun _ : Fin n ↦ (1 : ℝ)) k = if k ≤ n then 1 else 0 := by
  simpa [pbTail] using pbTailOn_const_one (univ : Finset (Fin n)) k

@[simp] theorem tailObjective_self (p : Fin n → ℝ) : tailObjective p p = 0 := by
  by_cases hn : 0 < n
  · obtain ⟨k, _, hk⟩ := tailObjective_attained p p hn
    simpa [tailDiff] using hk
  · simp [tailObjective, hn]

theorem tailObjective_const_one_zero (hn : 0 < n) :
    tailObjective (fun _ : Fin n ↦ (1 : ℝ)) (fun _ ↦ 0) = 1 := by
  obtain ⟨k, hk, heq⟩ := tailObjective_attained
    (fun _ : Fin n ↦ (1 : ℝ)) (fun _ ↦ 0) hn
  have hk0 : k ≠ 0 := by have := (mem_Icc.mp hk).1; omega
  simpa [tailDiff, pbTail_const_one, pbTail_const_zero, (mem_Icc.mp hk).2, hk0] using heq

theorem tailObjective_eq_zero_of_meanGap_eq_zero (h : AdmissiblePair p q)
    (hgap : meanGap p q = 0) : tailObjective p q = 0 := by
  rw [(meanGap_eq_zero_iff h).mp hgap]
  exact tailObjective_self q

theorem tailObjective_eq_one_of_meanGap_eq_dimension (h : AdmissiblePair p q)
    (hn : 0 < n) (hgap : meanGap p q = n) : tailObjective p q = 1 := by
  obtain ⟨rfl, rfl⟩ := (meanGap_eq_dimension_iff h).mp hgap
  exact tailObjective_const_one_zero hn

end

end PoissonBinomialComparison

-- ActiveThresholds
namespace PoissonBinomialComparison

open scoped BigOperators
open Finset

noncomputable section

variable {n : ℕ} {p q : Fin n → ℝ}

def activeThresholds (p q : Fin n → ℝ) : Finset ℕ :=
  (Icc 1 n).filter (fun k ↦ tailDiff p q k = tailObjective p q)

theorem mem_activeThresholds (p q : Fin n → ℝ) (k : ℕ) :
    k ∈ activeThresholds p q ↔
      1 ≤ k ∧ k ≤ n ∧ tailDiff p q k = tailObjective p q := by
  simp only [activeThresholds, mem_filter, mem_Icc]
  tauto

theorem activeThresholds_nonempty (p q : Fin n → ℝ) (hn : 0 < n) :
    (activeThresholds p q).Nonempty := by
  obtain ⟨k, hk, heq⟩ := tailObjective_attained p q hn
  exact ⟨k, mem_filter.mpr ⟨hk, heq.symm⟩⟩

theorem exists_strict_coordinate_of_meanGap_pos (h : AdmissiblePair p q)
    (hgap : 0 < meanGap p q) : ∃ i, q i < p i := by
  rw [meanGap_eq_sum] at hgap
  obtain ⟨i, _, hi⟩ := (sum_pos_iff_of_nonneg
    (fun i (_ : i ∈ (univ : Finset (Fin n))) ↦ sub_nonneg.mpr (h.2.2 i))).mp hgap
  exact ⟨i, sub_pos.mp hi⟩

theorem tailObjective_pos_of_meanGap_pos (hgap : 0 < meanGap p q) :
    0 < tailObjective p q := by
  by_contra hnot
  have hsum : ∑ k ∈ Icc 1 n, tailDiff p q k ≤ 0 := by
    apply sum_nonpos
    intro k hk
    exact (tailDiff_le_tailObjective p q hk).trans (le_of_not_gt hnot)
  rw [sum_tailDiff] at hsum
  exact not_lt_of_ge hsum hgap

theorem tailDiff_sub_succ (p q : Fin n → ℝ) (k : ℕ) :
    tailDiff p q k - tailDiff p q (k + 1) = pbMass p k - pbMass q k := by
  have hp := pbTail_sub_succ p k
  have hq := pbTail_sub_succ q k
  unfold tailDiff
  linarith

theorem pbMass_strict_likelihoodRatio (h : AdmissiblePair p q)
    (hstrict : ∃ i, q i < p i) {i j : ℕ} (hij : i < j)
    (hq0 : 0 < pbMass q i) (hq1 : 0 < pbMass q j) (hp1 : 0 < pbMass p j) :
    pbMass p i * pbMass q j < pbMass p j * pbMass q i := by
  by_cases hp0 : 0 < pbMass p i
  · have hqm : 0 < pbMass q (i + 1) :=
      pbMass_positive_between h.2.1 (by omega) (by omega) hq0 hq1
    have hpm : 0 < pbMass p (i + 1) := pos_of_mul_pos_left
      ((mul_pos hp0 hqm).trans_le (pbMass_likelihoodRatio h i (i + 1) (by omega)))
      (pbMass_nonneg h.2.1 i)
    have hs := pbMass_strict_adjacent_likelihoodRatio h hstrict i hq0 hqm hpm
    have hw := pbMass_likelihoodRatio h (i + 1) j (by omega)
    apply (mul_lt_mul_iff_right₀ hqm).mp
    have h1 := mul_lt_mul_of_pos_right hs hq1
    have h2 := mul_le_mul_of_nonneg_right hw hq0.le
    nlinarith
  · have hz : pbMass p i = 0 := le_antisymm (le_of_not_gt hp0) (pbMass_nonneg h.1 i)
    rw [hz, zero_mul]
    exact mul_pos hp1 hq0

theorem pbTail_eq_one_of_mass_zero_below (p : Fin n → ℝ) (k : ℕ)
    (hz : ∀ j < k, pbMass p j = 0) : pbTail p k = 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hprev := ih (fun j hj ↦ hz j (by omega))
    have hdiff := pbTail_sub_succ p k
    rw [hz k (by omega), hprev] at hdiff
    linarith

theorem pbTail_eq_zero_or_one_of_mass_zero (hp : ValidParameters p) (k : ℕ)
    (hz : pbMass p k = 0) : pbTail p k = 0 ∨ pbTail p k = 1 := by
  by_cases hbelow : ∃ j < k, 0 < pbMass p j
  · obtain ⟨j, hj, hpj⟩ := hbelow
    left
    rw [pbTail_eq_sum_mass]
    apply sum_eq_zero
    intro l hl
    have hkl := (mem_Icc.mp hl).1
    apply le_antisymm _ (pbMass_nonneg hp l)
    by_contra hnot
    have hpk := pbMass_positive_between hp hj.le hkl hpj (lt_of_not_ge hnot)
    rw [hz] at hpk
    exact lt_irrefl _ hpk
  · right
    apply pbTail_eq_one_of_mass_zero_below
    intro j hj
    apply le_antisymm _ (pbMass_nonneg hp j)
    exact le_of_not_gt (fun hpos ↦ hbelow ⟨j, hj, hpos⟩)

theorem mass_pair_pos_of_tailDiff_between (h : AdmissiblePair p q) (k : ℕ)
    (h0 : 0 < tailDiff p q k) (h1 : tailDiff p q k < 1) :
    0 < pbMass p k ∨ 0 < pbMass q k := by
  by_contra hnot
  push Not at hnot
  have hpz := le_antisymm hnot.1 (pbMass_nonneg h.1 k)
  have hqz := le_antisymm hnot.2 (pbMass_nonneg h.2.1 k)
  rcases pbTail_eq_zero_or_one_of_mass_zero h.1 k hpz with hp | hp <;>
    rcases pbTail_eq_zero_or_one_of_mass_zero h.2.1 k hqz with hq | hq <;>
    simp only [tailDiff, hp, hq] at h0 h1 <;> norm_num at *

theorem mass_pair_pos_of_succ_tailDiff_between (h : AdmissiblePair p q) (k : ℕ)
    (h0 : 0 < tailDiff p q (k + 1)) (h1 : tailDiff p q (k + 1) < 1) :
    0 < pbMass p k ∨ 0 < pbMass q k := by
  by_contra hnot
  push Not at hnot
  have hpz := le_antisymm hnot.1 (pbMass_nonneg h.1 k)
  have hqz := le_antisymm hnot.2 (pbMass_nonneg h.2.1 k)
  have heq : tailDiff p q k = tailDiff p q (k + 1) := by
    have hd := tailDiff_sub_succ p q k
    rw [hpz, hqz] at hd
    linarith
  rcases mass_pair_pos_of_tailDiff_between h k (by rwa [heq]) (by rwa [heq]) with hp | hq
  · exact not_lt_of_ge hnot.1 hp
  · exact not_lt_of_ge hnot.2 hq

theorem activeThresholds_distance_le_one (h : AdmissiblePair p q)
    (hgap : 0 < meanGap p q) (hT : tailObjective p q < 1)
    {k l : ℕ} (hk : k ∈ activeThresholds p q) (hl : l ∈ activeThresholds p q) :
    l ≤ k + 1 := by
  by_contra hfar
  have hk' := (mem_activeThresholds p q k).mp hk
  have hl' := (mem_activeThresholds p q l).mp hl
  have hpos := tailObjective_pos_of_meanGap_pos hgap
  have hstrict := exists_strict_coordinate_of_meanGap_pos h hgap
  have hkstep : k + 1 ∈ Icc 1 n := mem_Icc.mpr ⟨by omega, by omega⟩
  have hlstep : l - 1 ∈ Icc 1 n := mem_Icc.mpr ⟨by omega, by omega⟩
  have hlpred : l - 1 + 1 = l := by omega
  have hleft : pbMass q k ≤ pbMass p k := by
    have hb := tailDiff_le_tailObjective p q hkstep
    have hd := tailDiff_sub_succ p q k
    rw [hk'.2.2] at hd
    linarith
  have hright : pbMass p (l - 1) ≤ pbMass q (l - 1) := by
    have hb := tailDiff_le_tailObjective p q hlstep
    have hd := tailDiff_sub_succ p q (l - 1)
    rw [hlpred, hl'.2.2] at hd
    linarith
  have hpk : 0 < pbMass p k := by
    rcases mass_pair_pos_of_tailDiff_between h k (by rwa [hk'.2.2])
      (by rwa [hk'.2.2]) with hp | hq
    · exact hp
    · exact hq.trans_le hleft
  have hql : 0 < pbMass q (l - 1) := by
    rcases mass_pair_pos_of_succ_tailDiff_between h (l - 1)
      (by rwa [hlpred, hl'.2.2]) (by rwa [hlpred, hl'.2.2]) with hp | hq
    · exact hp.trans_le hright
    · exact hq
  have hw := pbMass_likelihoodRatio h k (l - 1) (by omega)
  have hprod := (mul_pos hpk hql).trans_le hw
  have hpl := pos_of_mul_pos_left hprod (pbMass_nonneg h.2.1 k)
  have hqk := pos_of_mul_pos_right hprod (pbMass_nonneg h.1 (l - 1))
  have hs := pbMass_strict_likelihoodRatio h hstrict (by omega : k < l - 1) hqk hql hpl
  have hreverse : pbMass p (l - 1) * pbMass q k ≤ pbMass p k * pbMass q (l - 1) := by
    calc
      pbMass p (l - 1) * pbMass q k ≤ pbMass q (l - 1) * pbMass q k :=
        mul_le_mul_of_nonneg_right hright hqk.le
      _ ≤ pbMass q (l - 1) * pbMass p k := mul_le_mul_of_nonneg_left hleft hql.le
      _ = pbMass p k * pbMass q (l - 1) := mul_comm _ _
  exact not_lt_of_ge hreverse hs

theorem activeThresholds_singleton_or_adjacent (h : AdmissiblePair p q)
    (hgap : 0 < meanGap p q) (hT : tailObjective p q < 1) :
    ∃ k, 1 ≤ k ∧ k ≤ n ∧
      (activeThresholds p q = {k} ∨
        (k + 1 ≤ n ∧ activeThresholds p q = {k, k + 1})) := by
  obtain ⟨i, _⟩ := exists_strict_coordinate_of_meanGap_pos h hgap
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  have hne := activeThresholds_nonempty p q hn
  let k := (activeThresholds p q).min' hne
  have hk : k ∈ activeThresholds p q := min'_mem _ hne
  have hk' := (mem_activeThresholds p q k).mp hk
  have hbounds : ∀ l ∈ activeThresholds p q, k ≤ l ∧ l ≤ k + 1 := by
    intro l hl
    have hmin : k ≤ l := min'_le _ l hl
    exact ⟨hmin, activeThresholds_distance_le_one h hgap hT hk hl⟩
  refine ⟨k, hk'.1, hk'.2.1, ?_⟩
  by_cases hnext : k + 1 ∈ activeThresholds p q
  · right
    refine ⟨((mem_activeThresholds p q (k + 1)).mp hnext).2.1, ?_⟩
    ext l
    simp only [mem_insert, mem_singleton]
    constructor
    · intro hl
      have hb := hbounds l hl
      omega
    · rintro (rfl | rfl)
      · exact hk
      · exact hnext
  · left
    apply eq_singleton_iff_unique_mem.mpr
    refine ⟨hk, ?_⟩
    intro l hl
    have hb := hbounds l hl
    have hneq : l ≠ k + 1 := by
      intro heq
      exact hnext (heq ▸ hl)
    omega

end

end PoissonBinomialComparison

-- RandomizedThreshold
namespace PoissonBinomialComparison

open scoped BigOperators
open Finset

noncomputable section

variable {ι : Type*} [DecidableEq ι]

def randomizedTailOn (p : ι → ℝ) (s : Finset ι) (w : ℝ) (k : ℕ) : ℝ :=
  w * pbTailOn p s k + (1 - w) * pbTailOn p s (k + 1)

def randomizedSlopeOn (p : ι → ℝ) (s : Finset ι) (w : ℝ) (k : ℕ) : ℝ :=
  (1 - w) * pbMassOn p s k + w * (if k = 0 then 0 else pbMassOn p s (k - 1))

def randomizedCoefficientOn (p : ι → ℝ) (s : Finset ι) (w : ℝ) (k : ℕ) : ℝ :=
  (if k = 0 then 0 else randomizedSlopeOn p s w (k - 1)) - randomizedSlopeOn p s w k

private theorem RandomizedThreshold_randomizedTailOn_congr {p q : ι → ℝ} {s : Finset ι}
    (h : ∀ i ∈ s, p i = q i) (w : ℝ) (k : ℕ) :
    randomizedTailOn p s w k = randomizedTailOn q s w k := by
  simp only [randomizedTailOn, pbTailOn_congr h]

private theorem RandomizedThreshold_randomizedSlopeOn_congr {p q : ι → ℝ} {s : Finset ι}
    (h : ∀ i ∈ s, p i = q i) (w : ℝ) (k : ℕ) :
    randomizedSlopeOn p s w k = randomizedSlopeOn q s w k := by
  simp only [randomizedSlopeOn, pbMassOn_congr h]

private theorem RandomizedThreshold_randomizedCoefficientOn_congr {p q : ι → ℝ} {s : Finset ι}
    (h : ∀ i ∈ s, p i = q i) (w : ℝ) (k : ℕ) :
    randomizedCoefficientOn p s w k = randomizedCoefficientOn q s w k := by
  simp only [randomizedCoefficientOn, RandomizedThreshold_randomizedSlopeOn_congr h]

theorem randomizedTailOn_eq_adjoin (p : ι → ℝ) {s : Finset ι} {e : ι}
    (he : e ∉ s) (w : ℝ) (k : ℕ) :
    randomizedTailOn p s w k =
      pbTailOn (Function.update p e w) (insert e s) (k + 1) := by
  rw [pbTailOn_insert_succ _ he]
  simp only [Function.update_self, pbTailOn_update_of_notMem p he, randomizedTailOn]
  ring

theorem randomizedSlopeOn_eq_adjoin (p : ι → ℝ) {s : Finset ι} {e : ι}
    (he : e ∉ s) (w : ℝ) (k : ℕ) :
    randomizedSlopeOn p s w k =
      pbMassOn (Function.update p e w) (insert e s) k := by
  cases k with
  | zero =>
    rw [pbMassOn_insert_zero _ he]
    simp [randomizedSlopeOn, pbMassOn_update_of_notMem p he]
  | succ k =>
    rw [pbMassOn_insert_succ _ he]
    simp [randomizedSlopeOn, pbMassOn_update_of_notMem p he]

theorem randomizedCoefficientOn_eq_adjoin (p : ι → ℝ) {s : Finset ι} {e : ι}
    (he : e ∉ s) (w : ℝ) (k : ℕ) :
    randomizedCoefficientOn p s w (k + 1) =
      pbMassOn (Function.update p e w) (insert e s) k -
        pbMassOn (Function.update p e w) (insert e s) (k + 1) := by
  simp only [randomizedCoefficientOn, Nat.add_one_ne_zero, ite_false,
    Nat.add_sub_cancel, randomizedSlopeOn_eq_adjoin p he]

theorem randomizedTailOn_insert (p : ι → ℝ) {s : Finset ι} {i : ι}
    (hi : i ∉ s) (w : ℝ) (k : ℕ) :
    randomizedTailOn p (insert i s) w k =
      randomizedTailOn p s w k + p i * randomizedSlopeOn p s w k := by
  cases k with
  | zero =>
    simp only [randomizedTailOn, pbTailOn_zero, pbTailOn_insert_succ p hi,
      randomizedSlopeOn, ite_true, mul_zero, add_zero]
    have h := pbTailOn_sub_succ p s 0
    simp only [pbTailOn_zero] at h
    rw [← h]
    ring
  | succ k =>
    simp only [randomizedTailOn, pbTailOn_insert_succ p hi, randomizedSlopeOn,
      Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel]
    rw [← pbTailOn_sub_succ p s k, ← pbTailOn_sub_succ p s (k + 1)]
    ring

theorem randomizedSlopeOn_insert (p : ι → ℝ) {s : Finset ι} {i : ι}
    (hi : i ∉ s) (w : ℝ) (k : ℕ) :
    randomizedSlopeOn p (insert i s) w k =
      randomizedSlopeOn p s w k + p i * randomizedCoefficientOn p s w k := by
  cases k with
  | zero =>
    simp only [randomizedSlopeOn, randomizedCoefficientOn, ite_true, mul_zero,
      add_zero, pbMassOn_insert_zero p hi]
    ring
  | succ k =>
    cases k with
    | zero =>
      simp only [randomizedSlopeOn, randomizedCoefficientOn, Nat.succ_ne_zero,
        ite_false, Nat.add_sub_cancel, ite_true, mul_zero, add_zero,
        pbMassOn_insert_succ p hi, pbMassOn_insert_zero p hi]
      ring
    | succ k =>
      simp only [randomizedSlopeOn, randomizedCoefficientOn, Nat.succ_ne_zero,
        ite_false, Nat.add_sub_cancel, pbMassOn_insert_succ p hi]
      ring

theorem randomizedSlopeOn_insert_sub (p : ι → ℝ) {s : Finset ι} {i j : ι}
    (hi : i ∉ s) (hj : j ∉ s) (w : ℝ) (k : ℕ) :
    randomizedSlopeOn p (insert j s) w k - randomizedSlopeOn p (insert i s) w k =
      (p j - p i) * randomizedCoefficientOn p s w k := by
  rw [randomizedSlopeOn_insert p hj, randomizedSlopeOn_insert p hi]
  ring

theorem randomizedTailOn_insert_insert (p : ι → ℝ) {s : Finset ι} {i j : ι}
    (hi : i ∉ s) (hj : j ∉ s) (hij : i ≠ j) (w : ℝ) (k : ℕ) :
    randomizedTailOn p (insert i (insert j s)) w k =
      randomizedTailOn p s w k + (p i + p j) * randomizedSlopeOn p s w k +
        p i * p j * randomizedCoefficientOn p s w k := by
  rw [randomizedTailOn_insert p (by simp [hi, hij]),
    randomizedTailOn_insert p hj, randomizedSlopeOn_insert p hj]
  ring

theorem randomizedTailOn_update_sub (p : ι → ℝ) {s : Finset ι} {i : ι}
    (hi : i ∉ s) (a b w : ℝ) (k : ℕ) :
    randomizedTailOn (Function.update p i b) (insert i s) w k -
      randomizedTailOn (Function.update p i a) (insert i s) w k =
        (b - a) * randomizedSlopeOn p s w k := by
  have heq (x : ℝ) : ∀ j ∈ s, Function.update p i x j = p j := by
    intro j hj
    have hji : j ≠ i := by
      intro h
      subst j
      exact hi hj
    exact Function.update_of_ne hji x p
  rw [randomizedTailOn_insert _ hi, randomizedTailOn_insert _ hi,
    RandomizedThreshold_randomizedTailOn_congr (heq b), RandomizedThreshold_randomizedTailOn_congr (heq a),
    RandomizedThreshold_randomizedSlopeOn_congr (heq b), RandomizedThreshold_randomizedSlopeOn_congr (heq a)]
  simp only [Function.update_self]
  ring

theorem randomizedTailOn_update_update (p : ι → ℝ) {s : Finset ι} {i j : ι}
    (hi : i ∉ s) (hj : j ∉ s) (hij : i ≠ j) (a b w : ℝ) (k : ℕ) :
    randomizedTailOn (Function.update (Function.update p i a) j b)
      (insert i (insert j s)) w k = randomizedTailOn p s w k +
        (a + b) * randomizedSlopeOn p s w k + a * b * randomizedCoefficientOn p s w k := by
  have heq : ∀ l ∈ s, Function.update (Function.update p i a) j b l = p l := by
    intro l hl
    have hlj : l ≠ j := by
      intro h
      subst l
      exact hj hl
    have hli : l ≠ i := by
      intro h
      subst l
      exact hi hl
    rw [Function.update_of_ne hlj, Function.update_of_ne hli]
  rw [randomizedTailOn_insert_insert _ hi hj hij,
    RandomizedThreshold_randomizedTailOn_congr heq, RandomizedThreshold_randomizedSlopeOn_congr heq,
    RandomizedThreshold_randomizedCoefficientOn_congr heq]
  simp [Function.update_of_ne hij]

theorem randomizedTailOn_split (p : ι → ℝ) {s : Finset ι} {i j : ι}
    (hi : i ∉ s) (hj : j ∉ s) (hij : i ≠ j) (u t w : ℝ) (k : ℕ) :
    randomizedTailOn (Function.update (Function.update p i (u + t)) j (u - t))
        (insert i (insert j s)) w k -
      randomizedTailOn (Function.update (Function.update p i u) j u)
        (insert i (insert j s)) w k = -randomizedCoefficientOn p s w k * t ^ 2 := by
  rw [randomizedTailOn_update_update p hi hj hij,
    randomizedTailOn_update_update p hi hj hij]
  ring

variable {n : ℕ}

def randomizedTail (p : Fin n → ℝ) (w : ℝ) (k : ℕ) : ℝ :=
  randomizedTailOn p univ w k

def randomizedGradient (p : Fin n → ℝ) (w : ℝ) (k : ℕ) (i : Fin n) : ℝ :=
  randomizedSlopeOn p (univ.erase i) w k

def randomizedMixedCoefficient (p : Fin n → ℝ) (w : ℝ) (k : ℕ)
    (i j : Fin n) : ℝ :=
  randomizedCoefficientOn p ((univ.erase i).erase j) w k

theorem randomizedTail_update_sub (p : Fin n → ℝ) (i : Fin n) (a b w : ℝ) (k : ℕ) :
    randomizedTail (Function.update p i b) w k -
      randomizedTail (Function.update p i a) w k = (b - a) * randomizedGradient p w k i := by
  simpa [randomizedTail, randomizedGradient] using
    randomizedTailOn_update_sub p (notMem_erase i univ) a b w k

theorem randomizedGradient_sub (p : Fin n → ℝ) {i j : Fin n}
    (hij : i ≠ j) (w : ℝ) (k : ℕ) :
    randomizedGradient p w k i - randomizedGradient p w k j =
      (p j - p i) * randomizedMixedCoefficient p w k i j := by
  let s := (univ.erase i).erase j
  have hi : i ∉ s := by simp [s]
  have hj : j ∉ s := by simp [s]
  have hsi : insert i s = univ.erase j := by
    ext x
    by_cases hxi : x = i <;> by_cases hxj : x = j <;> simp_all [s]
  have hsj : insert j s = univ.erase i := by
    ext x
    by_cases hxi : x = i <;> by_cases hxj : x = j <;> simp_all [s]
  simpa only [hsi, hsj, randomizedGradient, randomizedMixedCoefficient, s] using
    randomizedSlopeOn_insert_sub p hi hj w k

theorem randomizedTail_split (p : Fin n → ℝ) {i j : Fin n}
    (hij : i ≠ j) (heq : p i = p j) (t w : ℝ) (k : ℕ) :
    randomizedTail (Function.update (Function.update p i (p i + t)) j (p j - t)) w k -
      randomizedTail p w k = -randomizedMixedCoefficient p w k i j * t ^ 2 := by
  let s := (univ.erase i).erase j
  have hi : i ∉ s := by simp [s]
  have hj : j ∉ s := by simp [s]
  have hs : insert i (insert j s) = univ := by
    ext x
    by_cases hxi : x = i <;> by_cases hxj : x = j <;> simp_all [s]
  have hbase : Function.update (Function.update p i (p i)) j (p i) = p := by
    rw [Function.update_eq_self, heq, Function.update_eq_self]
  have hsplit := randomizedTailOn_split p hi hj hij (p i) t w k
  rw [hs, hbase] at hsplit
  simpa only [heq, randomizedTail, randomizedMixedCoefficient, s] using hsplit

end

end PoissonBinomialComparison

-- Switch
namespace PoissonBinomialComparison

def IsSwitch (n j : ℕ) (γ a b : ℝ) : Prop :=
  0 < b ∧ b < a ∧ a < 1 ∧ a - b = γ ∧
    a ^ j * (1 - a) ^ (n - j) = b ^ j * (1 - b) ^ (n - j)

private theorem switch_ratio_strictAntiOn {n j : ℕ} {γ : ℝ}
    (hj : 0 < j) (hjn : j < n) (hγ : 0 < γ) :
    StrictAntiOn
      (fun b : ℝ ↦ ((b + γ) / b) ^ j * ((1 - (b + γ)) / (1 - b)) ^ (n - j))
      (Set.Ioo 0 (1 - γ)) := by
  intro b₁ hb₁ b₂ hb₂ hlt
  have hb₁' : 0 < 1 - b₁ := by linarith [hb₁.2]
  have hb₂' : 0 < 1 - b₂ := by linarith [hb₂.2]
  have hr₁ : (b₂ + γ) / b₂ < (b₁ + γ) / b₁ := by
    apply (div_lt_div_iff₀ hb₂.1 hb₁.1).2
    nlinarith
  have hr₂ : (1 - (b₂ + γ)) / (1 - b₂) <
      (1 - (b₁ + γ)) / (1 - b₁) := by
    apply (div_lt_div_iff₀ hb₂' hb₁').2
    nlinarith
  have hp₁ : 0 < (b₂ + γ) / b₂ := div_pos (by linarith [hb₂.1]) hb₂.1
  have hp₂ : 0 < (1 - (b₁ + γ)) / (1 - b₁) :=
    div_pos (by linarith [hb₁.2]) hb₁'
  have hp₂' : 0 < (1 - (b₂ + γ)) / (1 - b₂) :=
    div_pos (by linarith [hb₂.2]) hb₂'
  exact mul_lt_mul_of_pos
    (pow_lt_pow_left₀ hr₁ hp₁.le (by omega))
    (pow_lt_pow_left₀ hr₂ hp₂'.le (by omega))
    (pow_pos hp₁ _) (pow_pos hp₂ _)

private theorem switch_ratio_eq_one {n j : ℕ} {γ a b : ℝ}
    (h : IsSwitch n j γ a b) :
    ((b + γ) / b) ^ j * ((1 - (b + γ)) / (1 - b)) ^ (n - j) = 1 := by
  have ha : b + γ = a := by linarith [h.2.2.2.1]
  have hb : 0 < 1 - b := by linarith [h.2.1, h.2.2.1]
  rw [ha, div_pow, div_pow, div_mul_div_comm, h.2.2.2.2]
  exact div_self (ne_of_gt (mul_pos (pow_pos h.1 _) (pow_pos hb _)))

theorem exists_switch {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    ∃ a b : ℝ, IsSwitch n j γ a b := by
  let H : ℝ → ℝ := fun b ↦
    (b + γ) ^ j * (1 - (b + γ)) ^ (n - j) - b ^ j * (1 - b) ^ (n - j)
  have hj0 : j ≠ 0 := by omega
  have hnj0 : n - j ≠ 0 := by omega
  have H0 : 0 < H 0 := by
    simp only [H, zero_add, zero_pow hj0, zero_mul, sub_zero]
    exact mul_pos (pow_pos hγ0 _) (pow_pos (by linarith) _)
  have H1 : H (1 - γ) < 0 := by
    have heq : 1 - γ + γ = 1 := by ring
    simp only [H, heq, sub_self, zero_pow hnj0, mul_zero, zero_sub]
    exact neg_neg_of_pos (mul_pos (pow_pos (by linarith) _) (pow_pos (by linarith) _))
  have hcont : ContinuousOn H (Set.Icc 0 (1 - γ)) := by
    dsimp [H]
    fun_prop
  obtain ⟨b, hb, heq⟩ :=
    intermediate_value_Icc' (by linarith : 0 ≤ 1 - γ) hcont ⟨H1.le, H0.le⟩
  have hb0 : 0 < b := by
    apply lt_of_le_of_ne hb.1
    intro he
    subst b
    linarith
  have hb1 : b < 1 - γ := by
    apply lt_of_le_of_ne hb.2
    intro he
    rw [he] at heq
    linarith
  refine ⟨b + γ, b, hb0, by linarith, by linarith, by ring, ?_⟩
  exact sub_eq_zero.mp heq

theorem switch_unique {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ a₁ b₁ a₂ b₂ : ℝ} (hγ : 0 < γ)
    (h₁ : IsSwitch n j γ a₁ b₁) (h₂ : IsSwitch n j γ a₂ b₂) :
    a₁ = a₂ ∧ b₁ = b₂ := by
  have hb₁ : b₁ ∈ Set.Ioo 0 (1 - γ) :=
    ⟨h₁.1, by linarith [h₁.2.2.1, h₁.2.2.2.1]⟩
  have hb₂ : b₂ ∈ Set.Ioo 0 (1 - γ) :=
    ⟨h₂.1, by linarith [h₂.2.2.1, h₂.2.2.2.1]⟩
  have heq : b₁ = b₂ := (switch_ratio_strictAntiOn hj hjn hγ).injOn hb₁ hb₂
    ((switch_ratio_eq_one h₁).trans (switch_ratio_eq_one h₂).symm)
  exact ⟨by linarith [h₁.2.2.2.1, h₂.2.2.2.1], heq⟩

theorem existsUnique_switch {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    ∃! ab : ℝ × ℝ, IsSwitch n j γ ab.1 ab.2 := by
  obtain ⟨a, b, h⟩ := exists_switch hj hjn hγ0 hγ1
  refine ⟨(a, b), h, ?_⟩
  intro ab hab
  exact Prod.ext (switch_unique hj hjn hγ0 hab h).1 (switch_unique hj hjn hγ0 hab h).2

end PoissonBinomialComparison

-- Homogeneous
namespace PoissonBinomialComparison

open scoped BigOperators
open Finset

variable {ι : Type*} [DecidableEq ι]

theorem bernoulliWeight_const (t : ℝ) {s A : Finset ι} (hA : A ⊆ s) :
    bernoulliWeight (fun _ ↦ t) s A = t ^ A.card * (1 - t) ^ (s.card - A.card) := by
  simp [bernoulliWeight, card_sdiff_of_subset hA]

theorem pbMassOn_const (t : ℝ) (s : Finset ι) (k : ℕ) :
    pbMassOn (fun _ ↦ t) s k =
      (s.card.choose k : ℝ) * t ^ k * (1 - t) ^ (s.card - k) := by
  unfold pbMassOn
  calc
    _ = ∑ _A ∈ s.powersetCard k, t ^ k * (1 - t) ^ (s.card - k) := by
      apply sum_congr rfl
      intro A hA
      rw [bernoulliWeight_const t (mem_powersetCard.mp hA).1,
        (mem_powersetCard.mp hA).2]
    _ = _ := by simp [card_powersetCard, mul_assoc]

theorem pbMass_const (n k : ℕ) (t : ℝ) :
    pbMass (fun _ : Fin n ↦ t) k =
      (n.choose k : ℝ) * t ^ k * (1 - t) ^ (n - k) := by
  simpa [pbMass] using pbMassOn_const t (univ : Finset (Fin n)) k

theorem pbTailOn_const (t : ℝ) (s : Finset ι) (k : ℕ) :
    pbTailOn (fun _ ↦ t) s k =
      ∑ j ∈ Icc k s.card, (s.card.choose j : ℝ) * t ^ j * (1 - t) ^ (s.card - j) := by
  simp only [pbTailOn_eq_sum_mass, pbMassOn_const]

theorem pbTail_const (n k : ℕ) (t : ℝ) :
    pbTail (fun _ : Fin n ↦ t) k =
      ∑ j ∈ Icc k n, (n.choose j : ℝ) * t ^ j * (1 - t) ^ (n - j) := by
  simp only [pbTail_eq_sum_mass, pbMass_const]

theorem meanGap_const (n : ℕ) (a b : ℝ) :
    meanGap (fun _ : Fin n ↦ a) (fun _ : Fin n ↦ b) = n * (a - b) := by
  simp [meanGap, mul_sub]

theorem pbMass_const_eq_iff {n j : ℕ} (hj : j ≤ n) (a b : ℝ) :
    pbMass (fun _ : Fin n ↦ a) j = pbMass (fun _ : Fin n ↦ b) j ↔
      a ^ j * (1 - a) ^ (n - j) = b ^ j * (1 - b) ^ (n - j) := by
  have hchoose : (n.choose j : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hj).ne'
  simp only [pbMass_const, mul_assoc]
  exact ⟨mul_left_cancel₀ hchoose, congrArg ((n.choose j : ℝ) * ·)⟩

theorem IsSwitch.pbMass_eq {n j : ℕ} {γ a b : ℝ} (h : IsSwitch n j γ a b) :
    pbMass (fun _ : Fin n ↦ a) j = pbMass (fun _ : Fin n ↦ b) j := by
  simp only [pbMass_const, mul_assoc, h.2.2.2.2]

end PoissonBinomialComparison

-- Compactness
namespace PoissonBinomialComparison

open scoped BigOperators
open Finset

noncomputable section

variable {ι : Type*} [DecidableEq ι]

theorem continuous_bernoulliWeight (s A : Finset ι) :
    Continuous (fun p : ι → ℝ ↦ bernoulliWeight p s A) := by
  unfold bernoulliWeight
  fun_prop

theorem continuous_pbMassOn (s : Finset ι) (k : ℕ) :
    Continuous (fun p : ι → ℝ ↦ pbMassOn p s k) := by
  unfold pbMassOn
  exact continuous_finsetSum _ (fun A _ ↦ continuous_bernoulliWeight s A)

theorem continuous_pbTailOn (s : Finset ι) (k : ℕ) :
    Continuous (fun p : ι → ℝ ↦ pbTailOn p s k) := by
  unfold pbTailOn
  apply continuous_finsetSum
  intro A _
  split_ifs
  · exact continuous_bernoulliWeight s A
  · exact continuous_const

variable {n : ℕ}

theorem continuous_pbMass (k : ℕ) :
    Continuous (fun p : Fin n → ℝ ↦ pbMass p k) := continuous_pbMassOn univ k

theorem continuous_pbTail (k : ℕ) :
    Continuous (fun p : Fin n → ℝ ↦ pbTail p k) := continuous_pbTailOn univ k

theorem continuous_meanGap :
    Continuous (fun x : (Fin n → ℝ) × (Fin n → ℝ) ↦ meanGap x.1 x.2) := by
  unfold meanGap
  fun_prop

theorem continuous_tailDiff (k : ℕ) :
    Continuous (fun x : (Fin n → ℝ) × (Fin n → ℝ) ↦ tailDiff x.1 x.2 k) := by
  exact ((continuous_pbTail k).comp continuous_fst).sub ((continuous_pbTail k).comp continuous_snd)

theorem continuous_tailObjective :
    Continuous (fun x : (Fin n → ℝ) × (Fin n → ℝ) ↦ tailObjective x.1 x.2) := by
  by_cases hn : 0 < n
  · simp only [tailObjective, dif_pos hn]
    exact Continuous.finset_sup'_apply _ (fun k _ ↦ continuous_tailDiff k)
  · simp only [tailObjective, dif_neg hn]
    exact continuous_const

def feasiblePairs (n : ℕ) (Δ : ℝ) : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
  {x | AdmissiblePair x.1 x.2 ∧ meanGap x.1 x.2 = Δ}

theorem isClosed_admissiblePairs :
    IsClosed {x : (Fin n → ℝ) × (Fin n → ℝ) | AdmissiblePair x.1 x.2} := by
  have hc : ∀ i : Fin n, IsClosed {x : (Fin n → ℝ) × (Fin n → ℝ) |
      0 ≤ x.2 i ∧ x.2 i ≤ x.1 i ∧ x.1 i ≤ 1} := by
    intro i
    have hp : Continuous (fun x : (Fin n → ℝ) × (Fin n → ℝ) ↦ x.1 i) := by fun_prop
    have hq : Continuous (fun x : (Fin n → ℝ) × (Fin n → ℝ) ↦ x.2 i) := by fun_prop
    exact (isClosed_le continuous_const hq).inter
      ((isClosed_le hq hp).inter (isClosed_le hp continuous_const))
  convert! isClosed_iInter hc using 1
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_iInter]
  exact admissiblePair_iff x.1 x.2

theorem isClosed_feasiblePairs (Δ : ℝ) : IsClosed (feasiblePairs n Δ) :=
  isClosed_admissiblePairs.inter (isClosed_eq continuous_meanGap continuous_const)

theorem isCompact_feasiblePairs (Δ : ℝ) : IsCompact (feasiblePairs n Δ) := by
  apply (isCompact_Icc : IsCompact (Set.Icc
    ((0 : Fin n → ℝ), (0 : Fin n → ℝ)) (1, 1))).of_isClosed_subset
      (isClosed_feasiblePairs Δ)
  intro x hx
  exact ⟨⟨fun i ↦ (hx.1.1 i).1, fun i ↦ (hx.1.2.1 i).1⟩,
    ⟨fun i ↦ (hx.1.1 i).2, fun i ↦ (hx.1.2.1 i).2⟩⟩

theorem exists_tailObjective_minimizer_of_nonempty (Δ : ℝ)
    (hne : (feasiblePairs n Δ).Nonempty) :
    ∃ p q : Fin n → ℝ, AdmissiblePair p q ∧ meanGap p q = Δ ∧
      ∀ p' q' : Fin n → ℝ, AdmissiblePair p' q' → meanGap p' q' = Δ →
        tailObjective p q ≤ tailObjective p' q' := by
  obtain ⟨x, hx, hmin⟩ := (isCompact_feasiblePairs (n := n) Δ).exists_isMinOn
    (f := fun x : (Fin n → ℝ) × (Fin n → ℝ) ↦ tailObjective x.1 x.2)
    hne (continuous_tailObjective (n := n)).continuousOn
  refine ⟨x.1, x.2, hx.1, hx.2, ?_⟩
  intro p q hp hgap
  exact (isMinOn_iff.mp hmin) (p, q) ⟨hp, hgap⟩

theorem feasiblePairs_nonempty (Δ : ℝ) (h0 : 0 ≤ Δ) (hn : Δ ≤ n) :
    (feasiblePairs n Δ).Nonempty := by
  by_cases hnp : 0 < n
  · have hnr : (0 : ℝ) < n := by exact_mod_cast hnp
    refine ⟨((fun _ ↦ Δ / n), (fun _ ↦ 0)), ?_, ?_⟩
    · rw [admissiblePair_iff]
      intro i
      exact ⟨le_rfl, div_nonneg h0 hnr.le, (div_le_one hnr).mpr hn⟩
    · rw [meanGap_const]
      rw [sub_zero, mul_div_cancel₀ _ hnr.ne']
  · have hn0 : n = 0 := by omega
    have hΔ : Δ = 0 := by simp [hn0] at hn; linarith
    refine ⟨((fun _ ↦ 0), (fun _ ↦ 0)), ?_, ?_⟩
    · rw [admissiblePair_iff]
      intro i
      norm_num
    · simp [meanGap, hΔ]

theorem exists_tailObjective_minimizer (Δ : ℝ) (h0 : 0 ≤ Δ) (hn : Δ ≤ n) :
    ∃ p q : Fin n → ℝ, AdmissiblePair p q ∧ meanGap p q = Δ ∧
      ∀ p' q' : Fin n → ℝ, AdmissiblePair p' q' → meanGap p' q' = Δ →
        tailObjective p q ≤ tailObjective p' q' :=
  exists_tailObjective_minimizer_of_nonempty Δ (feasiblePairs_nonempty Δ h0 hn)

end

end PoissonBinomialComparison

-- ParameterDerivative
namespace PoissonBinomialComparison

open scoped BigOperators
open Finset

noncomputable section

variable {n : ℕ}

private theorem differentiable_product {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → (Fin n → ℝ) → ℝ) (h : ∀ i ∈ s, Differentiable ℝ (f i)) :
    Differentiable ℝ (fun p ↦ ∏ i ∈ s, f i p) := by
  intro p
  exact (HasFDerivAt.finsetProd (fun i hi ↦ (h i hi p).hasFDerivAt)).differentiableAt

theorem differentiable_bernoulliWeight (s A : Finset (Fin n)) :
    Differentiable ℝ (fun p ↦ bernoulliWeight p s A) := by
  exact (differentiable_product A (fun i p ↦ p i) (by intros; fun_prop)).mul
    (differentiable_product (s \ A) (fun i p ↦ 1-p i) (by intros; fun_prop))

theorem differentiable_pbMass (k : ℕ) :
    Differentiable ℝ (fun p : Fin n → ℝ ↦ pbMass p k) := by
  unfold pbMass pbMassOn
  apply Differentiable.fun_sum
  intro A _
  exact differentiable_bernoulliWeight univ A

theorem differentiable_pbTail (k : ℕ) :
    Differentiable ℝ (fun p : Fin n → ℝ ↦ pbTail p k) := by
  unfold pbTail pbTailOn
  apply Differentiable.fun_sum
  intro A _
  split_ifs
  · exact differentiable_bernoulliWeight univ A
  · exact differentiable_const _

theorem differentiable_randomizedTail (w : ℝ) (k : ℕ) :
    Differentiable ℝ (fun p : Fin n → ℝ ↦ randomizedTail p w k) := by
  change Differentiable ℝ (fun p : Fin n → ℝ ↦ w * pbTail p k + (1-w)*pbTail p (k+1))
  exact ((differentiable_pbTail k).const_mul w).add ((differentiable_pbTail (k+1)).const_mul (1-w))

theorem hasDerivAt_randomizedTail_update (p : Fin n → ℝ) (i : Fin n)
    (w : ℝ) (k : ℕ) (x : ℝ) :
    HasDerivAt (fun t ↦ randomizedTail (Function.update p i t) w k)
      (randomizedGradient p w k i) x := by
  have heq : (fun t ↦ randomizedTail (Function.update p i t) w k) =
      (fun t ↦ randomizedTail p w k + (t-p i)*randomizedGradient p w k i) := by
    funext t
    have h := randomizedTail_update_sub p i (p i) t w k
    rw [Function.update_eq_self] at h
    linarith
  rw [heq]
  convert! ((hasDerivAt_id x).sub_const (p i)).mul_const
    (randomizedGradient p w k i) |>.const_add (randomizedTail p w k) using 1; first | rfl | simp

theorem fderiv_randomizedTail_single (p : Fin n → ℝ) (i : Fin n) (w : ℝ) (k : ℕ) :
    fderiv ℝ (fun q ↦ randomizedTail q w k) p (Pi.single i 1) =
      randomizedGradient p w k i := by
  have h := ((differentiable_randomizedTail (n := n) w k) p).hasFDerivAt
  have hc := h.comp_hasDerivAt_of_eq (p i) (hasDerivAt_update p i (p i))
    (Function.update_eq_self i p).symm
  exact hc.unique (hasDerivAt_randomizedTail_update p i w k (p i))

theorem fderiv_randomizedTail_apply (p v : Fin n → ℝ) (w : ℝ) (k : ℕ) :
    fderiv ℝ (fun q ↦ randomizedTail q w k) p v =
      ∑ i, v i * randomizedGradient p w k i := by
  conv_lhs => rw [pi_eq_sum_univ' v]
  simp only [map_sum, map_smul, smul_eq_mul, fderiv_randomizedTail_single]

theorem hasDerivAt_randomizedTail_curve {p : ℝ → Fin n → ℝ} {v : Fin n → ℝ}
    {t : ℝ} (hp : HasDerivAt p v t) (w : ℝ) (k : ℕ) :
    HasDerivAt (fun x ↦ randomizedTail (p x) w k)
      (∑ i, v i * randomizedGradient (p t) w k i) t := by
  simpa only [Function.comp_def, fderiv_randomizedTail_apply] using
    (((differentiable_randomizedTail (n := n) w k) (p t)).hasFDerivAt.comp_hasDerivAt t hp)

theorem hasDerivAt_randomizedDiff_curve {p q : ℝ → Fin n → ℝ}
    {u v : Fin n → ℝ} {t : ℝ} (hp : HasDerivAt p u t) (hq : HasDerivAt q v t)
    (w : ℝ) (k : ℕ) :
    HasDerivAt (fun x ↦ randomizedTail (p x) w k - randomizedTail (q x) w k)
      (∑ i, (u i * randomizedGradient (p t) w k i -
        v i * randomizedGradient (q t) w k i)) t := by
  convert! (hasDerivAt_randomizedTail_curve hp w k).sub
    (hasDerivAt_randomizedTail_curve hq w k) using 1
  simp [sum_sub_distrib]

theorem differentiable_tailDiff (k : ℕ) :
    Differentiable ℝ (fun x : (Fin n → ℝ) × (Fin n → ℝ) ↦ tailDiff x.1 x.2 k) := by
  exact ((differentiable_pbTail k).comp differentiable_fst).sub ((differentiable_pbTail k).comp differentiable_snd)

theorem randomizedDiff_eq (p q : Fin n → ℝ) (w : ℝ) (k : ℕ) :
    randomizedTail p w k - randomizedTail q w k =
      w*tailDiff p q k + (1-w)*tailDiff p q (k+1) := by
  unfold randomizedTail randomizedTailOn tailDiff pbTail
  ring

theorem weighted_fderiv_tailDiff_apply (p q u v : Fin n → ℝ) (w : ℝ) (k : ℕ) :
    w * fderiv ℝ (fun x : (Fin n → ℝ) × (Fin n → ℝ) ↦ tailDiff x.1 x.2 k) (p,q) (u,v) +
      (1-w) * fderiv ℝ (fun x : (Fin n → ℝ) × (Fin n → ℝ) ↦ tailDiff x.1 x.2 (k+1)) (p,q) (u,v) =
      ∑ i, (u i * randomizedGradient p w k i - v i * randomizedGradient q w k i) := by
  have hp : HasDerivAt (fun t : ℝ ↦ p+t • u) u 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add p
  have hq : HasDerivAt (fun t : ℝ ↦ q+t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add q
  have hpath := hp.prodMk hq
  have hk := ((differentiable_tailDiff (n := n) k) (p,q)).hasFDerivAt.comp_hasDerivAt_of_eq 0 hpath (by simp)
  have hk1 := ((differentiable_tailDiff (n := n) (k+1)) (p,q)).hasFDerivAt.comp_hasDerivAt_of_eq 0 hpath (by simp)
  have hcomb := (hk.const_mul w).add (hk1.const_mul (1-w))
  have hrand := hasDerivAt_randomizedDiff_curve hp hq w k
  have heq : (fun t : ℝ ↦ w*tailDiff (p+t • u) (q+t • v) k +
      (1-w)*tailDiff (p+t • u) (q+t • v) (k+1)) =
      (fun t ↦ randomizedTail (p+t • u) w k-randomizedTail (q+t • v) w k) := by
    funext t
    exact (randomizedDiff_eq _ _ w k).symm
  change HasDerivAt (fun t : ℝ ↦ w*tailDiff (p+t • u) (q+t • v) k +
    (1-w)*tailDiff (p+t • u) (q+t • v) (k+1)) _ 0 at hcomb
  rw [heq] at hcomb
  simpa using hcomb.unique hrand

end

end PoissonBinomialComparison

-- FeasibleDirections
namespace PoissonBinomialComparison

open scoped BigOperators Topology
open Finset Filter

def feasibleDirections {n : ℕ} (p q : Fin n → ℝ) :
    Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
  {d | (∑ i, (d.1 i-d.2 i)) = 0 ∧ ∀ i,
    (p i = 1 → d.1 i ≤ 0) ∧ (q i = 0 → 0 ≤ d.2 i) ∧
      (p i = q i → d.2 i ≤ d.1 i)}

theorem zero_mem_feasibleDirections {n : ℕ} (p q : Fin n → ℝ) :
    0 ∈ feasibleDirections p q := by
  simp [feasibleDirections]

theorem convex_feasibleDirections {n : ℕ} (p q : Fin n → ℝ) :
    Convex ℝ (feasibleDirections p q) := by
  intro x hx y hy a b ha hb _
  constructor
  · change ∑ i, (a*x.1 i+b*y.1 i-(a*x.2 i+b*y.2 i)) = 0
    simp_rw [show ∀ i, a*x.1 i+b*y.1 i-(a*x.2 i+b*y.2 i) =
      a*(x.1 i-x.2 i)+b*(y.1 i-y.2 i) by intro i; ring]
    rw [sum_add_distrib, ← mul_sum, ← mul_sum, hx.1, hy.1]
    ring
  · intro i
    change (p i = 1 → a*x.1 i+b*y.1 i ≤ 0) ∧
      (q i = 0 → 0 ≤ a*x.2 i+b*y.2 i) ∧
      (p i = q i → a*x.2 i+b*y.2 i ≤ a*x.1 i+b*y.1 i)
    exact ⟨fun h ↦ add_nonpos (mul_nonpos_of_nonneg_of_nonpos ha ((hx.2 i).1 h))
      (mul_nonpos_of_nonneg_of_nonpos hb ((hy.2 i).1 h)),
      fun h ↦ add_nonneg (mul_nonneg ha ((hx.2 i).2.1 h))
        (mul_nonneg hb ((hy.2 i).2.1 h)),
      fun h ↦ add_le_add (mul_le_mul_of_nonneg_left ((hx.2 i).2.2 h) ha)
        (mul_le_mul_of_nonneg_left ((hy.2 i).2.2 h) hb)⟩

theorem eventually_nonneg_affine {a b : ℝ} (ha : 0 ≤ a) (hb : a = 0 → 0 ≤ b) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 ≤ a+t*b := by
  rcases ha.eq_or_lt with h | h
  · have ha0 : a = 0 := h.symm
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact by simpa [ha0] using mul_nonneg (le_of_lt ht) (hb ha0)
  · have hc : ContinuousAt (fun t : ℝ ↦ a+t*b) 0 := by fun_prop
    have he := hc.eventually (eventually_gt_nhds (by simpa using h))
    have he' : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < a+t*b := he.filter_mono nhdsWithin_le_nhds
    exact he'.mono (fun _ ht ↦ ht.le)

theorem eventually_admissible_of_feasibleDirection {n : ℕ} {p q : Fin n → ℝ}
    (h : AdmissiblePair p q) {d : (Fin n → ℝ) × (Fin n → ℝ)}
    (hd : d ∈ feasibleDirections p q) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), AdmissiblePair (p+t • d.1) (q+t • d.2) := by
  have hpq := (admissiblePair_iff p q).mp h
  have he : ∀ i, ∀ᶠ t in 𝓝[>] (0 : ℝ),
      0 ≤ q i+t*d.2 i ∧ q i+t*d.2 i ≤ p i+t*d.1 i ∧ p i+t*d.1 i ≤ 1 := by
    intro i
    have hq := eventually_nonneg_affine (hpq i).1 ((hd.2 i).2.1)
    have hp := eventually_nonneg_affine (sub_nonneg.mpr (hpq i).2.2)
      (b := -d.1 i) (fun hh ↦ neg_nonneg.mpr ((hd.2 i).1 (by linarith)))
    have hg := eventually_nonneg_affine (sub_nonneg.mpr (hpq i).2.1)
      (b := d.1 i-d.2 i) (fun hh ↦ sub_nonneg.mpr ((hd.2 i).2.2 (by linarith)))
    filter_upwards [hq,hp,hg] with t htq htp htg
    exact ⟨htq, by nlinarith, by nlinarith⟩
  have hall := (eventually_all.mpr he)
  filter_upwards [hall] with t ht
  rw [admissiblePair_iff]
  exact ht

theorem meanGap_add_feasibleDirection {n : ℕ} {p q : Fin n → ℝ}
    {d : (Fin n → ℝ) × (Fin n → ℝ)} (hd : d ∈ feasibleDirections p q) (t : ℝ) :
    meanGap (p+t • d.1) (q+t • d.2) = meanGap p q := by
  simp only [meanGap_eq_sum, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [show ∀ i, p i+t*d.1 i-(q i+t*d.2 i) =
    (p i-q i)+t*(d.1 i-d.2 i) by intro i; ring]
  rw [sum_add_distrib, ← mul_sum, hd.1, mul_zero, add_zero]

theorem eventually_mem_feasiblePairs_of_direction {n : ℕ} {p q : Fin n → ℝ}
    (h : AdmissiblePair p q) {d : (Fin n → ℝ) × (Fin n → ℝ)}
    (hd : d ∈ feasibleDirections p q) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), (p,q)+t • d ∈ feasiblePairs n (meanGap p q) := by
  filter_upwards [eventually_admissible_of_feasibleDirection h hd] with t ht
  exact ⟨ht, meanGap_add_feasibleDirection hd t⟩

end PoissonBinomialComparison

-- ConvexStationarity
namespace PoissonBinomialComparison

open Set Filter
open scoped Topology

theorem exists_weight_of_no_simultaneous_descent {C : Set (ℝ × ℝ)}
    (hC : Convex ℝ C) (hzero : (0, 0) ∈ C)
    (hdesc : ∀ x ∈ C, 0 ≤ max x.1 x.2) :
    ∃ w : ℝ, 0 ≤ w ∧ w ≤ 1 ∧ ∀ x ∈ C, 0 ≤ w*x.1 + (1-w)*x.2 := by
  let S : Set (ℝ × ℝ) := Iic 0 ×ˢ Iic 0
  have hS : Convex ℝ S := (convex_Iic (0 : ℝ)).prod (convex_Iic (0 : ℝ))
  have hint : interior S = Iio 0 ×ˢ Iio 0 := by
    dsimp only [S]
    rw [interior_prod_eq, interior_Iic]
  have hdisj : Disjoint (interior S) C := by
    rw [Set.disjoint_left]
    intro x hx hxC
    rw [hint] at hx
    exact (max_lt hx.1 hx.2).not_ge (hdesc x hxC)
  have hne : (interior S).Nonempty := by
    rw [hint]
    exact ⟨(-1,-1), by norm_num⟩
  obtain ⟨f, r, hf, hneg, hpos⟩ := geometric_hahn_banach_of_nonempty_interior
    hS hC hdisj hne ⟨(0,0),hzero⟩
  have hr : r = 0 := by
    have ha := hneg (0,0) (by simp [S])
    have hb := hpos (0,0) hzero
    simp only [← Prod.zero_eq_mk, map_zero] at ha hb
    exact le_antisymm hb ha
  subst r
  have hform (x : ℝ × ℝ) : f x = x.1*f (1,0) + x.2*f (0,1) := by
    have hx : x = x.1 • (1,0) + x.2 • (0,1) := by ext <;> simp
    calc
      f x = f (x.1 • (1,0) + x.2 • (0,1)) := congrArg f hx
      _ = _ := by rw [map_add, map_smul, map_smul]; rfl
  have hA : 0 ≤ f (1,0) := by
    have h := hneg (-1,0) (by simp [S])
    rw [hform] at h
    linarith
  have hB : 0 ≤ f (0,1) := by
    have h := hneg (0,-1) (by simp [S])
    rw [hform] at h
    linarith
  have hsum : 0 < f (1,0) + f (0,1) := by
    by_contra h
    have ha : f (1,0) = 0 := by linarith
    have hb : f (0,1) = 0 := by linarith
    apply hf
    apply ContinuousLinearMap.ext
    intro x
    simp [hform x, ha, hb]
  refine ⟨f (1,0) / (f (1,0) + f (0,1)), div_nonneg hA hsum.le,
    (div_le_one hsum).mpr (by linarith), ?_⟩
  intro x hx
  have h := hpos x hx
  rw [hform] at h
  have heq : f (1,0) / (f (1,0)+f (0,1))*x.1 +
      (1-f (1,0)/(f (1,0)+f (0,1)))*x.2 =
      (x.1*f (1,0)+x.2*f (0,1))/(f (1,0)+f (0,1)) := by
    field_simp
    ring
  rw [heq]
  exact div_nonneg h hsum.le

theorem eventually_lt_of_hasDerivAt_neg {f : ℝ → ℝ} {x d : ℝ}
    (hf : HasDerivAt f d x) (hd : d < 0) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), f (x+t) < f x := by
  have h := hf.tendsto_slope_zero_right.eventually (eventually_lt_nhds hd)
  filter_upwards [h, self_mem_nhdsWithin] with t ht ht0
  change 0 < t at ht0
  simp only [smul_eq_mul] at ht
  have hsub : f (x+t)-f x < 0 := neg_of_mul_neg_right ht (inv_nonneg.mpr ht0.le)
  linarith

theorem max_derivatives_nonneg_of_eventually_le {f g : ℝ → ℝ} {a b : ℝ}
    (hf : HasDerivAt f a 0) (hg : HasDerivAt g b 0)
    (hmin : ∀ᶠ t in 𝓝[>] (0 : ℝ), max (f 0) (g 0) ≤ max (f t) (g t)) :
    0 ≤ max a b := by
  by_contra h
  have hab := max_lt_iff.mp (lt_of_not_ge h)
  have hF := eventually_lt_of_hasDerivAt_neg hf hab.1
  have hG := eventually_lt_of_hasDerivAt_neg hg hab.2
  obtain ⟨t, ht, hft, hgt⟩ := (hmin.and (hF.and hG)).exists
  simp only [zero_add] at hft hgt
  exact (max_lt (hft.trans_le (le_max_left _ _))
    (hgt.trans_le (le_max_right _ _))).not_ge ht

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_supporting_gradient {V : Set E} (hV : Convex ℝ V) (hzero : 0 ∈ V)
    (f g : E →L[ℝ] ℝ) (hdesc : ∀ v ∈ V, 0 ≤ max (f v) (g v)) :
    ∃ w : ℝ, 0 ≤ w ∧ w ≤ 1 ∧ ∀ v ∈ V, 0 ≤ w*f v + (1-w)*g v := by
  let L := f.prod g
  have hC : Convex ℝ (L '' V) := hV.linear_image L.toLinearMap
  have hz : (0,0) ∈ L '' V := ⟨0, hzero, by simp [L]⟩
  obtain ⟨w, hw0, hw1, hw⟩ := exists_weight_of_no_simultaneous_descent hC hz (by
    rintro x ⟨v,hv,rfl⟩
    exact hdesc v hv)
  exact ⟨w, hw0, hw1, fun v hv ↦ hw (L v) ⟨v,hv,rfl⟩⟩

theorem max_directionalDerivatives_nonneg {f g : E → ℝ} {x v : E}
    {f' g' : E →L[ℝ] ℝ} {S : Set E}
    (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x)
    (hmin : IsLocalMinOn (fun y ↦ max (f y) (g y)) S x)
    (hv : ∀ᶠ t in 𝓝[>] (0 : ℝ), x + t • v ∈ S) :
    0 ≤ max (f' v) (g' v) := by
  have hpath : HasDerivAt (fun t : ℝ ↦ x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hF := hf.comp_hasDerivAt_of_eq 0 hpath (by simp)
  have hG := hg.comp_hasDerivAt_of_eq 0 hpath (by simp)
  apply max_derivatives_nonneg_of_eventually_le hF hG
  have ht : Tendsto (fun t : ℝ ↦ x+t • v) (𝓝[>] 0) (𝓝[S] x) :=
    tendsto_nhdsWithin_iff.mpr ⟨by simpa using (hpath.continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds), hv⟩
  simpa using ht.eventually hmin

theorem exists_supporting_gradient_of_localMinOn {f g : E → ℝ} {x : E}
    {f' g' : E →L[ℝ] ℝ} {S V : Set E}
    (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x)
    (hmin : IsLocalMinOn (fun y ↦ max (f y) (g y)) S x)
    (hV : Convex ℝ V) (hzero : 0 ∈ V)
    (hfeas : ∀ v ∈ V, ∀ᶠ t in 𝓝[>] (0 : ℝ), x+t • v ∈ S) :
    ∃ w : ℝ, 0 ≤ w ∧ w ≤ 1 ∧ ∀ v ∈ V, 0 ≤ w*f' v + (1-w)*g' v :=
  exists_supporting_gradient hV hzero f' g'
    (fun v hv ↦ max_directionalDerivatives_nonneg hf hg hmin (hfeas v hv))

end PoissonBinomialComparison

-- TailStationarity
namespace PoissonBinomialComparison

open scoped BigOperators Topology
open Finset Filter

noncomputable section

variable {n : ℕ} {p q : Fin n → ℝ}

theorem tailObjective_eventually_eq_max {k l : ℕ} (hk : k ∈ activeThresholds p q)
    (hl : l ∈ Icc 1 n) (hactive : activeThresholds p q ⊆ {k,l}) :
    (fun x : (Fin n → ℝ) × (Fin n → ℝ) ↦ tailObjective x.1 x.2) =ᶠ[𝓝 (p,q)]
      (fun x ↦ max (tailDiff x.1 x.2 k) (tailDiff x.1 x.2 l)) := by
  have hk' := (mem_activeThresholds p q k).mp hk
  have hn : 0 < n := by omega
  have he : ∀ h ∈ Icc 1 n, ∀ᶠ x : (Fin n → ℝ) × (Fin n → ℝ) in 𝓝 (p,q),
      tailDiff x.1 x.2 h ≤ max (tailDiff x.1 x.2 k) (tailDiff x.1 x.2 l) := by
    intro h hh
    by_cases hhk : h = k
    · subst h
      exact Eventually.of_forall (fun _ ↦ le_max_left _ _)
    by_cases hhl : h = l
    · subst h
      exact Eventually.of_forall (fun _ ↦ le_max_right _ _)
    have hlt : tailDiff p q h < tailDiff p q k := by
      have hle := tailDiff_le_tailObjective p q hh
      rw [← hk'.2.2] at hle
      apply lt_of_le_of_ne hle
      intro heq
      have hm : h ∈ activeThresholds p q := mem_filter.mpr ⟨hh, heq.trans hk'.2.2⟩
      have := hactive hm
      simp only [mem_insert, mem_singleton] at this
      exact this.elim hhk hhl
    exact ((continuous_tailDiff h).continuousAt.eventually_lt
      (continuous_tailDiff k).continuousAt hlt).mono
      (fun _ ht ↦ ht.le.trans (le_max_left _ _))
  have hall : ∀ᶠ x : (Fin n → ℝ) × (Fin n → ℝ) in 𝓝 (p,q),
      ∀ h ∈ Icc 1 n, tailDiff x.1 x.2 h ≤ max (tailDiff x.1 x.2 k) (tailDiff x.1 x.2 l) := by
    rw [eventually_all_finset]
    exact he
  filter_upwards [hall] with x hx
  apply le_antisymm
  · exact (tailObjective_le_iff x.1 x.2 hn _).mpr hx
  · exact max_le (tailDiff_le_tailObjective x.1 x.2 (mem_Icc.mpr ⟨hk'.1,hk'.2.1⟩))
      (tailDiff_le_tailObjective x.1 x.2 hl)

theorem exists_supporting_tail_gradients (h : AdmissiblePair p q)
    (hmin : IsLocalMinOn (fun x : (Fin n → ℝ) × (Fin n → ℝ) ↦ tailObjective x.1 x.2)
      (feasiblePairs n (meanGap p q)) (p,q))
    {k l : ℕ} (hk : k ∈ activeThresholds p q) (hl : l ∈ Icc 1 n)
    (hactive : activeThresholds p q ⊆ {k,l}) :
    ∃ w : ℝ, 0 ≤ w ∧ w ≤ 1 ∧ ∀ d ∈ feasibleDirections p q,
      0 ≤ w * fderiv ℝ (fun x : (Fin n → ℝ) × (Fin n → ℝ) ↦ tailDiff x.1 x.2 k) (p,q) d +
        (1-w) * fderiv ℝ (fun x : (Fin n → ℝ) × (Fin n → ℝ) ↦ tailDiff x.1 x.2 l) (p,q) d := by
  have heq := tailObjective_eventually_eq_max hk hl hactive
  have hm := hmin.congr (heq.filter_mono nhdsWithin_le_nhds) (show (p,q) ∈
    feasiblePairs n (meanGap p q) from ⟨h,rfl⟩)
  exact exists_supporting_gradient_of_localMinOn
    ((differentiable_tailDiff k) (p,q)).hasFDerivAt
    ((differentiable_tailDiff l) (p,q)).hasFDerivAt hm
    (convex_feasibleDirections p q) (zero_mem_feasibleDirections p q)
    (fun _ hd ↦ eventually_mem_feasiblePairs_of_direction h hd)

theorem exists_stationary_randomized_test_with_activeSet (h : AdmissiblePair p q)
    (hgap : 0 < meanGap p q) (hT : tailObjective p q < 1)
    (hmin : IsLocalMinOn (fun x : (Fin n → ℝ) × (Fin n → ℝ) ↦ tailObjective x.1 x.2)
      (feasiblePairs n (meanGap p q)) (p,q)) :
    ∃ k : ℕ, ∃ w : ℝ, 1 ≤ k ∧ k ≤ n ∧ 0 ≤ w ∧ w ≤ 1 ∧
      k ∈ activeThresholds p q ∧ (w = 1 ∨ k+1 ∈ activeThresholds p q) ∧
      randomizedTail p w k-randomizedTail q w k = tailObjective p q ∧
      ((activeThresholds p q = {k} ∧ w = 1) ∨ activeThresholds p q = {k,k+1}) ∧
      ∀ d ∈ feasibleDirections p q,
        0 ≤ ∑ i, (d.1 i*randomizedGradient p w k i-d.2 i*randomizedGradient q w k i) := by
  obtain ⟨k,hk0,hkn,hactive⟩ := activeThresholds_singleton_or_adjacent h hgap hT
  have hkr : k ∈ Icc 1 n := mem_Icc.mpr ⟨hk0,hkn⟩
  rcases hactive with hone | ⟨hk1,htwo⟩
  · have hk : k ∈ activeThresholds p q := by rw [hone]; simp
    have hsub : activeThresholds p q ⊆ {k,k} := by simp [hone]
    obtain ⟨w,_,_,hw⟩ := exists_supporting_tail_gradients h hmin hk hkr hsub
    refine ⟨k,1,hk0,hkn,by norm_num,le_rfl,hk,Or.inl rfl,?_,Or.inl ⟨hone,rfl⟩,?_⟩
    · simpa [randomizedDiff_eq] using (mem_activeThresholds p q k).mp hk |>.2.2
    · intro d hd
      have hv := hw d hd
      rw [← weighted_fderiv_tailDiff_apply p q d.1 d.2 1 k]
      simp only [one_mul, sub_self, zero_mul, add_zero]
      nlinarith
  · have hk : k ∈ activeThresholds p q := by rw [htwo]; simp
    have hl : k+1 ∈ activeThresholds p q := by rw [htwo]; simp
    obtain ⟨w,hw0,hw1,hw⟩ := exists_supporting_tail_gradients h hmin hk
      (mem_Icc.mpr ⟨by omega,hk1⟩) (by rw [htwo])
    refine ⟨k,w,hk0,hkn,hw0,hw1,hk,Or.inr hl,?_,Or.inr htwo,?_⟩
    · rw [randomizedDiff_eq, ((mem_activeThresholds p q k).mp hk).2.2,
        ((mem_activeThresholds p q (k+1)).mp hl).2.2]
      ring
    · intro d hd
      rw [← weighted_fderiv_tailDiff_apply p q d.1 d.2 w k]
      exact hw d hd

theorem exists_stationary_randomized_test (h : AdmissiblePair p q)
    (hgap : 0 < meanGap p q) (hT : tailObjective p q < 1)
    (hmin : IsLocalMinOn (fun x : (Fin n → ℝ) × (Fin n → ℝ) ↦ tailObjective x.1 x.2)
      (feasiblePairs n (meanGap p q)) (p,q)) :
    ∃ k : ℕ, ∃ w : ℝ, 1 ≤ k ∧ k ≤ n ∧ 0 ≤ w ∧ w ≤ 1 ∧
      k ∈ activeThresholds p q ∧ (w = 1 ∨ k+1 ∈ activeThresholds p q) ∧
      randomizedTail p w k-randomizedTail q w k = tailObjective p q ∧
      ∀ d ∈ feasibleDirections p q,
        0 ≤ ∑ i, (d.1 i*randomizedGradient p w k i-d.2 i*randomizedGradient q w k i) := by
  obtain ⟨k,w,hk0,hkn,hw0,hw1,hk,hlast,hval,_,hstat⟩ :=
    exists_stationary_randomized_test_with_activeSet h hgap hT hmin
  exact ⟨k,w,hk0,hkn,hw0,hw1,hk,hlast,hval,hstat⟩

end

end PoissonBinomialComparison

-- GapMultiplier
namespace PoissonBinomialComparison

open scoped BigOperators
open Finset

noncomputable section

variable {n : ℕ}

def gapSlotDirection : (Fin n ⊕ Fin n) → (Fin n → ℝ) × (Fin n → ℝ)
  | .inl i => (Pi.single i 1, 0)
  | .inr i => (0, -Pi.single i 1)

def gapSlotCoefficient (P Q : Fin n → ℝ) : (Fin n ⊕ Fin n) → ℝ
  | .inl i => P i
  | .inr i => Q i

def gapSlotCanDecrease (p q : Fin n → ℝ) : (Fin n ⊕ Fin n) → Prop
  | .inl i => q i < p i
  | .inr i => q i < p i

def gapSlotCanIncrease (p q : Fin n → ℝ) : (Fin n ⊕ Fin n) → Prop
  | .inl i => p i < 1
  | .inr i => 0 < q i

private theorem sum_gapSlotDirection (r : Fin n ⊕ Fin n) :
    ∑ i, ((gapSlotDirection r).1 i-(gapSlotDirection r).2 i) = 1 := by
  cases r <;> simp [gapSlotDirection]

private theorem gapSlotDirection_signs_increase {p q : Fin n → ℝ}
    (r : Fin n ⊕ Fin n) (hr : gapSlotCanIncrease p q r) (i : Fin n) :
    (p i = 1 → (gapSlotDirection r).1 i ≤ 0) ∧
    (q i = 0 → 0 ≤ (gapSlotDirection r).2 i) ∧
    (p i = q i → (gapSlotDirection r).2 i ≤ (gapSlotDirection r).1 i) := by
  cases r with
  | inl j =>
    change p j < 1 at hr
    by_cases hij : i = j
    · subst i
      simp only [gapSlotDirection, Pi.single_eq_same, Pi.zero_apply]
      exact ⟨by intro h; linarith, by simp, by norm_num⟩
    · simp [gapSlotDirection, Pi.single_eq_of_ne hij]
  | inr j =>
    change 0 < q j at hr
    by_cases hij : i = j
    · subst i
      simp only [gapSlotDirection, Pi.single_eq_same, Pi.zero_apply, Pi.neg_apply]
      exact ⟨by simp, by intro h; linarith, by norm_num⟩
    · simp [gapSlotDirection, Pi.single_eq_of_ne hij]

private theorem gapSlotDirection_signs_decrease {p q : Fin n → ℝ}
    (r : Fin n ⊕ Fin n) (hr : gapSlotCanDecrease p q r) (i : Fin n) :
    (p i = 1 → 0 ≤ (gapSlotDirection r).1 i) ∧
    (q i = 0 → (gapSlotDirection r).2 i ≤ 0) ∧
    (p i = q i → (gapSlotDirection r).1 i ≤ (gapSlotDirection r).2 i) := by
  cases r with
  | inl j =>
    change q j < p j at hr
    by_cases hij : i = j
    · subst i
      simp only [gapSlotDirection, Pi.single_eq_same, Pi.zero_apply]
      exact ⟨by norm_num, by simp, by intro h; linarith⟩
    · simp [gapSlotDirection, Pi.single_eq_of_ne hij]
  | inr j =>
    change q j < p j at hr
    by_cases hij : i = j
    · subst i
      simp only [gapSlotDirection, Pi.single_eq_same, Pi.zero_apply, Pi.neg_apply]
      exact ⟨by simp, by norm_num, by intro h; linarith⟩
    · simp [gapSlotDirection, Pi.single_eq_of_ne hij]

theorem gapSlot_transfer_mem {p q : Fin n → ℝ} {r s : Fin n ⊕ Fin n}
    (hr : gapSlotCanDecrease p q r) (hs : gapSlotCanIncrease p q s) :
    gapSlotDirection s-gapSlotDirection r ∈ feasibleDirections p q := by
  constructor
  · change ∑ i, ((gapSlotDirection s).1 i-(gapSlotDirection r).1 i-
      ((gapSlotDirection s).2 i-(gapSlotDirection r).2 i)) = 0
    simp_rw [show ∀ i, (gapSlotDirection s).1 i-(gapSlotDirection r).1 i-
      ((gapSlotDirection s).2 i-(gapSlotDirection r).2 i) =
      ((gapSlotDirection s).1 i-(gapSlotDirection s).2 i)-
      ((gapSlotDirection r).1 i-(gapSlotDirection r).2 i) by intro i; ring]
    rw [sum_sub_distrib, sum_gapSlotDirection, sum_gapSlotDirection, sub_self]
  · intro i
    have ha := gapSlotDirection_signs_increase s hs i
    have hb := gapSlotDirection_signs_decrease r hr i
    change (p i = 1 → (gapSlotDirection s).1 i-(gapSlotDirection r).1 i ≤ 0) ∧
      (q i = 0 → 0 ≤ (gapSlotDirection s).2 i-(gapSlotDirection r).2 i) ∧
      (p i = q i → (gapSlotDirection s).2 i-(gapSlotDirection r).2 i ≤
        (gapSlotDirection s).1 i-(gapSlotDirection r).1 i)
    exact ⟨fun h ↦ sub_nonpos.mpr ((ha.1 h).trans (hb.1 h)),
      fun h ↦ sub_nonneg.mpr ((hb.2.1 h).trans (ha.2.1 h)),
      fun h ↦ sub_le_sub (ha.2.2 h) (hb.2.2 h)⟩

private theorem gapSlotCoefficient_eq_sum (P Q : Fin n → ℝ) (r : Fin n ⊕ Fin n) :
    (∑ i, ((gapSlotDirection r).1 i*P i-(gapSlotDirection r).2 i*Q i)) =
      gapSlotCoefficient P Q r := by
  cases r <;> simp [gapSlotDirection, gapSlotCoefficient, Pi.single_apply, ite_mul]

theorem gapSlotCoefficient_le {p q P Q : Fin n → ℝ}
    (hstat : ∀ d ∈ feasibleDirections p q, 0 ≤ ∑ i, (d.1 i*P i-d.2 i*Q i))
    {r s : Fin n ⊕ Fin n} (hr : gapSlotCanDecrease p q r) (hs : gapSlotCanIncrease p q s) :
    gapSlotCoefficient P Q r ≤ gapSlotCoefficient P Q s := by
  have h := hstat _ (gapSlot_transfer_mem hr hs)
  change 0 ≤ ∑ i, (((gapSlotDirection s).1 i-(gapSlotDirection r).1 i)*P i-
    ((gapSlotDirection s).2 i-(gapSlotDirection r).2 i)*Q i) at h
  simp_rw [show ∀ i, ((gapSlotDirection s).1 i-(gapSlotDirection r).1 i)*P i-
      ((gapSlotDirection s).2 i-(gapSlotDirection r).2 i)*Q i =
      ((gapSlotDirection s).1 i*P i-(gapSlotDirection s).2 i*Q i)-
      ((gapSlotDirection r).1 i*P i-(gapSlotDirection r).2 i*Q i) by intro i; ring] at h
  rw [sum_sub_distrib, gapSlotCoefficient_eq_sum, gapSlotCoefficient_eq_sum] at h
  exact sub_nonneg.mp h

theorem exists_gap_multiplier {p q P Q : Fin n → ℝ} (hchange : ∃ i, q i < p i)
    (hstat : ∀ d ∈ feasibleDirections p q, 0 ≤ ∑ i, (d.1 i*P i-d.2 i*Q i)) :
    ∃ c : ℝ, (∀ r, gapSlotCanDecrease p q r → gapSlotCoefficient P Q r ≤ c) ∧
      (∀ s, gapSlotCanIncrease p q s → c ≤ gapSlotCoefficient P Q s) := by
  classical
  let L := univ.filter (gapSlotCanDecrease p q)
  have hne : L.Nonempty := by
    obtain ⟨i,hi⟩ := hchange
    exact ⟨Sum.inl i, mem_filter.mpr ⟨mem_univ _,hi⟩⟩
  refine ⟨L.sup' hne (gapSlotCoefficient P Q), ?_, ?_⟩
  · intro r hr
    exact le_sup' _ (mem_filter.mpr ⟨mem_univ _,hr⟩)
  · intro s hs
    apply sup'_le
    intro r hr
    exact gapSlotCoefficient_le hstat (mem_filter.mp hr).2 hs

theorem common_coordinate_gradient_eq {p q P Q : Fin n → ℝ}
    (hstat : ∀ d ∈ feasibleDirections p q, 0 ≤ ∑ i, (d.1 i*P i-d.2 i*Q i))
    (i : Fin n) (hp : p i < 1) (hq : 0 < q i) : P i = Q i := by
  have hdir (t : ℝ) : ((Pi.single i t), (Pi.single i t)) ∈ feasibleDirections p q := by
    constructor
    · simp
    · intro j
      by_cases hji : j = i
      · subst j
        simp only [Pi.single_eq_same]
        exact ⟨by intro h; linarith, by intro h; linarith, by simp⟩
      · simp [Pi.single_eq_of_ne hji]
  have hpos := hstat _ (hdir 1)
  have hneg := hstat _ (hdir (-1))
  simp [Pi.single_apply, ite_mul, sum_sub_distrib] at hpos hneg
  linarith

theorem exists_gap_multiplier_coordinates {p q P Q : Fin n → ℝ}
    (hchange : ∃ i, q i < p i)
    (hcommon : ∀ i, p i = q i → 0 < q i ∧ p i < 1)
    (hstat : ∀ d ∈ feasibleDirections p q, 0 ≤ ∑ i, (d.1 i*P i-d.2 i*Q i)) :
    ∃ c : ℝ,
      (∀ i, q i < p i → P i ≤ c ∧ Q i ≤ c ∧
        (p i < 1 → P i = c) ∧ (0 < q i → Q i = c)) ∧
      (∀ i, p i = q i → ∃ ν : ℝ, 0 ≤ ν ∧ P i = c+ν ∧ Q i = c+ν) := by
  obtain ⟨c,hclose,hopen⟩ := exists_gap_multiplier hchange hstat
  refine ⟨c,?_,?_⟩
  · intro i hi
    have hp := hclose (Sum.inl i) hi
    have hq := hclose (Sum.inr i) hi
    exact ⟨hp,hq, fun h ↦ le_antisymm hp (hopen (Sum.inl i) h),
      fun h ↦ le_antisymm hq (hopen (Sum.inr i) h)⟩
  · intro i hi
    obtain ⟨hq,hp⟩ := hcommon i hi
    have heq := common_coordinate_gradient_eq hstat i hp hq
    have hc := hopen (Sum.inl i) hp
    refine ⟨P i-c, sub_nonneg.mpr hc, by ring, ?_⟩
    linarith

end

end PoissonBinomialComparison

-- GradientPositivity
namespace PoissonBinomialComparison

open Finset

noncomputable section

variable {ι : Type*} [DecidableEq ι]

theorem pbMassOn_card_eq_prod (p : ι → ℝ) (s : Finset ι) :
    pbMassOn p s s.card = ∏ i ∈ s, p i := by
  simp [pbMassOn, bernoulliWeight]

theorem pbTailOn_eq_one_of_mass_zero_below (p : ι → ℝ) (s : Finset ι) (k : ℕ)
    (hz : ∀ j < k, pbMassOn p s j = 0) : pbTailOn p s k = 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hprev := ih (fun j hj ↦ hz j (by omega))
    have hdiff := pbTailOn_sub_succ p s k
    rw [hz k (by omega), hprev] at hdiff
    linarith

theorem pbTailOn_succ_eq_one_of_mass_zero_of_top_pos {p : ι → ℝ} {s : Finset ι}
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) {k : ℕ} (hk : k ≤ s.card)
    (htop : 0 < pbMassOn p s s.card) (hz : pbMassOn p s k = 0) :
    pbTailOn p s (k + 1) = 1 := by
  apply pbTailOn_eq_one_of_mass_zero_below
  intro j hj
  apply le_antisymm _ (pbMassOn_nonneg hp j)
  by_contra hnot
  have hpos := pbMassOn_positive_between s hp (by omega : j ≤ k) hk
    (lt_of_not_ge hnot) htop
  rw [hz] at hpos
  exact lt_irrefl _ hpos

theorem pbTailOn_eq_zero_of_mass_zero_of_zero_pos {p : ι → ℝ} {s : Finset ι}
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) {k : ℕ}
    (hzero : 0 < pbMassOn p s 0) (hz : pbMassOn p s k = 0) :
    pbTailOn p s k = 0 := by
  rw [pbTailOn_eq_sum_mass]
  apply sum_eq_zero
  intro j hj
  apply le_antisymm _ (pbMassOn_nonneg hp j)
  by_contra hnot
  have hpos := pbMassOn_positive_between s hp (Nat.zero_le k) (mem_Icc.mp hj).1
    hzero (lt_of_not_ge hnot)
  rw [hz] at hpos
  exact lt_irrefl _ hpos

variable {n : ℕ} {p q : Fin n → ℝ}

theorem deleted_mass_pair_pos (h : AdmissiblePair p q)
    (hp : ∀ i, 0 < p i) (hq : ∀ i, q i < 1)
    (hT : tailObjective p q < 1) (i : Fin n) {k : ℕ}
    (hk0 : 1 ≤ k) (hkn : k ≤ n) :
    0 < pbMassOn p (univ.erase i) (k - 1) +
      pbMassOn q (univ.erase i) (k - 1) := by
  let s := (univ : Finset (Fin n)).erase i
  have hps : ∀ j ∈ s, 0 ≤ p j ∧ p j ≤ 1 := fun j _ ↦ h.1 j
  have hqs : ∀ j ∈ s, 0 ≤ q j ∧ q j ≤ 1 := fun j _ ↦ h.2.1 j
  have hcard : s.card = n - 1 := by simp [s]
  have hk : k - 1 ≤ s.card := by omega
  have htop : 0 < pbMassOn p s s.card := by
    rw [pbMassOn_card_eq_prod]
    exact prod_pos fun j _ ↦ hp j
  have hzero : 0 < pbMassOn q s 0 := by
    rw [pbMassOn_zero]
    exact prod_pos fun j _ ↦ sub_pos.mpr (hq j)
  by_contra hnot
  have hpnonneg := pbMassOn_nonneg hps (k - 1)
  have hqnonneg := pbMassOn_nonneg hqs (k - 1)
  change ¬ 0 < pbMassOn p s (k - 1) + pbMassOn q s (k - 1) at hnot
  have hpz : pbMassOn p s (k - 1) = 0 := by linarith
  have hqz : pbMassOn q s (k - 1) = 0 := by linarith
  have hpk := pbTailOn_succ_eq_one_of_mass_zero_of_top_pos hps hk htop hpz
  have hqkm := pbTailOn_eq_zero_of_mass_zero_of_zero_pos hqs hzero hqz
  have hpstep := pbTailOn_sub_succ p s (k - 1)
  have hqstep := pbTailOn_sub_succ q s (k - 1)
  have hpred : k - 1 + 1 = k := by omega
  rw [hpred] at hpk hpstep hqstep
  have hpkm : pbTailOn p s (k - 1) = 1 := by linarith
  have hqk : pbTailOn q s k = 0 := by linarith
  have hpfull := pbTail_delete_succ p i (k - 1)
  have hqfull := pbTail_delete_succ q i (k - 1)
  change pbTail p (k - 1 + 1) = (1 - p i) * pbTailOn p s (k - 1 + 1) +
    p i * pbTailOn p s (k - 1) at hpfull
  change pbTail q (k - 1 + 1) = (1 - q i) * pbTailOn q s (k - 1 + 1) +
    q i * pbTailOn q s (k - 1) at hqfull
  rw [hpred, hpk, hpkm] at hpfull
  rw [hpred, hqk, hqkm] at hqfull
  have hbound := tailDiff_le_tailObjective p q (mem_Icc.mpr ⟨hk0, hkn⟩)
  unfold tailDiff at hbound
  rw [hpfull, hqfull] at hbound
  linarith

theorem randomizedGradient_nonneg (hp : ValidParameters p) {w : ℝ}
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (k : ℕ) (i : Fin n) :
    0 ≤ randomizedGradient p w k i := by
  unfold randomizedGradient randomizedSlopeOn
  apply add_nonneg
  · exact mul_nonneg (sub_nonneg.mpr hw1) (pbMassOn_nonneg (fun j _ ↦ hp j) k)
  · apply mul_nonneg hw0
    split
    · exact le_rfl
    · exact pbMassOn_nonneg (fun j _ ↦ hp j) (k - 1)

theorem randomizedGradient_pair_pos (h : AdmissiblePair p q)
    (hp : ∀ i, 0 < p i) (hq : ∀ i, q i < 1)
    (hT : tailObjective p q < 1) {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    {k : ℕ} (hk0 : 1 ≤ k) (hkn : k < n) (i : Fin n) :
    0 < randomizedGradient p w k i + randomizedGradient q w k i := by
  have hleft := deleted_mass_pair_pos h hp hq hT i hk0 hkn.le
  have hright := deleted_mass_pair_pos h hp hq hT i (by omega : 1 ≤ k + 1)
    (by omega : k + 1 ≤ n)
  simp only [Nat.add_sub_cancel] at hright
  unfold randomizedGradient randomizedSlopeOn
  simp only [show k ≠ 0 by omega, ite_false]
  by_cases hw : w = 1
  · subst w
    simpa using hleft
  · have hr := mul_pos (sub_pos.mpr (lt_of_le_of_ne hw1 hw)) hright
    have hl := mul_nonneg hw0 hleft.le
    nlinarith

theorem randomizedGradient_pair_pos_pure (h : AdmissiblePair p q)
    (hp : ∀ i, 0 < p i) (hq : ∀ i, q i < 1)
    (hT : tailObjective p q < 1) {k : ℕ} (hk0 : 1 ≤ k) (hkn : k ≤ n) (i : Fin n) :
    0 < randomizedGradient p 1 k i + randomizedGradient q 1 k i := by
  simpa [randomizedGradient, randomizedSlopeOn, show k ≠ 0 by omega] using
    deleted_mass_pair_pos h hp hq hT i hk0 hkn

theorem randomizedGradient_multiplier_pos (h : AdmissiblePair p q)
    (hp : ∀ i, 0 < p i) (hq : ∀ i, q i < 1)
    (hT : tailObjective p q < 1) {w c : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    {k : ℕ} (hk0 : 1 ≤ k) (hkn : k ≤ n) (hlast : k < n ∨ w = 1)
    (i : Fin n) (hpc : randomizedGradient p w k i ≤ c)
    (hqc : randomizedGradient q w k i ≤ c) : 0 < c := by
  have hpos : 0 < randomizedGradient p w k i + randomizedGradient q w k i := by
    rcases hlast with hk | rfl
    · exact randomizedGradient_pair_pos h hp hq hT hw0 hw1 hk0 hk i
    · exact randomizedGradient_pair_pos_pure h hp hq hT hk0 hkn i
  linarith

end

end PoissonBinomialComparison

-- TailKKT
namespace PoissonBinomialComparison

open Finset

noncomputable section

theorem exists_tail_kkt_with_activeSet {n : ℕ} {p q : Fin n → ℝ} (h : AdmissiblePair p q)
    (hp : ∀ i, 0 < p i) (hq : ∀ i, q i < 1)
    (hgap : 0 < meanGap p q) (hT : tailObjective p q < 1)
    (hmin : IsLocalMinOn (fun x : (Fin n → ℝ) × (Fin n → ℝ) ↦ tailObjective x.1 x.2)
      (feasiblePairs n (meanGap p q)) (p,q)) :
    ∃ k : ℕ, ∃ w c : ℝ, 1 ≤ k ∧ k ≤ n ∧ 0 ≤ w ∧ w ≤ 1 ∧ 0 < c ∧
      k ∈ activeThresholds p q ∧ (w = 1 ∨ k+1 ∈ activeThresholds p q) ∧
      randomizedTail p w k-randomizedTail q w k = tailObjective p q ∧
      ((activeThresholds p q = {k} ∧ w = 1) ∨ activeThresholds p q = {k,k+1}) ∧
      (∀ i, q i < p i →
        randomizedGradient p w k i ≤ c ∧ randomizedGradient q w k i ≤ c ∧
        (p i < 1 → randomizedGradient p w k i = c) ∧
        (0 < q i → randomizedGradient q w k i = c)) ∧
      (∀ i, p i = q i → ∃ ν : ℝ, 0 ≤ ν ∧
        randomizedGradient p w k i = c+ν ∧ randomizedGradient q w k i = c+ν) := by
  obtain ⟨k,w,hk0,hkn,hw0,hw1,hactive,hlast,hval,hset,hstat⟩ :=
    exists_stationary_randomized_test_with_activeSet h hgap hT hmin
  have hchange := exists_strict_coordinate_of_meanGap_pos h hgap
  obtain ⟨c,hc,hcommon⟩ := exists_gap_multiplier_coordinates hchange (by
    intro i hi
    exact ⟨hi ▸ hp i, hi.symm ▸ hq i⟩) hstat
  have hlast' : k < n ∨ w = 1 := by
    rcases hlast with hw | hk
    · exact Or.inr hw
    · have := ((mem_activeThresholds p q (k+1)).mp hk).2.1
      exact Or.inl (by omega)
  obtain ⟨i,hi⟩ := hchange
  have hcpos := randomizedGradient_multiplier_pos h hp hq hT hw0 hw1 hk0 hkn hlast'
    i (hc i hi).1 (hc i hi).2.1
  exact ⟨k,w,c,hk0,hkn,hw0,hw1,hcpos,hactive,hlast,hval,hset,hc,hcommon⟩

theorem exists_tail_kkt {n : ℕ} {p q : Fin n → ℝ} (h : AdmissiblePair p q)
    (hp : ∀ i, 0 < p i) (hq : ∀ i, q i < 1)
    (hgap : 0 < meanGap p q) (hT : tailObjective p q < 1)
    (hmin : IsLocalMinOn (fun x : (Fin n → ℝ) × (Fin n → ℝ) ↦ tailObjective x.1 x.2)
      (feasiblePairs n (meanGap p q)) (p,q)) :
    ∃ k : ℕ, ∃ w c : ℝ, 1 ≤ k ∧ k ≤ n ∧ 0 ≤ w ∧ w ≤ 1 ∧ 0 < c ∧
      k ∈ activeThresholds p q ∧ (w = 1 ∨ k+1 ∈ activeThresholds p q) ∧
      randomizedTail p w k-randomizedTail q w k = tailObjective p q ∧
      (∀ i, q i < p i →
        randomizedGradient p w k i ≤ c ∧ randomizedGradient q w k i ≤ c ∧
        (p i < 1 → randomizedGradient p w k i = c) ∧
        (0 < q i → randomizedGradient q w k i = c)) ∧
      (∀ i, p i = q i → ∃ ν : ℝ, 0 ≤ ν ∧
        randomizedGradient p w k i = c+ν ∧ randomizedGradient q w k i = c+ν) := by
  obtain ⟨k,w,c,hk0,hkn,hw0,hw1,hc,hk,hlast,hval,_,hchanging,hcommon⟩ :=
    exists_tail_kkt_with_activeSet h hp hq hgap hT hmin
  exact ⟨k,w,c,hk0,hkn,hw0,hw1,hc,hk,hlast,hval,hchanging,hcommon⟩

end

end PoissonBinomialComparison

-- Reindex
namespace PoissonBinomialComparison

open scoped BigOperators
open Finset

noncomputable section

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]

theorem pbMassIntOn_map (p : κ → ℝ) (e : ι ↪ κ) (s : Finset ι) (k : ℤ) :
    pbMassIntOn p (s.map e) k = pbMassIntOn (fun i ↦ p (e i)) s k := by
  induction s using Finset.induction_on generalizing k with
  | empty => simp
  | @insert i s hi ih =>
    have hei : e i ∉ s.map e := by simpa using hi
    rw [map_insert, pbMassIntOn_insert p hei, pbMassIntOn_insert _ hi, ih, ih]

theorem pbMassOn_map (p : κ → ℝ) (e : ι ↪ κ) (s : Finset ι) (k : ℕ) :
    pbMassOn p (s.map e) k = pbMassOn (fun i ↦ p (e i)) s k := by
  simpa using pbMassIntOn_map p e s (k : ℤ)

theorem pbTailOn_map (p : κ → ℝ) (e : ι ↪ κ) (s : Finset ι) (k : ℕ) :
    pbTailOn p (s.map e) k = pbTailOn (fun i ↦ p (e i)) s k := by
  induction s using Finset.induction_on generalizing k with
  | empty => simp [pbTailOn, bernoulliWeight]
  | @insert i s hi ih =>
    have hei : e i ∉ s.map e := by simpa using hi
    cases k with
    | zero => simp
    | succ k =>
      rw [map_insert, pbTailOn_insert_succ p hei, pbTailOn_insert_succ _ hi, ih, ih]

def finsetParameters (p : ι → ℝ) (s : Finset ι) : Fin s.card → ℝ :=
  fun i ↦ p ((s.equivFin).symm i)

private def finsetEmbedding (s : Finset ι) : Fin s.card ↪ ι :=
  (s.equivFin.symm.toEmbedding).trans ⟨Subtype.val, Subtype.val_injective⟩

omit [DecidableEq ι] in
private theorem map_finsetEmbedding (s : Finset ι) : univ.map (finsetEmbedding s) = s := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, _, rfl⟩ := mem_map.mp hx
    exact (s.equivFin.symm i).property
  · intro hx
    refine mem_map.mpr ⟨s.equivFin ⟨x, hx⟩, mem_univ _, ?_⟩
    simp [finsetEmbedding]

omit [DecidableEq ι] in

theorem valid_finsetParameters {p : ι → ℝ} (s : Finset ι)
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) : ValidParameters (finsetParameters p s) :=
  fun i ↦ hp _ (s.equivFin.symm i).property

theorem pbMass_finsetParameters (p : ι → ℝ) (s : Finset ι) (k : ℕ) :
    pbMass (finsetParameters p s) k = pbMassOn p s k := by
  have h := pbMassOn_map p (finsetEmbedding s) univ k
  rw [map_finsetEmbedding] at h
  exact h.symm

theorem pbTail_finsetParameters (p : ι → ℝ) (s : Finset ι) (k : ℕ) :
    pbTail (finsetParameters p s) k = pbTailOn p s k := by
  have h := pbTailOn_map p (finsetEmbedding s) univ k
  rw [map_finsetEmbedding] at h
  exact h.symm

omit [DecidableEq ι] in

theorem sum_finsetParameters (p : ι → ℝ) (s : Finset ι) :
    (∑ i, finsetParameters p s i) = ∑ i ∈ s, p i := by
  have h := sum_map univ (finsetEmbedding s) p
  rw [map_finsetEmbedding] at h
  exact h.symm

variable {n : ℕ}

theorem pbMassInt_cons (p : Fin n → ℝ) (t : ℝ) (k : ℤ) :
    pbMassIntOn (Fin.cons t p) univ k =
      (1 - t) * pbMassIntOn p univ k + t * pbMassIntOn p univ (k - 1) := by
  rw [Fin.univ_succ, cons_eq_insert]
  rw [pbMassIntOn_insert _ (by simp [map_eq_image])]
  rw [pbMassIntOn_map, pbMassIntOn_map]
  rfl

theorem pbTail_cons (p : Fin n → ℝ) (t : ℝ) (k : ℕ) :
    pbTail (Fin.cons t p) (k + 1) = (1 - t) * pbTail p (k + 1) + t * pbTail p k := by
  unfold pbTail
  rw [Fin.univ_succ, cons_eq_insert]
  rw [pbTailOn_insert_succ _ (by simp [map_eq_image])]
  rw [pbTailOn_map, pbTailOn_map]
  rfl

theorem tailDiff_cons_common (p q : Fin n → ℝ) (t : ℝ) (k : ℕ) :
    tailDiff (Fin.cons t p) (Fin.cons t q) (k + 1) =
      (1 - t) * tailDiff p q (k + 1) + t * tailDiff p q k := by
  simp only [tailDiff, pbTail_cons]
  ring

theorem meanGap_cons_common (p q : Fin n → ℝ) (t : ℝ) :
    meanGap (Fin.cons t p) (Fin.cons t q) = meanGap p q := by
  simp [meanGap, Fin.sum_univ_succ]

end

end PoissonBinomialComparison

-- TwoDimensional
namespace PoissonBinomialComparison

open scoped BigOperators
open Finset

noncomputable section

theorem tailDiff_one_add_two (p q : Fin 2 → ℝ) :
    tailDiff p q 1 + tailDiff p q 2 = meanGap p q := by
  have h : Icc (1 : ℕ) 2 = {1, 2} := by decide
  simpa [h] using sum_tailDiff p q

theorem tailObjective_two (p q : Fin 2 → ℝ) :
    tailObjective p q = max (tailDiff p q 1) (tailDiff p q 2) := by
  rw [tailObjective_eq_sup' p q (by decide)]
  have h : Icc (1 : ℕ) 2 = {1, 2} := by decide
  simp [h, sup'_insert (singleton_nonempty 2)]

theorem pbTail_two_two (p : Fin 2 → ℝ) : pbTail p 2 = p 0 * p 1 := by
  rw [pbTail_eq_sum_mass, Icc_self, sum_singleton, pbMass, pbMassOn]
  have h : (univ : Finset (Fin 2)).powersetCard 2 = {univ} := by
    simpa using powersetCard_self (univ : Finset (Fin 2))
  rw [h]
  simp [bernoulliWeight, Fin.prod_univ_two]

theorem twoDimensional_lower_bound (p q : Fin 2 → ℝ) :
    meanGap p q / 2 ≤ tailObjective p q := by
  have hsum := tailDiff_one_add_two p q
  have h1 := tailDiff_le_tailObjective p q (k := 1) (by decide)
  have h2 := tailDiff_le_tailObjective p q (k := 2) (by decide)
  linarith

theorem complementaryPair_two_attains (Δ : ℝ) (hΔ0 : 0 ≤ Δ) (hΔ2 : Δ ≤ 2) :
    let p : Fin 2 → ℝ := fun _ ↦ (1 + Δ / 2) / 2
    let q : Fin 2 → ℝ := fun _ ↦ (1 - Δ / 2) / 2
    AdmissiblePair p q ∧ meanGap p q = Δ ∧ tailObjective p q = Δ / 2 := by
  let p : Fin 2 → ℝ := fun _ ↦ (1 + Δ / 2) / 2
  let q : Fin 2 → ℝ := fun _ ↦ (1 - Δ / 2) / 2
  change AdmissiblePair p q ∧ meanGap p q = Δ ∧ tailObjective p q = Δ / 2
  have hgap : meanGap p q = Δ := by
    simp only [meanGap, Fin.sum_univ_two, p, q]
    ring
  have htwo : tailDiff p q 2 = Δ / 2 := by
    rw [tailDiff, pbTail_two_two, pbTail_two_two]
    dsimp [p, q]
    ring
  have hone : tailDiff p q 1 = Δ / 2 := by
    have hsum := tailDiff_one_add_two p q
    rw [hgap, htwo] at hsum
    linarith
  refine ⟨?_, hgap, ?_⟩
  · rw [admissiblePair_iff]
    intro i
    dsimp [p, q]
    constructor
    · linarith
    · constructor <;> linarith
  · rw [tailObjective_two, hone, htwo, max_self]

end

end PoissonBinomialComparison

-- TotalVariation
namespace PoissonBinomialComparison

open scoped BigOperators
open Finset

noncomputable section

def productTV {n : ℕ} (p q : Fin n → ℝ) : ℝ :=
  (∑ A ∈ (univ : Finset (Fin n)).powerset,
    |bernoulliWeight p univ A - bernoulliWeight q univ A|) / 2

private theorem sum_event_le_half_sum_abs {α : Type*} (s : Finset α)
    (f : α → ℝ) (P : α → Prop) [DecidablePred P] (hf : ∑ x ∈ s, f x = 0) :
    (∑ x ∈ s, if P x then f x else 0) ≤ (∑ x ∈ s, |f x|) / 2 := by
  have h : (∑ x ∈ s, (2 * (if P x then f x else 0) - f x)) ≤
      ∑ x ∈ s, |f x| := by
    apply sum_le_sum
    intro x hx
    by_cases hP : P x
    · simp only [if_pos hP]
      linarith [le_abs_self (f x)]
    · simp only [if_neg hP, mul_zero, zero_sub]
      exact neg_le_abs (f x)
  rw [sum_sub_distrib, ← mul_sum, hf, sub_zero] at h
  linarith

theorem productTV_nonneg {n : ℕ} (p q : Fin n → ℝ) : 0 ≤ productTV p q := by
  exact div_nonneg (sum_nonneg fun _ _ ↦ abs_nonneg _) (by norm_num)

@[simp] theorem productTV_self {n : ℕ} (p : Fin n → ℝ) : productTV p p = 0 := by
  simp [productTV]

theorem eventDiff_le_productTV {n : ℕ} (p q : Fin n → ℝ)
    (P : Finset (Fin n) → Prop) [DecidablePred P] :
    (∑ A ∈ (univ : Finset (Fin n)).powerset,
      if P A then bernoulliWeight p univ A - bernoulliWeight q univ A else 0) ≤
        productTV p q := by
  apply sum_event_le_half_sum_abs
  rw [sum_sub_distrib, sum_bernoulliWeight, sum_bernoulliWeight, sub_self]

theorem tailDiff_le_productTV {n : ℕ} (p q : Fin n → ℝ) (k : ℕ) :
    tailDiff p q k ≤ productTV p q := by
  have h := eventDiff_le_productTV p q (fun A ↦ k ≤ A.card)
  convert! h using 1
  simp only [tailDiff, pbTail, pbTailOn, ← sum_sub_distrib]
  apply sum_congr rfl
  intro A hA
  split_ifs <;> simp

theorem tailObjective_le_productTV {n : ℕ} (p q : Fin n → ℝ) :
    tailObjective p q ≤ productTV p q := by
  cases n with
  | zero => simpa using productTV_nonneg p q
  | succ n =>
    exact (tailObjective_le_iff p q (Nat.succ_pos n) _).mpr
      fun k _ ↦ tailDiff_le_productTV p q k

end

end PoissonBinomialComparison

-- TotalVariationHomogeneous
namespace PoissonBinomialComparison

open scoped BigOperators
open Finset

noncomputable section

variable {n : ℕ} {p q : Fin n → ℝ}

def countTV (p q : Fin n → ℝ) : ℝ :=
  (∑ k ∈ range (n + 1), |pbMass p k - pbMass q k|) / 2

theorem countTV_nonneg (p q : Fin n → ℝ) : 0 ≤ countTV p q :=
  div_nonneg (sum_nonneg fun _ _ ↦ abs_nonneg _) (by norm_num)

@[simp] theorem countTV_self (p : Fin n → ℝ) : countTV p p = 0 := by
  simp [countTV]

theorem sum_massDiff (p q : Fin n → ℝ) :
    ∑ k ∈ range (n + 1), (pbMass p k - pbMass q k) = 0 := by
  rw [sum_sub_distrib, sum_pbMass, sum_pbMass, sub_self]

theorem massDiff_nonneg_after_pos (h : AdmissiblePair p q) {i j : ℕ}
    (hij : i ≤ j) (hi : pbMass q i < pbMass p i) : pbMass q j ≤ pbMass p j := by
  by_contra hnot
  have hj : pbMass p j < pbMass q j := lt_of_not_ge hnot
  have hqj : 0 < pbMass q j := (pbMass_nonneg h.1 j).trans_lt hj
  have hstrict := mul_lt_mul_of_pos_right hi hqj
  have hweak := mul_le_mul_of_nonneg_left hj.le (pbMass_nonneg h.2.1 i)
  have hlr := pbMass_likelihoodRatio h i j hij
  nlinarith

theorem pbMass_zero_antitone (h : AdmissiblePair p q) : pbMass p 0 ≤ pbMass q 0 := by
  have hd := tailDiff_sub_succ p q 0
  have hn := tailDiff_nonneg h 1
  simp only [tailDiff, pbTail_zero, sub_self, zero_add, zero_sub] at hd
  change 0 ≤ pbTail p 1 - pbTail q 1 at hn
  linarith

theorem tailDiff_eq_sum_count_indicator (p q : Fin n → ℝ) (k : ℕ) :
    tailDiff p q k = ∑ j ∈ range (n + 1),
      if k ≤ j then pbMass p j - pbMass q j else 0 := by
  rw [← sum_filter]
  have heq : (range (n + 1)).filter (fun j ↦ k ≤ j) = Icc k n := by
    ext j
    simp only [mem_filter, mem_range, mem_Icc]
    omega
  rw [heq]
  exact tailDiff_eq_sum_mass p q k

theorem countTV_eq_tailDiff_of_signs (p q : Fin n → ℝ) (k : ℕ)
    (hbefore : ∀ j < k, pbMass p j ≤ pbMass q j)
    (hafter : ∀ j, k ≤ j → pbMass q j ≤ pbMass p j) :
    countTV p q = tailDiff p q k := by
  have habs : ∑ j ∈ range (n + 1), |pbMass p j - pbMass q j| =
      ∑ j ∈ range (n + 1),
        (2 * (if k ≤ j then pbMass p j - pbMass q j else 0) -
          (pbMass p j - pbMass q j)) := by
    apply sum_congr rfl
    intro j _
    by_cases hj : k ≤ j
    · rw [if_pos hj, abs_of_nonneg (sub_nonneg.mpr (hafter j hj))]
      ring
    · rw [if_neg hj, abs_of_nonpos (sub_nonpos.mpr (hbefore j (by omega)))]
      ring
  rw [sum_sub_distrib, ← mul_sum, sum_massDiff, sub_zero,
    ← tailDiff_eq_sum_count_indicator] at habs
  unfold countTV
  rw [habs]
  ring

theorem tailObjective_nonneg (h : AdmissiblePair p q) : 0 ≤ tailObjective p q := by
  cases n with
  | zero => simp
  | succ n =>
    obtain ⟨k, _, hk⟩ := tailObjective_attained p q (by omega)
    rw [hk]
    exact tailDiff_nonneg h k

theorem countTV_eq_tailObjective (h : AdmissiblePair p q) :
    countTV p q = tailObjective p q := by
  let pos := (range (n + 1)).filter (fun k ↦ pbMass q k < pbMass p k)
  by_cases hpos : pos.Nonempty
  · let k := pos.min' hpos
    have hk : k ∈ pos := min'_mem _ hpos
    have hkm := mem_filter.mp hk
    have hk1 : 1 ≤ k := by
      have hz := pbMass_zero_antitone h
      by_contra hnot
      have heq : k = 0 := by omega
      rw [heq] at hkm
      exact not_lt_of_ge hz hkm.2
    have hkn : k ≤ n := by have := mem_range.mp hkm.1; omega
    have hbefore : ∀ j < k, pbMass p j ≤ pbMass q j := by
      intro j hj
      by_contra hnot
      have hjmem : j ∈ pos := mem_filter.mpr ⟨mem_range.mpr (by omega), lt_of_not_ge hnot⟩
      have hmin : k ≤ j := min'_le _ j hjmem
      omega
    have hafter : ∀ j, k ≤ j → pbMass q j ≤ pbMass p j :=
      fun j hj ↦ massDiff_nonneg_after_pos h hj hkm.2
    rw [countTV_eq_tailDiff_of_signs p q k hbefore hafter]
    apply le_antisymm (tailDiff_le_tailObjective p q (mem_Icc.mpr ⟨hk1, hkn⟩))
    rw [tailObjective_le_iff p q (by omega)]
    intro l _
    rw [tailDiff_eq_sum_count_indicator p q l, tailDiff_eq_sum_count_indicator p q k]
    apply sum_le_sum
    intro j _
    by_cases hjl : l ≤ j <;> by_cases hjk : k ≤ j
    · simp only [hjl, hjk, ite_true, le_refl]
    · simp only [hjl, hjk, ite_true, ite_false]
      exact sub_nonpos.mpr (hbefore j (by omega))
    · simp only [hjl, hjk, ite_false, ite_true]
      exact sub_nonneg.mpr (hafter j hjk)
    · simp only [hjl, hjk, ite_false, le_refl]
  · have hnonpos : ∀ j, pbMass p j ≤ pbMass q j := by
      intro j
      by_cases hj : j ≤ n
      · by_contra hnot
        exact hpos ⟨j, mem_filter.mpr ⟨mem_range.mpr (by omega), lt_of_not_ge hnot⟩⟩
      · rw [pbMass_eq_zero_of_lt p (by omega), pbMass_eq_zero_of_lt q (by omega)]
    have hcount : countTV p q = 0 := by
      unfold countTV
      simp_rw [abs_of_nonpos (sub_nonpos.mpr (hnonpos _))]
      rw [sum_neg_distrib, sum_massDiff]
      norm_num
    rw [hcount]
    apply le_antisymm (tailObjective_nonneg h)
    cases n with
    | zero => simp
    | succ n =>
      rw [tailObjective_le_iff p q (by omega)]
      intro k _
      rw [tailDiff_eq_sum_mass]
      exact sum_nonpos fun j _ ↦ sub_nonpos.mpr (hnonpos j)

theorem productTV_const_eq_countTV (n : ℕ) (a b : ℝ) :
    productTV (fun _ : Fin n ↦ a) (fun _ ↦ b) =
      countTV (fun _ : Fin n ↦ a) (fun _ ↦ b) := by
  unfold productTV countTV
  congr 1
  rw [sum_powerset]
  simp only [card_univ, Fintype.card_fin]
  apply sum_congr rfl
  intro k _
  calc
    (∑ A ∈ (univ : Finset (Fin n)).powersetCard k,
        |bernoulliWeight (fun _ ↦ a) univ A - bernoulliWeight (fun _ ↦ b) univ A|) =
        ∑ _A ∈ (univ : Finset (Fin n)).powersetCard k,
          |a ^ k * (1 - a) ^ (n - k) - b ^ k * (1 - b) ^ (n - k)| := by
      apply sum_congr rfl
      intro A hA
      rw [bernoulliWeight_const a (mem_powersetCard.mp hA).1,
        bernoulliWeight_const b (mem_powersetCard.mp hA).1, (mem_powersetCard.mp hA).2]
      simp only [card_univ, Fintype.card_fin]
    _ = |pbMass (fun _ : Fin n ↦ a) k - pbMass (fun _ : Fin n ↦ b) k| := by
      simp only [sum_const, nsmul_eq_mul, card_powersetCard, card_univ, Fintype.card_fin,
        pbMass_const, mul_assoc]
      rw [← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg (n.choose k) : (0 : ℝ) ≤ _)]

theorem productTV_const_eq_tailObjective (n : ℕ) {a b : ℝ}
    (hb0 : 0 ≤ b) (hba : b ≤ a) (ha1 : a ≤ 1) :
    productTV (fun _ : Fin n ↦ a) (fun _ ↦ b) =
      tailObjective (fun _ : Fin n ↦ a) (fun _ ↦ b) := by
  rw [productTV_const_eq_countTV]
  exact countTV_eq_tailObjective
    ((admissiblePair_iff _ _).mpr (fun _ ↦ ⟨hb0, hba, ha1⟩))

end

end PoissonBinomialComparison

-- HomogeneousDerivative
namespace PoissonBinomialComparison

theorem pbMass_const_eq_bernstein_eval (n k : ℕ) (t : ℝ) :
    pbMass (fun _ : Fin n ↦ t) k = (bernsteinPolynomial ℝ n k).eval t := by
  simp [pbMass_const, bernsteinPolynomial]

theorem hasDerivAt_pbMass_const_zero (n : ℕ) (t : ℝ) :
    HasDerivAt (fun u : ℝ ↦ pbMass (fun _ : Fin n ↦ u) 0)
      (-(n : ℝ) * pbMass (fun _ : Fin (n - 1) ↦ t) 0) t := by
  simpa only [pbMass_const_eq_bernstein_eval, bernsteinPolynomial.derivative_zero,
    Polynomial.eval_mul, Polynomial.eval_neg, Polynomial.eval_natCast] using
    (bernsteinPolynomial ℝ n 0).hasDerivAt t

theorem hasDerivAt_pbMass_const_succ (n k : ℕ) (t : ℝ) :
    HasDerivAt (fun u : ℝ ↦ pbMass (fun _ : Fin n ↦ u) (k + 1))
      ((n : ℝ) * (pbMass (fun _ : Fin (n - 1) ↦ t) k -
        pbMass (fun _ : Fin (n - 1) ↦ t) (k + 1))) t := by
  simpa only [pbMass_const_eq_bernstein_eval, bernsteinPolynomial.derivative_succ,
    Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_natCast] using
    (bernsteinPolynomial ℝ n (k + 1)).hasDerivAt t

theorem hasDerivAt_pbTail_const_succ (n k : ℕ) (t : ℝ) :
    HasDerivAt (fun u : ℝ ↦ pbTail (fun _ : Fin n ↦ u) (k + 1))
      ((n : ℝ) * pbMass (fun _ : Fin (n - 1) ↦ t) k) t := by
  induction k with
  | zero =>
    have hd := (hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_pbMass_const_zero n t)
    convert! hd using 1
    · funext u
      simp only [Pi.sub_apply, zero_add]
      have h := pbTail_sub_succ (fun _ : Fin n ↦ u) 0
      simp only [pbTail_zero, zero_add] at h
      linarith
    · ring
  | succ k ih =>
    have hd := ih.sub (hasDerivAt_pbMass_const_succ n k t)
    convert! hd using 1
    · funext u
      simp only [Pi.sub_apply]
      have h := pbTail_sub_succ (fun _ : Fin n ↦ u) (k + 1)
      linarith
    · ring

theorem hasDerivAt_pbTail_const (n k : ℕ) (hk : 0 < k) (t : ℝ) :
    HasDerivAt (fun u : ℝ ↦ pbTail (fun _ : Fin n ↦ u) k)
      ((n : ℝ) * pbMass (fun _ : Fin (n - 1) ↦ t) (k - 1)) t := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  simpa using hasDerivAt_pbTail_const_succ n j t

theorem hasDerivAt_pbTail_const_density (n k : ℕ) (hk : 0 < k) (t : ℝ) :
    HasDerivAt (fun u : ℝ ↦ pbTail (fun _ : Fin n ↦ u) k)
      ((n : ℝ) * ((n - 1).choose (k - 1) : ℝ) *
        t ^ (k - 1) * (1 - t) ^ (n - k)) t := by
  convert! hasDerivAt_pbTail_const n k hk t using 1
  rw [pbMass_const]
  have hexp : n - 1 - (k - 1) = n - k := by omega
  rw [hexp]
  ring

theorem deriv_pbTail_const (n k : ℕ) (hk : 0 < k) (t : ℝ) :
    deriv (fun u : ℝ ↦ pbTail (fun _ : Fin n ↦ u) k) t =
      (n : ℝ) * pbMass (fun _ : Fin (n - 1) ↦ t) (k - 1) :=
  (hasDerivAt_pbTail_const n k hk t).deriv

theorem IsSwitch.tailDiff_eq {n j : ℕ} {γ a b : ℝ} (h : IsSwitch n j γ a b) :
    tailDiff (fun _ : Fin n ↦ a) (fun _ : Fin n ↦ b) j =
      tailDiff (fun _ : Fin n ↦ a) (fun _ : Fin n ↦ b) (j + 1) := by
  have ha := pbTail_sub_succ (fun _ : Fin n ↦ a) j
  have hb := pbTail_sub_succ (fun _ : Fin n ↦ b) j
  have hm := h.pbMass_eq
  unfold tailDiff
  linarith

end PoissonBinomialComparison

-- SwitchGeometry
namespace PoissonBinomialComparison

private theorem hasDerivAt_switchHeight {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    (x : ℝ) :
    HasDerivAt (fun u : ℝ ↦ u ^ j * (1 - u) ^ (n - j))
      (x ^ (j - 1) * (1 - x) ^ (n - j - 1) * ((j : ℝ) - n * x)) x := by
  have hd := ((hasDerivAt_id x).pow j).mul
    (((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).pow (n - j))
  convert! hd using 1
  dsimp only [Pi.mul_apply, Pi.pow_apply, Pi.sub_apply, id_eq]
  have hjpow : x ^ j = x ^ (j - 1) * x := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ j)]
  have hnjpow : (1 - x) ^ (n - j) = (1 - x) ^ (n - j - 1) * (1 - x) := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ n - j)]
  rw [hjpow, hnjpow, Nat.cast_sub hjn.le]
  ring

theorem IsSwitch.center_bounds {n j : ℕ} {γ a b : ℝ} (h : IsSwitch n j γ a b)
    (hj : 0 < j) (hjn : j < n) : b < (j : ℝ) / n ∧ (j : ℝ) / n < a := by
  obtain ⟨x, hx, hderiv⟩ := exists_hasDerivAt_eq_zero h.2.1
    (by fun_prop : ContinuousOn (fun u : ℝ ↦ u ^ j * (1 - u) ^ (n - j)) (Set.Icc b a))
    h.2.2.2.2.symm (fun x _ ↦ hasDerivAt_switchHeight hj hjn x)
  have hx0 : 0 < x := lt_trans h.1 hx.1
  have hx1 : 0 < 1 - x := by linarith [h.2.2.1, hx.2]
  have hfac : 0 < x ^ (j - 1) * (1 - x) ^ (n - j - 1) :=
    mul_pos (pow_pos hx0 _) (pow_pos hx1 _)
  have hz : (j : ℝ) - n * x = 0 := (mul_eq_zero.mp hderiv).resolve_left hfac.ne'
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hxc : x = (j : ℝ) / n := (eq_div_iff hn).2 (by linarith)
  exact hxc ▸ hx

theorem IsSwitch.reflect {n j : ℕ} {γ a b : ℝ} (h : IsSwitch n j γ a b)
    (hj : j ≤ n) : IsSwitch n (n - j) γ (1 - b) (1 - a) := by
  refine ⟨by linarith [h.2.2.1], by linarith [h.2.1], by linarith [h.1],
    by linarith [h.2.2.2.1], ?_⟩
  simpa only [sub_sub_cancel, Nat.sub_sub_self hj, mul_comm] using h.2.2.2.2.symm

theorem switch_denominator_identity (c a b : ℝ) :
    c * (1 - c) - (a - c) * (c - b) =
      c * (1 - a) * (1 - b) + (1 - c) * a * b := by
  ring

theorem IsSwitch.denominator_pos {n j : ℕ} {γ a b : ℝ} (h : IsSwitch n j γ a b)
    (hj : 0 < j) (hjn : j < n) :
    0 < ((j : ℝ) / n) * (1 - a) * (1 - b) + (1 - (j : ℝ) / n) * a * b := by
  obtain ⟨hbc, hca⟩ := h.center_bounds hj hjn
  have hc0 : 0 < (j : ℝ) / n := lt_trans h.1 hbc
  have hc1 : 0 < 1 - (j : ℝ) / n := by linarith [h.2.2.1]
  have ha0 : 0 < a := lt_trans h.1 h.2.1
  have ha1 : 0 < 1 - a := by linarith [h.2.2.1]
  have hb1 : 0 < 1 - b := by linarith [h.2.1, h.2.2.1]
  exact add_pos (mul_pos (mul_pos hc0 ha1) hb1) (mul_pos (mul_pos hc1 ha0) h.1)

theorem IsSwitch.geometric_ratio_bounds {n j : ℕ} {γ a b : ℝ}
    (h : IsSwitch n j γ a b) (hj : 0 < j) (hjn : j < n) :
    let c := (j : ℝ) / n
    0 < (a - c) * (c - b) / (c * (1 - c)) ∧
      (a - c) * (c - b) / (c * (1 - c)) < 1 := by
  dsimp
  obtain ⟨hbc, hca⟩ := h.center_bounds hj hjn
  have hc0 : 0 < (j : ℝ) / n := lt_trans h.1 hbc
  have hc1 : 0 < 1 - (j : ℝ) / n := by linarith [h.2.2.1]
  have hv : 0 < ((j : ℝ) / n) * (1 - (j : ℝ) / n) := mul_pos hc0 hc1
  refine ⟨div_pos (mul_pos (sub_pos.mpr hca) (sub_pos.mpr hbc)) hv, ?_⟩
  apply (div_lt_one hv).2
  have hid := switch_denominator_identity ((j : ℝ) / n) a b
  have hp := h.denominator_pos hj hjn
  linarith

theorem IsSwitch.normalized_denominator {n j : ℕ} {γ a b : ℝ}
    (h : IsSwitch n j γ a b) (hj : 0 < j) (hjn : j < n) :
    let c := (j : ℝ) / n
    c * (1 - c) * (1 - (a - c) * (c - b) / (c * (1 - c))) =
      c * (1 - a) * (1 - b) + (1 - c) * a * b := by
  dsimp
  obtain ⟨hbc, hca⟩ := h.center_bounds hj hjn
  have hc0 : 0 < (j : ℝ) / n := lt_trans h.1 hbc
  have hc1 : 0 < 1 - (j : ℝ) / n := by linarith [h.2.2.1]
  have hv : ((j : ℝ) / n) * (1 - (j : ℝ) / n) ≠ 0 := (mul_pos hc0 hc1).ne'
  rw [mul_sub, mul_one, mul_div_cancel₀ _ hv]
  exact switch_denominator_identity ((j : ℝ) / n) a b

noncomputable def switchRho (n j : ℕ) (a b : ℝ) : ℝ :=
  (n - j : ℕ) * a * b / ((n - j : ℕ) * a * b + (j : ℝ) * (1 - a) * (1 - b))

theorem IsSwitch.switchRho_mem_Ioo {n j : ℕ} {γ a b : ℝ}
    (h : IsSwitch n j γ a b) (hj : 0 < j) (hjn : j < n) :
    switchRho n j a b ∈ Set.Ioo (0 : ℝ) 1 := by
  have hj' : (0 : ℝ) < j := by exact_mod_cast hj
  have hnj' : (0 : ℝ) < (n - j : ℕ) := by exact_mod_cast (Nat.sub_pos_of_lt hjn)
  have ha0 : 0 < a := lt_trans h.1 h.2.1
  have ha1 : 0 < 1 - a := by linarith [h.2.2.1]
  have hb1 : 0 < 1 - b := by linarith [h.2.1, h.2.2.1]
  have hp : 0 < (n - j : ℕ) * a * b := mul_pos (mul_pos hnj' ha0) h.1
  have hq : 0 < (j : ℝ) * (1 - a) * (1 - b) := mul_pos (mul_pos hj' ha1) hb1
  exact ⟨div_pos hp (add_pos hp hq), (div_lt_one (add_pos hp hq)).2 (by linarith)⟩

end PoissonBinomialComparison

-- Reflection
namespace PoissonBinomialComparison

open scoped BigOperators
open Finset

noncomputable section

variable {n : ℕ}

theorem bernoulliWeight_complement (p : Fin n → ℝ) (A : Finset (Fin n)) :
    bernoulliWeight (fun i ↦ 1 - p i) univ A = bernoulliWeight p univ Aᶜ := by
  simp [bernoulliWeight, compl_eq_univ_sdiff, mul_comm]

private theorem sum_powerset_complement (f : Finset (Fin n) → ℝ) :
    ∑ A ∈ (univ : Finset (Fin n)).powerset, f A =
      ∑ A ∈ (univ : Finset (Fin n)).powerset, f Aᶜ := by
  apply sum_nbij' (fun A ↦ Aᶜ) (fun A ↦ Aᶜ)
  · intro A _; simp
  · intro A _; simp
  · intro A _; simp
  · intro A _; simp
  · intro A _; simp

theorem pbMass_complement (p : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) :
    pbMass (fun i ↦ 1 - p i) k = pbMass p (n - k) := by
  simp only [pbMass, pbMassOn_eq_sum_powerset]
  rw [sum_powerset_complement]
  simp only [bernoulliWeight_complement, compl_compl]
  apply sum_congr rfl
  intro A _
  have hcard : A.card ≤ n := by simpa using card_le_univ A
  simp only [card_compl, Fintype.card_fin]
  have heq : n - A.card = k ↔ A.card = n - k := by omega
  simp only [heq]

theorem pbTail_complement (p : Fin n → ℝ) (k : ℕ) (hk : k ≤ n + 1) :
    pbTail (fun i ↦ 1 - p i) k = 1 - pbTail p (n + 1 - k) := by
  unfold pbTail pbTailOn
  rw [sum_powerset_complement]
  simp only [bernoulliWeight_complement, compl_compl]
  rw [← sum_bernoulliWeight p (univ : Finset (Fin n)), ← sum_sub_distrib]
  apply sum_congr rfl
  intro A _
  have hcard : A.card ≤ n := by simpa using card_le_univ A
  simp only [card_compl, Fintype.card_fin]
  by_cases h : n + 1 - k ≤ A.card
  · have hh : ¬ k ≤ n - A.card := by omega
    simp [h, hh]
  · have hh : k ≤ n - A.card := by omega
    simp [h, hh]

theorem meanGap_reflection (p q : Fin n → ℝ) :
    meanGap (fun i ↦ 1 - q i) (fun i ↦ 1 - p i) = meanGap p q := by
  simp only [meanGap, sum_sub_distrib]
  ring

theorem admissiblePair_reflection {p q : Fin n → ℝ} (h : AdmissiblePair p q) :
    AdmissiblePair (fun i ↦ 1 - q i) (fun i ↦ 1 - p i) := by
  rw [admissiblePair_iff] at h ⊢
  intro i
  obtain ⟨hq, hqp, hp⟩ := h i
  exact ⟨sub_nonneg.mpr hp, sub_le_sub_left hqp 1, by linarith⟩

theorem tailDiff_reflection (p q : Fin n → ℝ) (k : ℕ) (hk : k ≤ n + 1) :
    tailDiff (fun i ↦ 1 - q i) (fun i ↦ 1 - p i) k =
      tailDiff p q (n + 1 - k) := by
  simp only [tailDiff, pbTail_complement _ k hk]
  ring

theorem tailDiff_reflection_of_mem (p q : Fin n → ℝ) {k : ℕ}
    (hk : k ∈ Icc 1 n) :
    tailDiff (fun i ↦ 1 - q i) (fun i ↦ 1 - p i) k =
      tailDiff p q (n - k + 1) := by
  have hkn := (mem_Icc.mp hk).2
  rw [tailDiff_reflection p q k (by omega)]
  congr 1
  omega

private theorem tailObjective_reflection_le (p q : Fin n → ℝ) (hn : 0 < n) :
    tailObjective (fun i ↦ 1 - q i) (fun i ↦ 1 - p i) ≤ tailObjective p q := by
  rw [tailObjective_le_iff _ _ hn]
  intro k hk
  have hkr := mem_Icc.mp hk
  rw [tailDiff_reflection p q k (by omega)]
  exact tailDiff_le_tailObjective p q (mem_Icc.mpr (by omega))

theorem tailObjective_reflection (p q : Fin n → ℝ) :
    tailObjective (fun i ↦ 1 - q i) (fun i ↦ 1 - p i) = tailObjective p q := by
  by_cases hn : 0 < n
  · apply le_antisymm (tailObjective_reflection_le p q hn)
    simpa only [sub_sub_cancel] using
      tailObjective_reflection_le (fun i ↦ 1 - q i) (fun i ↦ 1 - p i) hn
  · simp [tailObjective, hn]

end

end PoissonBinomialComparison

-- SwitchFunctions
namespace PoissonBinomialComparison

noncomputable section

def switchPair (n j : ℕ) (γ : ℝ) : ℝ × ℝ :=
  if h : 0 < j ∧ j < n ∧ 0 < γ ∧ γ < 1 then
    Classical.choose (existsUnique_switch h.1 h.2.1 h.2.2.1 h.2.2.2).exists
  else if γ ≤ 0 then ((j : ℝ) / n, (j : ℝ) / n) else (1, 0)

def switchUpper (n j : ℕ) (γ : ℝ) : ℝ := (switchPair n j γ).1

def switchLower (n j : ℕ) (γ : ℝ) : ℝ := (switchPair n j γ).2

def switchValue (n j : ℕ) (γ : ℝ) : ℝ :=
  tailDiff (fun _ : Fin n ↦ switchUpper n j γ) (fun _ : Fin n ↦ switchLower n j γ) j

def switchMass (n j : ℕ) (γ : ℝ) : ℝ :=
  pbMass (fun _ : Fin n ↦ switchUpper n j γ) j

def benchmark (n : ℕ) (Δ : ℝ) : ℝ :=
  if Δ = 0 then 0 else if Δ = n then 1 else switchValue n (n / 2) (Δ / n)

theorem switchPair_spec {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    IsSwitch n j γ (switchUpper n j γ) (switchLower n j γ) := by
  have hh : 0 < j ∧ j < n ∧ 0 < γ ∧ γ < 1 := ⟨hj, hjn, hγ0, hγ1⟩
  simp only [switchUpper, switchLower, switchPair, dif_pos hh]
  exact Classical.choose_spec (existsUnique_switch hj hjn hγ0 hγ1).exists

theorem IsSwitch.eq_switchPair {n j : ℕ} {γ a b : ℝ} (h : IsSwitch n j γ a b)
    (hj : 0 < j) (hjn : j < n) :
    a = switchUpper n j γ ∧ b = switchLower n j γ := by
  have hγ0 : 0 < γ := by linarith [h.2.1, h.2.2.2.1]
  have hγ1 : γ < 1 := by linarith [h.1, h.2.2.1, h.2.2.2.1]
  exact switch_unique hj hjn hγ0 h (switchPair_spec hj hjn hγ0 hγ1)

theorem switchUpper_sub_switchLower {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    switchUpper n j γ - switchLower n j γ = γ :=
  (switchPair_spec hj hjn hγ0 hγ1).2.2.2.1

theorem switchPair_admissible {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    AdmissiblePair (fun _ : Fin n ↦ switchUpper n j γ)
      (fun _ : Fin n ↦ switchLower n j γ) := by
  have h := switchPair_spec hj hjn hγ0 hγ1
  rw [admissiblePair_iff]
  intro i
  exact ⟨h.1.le, h.2.1.le, h.2.2.1.le⟩

theorem meanGap_switchPair {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    meanGap (fun _ : Fin n ↦ switchUpper n j γ)
      (fun _ : Fin n ↦ switchLower n j γ) = n * γ := by
  rw [meanGap_const, switchUpper_sub_switchLower hj hjn hγ0 hγ1]

@[simp] theorem switchPair_zero (n j : ℕ) :
    switchPair n j 0 = ((j : ℝ) / n, (j : ℝ) / n) := by
  simp [switchPair]

@[simp] theorem switchPair_one (n j : ℕ) : switchPair n j 1 = (1, 0) := by
  simp [switchPair]

@[simp] theorem switchUpper_zero (n j : ℕ) : switchUpper n j 0 = (j : ℝ) / n := by
  simp [switchUpper]

@[simp] theorem switchLower_zero (n j : ℕ) : switchLower n j 0 = (j : ℝ) / n := by
  simp [switchLower]

@[simp] theorem switchUpper_one (n j : ℕ) : switchUpper n j 1 = 1 := by
  simp [switchUpper]

@[simp] theorem switchLower_one (n j : ℕ) : switchLower n j 1 = 0 := by
  simp [switchLower]

@[simp] theorem switchValue_zero (n j : ℕ) : switchValue n j 0 = 0 := by
  simp [switchValue, tailDiff]

@[simp] theorem switchValue_one {n j : ℕ} (hj : 0 < j) (hjn : j ≤ n) :
    switchValue n j 1 = 1 := by
  simp [switchValue, tailDiff, pbTail_const_one, pbTail_const_zero, hjn, hj.ne']

@[simp] theorem switchMass_zero (n j : ℕ) :
    switchMass n j 0 = (n.choose j : ℝ) * ((j : ℝ) / n) ^ j *
      (1 - (j : ℝ) / n) ^ (n - j) := by
  simp [switchMass, pbMass_const]

@[simp] theorem switchMass_one {n j : ℕ} (hjn : j < n) : switchMass n j 1 = 0 := by
  simp [switchMass, pbMass_const, zero_pow (by omega : n - j ≠ 0)]

theorem switchMass_eq_lower {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    switchMass n j γ = pbMass (fun _ : Fin n ↦ switchLower n j γ) j :=
  (switchPair_spec hj hjn hγ0 hγ1).pbMass_eq

theorem switchValue_eq_succ {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    switchValue n j γ = tailDiff (fun _ : Fin n ↦ switchUpper n j γ)
      (fun _ : Fin n ↦ switchLower n j γ) (j + 1) :=
  (switchPair_spec hj hjn hγ0 hγ1).tailDiff_eq

theorem switchPair_reflection {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    switchUpper n (n - j) γ = 1 - switchLower n j γ ∧
      switchLower n (n - j) γ = 1 - switchUpper n j γ := by
  have h := ((switchPair_spec hj hjn hγ0 hγ1).reflect hjn.le).eq_switchPair
    (by omega : 0 < n - j) (by omega : n - j < n)
  exact ⟨h.1.symm, h.2.symm⟩

theorem switchValue_reflection {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    switchValue n (n - j) γ = switchValue n j γ := by
  obtain ⟨ha, hb⟩ := switchPair_reflection hj hjn hγ0 hγ1
  unfold switchValue
  rw [ha, hb, tailDiff_reflection _ _ _ (by omega : n - j ≤ n + 1)]
  have hi : n + 1 - (n - j) = j + 1 := by omega
  rw [hi]
  exact (switchValue_eq_succ hj hjn hγ0 hγ1).symm

theorem switchMass_reflection {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    switchMass n (n - j) γ = switchMass n j γ := by
  have ha := (switchPair_reflection hj hjn hγ0 hγ1).1
  unfold switchMass
  rw [ha, pbMass_complement _ _ (by omega : n - j ≤ n), Nat.sub_sub_self hjn.le]
  exact (switchMass_eq_lower hj hjn hγ0 hγ1).symm

theorem switchPair_even {m : ℕ} (hm : 0 < m)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    switchUpper (2 * m) m γ = (1 + γ) / 2 ∧
      switchLower (2 * m) m γ = (1 - γ) / 2 := by
  have hn : m < 2 * m := by omega
  have hh := switchPair_reflection hm hn hγ0 hγ1
  have hid : 2 * m - m = m := by omega
  rw [hid] at hh
  have hg := switchUpper_sub_switchLower hm hn hγ0 hγ1
  constructor <;> linarith [hh.1]

private theorem switchPair_of_nonpos (n j : ℕ) {γ : ℝ} (hγ : γ ≤ 0) :
    switchPair n j γ = ((j : ℝ) / n, (j : ℝ) / n) := by
  simp [switchPair, not_lt.mpr hγ, hγ]

private theorem switchPair_of_one_le (n j : ℕ) {γ : ℝ} (hγ : 1 ≤ γ) :
    switchPair n j γ = (1, 0) := by
  have hγ0 : ¬γ ≤ 0 := by linarith
  simp [switchPair, not_lt.mpr hγ, hγ0]

theorem continuousAt_switchUpper_zero {n j : ℕ} (hj : 0 < j) (hjn : j < n) :
    ContinuousAt (switchUpper n j) 0 := by
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  refine ⟨min ε 1, lt_min hε zero_lt_one, ?_⟩
  intro γ hγ
  have hdist : |γ| < min ε 1 := by simpa [Real.dist_eq] using hγ
  have hγ1 : γ < 1 := lt_of_le_of_lt (le_abs_self γ) (lt_min_iff.mp hdist).2
  by_cases hγ0 : γ ≤ 0
  · simp [switchUpper, switchPair_of_nonpos n j hγ0, hε]
  · have hs := switchPair_spec hj hjn (lt_of_not_ge hγ0) hγ1
    have hc := hs.center_bounds hj hjn
    rw [switchUpper_zero, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hc.2.le)]
    have hg := hs.2.2.2.1
    have hγε : γ < ε := lt_of_le_of_lt (le_abs_self γ) (lt_min_iff.mp hdist).1
    linarith [hc.1]

theorem continuousAt_switchLower_zero {n j : ℕ} (hj : 0 < j) (hjn : j < n) :
    ContinuousAt (switchLower n j) 0 := by
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  refine ⟨min ε 1, lt_min hε zero_lt_one, ?_⟩
  intro γ hγ
  have hdist : |γ| < min ε 1 := by simpa [Real.dist_eq] using hγ
  have hγ1 : γ < 1 := lt_of_le_of_lt (le_abs_self γ) (lt_min_iff.mp hdist).2
  by_cases hγ0 : γ ≤ 0
  · simp [switchLower, switchPair_of_nonpos n j hγ0, hε]
  · have hs := switchPair_spec hj hjn (lt_of_not_ge hγ0) hγ1
    have hc := hs.center_bounds hj hjn
    rw [switchLower_zero, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hc.1.le)]
    have hg := hs.2.2.2.1
    have hγε : γ < ε := lt_of_le_of_lt (le_abs_self γ) (lt_min_iff.mp hdist).1
    linarith [hc.2]

theorem continuousAt_switchUpper_one {n j : ℕ} (hj : 0 < j) (hjn : j < n) :
    ContinuousAt (switchUpper n j) 1 := by
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  refine ⟨min ε 1, lt_min hε zero_lt_one, ?_⟩
  intro γ hγ
  have hdist : |γ - 1| < min ε 1 := by simpa [Real.dist_eq] using hγ
  have hγ0 : 0 < γ := by have := (abs_lt.mp ((lt_min_iff.mp hdist).2)).1; linarith
  by_cases hγ1 : 1 ≤ γ
  · simp [switchUpper, switchPair_of_one_le n j hγ1, hε]
  · have hs := switchPair_spec hj hjn hγ0 (lt_of_not_ge hγ1)
    rw [switchUpper_one, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hs.2.2.1.le)]
    have hg := hs.2.2.2.1
    have hγε := (abs_lt.mp ((lt_min_iff.mp hdist).1)).1
    linarith [hs.1]

theorem continuousAt_switchLower_one {n j : ℕ} (hj : 0 < j) (hjn : j < n) :
    ContinuousAt (switchLower n j) 1 := by
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  refine ⟨min ε 1, lt_min hε zero_lt_one, ?_⟩
  intro γ hγ
  have hdist : |γ - 1| < min ε 1 := by simpa [Real.dist_eq] using hγ
  have hγ0 : 0 < γ := by have := (abs_lt.mp ((lt_min_iff.mp hdist).2)).1; linarith
  by_cases hγ1 : 1 ≤ γ
  · simp [switchLower, switchPair_of_one_le n j hγ1, hε]
  · have hs := switchPair_spec hj hjn hγ0 (lt_of_not_ge hγ1)
    rw [switchLower_one, Real.dist_eq, sub_zero, abs_of_nonneg hs.1.le]
    have hg := hs.2.2.2.1
    have hγε := (abs_lt.mp ((lt_min_iff.mp hdist).1)).1
    linarith [hs.2.2.1]

theorem continuousAt_switchValue_of_parameters (n j : ℕ) (γ : ℝ)
    (ha : ContinuousAt (switchUpper n j) γ) (hb : ContinuousAt (switchLower n j) γ) :
    ContinuousAt (switchValue n j) γ := by
  change ContinuousAt (fun u ↦ tailDiff (fun _ : Fin n ↦ switchUpper n j u)
    (fun _ : Fin n ↦ switchLower n j u) j) γ
  simp only [tailDiff, pbTail_const]
  fun_prop

theorem continuousAt_switchMass_of_upper (n j : ℕ) (γ : ℝ)
    (ha : ContinuousAt (switchUpper n j) γ) : ContinuousAt (switchMass n j) γ := by
  change ContinuousAt (fun u ↦ pbMass (fun _ : Fin n ↦ switchUpper n j u) j) γ
  simp only [pbMass_const]
  fun_prop

theorem continuousAt_switchValue_zero {n j : ℕ} (hj : 0 < j) (hjn : j < n) :
    ContinuousAt (switchValue n j) 0 :=
  continuousAt_switchValue_of_parameters n j 0
    (continuousAt_switchUpper_zero hj hjn) (continuousAt_switchLower_zero hj hjn)

theorem continuousAt_switchValue_one {n j : ℕ} (hj : 0 < j) (hjn : j < n) :
    ContinuousAt (switchValue n j) 1 :=
  continuousAt_switchValue_of_parameters n j 1
    (continuousAt_switchUpper_one hj hjn) (continuousAt_switchLower_one hj hjn)

theorem continuousAt_switchMass_zero {n j : ℕ} (hj : 0 < j) (hjn : j < n) :
    ContinuousAt (switchMass n j) 0 :=
  continuousAt_switchMass_of_upper n j 0 (continuousAt_switchUpper_zero hj hjn)

theorem continuousAt_switchMass_one {n j : ℕ} (hj : 0 < j) (hjn : j < n) :
    ContinuousAt (switchMass n j) 1 :=
  continuousAt_switchMass_of_upper n j 1 (continuousAt_switchUpper_one hj hjn)

@[simp] theorem benchmark_zero (n : ℕ) : benchmark n 0 = 0 := by simp [benchmark]

@[simp] theorem benchmark_at_dimension {n : ℕ} (hn : 0 < n) : benchmark n n = 1 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp [benchmark, hn']

theorem benchmark_eq_switchValue {n : ℕ} {Δ : ℝ} (hΔ0 : 0 < Δ) (hΔn : Δ < n) :
    benchmark n Δ = switchValue n (n / 2) (Δ / n) := by
  simp [benchmark, hΔ0.ne', hΔn.ne]

end

end PoissonBinomialComparison

-- SwitchMaximum
namespace PoissonBinomialComparison

open scoped BigOperators
open Finset

noncomputable section

variable {n : ℕ} {p q : Fin n → ℝ}

theorem productTV_lt_one_of_common_atom (hp : ValidParameters p) (hq : ValidParameters q)
    (A : Finset (Fin n)) (hAp : 0 < bernoulliWeight p univ A)
    (hAq : 0 < bernoulliWeight q univ A) : productTV p q < 1 := by
  have hs : (∑ B ∈ (univ : Finset (Fin n)).powerset,
      |bernoulliWeight p univ B - bernoulliWeight q univ B|) <
      ∑ B ∈ (univ : Finset (Fin n)).powerset,
        (bernoulliWeight p univ B + bernoulliWeight q univ B) := by
    apply sum_lt_sum
    · intro B hB
      have hBp := bernoulliWeight_nonneg (fun i _ ↦ hp i) (mem_powerset.mp hB)
      have hBq := bernoulliWeight_nonneg (fun i _ ↦ hq i) (mem_powerset.mp hB)
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    · exact ⟨A, by simp, abs_lt.mpr ⟨by linarith, by linarith⟩⟩
  rw [sum_add_distrib, sum_bernoulliWeight, sum_bernoulliWeight] at hs
  unfold productTV
  linarith

theorem tailObjective_eq_tailDiff_of_equal_mass (h : AdmissiblePair p q) (k : ℕ)
    (heq : pbMass p k = pbMass q k) (hpos : 0 < pbMass q k) :
    tailObjective p q = tailDiff p q k := by
  rw [← countTV_eq_tailObjective h]
  apply countTV_eq_tailDiff_of_signs
  · intro l hl
    apply (mul_le_mul_iff_left₀ hpos).mp
    simpa [heq, mul_comm] using pbMass_likelihoodRatio h l k hl.le
  · intro l hl
    apply (mul_le_mul_iff_left₀ hpos).mp
    simpa [heq, mul_comm] using pbMass_likelihoodRatio h k l hl

theorem IsSwitch.tailObjective_eq {n j : ℕ} {γ a b : ℝ}
    (h : IsSwitch n j γ a b) (_hj : 0 < j) (hjn : j < n) :
    tailObjective (fun _ : Fin n ↦ a) (fun _ ↦ b) =
      tailDiff (fun _ : Fin n ↦ a) (fun _ ↦ b) j := by
  apply tailObjective_eq_tailDiff_of_equal_mass
    ((admissiblePair_iff _ _).mpr (fun _ ↦ ⟨h.1.le, h.2.1.le, h.2.2.1.le⟩)) j h.pbMass_eq
  rw [pbMass_const]
  have hc : (0 : ℝ) < n.choose j := by exact_mod_cast Nat.choose_pos hjn.le
  exact mul_pos (mul_pos hc (pow_pos h.1 _)) (pow_pos (by linarith [h.2.1, h.2.2.1]) _)

theorem tailObjective_switchPair {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    tailObjective (fun _ : Fin n ↦ switchUpper n j γ)
      (fun _ ↦ switchLower n j γ) = switchValue n j γ :=
  (switchPair_spec hj hjn hγ0 hγ1).tailObjective_eq hj hjn

theorem IsSwitch.tailObjective_lt_one {n j : ℕ} {γ a b : ℝ}
    (h : IsSwitch n j γ a b) :
    tailObjective (fun _ : Fin n ↦ a) (fun _ ↦ b) < 1 := by
  have hp : ValidParameters (fun _ : Fin n ↦ a) :=
    fun _ ↦ ⟨(h.1.trans h.2.1).le, h.2.2.1.le⟩
  have hq : ValidParameters (fun _ : Fin n ↦ b) :=
    fun _ ↦ ⟨h.1.le, (h.2.1.trans h.2.2.1).le⟩
  apply (tailObjective_le_productTV _ _).trans_lt
    (productTV_lt_one_of_common_atom hp hq ∅ ?_ ?_)
  · simp [bernoulliWeight]
    exact pow_pos (sub_pos.mpr h.2.2.1) n
  · simp [bernoulliWeight]
    exact pow_pos (sub_pos.mpr (h.2.1.trans h.2.2.1)) n

theorem IsSwitch.activeThresholds_eq {n j : ℕ} {γ a b : ℝ}
    (h : IsSwitch n j γ a b) (hj : 0 < j) (hjn : j < n) :
    activeThresholds (fun _ : Fin n ↦ a) (fun _ ↦ b) = {j, j + 1} := by
  let p : Fin n → ℝ := fun _ ↦ a
  let q : Fin n → ℝ := fun _ ↦ b
  have hpq : AdmissiblePair p q :=
    (admissiblePair_iff _ _).mpr (fun _ ↦ ⟨h.1.le, h.2.1.le, h.2.2.1.le⟩)
  have hgap : 0 < meanGap p q := by
    rw [meanGap_const]
    exact mul_pos (by exact_mod_cast (show 0 < n by omega)) (sub_pos.mpr h.2.1)
  have hmax : tailObjective p q = tailDiff p q j := h.tailObjective_eq hj hjn
  have hjmem : j ∈ activeThresholds p q :=
    (mem_activeThresholds p q j).mpr ⟨hj, hjn.le, hmax.symm⟩
  have hjmem' : j + 1 ∈ activeThresholds p q :=
    (mem_activeThresholds p q (j + 1)).mpr ⟨by omega, by omega,
      h.tailDiff_eq.symm.trans hmax.symm⟩
  ext k
  simp only [mem_insert, mem_singleton]
  constructor
  · intro hk
    have hleft := activeThresholds_distance_le_one hpq hgap h.tailObjective_lt_one hk hjmem'
    have hright := activeThresholds_distance_le_one hpq hgap h.tailObjective_lt_one hjmem hk
    omega
  · rintro (rfl | rfl)
    · exact hjmem
    · exact hjmem'

end

end PoissonBinomialComparison

-- CommonStationarity
namespace PoissonBinomialComparison

open scoped BigOperators
open Finset

noncomputable section

variable {ι : Type*} [DecidableEq ι]

theorem adjacent_mass_equal_impossible {p q : ι → ℝ} {s : Finset ι}
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) (hq : ∀ i ∈ s, 0 ≤ q i ∧ q i ≤ 1)
    (hpq : ∀ i ∈ s, q i ≤ p i) (hstrict : ∃ i ∈ s, q i < p i)
    (htop : 0 < pbMassOn p s s.card) (hzero : 0 < pbMassOn q s 0)
    {k : ℕ} (hk : 1 ≤ k) (hks : k ≤ s.card)
    (heq0 : pbMassOn p s (k-1) = pbMassOn q s (k-1))
    (heq1 : pbMassOn p s k = pbMassOn q s k)
    (hpos : 0 < pbMassOn p s (k-1) ∨ 0 < pbMassOn p s k) : False := by
  have hp1 : 0 < pbMassOn p s k := by
    rcases hpos with hprev | hnext
    · exact pbMassOn_positive_between s hp (by omega) hks hprev htop
    · exact hnext
  have hq1 : 0 < pbMassOn q s k := heq1 ▸ hp1
  have hq0 : 0 < pbMassOn q s (k-1) :=
    pbMassOn_positive_between s hq (Nat.zero_le _) (by omega) hzero hq1
  have hcast : ((k-1 : ℕ) : ℤ)+1 = (k : ℤ) := by omega
  have hlr := pbMassIntOn_strict_adjacent s hq hp hpq hstrict ((k-1 : ℕ) : ℤ)
    (by simpa only [pbMassIntOn_natCast] using hq0)
    (by simpa only [hcast,pbMassIntOn_natCast] using hq1)
    (by simpa only [hcast,pbMassIntOn_natCast] using hp1)
  simp only [hcast,pbMassIntOn_natCast,heq0,heq1] at hlr
  nlinarith

variable {n : ℕ} {p q : Fin n → ℝ}

theorem common_parameter_eq_weight (h : AdmissiblePair p q)
    (hp : ∀ i, 0 < p i) (hq : ∀ i, q i < 1)
    {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    {k : ℕ} (hk0 : 1 ≤ k) (hkn : k < n)
    (htie : pbMass p k = pbMass q k)
    (i : Fin n) (hcommon : p i = q i) (hstrict : ∃ j, j ≠ i ∧ q j < p j)
    (hgrad : randomizedGradient p w k i = randomizedGradient q w k i)
    (hpos : 0 < randomizedGradient p w k i) : p i = w := by
  let s := (univ : Finset (Fin n)).erase i
  have hps : ∀ j ∈ s, 0 ≤ p j ∧ p j ≤ 1 := fun j _ ↦ h.1 j
  have hqs : ∀ j ∈ s, 0 ≤ q j ∧ q j ≤ 1 := fun j _ ↦ h.2.1 j
  have hcard : s.card = n-1 := by simp [s]
  have hstrict' : ∃ j ∈ s, q j < p j := by
    obtain ⟨j,hji,hj⟩ := hstrict
    exact ⟨j,by simp [s,hji],hj⟩
  have hpred : k-1+1 = k := by omega
  have hP := pbMass_delete_succ p i (k-1)
  have hQ := pbMass_delete_succ q i (k-1)
  rw [hpred] at hP hQ
  change pbMass p k = (1-p i)*pbMassOn p s k+p i*pbMassOn p s (k-1) at hP
  change pbMass q k = (1-q i)*pbMassOn q s k+q i*pbMassOn q s (k-1) at hQ
  have hG : (1-w)*pbMassOn p s k+w*pbMassOn p s (k-1) =
      (1-w)*pbMassOn q s k+w*pbMassOn q s (k-1) := by
    simpa only [randomizedGradient, randomizedSlopeOn, show k ≠ 0 by omega, ite_false] using hgrad
  have hT : (1-p i)*pbMassOn p s k+p i*pbMassOn p s (k-1) =
      (1-p i)*pbMassOn q s k+p i*pbMassOn q s (k-1) := by
    rw [← hP, hcommon, ← hQ]
    exact htie
  by_contra hneq
  have hdet : p i-w ≠ 0 := sub_ne_zero.mpr hneq
  have h0 : (p i-w)*(pbMassOn p s (k-1)-pbMassOn q s (k-1)) = 0 := by
    linear_combination (1-w)*hT-(1-p i)*hG
  have h1 : (p i-w)*(pbMassOn p s k-pbMassOn q s k) = 0 := by
    linear_combination p i*hG-w*hT
  have heq0 := sub_eq_zero.mp ((mul_eq_zero.mp h0).resolve_left hdet)
  have heq1 := sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_left hdet)
  have hmpos : 0 < pbMassOn p s (k-1) ∨ 0 < pbMassOn p s k := by
    by_contra hnot
    push Not at hnot
    have hnonpos := add_nonpos (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hw1) hnot.2)
      (mul_nonpos_of_nonneg_of_nonpos hw0 hnot.1)
    have hGpos : 0 < (1-w)*pbMassOn p s k+w*pbMassOn p s (k-1) := by
      simpa only [randomizedGradient,randomizedSlopeOn,show k ≠ 0 by omega,ite_false] using hpos
    linarith
  apply adjacent_mass_equal_impossible hps hqs (fun j _ ↦ h.2.2 j) hstrict'
    (by rw [pbMassOn_card_eq_prod]; exact prod_pos (fun j _ ↦ hp j))
    (by rw [pbMassOn_zero]; exact prod_pos (fun j _ ↦ sub_pos.mpr (hq j)))
    hk0 (by omega) heq0 heq1 hmpos

theorem randomizedGradient_eq_mass_of_parameter_eq {p : Fin n → ℝ} {w : ℝ}
    {k : ℕ} (hk : 1 ≤ k) (i : Fin n) (hi : p i = w) :
    randomizedGradient p w k i = pbMass p k := by
  have hp := pbMass_delete_succ p i (k-1)
  rw [show k-1+1 = k by omega, hi] at hp
  simpa [randomizedGradient,randomizedSlopeOn,show k ≠ 0 by omega] using hp.symm

theorem exists_deleted_pair_of_stationary_active (h : AdmissiblePair p q)
    (i : Fin n) (hi : p i = q i) {k : ℕ} (hk : k ∈ activeThresholds p q)
    (heq : pbMassOn p (univ.erase i) (k-1) = pbMassOn q (univ.erase i) (k-1))
    (hpos : 0 < pbMassOn q (univ.erase i) (k-1)) :
    ∃ r t : Fin (n-1) → ℝ, AdmissiblePair r t ∧ meanGap r t = meanGap p q ∧
      tailObjective r t = tailObjective p q := by
  let s := (univ : Finset (Fin n)).erase i
  have hcard : s.card = n-1 := by simp [s]
  have hex : ∃ r t : Fin s.card → ℝ, AdmissiblePair r t ∧ meanGap r t = meanGap p q ∧
      tailObjective r t = tailObjective p q := by
    let r := finsetParameters p s
    let t := finsetParameters q s
    have hrs : AdmissiblePair r t := ⟨valid_finsetParameters _ (fun j _ ↦ h.1 j),
      valid_finsetParameters _ (fun j _ ↦ h.2.1 j), fun _ ↦ h.2.2 _⟩
    have hm : pbMass r (k-1) = pbMass t (k-1) := by
      simpa only [r,t,pbMass_finsetParameters] using heq
    have hmp : 0 < pbMass t (k-1) := by
      simpa only [t,pbMass_finsetParameters] using hpos
    have hmax := tailObjective_eq_tailDiff_of_equal_mass hrs (k-1) hm hmp
    have hk' := (mem_activeThresholds p q k).mp hk
    have hpred : k-1+1 = k := by omega
    have hadj := tailDiff_sub_succ r t (k-1)
    rw [hpred,hm,sub_self] at hadj
    have hrec : tailDiff p q k = (1-p i)*tailDiff r t k+p i*tailDiff r t (k-1) := by
      unfold tailDiff
      simp only [r,t,pbTail_finsetParameters]
      have hP := pbTail_delete_succ p i (k-1)
      have hQ := pbTail_delete_succ q i (k-1)
      rw [hpred] at hP hQ
      rw [hP,hQ,← hi]
      dsimp [s]
      ring
    refine ⟨r,t,hrs,?_,?_⟩
    · simp only [r,t,meanGap,sum_finsetParameters]
      have hP := sum_erase_add univ p (mem_univ i)
      have hQ := sum_erase_add univ q (mem_univ i)
      dsimp [s]
      linarith
    · rw [hmax,← hk'.2.2,hrec]
      rw [sub_eq_zero.mp hadj]
      ring
  rwa [hcard] at hex

end

end PoissonBinomialComparison

-- DeletionObjective
namespace PoissonBinomialComparison

open Finset
open scoped BigOperators

theorem exists_deleted_common_pair {n : ℕ} {p q : Fin n → ℝ}
    (h : AdmissiblePair p q) (i : Fin n) (heq : p i = q i) :
    ∃ r s : Fin (n - 1) → ℝ, AdmissiblePair r s ∧ meanGap r s = meanGap p q ∧
      ∀ k, tailDiff p q (k + 1) =
        (1 - p i) * tailDiff r s (k + 1) + p i * tailDiff r s k := by
  let u := (univ.erase i : Finset (Fin n))
  have hcard : u.card = n - 1 := by simp [u]
  have hex : ∃ r s : Fin u.card → ℝ, AdmissiblePair r s ∧
      meanGap r s = meanGap p q ∧ ∀ k, tailDiff p q (k + 1) =
        (1 - p i) * tailDiff r s (k + 1) + p i * tailDiff r s k := by
    refine ⟨finsetParameters p u, finsetParameters q u, ?_, ?_, ?_⟩
    · exact ⟨valid_finsetParameters _ (fun j _ => h.1 j),
        valid_finsetParameters _ (fun j _ => h.2.1 j), fun j => h.2.2 _⟩
    · simp only [meanGap, sum_finsetParameters]
      have hp := sum_erase_add univ p (mem_univ i)
      have hq := sum_erase_add univ q (mem_univ i)
      dsimp [u]
      linarith
    · intro k
      simp only [tailDiff, pbTail_finsetParameters]
      rw [pbTail_delete_succ p i, pbTail_delete_succ q i, ← heq]
      dsimp [u]
      ring
  rwa [hcard] at hex

theorem exists_deleted_deterministic_pair {n : ℕ} (hn : 2 ≤ n) {p q : Fin n → ℝ}
    (h : AdmissiblePair p q) (i : Fin n) (heq : p i = q i)
    (hdet : p i = 0 ∨ p i = 1) :
    ∃ r s : Fin (n - 1) → ℝ, AdmissiblePair r s ∧ meanGap r s = meanGap p q ∧
      tailObjective r s = tailObjective p q := by
  obtain ⟨r,s,hrs,hgap,hrec⟩ := exists_deleted_common_pair h i heq
  refine ⟨r,s,hrs,hgap,le_antisymm ?_ ?_⟩
  · obtain ⟨k,hk,hmax⟩ := tailObjective_attained r s (by omega)
    rcases hdet with hz | ho
    · have he := hrec (k-1)
      have hk1 : k - 1 + 1 = k := by have := (mem_Icc.mp hk).1; omega
      simp only [hz, sub_zero, one_mul, zero_mul, add_zero, hk1] at he
      rw [hmax, ← he]
      exact tailDiff_le_tailObjective p q (mem_Icc.mpr ⟨(mem_Icc.mp hk).1, by have := (mem_Icc.mp hk).2; omega⟩)
    · have he := hrec k
      simp only [ho, sub_self, zero_mul, one_mul, zero_add] at he
      rw [hmax, ← he]
      exact tailDiff_le_tailObjective p q (mem_Icc.mpr ⟨by omega, by have := (mem_Icc.mp hk).2; omega⟩)
  · apply (tailObjective_le_iff p q (by omega) _).mpr
    intro k hk
    have hk0 := (mem_Icc.mp hk).1
    have hkn := (mem_Icc.mp hk).2
    have he := hrec (k-1)
    have hk1 : k - 1 + 1 = k := by omega
    rw [hk1] at he
    rcases hdet with hz | ho
    · simp only [hz, sub_zero, one_mul, zero_mul, add_zero] at he
      rw [he]
      by_cases hkm : k ≤ n-1
      · exact tailDiff_le_tailObjective r s (mem_Icc.mpr ⟨hk0,hkm⟩)
      · have hz' : tailDiff r s k = 0 := by
          simp [tailDiff, pbTail_eq_zero_of_lt r (by omega : n-1 < k),
            pbTail_eq_zero_of_lt s (by omega : n-1 < k)]
        rw [hz']
        exact (tailDiff_nonneg hrs 1).trans (tailDiff_le_tailObjective r s (by simp; omega))
    · simp only [ho, sub_self, zero_mul, one_mul, zero_add] at he
      rw [he]
      by_cases hk2 : 1 ≤ k-1
      · exact tailDiff_le_tailObjective r s (mem_Icc.mpr ⟨hk2, by omega⟩)
      · have hkz : k-1 = 0 := by omega
        simp only [hkz, tailDiff, pbTail_zero, sub_self]
        exact (tailDiff_nonneg hrs 1).trans (tailDiff_le_tailObjective r s (by simp; omega))

end PoissonBinomialComparison

-- BinomialAtom
namespace PoissonBinomialComparison

open scoped BigOperators

noncomputable section

def integerMeanBinomialMass (M ℓ : ℕ) : ℝ :=
  (M.choose ℓ : ℝ) * ((ℓ : ℝ) / M) ^ ℓ * (1 - (ℓ : ℝ) / M) ^ (M - ℓ)

def kappa (n : ℕ) : ℝ := integerMeanBinomialMass n (n / 2)

def atomLogIncrement (x : ℝ) : ℝ := x * Real.log (1 + x⁻¹)

private def atomFactor (m : ℕ) : ℝ := (m : ℝ) ^ m / (m.factorial : ℝ)

private theorem atomFactor_pos (m : ℕ) : 0 < atomFactor m := by
  cases m with
  | zero => norm_num [atomFactor]
  | succ m => unfold atomFactor; positivity

@[simp] theorem atomLogIncrement_zero : atomLogIncrement 0 = 0 := by
  simp [atomLogIncrement]

theorem hasDerivAt_atomLogIncrement {x : ℝ} (hx : 0 < x) :
    HasDerivAt atomLogIncrement (Real.log (1 + x⁻¹) - (x + 1)⁻¹) x := by
  have hxne := hx.ne'
  have hne : 1 + x⁻¹ ≠ 0 := by positivity
  have hd := (hasDerivAt_id x).mul (((hasDerivAt_inv hxne).const_add 1).log hne)
  convert! hd using 1
  · simp only [one_mul, id_eq]
    field_simp
    ring

theorem atomLogIncrement_deriv_nonneg {x : ℝ} (hx : 0 < x) :
    0 ≤ deriv atomLogIncrement x := by
  rw [(hasDerivAt_atomLogIncrement hx).deriv]
  have h := Real.one_sub_inv_le_log_of_pos (show 0 < 1 + x⁻¹ by positivity)
  have heq : 1 - (1 + x⁻¹)⁻¹ = (x + 1)⁻¹ := by
    have hxne := hx.ne'
    have hx1 : x + 1 ≠ 0 := by positivity
    field_simp
    ring
  rw [heq] at h
  exact sub_nonneg.mpr h

theorem atomLogIncrement_mono : MonotoneOn atomLogIncrement (Set.Ici 0) := by
  have hmono : MonotoneOn atomLogIncrement (Set.Ioi 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioi 0)
    · intro x hx
      exact (hasDerivAt_atomLogIncrement hx).continuousAt.continuousWithinAt
    · intro x hx
      exact (hasDerivAt_atomLogIncrement (interior_subset hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      exact atomLogIncrement_deriv_nonneg (interior_subset hx)
  intro x hx y hy hxy
  by_cases hx0 : x = 0
  · subst x
    rw [atomLogIncrement_zero]
    exact mul_nonneg hy (Real.log_nonneg (by have := inv_nonneg.mpr (show 0 ≤ y from hy); linarith))
  · exact hmono (lt_of_le_of_ne hx (Ne.symm hx0))
      ((lt_of_le_of_ne hx (Ne.symm hx0)).trans_le hxy) hxy

private theorem atomLogIncrement_nat (m : ℕ) :
    atomLogIncrement m = (m : ℝ) * (Real.log (m + 1) - Real.log m) := by
  cases m with
  | zero => simp
  | succ m =>
    have hm : (m + 1 : ℝ) ≠ 0 := by positivity
    have hid : 1 + (m + 1 : ℝ)⁻¹ = ((m + 1 : ℝ) + 1) / (m + 1 : ℝ) := by
      field_simp
    simp only [atomLogIncrement, Nat.cast_add, Nat.cast_one]
    rw [hid, Real.log_div (by positivity) hm]

private theorem log_atomFactor_succ (m : ℕ) :
    Real.log (atomFactor (m + 1)) - Real.log (atomFactor m) = atomLogIncrement m := by
  have hmfact : (m.factorial : ℝ) ≠ 0 := by positivity
  have hm1fact : ((m + 1).factorial : ℝ) ≠ 0 := by positivity
  have hpow : (m : ℝ) ^ m ≠ 0 := by
    cases m with
    | zero => simp
    | succ m => positivity
  have hpow1 : ((m + 1 : ℕ) : ℝ) ^ (m + 1) ≠ 0 := by positivity
  rw [atomFactor, atomFactor, Real.log_div hpow1 hm1fact, Real.log_div hpow hmfact,
    Real.log_pow, Real.log_pow, Nat.factorial_succ, Nat.cast_mul,
    Real.log_mul (by positivity) hmfact, atomLogIncrement_nat]
  simp only [Nat.cast_add, Nat.cast_one]
  ring

theorem integerMeanBinomialMass_eq_pbMass (M ℓ : ℕ) :
    integerMeanBinomialMass M ℓ = pbMass (fun _ : Fin M ↦ (ℓ : ℝ) / M) ℓ := by
  rw [pbMass_const]
  rfl

private theorem integerMeanBinomialMass_factor {M ℓ : ℕ} (hℓ : ℓ ≤ M) :
    integerMeanBinomialMass M ℓ = atomFactor ℓ * atomFactor (M - ℓ) / atomFactor M := by
  by_cases hM : M = 0
  · subst M
    have hℓ0 : ℓ = 0 := by omega
    subst ℓ
    norm_num [integerMeanBinomialMass, atomFactor]
  have hMn : (M : ℝ) ≠ 0 := by exact_mod_cast hM
  have hMpow : (M : ℝ) ^ M ≠ 0 := pow_ne_zero M hMn
  have hlfact : (ℓ.factorial : ℝ) ≠ 0 := by positivity
  have hrfact : ((M - ℓ).factorial : ℝ) ≠ 0 := by positivity
  have hMfact : (M.factorial : ℝ) ≠ 0 := by positivity
  have hfactor : (M.choose ℓ : ℝ) * (ℓ.factorial : ℝ) * ((M - ℓ).factorial : ℝ) = M.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hℓ
  have hchoose : (M.choose ℓ : ℝ) = (M.factorial : ℝ) /
      ((ℓ.factorial : ℝ) * ((M - ℓ).factorial : ℝ)) := by
    apply (eq_div_iff (mul_ne_zero hlfact hrfact)).mpr
    simpa only [mul_assoc] using hfactor
  have hfrac : 1 - (ℓ : ℝ) / M = ((M - ℓ : ℕ) : ℝ) / M := by
    rw [Nat.cast_sub hℓ]
    field_simp
  have hpower : (M : ℝ) ^ ℓ * (M : ℝ) ^ (M - ℓ) = (M : ℝ) ^ M := by
    rw [← pow_add, Nat.add_sub_of_le hℓ]
  unfold integerMeanBinomialMass atomFactor
  rw [hchoose, hfrac, div_pow, div_pow]
  field_simp
  rw [← hpower]
  ring

theorem integerMeanBinomialMass_pos {M ℓ : ℕ} (hℓ : ℓ ≤ M) :
    0 < integerMeanBinomialMass M ℓ := by
  rw [integerMeanBinomialMass_factor hℓ]
  exact div_pos (mul_pos (atomFactor_pos ℓ) (atomFactor_pos (M - ℓ))) (atomFactor_pos M)

private theorem log_integerMeanBinomialMass {M ℓ : ℕ} (hℓ : ℓ ≤ M) :
    Real.log (integerMeanBinomialMass M ℓ) =
      Real.log (atomFactor ℓ) + Real.log (atomFactor (M - ℓ)) - Real.log (atomFactor M) := by
  rw [integerMeanBinomialMass_factor hℓ,
    Real.log_div (mul_ne_zero (atomFactor_pos ℓ).ne' (atomFactor_pos (M - ℓ)).ne')
      (atomFactor_pos M).ne', Real.log_mul (atomFactor_pos ℓ).ne' (atomFactor_pos (M - ℓ)).ne']

theorem integerMeanBinomialMass_log_step_count {M ℓ : ℕ} (hℓ : ℓ + 1 ≤ M) :
    Real.log (integerMeanBinomialMass M ℓ) - Real.log (integerMeanBinomialMass M (ℓ + 1)) =
      atomLogIncrement (M - ℓ - 1 : ℕ) - atomLogIncrement ℓ := by
  rw [log_integerMeanBinomialMass (by omega), log_integerMeanBinomialMass hℓ]
  have h1 := log_atomFactor_succ ℓ
  have h2 := log_atomFactor_succ (M - ℓ - 1)
  have hr : M - ℓ - 1 + 1 = M - ℓ := by omega
  have hr' : M - (ℓ + 1) = M - ℓ - 1 := by omega
  rw [hr] at h2
  rw [hr']
  linarith

theorem integerMeanBinomialMass_log_step_dimension {M ℓ : ℕ} (hℓ : ℓ ≤ M) :
    Real.log (integerMeanBinomialMass (M + 1) ℓ) - Real.log (integerMeanBinomialMass M ℓ) =
      atomLogIncrement (M - ℓ : ℕ) - atomLogIncrement M := by
  rw [log_integerMeanBinomialMass (by omega), log_integerMeanBinomialMass hℓ]
  have h1 := log_atomFactor_succ M
  have h2 := log_atomFactor_succ (M - ℓ)
  have hr : M + 1 - ℓ = (M - ℓ) + 1 := by omega
  rw [hr]
  linarith

theorem integerMeanBinomialMass_symm {M ℓ : ℕ} (hℓ : ℓ ≤ M) :
    integerMeanBinomialMass M (M - ℓ) = integerMeanBinomialMass M ℓ := by
  rw [integerMeanBinomialMass_factor (by omega), integerMeanBinomialMass_factor hℓ,
    Nat.sub_sub_self hℓ]
  ring

theorem integerMeanBinomialMass_succ_count_le {M ℓ : ℕ} (hℓ : ℓ < M / 2) :
    integerMeanBinomialMass M (ℓ + 1) ≤ integerMeanBinomialMass M ℓ := by
  have hℓM : ℓ + 1 ≤ M := by omega
  apply (Real.log_le_log_iff (integerMeanBinomialMass_pos hℓM)
    (integerMeanBinomialMass_pos (by omega))).mp
  have h := integerMeanBinomialMass_log_step_count hℓM
  have hinc : atomLogIncrement (ℓ : ℝ) ≤ atomLogIncrement ((M - ℓ - 1 : ℕ) : ℝ) := by
    apply atomLogIncrement_mono (by simp) (by simp)
    exact_mod_cast (show ℓ ≤ M - ℓ - 1 by omega)
  linarith

private theorem integerMeanBinomialMass_central_le_of_le_half {M ℓ : ℕ}
    (hℓ : ℓ ≤ M / 2) : integerMeanBinomialMass M (M / 2) ≤ integerMeanBinomialMass M ℓ := by
  by_cases heq : ℓ = M / 2
  · simp [heq]
  · have hlt : ℓ < M / 2 := by omega
    exact (integerMeanBinomialMass_central_le_of_le_half (ℓ := ℓ + 1) (by omega)).trans
      (integerMeanBinomialMass_succ_count_le hlt)
termination_by M / 2 - ℓ
decreasing_by omega

theorem kappa_le_integerMeanBinomialMass {M ℓ : ℕ} (hℓ : ℓ ≤ M) :
    kappa M ≤ integerMeanBinomialMass M ℓ := by
  unfold kappa
  by_cases hhalf : ℓ ≤ M / 2
  · exact integerMeanBinomialMass_central_le_of_le_half hhalf
  · have hother : M - ℓ ≤ M / 2 := by omega
    simpa only [integerMeanBinomialMass_symm hℓ] using
      integerMeanBinomialMass_central_le_of_le_half hother

theorem integerMeanBinomialMass_succ_dimension_le {M ℓ : ℕ} (hℓ : ℓ ≤ M) :
    integerMeanBinomialMass (M + 1) ℓ ≤ integerMeanBinomialMass M ℓ := by
  apply (Real.log_le_log_iff (integerMeanBinomialMass_pos (by omega))
    (integerMeanBinomialMass_pos hℓ)).mp
  have h := integerMeanBinomialMass_log_step_dimension hℓ
  have hinc : atomLogIncrement ((M - ℓ : ℕ) : ℝ) ≤ atomLogIncrement (M : ℝ) := by
    apply atomLogIncrement_mono (by simp) (by simp)
    exact_mod_cast Nat.sub_le M ℓ
  linarith

theorem integerMeanBinomialMass_antitone_dimension {M n ℓ : ℕ}
    (hℓ : ℓ ≤ M) (hMn : M ≤ n) :
    integerMeanBinomialMass n ℓ ≤ integerMeanBinomialMass M ℓ := by
  have hanti : AntitoneOn (fun j ↦ integerMeanBinomialMass j ℓ) (Set.Ici ℓ) :=
    antitoneOn_nat_Ici_of_succ_le (fun j hj ↦ integerMeanBinomialMass_succ_dimension_le hj)
  exact hanti hℓ (hℓ.trans hMn) hMn

theorem kappa_le_integerMeanBinomialMass_of_le {n M ℓ : ℕ}
    (hℓ : ℓ ≤ M) (hMn : M ≤ n) :
    kappa n ≤ integerMeanBinomialMass M ℓ :=
  (kappa_le_integerMeanBinomialMass (hℓ.trans hMn)).trans
    (integerMeanBinomialMass_antitone_dimension hℓ hMn)

theorem kappa_le_pbMass_integerMean {n M ℓ : ℕ} (hℓ : ℓ ≤ M) (hMn : M ≤ n) :
    kappa n ≤ pbMass (fun _ : Fin M ↦ (ℓ : ℝ) / M) ℓ := by
  rw [← integerMeanBinomialMass_eq_pbMass]
  exact kappa_le_integerMeanBinomialMass_of_le hℓ hMn

theorem kappa_pos (n : ℕ) : 0 < kappa n :=
  integerMeanBinomialMass_pos (Nat.div_le_self n 2)

theorem kappa_le_one (n : ℕ) : kappa n ≤ 1 := by
  have h := kappa_le_integerMeanBinomialMass_of_le (n := n) (M := 0) (ℓ := 0)
    (by omega) (by omega)
  simpa [integerMeanBinomialMass] using h

theorem kappa_eq_formula {n : ℕ} (hn : 0 < n) :
    kappa n = (n.choose (n / 2) : ℝ) * (((n / 2 : ℕ) : ℝ) / n) ^ (n / 2) *
      ((((n + 1) / 2 : ℕ) : ℝ) / n) ^ ((n + 1) / 2) := by
  have hsub : n - n / 2 = (n + 1) / 2 := by omega
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hfrac : 1 - ((n / 2 : ℕ) : ℝ) / n = (((n + 1) / 2 : ℕ) : ℝ) / n := by
    rw [← hsub, Nat.cast_sub (Nat.div_le_self n 2)]
    field_simp
  simp only [kappa, integerMeanBinomialMass, hsub, hfrac]

end

end PoissonBinomialComparison

-- Adjoining
namespace PoissonBinomialComparison

open scoped BigOperators
open Finset

noncomputable section

theorem MassCrossInequalities.prefix_order {f : ℤ → ℝ}
    (hc : MassCrossInequalities f) (hf : ∀ j, 0 ≤ f j) {k : ℤ}
    (hk : 0 < f k) (hadj : f (k - 1) ≤ f k) :
    ∀ j ≤ k, f (j - 1) ≤ f j := by
  intro j hj
  by_cases heq : j = k
  · simpa [heq] using hadj
  have hcross := hc j (k - 1) (by omega)
  simp only [show k - 1 + 1 = k by omega] at hcross
  have hmul := mul_le_mul_of_nonneg_left hadj (hf j)
  exact (mul_le_mul_iff_left₀ hk).mp (hcross.trans hmul)

private theorem prefix_order_le {f : ℤ → ℝ} {k j : ℤ}
    (h : ∀ l ≤ k, f (l - 1) ≤ f l) (hj : j ≤ k) : f j ≤ f k := by
  by_cases heq : j = k
  · simp [heq]
  have hstep : f j ≤ f (j + 1) := by simpa using h (j + 1) (by omega)
  exact hstep.trans (prefix_order_le h (j := j + 1) (by omega))
termination_by (k - j).toNat
decreasing_by omega

variable {ι : Type*} [DecidableEq ι]

theorem pbMassIntOn_insert_le {p : ι → ℝ} {s : Finset ι} {i : ι}
    (hi : i ∉ s) (hpi : 0 ≤ p i) (k : ℤ)
    (hadj : pbMassIntOn p s (k - 1) ≤ pbMassIntOn p s k) :
    pbMassIntOn p (insert i s) k ≤ pbMassIntOn p s k := by
  rw [pbMassIntOn_insert p hi]
  have h := mul_le_mul_of_nonneg_left hadj hpi
  linarith

theorem pbMassIntOn_insert_lt {p : ι → ℝ} {s : Finset ι} {i : ι}
    (hi : i ∉ s) (hpi : 0 < p i) (k : ℤ)
    (hadj : pbMassIntOn p s (k - 1) < pbMassIntOn p s k) :
    pbMassIntOn p (insert i s) k < pbMassIntOn p s k := by
  rw [pbMassIntOn_insert p hi]
  have h := mul_lt_mul_of_pos_left hadj hpi
  linarith

theorem pbMassIntOn_insert_prefix_order {p : ι → ℝ} {s : Finset ι} {i : ι}
    (hi : i ∉ s) (hpi : 0 ≤ p i ∧ p i ≤ 1) (k : ℤ)
    (hprefix : ∀ j ≤ k, pbMassIntOn p s (j - 1) ≤ pbMassIntOn p s j) :
    ∀ j ≤ k, pbMassIntOn p (insert i s) (j - 1) ≤ pbMassIntOn p (insert i s) j := by
  intro j hj
  rw [pbMassIntOn_insert p hi, pbMassIntOn_insert p hi]
  exact add_le_add
    (mul_le_mul_of_nonneg_left (hprefix j hj) (sub_nonneg.mpr hpi.2))
    (mul_le_mul_of_nonneg_left (hprefix (j - 1) (by omega)) hpi.1)

theorem pbMassIntOn_insert_adjacent_le {p : ι → ℝ} {s : Finset ι} {i : ι}
    (hi : i ∉ s) (hp : ∀ j ∈ s, 0 ≤ p j ∧ p j ≤ 1)
    (hpi : 0 ≤ p i ∧ p i ≤ 1) (k : ℤ)
    (hk : 0 < pbMassIntOn p s k)
    (hadj : pbMassIntOn p s (k - 1) ≤ pbMassIntOn p s k) :
    pbMassIntOn p (insert i s) (k - 1) ≤ pbMassIntOn p (insert i s) k := by
  exact pbMassIntOn_insert_prefix_order hi hpi k
    ((pbMassIntOn_cross s hp).prefix_order (pbMassIntOn_nonneg hp) hk hadj) k le_rfl

theorem pbMassIntOn_insert_eq_of_tie {p : ι → ℝ} {s : Finset ι} {i : ι}
    (hi : i ∉ s) (k : ℤ)
    (htie : pbMassIntOn p s (k - 1) = pbMassIntOn p s k) :
    pbMassIntOn p (insert i s) k = pbMassIntOn p s k := by
  rw [pbMassIntOn_insert p hi, htie]
  ring

theorem pbMassIntOn_insert_adjacent_lt_of_tie {p : ι → ℝ} {s : Finset ι} {i : ι}
    (hi : i ∉ s) (hp : ∀ j ∈ s, 0 ≤ p j ∧ p j ≤ 1) (hpi : 0 < p i)
    (k : ℤ) (hk : 0 < pbMassIntOn p s k)
    (htie : pbMassIntOn p s (k - 1) = pbMassIntOn p s k) :
    pbMassIntOn p (insert i s) (k - 1) < pbMassIntOn p (insert i s) k := by
  have hprev : 0 < pbMassIntOn p s (k - 1) := by rw [htie]; exact hk
  have hstrict := pbMassIntOn_strictLogConcavity s hp (k - 1) hprev
  simp only [show k - 1 + 1 = k by omega, htie, pow_two] at hstrict
  have hsmall : pbMassIntOn p s (k - 1 - 1) < pbMassIntOn p s k :=
    (mul_lt_mul_iff_left₀ hk).mp hstrict
  rw [pbMassIntOn_insert_eq_of_tie hi k htie, pbMassIntOn_insert p hi, htie]
  have hmul := mul_lt_mul_of_pos_left hsmall hpi
  linarith

theorem pbMassIntOn_insert_insert_lt_of_tie {p : ι → ℝ} {s : Finset ι} {i j : ι}
    (hi : i ∉ s) (hj : j ∉ s) (hij : i ≠ j)
    (hp : ∀ l ∈ s, 0 ≤ p l ∧ p l ≤ 1) (hpi : 0 < p i) (hpj : 0 < p j)
    (k : ℤ) (hk : 0 < pbMassIntOn p s k)
    (htie : pbMassIntOn p s (k - 1) = pbMassIntOn p s k) :
    pbMassIntOn p (insert j (insert i s)) k < pbMassIntOn p s k := by
  have hj' : j ∉ insert i s := by simp [hj, Ne.symm hij]
  have hlt := pbMassIntOn_insert_lt hj' hpj k
    (pbMassIntOn_insert_adjacent_lt_of_tie hi hp hpi k hk htie)
  rwa [pbMassIntOn_insert_eq_of_tie hi k htie] at hlt

theorem pbMassIntOn_union_prefix_order {p : ι → ℝ} (s t : Finset ι)
    (hp : ∀ j ∈ s ∪ t, 0 ≤ p j ∧ p j ≤ 1) (k : ℤ)
    (hprefix : ∀ j ≤ k, pbMassIntOn p s (j - 1) ≤ pbMassIntOn p s j) :
    pbMassIntOn p (s ∪ t) k ≤ pbMassIntOn p s k ∧
      ∀ j ≤ k, pbMassIntOn p (s ∪ t) (j - 1) ≤ pbMassIntOn p (s ∪ t) j := by
  induction t using Finset.induction_on with
  | empty => simpa using And.intro (le_refl (pbMassIntOn p s k)) hprefix
  | @insert i t hi ih =>
    have hps : ∀ j ∈ s ∪ t, 0 ≤ p j ∧ p j ≤ 1 := by
      intro j hj
      exact hp j (by simp only [mem_union, mem_insert] at hj ⊢; tauto)
    obtain ⟨hle, hpre⟩ := ih hps
    have hpi : 0 ≤ p i ∧ p i ≤ 1 := hp i (by simp)
    rw [union_insert]
    by_cases him : i ∈ s ∪ t
    · rw [insert_eq_of_mem him]
      exact ⟨hle, hpre⟩
    · exact ⟨(pbMassIntOn_insert_le him hpi.1 k (hpre k le_rfl)).trans hle,
        pbMassIntOn_insert_prefix_order him hpi k hpre⟩

theorem pbMassIntOn_union_le_of_adjacent {p : ι → ℝ} (s t : Finset ι)
    (hp : ∀ j ∈ s ∪ t, 0 ≤ p j ∧ p j ≤ 1) (k : ℤ)
    (hk : 0 < pbMassIntOn p s k)
    (hadj : pbMassIntOn p s (k - 1) ≤ pbMassIntOn p s k) :
    pbMassIntOn p (s ∪ t) k ≤ pbMassIntOn p s k := by
  have hps : ∀ j ∈ s, 0 ≤ p j ∧ p j ≤ 1 := fun j hj ↦ hp j (mem_union_left t hj)
  exact (pbMassIntOn_union_prefix_order s t hp k
    ((pbMassIntOn_cross s hps).prefix_order (pbMassIntOn_nonneg hps) hk hadj)).1

theorem pbMassIntOn_union_lt_of_two_positive_of_tie {p : ι → ℝ} (s t : Finset ι)
    {i j : ι} (hi : i ∉ s) (hj : j ∉ s) (hij : i ≠ j)
    (hp : ∀ l ∈ insert j (insert i s) ∪ t, 0 ≤ p l ∧ p l ≤ 1)
    (hpi : 0 < p i) (hpj : 0 < p j) (k : ℤ)
    (hk : 0 < pbMassIntOn p s k)
    (htie : pbMassIntOn p s (k - 1) = pbMassIntOn p s k) :
    pbMassIntOn p (insert j (insert i s) ∪ t) k < pbMassIntOn p s k := by
  have hps : ∀ l ∈ s, 0 ≤ p l ∧ p l ≤ 1 :=
    fun l hl ↦ hp l (mem_union_left t (mem_insert_of_mem (mem_insert_of_mem hl)))
  have hpi' : 0 ≤ p i ∧ p i ≤ 1 := hp i (by simp)
  have hpj' : 0 ≤ p j ∧ p j ≤ 1 := hp j (by simp)
  have hj' : j ∉ insert i s := by simp [hj, Ne.symm hij]
  have hprefix := (pbMassIntOn_cross s hps).prefix_order
    (pbMassIntOn_nonneg hps) hk htie.le
  have hprefix' := pbMassIntOn_insert_prefix_order hj' hpj' k
    (pbMassIntOn_insert_prefix_order hi hpi' k hprefix)
  exact (pbMassIntOn_union_prefix_order (insert j (insert i s)) t hp k hprefix').1.trans_lt
    (pbMassIntOn_insert_insert_lt_of_tie hi hj hij hps hpi hpj k hk htie)

theorem pbMassIntOn_zero_below_of_union_eq_zero {p : ι → ℝ} (s t : Finset ι)
    (hp : ∀ j ∈ s ∪ t, 0 ≤ p j ∧ p j ≤ 1) (k : ℤ)
    (hk : 0 < pbMassIntOn p s k)
    (hadj : pbMassIntOn p s (k - 1) ≤ pbMassIntOn p s k)
    (hzero : pbMassIntOn p (s ∪ t) k = 0) :
    ∀ j ≤ k, pbMassIntOn p (s ∪ t) j = 0 := by
  have hps : ∀ j ∈ s, 0 ≤ p j ∧ p j ≤ 1 := fun j hj ↦ hp j (mem_union_left t hj)
  have hprefix := (pbMassIntOn_union_prefix_order s t hp k
    ((pbMassIntOn_cross s hps).prefix_order (pbMassIntOn_nonneg hps) hk hadj)).2
  intro j hj
  apply le_antisymm
  · simpa only [hzero] using prefix_order_le hprefix hj
  · exact pbMassIntOn_nonneg hp j

theorem pbMassIntOn_union_zero_of_zero_below (p : ι → ℝ) (s t : Finset ι) (k : ℤ)
    (hzero : ∀ j ≤ k, pbMassIntOn p s j = 0) :
    ∀ j ≤ k, pbMassIntOn p (s ∪ t) j = 0 := by
  induction t using Finset.induction_on with
  | empty => simpa using hzero
  | @insert i t hi ih =>
    rw [union_insert]
    by_cases him : i ∈ s ∪ t
    · simpa [insert_eq_of_mem him] using ih
    · intro j hj
      rw [pbMassIntOn_insert p him, ih j hj, ih (j - 1) (by omega)]
      ring

theorem pbMassIntOn_union_le_of_deleted_adjacent {p : ι → ℝ} (s t : Finset ι)
    {i : ι} (hi : i ∉ s)
    (hp : ∀ j ∈ insert i s ∪ t, 0 ≤ p j ∧ p j ≤ 1) (k : ℤ)
    (hk : 0 < pbMassIntOn p (insert i s) k)
    (hadj : pbMassIntOn p s (k - 1) ≤ pbMassIntOn p s k) :
    pbMassIntOn p (insert i s ∪ t) k ≤ pbMassIntOn p (insert i s) k := by
  have hps : ∀ j ∈ s, 0 ≤ p j ∧ p j ≤ 1 :=
    fun j hj ↦ hp j (mem_union_left t (mem_insert_of_mem hj))
  have hpi : 0 ≤ p i ∧ p i ≤ 1 := hp i (by simp)
  have hbase : 0 < pbMassIntOn p s k :=
    hk.trans_le (pbMassIntOn_insert_le hi hpi.1 k hadj)
  exact pbMassIntOn_union_le_of_adjacent (insert i s) t hp k hk
    (pbMassIntOn_insert_adjacent_le hi hps hpi k hbase hadj)

end

end PoissonBinomialComparison

-- HomogeneousBlock
namespace PoissonBinomialComparison

open scoped BigOperators
open Finset

noncomputable section

variable {ι : Type*} [DecidableEq ι]

def homogeneousBlockMass (p : ι → ℝ) (s : Finset ι) : ℕ → ℝ → ℤ → ℝ
  | 0, _, k => pbMassIntOn p s k
  | M + 1, t, k => (1 - t) * homogeneousBlockMass p s M t k +
      t * homogeneousBlockMass p s M t (k - 1)

@[simp] theorem homogeneousBlockMass_zero (p : ι → ℝ) (s : Finset ι) (t : ℝ) (k : ℤ) :
    homogeneousBlockMass p s 0 t k = pbMassIntOn p s k := rfl

theorem homogeneousBlockMass_succ (p : ι → ℝ) (s : Finset ι)
    (M : ℕ) (t : ℝ) (k : ℤ) :
    homogeneousBlockMass p s (M + 1) t k =
      (1 - t) * homogeneousBlockMass p s M t k +
        t * homogeneousBlockMass p s M t (k - 1) := rfl

theorem homogeneousBlockMass_eq_union (p : ι → ℝ) (s u : Finset ι)
    (hdisj : Disjoint s u) (t : ℝ) (hconst : ∀ i ∈ u, p i = t) (k : ℤ) :
    homogeneousBlockMass p s u.card t k = pbMassIntOn p (s ∪ u) k := by
  induction u using Finset.induction_on generalizing k with
  | empty => simp
  | @insert i u hi ih =>
    have hdi : i ∉ s := by
      intro his
      exact disjoint_left.mp hdisj his (mem_insert_self i u)
    have hdu : Disjoint s u := hdisj.mono_right (subset_insert i u)
    have hcu : ∀ j ∈ u, p j = t := fun j hj ↦ hconst j (mem_insert_of_mem hj)
    have hpi := hconst i (mem_insert_self i u)
    rw [card_insert_of_notMem hi, homogeneousBlockMass_succ,
      ih hdu hcu k, ih hdu hcu (k - 1), union_insert,
      pbMassIntOn_insert p (by simp [hdi, hi]), hpi]

theorem homogeneousBlockMass_insert (p : ι → ℝ) {s : Finset ι} {i : ι}
    (hi : i ∉ s) (M : ℕ) (t : ℝ) (k : ℤ) :
    homogeneousBlockMass p (insert i s) M t k =
      (1 - p i) * homogeneousBlockMass p s M t k +
        p i * homogeneousBlockMass p s M t (k - 1) := by
  induction M generalizing k with
  | zero => exact pbMassIntOn_insert p hi k
  | succ M ih =>
    simp only [homogeneousBlockMass_succ, ih]
    ring

theorem homogeneousBlockMass_nonneg {p : ι → ℝ} {s : Finset ι}
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) (M : ℕ) {t : ℝ}
    (ht : 0 ≤ t ∧ t ≤ 1) (k : ℤ) : 0 ≤ homogeneousBlockMass p s M t k := by
  induction M generalizing k with
  | zero => exact pbMassIntOn_nonneg hp k
  | succ M ih =>
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr ht.2) (ih k))
      (mul_nonneg ht.1 (ih (k - 1)))

theorem homogeneousBlockMass_cross {p : ι → ℝ} {s : Finset ι}
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) (M : ℕ) {t : ℝ}
    (ht : 0 ≤ t ∧ t ≤ 1) : MassCrossInequalities (homogeneousBlockMass p s M t) := by
  induction M with
  | zero => exact pbMassIntOn_cross s hp
  | succ M ih => exact ih.convolve ht.1 (sub_nonneg.mpr ht.2)

theorem homogeneousBlockMass_strictLogConcavity {p : ι → ℝ} {s : Finset ι}
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) (M : ℕ) {t : ℝ}
    (ht : 0 ≤ t ∧ t ≤ 1) : StrictMassLogConcavity (homogeneousBlockMass p s M t) := by
  induction M with
  | zero => exact pbMassIntOn_strictLogConcavity s hp
  | succ M ih =>
    exact ih.convolve (homogeneousBlockMass_nonneg hp M ht)
      (homogeneousBlockMass_cross hp M ht) ht.1 (sub_nonneg.mpr ht.2)

theorem hasDerivAt_homogeneousBlockMass_succ (p : ι → ℝ) (s : Finset ι)
    (M : ℕ) (t : ℝ) (k : ℤ) :
    HasDerivAt (fun u ↦ homogeneousBlockMass p s (M + 1) u k)
      ((M + 1 : ℕ) * (homogeneousBlockMass p s M t (k - 1) -
        homogeneousBlockMass p s M t k)) t := by
  induction M generalizing k with
  | zero =>
    have hd := (((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).mul
      (hasDerivAt_const t (pbMassIntOn p s k))).add
      ((hasDerivAt_id t).mul (hasDerivAt_const t (pbMassIntOn p s (k - 1))))
    convert! hd using 1
    · simp only [homogeneousBlockMass_zero, zero_sub,
        Pi.sub_apply, id_eq, mul_zero, add_zero, one_mul]
      ring
  | succ M ih =>
    have hd := (((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).mul (ih k)).add
      ((hasDerivAt_id t).mul (ih (k - 1)))
    convert! hd using 1
    · simp only [homogeneousBlockMass_succ, Nat.cast_add, Nat.cast_one, Pi.sub_apply, id_eq]
      ring

theorem hasDerivAt_homogeneousBlockMass (p : ι → ℝ) (s : Finset ι)
    (M : ℕ) (t : ℝ) (k : ℤ) :
    HasDerivAt (fun u ↦ homogeneousBlockMass p s M u k)
      ((M : ℝ) * (homogeneousBlockMass p s (M - 1) t (k - 1) -
        homogeneousBlockMass p s (M - 1) t k)) t := by
  cases M with
  | zero => simpa using hasDerivAt_const t (pbMassIntOn p s k)
  | succ M => simpa using hasDerivAt_homogeneousBlockMass_succ p s M t k

theorem deriv_homogeneousBlockMass_succ (p : ι → ℝ) (s : Finset ι)
    (M : ℕ) (t : ℝ) (k : ℤ) :
    deriv (fun u ↦ homogeneousBlockMass p s (M + 1) u k) t =
      (M + 1 : ℕ) * (homogeneousBlockMass p s M t (k - 1) -
        homogeneousBlockMass p s M t k) :=
  (hasDerivAt_homogeneousBlockMass_succ p s M t k).deriv

theorem deriv_homogeneousBlockMass (p : ι → ℝ) (s : Finset ι)
    (M : ℕ) (t : ℝ) (k : ℤ) :
    deriv (fun u ↦ homogeneousBlockMass p s M u k) t =
      (M : ℝ) * (homogeneousBlockMass p s (M - 1) t (k - 1) -
        homogeneousBlockMass p s (M - 1) t k) :=
  (hasDerivAt_homogeneousBlockMass p s M t k).deriv

theorem homogeneousBlockMass_adjacent_le_of_deriv_nonpos {p : ι → ℝ} {s : Finset ι}
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) (M : ℕ) {t : ℝ}
    (ht : 0 ≤ t ∧ t ≤ 1) (k : ℤ)
    (hk : 0 < homogeneousBlockMass p s (M + 1) t k)
    (hd : deriv (fun u ↦ homogeneousBlockMass p s (M + 1) u k) t ≤ 0) :
    homogeneousBlockMass p s (M + 1) t (k - 1) ≤
      homogeneousBlockMass p s (M + 1) t k := by
  rw [deriv_homogeneousBlockMass_succ] at hd
  have hM : (0 : ℝ) < (M + 1 : ℕ) := by exact_mod_cast Nat.succ_pos M
  have hadj : homogeneousBlockMass p s M t (k - 1) ≤ homogeneousBlockMass p s M t k := by
    have hdiff : homogeneousBlockMass p s M t (k - 1) -
        homogeneousBlockMass p s M t k ≤ 0 := by nlinarith
    linarith
  have hbase : 0 < homogeneousBlockMass p s M t k := by
    rw [homogeneousBlockMass_succ] at hk
    have hmul := mul_le_mul_of_nonneg_left hadj ht.1
    linarith
  have hprefix := (homogeneousBlockMass_cross hp M ht).prefix_order
    (homogeneousBlockMass_nonneg hp M ht) hbase hadj
  rw [homogeneousBlockMass_succ, homogeneousBlockMass_succ]
  exact add_le_add (mul_le_mul_of_nonneg_left hadj (sub_nonneg.mpr ht.2))
    (mul_le_mul_of_nonneg_left (hprefix (k - 1) (by omega)) ht.1)

private theorem homogeneousBlockMass_union_prefix_order {p : ι → ℝ} (s u : Finset ι)
    (hp : ∀ i ∈ s ∪ u, 0 ≤ p i ∧ p i ≤ 1) (M : ℕ) (t : ℝ) (k : ℤ)
    (hprefix : ∀ j ≤ k, homogeneousBlockMass p s M t (j - 1) ≤
      homogeneousBlockMass p s M t j) :
    homogeneousBlockMass p (s ∪ u) M t k ≤ homogeneousBlockMass p s M t k ∧
      ∀ j ≤ k, homogeneousBlockMass p (s ∪ u) M t (j - 1) ≤
        homogeneousBlockMass p (s ∪ u) M t j := by
  induction u using Finset.induction_on with
  | empty => simpa using And.intro (le_refl (homogeneousBlockMass p s M t k)) hprefix
  | @insert i u hi ih =>
    have hps : ∀ j ∈ s ∪ u, 0 ≤ p j ∧ p j ≤ 1 := by
      intro j hj
      exact hp j (by simp only [mem_union, mem_insert] at hj ⊢; tauto)
    obtain ⟨hle, hpre⟩ := ih hps
    have hpi := hp i (by simp)
    rw [union_insert]
    by_cases him : i ∈ s ∪ u
    · rw [insert_eq_of_mem him]
      exact ⟨hle, hpre⟩
    · constructor
      · rw [homogeneousBlockMass_insert p him]
        have hmul := mul_le_mul_of_nonneg_left (hpre k le_rfl) hpi.1
        linarith
      · intro j hj
        rw [homogeneousBlockMass_insert p him, homogeneousBlockMass_insert p him]
        exact add_le_add (mul_le_mul_of_nonneg_left (hpre j hj) (sub_nonneg.mpr hpi.2))
          (mul_le_mul_of_nonneg_left (hpre (j - 1) (by omega)) hpi.1)

theorem homogeneousBlockMass_union_le_of_deriv_nonpos {p : ι → ℝ} (s u : Finset ι)
    (hp : ∀ i ∈ s ∪ u, 0 ≤ p i ∧ p i ≤ 1) (M : ℕ) {t : ℝ}
    (ht : 0 ≤ t ∧ t ≤ 1) (k : ℤ)
    (hk : 0 < homogeneousBlockMass p s (M + 1) t k)
    (hd : deriv (fun v ↦ homogeneousBlockMass p s (M + 1) v k) t ≤ 0) :
    homogeneousBlockMass p (s ∪ u) (M + 1) t k ≤
      homogeneousBlockMass p s (M + 1) t k := by
  have hps : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1 := fun i hi ↦ hp i (mem_union_left u hi)
  have hadj := homogeneousBlockMass_adjacent_le_of_deriv_nonpos hps M ht k hk hd
  have hprefix := (homogeneousBlockMass_cross hps (M + 1) ht).prefix_order
    (homogeneousBlockMass_nonneg hps (M + 1) ht) hk hadj
  exact (homogeneousBlockMass_union_prefix_order s u hp (M + 1) t k hprefix).1

end

end PoissonBinomialComparison

-- FixedMean
namespace PoissonBinomialComparison

open scoped BigOperators
open Finset

noncomputable section

variable {n : ℕ}

def parameterSlice (n : ℕ) (μ : ℝ) : Set (Fin n → ℝ) :=
  {p | ValidParameters p ∧ ∑ i, p i = μ}

def squareSum (p : Fin n → ℝ) : ℝ := ∑ i, (p i) ^ 2

theorem continuous_squareSum : Continuous (squareSum (n := n)) := by
  unfold squareSum
  fun_prop

theorem isCompact_parameterSlice (μ : ℝ) : IsCompact (parameterSlice n μ) := by
  have heq : parameterSlice n μ = Set.Icc (0 : Fin n → ℝ) 1 ∩ {p | ∑ i, p i = μ} := by
    ext p
    simp only [parameterSlice, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_Icc,
      ValidParameters, Pi.le_def, Pi.zero_apply, Pi.one_apply]
    simp only [forall_and]
  rw [heq]
  exact isCompact_Icc.inter_right (isClosed_eq (by fun_prop) continuous_const)

theorem parameterSlice_nonempty (μ : ℝ) (h0 : 0 ≤ μ) (hn : μ ≤ n) :
    (parameterSlice n μ).Nonempty := by
  obtain ⟨⟨p, q⟩, h, hg⟩ := feasiblePairs_nonempty μ h0 hn
  refine ⟨fun i ↦ p i - q i, ?_, ?_⟩
  · intro i
    have hi := (admissiblePair_iff p q).mp h i
    exact ⟨sub_nonneg.mpr hi.2.1, by linarith⟩
  · rw [← meanGap_eq_sum]
    exact hg

theorem exists_lexicographic_minimizer {α : Type*} [TopologicalSpace α]
    {s : Set α} (hs : IsCompact s) (hne : s.Nonempty) (f g : α → ℝ)
    (hf : Continuous f) (hg : Continuous g) :
    ∃ x ∈ s, (∀ y ∈ s, f x ≤ f y) ∧
      ∀ y ∈ s, f y = f x → g x ≤ g y := by
  obtain ⟨x, hx, hmin⟩ := hs.exists_isMinOn hne hf.continuousOn
  have hc : IsCompact (s ∩ {y | f y = f x}) :=
    hs.inter_right (isClosed_eq hf continuous_const)
  obtain ⟨z, hz, hzmin⟩ := hc.exists_isMinOn ⟨x, hx, rfl⟩ hg.continuousOn
  refine ⟨z, hz.1, ?_, ?_⟩
  · intro y hy
    rw [hz.2]
    exact (isMinOn_iff.mp hmin) y hy
  · intro y hy he
    exact (isMinOn_iff.mp hzmin) y ⟨hy, he.trans hz.2⟩

theorem exists_mass_minimizer_minimal_squareSum (μ : ℝ) (h0 : 0 ≤ μ)
    (hn : μ ≤ n) (k : ℕ) :
    ∃ p ∈ parameterSlice n μ,
      (∀ q ∈ parameterSlice n μ, pbMass p k ≤ pbMass q k) ∧
      ∀ q ∈ parameterSlice n μ, pbMass q k = pbMass p k → squareSum p ≤ squareSum q :=
  exists_lexicographic_minimizer (isCompact_parameterSlice μ)
    (parameterSlice_nonempty μ h0 hn) (fun p ↦ pbMass p k) squareSum
    (continuous_pbMass k) continuous_squareSum

def SymmetricQuadraticUpdates (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ p (i j : Fin n), i ≠ j → ∃ A B C : ℝ, ∀ u v : ℝ,
    f (Function.update (Function.update p i u) j v) = A + B * (u + v) + C * u * v

theorem pbMass_symmetricQuadraticUpdates (k : ℕ) :
    SymmetricQuadraticUpdates (fun p : Fin n → ℝ ↦ pbMass p k) := by
  intro p i j hij
  let s := (univ.erase i).erase j
  have hi : i ∉ s := by simp [s]
  have hj : j ∉ s := by simp [s]
  have hs : insert i (insert j s) = univ := by
    ext l
    by_cases hli : l = i <;> by_cases hlj : l = j <;> simp_all [s]
  refine ⟨randomizedTailOn p s 1 k - randomizedTailOn p s 0 k,
    randomizedSlopeOn p s 1 k - randomizedSlopeOn p s 0 k,
    randomizedCoefficientOn p s 1 k - randomizedCoefficientOn p s 0 k, ?_⟩
  intro u v
  dsimp only
  rw [← pbTail_sub_succ]
  have he (x : Fin n → ℝ) : pbTail x k - pbTail x (k + 1) =
      randomizedTailOn x univ 1 k - randomizedTailOn x univ 0 k := by
    simp [randomizedTailOn, pbTail]
  rw [he, ← hs, randomizedTailOn_update_update p hi hj hij,
    randomizedTailOn_update_update p hi hj hij]
  ring

theorem sum_map_update (F : ℝ → ℝ) (p : Fin n → ℝ) (i : Fin n) (u : ℝ) :
    (∑ l, F (Function.update p i u l)) = ∑ l, F (p l) + F u - F (p i) := by
  have he : (fun l ↦ F (Function.update p i u l)) =
      Function.update (fun l ↦ F (p l)) i (F u) := Function.comp_update F p i u
  rw [he, sum_update_of_mem (mem_univ i)]
  have h := sum_erase_add univ (fun l ↦ F (p l)) (mem_univ i)
  rw [sdiff_singleton_eq_erase]
  linarith

theorem squareSum_update (p : Fin n → ℝ) (i : Fin n) (u : ℝ) :
    squareSum (Function.update p i u) = squareSum p + u ^ 2 - (p i) ^ 2 :=
  sum_map_update (fun x ↦ x ^ 2) p i u

theorem update_pair_mem_parameterSlice {p : Fin n → ℝ} {μ : ℝ}
    (hp : p ∈ parameterSlice n μ) {i j : Fin n} (hij : i ≠ j)
    {u v : ℝ} (hu : 0 ≤ u ∧ u ≤ 1) (hv : 0 ≤ v ∧ v ≤ 1)
    (hsum : u + v = p i + p j) :
    Function.update (Function.update p i u) j v ∈ parameterSlice n μ := by
  constructor
  · intro l
    by_cases hlj : l = j
    · subst l
      simpa using hv
    · by_cases hli : l = i
      · subst l
        simpa [Function.update_of_ne hij] using hu
      · simpa [Function.update_of_ne hlj, Function.update_of_ne hli] using hp.1 l
  · change (∑ l, id (Function.update (Function.update p i u) j v l)) = μ
    rw [sum_map_update, sum_map_update]
    simp only [id_eq, Function.update_of_ne (Ne.symm hij)]
    rw [hp.2]
    linarith

private theorem no_distinct_ordered_interior {f : (Fin n → ℝ) → ℝ}
    (hf : SymmetricQuadraticUpdates f) {p : Fin n → ℝ} {μ : ℝ}
    (hp : p ∈ parameterSlice n μ)
    (hmin : ∀ q ∈ parameterSlice n μ, f p ≤ f q)
    (hsec : ∀ q ∈ parameterSlice n μ, f q = f p → squareSum p ≤ squareSum q)
    {i j : Fin n} (hij : i ≠ j) (hi : 0 < p i) (hj : p j < 1)
    (hlt : p i < p j) : False := by
  obtain ⟨A, B, C, hpoly⟩ := hf p i j hij
  have hbase : f p = A + B * (p i + p j) + C * p i * p j := by
    simpa only [Function.update_eq_self] using hpoly (p i) (p j)
  let a := (p i + p j) / 2
  have ha : 0 ≤ a ∧ a ≤ 1 := by dsimp [a]; constructor <;> linarith
  have hamean : a + a = p i + p j := by dsimp [a]; ring
  have hamem := update_pair_mem_parameterSlice hp hij ha ha hamean
  have havg := hmin _ hamem
  rw [hbase, hpoly] at havg
  have hsquare : 0 < (p i - p j) ^ 2 := sq_pos_of_ne_zero (by linarith)
  have hc0 : 0 ≤ C := by
    apply (mul_nonneg_iff_of_pos_right hsquare).mp
    dsimp [a] at havg
    nlinarith only [havg]
  let t := min (p i) (1 - p j)
  have ht : 0 < t := lt_min hi (by linarith)
  have hti : t ≤ p i := min_le_left _ _
  have htj : t ≤ 1 - p j := min_le_right _ _
  have hui : 0 ≤ p i - t ∧ p i - t ≤ 1 := ⟨by linarith, by linarith⟩
  have hvj : 0 ≤ p j + t ∧ p j + t ≤ 1 := ⟨by linarith, by linarith⟩
  have hspread := hmin _ (update_pair_mem_parameterSlice hp hij hui hvj (by ring))
  rw [hbase, hpoly] at hspread
  have hfac : 0 < t * (p j - p i + t) := mul_pos ht (by linarith)
  have hc1 : C ≤ 0 := by
    have hprod : C * (t * (p j - p i + t)) ≤ 0 := by nlinarith only [hspread]
    exact nonpos_of_mul_nonpos_left hprod hfac
  have hcz : C = 0 := le_antisymm hc1 hc0
  have heq : f (Function.update (Function.update p i a) j a) = f p := by
    rw [hpoly, hbase, hcz, hamean]
    ring
  have hs := hsec _ hamem heq
  rw [squareSum_update, squareSum_update, Function.update_of_ne (Ne.symm hij)] at hs
  dsimp [a] at hs
  nlinarith only [hs, hsquare]

theorem interior_coordinates_eq_of_minimal_squareSum {f : (Fin n → ℝ) → ℝ}
    (hf : SymmetricQuadraticUpdates f) {p : Fin n → ℝ} {μ : ℝ}
    (hp : p ∈ parameterSlice n μ)
    (hmin : ∀ q ∈ parameterSlice n μ, f p ≤ f q)
    (hsec : ∀ q ∈ parameterSlice n μ, f q = f p → squareSum p ≤ squareSum q)
    (i j : Fin n) (hi : 0 < p i ∧ p i < 1) (hj : 0 < p j ∧ p j < 1) :
    p i = p j := by
  by_contra hne
  have hij : i ≠ j := fun he ↦ hne (congrArg p he)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact no_distinct_ordered_interior hf hp hmin hsec hij hi.1 hj.2 hlt
  · exact no_distinct_ordered_interior hf hp hmin hsec (Ne.symm hij) hj.1 hi.2 hgt

theorem exists_mass_minimizer_equal_interior (μ : ℝ) (h0 : 0 ≤ μ)
    (hn : μ ≤ n) (k : ℕ) :
    ∃ p ∈ parameterSlice n μ,
      (∀ q ∈ parameterSlice n μ, pbMass p k ≤ pbMass q k) ∧
      ∀ i j, (0 < p i ∧ p i < 1) → (0 < p j ∧ p j < 1) → p i = p j := by
  obtain ⟨p, hp, hmin, hsec⟩ := exists_mass_minimizer_minimal_squareSum μ h0 hn k
  exact ⟨p, hp, hmin, interior_coordinates_eq_of_minimal_squareSum
    (pbMass_symmetricQuadraticUpdates k) hp hmin hsec⟩

end

end PoissonBinomialComparison

-- Deterministic
namespace PoissonBinomialComparison

open scoped BigOperators
open Finset

noncomputable section

variable {ι : Type*} [DecidableEq ι]

theorem homogeneousBlockMass_empty_eq {κ : Type*} [DecidableEq κ]
    (p : ι → ℝ) (q : κ → ℝ) (M : ℕ) (t : ℝ) (k : ℤ) :
    homogeneousBlockMass p ∅ M t k = homogeneousBlockMass q ∅ M t k := by
  induction M generalizing k with
  | zero => simp
  | succ M ih => simp only [homogeneousBlockMass_succ, ih]

theorem homogeneousBlockMass_empty_eq_pbMassInt (p : ι → ℝ) (M : ℕ) (t : ℝ) (k : ℤ) :
    homogeneousBlockMass p ∅ M t k =
      pbMassIntOn (fun _ : Fin M ↦ t) univ k := by
  rw [homogeneousBlockMass_empty_eq p (fun _ : Fin M ↦ t)]
  simpa using homogeneousBlockMass_eq_union (fun _ : Fin M ↦ t) ∅ univ
    (by simp) t (by simp) k

theorem exists_deterministic_binomial_decomposition (p : ι → ℝ) (s : Finset ι)
    (t : ℝ) (hp : ∀ i ∈ s, p i = 0 ∨ p i = 1 ∨ p i = t) :
    ∃ J M : ℕ, J + M ≤ s.card ∧
      (∑ i ∈ s, p i) = (J : ℝ) + M * t ∧
      ∀ k : ℤ, pbMassIntOn p s k =
        homogeneousBlockMass (fun _ : Unit ↦ (0 : ℝ)) ∅ M t (k - J) := by
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨0, 0, by simp, by simp, ?_⟩
    intro k
    simp
  | @insert i s hi ih =>
    obtain ⟨J, M, hcard, hsum, hmass⟩ := ih (fun j hj ↦ hp j (mem_insert_of_mem hj))
    rcases hp i (mem_insert_self i s) with hz | ho | ht
    · refine ⟨J, M, ?_, ?_, ?_⟩
      · rw [card_insert_of_notMem hi]
        omega
      · rw [sum_insert hi, hz, zero_add, hsum]
      · intro k
        rw [pbMassIntOn_insert p hi, hz]
        simpa using hmass k
    · refine ⟨J + 1, M, ?_, ?_, ?_⟩
      · rw [card_insert_of_notMem hi]
        omega
      · rw [sum_insert hi, ho, hsum, Nat.cast_add, Nat.cast_one]
        ring
      · intro k
        rw [pbMassIntOn_insert p hi, ho]
        simp only [sub_self, zero_mul, one_mul, zero_add, hmass]
        congr 1
        omega
    · refine ⟨J, M + 1, ?_, ?_, ?_⟩
      · rw [card_insert_of_notMem hi]
        omega
      · rw [sum_insert hi, ht, hsum, Nat.cast_add, Nat.cast_one]
        ring
      · intro k
        rw [pbMassIntOn_insert p hi, ht, hmass, hmass, homogeneousBlockMass_succ]
        rw [show k - 1 - (J : ℤ) = k - J - 1 by omega]

variable {n : ℕ}

theorem equal_interior_binomial_decomposition {p : Fin n → ℝ}
    (hp : ValidParameters p)
    (heq : ∀ i j, (0 < p i ∧ p i < 1) → (0 < p j ∧ p j < 1) → p i = p j) :
    ∃ (t : ℝ) (J M : ℕ), 0 ≤ t ∧ t ≤ 1 ∧ J + M ≤ n ∧
      (∑ i, p i) = (J : ℝ) + M * t ∧
      ∀ k : ℤ, pbMassIntOn p univ k = pbMassIntOn (fun _ : Fin M ↦ t) univ (k - J) := by
  have hex : ∃ t : ℝ, (0 ≤ t ∧ t ≤ 1) ∧ ∀ i, p i = 0 ∨ p i = 1 ∨ p i = t := by
    by_cases h : ∃ i, 0 < p i ∧ p i < 1
    · obtain ⟨i, hi⟩ := h
      refine ⟨p i, hp i, ?_⟩
      intro j
      by_cases hj0 : p j = 0
      · exact Or.inl hj0
      by_cases hj1 : p j = 1
      · exact Or.inr (Or.inl hj1)
      exact Or.inr (Or.inr (heq j i
        ⟨lt_of_le_of_ne (hp j).1 (Ne.symm hj0), lt_of_le_of_ne (hp j).2 hj1⟩ hi))
    · refine ⟨0, ⟨le_rfl, zero_le_one⟩, ?_⟩
      intro i
      by_cases hi0 : p i = 0
      · exact Or.inl hi0
      right
      left
      by_contra hi1
      exact h ⟨i, lt_of_le_of_ne (hp i).1 (Ne.symm hi0), lt_of_le_of_ne (hp i).2 hi1⟩
  obtain ⟨t, ht, hvalues⟩ := hex
  obtain ⟨J, M, hcard, hsum, hmass⟩ :=
    exists_deterministic_binomial_decomposition p univ t (fun i _ ↦ hvalues i)
  refine ⟨t, J, M, ht.1, ht.2, ?_, hsum, ?_⟩
  · simpa using hcard
  · intro k
    rw [hmass, homogeneousBlockMass_empty_eq_pbMassInt]

theorem integer_mean_binomial_decomposition {p : Fin n → ℝ}
    (hp : ValidParameters p) (k : ℕ) (hmean : (∑ i, p i) = k)
    (heq : ∀ i j, (0 < p i ∧ p i < 1) → (0 < p j ∧ p j < 1) → p i = p j) :
    ∃ M ℓ : ℕ, M ≤ n ∧ ℓ ≤ M ∧
      pbMass p k = pbMass (fun _ : Fin M ↦ (ℓ : ℝ) / M) ℓ := by
  obtain ⟨t, J, M, ht0, ht1, hcard, hsum, hmass⟩ := equal_interior_binomial_decomposition hp heq
  have hm0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hJk : J ≤ k := by
    have hr : (J : ℝ) ≤ k := by rw [hmean] at hsum; nlinarith
    exact_mod_cast hr
  have hkJM : k ≤ J + M := by
    have hr : (k : ℝ) ≤ J + M := by rw [hmean] at hsum; nlinarith
    exact_mod_cast hr
  let ℓ := k - J
  have hℓ : ℓ ≤ M := by dsimp [ℓ]; omega
  have hcast : (k : ℤ) - J = (ℓ : ℤ) := by dsimp [ℓ]; omega
  have hmass' : pbMass p k = pbMass (fun _ : Fin M ↦ t) ℓ := by
    have h := hmass (k : ℤ)
    rw [hcast, pbMassIntOn_natCast, pbMassIntOn_natCast] at h
    exact h
  refine ⟨M, ℓ, by omega, hℓ, ?_⟩
  by_cases hM : M = 0
  · have hℓ0 : ℓ = 0 := by omega
    rw [hmass', hM, hℓ0]
    simp
  · have hMr : (M : ℝ) ≠ 0 := by exact_mod_cast hM
    have ht : t = (ℓ : ℝ) / M := by
      apply (eq_div_iff hMr).mpr
      dsimp [ℓ]
      rw [Nat.cast_sub hJk]
      rw [hmean] at hsum
      linarith
    rw [hmass', ht]

theorem exists_binomial_mass_le_integer_mean_mass {p : Fin n → ℝ}
    (hp : ValidParameters p) (k : ℕ) (hmean : (∑ i, p i) = k) :
    ∃ M ℓ : ℕ, M ≤ n ∧ ℓ ≤ M ∧
      pbMass (fun _ : Fin M ↦ (ℓ : ℝ) / M) ℓ ≤ pbMass p k := by
  have hkn : (k : ℝ) ≤ n := by
    calc
      (k : ℝ) = ∑ i, p i := hmean.symm
      _ ≤ ∑ _i : Fin n, (1 : ℝ) := sum_le_sum (fun i _ ↦ (hp i).2)
      _ = n := by simp
  obtain ⟨q, hq, hmin, heq⟩ := exists_mass_minimizer_equal_interior
    (k : ℝ) (Nat.cast_nonneg k) hkn k
  obtain ⟨M, ℓ, hM, hℓ, hmass⟩ := integer_mean_binomial_decomposition hq.1 k hq.2 heq
  refine ⟨M, ℓ, hM, hℓ, ?_⟩
  rw [← hmass]
  exact hmin p ⟨hp, hmean⟩

end

end PoissonBinomialComparison

-- MaximalAtom
namespace PoissonBinomialComparison

open scoped BigOperators
open Finset

noncomputable section

variable {n : ℕ}

theorem kappa_le_pbMass_at_integer_mean {p : Fin n → ℝ} (hp : ValidParameters p)
    (k : ℕ) (hmean : (∑ i, p i) = k) : kappa n ≤ pbMass p k := by
  obtain ⟨M, ℓ, hM, hℓ, hmass⟩ := exists_binomial_mass_le_integer_mean_mass hp k hmean
  exact (kappa_le_pbMass_integerMean hℓ hM).trans hmass

theorem exists_pbMass_ge_kappa_succ {p : Fin n → ℝ} (hp : ValidParameters p) :
    ∃ k : ℕ, k ≤ n ∧ kappa (n + 1) ≤ pbMass p k := by
  let μ : ℝ := ∑ i, p i
  have hμ : 0 ≤ μ := sum_nonneg (fun i _ ↦ (hp i).1)
  let k : ℕ := ⌊μ⌋₊
  let t : ℝ := (k : ℝ) + 1 - μ
  have hfloor : (k : ℝ) ≤ μ := Nat.floor_le hμ
  have hceil : μ < (k : ℝ) + 1 := Nat.lt_floor_add_one μ
  have ht : 0 ≤ t ∧ t ≤ 1 := by dsimp [t]; constructor <;> linarith
  have hvalid : ValidParameters (Fin.cons t p) := by
    intro i
    exact Fin.cases ht hp i
  have hmean : (∑ i, Fin.cons t p i) = ((k + 1 : ℕ) : ℝ) := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, Nat.cast_add, Nat.cast_one]
    change t + μ = (k : ℝ) + 1
    dsimp [t]
    ring
  have hnew := kappa_le_pbMass_at_integer_mean hvalid (k + 1) hmean
  have hrec : pbMass (Fin.cons t p) (k + 1) =
      (1 - t) * pbMass p (k + 1) + t * pbMass p k := by
    have h := pbMassInt_cons p t ((k + 1 : ℕ) : ℤ)
    have hc : ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) := by omega
    simpa only [hc, pbMassIntOn_natCast, pbMass] using h
  rw [hrec] at hnew
  have hmax : kappa (n + 1) ≤ max (pbMass p (k + 1)) (pbMass p k) := by
    have h1 := mul_le_mul_of_nonneg_left (le_max_left (pbMass p (k + 1)) (pbMass p k))
      (sub_nonneg.mpr ht.2)
    have h2 := mul_le_mul_of_nonneg_left (le_max_right (pbMass p (k + 1)) (pbMass p k)) ht.1
    nlinarith
  have hsupport : ∀ j : ℕ, kappa (n + 1) ≤ pbMass p j → j ≤ n := by
    intro j hj
    by_contra hnj
    have hz := pbMass_eq_zero_of_lt p (show n < j by omega)
    rw [hz] at hj
    exact (not_le_of_gt (kappa_pos (n + 1))) hj
  rcases le_max_iff.mp hmax with hnext | hprev
  · exact ⟨k + 1, hsupport (k + 1) hnext, hnext⟩
  · exact ⟨k, hsupport k hprev, hprev⟩

theorem exists_pbMass_ge_kappa (n : ℕ) (hn : 1 ≤ n)
    {p : Fin (n - 1) → ℝ} (hp : ValidParameters p) :
    ∃ k : ℕ, k ≤ n - 1 ∧ kappa n ≤ pbMass p k := by
  simpa only [Nat.sub_add_cancel hn] using exists_pbMass_ge_kappa_succ hp

variable {ι : Type*} [DecidableEq ι]

theorem kappa_le_pbMassOn_at_integer_mean {p : ι → ℝ} (s : Finset ι)
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) (k : ℕ)
    (hmean : (∑ i ∈ s, p i) = k) : kappa s.card ≤ pbMassOn p s k := by
  have h := kappa_le_pbMass_at_integer_mean (valid_finsetParameters s hp) k
    (by rw [sum_finsetParameters]; exact hmean)
  simpa only [pbMass_finsetParameters] using h

theorem exists_pbMassOn_ge_kappa_succ {p : ι → ℝ} (s : Finset ι)
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) :
    ∃ k : ℕ, k ≤ s.card ∧ kappa (s.card + 1) ≤ pbMassOn p s k := by
  simpa only [pbMass_finsetParameters] using
    exists_pbMass_ge_kappa_succ (valid_finsetParameters s hp)

end

end PoissonBinomialComparison

-- DeletionMixture
namespace PoissonBinomialComparison

open scoped BigOperators
open Finset

noncomputable section

variable {ι : Type*} [DecidableEq ι]

def midpointParameters (p q : ι → ℝ) (i : ι) : ℝ := (p i + q i) / 2

omit [DecidableEq ι] in
theorem midpointParameters_valid {p q : ι → ℝ}
    (hp : ValidParameters p) (hq : ValidParameters q) :
    ValidParameters (midpointParameters p q) := by
  intro i
  have hp' := hp i
  have hq' := hq i
  simp only [midpointParameters]
  constructor <;> linarith

private theorem coefficient_congr {p q : ι → ℝ} {s : Finset ι}
    (h : ∀ i ∈ s, p i = q i) (k : ℕ) :
    randomizedCoefficientOn p s 0 k = randomizedCoefficientOn q s 0 k := by
  simp only [randomizedCoefficientOn, randomizedSlopeOn, pbMassOn_congr h]

theorem pbMassOn_insert_affine (p : ι → ℝ) {s : Finset ι} {i : ι}
    (hi : i ∉ s) (k : ℕ) :
    pbMassOn p (insert i s) k = pbMassOn p s k +
      p i * randomizedCoefficientOn p s 0 k := by
  simpa [randomizedSlopeOn] using randomizedSlopeOn_insert p hi 0 k

theorem pbTailOn_insert_insert_polynomial (p : ι → ℝ) {s : Finset ι} {i j : ι}
    (hi : i ∉ s) (hj : j ∉ s) (hij : i ≠ j) (k : ℕ) :
    pbTailOn p (insert i (insert j s)) (k + 1) = pbTailOn p s (k + 1) +
      (p i + p j) * pbMassOn p s k + p i * p j * randomizedCoefficientOn p s 0 k := by
  simpa [randomizedTailOn, randomizedSlopeOn] using
    randomizedTailOn_insert_insert p hi hj hij 0 k

theorem pbTailOn_two_coordinate_midpoint (p q : ι → ℝ) {s : Finset ι} {i j : ι}
    (hi : i ∉ s) (hj : j ∉ s) (hij : i ≠ j)
    (heq : ∀ l ∈ s, p l = q l) (k : ℕ) :
    pbTailOn p (insert i (insert j s)) (k + 1) -
      pbTailOn q (insert i (insert j s)) (k + 1) =
        (p i - q i) * pbMassOn (midpointParameters p q) (insert j s) k +
        (p j - q j) * pbMassOn (midpointParameters p q) (insert i s) k := by
  have hpr : ∀ l ∈ s, p l = midpointParameters p q l := by
    intro l hl
    simp only [midpointParameters, ← heq l hl]
    ring
  have hqr : ∀ l ∈ s, q l = midpointParameters p q l :=
    fun l hl ↦ (heq l hl).symm.trans (hpr l hl)
  rw [pbTailOn_insert_insert_polynomial p hi hj hij,
    pbTailOn_insert_insert_polynomial q hi hj hij,
    pbMassOn_insert_affine _ hj, pbMassOn_insert_affine _ hi,
    pbTailOn_congr hpr, pbTailOn_congr hqr, pbMassOn_congr hpr,
    pbMassOn_congr hqr, coefficient_congr hpr, coefficient_congr hqr]
  simp only [midpointParameters]
  ring

theorem pbMassOn_two_deletion_mixture (r : ι → ℝ) {s : Finset ι} {i j : ι}
    (hi : i ∉ s) (hj : j ∉ s) (u v : ℝ) (huv : u + v = 1) (k : ℕ) :
    u * pbMassOn r (insert j s) k + v * pbMassOn r (insert i s) k =
      pbMassOn (Function.update r j (u * r j + v * r i)) (insert j s) k := by
  have hr : ∀ l ∈ s, Function.update r j (u * r j + v * r i) l = r l := by
    intro l hl
    have hlj : l ≠ j := by intro he; subst l; exact hj hl
    exact Function.update_of_ne hlj _ r
  rw [pbMassOn_insert_affine r hj, pbMassOn_insert_affine r hi,
    pbMassOn_insert_affine _ hj, pbMassOn_congr hr, coefficient_congr hr,
    Function.update_self]
  calc
    _ = (u + v) * pbMassOn r s k +
        (u * r j + v * r i) * randomizedCoefficientOn r s 0 k := by ring
    _ = _ := by rw [huv]; ring

theorem two_deletion_mixture_valid {r : ι → ℝ} (hr : ValidParameters r)
    (i j : ι) {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u + v = 1) :
    ValidParameters (Function.update r j (u * r j + v * r i)) := by
  intro l
  by_cases hl : l = j
  · subst l
    rw [Function.update_self]
    constructor
    · exact add_nonneg (mul_nonneg hu (hr j).1) (mul_nonneg hv (hr i).1)
    · calc
        u * r j + v * r i ≤ u * 1 + v * 1 :=
          add_le_add (mul_le_mul_of_nonneg_left (hr j).2 hu)
            (mul_le_mul_of_nonneg_left (hr i).2 hv)
        _ = 1 := by simpa using huv
  · simpa [Function.update_of_ne hl] using hr l

variable {n : ℕ}

def positiveGapCoordinates (p q : Fin n → ℝ) : Finset (Fin n) :=
  univ.filter (fun i ↦ q i < p i)

def gapWeights (p q : Fin n → ℝ) (i : Fin n) : ℝ := (p i - q i) / meanGap p q

def deletionMixture (r w : Fin n → ℝ) (k : ℕ) : ℝ :=
  ∑ i, w i * pbMassOn r (univ.erase i) k

theorem gapWeights_nonneg {p q : Fin n → ℝ} (h : AdmissiblePair p q) (i : Fin n) :
    0 ≤ gapWeights p q i :=
  div_nonneg (sub_nonneg.mpr (h.2.2 i)) (meanGap_nonneg h)

theorem sum_gapWeights {p q : Fin n → ℝ} (hgap : meanGap p q ≠ 0) :
    ∑ i, gapWeights p q i = 1 := by
  simp only [gapWeights, div_eq_mul_inv, ← sum_mul, ← meanGap_eq_sum]
  exact mul_inv_cancel₀ hgap

private theorem sum_eq_two {f : Fin n → ℝ} {i j : Fin n} (hij : i ≠ j)
    (hz : ∀ l, l ≠ i → l ≠ j → f l = 0) : ∑ l, f l = f i + f j := by
  have hs : ∑ l ∈ ({i, j} : Finset (Fin n)), f l = ∑ l, f l := by
    apply sum_subset (subset_univ _)
    intro l _ hl
    have hli : l ≠ i := by intro he; subst l; exact hl (by simp)
    have hlj : l ≠ j := by intro he; subst l; exact hl (by simp)
    exact hz l hli hlj
  rw [← hs]
  simp [hij]

theorem tailDiff_two_coordinate_midpoint (p q : Fin n → ℝ) {i j : Fin n}
    (hij : i ≠ j) (heq : ∀ l, l ≠ i → l ≠ j → p l = q l) (k : ℕ) :
    tailDiff p q (k + 1) =
      (p i - q i) * pbMassOn (midpointParameters p q) (univ.erase i) k +
      (p j - q j) * pbMassOn (midpointParameters p q) (univ.erase j) k := by
  let s := (univ.erase i).erase j
  have hi : i ∉ s := by simp [s]
  have hj : j ∉ s := by simp [s]
  have hfull : insert i (insert j s) = univ := by
    ext l
    by_cases hli : l = i <;> by_cases hlj : l = j <;> simp_all [s]
  have hsi : insert i s = univ.erase j := by
    ext l
    by_cases hli : l = i <;> by_cases hlj : l = j <;> simp_all [s]
  have hsj : insert j s = univ.erase i := by
    ext l
    by_cases hli : l = i <;> by_cases hlj : l = j <;> simp_all [s]
  have hs : ∀ l ∈ s, p l = q l := by
    intro l hl
    have hl' := mem_erase.mp hl
    exact heq l (mem_erase.mp hl'.2).1 hl'.1
  have ht := pbTailOn_two_coordinate_midpoint p q hi hj hij hs k
  rw [hfull, hsi, hsj] at ht
  exact ht

theorem tailDiff_one_coordinate_midpoint (p q : Fin n → ℝ) (i : Fin n)
    (heq : ∀ l, l ≠ i → p l = q l) (k : ℕ) :
    tailDiff p q (k + 1) =
      (p i - q i) * pbMassOn (midpointParameters p q) (univ.erase i) k := by
  have hp : Function.update q i (p i) = p := by
    funext l
    by_cases hl : l = i
    · subst l; simp
    · simpa [Function.update_of_ne hl] using (heq l hl).symm
  have hr : ∀ l ∈ univ.erase i, q l = midpointParameters p q l := by
    intro l hl
    simp only [midpointParameters, heq l (mem_erase.mp hl).1]
    ring
  have ht := pbTail_update_sub q i (q i) (p i) k
  rw [hp, Function.update_eq_self, pbMassOn_congr hr] at ht
  exact ht

private theorem two_gap_cases {p q : Fin n → ℝ} (h : AdmissiblePair p q)
    (hcard : (positiveGapCoordinates p q).card ≤ 2) (hgap : 0 < meanGap p q) :
    (∃ i, ∀ l, l ≠ i → p l = q l) ∨
      (∃ i j, i ≠ j ∧ ∀ l, l ≠ i → l ≠ j → p l = q l) := by
  obtain ⟨i, hi⟩ := exists_strict_coordinate_of_meanGap_pos h hgap
  by_cases hsecond : ∃ j, j ≠ i ∧ q j < p j
  · obtain ⟨j, hji, hj⟩ := hsecond
    right
    refine ⟨i, j, hji.symm, ?_⟩
    intro l hli hlj
    apply le_antisymm _ (h.2.2 l)
    by_contra hnot
    have hl : q l < p l := lt_of_not_ge hnot
    have hs : ({i, j, l} : Finset (Fin n)) ⊆ positiveGapCoordinates p q := by
      intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> simp [positiveGapCoordinates, hi, hj, hl]
    have hthree : ({i, j, l} : Finset (Fin n)).card = 3 := by
      simp [hji.symm, hli.symm, hlj.symm]
    have hc := card_le_card hs
    rw [hthree] at hc
    omega
  · left
    refine ⟨i, ?_⟩
    intro l hli
    exact le_antisymm (le_of_not_gt (fun hl ↦ hsecond ⟨l, hli, hl⟩)) (h.2.2 l)

theorem tailDiff_eq_midpoint_deletion_sum {p q : Fin n → ℝ} (h : AdmissiblePair p q)
    (hcard : (positiveGapCoordinates p q).card ≤ 2) (k : ℕ) :
    tailDiff p q (k + 1) =
      ∑ i, (p i - q i) * pbMassOn (midpointParameters p q) (univ.erase i) k := by
  by_cases hz : meanGap p q = 0
  · have heq := (meanGap_eq_zero_iff h).mp hz
    subst p
    simp [tailDiff]
  · have hgap : 0 < meanGap p q := lt_of_le_of_ne (meanGap_nonneg h) (Ne.symm hz)
    rcases two_gap_cases h hcard hgap with ⟨i, heq⟩ | ⟨i, j, hij, heq⟩
    · rw [tailDiff_one_coordinate_midpoint p q i heq]
      symm
      apply sum_eq_single i
      · intro l _ hli
        rw [heq l hli, sub_self, zero_mul]
      · intro hi
        exact False.elim (hi (mem_univ i))
    · rw [tailDiff_two_coordinate_midpoint p q hij heq]
      symm
      exact sum_eq_two hij (fun l hli hlj ↦ by rw [heq l hli hlj, sub_self, zero_mul])

theorem tailDiff_div_meanGap_eq_deletionMixture {p q : Fin n → ℝ}
    (h : AdmissiblePair p q) (hcard : (positiveGapCoordinates p q).card ≤ 2) (k : ℕ) :
    tailDiff p q (k + 1) / meanGap p q =
      deletionMixture (midpointParameters p q) (gapWeights p q) k := by
  rw [tailDiff_eq_midpoint_deletion_sum h hcard]
  simp only [deletionMixture, gapWeights, div_eq_mul_inv, sum_mul]
  apply sum_congr rfl
  intro i _
  ring

theorem exists_deleted_law_of_two_gaps {p q : Fin n → ℝ} (h : AdmissiblePair p q)
    (hcard : (positiveGapCoordinates p q).card ≤ 2) (hgap : 0 < meanGap p q) :
    ∃ (r : Fin n → ℝ) (i : Fin n), ValidParameters r ∧
      ∀ k, tailDiff p q (k + 1) / meanGap p q = pbMassOn r (univ.erase i) k := by
  have hr := midpointParameters_valid h.1 h.2.1
  rcases two_gap_cases h hcard hgap with ⟨i, heq⟩ | ⟨i, j, hij, heq⟩
  · refine ⟨midpointParameters p q, i, hr, ?_⟩
    have hmean : meanGap p q = p i - q i := by
      rw [meanGap_eq_sum]
      apply sum_eq_single i
      · intro l _ hli
        rw [heq l hli, sub_self]
      · intro hi
        exact False.elim (hi (mem_univ i))
    intro k
    apply (div_eq_iff hgap.ne').mpr
    rw [tailDiff_one_coordinate_midpoint p q i heq, hmean]
    ring
  · let u := (p i - q i) / meanGap p q
    let v := (p j - q j) / meanGap p q
    have hu : 0 ≤ u := div_nonneg (sub_nonneg.mpr (h.2.2 i)) hgap.le
    have hv : 0 ≤ v := div_nonneg (sub_nonneg.mpr (h.2.2 j)) hgap.le
    have hmean : meanGap p q = (p i - q i) + (p j - q j) := by
      rw [meanGap_eq_sum]
      exact sum_eq_two hij (fun l hli hlj ↦ by rw [heq l hli hlj, sub_self])
    have huv : u + v = 1 := by
      change (p i - q i) / meanGap p q + (p j - q j) / meanGap p q = 1
      rw [← add_div, ← hmean, div_self hgap.ne']
    let r := midpointParameters p q
    let t := Function.update r j (u * r j + v * r i)
    refine ⟨t, i, two_deletion_mixture_valid hr i j hu hv huv, ?_⟩
    let s := (univ.erase i).erase j
    have hi : i ∉ s := by simp [s]
    have hj : j ∉ s := by simp [s]
    have hsi : insert i s = univ.erase j := by
      ext l
      by_cases hli : l = i <;> by_cases hlj : l = j <;> simp_all [s]
    have hsj : insert j s = univ.erase i := by
      ext l
      by_cases hli : l = i <;> by_cases hlj : l = j <;> simp_all [s]
    intro k
    have hmix := pbMassOn_two_deletion_mixture r hi hj u v huv k
    rw [hsi, hsj] at hmix
    rw [← hmix, tailDiff_two_coordinate_midpoint p q hij heq]
    change _ = (p i - q i) / meanGap p q * _ + (p j - q j) / meanGap p q * _
    ring

theorem exists_bernoulli_law_of_two_gaps {p q : Fin n → ℝ} (h : AdmissiblePair p q)
    (hcard : (positiveGapCoordinates p q).card ≤ 2) (hgap : 0 < meanGap p q) :
    ∃ r : Fin (n - 1) → ℝ, ValidParameters r ∧
      ∀ k, tailDiff p q (k + 1) / meanGap p q = pbMass r k := by
  obtain ⟨r, i, hr, heq⟩ := exists_deleted_law_of_two_gaps h hcard hgap
  have hsize : (univ.erase i : Finset (Fin n)).card = n - 1 := by simp
  have hex : ∃ t : Fin (univ.erase i : Finset (Fin n)).card → ℝ,
      ValidParameters t ∧ ∀ k, tailDiff p q (k + 1) / meanGap p q = pbMass t k := by
    refine ⟨finsetParameters r (univ.erase i),
      valid_finsetParameters _ (fun j _ ↦ hr j), ?_⟩
    intro k
    rw [pbMass_finsetParameters]
    exact heq k
  rw [hsize] at hex
  exact hex

theorem deletionMixture_is_bernoulli_of_two_gaps {p q : Fin n → ℝ}
    (h : AdmissiblePair p q) (hcard : (positiveGapCoordinates p q).card ≤ 2)
    (hgap : 0 < meanGap p q) :
    ∃ r : Fin (n - 1) → ℝ, ValidParameters r ∧
      ∀ k, deletionMixture (midpointParameters p q) (gapWeights p q) k = pbMass r k := by
  obtain ⟨r, hr, heq⟩ := exists_bernoulli_law_of_two_gaps h hcard hgap
  refine ⟨r, hr, ?_⟩
  intro k
  rw [← tailDiff_div_meanGap_eq_deletionMixture h hcard]
  exact heq k

theorem two_gap_lower_bound_of_maximal_atom {p q : Fin n → ℝ}
    (h : AdmissiblePair p q) (hcard : (positiveGapCoordinates p q).card ≤ 2)
    (κ : ℝ) (hAtom : ∀ r : Fin (n - 1) → ℝ, ValidParameters r →
      ∃ k, k < n ∧ κ ≤ pbMass r k) :
    κ * meanGap p q ≤ tailObjective p q := by
  by_cases hz : meanGap p q = 0
  · rw [tailObjective_eq_zero_of_meanGap_eq_zero h hz, hz, mul_zero]
  · have hgap : 0 < meanGap p q := lt_of_le_of_ne (meanGap_nonneg h) (Ne.symm hz)
    obtain ⟨r, hr, heq⟩ := exists_bernoulli_law_of_two_gaps h hcard hgap
    obtain ⟨k, hk, hmass⟩ := hAtom r hr
    rw [← heq k] at hmass
    have hscaled := (le_div_iff₀ hgap).mp hmass
    exact hscaled.trans (tailDiff_le_tailObjective p q (mem_Icc.mpr ⟨by omega, by omega⟩))

theorem two_gap_lower_bound {p q : Fin n → ℝ} (hn : 1 ≤ n)
    (h : AdmissiblePair p q) (hcard : (positiveGapCoordinates p q).card ≤ 2) :
    kappa n * meanGap p q ≤ tailObjective p q := by
  apply two_gap_lower_bound_of_maximal_atom h hcard (kappa n)
  intro r hr
  obtain ⟨k, hk, hmass⟩ := exists_pbMass_ge_kappa n hn hr
  exact ⟨k, by omega, hmass⟩

end

end PoissonBinomialComparison

-- ContinuousSwitch
namespace PoissonBinomialComparison

noncomputable def continuousSwitchHeight (c x : ℝ) : ℝ :=
  x ^ c * (1 - x) ^ (1 - c)

noncomputable def continuousSwitchLogHeight (c x : ℝ) : ℝ :=
  c * Real.log x + (1 - c) * Real.log (1 - x)

def IsContinuousSwitch (c γ a b : ℝ) : Prop :=
  0 < b ∧ b < a ∧ a < 1 ∧ a - b = γ ∧
    continuousSwitchLogHeight c a = continuousSwitchLogHeight c b

theorem continuousSwitchHeight_pos (c : ℝ) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    0 < continuousSwitchHeight c x :=
  mul_pos (Real.rpow_pos_of_pos hx0 c) (Real.rpow_pos_of_pos (sub_pos.mpr hx1) (1 - c))

theorem log_continuousSwitchHeight (c : ℝ) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    Real.log (continuousSwitchHeight c x) = continuousSwitchLogHeight c x := by
  rw [continuousSwitchHeight, Real.log_mul
    (Real.rpow_pos_of_pos hx0 c).ne'
    (Real.rpow_pos_of_pos (sub_pos.mpr hx1) (1 - c)).ne',
    Real.log_rpow hx0, Real.log_rpow (sub_pos.mpr hx1)]
  rfl

theorem continuousSwitchHeight_eq_iff (c : ℝ) {a b : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) (hb0 : 0 < b) (hb1 : b < 1) :
    continuousSwitchHeight c a = continuousSwitchHeight c b ↔
      continuousSwitchLogHeight c a = continuousSwitchLogHeight c b := by
  constructor
  · intro h
    simpa only [log_continuousSwitchHeight c ha0 ha1,
      log_continuousSwitchHeight c hb0 hb1] using congrArg Real.log h
  · intro h
    apply Real.log_injOn_pos (continuousSwitchHeight_pos c ha0 ha1)
      (continuousSwitchHeight_pos c hb0 hb1)
    simpa only [log_continuousSwitchHeight c ha0 ha1,
      log_continuousSwitchHeight c hb0 hb1] using h

theorem exists_continuousSwitch {c γ : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) : ∃ a b : ℝ, IsContinuousSwitch c γ a b := by
  let H : ℝ → ℝ := fun b ↦ continuousSwitchHeight c (b + γ) - continuousSwitchHeight c b
  have hc' : 0 < 1 - c := sub_pos.mpr hc1
  have hzero : continuousSwitchHeight c 0 = 0 := by
    simp [continuousSwitchHeight, Real.zero_rpow hc0.ne']
  have hone : continuousSwitchHeight c 1 = 0 := by
    simp [continuousSwitchHeight, Real.zero_rpow hc'.ne']
  have H0 : 0 < H 0 := by simpa [H, hzero] using continuousSwitchHeight_pos c hγ0 hγ1
  have H1 : H (1 - γ) < 0 := by
    have heq : 1 - γ + γ = 1 := by ring
    simp only [H, heq, hone, zero_sub, neg_neg_iff_pos]
    exact continuousSwitchHeight_pos c (by linarith) (by linarith)
  have hheight : Continuous (continuousSwitchHeight c) := by
    exact (Real.continuous_rpow_const hc0.le).mul
      ((Real.continuous_rpow_const hc'.le).comp (continuous_const.sub continuous_id))
  have hcont : ContinuousOn H (Set.Icc 0 (1 - γ)) :=
    ((hheight.comp (continuous_id.add continuous_const)).sub hheight).continuousOn
  obtain ⟨b, hb, heq⟩ := intermediate_value_Icc' (by linarith : 0 ≤ 1 - γ) hcont ⟨H1.le, H0.le⟩
  have hb0 : 0 < b := by
    apply lt_of_le_of_ne hb.1
    intro h
    subst b
    linarith
  have hb1 : b < 1 - γ := by
    apply lt_of_le_of_ne hb.2
    intro h
    rw [h] at heq
    linarith
  refine ⟨b + γ, b, hb0, by linarith, by linarith, by ring, ?_⟩
  exact (continuousSwitchHeight_eq_iff c (by linarith) (by linarith) hb0 (by linarith)).mp
    (sub_eq_zero.mp heq)

private theorem continuous_switch_ratio_strictAntiOn {c γ : ℝ}
    (hc0 : 0 < c) (hc1 : c < 1) (hγ : 0 < γ) :
    StrictAntiOn (fun b : ℝ ↦ ((b + γ) / b) ^ c *
      ((1 - (b + γ)) / (1 - b)) ^ (1 - c)) (Set.Ioo 0 (1 - γ)) := by
  intro b₁ hb₁ b₂ hb₂ hlt
  have hb₁' : 0 < 1 - b₁ := by linarith [hb₁.2]
  have hb₂' : 0 < 1 - b₂ := by linarith [hb₂.2]
  have hr₁ : (b₂ + γ) / b₂ < (b₁ + γ) / b₁ := by
    apply (div_lt_div_iff₀ hb₂.1 hb₁.1).2
    nlinarith
  have hr₂ : (1 - (b₂ + γ)) / (1 - b₂) < (1 - (b₁ + γ)) / (1 - b₁) := by
    apply (div_lt_div_iff₀ hb₂' hb₁').2
    nlinarith
  have hp₁ : 0 < (b₂ + γ) / b₂ := div_pos (by linarith [hb₂.1]) hb₂.1
  have hp₂ : 0 < (1 - (b₁ + γ)) / (1 - b₁) := div_pos (by linarith [hb₁.2]) hb₁'
  have hp₂' : 0 < (1 - (b₂ + γ)) / (1 - b₂) := div_pos (by linarith [hb₂.2]) hb₂'
  exact mul_lt_mul_of_pos (Real.rpow_lt_rpow hp₁.le hr₁ hc0)
    (Real.rpow_lt_rpow hp₂'.le hr₂ (sub_pos.mpr hc1))
    (Real.rpow_pos_of_pos hp₁ _) (Real.rpow_pos_of_pos hp₂ _)

private theorem continuous_switch_ratio_eq_one {c γ a b : ℝ} (h : IsContinuousSwitch c γ a b) :
    ((b + γ) / b) ^ c * ((1 - (b + γ)) / (1 - b)) ^ (1 - c) = 1 := by
  have ha0 : 0 < a := lt_trans h.1 h.2.1
  have hb1 : b < 1 := lt_trans h.2.1 h.2.2.1
  have hab : b + γ = a := by linarith [h.2.2.2.1]
  have heq := (continuousSwitchHeight_eq_iff c ha0 h.2.2.1 h.1 hb1).mpr h.2.2.2.2
  rw [hab, Real.div_rpow ha0.le h.1.le,
    Real.div_rpow (sub_nonneg.mpr h.2.2.1.le) (sub_nonneg.mpr hb1.le), div_mul_div_comm]
  change continuousSwitchHeight c a / continuousSwitchHeight c b = 1
  rw [heq, div_self (continuousSwitchHeight_pos c h.1 hb1).ne']

theorem continuousSwitch_unique {c γ a₁ b₁ a₂ b₂ : ℝ}
    (hc0 : 0 < c) (hc1 : c < 1) (hγ : 0 < γ)
    (h₁ : IsContinuousSwitch c γ a₁ b₁) (h₂ : IsContinuousSwitch c γ a₂ b₂) :
    a₁ = a₂ ∧ b₁ = b₂ := by
  have hb₁ : b₁ ∈ Set.Ioo 0 (1 - γ) := ⟨h₁.1, by linarith [h₁.2.2.1, h₁.2.2.2.1]⟩
  have hb₂ : b₂ ∈ Set.Ioo 0 (1 - γ) := ⟨h₂.1, by linarith [h₂.2.2.1, h₂.2.2.2.1]⟩
  have heq := (continuous_switch_ratio_strictAntiOn hc0 hc1 hγ).injOn hb₁ hb₂
    ((continuous_switch_ratio_eq_one h₁).trans (continuous_switch_ratio_eq_one h₂).symm)
  exact ⟨by linarith [h₁.2.2.2.1, h₂.2.2.2.1], heq⟩

theorem existsUnique_continuousSwitch {c γ : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) : ∃! ab : ℝ × ℝ, IsContinuousSwitch c γ ab.1 ab.2 := by
  obtain ⟨a, b, h⟩ := exists_continuousSwitch hc0 hc1 hγ0 hγ1
  refine ⟨(a, b), h, ?_⟩
  intro ab hab
  exact Prod.ext (continuousSwitch_unique hc0 hc1 hγ0 hab h).1
    (continuousSwitch_unique hc0 hc1 hγ0 hab h).2

theorem IsContinuousSwitch.log_ratio_eq_zero {c γ a b : ℝ} (h : IsContinuousSwitch c γ a b) :
    c * Real.log (a / b) + (1 - c) * Real.log ((1 - a) / (1 - b)) = 0 := by
  have ha0 : a ≠ 0 := (lt_trans h.1 h.2.1).ne'
  have ha1 : 1 - a ≠ 0 := (sub_pos.mpr h.2.2.1).ne'
  have hb1 : 1 - b ≠ 0 := (sub_pos.mpr (lt_trans h.2.1 h.2.2.1)).ne'
  rw [Real.log_div ha0 h.1.ne', Real.log_div ha1 hb1]
  have heq := h.2.2.2.2
  unfold continuousSwitchLogHeight at heq
  linarith

theorem hasStrictDerivAt_continuousSwitchLogHeight (c : ℝ) {x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) :
    HasStrictDerivAt (continuousSwitchLogHeight c) ((c - x) / (x * (1 - x))) x := by
  have hx1' : 1 - x ≠ 0 := (sub_pos.mpr hx1).ne'
  have hd := ((Real.hasStrictDerivAt_log hx0.ne').const_mul c).add
    ((((hasStrictDerivAt_const x (1 : ℝ)).sub (hasStrictDerivAt_id x)).log hx1').const_mul (1 - c))
  convert! hd using 1
  · dsimp only [Pi.sub_apply, id_eq]
    field_simp
    ring

theorem IsContinuousSwitch.center_bounds {c γ a b : ℝ} (h : IsContinuousSwitch c γ a b) :
    b < c ∧ c < a := by
  have hcont : ContinuousOn (continuousSwitchLogHeight c) (Set.Icc b a) := by
    intro x hx
    exact (hasStrictDerivAt_continuousSwitchLogHeight c (lt_of_lt_of_le h.1 hx.1)
      (lt_of_le_of_lt hx.2 h.2.2.1)).hasDerivAt.continuousAt.continuousWithinAt
  obtain ⟨x, hx, hd⟩ := exists_hasDerivAt_eq_zero h.2.1 hcont h.2.2.2.2.symm
    (fun x hx ↦ (hasStrictDerivAt_continuousSwitchLogHeight c (lt_trans h.1 hx.1)
      (lt_trans hx.2 h.2.2.1)).hasDerivAt)
  have hx0 : 0 < x := lt_trans h.1 hx.1
  have hx1 : 0 < 1 - x := sub_pos.mpr (lt_trans hx.2 h.2.2.1)
  have hcx : c - x = 0 := (div_eq_zero_iff.mp hd).resolve_right (mul_pos hx0 hx1).ne'
  have hxc : x = c := by linarith
  exact hxc ▸ hx

theorem IsContinuousSwitch.reflect {c γ a b : ℝ} (h : IsContinuousSwitch c γ a b) :
    IsContinuousSwitch (1 - c) γ (1 - b) (1 - a) := by
  refine ⟨by linarith [h.2.2.1], by linarith [h.2.1], by linarith [h.1],
    by linarith [h.2.2.2.1], ?_⟩
  have heq := h.2.2.2.2
  simp only [continuousSwitchLogHeight, sub_sub_cancel] at heq ⊢
  linarith

theorem isSwitch_iff_isContinuousSwitch {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    (γ a b : ℝ) : IsSwitch n j γ a b ↔ IsContinuousSwitch ((j : ℝ) / n) γ a b := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hlog (ha0 : 0 < a) (ha1 : a < 1) (hb0 : 0 < b) (hb1 : b < 1) :
      a ^ j * (1 - a) ^ (n - j) = b ^ j * (1 - b) ^ (n - j) ↔
        continuousSwitchLogHeight ((j : ℝ) / n) a =
          continuousSwitchLogHeight ((j : ℝ) / n) b := by
    have hapos : 0 < a ^ j * (1 - a) ^ (n - j) :=
      mul_pos (pow_pos ha0 _) (pow_pos (sub_pos.mpr ha1) _)
    have hbpos : 0 < b ^ j * (1 - b) ^ (n - j) :=
      mul_pos (pow_pos hb0 _) (pow_pos (sub_pos.mpr hb1) _)
    have hlogA : Real.log (a ^ j * (1 - a) ^ (n - j)) =
        (j : ℝ) * Real.log a + ((n : ℝ) - j) * Real.log (1 - a) := by
      rw [Real.log_mul (pow_pos ha0 _).ne' (pow_pos (sub_pos.mpr ha1) _).ne',
        Real.log_pow, Real.log_pow, Nat.cast_sub hjn.le]
    have hlogB : Real.log (b ^ j * (1 - b) ^ (n - j)) =
        (j : ℝ) * Real.log b + ((n : ℝ) - j) * Real.log (1 - b) := by
      rw [Real.log_mul (pow_pos hb0 _).ne' (pow_pos (sub_pos.mpr hb1) _).ne',
        Real.log_pow, Real.log_pow, Nat.cast_sub hjn.le]
    constructor
    · intro heq
      have h := congrArg Real.log heq
      rw [hlogA, hlogB] at h
      unfold continuousSwitchLogHeight
      field_simp
      nlinarith only [h]
    · intro heq
      apply Real.log_injOn_pos hapos hbpos
      rw [hlogA, hlogB]
      unfold continuousSwitchLogHeight at heq
      field_simp at heq
      nlinarith only [heq]
  constructor
  · intro h
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1,
      (hlog (lt_trans h.1 h.2.1) h.2.2.1 h.1 (lt_trans h.2.1 h.2.2.1)).mp h.2.2.2.2⟩
  · intro h
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1,
      (hlog (lt_trans h.1 h.2.1) h.2.2.1 h.1 (lt_trans h.2.1 h.2.2.1)).mpr h.2.2.2.2⟩

noncomputable def continuousSwitchPair (c γ : ℝ) : ℝ × ℝ :=
  if h : 0 < c ∧ c < 1 ∧ 0 < γ ∧ γ < 1 then
    Classical.choose (existsUnique_continuousSwitch h.1 h.2.1 h.2.2.1 h.2.2.2).exists
  else if γ ≤ 0 then (c, c) else (1, 0)

noncomputable def continuousSwitchUpper (c γ : ℝ) : ℝ := (continuousSwitchPair c γ).1

noncomputable def continuousSwitchLower (c γ : ℝ) : ℝ := (continuousSwitchPair c γ).2

noncomputable def continuousSwitchRatio (c γ : ℝ) : ℝ :=
  (continuousSwitchUpper c γ - c) * (c - continuousSwitchLower c γ) / (c * (1 - c))

theorem continuousSwitchPair_spec {c γ : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    IsContinuousSwitch c γ (continuousSwitchUpper c γ) (continuousSwitchLower c γ) := by
  have h : 0 < c ∧ c < 1 ∧ 0 < γ ∧ γ < 1 := ⟨hc0, hc1, hγ0, hγ1⟩
  simp only [continuousSwitchUpper, continuousSwitchLower, continuousSwitchPair, dif_pos h]
  exact Classical.choose_spec (existsUnique_continuousSwitch hc0 hc1 hγ0 hγ1).exists

theorem IsContinuousSwitch.eq_continuousSwitchPair {c γ a b : ℝ}
    (h : IsContinuousSwitch c γ a b) (hc0 : 0 < c) (hc1 : c < 1) :
    a = continuousSwitchUpper c γ ∧ b = continuousSwitchLower c γ := by
  have hγ0 : 0 < γ := by linarith [h.2.1, h.2.2.2.1]
  have hγ1 : γ < 1 := by linarith [h.1, h.2.2.1, h.2.2.2.1]
  exact continuousSwitch_unique hc0 hc1 hγ0 h (continuousSwitchPair_spec hc0 hc1 hγ0 hγ1)

theorem continuousSwitch_at_ratio {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    continuousSwitchUpper ((j : ℝ) / n) γ = switchUpper n j γ ∧
      continuousSwitchLower ((j : ℝ) / n) γ = switchLower n j γ := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hc0 : (0 : ℝ) < (j : ℝ) / n := div_pos (by exact_mod_cast hj) hn
  have hc1 : (j : ℝ) / n < 1 := (div_lt_one hn).2 (by exact_mod_cast hjn)
  have hs := (isSwitch_iff_isContinuousSwitch hj hjn γ _ _).mp (switchPair_spec hj hjn hγ0 hγ1)
  have heq := hs.eq_continuousSwitchPair hc0 hc1
  exact ⟨heq.1.symm, heq.2.symm⟩

theorem continuousSwitchPair_reflection {c γ : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    continuousSwitchUpper (1 - c) γ = 1 - continuousSwitchLower c γ ∧
      continuousSwitchLower (1 - c) γ = 1 - continuousSwitchUpper c γ := by
  have h := ((continuousSwitchPair_spec hc0 hc1 hγ0 hγ1).reflect).eq_continuousSwitchPair
    (by linarith) (by linarith)
  exact ⟨h.1.symm, h.2.symm⟩

theorem continuousSwitchRatio_bounds {c γ : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    0 < continuousSwitchRatio c γ ∧ continuousSwitchRatio c γ < 1 := by
  have hs := continuousSwitchPair_spec hc0 hc1 hγ0 hγ1
  have hc := hs.center_bounds
  have hv : 0 < c * (1 - c) := mul_pos hc0 (sub_pos.mpr hc1)
  have ha0 := lt_trans hs.1 hs.2.1
  have ha1 := sub_pos.mpr hs.2.2.1
  have hb1 := sub_pos.mpr (lt_trans hs.2.1 hs.2.2.1)
  refine ⟨div_pos (mul_pos (sub_pos.mpr hc.2) (sub_pos.mpr hc.1)) hv, ?_⟩
  apply (div_lt_one hv).2
  have hid := switch_denominator_identity c (continuousSwitchUpper c γ) (continuousSwitchLower c γ)
  have hpos := add_pos (mul_pos (mul_pos hc0 ha1) hb1)
    (mul_pos (mul_pos (sub_pos.mpr hc1) ha0) hs.1)
  linarith

end PoissonBinomialComparison

-- SwitchDerivative
namespace PoissonBinomialComparison

open Filter
open scoped Topology

private theorem hasStrictDerivAt_height {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    (x : ℝ) :
    HasStrictDerivAt (fun u : ℝ ↦ u ^ j * (1 - u) ^ (n - j))
      (x ^ (j - 1) * (1 - x) ^ (n - j - 1) * ((j : ℝ) - n * x)) x := by
  have hd := ((hasStrictDerivAt_id x).pow j).mul
    (((hasStrictDerivAt_const x (1 : ℝ)).sub (hasStrictDerivAt_id x)).pow (n - j))
  convert hd using 1 <;> try rfl
  dsimp only [Pi.mul_apply, Pi.pow_apply, Pi.sub_apply, id_eq]
  have hjpow : x ^ j = x ^ (j - 1) * x := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ j)]
  have hnjpow : (1 - x) ^ (n - j) = (1 - x) ^ (n - j - 1) * (1 - x) := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ n - j)]
  rw [hjpow, hnjpow, Nat.cast_sub hjn.le]
  ring

private theorem implicit_height_solution {g : ℝ → ℝ} {γ b da db : ℝ}
    (ha : HasStrictDerivAt g da (γ + b)) (hb : HasStrictDerivAt g db b)
    (hne : da - db ≠ 0) :
    ∃ ψ : ℝ → ℝ, DifferentiableAt ℝ ψ γ ∧ Tendsto ψ (𝓝 γ) (𝓝 b) ∧
      ∀ᶠ t in 𝓝 γ, g (t + ψ t) - g (ψ t) = g (γ + b) - g b := by
  let L : (ℝ × ℝ) →L[ℝ] ℝ :=
    da • (ContinuousLinearMap.fst ℝ ℝ ℝ + ContinuousLinearMap.snd ℝ ℝ ℝ) -
      db • ContinuousLinearMap.snd ℝ ℝ ℝ
  have hF : HasStrictFDerivAt (fun z : ℝ × ℝ ↦ g (z.1 + z.2) - g z.2) L (γ, b) := by
    exact (ha.comp_hasStrictFDerivAt (γ, b)
      (hasStrictFDerivAt_fst.add hasStrictFDerivAt_snd)).sub
      (hb.comp_hasStrictFDerivAt (γ, b) hasStrictFDerivAt_snd)
  have hL : L ∘L ContinuousLinearMap.inr ℝ ℝ ℝ =
      (da - db) • ContinuousLinearMap.id ℝ ℝ := by
    ext
    simp [L]
  have hinv : (L ∘L ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible := by
    rw [hL]
    apply ContinuousLinearMap.IsInvertible.of_inverse
      (g := (da - db)⁻¹ • ContinuousLinearMap.id ℝ ℝ)
    · ext
      simp [hne]
    · ext
      simp [hne]
  refine ⟨hF.implicitFunctionOfProdDomain hinv,
    (hF.hasStrictFDerivAt_implicitFunctionOfProdDomain hinv).hasFDerivAt.differentiableAt,
    hF.tendsto_implicitFunctionOfProdDomain hinv, ?_⟩
  exact hF.eventually_apply_implicitFunctionOfProdDomain hinv

theorem differentiableAt_switchLower {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    DifferentiableAt ℝ (switchLower n j) γ := by
  let a := switchUpper n j γ
  let b := switchLower n j γ
  have hs : IsSwitch n j γ a b := switchPair_spec hj hjn hγ0 hγ1
  have hc := hs.center_bounds hj hjn
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have ha0 : 0 < a := lt_trans hs.1 hs.2.1
  have ha1 : 0 < 1 - a := by linarith [hs.2.2.1]
  have hb1 : 0 < 1 - b := by linarith [hs.2.1, hs.2.2.1]
  have hda : a ^ (j - 1) * (1 - a) ^ (n - j - 1) * ((j : ℝ) - n * a) < 0 := by
    have hja : (j : ℝ) < a * n := (div_lt_iff₀ hn).mp hc.2
    exact mul_neg_of_pos_of_neg (mul_pos (pow_pos ha0 _) (pow_pos ha1 _)) (by nlinarith)
  have hdb : 0 < b ^ (j - 1) * (1 - b) ^ (n - j - 1) * ((j : ℝ) - n * b) := by
    have hjb : b * n < (j : ℝ) := (lt_div_iff₀ hn).mp hc.1
    exact mul_pos (mul_pos (pow_pos hs.1 _) (pow_pos hb1 _)) (by nlinarith)
  have hab : γ + b = a := by linarith [hs.2.2.2.1]
  obtain ⟨ψ, hψd, hψt, hψeq⟩ := implicit_height_solution (γ := γ) (b := b)
    (by rw [hab]; exact hasStrictDerivAt_height hj hjn a)
    (hasStrictDerivAt_height hj hjn b) (by linarith :
      a ^ (j - 1) * (1 - a) ^ (n - j - 1) * ((j : ℝ) - n * a) -
        b ^ (j - 1) * (1 - b) ^ (n - j - 1) * ((j : ℝ) - n * b) ≠ 0)
  have heq : (switchLower n j) =ᶠ[𝓝 γ] ψ := by
    have evb : ∀ᶠ t in 𝓝 γ, 0 < ψ t := hψt.eventually (Ioi_mem_nhds hs.1)
    have hva : γ + b < 1 := hab ▸ hs.2.2.1
    have eva : ∀ᶠ t in 𝓝 γ, t + ψ t < 1 :=
      (tendsto_id.add hψt).eventually (Iio_mem_nhds hva)
    filter_upwards [hψeq, evb, eva, Ioo_mem_nhds hγ0 hγ1] with t ht htb hta htγ
    have htS : IsSwitch n j t (t + ψ t) (ψ t) := by
      refine ⟨htb, by linarith [htγ.1], hta, by ring, ?_⟩
      rw [hab, hs.2.2.2.2, sub_self] at ht
      exact sub_eq_zero.mp ht
    exact (htS.eq_switchPair hj hjn).2.symm
  exact hψd.congr_of_eventuallyEq heq

theorem differentiableAt_switchUpper {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    DifferentiableAt ℝ (switchUpper n j) γ := by
  have heq : switchUpper n j =ᶠ[𝓝 γ] (fun t ↦ t + switchLower n j t) := by
    filter_upwards [Ioo_mem_nhds hγ0 hγ1] with t ht
    have h := switchUpper_sub_switchLower hj hjn ht.1 ht.2
    linarith
  exact (differentiableAt_id.add (differentiableAt_switchLower hj hjn hγ0 hγ1)).congr_of_eventuallyEq heq

private theorem height_derivative_times {n j : ℕ} (hj : 0 < j) (hjn : j < n) (x : ℝ) :
    (x ^ (j - 1) * (1 - x) ^ (n - j - 1) * ((j : ℝ) - n * x)) * (x * (1 - x)) =
      (x ^ j * (1 - x) ^ (n - j)) * ((j : ℝ) - n * x) := by
  have hjpow : x ^ j = x ^ (j - 1) * x := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ j)]
  have hnjpow : (1 - x) ^ (n - j) = (1 - x) ^ (n - j - 1) * (1 - x) := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ n - j)]
  rw [hjpow, hnjpow]
  ring

theorem deriv_switchUpper_sub_lower {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    deriv (switchUpper n j) γ - deriv (switchLower n j) γ = 1 := by
  have hd := (differentiableAt_switchUpper hj hjn hγ0 hγ1).hasDerivAt.sub
    (differentiableAt_switchLower hj hjn hγ0 hγ1).hasDerivAt
  have heq : (fun t : ℝ ↦ t) =ᶠ[𝓝 γ] (switchUpper n j - switchLower n j) := by
    filter_upwards [Ioo_mem_nhds hγ0 hγ1] with t ht
    exact (switchUpper_sub_switchLower hj hjn ht.1 ht.2).symm
  exact (hd.congr_of_eventuallyEq heq).unique (hasDerivAt_id γ)

private theorem deriv_height_equation {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    let a := switchUpper n j γ
    let b := switchLower n j γ
    ((j : ℝ) - n * a) * (b * (1 - b)) * deriv (switchUpper n j) γ =
      ((j : ℝ) - n * b) * (a * (1 - a)) * deriv (switchLower n j) γ := by
  dsimp
  let a := switchUpper n j γ
  let b := switchLower n j γ
  have hs : IsSwitch n j γ a b := switchPair_spec hj hjn hγ0 hγ1
  have hdA := (hasStrictDerivAt_height hj hjn a).hasDerivAt.comp γ
    (differentiableAt_switchUpper hj hjn hγ0 hγ1).hasDerivAt
  have hdB := (hasStrictDerivAt_height hj hjn b).hasDerivAt.comp γ
    (differentiableAt_switchLower hj hjn hγ0 hγ1).hasDerivAt
  have heq : (fun t ↦ (switchUpper n j t) ^ j * (1 - switchUpper n j t) ^ (n - j))
      =ᶠ[𝓝 γ] (fun t ↦ (switchLower n j t) ^ j * (1 - switchLower n j t) ^ (n - j)) := by
    filter_upwards [Ioo_mem_nhds hγ0 hγ1] with t ht
    exact (switchPair_spec hj hjn ht.1 ht.2).2.2.2.2
  have hdEq := hdA.unique (hdB.congr_of_eventuallyEq heq)
  have hm : a ^ j * (1 - a) ^ (n - j) ≠ 0 := by
    have ha0 : 0 < a := lt_trans hs.1 hs.2.1
    exact (mul_pos (pow_pos ha0 _) (pow_pos (by linarith [hs.2.2.1]) _)).ne'
  apply mul_left_cancel₀ hm
  calc
    _ = (a ^ (j - 1) * (1 - a) ^ (n - j - 1) * ((j : ℝ) - n * a)) *
        deriv (switchUpper n j) γ * (a * (1 - a)) * (b * (1 - b)) := by
      convert congrArg (fun z : ℝ ↦ z * deriv (switchUpper n j) γ * (b * (1 - b)))
        (height_derivative_times hj hjn a).symm using 1 <;> dsimp [a, b] <;> ring
    _ = (b ^ (j - 1) * (1 - b) ^ (n - j - 1) * ((j : ℝ) - n * b)) *
        deriv (switchLower n j) γ * (a * (1 - a)) * (b * (1 - b)) := by rw [hdEq]
    _ = _ := by
      rw [hs.2.2.2.2]
      convert congrArg (fun z : ℝ ↦ z * deriv (switchLower n j) γ * (a * (1 - a)))
        (height_derivative_times hj hjn b) using 1 <;> dsimp [a, b] <;> ring

noncomputable def switchRatio (n j : ℕ) (γ : ℝ) : ℝ :=
  let c := (j : ℝ) / n
  (switchUpper n j γ - c) * (c - switchLower n j γ) / (c * (1 - c))

theorem switchRatio_bounds {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    0 < switchRatio n j γ ∧ switchRatio n j γ < 1 :=
  (switchPair_spec hj hjn hγ0 hγ1).geometric_ratio_bounds hj hjn

private theorem deriv_switch_equations {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    let a := switchUpper n j γ
    let b := switchLower n j γ
    let c := (j : ℝ) / n
    (a - c) * (b * (1 - b)) * deriv (switchUpper n j) γ +
      (c - b) * (a * (1 - a)) * deriv (switchLower n j) γ = 0 := by
  dsimp
  have hh := deriv_height_equation hj hjn hγ0 hγ1
  dsimp at hh
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hnc : (n : ℝ) * ((j : ℝ) / n) = j := mul_div_cancel₀ _ hn
  apply (mul_eq_zero.mp ?_).resolve_left hn
  linear_combination -hh -
    (switchLower n j γ * (1 - switchLower n j γ) * deriv (switchUpper n j) γ -
      switchUpper n j γ * (1 - switchUpper n j γ) * deriv (switchLower n j) γ) * hnc

theorem deriv_switchUpper {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    let a := switchUpper n j γ
    let b := switchLower n j γ
    let c := (j : ℝ) / n
    deriv (switchUpper n j) γ =
      (c - b) * a * (1 - a) / (γ * (c * (1 - c)) * (1 - switchRatio n j γ)) := by
  dsimp
  let a := switchUpper n j γ
  let b := switchLower n j γ
  let c := (j : ℝ) / n
  have hs : IsSwitch n j γ a b := switchPair_spec hj hjn hγ0 hγ1
  have hc := hs.center_bounds hj hjn
  have hv : 0 < c * (1 - c) :=
    mul_pos (lt_trans hs.1 hc.1) (by linarith [hc.2, hs.2.2.1])
  have hR : 0 < 1 - switchRatio n j γ := sub_pos.mpr (switchRatio_bounds hj hjn hγ0 hγ1).2
  have hden : γ * (c * (1 - c)) * (1 - switchRatio n j γ) ≠ 0 :=
    (mul_pos (mul_pos hγ0 hv) hR).ne'
  apply (eq_div_iff hden).2
  have hn := hs.normalized_denominator hj hjn
  change c * (1 - c) * (1 - switchRatio n j γ) =
    c * (1 - a) * (1 - b) + (1 - c) * a * b at hn
  have hdeq : γ * (c * (1 - c)) * (1 - switchRatio n j γ) =
      (a - c) * (b * (1 - b)) + (c - b) * (a * (1 - a)) := by
    rw [mul_assoc, hn, ← hs.2.2.2.1]
    ring
  change deriv (switchUpper n j) γ * (γ * (c * (1 - c)) * (1 - switchRatio n j γ)) =
    (c - b) * a * (1 - a)
  rw [hdeq]
  have heq := deriv_switch_equations hj hjn hγ0 hγ1
  have hgap := deriv_switchUpper_sub_lower hj hjn hγ0 hγ1
  change (a - c) * (b * (1 - b)) * deriv (switchUpper n j) γ +
    (c - b) * (a * (1 - a)) * deriv (switchLower n j) γ = 0 at heq
  linear_combination heq + ((c - b) * (a * (1 - a))) * hgap

theorem deriv_switchLower {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    let a := switchUpper n j γ
    let b := switchLower n j γ
    let c := (j : ℝ) / n
    deriv (switchLower n j) γ =
      -(a - c) * b * (1 - b) / (γ * (c * (1 - c)) * (1 - switchRatio n j γ)) := by
  dsimp
  let a := switchUpper n j γ
  let b := switchLower n j γ
  let c := (j : ℝ) / n
  have hs : IsSwitch n j γ a b := switchPair_spec hj hjn hγ0 hγ1
  have hc := hs.center_bounds hj hjn
  have hv : 0 < c * (1 - c) :=
    mul_pos (lt_trans hs.1 hc.1) (by linarith [hc.2, hs.2.2.1])
  have hR : 0 < 1 - switchRatio n j γ := sub_pos.mpr (switchRatio_bounds hj hjn hγ0 hγ1).2
  have hden : γ * (c * (1 - c)) * (1 - switchRatio n j γ) ≠ 0 :=
    (mul_pos (mul_pos hγ0 hv) hR).ne'
  apply (eq_div_iff hden).2
  have hn := hs.normalized_denominator hj hjn
  change c * (1 - c) * (1 - switchRatio n j γ) =
    c * (1 - a) * (1 - b) + (1 - c) * a * b at hn
  have hdeq : γ * (c * (1 - c)) * (1 - switchRatio n j γ) =
      (a - c) * (b * (1 - b)) + (c - b) * (a * (1 - a)) := by
    rw [mul_assoc, hn, ← hs.2.2.2.1]
    ring
  change deriv (switchLower n j) γ * (γ * (c * (1 - c)) * (1 - switchRatio n j γ)) =
    -(a - c) * b * (1 - b)
  rw [hdeq]
  have heq := deriv_switch_equations hj hjn hγ0 hγ1
  have hgap := deriv_switchUpper_sub_lower hj hjn hγ0 hγ1
  change (a - c) * (b * (1 - b)) * deriv (switchUpper n j) γ +
    (c - b) * (a * (1 - a)) * deriv (switchLower n j) γ = 0 at heq
  linear_combination heq - ((a - c) * (b * (1 - b))) * hgap

theorem switchMass_pos {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) : 0 < switchMass n j γ := by
  have hs := switchPair_spec hj hjn hγ0 hγ1
  have ha0 : 0 < switchUpper n j γ := lt_trans hs.1 hs.2.1
  have ha1 : 0 < 1 - switchUpper n j γ := by linarith [hs.2.2.1]
  have hc : (0 : ℝ) < n.choose j := by exact_mod_cast Nat.choose_pos hjn.le
  simp only [switchMass, pbMass_const]
  exact mul_pos (mul_pos hc (pow_pos ha0 _)) (pow_pos ha1 _)

private theorem hasDerivAt_switchMass_raw {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    let a := switchUpper n j γ
    HasDerivAt (switchMass n j)
      (switchMass n j γ * ((j : ℝ) - n * a) / (a * (1 - a)) * deriv (switchUpper n j) γ) γ := by
  let a := switchUpper n j γ
  have hs := switchPair_spec hj hjn hγ0 hγ1
  have ha0 : a ≠ 0 := (lt_trans hs.1 hs.2.1).ne'
  have ha1 : 1 - a ≠ 0 := (sub_pos.mpr hs.2.2.1).ne'
  have hd := ((hasStrictDerivAt_height hj hjn a).hasDerivAt.comp γ
    (differentiableAt_switchUpper hj hjn hγ0 hγ1).hasDerivAt).const_mul (n.choose j : ℝ)
  convert hd using 1 <;> try rfl
  · funext t
    simp [switchMass, pbMass_const, mul_assoc]
  · change switchMass n j γ * ((j : ℝ) - n * a) / (a * (1 - a)) * _ = _
    rw [div_mul_eq_mul_div]
    apply (div_eq_iff (mul_ne_zero ha0 ha1)).2
    have ht := height_derivative_times hj hjn a
    simp only [switchMass, pbMass_const]
    convert congrArg (fun z : ℝ ↦ (n.choose j : ℝ) * z * deriv (switchUpper n j) γ)
      ht.symm using 1 <;> dsimp [a] <;> ring

theorem hasDerivAt_switchMass {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    HasDerivAt (switchMass n j)
      (-(n : ℝ) * switchRatio n j γ / (γ * (1 - switchRatio n j γ)) * switchMass n j γ) γ := by
  have hd := hasDerivAt_switchMass_raw hj hjn hγ0 hγ1
  dsimp at hd
  convert hd using 1; try rfl
  let a := switchUpper n j γ
  let b := switchLower n j γ
  let c := (j : ℝ) / n
  let v := c * (1 - c)
  let R := switchRatio n j γ
  have hs : IsSwitch n j γ a b := switchPair_spec hj hjn hγ0 hγ1
  have hc := hs.center_bounds hj hjn
  have ha0 : a ≠ 0 := (lt_trans hs.1 hs.2.1).ne'
  have ha1 : 1 - a ≠ 0 := (sub_pos.mpr hs.2.2.1).ne'
  have hv : v ≠ 0 := (mul_pos (lt_trans hs.1 hc.1) (by linarith [hc.2, hs.2.2.1])).ne'
  have hR : 1 - R ≠ 0 := (sub_pos.mpr (switchRatio_bounds hj hjn hγ0 hγ1).2).ne'
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hnc : (n : ℝ) * c = j := mul_div_cancel₀ _ hn
  have hRv : R * v = (a - c) * (c - b) := div_mul_cancel₀ _ hv
  rw [deriv_switchUpper hj hjn hγ0 hγ1]
  change -(n : ℝ) * R / (γ * (1 - R)) * switchMass n j γ =
    switchMass n j γ * ((j : ℝ) - n * a) / (a * (1 - a)) *
      ((c - b) * a * (1 - a) / (γ * v * (1 - R)))
  field_simp
  linear_combination - (switchMass n j γ * (n : ℝ)) * hRv +
    (switchMass n j γ * (c - b)) * hnc

theorem deriv_switchMass_div {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    deriv (switchMass n j) γ / switchMass n j γ =
      -(n : ℝ) * switchRatio n j γ / (γ * (1 - switchRatio n j γ)) := by
  rw [(hasDerivAt_switchMass hj hjn hγ0 hγ1).deriv]
  exact mul_div_cancel_right₀ _ (switchMass_pos hj hjn hγ0 hγ1).ne'

private theorem tail_density_times {n j : ℕ} (hj : 0 < j) (hjn : j < n) (t : ℝ) :
    ((n : ℝ) * pbMass (fun _ : Fin (n - 1) ↦ t) (j - 1)) * t =
      (j : ℝ) * pbMass (fun _ : Fin n ↦ t) j := by
  have hcoeff : (n : ℝ) * ((n - 1).choose (j - 1) : ℝ) = (n.choose j : ℝ) * j := by
    have hn1 : 1 ≤ n := by omega
    have hj1 : 1 ≤ j := by omega
    have hh := Nat.add_one_mul_choose_eq (n - 1) (j - 1)
    rw [Nat.sub_add_cancel hn1, Nat.sub_add_cancel hj1] at hh
    exact_mod_cast hh
  have hexp : n - 1 - (j - 1) = n - j := by omega
  have hpow : t ^ j = t ^ (j - 1) * t := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ j)]
  simp only [pbMass_const, hexp]
  rw [hpow]
  linear_combination (t ^ (j - 1) * (1 - t) ^ (n - j) * t) * hcoeff

private theorem hasDerivAt_tail_density_div {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun u : ℝ ↦ pbTail (fun _ : Fin n ↦ u) j)
      ((j : ℝ) * pbMass (fun _ : Fin n ↦ t) j / t) t := by
  have heq : (n : ℝ) * pbMass (fun _ : Fin (n - 1) ↦ t) (j - 1) =
      (j : ℝ) * pbMass (fun _ : Fin n ↦ t) j / t :=
    (eq_div_iff ht).2 (tail_density_times hj hjn t)
  rw [← heq]
  exact hasDerivAt_pbTail_const n j hj t

theorem hasDerivAt_switchValue {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    HasDerivAt (switchValue n j)
      ((n : ℝ) * switchMass n j γ / (1 - switchRatio n j γ)) γ := by
  let a := switchUpper n j γ
  let b := switchLower n j γ
  let c := (j : ℝ) / n
  let v := c * (1 - c)
  let R := switchRatio n j γ
  have hs : IsSwitch n j γ a b := switchPair_spec hj hjn hγ0 hγ1
  have hc := hs.center_bounds hj hjn
  have ha0 : a ≠ 0 := (lt_trans hs.1 hs.2.1).ne'
  have hb0 : b ≠ 0 := hs.1.ne'
  have hv : v ≠ 0 := (mul_pos (lt_trans hs.1 hc.1) (by linarith [hc.2, hs.2.2.1])).ne'
  have hR : 1 - R ≠ 0 := (sub_pos.mpr (switchRatio_bounds hj hjn hγ0 hγ1).2).ne'
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hnc : (n : ℝ) * c = j := mul_div_cancel₀ _ hn
  have hdA := (hasDerivAt_tail_density_div hj hjn ha0).comp γ
    (differentiableAt_switchUpper hj hjn hγ0 hγ1).hasDerivAt
  have hdB := (hasDerivAt_tail_density_div hj hjn hb0).comp γ
    (differentiableAt_switchLower hj hjn hγ0 hγ1).hasDerivAt
  convert hdA.sub hdB using 1 <;> try rfl
  · change (n : ℝ) * switchMass n j γ / (1 - R) =
      ((j : ℝ) * switchMass n j γ / a) * deriv (switchUpper n j) γ -
        ((j : ℝ) * pbMass (fun _ : Fin n ↦ b) j / b) * deriv (switchLower n j) γ
    rw [← switchMass_eq_lower hj hjn hγ0 hγ1, deriv_switchUpper hj hjn hγ0 hγ1,
      deriv_switchLower hj hjn hγ0 hγ1]
    change (n : ℝ) * switchMass n j γ / (1 - R) =
      ((j : ℝ) * switchMass n j γ / a) * ((c - b) * a * (1 - a) / (γ * v * (1 - R))) -
      ((j : ℝ) * switchMass n j γ / b) * (-(a - c) * b * (1 - b) / (γ * v * (1 - R)))
    field_simp
    dsimp [v]
    linear_combination (switchMass n j γ * (a - b) * (1 - c)) * hnc -
      ((n : ℝ) * switchMass n j γ * c * (1 - c)) * hs.2.2.2.1

theorem deriv_switchValue {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    deriv (switchValue n j) γ = (n : ℝ) * switchMass n j γ / (1 - switchRatio n j γ) :=
  (hasDerivAt_switchValue hj hjn hγ0 hγ1).deriv

theorem deriv_switchValue_eq_mass_sub {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    deriv (switchValue n j) γ =
      (n : ℝ) * switchMass n j γ - γ * deriv (switchMass n j) γ := by
  rw [deriv_switchValue hj hjn hγ0 hγ1, (hasDerivAt_switchMass hj hjn hγ0 hγ1).deriv]
  have hR : 1 - switchRatio n j γ ≠ 0 :=
    (sub_pos.mpr (switchRatio_bounds hj hjn hγ0 hγ1).2).ne'
  field_simp
  ring

theorem continuousOn_switchMass {n j : ℕ} (hj : 0 < j) (hjn : j < n) :
    ContinuousOn (switchMass n j) (Set.Icc 0 1) := by
  intro γ hγ
  by_cases h0 : γ = 0
  · subst γ
    exact (continuousAt_switchMass_zero hj hjn).continuousWithinAt
  by_cases h1 : γ = 1
  · subst γ
    exact (continuousAt_switchMass_one hj hjn).continuousWithinAt
  exact (hasDerivAt_switchMass hj hjn (lt_of_le_of_ne hγ.1 (Ne.symm h0))
    (lt_of_le_of_ne hγ.2 h1)).continuousAt.continuousWithinAt

theorem continuousOn_switchValue {n j : ℕ} (hj : 0 < j) (hjn : j < n) :
    ContinuousOn (switchValue n j) (Set.Icc 0 1) := by
  intro γ hγ
  by_cases h0 : γ = 0
  · subst γ
    exact (continuousAt_switchValue_zero hj hjn).continuousWithinAt
  by_cases h1 : γ = 1
  · subst γ
    exact (continuousAt_switchValue_one hj hjn).continuousWithinAt
  exact (hasDerivAt_switchValue hj hjn (lt_of_le_of_ne hγ.1 (Ne.symm h0))
    (lt_of_le_of_ne hγ.2 h1)).continuousAt.continuousWithinAt

end PoissonBinomialComparison

-- ContinuousSwitchDerivative
namespace PoissonBinomialComparison

open Filter
open scoped Topology

private theorem logarithmic_equation_hasStrictFDerivAt {c γ b : ℝ}
    (hb0 : 0 < b) (ha0 : 0 < γ + b) (ha1 : γ + b < 1) (hb1 : b < 1) :
    HasStrictFDerivAt
      (fun z : ℝ × ℝ ↦ continuousSwitchLogHeight z.1 (γ + z.2) - continuousSwitchLogHeight z.1 z.2)
      ((Real.log (γ + b) - Real.log b - Real.log (1 - (γ + b)) + Real.log (1 - b)) •
          ContinuousLinearMap.fst ℝ ℝ ℝ +
        ((c - (γ + b)) / ((γ + b) * (1 - (γ + b))) - (c - b) / (b * (1 - b))) •
          ContinuousLinearMap.snd ℝ ℝ ℝ) (c, b) := by
  have hS : HasStrictFDerivAt (fun z : ℝ × ℝ ↦ z.2)
      (ContinuousLinearMap.snd ℝ ℝ ℝ) (c, b) := hasStrictFDerivAt_snd
  have hA := (Real.hasStrictDerivAt_log ha0.ne').comp_hasStrictFDerivAt (c, b)
    ((hasStrictFDerivAt_const γ (c, b)).add hS)
  have hB := (Real.hasStrictDerivAt_log hb0.ne').comp_hasStrictFDerivAt (c, b) hS
  have hA1 := (Real.hasStrictDerivAt_log (sub_pos.mpr ha1).ne').comp_hasStrictFDerivAt (c, b)
    ((hasStrictFDerivAt_const (1 : ℝ) (c, b)).sub
      ((hasStrictFDerivAt_const γ (c, b)).add hS))
  have hB1 := (Real.hasStrictDerivAt_log (sub_pos.mpr hb1).ne').comp_hasStrictFDerivAt (c, b)
    ((hasStrictFDerivAt_const (1 : ℝ) (c, b)).sub hS)
  have hC : HasStrictFDerivAt (fun z : ℝ × ℝ ↦ z.1)
      (ContinuousLinearMap.fst ℝ ℝ ℝ) (c, b) := hasStrictFDerivAt_fst
  have hC1 := (hasStrictFDerivAt_const (1 : ℝ) (c, b)).sub hC
  have hd := ((hC.mul hA).add (hC1.mul hA1)).sub ((hC.mul hB).add (hC1.mul hB1))
  have ha1' : 1 - (γ + b) ≠ 0 := (sub_pos.mpr ha1).ne'
  have hb1' : 1 - b ≠ 0 := (sub_pos.mpr hb1).ne'
  convert hd using 1 <;> try rfl
  · apply ContinuousLinearMap.ext
    intro z
    simp
    field_simp [ha1', hb1', ha0.ne', hb0.ne']
    ring

theorem IsContinuousSwitch.lower_partial_neg {c γ a b : ℝ} (h : IsContinuousSwitch c γ a b) :
    (c - a) / (a * (1 - a)) - (c - b) / (b * (1 - b)) < 0 := by
  have hc := h.center_bounds
  have ha0 := lt_trans h.1 h.2.1
  have ha1 := sub_pos.mpr h.2.2.1
  have hb1 := sub_pos.mpr (lt_trans h.2.1 h.2.2.1)
  have hleft := div_neg_of_neg_of_pos (sub_neg.mpr hc.2) (mul_pos ha0 ha1)
  have hright := div_pos (sub_pos.mpr hc.1) (mul_pos h.1 hb1)
  linarith

theorem IsContinuousSwitch.ratio_partial_pos {c γ a b : ℝ} (h : IsContinuousSwitch c γ a b) :
    0 < Real.log a - Real.log b - Real.log (1 - a) + Real.log (1 - b) := by
  have hlog := Real.log_lt_log h.1 h.2.1
  have hlog1 := Real.log_lt_log (sub_pos.mpr h.2.2.1) (by linarith [h.2.1] : 1 - a < 1 - b)
  linarith

theorem hasDerivAt_continuousSwitchLower_count {c γ : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    let a := continuousSwitchUpper c γ
    let b := continuousSwitchLower c γ
    HasDerivAt (fun d ↦ continuousSwitchLower d γ)
      (-(Real.log a - Real.log b - Real.log (1 - a) + Real.log (1 - b)) /
        ((c - a) / (a * (1 - a)) - (c - b) / (b * (1 - b)))) c := by
  let a := continuousSwitchUpper c γ
  let b := continuousSwitchLower c γ
  let A := Real.log a - Real.log b - Real.log (1 - a) + Real.log (1 - b)
  let B := (c - a) / (a * (1 - a)) - (c - b) / (b * (1 - b))
  let L : (ℝ × ℝ) →L[ℝ] ℝ := A • ContinuousLinearMap.fst ℝ ℝ ℝ + B • ContinuousLinearMap.snd ℝ ℝ ℝ
  have hs : IsContinuousSwitch c γ a b := continuousSwitchPair_spec hc0 hc1 hγ0 hγ1
  have hab : γ + b = a := by linarith [hs.2.2.2.1]
  have hB : B ≠ 0 := hs.lower_partial_neg.ne
  have hF : HasStrictFDerivAt
      (fun z : ℝ × ℝ ↦ continuousSwitchLogHeight z.1 (γ + z.2) - continuousSwitchLogHeight z.1 z.2)
      L (c, b) := by
    simpa only [hab] using logarithmic_equation_hasStrictFDerivAt (c := c) (γ := γ)
      hs.1 (hab ▸ lt_trans hs.1 hs.2.1) (hab ▸ hs.2.2.1) (lt_trans hs.2.1 hs.2.2.1)
  have hL : L ∘L ContinuousLinearMap.inr ℝ ℝ ℝ = B • ContinuousLinearMap.id ℝ ℝ := by
    ext
    simp [L]
  have hL1 : L ∘L ContinuousLinearMap.inl ℝ ℝ ℝ = A • ContinuousLinearMap.id ℝ ℝ := by
    ext
    simp [L]
  have hInv1 : (B • ContinuousLinearMap.id ℝ ℝ) ∘L (B⁻¹ • ContinuousLinearMap.id ℝ ℝ) =
      ContinuousLinearMap.id ℝ ℝ := by ext; simp [hB]
  have hInv2 : (B⁻¹ • ContinuousLinearMap.id ℝ ℝ) ∘L (B • ContinuousLinearMap.id ℝ ℝ) =
      ContinuousLinearMap.id ℝ ℝ := by ext; simp [hB]
  have hinv : (L ∘L ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible := by
    rw [hL]
    exact ContinuousLinearMap.IsInvertible.of_inverse hInv1 hInv2
  let ψ := hF.implicitFunctionOfProdDomain hinv
  have hψd : HasDerivAt ψ (-A / B) c := by
    have hd := (hF.hasStrictFDerivAt_implicitFunctionOfProdDomain hinv).hasFDerivAt.hasDerivAt
    rw [hL, hL1, ContinuousLinearMap.inverse_eq hInv1 hInv2] at hd
    simpa [ψ, div_eq_mul_inv, mul_comm] using hd
  have hψt : Tendsto ψ (𝓝 c) (𝓝 b) := hF.tendsto_implicitFunctionOfProdDomain hinv
  have hψeq := hF.eventually_apply_implicitFunctionOfProdDomain hinv
  have heq : (fun d ↦ continuousSwitchLower d γ) =ᶠ[𝓝 c] ψ := by
    have evb : ∀ᶠ d in 𝓝 c, 0 < ψ d := hψt.eventually (Ioi_mem_nhds hs.1)
    have eva : ∀ᶠ d in 𝓝 c, γ + ψ d < 1 :=
      (tendsto_const_nhds.add hψt).eventually (Iio_mem_nhds (hab ▸ hs.2.2.1))
    filter_upwards [hψeq, evb, eva, Ioo_mem_nhds hc0 hc1] with d hd hdb hda hdc
    have hdS : IsContinuousSwitch d γ (γ + ψ d) (ψ d) := by
      refine ⟨hdb, by linarith, hda, by ring, ?_⟩
      change continuousSwitchLogHeight d (γ + ψ d) - continuousSwitchLogHeight d (ψ d) =
        continuousSwitchLogHeight c (γ + b) - continuousSwitchLogHeight c b at hd
      rw [hab, hs.2.2.2.2, sub_self] at hd
      exact sub_eq_zero.mp hd
    exact (hdS.eq_continuousSwitchPair hdc.1 hdc.2).2.symm
  exact hψd.congr_of_eventuallyEq heq

theorem hasDerivAt_continuousSwitchUpper_count {c γ : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    HasDerivAt (fun d ↦ continuousSwitchUpper d γ)
      (deriv (fun d ↦ continuousSwitchLower d γ) c) c := by
  have hd := (hasDerivAt_continuousSwitchLower_count hc0 hc1 hγ0 hγ1).differentiableAt.hasDerivAt
  have heq : (fun d ↦ continuousSwitchUpper d γ) =ᶠ[𝓝 c]
      (fun d ↦ γ + continuousSwitchLower d γ) := by
    filter_upwards [Ioo_mem_nhds hc0 hc1] with d hd
    have h := (continuousSwitchPair_spec hd.1 hd.2 hγ0 hγ1).2.2.2.1
    linarith
  simpa only [zero_add] using ((hasDerivAt_const c γ).add hd).congr_of_eventuallyEq heq

theorem deriv_continuousSwitchLower_count_pos {c γ : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    0 < deriv (fun d ↦ continuousSwitchLower d γ) c := by
  rw [(hasDerivAt_continuousSwitchLower_count hc0 hc1 hγ0 hγ1).deriv]
  have hs := continuousSwitchPair_spec hc0 hc1 hγ0 hγ1
  exact div_pos_of_neg_of_neg (neg_neg_of_pos hs.ratio_partial_pos) hs.lower_partial_neg

theorem deriv_continuousSwitchUpper_count_pos {c γ : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    0 < deriv (fun d ↦ continuousSwitchUpper d γ) c := by
  rw [(hasDerivAt_continuousSwitchUpper_count hc0 hc1 hγ0 hγ1).deriv]
  exact deriv_continuousSwitchLower_count_pos hc0 hc1 hγ0 hγ1

theorem hasDerivAt_continuousSwitchRatio_count {c γ : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    let e := continuousSwitchUpper c γ + continuousSwitchLower c γ - 2 * c
    let t := deriv (fun d ↦ continuousSwitchLower d γ) c
    HasDerivAt (fun d ↦ continuousSwitchRatio d γ)
      (-(((1 - 2 * c) * continuousSwitchRatio c γ - e) + e * t) / (c * (1 - c))) c := by
  let a := continuousSwitchUpper c γ
  let b := continuousSwitchLower c γ
  let t := deriv (fun d ↦ continuousSwitchLower d γ) c
  let v := c * (1 - c)
  let R := continuousSwitchRatio c γ
  have ha := hasDerivAt_continuousSwitchUpper_count hc0 hc1 hγ0 hγ1
  have hb := (hasDerivAt_continuousSwitchLower_count hc0 hc1 hγ0 hγ1).differentiableAt.hasDerivAt
  have hv : v ≠ 0 := (mul_pos hc0 (sub_pos.mpr hc1)).ne'
  have hd := (((ha.sub (hasDerivAt_id c)).mul ((hasDerivAt_id c).sub hb)).div
    ((hasDerivAt_id c).mul ((hasDerivAt_const c (1 : ℝ)).sub (hasDerivAt_id c))) hv)
  convert hd using 1 <;> try rfl
  · change -(((1 - 2 * c) * R - (a + b - 2 * c)) + (a + b - 2 * c) * t) / v =
      (((t - 1) * (c - b) + (a - c) * (1 - t)) * v -
        (a - c) * (c - b) * (1 * (1 - c) + c * (0 - 1))) / v ^ 2
    have hRv : R * v = (a - c) * (c - b) := div_mul_cancel₀ _ hv
    field_simp
    dsimp [v]
    linear_combination -(1 - 2 * c) * hRv

end PoissonBinomialComparison

-- SwitchRatioDerivative
namespace PoissonBinomialComparison

theorem continuousSwitchRatio_at_ratio {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    continuousSwitchRatio ((j : ℝ) / n) γ = switchRatio n j γ := by
  obtain ⟨ha, hb⟩ := continuousSwitch_at_ratio hj hjn hγ0 hγ1
  simp only [continuousSwitchRatio, switchRatio, ha, hb]

private theorem ratio_gap_derivative_algebra {a b c γ v R : ℝ}
    (hγ : γ ≠ 0) (hv : v ≠ 0) (hR : 1 - R ≠ 0)
    (hvv : v = c * (1 - c)) (hRv : R * v = (a - c) * (c - b)) :
    (((c - b) * a * (1 - a) / (γ * v * (1 - R))) * (c - b) -
      (a - c) * (-(a - c) * b * (1 - b) / (γ * v * (1 - R)))) / v =
      2 * R / γ - (a + b - 2 * c) * ((1 - 2 * c) * R - (a + b - 2 * c)) /
        (γ * v * (1 - R)) := by
  field_simp
  rw [hvv] at hRv ⊢
  linear_combination (2 * R * (c * (1 - c)) - 2 * a * b + a + b - 4 * (c * (1 - c))) * hRv

theorem hasDerivAt_switchRatio_gap {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    let c := (j : ℝ) / n
    let e := switchUpper n j γ + switchLower n j γ - 2 * c
    HasDerivAt (switchRatio n j)
      (2 * switchRatio n j γ / γ -
        e * ((1 - 2 * c) * switchRatio n j γ - e) /
          (γ * (c * (1 - c)) * (1 - switchRatio n j γ))) γ := by
  let a := switchUpper n j γ
  let b := switchLower n j γ
  let c := (j : ℝ) / n
  have hs : IsSwitch n j γ a b := switchPair_spec hj hjn hγ0 hγ1
  have hc := hs.center_bounds hj hjn
  have hv : c * (1 - c) ≠ 0 :=
    (mul_pos (lt_trans hs.1 hc.1) (by linarith [hc.2, hs.2.2.1])).ne'
  have hR : 1 - (a - c) * (c - b) / (c * (1 - c)) ≠ 0 :=
    (sub_pos.mpr (switchRatio_bounds hj hjn hγ0 hγ1).2).ne'
  have hA := (differentiableAt_switchUpper hj hjn hγ0 hγ1).hasDerivAt
  have hB := (differentiableAt_switchLower hj hjn hγ0 hγ1).hasDerivAt
  have hd := ((hA.sub_const c).mul ((hasDerivAt_const γ c).sub hB)).div_const (c * (1 - c))
  convert hd using 1 <;> try rfl
  · rw [deriv_switchUpper hj hjn hγ0 hγ1, deriv_switchLower hj hjn hγ0 hγ1]
    have hRv : switchRatio n j γ * (c * (1 - c)) = (a - c) * (c - b) := div_mul_cancel₀ _ hv
    convert (ratio_gap_derivative_algebra hγ0.ne' hv hR rfl hRv).symm using 1 <;>
      dsimp [a, b, c, switchRatio]
    ring

theorem deriv_switchRatio_gap {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    let c := (j : ℝ) / n
    let e := switchUpper n j γ + switchLower n j γ - 2 * c
    deriv (switchRatio n j) γ =
      2 * switchRatio n j γ / γ -
        e * ((1 - 2 * c) * switchRatio n j γ - e) /
          (γ * (c * (1 - c)) * (1 - switchRatio n j γ)) :=
  (hasDerivAt_switchRatio_gap hj hjn hγ0 hγ1).deriv

end PoissonBinomialComparison

-- ContinuousSwitchGeometry
namespace PoissonBinomialComparison

noncomputable section

theorem continuousSwitchLogHeight_strictAntiOn {c : ℝ} (hc : 0 < c) :
    StrictAntiOn (continuousSwitchLogHeight c) (Set.Ioo c 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioo c 1)
  · intro x hx
    exact (hasStrictDerivAt_continuousSwitchLogHeight c (hc.trans hx.1) hx.2).hasDerivAt.continuousAt.continuousWithinAt
  · intro x hx
    have hx' : x ∈ Set.Ioo c 1 := interior_subset hx
    rw [(hasStrictDerivAt_continuousSwitchLogHeight c (hc.trans hx'.1) hx'.2).hasDerivAt.deriv]
    exact div_neg_of_neg_of_pos (sub_neg.mpr hx'.1)
      (mul_pos (hc.trans hx'.1) (sub_pos.mpr hx'.2))

private theorem additive_reflection_height_pos {c b : ℝ}
    (_hc0 : 0 < c) (hc1 : c < 1 / 2) (hb0 : 0 < b) (hbc : b < c) :
    0 < continuousSwitchLogHeight c (2 * c - b) - continuousSwitchLogHeight c b := by
  let G : ℝ → ℝ := fun x ↦ continuousSwitchLogHeight c (2 * c - x) - continuousSwitchLogHeight c x
  have hbounds (x : ℝ) (hx : x ∈ Set.Icc b c) :
      (0 < x ∧ x < 1) ∧ (0 < 2 * c - x ∧ 2 * c - x < 1) := by
    constructor <;> constructor <;> linarith [hx.1, hx.2]
  have hderiv (x : ℝ) (hx : x ∈ Set.Icc b c) :
      HasDerivAt G ((c - x) / ((2 * c - x) * (1 - (2 * c - x))) -
        (c - x) / (x * (1 - x))) x := by
    obtain ⟨hxb, hAb⟩ := hbounds x hx
    have hd := (((hasStrictDerivAt_continuousSwitchLogHeight c hAb.1 hAb.2).hasDerivAt).comp x
      ((hasDerivAt_const x (2 * c)).sub (hasDerivAt_id x))).sub
      (hasStrictDerivAt_continuousSwitchLogHeight c hxb.1 hxb.2).hasDerivAt
    convert hd using 1 <;> try rfl
    · simp only [zero_sub]
      congr 1
      ring
  have hanti : StrictAntiOn G (Set.Icc b c) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc b c)
    · intro x hx
      exact (hderiv x hx).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hxb := hbounds x ⟨hx.1.le, hx.2.le⟩
      rw [(hderiv x ⟨hx.1.le, hx.2.le⟩).deriv]
      apply sub_neg.mpr
      apply div_lt_div_of_pos_left (sub_pos.mpr hx.2)
        (mul_pos hxb.1.1 (sub_pos.mpr hxb.1.2))
      have hprod := mul_pos (sub_pos.mpr hx.2) (show 0 < 1 - 2 * c by linarith)
      nlinarith
  have hcmp := hanti ⟨le_rfl, hbc.le⟩ ⟨hbc.le, le_rfl⟩ hbc
  have hGc : G c = 0 := by simp [G, show 2 * c - c = c by ring]
  simpa only [hGc, G] using hcmp

theorem IsContinuousSwitch.additive_centering_pos {c γ a b : ℝ}
    (h : IsContinuousSwitch c γ a b) (hc : c < 1 / 2) : 0 < a + b - 2 * c := by
  have hcb := h.center_bounds
  have hc0 := h.1.trans hcb.1
  have hcmp := additive_reflection_height_pos hc0 hc h.1 hcb.1
  have href : 2 * c - b < a := by
    by_contra hn
    have haR : a ≤ 2 * c - b := le_of_not_gt hn
    have hmono := (continuousSwitchLogHeight_strictAntiOn hc0).antitoneOn
      ⟨hcb.2, h.2.2.1⟩ ⟨by linarith [hcb.1], by linarith [h.1]⟩ haR
    rw [h.2.2.2.2] at hmono
    linarith
  linarith

private def oddsReflection (c x : ℝ) : ℝ :=
  c ^ 2 * (1 - x) / (c ^ 2 + (1 - 2 * c) * x)

private theorem oddsReflection_bounds {c x : ℝ} (hc0 : 0 < c) (hc1 : c < 1 / 2)
    (hx0 : 0 < x) (hxc : x ≤ c) :
    0 < oddsReflection c x ∧ oddsReflection c x < 1 := by
  have hx1 : x < 1 := by linarith
  have hD : 0 < c ^ 2 + (1 - 2 * c) * x := by
    exact add_pos_of_pos_of_nonneg (sq_pos_of_pos hc0)
      (mul_nonneg (by linarith) hx0.le)
  refine ⟨div_pos (mul_pos (sq_pos_of_pos hc0) (sub_pos.mpr hx1)) hD, ?_⟩
  apply (div_lt_one hD).mpr
  have hpos := mul_pos (sq_pos_of_pos (show 0 < 1 - c by linarith)) hx0
  nlinarith

private theorem oddsReflection_gt_center {c x : ℝ} (hc0 : 0 < c) (hc1 : c < 1 / 2)
    (hx0 : 0 < x) (hxc : x < c) : c < oddsReflection c x := by
  have hD : 0 < c ^ 2 + (1 - 2 * c) * x := by
    exact add_pos_of_pos_of_nonneg (sq_pos_of_pos hc0)
      (mul_nonneg (by linarith) hx0.le)
  apply (lt_div_iff₀ hD).mpr
  have hpos := mul_pos (mul_pos hc0 (show 0 < 1 - c by linarith)) (sub_pos.mpr hxc)
  nlinarith

private theorem oddsReflection_center {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1 / 2) :
    oddsReflection c c = c := by
  have hD : c ^ 2 + (1 - 2 * c) * c ≠ 0 := by
    have hpos := mul_pos hc0 (show 0 < 1 - c by linarith)
    nlinarith
  unfold oddsReflection
  apply (div_eq_iff hD).mpr
  ring

private theorem odds_reflection_height_neg {c b : ℝ}
    (hc0 : 0 < c) (hc1 : c < 1 / 2) (hb0 : 0 < b) (hbc : b < c) :
    continuousSwitchLogHeight c (oddsReflection c b) - continuousSwitchLogHeight c b < 0 := by
  let G : ℝ → ℝ := fun x ↦ continuousSwitchLogHeight c (oddsReflection c x) - continuousSwitchLogHeight c x
  have hD (x : ℝ) (hx : x ∈ Set.Icc b c) : 0 < c ^ 2 + (1 - 2 * c) * x := by
    exact add_pos_of_pos_of_nonneg (sq_pos_of_pos hc0)
      (mul_nonneg (by linarith) (hb0.le.trans hx.1))
  have hderiv (x : ℝ) (hx : x ∈ Set.Icc b c) :
      HasDerivAt G ((1 - 2 * c) * (x - c) ^ 2 /
        ((c ^ 2 + (1 - 2 * c) * x) * x * (1 - x))) x := by
    have hx0 := hb0.trans_le hx.1
    have hx1 : x < 1 := by linarith [hx.2]
    have hR := oddsReflection_bounds hc0 hc1 hx0 hx.2
    have hnum := ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).const_mul (c ^ 2)
    have hden := (hasDerivAt_const x (c ^ 2)).add ((hasDerivAt_id x).const_mul (1 - 2 * c))
    have hRderiv := hnum.div hden (hD x hx).ne'
    have hd := (((hasStrictDerivAt_continuousSwitchLogHeight c hR.1 hR.2).hasDerivAt).comp x
      hRderiv).sub (hasStrictDerivAt_continuousSwitchLogHeight c hx0 hx1).hasDerivAt
    convert hd using 1 <;> try rfl
    · dsimp only [Pi.sub_apply, Pi.add_apply, id_eq]
      have hc1' : 1 - c ≠ 0 := by linarith
      have hx1' := (sub_pos.mpr hx1).ne'
      have hDn := (hD x hx).ne'
      have hN : c ^ 2 + (1 - 2 * c) * x - c ^ 2 * (1 - x) ≠ 0 := by
        have hp := mul_pos hx0 (sq_pos_of_ne_zero hc1')
        nlinarith
      unfold oddsReflection
      field_simp [hN]
      ring
  have hmono : StrictMonoOn G (Set.Icc b c) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc b c)
    · intro x hx
      exact (hderiv x hx).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hderiv x ⟨hx.1.le, hx.2.le⟩).deriv]
      exact div_pos (mul_pos (by linarith) (sq_pos_of_ne_zero (sub_ne_zero.mpr hx.2.ne)))
        (mul_pos (mul_pos (hD x ⟨hx.1.le, hx.2.le⟩) (hb0.trans hx.1)) (by linarith [hx.2]))
  have hcmp := hmono ⟨le_rfl, hbc.le⟩ ⟨hbc.le, le_rfl⟩ hbc
  have hGc : G c = 0 := by simp only [G, oddsReflection_center hc0 hc1, sub_self]
  simpa only [hGc, G] using hcmp

theorem IsContinuousSwitch.odds_centering_pos {c γ a b : ℝ}
    (h : IsContinuousSwitch c γ a b) (hc : c < 1 / 2) :
    0 < c ^ 2 * (1 - a) * (1 - b) - (1 - c) ^ 2 * a * b := by
  have hcb := h.center_bounds
  have hc0 := h.1.trans hcb.1
  have hcmp := odds_reflection_height_neg hc0 hc h.1 hcb.1
  have hR := oddsReflection_bounds hc0 hc h.1 hcb.1.le
  have haR : a < oddsReflection c b := by
    by_contra hn
    have hRa : oddsReflection c b ≤ a := le_of_not_gt hn
    have hmono := (continuousSwitchLogHeight_strictAntiOn hc0).antitoneOn
      ⟨oddsReflection_gt_center hc0 hc h.1 hcb.1, hR.2⟩ ⟨hcb.2, h.2.2.1⟩ hRa
    rw [h.2.2.2.2] at hmono
    linarith
  have hD : 0 < c ^ 2 + (1 - 2 * c) * b := by
    exact add_pos_of_pos_of_nonneg (sq_pos_of_pos hc0) (mul_nonneg (by linarith) h.1.le)
  have hmul := (lt_div_iff₀ hD).mp haR
  nlinarith

theorem IsContinuousSwitch.sum_eq_one_of_half {γ a b : ℝ}
    (h : IsContinuousSwitch (1 / 2) γ a b) : a + b = 1 := by
  have hγ : 0 < γ := by linarith [h.2.1, h.2.2.2.1]
  have href : IsContinuousSwitch (1 / 2) γ (1 - b) (1 - a) := by
    convert h.reflect using 1
    norm_num
  have heq := continuousSwitch_unique (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1) hγ h href
  linarith [heq.1]

theorem IsContinuousSwitch.additive_centering_nonneg {c γ a b : ℝ}
    (h : IsContinuousSwitch c γ a b) (hc : c ≤ 1 / 2) : 0 ≤ a + b - 2 * c := by
  rcases lt_or_eq_of_le hc with hlt | heq
  · exact (h.additive_centering_pos hlt).le
  · subst c
    linarith [h.sum_eq_one_of_half]

theorem IsContinuousSwitch.odds_centering_nonneg {c γ a b : ℝ}
    (h : IsContinuousSwitch c γ a b) (hc : c ≤ 1 / 2) :
    0 ≤ c ^ 2 * (1 - a) * (1 - b) - (1 - c) ^ 2 * a * b := by
  rcases lt_or_eq_of_le hc with hlt | heq
  · exact (h.odds_centering_pos hlt).le
  · subst c
    have hs := h.sum_eq_one_of_half
    nlinarith

theorem continuousSwitch_odds_centering_identity (c a b : ℝ) :
    c ^ 2 * (1 - a) * (1 - b) - (1 - c) ^ 2 * a * b =
      (1 - 2 * c) * (a - c) * (c - b) - (a + b - 2 * c) * c * (1 - c) := by
  ring

theorem IsContinuousSwitch.geometric_centering_nonneg {c γ a b : ℝ}
    (h : IsContinuousSwitch c γ a b) (hc : c ≤ 1 / 2) :
    0 ≤ (1 - 2 * c) * ((a - c) * (c - b) / (c * (1 - c))) - (a + b - 2 * c) := by
  have hc0 := h.1.trans h.center_bounds.1
  have hv : 0 < c * (1 - c) := mul_pos hc0 (by linarith)
  have heq : c * (1 - c) *
      ((1 - 2 * c) * ((a - c) * (c - b) / (c * (1 - c))) - (a + b - 2 * c)) =
      c ^ 2 * (1 - a) * (1 - b) - (1 - c) ^ 2 * a * b := by
    rw [continuousSwitch_odds_centering_identity]
    have hc1 : 1 - c ≠ 0 := by linarith
    field_simp
  have hm : 0 ≤ c * (1 - c) *
      ((1 - 2 * c) * ((a - c) * (c - b) / (c * (1 - c))) - (a + b - 2 * c)) := by
    rw [heq]
    exact h.odds_centering_nonneg hc
  exact nonneg_of_mul_nonneg_right hm hv

end

end PoissonBinomialComparison

-- SwitchMonotonicity
namespace PoissonBinomialComparison

theorem IsContinuousSwitch.centering_product_nonneg {c γ a b : ℝ}
    (h : IsContinuousSwitch c γ a b) :
    0 ≤ (a + b - 2 * c) *
      ((1 - 2 * c) * ((a - c) * (c - b) / (c * (1 - c))) - (a + b - 2 * c)) := by
  by_cases hc : c ≤ 1 / 2
  · exact mul_nonneg (h.additive_centering_nonneg hc) (h.geometric_centering_nonneg hc)
  · have hc' : 1 - c ≤ 1 / 2 := by linarith
    have hp := mul_nonneg (h.reflect.additive_centering_nonneg hc')
      (h.reflect.geometric_centering_nonneg hc')
    convert hp using 1 <;> try rfl
    ring

theorem deriv_continuousSwitchRatio_count_neg {c γ : ℝ} (hc0 : 0 < c) (hc2 : c < 1 / 2)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    deriv (fun d ↦ continuousSwitchRatio d γ) c < 0 := by
  have hc1 : c < 1 := by linarith
  rw [(hasDerivAt_continuousSwitchRatio_count hc0 hc1 hγ0 hγ1).deriv]
  have hs := continuousSwitchPair_spec hc0 hc1 hγ0 hγ1
  have he := hs.additive_centering_pos hc2
  have hz := hs.geometric_centering_nonneg hc2.le
  have ht := deriv_continuousSwitchLower_count_pos hc0 hc1 hγ0 hγ1
  exact div_neg_of_neg_of_pos (neg_neg_of_pos (add_pos_of_nonneg_of_pos hz (mul_pos he ht)))
    (mul_pos hc0 (sub_pos.mpr hc1))

theorem continuousSwitchRatio_strictAntiOn {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    StrictAntiOn (fun c ↦ continuousSwitchRatio c γ) (Set.Ioc 0 (1 / 2 : ℝ)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioc 0 (1 / 2 : ℝ))
  · intro c hc
    exact (hasDerivAt_continuousSwitchRatio_count hc.1 (by linarith [hc.2]) hγ0 hγ1).continuousAt.continuousWithinAt
  · intro c hc
    rw [interior_Ioc] at hc
    exact deriv_continuousSwitchRatio_count_neg hc.1 hc.2 hγ0 hγ1

theorem switchRatio_strict_order {n i j : ℕ} (hi : 0 < i) (hij : i < j) (hj : j ≤ n / 2)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) : switchRatio n j γ < switchRatio n i γ := by
  have hj0 : 0 < j := by omega
  have hjn : j < n := by omega
  have hin : i < n := by omega
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hjn2 : (2 : ℝ) * j ≤ n := by exact_mod_cast (show 2 * j ≤ n by omega)
  have hci0 : (0 : ℝ) < (i : ℝ) / n := div_pos (by exact_mod_cast hi) hn
  have hcj0 : (0 : ℝ) < (j : ℝ) / n := div_pos (by exact_mod_cast hj0) hn
  have hcj2 : (j : ℝ) / n ≤ 1 / 2 := (div_le_iff₀ hn).2 (by linarith)
  have hcij : (i : ℝ) / n < (j : ℝ) / n :=
    (div_lt_div_iff_of_pos_right hn).2 (by exact_mod_cast hij)
  have h := (continuousSwitchRatio_strictAntiOn hγ0 hγ1) ⟨hci0, le_trans hcij.le hcj2⟩
    ⟨hcj0, hcj2⟩ hcij
  simpa only [continuousSwitchRatio_at_ratio hi hin hγ0 hγ1,
    continuousSwitchRatio_at_ratio hj0 hjn hγ0 hγ1] using h

theorem deriv_switchRatio_le {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    deriv (switchRatio n j) γ ≤ 2 * switchRatio n j γ / γ := by
  rw [deriv_switchRatio_gap hj hjn hγ0 hγ1]
  apply sub_le_self
  have hs := switchPair_spec hj hjn hγ0 hγ1
  have hc := hs.center_bounds hj hjn
  have hcont := (isSwitch_iff_isContinuousSwitch hj hjn γ _ _).mp hs
  have hprod := hcont.centering_product_nonneg
  have hv : 0 < ((j : ℝ) / n) * (1 - (j : ℝ) / n) :=
    mul_pos (lt_trans hs.1 hc.1) (by linarith [hc.2, hs.2.2.1])
  exact div_nonneg hprod (mul_pos (mul_pos hγ0 hv)
    (sub_pos.mpr (switchRatio_bounds hj hjn hγ0 hγ1).2)).le

end PoissonBinomialComparison

-- BenchmarkConcavity
namespace PoissonBinomialComparison

open Set Filter
open scoped Topology

theorem hasDerivAt_deriv_switchValue {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    HasDerivAt (deriv (switchValue n j))
      ((n : ℝ) * (deriv (switchMass n j) γ * (1 - switchRatio n j γ) +
        switchMass n j γ * deriv (switchRatio n j) γ) / (1 - switchRatio n j γ)^2) γ := by
  have hf := (hasDerivAt_switchMass hj hjn hγ0 hγ1).differentiableAt.hasDerivAt
  have hR := (hasDerivAt_switchRatio_gap hj hjn hγ0 hγ1).differentiableAt.hasDerivAt
  have hd := (hf.const_mul (n : ℝ)).div ((hasDerivAt_const γ 1).sub hR)
    (sub_pos.mpr (switchRatio_bounds hj hjn hγ0 hγ1).2).ne'
  have heq : deriv (switchValue n j) =ᶠ[𝓝 γ]
      (fun x => (n : ℝ) * switchMass n j x / (1 - switchRatio n j x)) := by
    filter_upwards [Ioo_mem_nhds hγ0 hγ1] with x hx
    exact deriv_switchValue hj hjn hx.1 hx.2
  convert hd.congr_of_eventuallyEq heq using 1 <;> try rfl
  simp only [Pi.sub_apply]
  ring

theorem deriv2_switchValue_neg {n j : ℕ} (hn : 3 ≤ n) (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    deriv (deriv (switchValue n j)) γ < 0 := by
  rw [(hasDerivAt_deriv_switchValue hj hjn hγ0 hγ1).deriv]
  have hf := switchMass_pos hj hjn hγ0 hγ1
  obtain ⟨hR0,hR1⟩ := switchRatio_bounds hj hjn hγ0 hγ1
  have hRp := deriv_switchRatio_le hj hjn hγ0 hγ1
  have hnR : (2 : ℝ) < n := by exact_mod_cast (show 2 < n by omega)
  have hf' : deriv (switchMass n j) γ * (1 - switchRatio n j γ) =
      -(n : ℝ) * switchRatio n j γ / γ * switchMass n j γ := by
    rw [(hasDerivAt_switchMass hj hjn hγ0 hγ1).deriv]
    field_simp [(sub_pos.mpr hR1).ne']
  rw [hf']
  apply div_neg_of_neg_of_pos
  · apply mul_neg_of_pos_of_neg (by positivity)
    have hmul := mul_le_mul_of_nonneg_left hRp hf.le
    have hstrict : 0 < ((n : ℝ) - 2) * (switchRatio n j γ / γ) * switchMass n j γ :=
      mul_pos (mul_pos (sub_pos.mpr hnR) (div_pos hR0 hγ0)) hf
    simp only [div_eq_mul_inv] at *
    nlinarith
  · positivity

theorem strictConcaveOn_switchValue {n j : ℕ} (hn : 3 ≤ n) (hj : 0 < j) (hjn : j < n) :
    StrictConcaveOn ℝ (Icc 0 1) (switchValue n j) := by
  apply strictConcaveOn_of_deriv2_neg (convex_Icc 0 1) (continuousOn_switchValue hj hjn)
  intro x hx
  rw [interior_Icc] at hx
  exact deriv2_switchValue_neg hn hj hjn hx.1 hx.2

theorem continuousAt_switchRatio_zero {n j : ℕ} (hj : 0 < j) (hjn : j < n) :
    ContinuousAt (switchRatio n j) 0 := by
  unfold switchRatio
  exact (((continuousAt_switchUpper_zero hj hjn).sub continuousAt_const).mul
    (continuousAt_const.sub (continuousAt_switchLower_zero hj hjn))).div_const _

@[simp] theorem switchRatio_zero (n j : ℕ) : switchRatio n j 0 = 0 := by
  simp [switchRatio]

theorem tendsto_deriv_switchValue_zero {n j : ℕ} (hj : 0 < j) (hjn : j < n) :
    Tendsto (deriv (switchValue n j)) (𝓝[>] 0)
      (𝓝 ((n : ℝ) * switchMass n j 0)) := by
  have hc := ((continuousAt_switchMass_zero hj hjn).const_mul (n : ℝ)).div
    ((continuousAt_const : ContinuousAt (fun _ : ℝ => (1 : ℝ)) 0).sub
      (continuousAt_switchRatio_zero hj hjn)) (by simp)
  have ht := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  simp only [Pi.div_apply, Pi.sub_apply, switchRatio_zero, sub_zero, div_one] at ht
  apply ht.congr'
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with x hx
  exact (deriv_switchValue hj hjn hx.1 hx.2).symm

theorem hasDerivWithinAt_switchValue_zero {n j : ℕ} (hj : 0 < j) (hjn : j < n) :
    HasDerivWithinAt (switchValue n j) ((n : ℝ) * switchMass n j 0) (Ici 0) 0 := by
  apply hasDerivWithinAt_Ici_of_tendsto_deriv (s := Ioo 0 1)
  · intro x hx
    exact (hasDerivAt_switchValue hj hjn hx.1 hx.2).differentiableAt.differentiableWithinAt
  · exact (continuousAt_switchValue_zero hj hjn).continuousWithinAt
  · exact Ioo_mem_nhdsGT (by norm_num)
  · exact tendsto_deriv_switchValue_zero hj hjn

theorem strictMonoOn_switchValue {n j : ℕ} (hj : 0 < j) (hjn : j < n) :
    StrictMonoOn (switchValue n j) (Icc 0 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 1) (continuousOn_switchValue hj hjn)
  intro x hx
  rw [interior_Icc] at hx
  rw [deriv_switchValue hj hjn hx.1 hx.2]
  exact div_pos (mul_pos (by exact_mod_cast (lt_trans hj hjn))
    (switchMass_pos hj hjn hx.1 hx.2))
    (sub_pos.mpr (switchRatio_bounds hj hjn hx.1 hx.2).2)

theorem switchValue_strict_bounds {n j : ℕ} (hn : 3 ≤ n) (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    0 < switchValue n j γ ∧
      switchValue n j γ < min ((n : ℝ) * switchMass n j 0 * γ) 1 := by
  have hm := strictMonoOn_switchValue hj hjn
  have h0 := hm (show (0 : ℝ) ∈ Icc 0 1 by norm_num) ⟨hγ0.le,hγ1.le⟩ hγ0
  have h1 := hm ⟨hγ0.le,hγ1.le⟩ (show (1 : ℝ) ∈ Icc 0 1 by norm_num) hγ1
  simp only [switchValue_zero] at h0
  rw [switchValue_one hj hjn.le] at h1
  refine ⟨h0, lt_min ?_ h1⟩
  have hs := (strictConcaveOn_switchValue hn hj hjn).slope_lt_of_hasDerivWithinAt
    (show (0 : ℝ) ∈ Icc 0 1 by norm_num) ⟨hγ0.le,hγ1.le⟩ hγ0
    ((hasDerivWithinAt_switchValue_zero hj hjn).mono Icc_subset_Ici_self)
  simp only [slope_def_field, switchValue_zero, sub_zero] at hs
  exact (div_lt_iff₀ hγ0).mp hs

theorem benchmark_eq_switchValue_of_mem {n : ℕ} (hn : 2 ≤ n) {Δ : ℝ}
    (hΔ : Δ ∈ Icc (0 : ℝ) n) :
    benchmark n Δ = switchValue n (n / 2) (Δ / n) := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  by_cases h0 : Δ = 0
  · simp [h0]
  by_cases h1 : Δ = n
  · simp [h1, hn0, benchmark_at_dimension (by omega : 0 < n),
      switchValue_one (by omega : 0 < n / 2) (Nat.div_le_self n 2)]
  exact benchmark_eq_switchValue (lt_of_le_of_ne hΔ.1 (Ne.symm h0))
    (lt_of_le_of_ne hΔ.2 h1)

theorem switchMass_central_zero (n : ℕ) : switchMass n (n / 2) 0 = kappa n := by
  rw [switchMass_zero]
  rfl

theorem continuousOn_benchmark {n : ℕ} (hn : 2 ≤ n) :
    ContinuousOn (benchmark n) (Icc (0 : ℝ) n) := by
  have hn0 : (0 : ℝ) < n := by positivity
  have hc := (continuousOn_switchValue (by omega : 0 < n / 2)
    (by omega : n / 2 < n)).comp (continuous_id.div_const (n : ℝ)).continuousOn
    (show MapsTo (fun x : ℝ => x / n) (Icc 0 n) (Icc 0 1) from
      fun x hx => ⟨div_nonneg hx.1 hn0.le, (div_le_one hn0).mpr hx.2⟩)
  exact hc.congr (fun x hx => benchmark_eq_switchValue_of_mem hn hx)

theorem strictConcaveOn_benchmark {n : ℕ} (hn : 3 ≤ n) :
    StrictConcaveOn ℝ (Icc (0 : ℝ) n) (benchmark n) := by
  have hn0 : (0 : ℝ) < n := by positivity
  have hs := strictConcaveOn_switchValue hn (by omega : 0 < n / 2) (by omega : n / 2 < n)
  refine ⟨convex_Icc (0 : ℝ) n, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have hx' : x / n ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hx.1 hn0.le, (div_le_one hn0).mpr hx.2⟩
  have hy' : y / n ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hy.1 hn0.le, (div_le_one hn0).mpr hy.2⟩
  have hxy' : x / (n : ℝ) ≠ y / n := fun he => hxy ((div_left_inj' hn0.ne').mp he)
  have h := hs.2 hx' hy' hxy' ha hb hab
  rw [benchmark_eq_switchValue_of_mem (by omega) hx,
    benchmark_eq_switchValue_of_mem (by omega) hy,
    benchmark_eq_switchValue_of_mem (by omega)
      ((convex_Icc (0 : ℝ) n) hx hy ha.le hb.le hab)]
  simpa only [smul_eq_mul, add_div, mul_div_assoc] using h

theorem hasDerivWithinAt_benchmark_zero {n : ℕ} (hn : 2 ≤ n) :
    HasDerivWithinAt (benchmark n) (kappa n) (Icc (0 : ℝ) n) 0 := by
  have hn0 : (0 : ℝ) < n := by positivity
  have hd := (hasDerivWithinAt_switchValue_zero (by omega : 0 < n / 2)
    (by omega : n / 2 < n)).comp_of_eq 0
    ((hasDerivAt_id (0 : ℝ)).div_const (n : ℝ)).hasDerivWithinAt
    (show MapsTo (fun x : ℝ => x / n) (Icc 0 n) (Ici 0) from
      fun x hx => div_nonneg hx.1 hn0.le) (by simp)
  have he : ((n : ℝ) * switchMass n (n / 2) 0) * (1 / n) = kappa n := by
    rw [switchMass_central_zero]
    field_simp
  rw [he] at hd
  exact hd.congr (fun x hx => benchmark_eq_switchValue_of_mem hn hx) (by simp)

theorem hasDerivWithinAt_benchmark_zero_right {n : ℕ} (hn : 2 ≤ n) :
    HasDerivWithinAt (benchmark n) (kappa n) (Ici 0) 0 := by
  apply (hasDerivWithinAt_benchmark_zero hn).mono_of_mem_nhdsWithin
  exact Icc_mem_nhdsGE (by positivity)

theorem benchmark_strict_bounds {n : ℕ} (hn : 3 ≤ n) {Δ : ℝ}
    (hΔ0 : 0 < Δ) (hΔn : Δ < n) :
    0 < benchmark n Δ ∧ benchmark n Δ < min (kappa n * Δ) 1 := by
  have hn0 : (0 : ℝ) < n := by positivity
  rw [benchmark_eq_switchValue hΔ0 hΔn]
  have h := switchValue_strict_bounds hn (by omega : 0 < n / 2)
    (by omega : n / 2 < n) (div_pos hΔ0 hn0) ((div_lt_one hn0).mpr hΔn)
  rw [switchMass_central_zero] at h
  have he : (n : ℝ) * kappa n * (Δ / n) = kappa n * Δ := by field_simp
  rwa [he] at h

end PoissonBinomialComparison

-- SwitchRhoDensity
namespace PoissonBinomialComparison

noncomputable section

def switchRhoDensity (n j : ℕ) (a b t : ℝ) : ℝ :=
  switchRho n j a b * pbMass (fun _ : Fin (n - 1) ↦ t) (j - 1) +
    (1 - switchRho n j a b) * pbMass (fun _ : Fin (n - 1) ↦ t) j

theorem switchRhoDensity_eq_pbMass_cons (n j : ℕ) (hj : 0 < j) (a b t : ℝ) :
    switchRhoDensity n j a b t =
      pbMass (Fin.cons (switchRho n j a b) (fun _ : Fin (n - 1) ↦ t)) j := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
  have h := pbMassInt_cons (fun _ : Fin (n - 1) ↦ t) (switchRho n (k + 1) a b)
    ((k + 1 : ℕ) : ℤ)
  have hk : ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) := by omega
  simp only [hk, pbMassIntOn_natCast] at h
  simp only [switchRhoDensity, Nat.succ_eq_add_one, Nat.add_sub_cancel, pbMass]
  rw [h]
  ring

theorem pbMass_const_deleted_lower {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {t : ℝ} (ht : t ≠ 0) :
    pbMass (fun _ : Fin (n - 1) ↦ t) (j - 1) =
      (j : ℝ) * pbMass (fun _ : Fin n ↦ t) j / ((n : ℝ) * t) := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hcoeff : (n : ℝ) * ((n - 1).choose (j - 1) : ℝ) = (n.choose j : ℝ) * j := by
    have hh := Nat.add_one_mul_choose_eq (n - 1) (j - 1)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ n), Nat.sub_add_cancel (by omega : 1 ≤ j)] at hh
    exact_mod_cast hh
  have hexp : n - 1 - (j - 1) = n - j := by omega
  have hpow : t ^ j = t ^ (j - 1) * t := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ j)]
  apply (eq_div_iff (mul_ne_zero hn ht)).mpr
  simp only [pbMass_const, hexp, hpow]
  linear_combination (t ^ (j - 1) * (1 - t) ^ (n - j) * t) * hcoeff

theorem pbMass_const_deleted_upper {n j : ℕ} (hjn : j < n)
    {t : ℝ} (ht : 1 - t ≠ 0) :
    pbMass (fun _ : Fin (n - 1) ↦ t) j =
      ((n - j : ℕ) : ℝ) * pbMass (fun _ : Fin n ↦ t) j / ((n : ℝ) * (1 - t)) := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hcoeff : ((n - 1).choose j : ℝ) * n = (n.choose j : ℝ) * (n - j : ℕ) := by
    have hh := Nat.choose_mul_succ_eq (n - 1) j
    rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at hh
    exact_mod_cast hh
  have hexp : n - 1 - j + 1 = n - j := by omega
  have hpow : (1 - t) ^ (n - j) = (1 - t) ^ (n - 1 - j) * (1 - t) := by
    rw [← pow_succ, hexp]
  apply (eq_div_iff (mul_ne_zero hn ht)).mpr
  simp only [pbMass_const, hpow]
  linear_combination (t ^ j * (1 - t) ^ (n - 1 - j) * (1 - t)) * hcoeff

private theorem rho_density_algebra (c a b f : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) (ha1 : 1 - a ≠ 0) (hb1 : 1 - b ≠ 0)
    (hc : c * (1 - c) ≠ 0)
    (hD : c * (1 - a) * (1 - b) + (1 - c) * a * b ≠ 0) :
    let r := (1 - c) * a * b / (c * (1 - a) * (1 - b) + (1 - c) * a * b)
    let R := (a - c) * (c - b) / (c * (1 - c))
    (r * (c * f / a) + (1 - r) * ((1 - c) * f / (1 - a)) = f / (1 - R)) ∧
      (r * (c * f / b) + (1 - r) * ((1 - c) * f / (1 - b)) = f / (1 - R)) := by
  dsimp
  have hR : 1 - (a - c) * (c - b) / (c * (1 - c)) =
      (c * (1 - a) * (1 - b) + (1 - c) * a * b) / (c * (1 - c)) := by
    apply (eq_div_iff hc).mpr
    rw [sub_mul, one_mul, div_mul_cancel₀ _ hc]
    exact switch_denominator_identity c a b
  rw [hR]
  constructor <;> field_simp <;> ring

theorem switchRho_eq_normalized {n j : ℕ} (hjn : j ≤ n) (hn : 0 < n) (a b : ℝ) :
    switchRho n j a b =
      (1 - (j : ℝ) / n) * a * b /
        (((j : ℝ) / n) * (1 - a) * (1 - b) + (1 - (j : ℝ) / n) * a * b) := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  unfold switchRho
  rw [Nat.cast_sub hjn]
  field_simp
  ring

theorem IsSwitch.rhoDensity_eq {n j : ℕ} {γ a b : ℝ} (h : IsSwitch n j γ a b)
    (hj : 0 < j) (hjn : j < n) :
    let c := (j : ℝ) / n
    let R := (a - c) * (c - b) / (c * (1 - c))
    let f := pbMass (fun _ : Fin n ↦ a) j
    switchRhoDensity n j a b a = f / (1 - R) ∧
      switchRhoDensity n j a b b = f / (1 - R) := by
  dsimp
  have ha : 0 < a := h.1.trans h.2.1
  have ha1 : 0 < 1 - a := sub_pos.mpr h.2.2.1
  have hb1 : 0 < 1 - b := sub_pos.mpr (h.2.1.trans h.2.2.1)
  have hc := h.center_bounds hj hjn
  have hcv : ((j : ℝ) / n) * (1 - (j : ℝ) / n) ≠ 0 :=
    (mul_pos (h.1.trans hc.1) (by linarith [hc.2, h.2.2.1])).ne'
  have hh := rho_density_algebra ((j : ℝ) / n) a b (pbMass (fun _ : Fin n ↦ a) j)
    ha.ne' h.1.ne' ha1.ne' hb1.ne' hcv (h.denominator_pos hj hjn).ne'
  dsimp at hh
  unfold switchRhoDensity
  rw [pbMass_const_deleted_lower hj hjn ha.ne', pbMass_const_deleted_upper hjn ha1.ne',
    pbMass_const_deleted_lower hj hjn h.1.ne', pbMass_const_deleted_upper hjn hb1.ne',
    ← h.pbMass_eq, switchRho_eq_normalized hjn.le (by omega), Nat.cast_sub hjn.le]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hleft (x f : ℝ) : (j : ℝ) * f / ((n : ℝ) * x) = ((j : ℝ) / n) * f / x := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hright (x f : ℝ) : ((n : ℝ) - j) * f / ((n : ℝ) * (1 - x)) =
      (1 - (j : ℝ) / n) * f / (1 - x) := by
    have hc' : ((n : ℝ) - j) / n = 1 - (j : ℝ) / n := by field_simp
    calc
      _ = (((n : ℝ) - j) / n) * f / (1 - x) := by
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      _ = _ := by rw [hc']
  simp only [hleft, hright]
  exact hh

theorem switchRhoDensity_eq_switchMass {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    switchRhoDensity n j (switchUpper n j γ) (switchLower n j γ) (switchUpper n j γ) =
        switchMass n j γ / (1 - switchRatio n j γ) ∧
      switchRhoDensity n j (switchUpper n j γ) (switchLower n j γ) (switchLower n j γ) =
        switchMass n j γ / (1 - switchRatio n j γ) :=
  (switchPair_spec hj hjn hγ0 hγ1).rhoDensity_eq hj hjn

theorem switchRhoDensity_improvement_neg {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    switchMass n j γ -
      (switchRhoDensity n j (switchUpper n j γ) (switchLower n j γ) (switchUpper n j γ) +
        switchRhoDensity n j (switchUpper n j γ) (switchLower n j γ) (switchLower n j γ)) / 2 < 0 := by
  obtain ⟨ha, hb⟩ := switchRhoDensity_eq_switchMass hj hjn hγ0 hγ1
  rw [ha, hb]
  have hf := switchMass_pos hj hjn hγ0 hγ1
  have hR := switchRatio_bounds hj hjn hγ0 hγ1
  have hlt : switchMass n j γ < switchMass n j γ / (1 - switchRatio n j γ) := by
    apply (lt_div_iff₀ (sub_pos.mpr hR.2)).mpr
    nlinarith
  linarith

end

end PoissonBinomialComparison

-- CommonCoordinate
namespace PoissonBinomialComparison

open Finset

noncomputable section

variable {n : ℕ} {p q : Fin n → ℝ}

theorem admissiblePair_cons (h : AdmissiblePair p q) {a b : ℝ}
    (hb : 0 ≤ b) (hba : b ≤ a) (ha : a ≤ 1) :
    AdmissiblePair (Fin.cons a p) (Fin.cons b q) := by
  rw [admissiblePair_iff]
  exact Fin.cases ⟨hb, hba, ha⟩ (fun i ↦ (admissiblePair_iff p q).mp h i)

theorem tailDiff_le_tailObjective_all (h : AdmissiblePair p q) (k : ℕ) :
    tailDiff p q k ≤ tailObjective p q := by
  by_cases hk : k ∈ Icc 1 n
  · exact tailDiff_le_tailObjective p q hk
  by_cases hk0 : k = 0
  · simpa [hk0, tailDiff] using tailObjective_nonneg h
  · have hkn : n < k := by simp only [mem_Icc] at hk; omega
    simpa [tailDiff, pbTail_eq_zero_of_lt p hkn, pbTail_eq_zero_of_lt q hkn] using
      tailObjective_nonneg h

theorem tailObjective_cons_common_le (h : AdmissiblePair p q) {t : ℝ}
    (ht : 0 ≤ t ∧ t ≤ 1) :
    tailObjective (Fin.cons t p) (Fin.cons t q) ≤ tailObjective p q := by
  rw [tailObjective_le_iff _ _ (Nat.succ_pos n)]
  intro k hk
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := (mem_Icc.mp hk).1; omega : k ≠ 0)
  rw [tailDiff_cons_common]
  have h0 := mul_nonneg (sub_nonneg.mpr ht.2)
    (sub_nonneg.mpr (tailDiff_le_tailObjective_all h (j + 1)))
  have h1 := mul_nonneg ht.1 (sub_nonneg.mpr (tailDiff_le_tailObjective_all h j))
  nlinarith

theorem tailObjective_cons_zero (h : AdmissiblePair p q) :
    tailObjective (Fin.cons 0 p) (Fin.cons 0 q) = tailObjective p q := by
  apply le_antisymm (tailObjective_cons_common_le h ⟨le_rfl, zero_le_one⟩)
  by_cases hn : 0 < n
  · obtain ⟨k, hk, heq⟩ := tailObjective_attained p q hn
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := (mem_Icc.mp hk).1; omega : k ≠ 0)
    have hk' : j + 1 ∈ Icc 1 (n + 1) := by simp only [mem_Icc] at hk ⊢; omega
    have hb := tailDiff_le_tailObjective (Fin.cons 0 p) (Fin.cons 0 q) hk'
    simpa [tailDiff_cons_common, heq] using hb
  · have hn0 : n = 0 := by omega
    subst n
    simpa using tailObjective_nonneg (admissiblePair_cons h le_rfl le_rfl zero_le_one)

theorem tailObjective_cons_one (h : AdmissiblePair p q) :
    tailObjective (Fin.cons 1 p) (Fin.cons 1 q) = tailObjective p q := by
  apply le_antisymm (tailObjective_cons_common_le h ⟨zero_le_one, le_rfl⟩)
  by_cases hn : 0 < n
  · obtain ⟨k, hk, heq⟩ := tailObjective_attained p q hn
    have hk' : k + 1 ∈ Icc 1 (n + 1) := by simp only [mem_Icc] at hk ⊢; omega
    have hb := tailDiff_le_tailObjective (Fin.cons 1 p) (Fin.cons 1 q) hk'
    simpa [tailDiff_cons_common, heq] using hb
  · have hn0 : n = 0 := by omega
    subst n
    simpa using tailObjective_nonneg (admissiblePair_cons h zero_le_one le_rfl le_rfl)

end

end PoissonBinomialComparison

-- DimensionImprovement
namespace PoissonBinomialComparison

open scoped BigOperators Topology
open Finset Filter

noncomputable section

variable {n : ℕ} {p q : Fin n → ℝ}

private theorem threshold_mem_of_tailDiff_pos (p q : Fin n → ℝ) (k : ℕ)
    (hk : 0 < tailDiff p q k) : k ∈ Icc 1 n := by
  by_cases hk0 : k = 0
  · simp [hk0, tailDiff] at hk
  have hkn : k ≤ n := by
    by_contra hnot
    have hnk : n < k := by omega
    simp [tailDiff, pbTail_eq_zero_of_lt p hnk, pbTail_eq_zero_of_lt q hnk] at hk
  exact mem_Icc.mpr ⟨by omega, hkn⟩

theorem activeThresholds_cons_common (h : AdmissiblePair p q) {j : ℕ}
    (hactive : activeThresholds p q = {j, j + 1})
    (hT : 0 < tailObjective p q) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    tailObjective (Fin.cons ρ p) (Fin.cons ρ q) = tailObjective p q ∧
      activeThresholds (Fin.cons ρ p) (Fin.cons ρ q) = {j + 1} := by
  have hjmem : j ∈ activeThresholds p q := by rw [hactive]; simp
  have hjmem' : j + 1 ∈ activeThresholds p q := by rw [hactive]; simp
  have hj := (mem_activeThresholds p q j).mp hjmem
  have hj' := (mem_activeThresholds p q (j + 1)).mp hjmem'
  have heq : tailDiff (Fin.cons ρ p) (Fin.cons ρ q) (j + 1) = tailObjective p q := by
    rw [tailDiff_cons_common, hj.2.2, hj'.2.2]
    ring
  have hmax : tailObjective (Fin.cons ρ p) (Fin.cons ρ q) = tailObjective p q := by
    apply le_antisymm (tailObjective_cons_common_le h ⟨hρ0.le, hρ1.le⟩)
    rw [← heq]
    exact tailDiff_le_tailObjective _ _ (mem_Icc.mpr ⟨by omega, by omega⟩)
  refine ⟨hmax, eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩⟩
  · exact (mem_activeThresholds _ _ (j + 1)).mpr ⟨by omega, by omega, heq.trans hmax.symm⟩
  · intro k hk
    have hk' := (mem_activeThresholds _ _ k).mp hk
    obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    have hnew := hk'.2.2
    rw [tailDiff_cons_common, hmax] at hnew
    have hl := tailDiff_le_tailObjective_all h l
    have hl' := tailDiff_le_tailObjective_all h (l + 1)
    have hleq : tailDiff p q l = tailObjective p q := by
      have hnonneg := mul_nonneg (sub_nonneg.mpr hρ1.le) (sub_nonneg.mpr hl')
      have he : ρ * (tailObjective p q - tailDiff p q l) ≤ 0 := by nlinarith
      have hzero : ρ * (tailObjective p q - tailDiff p q l) = 0 :=
        le_antisymm he (mul_nonneg hρ0.le (sub_nonneg.mpr hl))
      exact (sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left hρ0.ne')).symm
    have hleq' : tailDiff p q (l + 1) = tailObjective p q := by
      rw [hleq] at hnew
      have he : (1 - ρ) * (tailObjective p q - tailDiff p q (l + 1)) = 0 := by nlinarith
      exact (sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left (sub_pos.mpr hρ1).ne')).symm
    have hlmem : l ∈ activeThresholds p q := mem_filter.mpr
      ⟨threshold_mem_of_tailDiff_pos p q l (by rwa [hleq]), hleq⟩
    have hlmem' : l + 1 ∈ activeThresholds p q := mem_filter.mpr
      ⟨threshold_mem_of_tailDiff_pos p q (l + 1) (by rwa [hleq']), hleq'⟩
    rw [hactive] at hlmem hlmem'
    simp only [mem_insert, mem_singleton] at hlmem hlmem'
    omega

theorem tailObjective_curve_eventually_eq_of_unique {m k : ℕ}
    (P Q : ℝ → Fin m → ℝ) (hP : Continuous P) (hQ : Continuous Q) (t : ℝ)
    (hunique : activeThresholds (P t) (Q t) = {k}) :
    (fun u ↦ tailObjective (P u) (Q u)) =ᶠ[𝓝 t] (fun u ↦ tailDiff (P u) (Q u) k) := by
  have hk : k ∈ activeThresholds (P t) (Q t) := by rw [hunique]; simp
  have hk' := (mem_activeThresholds _ _ k).mp hk
  have hm : 0 < m := by omega
  have hc (l : ℕ) : Continuous (fun u ↦ tailDiff (P u) (Q u) l) :=
    (continuous_tailDiff l).comp (hP.prodMk hQ)
  have hevent : ∀ᶠ u in 𝓝 t, ∀ l ∈ Icc 1 m, tailDiff (P u) (Q u) l ≤ tailDiff (P u) (Q u) k := by
    rw [eventually_all_finset]
    intro l hl
    by_cases hlk : l = k
    · subst l
      exact Eventually.of_forall (fun _ ↦ le_rfl)
    have hlt : tailDiff (P t) (Q t) l < tailDiff (P t) (Q t) k := by
      have hle := tailDiff_le_tailObjective (P t) (Q t) hl
      rw [← hk'.2.2] at hle
      apply lt_of_le_of_ne hle
      intro heq
      have hlmem : l ∈ activeThresholds (P t) (Q t) := mem_filter.mpr ⟨hl, heq.trans hk'.2.2⟩
      rw [hunique, mem_singleton] at hlmem
      exact hlk hlmem
    exact ((hc l).continuousAt.eventually_lt (hc k).continuousAt hlt).mono (fun _ ht ↦ ht.le)
  filter_upwards [hevent] with u hu
  apply le_antisymm
  · exact (tailObjective_le_iff _ _ hm _).mpr hu
  · exact tailDiff_le_tailObjective _ _ (mem_Icc.mpr ⟨hk'.1, hk'.2.1⟩)

private theorem eventually_descends {f : ℝ → ℝ} {d : ℝ}
    (hd : HasDerivAt f d 0) (hneg : d < 0) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), f ε < f 0 := by
  have hs := hd.tendsto_slope_zero_right.eventually (eventually_lt_nhds hneg)
  have hp : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  filter_upwards [hs, hp] with ε hs hε
  simp only [zero_add, smul_eq_mul] at hs
  have hdiff : f ε - f 0 < 0 :=
    (mul_lt_mul_iff_right₀ (inv_pos.mpr hε)).mp (by simpa using hs)
  exact sub_neg.mp hdiff

def dimensionUpperPath (n : ℕ) (a ρ ε : ℝ) : Fin (n + 1) → ℝ :=
  Fin.cons (ρ + ε / 2) (fun _ ↦ a - ε / (2 * n))

def dimensionLowerPath (n : ℕ) (b ρ ε : ℝ) : Fin (n + 1) → ℝ :=
  Fin.cons (ρ - ε / 2) (fun _ ↦ b + ε / (2 * n))

theorem continuous_dimensionUpperPath (n : ℕ) (a ρ : ℝ) :
    Continuous (dimensionUpperPath n a ρ) := by
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun _ ↦ ?_) i <;> simp [dimensionUpperPath] <;> fun_prop

theorem continuous_dimensionLowerPath (n : ℕ) (b ρ : ℝ) :
    Continuous (dimensionLowerPath n b ρ) := by
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun _ ↦ ?_) i <;> simp [dimensionLowerPath] <;> fun_prop

theorem meanGap_dimensionPath (n : ℕ) (hn : 0 < n) (a b ρ ε : ℝ) :
    meanGap (dimensionUpperPath n a ρ ε) (dimensionLowerPath n b ρ ε) = n * (a - b) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [dimensionUpperPath, dimensionLowerPath, meanGap, Fin.sum_univ_succ,
    Fin.cons_zero, Fin.cons_succ, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

theorem hasDerivAt_pbTail_cons_const_curve {n j : ℕ} (hj : 0 < j)
    {A R : ℝ → ℝ} {a ρ da dr : ℝ}
    (hA : HasDerivAt A da 0) (hR : HasDerivAt R dr 0)
    (ha : A 0 = a) (hr : R 0 = ρ) :
    HasDerivAt (fun ε ↦ pbTail (Fin.cons (R ε) (fun _ : Fin n ↦ A ε)) (j + 1))
      (dr * pbMass (fun _ : Fin n ↦ a) j + da * n *
        ((1 - ρ) * pbMass (fun _ : Fin (n - 1) ↦ a) j +
          ρ * pbMass (fun _ : Fin (n - 1) ↦ a) (j - 1))) 0 := by
  have hnext := (hasDerivAt_pbTail_const_succ n j (A 0)).comp 0 hA
  have hprev := (hasDerivAt_pbTail_const n j hj (A 0)).comp 0 hA
  have hd := (((hasDerivAt_const 0 (1 : ℝ)).sub hR).mul hnext).add (hR.mul hprev)
  convert! hd using 1
  · funext ε
    exact pbTail_cons (fun _ : Fin n ↦ A ε) (R ε) j
  · simp only [Pi.sub_apply, Function.comp_apply, ha, hr, zero_sub]
    rw [← pbTail_sub_succ (fun _ : Fin n ↦ a) j]
    ring

theorem IsSwitch.hasDerivAt_dimensionPath {n j : ℕ} {γ a b : ℝ}
    (h : IsSwitch n j γ a b) (hj : 0 < j) (hjn : j < n) :
    HasDerivAt
      (fun ε ↦ tailDiff (dimensionUpperPath n a (switchRho n j a b) ε)
        (dimensionLowerPath n b (switchRho n j a b) ε) (j + 1))
      (pbMass (fun _ : Fin n ↦ a) j -
        (switchRhoDensity n j a b a + switchRhoDensity n j a b b) / 2) 0 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hA : HasDerivAt (fun ε : ℝ ↦ a - ε / (2 * n)) (-1 / (2 * n)) 0 := by
    convert! (hasDerivAt_const 0 a).sub ((hasDerivAt_id 0).div_const (2 * (n : ℝ))) using 1; first | rfl | ring
  have hB : HasDerivAt (fun ε : ℝ ↦ b + ε / (2 * n)) (1 / (2 * n)) 0 := by
    convert! (hasDerivAt_const 0 b).add ((hasDerivAt_id 0).div_const (2 * (n : ℝ))) using 1; first | rfl | ring
  have hRp : HasDerivAt (fun ε : ℝ ↦ switchRho n j a b + ε / 2) (1 / 2) 0 := by
    convert! (hasDerivAt_const 0 (switchRho n j a b)).add ((hasDerivAt_id 0).div_const 2) using 1; first | rfl | ring
  have hRq : HasDerivAt (fun ε : ℝ ↦ switchRho n j a b - ε / 2) (-1 / 2) 0 := by
    convert! (hasDerivAt_const 0 (switchRho n j a b)).sub ((hasDerivAt_id 0).div_const 2) using 1; first | rfl | ring
  have hp := hasDerivAt_pbTail_cons_const_curve (n := n) (a := a) (ρ := switchRho n j a b) hj hA hRp (by simp) (by simp)
  have hq := hasDerivAt_pbTail_cons_const_curve (n := n) (a := b) (ρ := switchRho n j a b) hj hB hRq (by simp) (by simp)
  convert! hp.sub hq using 1
  · simp only [switchRhoDensity]
    rw [← h.pbMass_eq]
    field_simp
    ring

theorem dimensionPath_eventually_admissible {n : ℕ} {a b ρ : ℝ}
    (hb0 : 0 < b) (hba : b < a) (ha1 : a < 1) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      AdmissiblePair (dimensionUpperPath n a ρ ε) (dimensionLowerPath n b ρ ε) := by
  have hR0 : ∀ᶠ ε : ℝ in 𝓝 0, 0 < ρ - ε / 2 :=
    ContinuousAt.eventually_lt (by fun_prop) (by fun_prop) (by simpa using hρ0)
  have hR1 : ∀ᶠ ε : ℝ in 𝓝 0, ρ + ε / 2 < 1 :=
    ContinuousAt.eventually_lt (by fun_prop) (by fun_prop) (by simpa using hρ1)
  have hB0 : ∀ᶠ ε : ℝ in 𝓝 0, 0 < b + ε / (2 * n) :=
    ContinuousAt.eventually_lt (by fun_prop) (by fun_prop) (by simpa using hb0)
  have hBA : ∀ᶠ ε : ℝ in 𝓝 0, b + ε / (2 * n) < a - ε / (2 * n) :=
    ContinuousAt.eventually_lt (by fun_prop) (by fun_prop) (by simpa using hba)
  have hA1 : ∀ᶠ ε : ℝ in 𝓝 0, a - ε / (2 * n) < 1 :=
    ContinuousAt.eventually_lt (by fun_prop) (by fun_prop) (by simpa using ha1)
  have hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  filter_upwards [hR0.filter_mono nhdsWithin_le_nhds, hR1.filter_mono nhdsWithin_le_nhds,
    hB0.filter_mono nhdsWithin_le_nhds, hBA.filter_mono nhdsWithin_le_nhds,
    hA1.filter_mono nhdsWithin_le_nhds, hpos] with ε hR0 hR1 hB0 hBA hA1 hε
  exact admissiblePair_cons ((admissiblePair_iff _ _).mpr (fun _ ↦ ⟨hB0.le, hBA.le, hA1.le⟩))
    hR0.le (by linarith) hR1.le

theorem switch_dimension_improvement {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    ∃ ε : ℝ, 0 < ε ∧
      let a := switchUpper n j γ
      let b := switchLower n j γ
      let ρ := switchRho n j a b
      AdmissiblePair (dimensionUpperPath n a ρ ε) (dimensionLowerPath n b ρ ε) ∧
        meanGap (dimensionUpperPath n a ρ ε) (dimensionLowerPath n b ρ ε) = n * γ ∧
        tailObjective (dimensionUpperPath n a ρ ε) (dimensionLowerPath n b ρ ε) <
          switchValue n j γ := by
  let a := switchUpper n j γ
  let b := switchLower n j γ
  let ρ := switchRho n j a b
  let P := dimensionUpperPath n a ρ
  let Q := dimensionLowerPath n b ρ
  have hs : IsSwitch n j γ a b := switchPair_spec hj hjn hγ0 hγ1
  have hρ := hs.switchRho_mem_Ioo hj hjn
  have hpq : AdmissiblePair (fun _ : Fin n ↦ a) (fun _ ↦ b) := switchPair_admissible hj hjn hγ0 hγ1
  have hT : 0 < tailObjective (fun _ : Fin n ↦ a) (fun _ ↦ b) := by
    apply tailObjective_pos_of_meanGap_pos
    rw [meanGap_const, hs.2.2.2.1]
    exact mul_pos (by exact_mod_cast (show 0 < n by omega)) hγ0
  have hcommon := activeThresholds_cons_common hpq (hs.activeThresholds_eq hj hjn) hT hρ.1 hρ.2
  have hP0 : P 0 = Fin.cons ρ (fun _ : Fin n ↦ a) := by simp [P, dimensionUpperPath]
  have hQ0 : Q 0 = Fin.cons ρ (fun _ : Fin n ↦ b) := by simp [Q, dimensionLowerPath]
  have hunique : activeThresholds (P 0) (Q 0) = {j + 1} := by
    rw [hP0, hQ0]
    exact hcommon.2
  have hevent := tailObjective_curve_eventually_eq_of_unique P Q
    (continuous_dimensionUpperPath n a ρ) (continuous_dimensionLowerPath n b ρ) 0 hunique
  have hder := hs.hasDerivAt_dimensionPath hj hjn
  have hobj : HasDerivAt (fun ε ↦ tailObjective (P ε) (Q ε))
      (pbMass (fun _ : Fin n ↦ a) j -
        (switchRhoDensity n j a b a + switchRhoDensity n j a b b) / 2) 0 :=
    hder.congr_of_eventuallyEq hevent
  have hneg : pbMass (fun _ : Fin n ↦ a) j -
      (switchRhoDensity n j a b a + switchRhoDensity n j a b b) / 2 < 0 :=
    switchRhoDensity_improvement_neg hj hjn hγ0 hγ1
  have hdesc := eventually_descends hobj hneg
  have hfeasible := dimensionPath_eventually_admissible (n := n) hs.1 hs.2.1 hs.2.2.1 hρ.1 hρ.2
  have hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  obtain ⟨ε, hε, hfeas, himprove⟩ := (hpos.and (hfeasible.and hdesc)).exists
  refine ⟨ε, hε, hfeas, ?_, ?_⟩
  · rw [meanGap_dimensionPath n (by omega), hs.2.2.2.1]
  · have hbase : tailObjective (P 0) (Q 0) = switchValue n j γ := by
      rw [hP0, hQ0, hcommon.1]
      exact tailObjective_switchPair hj hjn hγ0 hγ1
    exact himprove.trans_eq hbase

theorem exists_dimension_endpoint_improvement (n : ℕ) (hn : 0 < n) :
    ∃ p q : Fin (n + 1) → ℝ, AdmissiblePair p q ∧ meanGap p q = n ∧
      tailObjective p q < 1 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < n + 1 := by positivity
  let γ : ℝ := n / (n + 1)
  let a : ℝ := (1 + γ) / 2
  let b : ℝ := (1 - γ) / 2
  have hγ0 : 0 < γ := div_pos hn0 hn1
  have hγ1 : γ < 1 := (div_lt_one hn1).mpr (by linarith)
  have hb0 : 0 < b := by dsimp [b]; linarith
  have hba : b < a := by dsimp [a, b]; linarith
  have ha1 : a < 1 := by dsimp [a]; linarith
  have hp : ValidParameters (fun _ : Fin (n + 1) ↦ a) :=
    fun _ ↦ ⟨(hb0.trans hba).le, ha1.le⟩
  have hq : ValidParameters (fun _ : Fin (n + 1) ↦ b) :=
    fun _ ↦ ⟨hb0.le, (hba.trans ha1).le⟩
  refine ⟨(fun _ ↦ a), (fun _ ↦ b),
    (admissiblePair_iff _ _).mpr (fun _ ↦ ⟨hb0.le, hba.le, ha1.le⟩), ?_, ?_⟩
  · rw [meanGap_const]
    push_cast
    dsimp [a, b, γ]
    field_simp
    ring
  · apply (tailObjective_le_productTV _ _).trans_lt
      (productTV_lt_one_of_common_atom hp hq ∅ ?_ ?_)
    · simp [bernoulliWeight]
      exact pow_pos (sub_pos.mpr ha1) (n + 1)
    · simp [bernoulliWeight]
      exact pow_pos (sub_pos.mpr (hba.trans ha1)) (n + 1)

theorem dimension_improvement {n : ℕ} (hn : 2 ≤ n) {Δ : ℝ}
    (hΔ0 : 0 < Δ) (hΔn : Δ ≤ n) :
    ∃ p q : Fin (n + 1) → ℝ, AdmissiblePair p q ∧ meanGap p q = Δ ∧
      tailObjective p q < benchmark n Δ := by
  rcases hΔn.eq_or_lt with heq | hlt
  · subst Δ
    simpa only [benchmark_at_dimension (show 0 < n by omega)] using
      exists_dimension_endpoint_improvement n (by omega)
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hj : 0 < n / 2 := by omega
    have hjn : n / 2 < n := by omega
    have hγ0 : 0 < Δ / n := div_pos hΔ0 hn0
    have hγ1 : Δ / n < 1 := (div_lt_one hn0).mpr hlt
    obtain ⟨ε, _, hfeasible, hgap, himprove⟩ :=
      switch_dimension_improvement hj hjn hγ0 hγ1
    refine ⟨_, _, hfeasible, ?_, ?_⟩
    · rw [hgap]
      field_simp
    · rw [benchmark_eq_switchValue hΔ0 hlt]
      exact himprove

end

end PoissonBinomialComparison

-- HomogeneousMinimizer
namespace PoissonBinomialComparison

open scoped BigOperators Topology
open Finset Filter

noncomputable section

def homogeneousTailDiff (n : ℕ) (γ : ℝ) (k : ℕ) (b : ℝ) : ℝ :=
  tailDiff (fun _ : Fin n ↦ b + γ) (fun _ ↦ b) k

def homogeneousObjective (n : ℕ) (γ b : ℝ) : ℝ :=
  tailObjective (fun _ : Fin n ↦ b + γ) (fun _ ↦ b)

theorem continuous_homogeneousTailDiff (n k : ℕ) (γ : ℝ) :
    Continuous (homogeneousTailDiff n γ k) := by
  exact (continuous_tailDiff k).comp (show Continuous (fun b : ℝ ↦ ((fun _ : Fin n ↦ b+γ), (fun _ : Fin n ↦ b))) by fun_prop)

theorem continuous_homogeneousObjective (n : ℕ) (γ : ℝ) :
    Continuous (homogeneousObjective n γ) := by
  have hmap : Continuous (fun b : ℝ ↦ ((fun _ : Fin n ↦ b+γ), (fun _ : Fin n ↦ b))) := by fun_prop
  have h := (continuous_tailObjective (n := n)).comp hmap
  exact h

theorem hasDerivAt_homogeneousTailDiff (n k : ℕ) (γ b : ℝ) :
    HasDerivAt (homogeneousTailDiff n γ (k + 1))
      ((n : ℝ) * (pbMass (fun _ : Fin (n - 1) ↦ b + γ) k -
        pbMass (fun _ : Fin (n - 1) ↦ b) k)) b := by
  have h := ((hasDerivAt_pbTail_const_succ n k (b + γ)).comp b
    ((hasDerivAt_id b).add_const γ)).sub (hasDerivAt_pbTail_const_succ n k b)
  convert! h using 1
  · ring

theorem pbMass_const_pos_of_interior (m k : ℕ) (hk : k ≤ m) {b : ℝ}
    (hb0 : 0 < b) (hb1 : b < 1) : 0 < pbMass (fun _ : Fin m ↦ b) k := by
  rw [pbMass_const]
  have hc : (0 : ℝ) < m.choose k := by exact_mod_cast Nat.choose_pos hk
  exact mul_pos (mul_pos hc (pow_pos hb0 _)) (pow_pos (sub_pos.mpr hb1) _)

private theorem density_ratio_strictAntiOn {m k : ℕ} (hm : 1 ≤ m) (hk : k ≤ m)
    {γ : ℝ} (hγ : 0 < γ) :
    StrictAntiOn
      (fun b : ℝ ↦ ((b + γ) / b) ^ k * ((1 - (b + γ)) / (1 - b)) ^ (m - k))
      (Set.Ioo 0 (1 - γ)) := by
  intro b₁ hb₁ b₂ hb₂ hlt
  have hb₁' : 0 < 1 - b₁ := by linarith [hb₁.2]
  have hb₂' : 0 < 1 - b₂ := by linarith [hb₂.2]
  have hr₁ : (b₂ + γ) / b₂ < (b₁ + γ) / b₁ := by
    apply (div_lt_div_iff₀ hb₂.1 hb₁.1).2
    nlinarith
  have hr₂ : (1 - (b₂ + γ)) / (1 - b₂) <
      (1 - (b₁ + γ)) / (1 - b₁) := by
    apply (div_lt_div_iff₀ hb₂' hb₁').2
    nlinarith
  have hp₁ : 0 < (b₂ + γ) / b₂ := div_pos (by linarith [hb₂.1]) hb₂.1
  have hp₂ : 0 < (1 - (b₁ + γ)) / (1 - b₁) :=
    div_pos (by linarith [hb₁.2]) hb₁'
  have hp₂' : 0 < (1 - (b₂ + γ)) / (1 - b₂) :=
    div_pos (by linarith [hb₂.2]) hb₂'
  by_cases hk0 : k = 0
  · subst k
    simpa using pow_lt_pow_left₀ hr₂ hp₂'.le (by omega : m ≠ 0)
  · calc
      _ ≤ ((b₂ + γ) / b₂) ^ k * ((1 - (b₁ + γ)) / (1 - b₁)) ^ (m - k) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp₂'.le hr₂.le _) (pow_nonneg hp₁.le _)
      _ < _ := mul_lt_mul_of_pos_right (pow_lt_pow_left₀ hr₁ hp₁.le hk0) (pow_pos hp₂ _)

private theorem density_ratio_eq {m k : ℕ} (hk : k ≤ m) {γ b : ℝ}
    (hb : b ∈ Set.Ioo 0 (1 - γ)) (hγ : 0 < γ) :
    pbMass (fun _ : Fin m ↦ b + γ) k / pbMass (fun _ : Fin m ↦ b) k =
      ((b + γ) / b) ^ k * ((1 - (b + γ)) / (1 - b)) ^ (m - k) := by
  have hc : (m.choose k : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk).ne'
  have hb1 : 1 - b ≠ 0 := ne_of_gt (by linarith [hb.2] : 0 < 1 - b)
  rw [pbMass_const, pbMass_const]
  simp only [div_pow]
  field_simp [hc, hb.1.ne', hb1]

theorem homogeneousTailDiff_lt_at_critical {n k : ℕ} (hn : 2 ≤ n) (hk : k < n)
    {γ b x : ℝ} (hγ : 0 < γ) (hb : b ∈ Set.Ioo 0 (1 - γ))
    (hx0 : 0 < x) (hxb : x < b)
    (hcrit : deriv (homogeneousTailDiff n γ (k + 1)) b = 0) :
    homogeneousTailDiff n γ (k + 1) x < homogeneousTailDiff n γ (k + 1) b := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hkp : k ≤ n - 1 := by omega
  have hmasspos := pbMass_const_pos_of_interior (n - 1) k hkp hb.1 (by linarith [hb.2])
  have hmass : pbMass (fun _ : Fin (n - 1) ↦ b + γ) k =
      pbMass (fun _ : Fin (n - 1) ↦ b) k := by
    rw [(hasDerivAt_homogeneousTailDiff n k γ b).deriv] at hcrit
    rcases mul_eq_zero.mp hcrit with hz | hz
    · exact False.elim (hnpos.ne' hz)
    · exact sub_eq_zero.mp hz
  have hratio : ((b + γ) / b) ^ k * ((1 - (b + γ)) / (1 - b)) ^ (n - 1 - k) = 1 := by
    rw [← density_ratio_eq hkp hb hγ, hmass, div_self hmasspos.ne']
  have hmono : StrictMonoOn (homogeneousTailDiff n γ (k + 1)) (Set.Icc x b) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc x b)
      (continuous_homogeneousTailDiff n (k + 1) γ).continuousOn
    intro t ht
    rw [interior_Icc] at ht
    have ht' : t ∈ Set.Ioo 0 (1 - γ) := ⟨hx0.trans ht.1, ht.2.trans hb.2⟩
    have hrat := density_ratio_strictAntiOn (by omega : 1 ≤ n - 1) hkp hγ ht' hb ht.2
    dsimp only at hrat
    rw [hratio, ← density_ratio_eq hkp ht' hγ] at hrat
    have hden := pbMass_const_pos_of_interior (n - 1) k hkp ht'.1 (by linarith [ht'.2])
    have hdiff : 0 < pbMass (fun _ : Fin (n - 1) ↦ t + γ) k -
        pbMass (fun _ : Fin (n - 1) ↦ t) k := by
      have hgt := (one_lt_div hden).mp hrat
      linarith
    rw [(hasDerivAt_homogeneousTailDiff n k γ t).deriv]
    exact mul_pos hnpos hdiff
  exact hmono ⟨le_rfl, hxb.le⟩ ⟨hxb.le, le_rfl⟩ hxb

theorem not_isLocalMin_homogeneousTailDiff {n k : ℕ} (hn : 2 ≤ n) (hk : k < n)
    {γ b : ℝ} (hγ : 0 < γ) (hb : b ∈ Set.Ioo 0 (1 - γ)) :
    ¬IsLocalMin (homogeneousTailDiff n γ (k + 1)) b := by
  intro hmin
  have hcrit := hmin.deriv_eq_zero
  obtain ⟨l, u, hb', hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hmin
  obtain ⟨x, hx, hxb⟩ := exists_between (max_lt hb.1 hb'.1)
  have hx0 : 0 < x := (le_max_left 0 l).trans_lt hx
  have hxl : l < x := (le_max_right 0 l).trans_lt hx
  have hlow := hsub ⟨hxl, hxb.trans hb'.2⟩
  exact not_lt_of_ge hlow (homogeneousTailDiff_lt_at_critical hn hk hγ hb hx0 hxb hcrit)

theorem homogeneousObjective_eventually_eq_of_unique {n k : ℕ} {γ b : ℝ}
    (hunique : activeThresholds (fun _ : Fin n ↦ b + γ) (fun _ ↦ b) = {k}) :
    homogeneousObjective n γ =ᶠ[𝓝 b] homogeneousTailDiff n γ k := by
  have hk : k ∈ activeThresholds (fun _ : Fin n ↦ b + γ) (fun _ ↦ b) := by rw [hunique]; simp
  have hk' := (mem_activeThresholds _ _ k).mp hk
  have hn : 0 < n := by omega
  have hevent : ∀ᶠ t in 𝓝 b, ∀ l ∈ Icc 1 n,
      homogeneousTailDiff n γ l t ≤ homogeneousTailDiff n γ k t := by
    rw [eventually_all_finset]
    intro l hl
    by_cases hlk : l = k
    · subst l
      exact Eventually.of_forall (fun _ ↦ le_rfl)
    have hlt : homogeneousTailDiff n γ l b < homogeneousTailDiff n γ k b := by
      have hle := tailDiff_le_tailObjective (fun _ : Fin n ↦ b + γ) (fun _ ↦ b) hl
      rw [← hk'.2.2] at hle
      apply lt_of_le_of_ne hle
      intro heq
      have hlmem : l ∈ activeThresholds (fun _ : Fin n ↦ b + γ) (fun _ ↦ b) :=
        mem_filter.mpr ⟨hl, heq.trans hk'.2.2⟩
      rw [hunique, mem_singleton] at hlmem
      exact hlk hlmem
    exact ((continuous_homogeneousTailDiff n l γ).continuousAt.eventually_lt
      (continuous_homogeneousTailDiff n k γ).continuousAt hlt).mono (fun _ ht ↦ ht.le)
  filter_upwards [hevent] with t ht
  apply le_antisymm
  · exact (tailObjective_le_iff _ _ hn _).mpr ht
  · exact tailDiff_le_tailObjective _ _ (mem_Icc.mpr ⟨hk'.1, hk'.2.1⟩)

theorem homogeneous_localMin_is_switch {n : ℕ} (hn : 2 ≤ n) {γ b : ℝ}
    (hγ : 0 < γ) (hb : b ∈ Set.Ioo 0 (1 - γ))
    (hmin : IsLocalMin (homogeneousObjective n γ) b) :
    ∃ j, 1 ≤ j ∧ j < n ∧ IsSwitch n j γ (b + γ) b := by
  have hpq : AdmissiblePair (fun _ : Fin n ↦ b + γ) (fun _ ↦ b) :=
    (admissiblePair_iff _ _).mpr (fun _ ↦ ⟨hb.1.le, by linarith, by linarith [hb.2]⟩)
  have hgap : 0 < meanGap (fun _ : Fin n ↦ b + γ) (fun _ ↦ b) := by
    rw [meanGap_const]
    exact mul_pos (by exact_mod_cast (show 0 < n by omega)) (by linarith)
  have hT : tailObjective (fun _ : Fin n ↦ b + γ) (fun _ ↦ b) < 1 := by
    apply (tailObjective_le_productTV _ _).trans_lt
      (productTV_lt_one_of_common_atom hpq.1 hpq.2.1 ∅ ?_ ?_)
    · simp [bernoulliWeight]
      exact pow_pos (by linarith [hb.2]) n
    · simp [bernoulliWeight]
      exact pow_pos (by linarith [hb.2]) n
  obtain ⟨j, hj, hjn, hactive⟩ := activeThresholds_singleton_or_adjacent hpq hgap hT
  rcases hactive with hsingle | ⟨hjnext, hpair⟩
  · have hlocal := hmin.congr (homogeneousObjective_eventually_eq_of_unique hsingle)
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    exact False.elim (not_isLocalMin_homogeneousTailDiff hn (by omega) hγ hb hlocal)
  · refine ⟨j, hj, by omega, hb.1, by linarith, by linarith [hb.2], by ring, ?_⟩
    have hjmem : j ∈ activeThresholds (fun _ : Fin n ↦ b + γ) (fun _ ↦ b) := by
      rw [hpair]; simp
    have hjmem' : j + 1 ∈ activeThresholds (fun _ : Fin n ↦ b + γ) (fun _ ↦ b) := by
      rw [hpair]; simp
    have heq := (mem_activeThresholds _ _ j).mp hjmem |>.2.2
    have heq' := (mem_activeThresholds _ _ (j + 1)).mp hjmem' |>.2.2
    have hd := tailDiff_sub_succ (fun _ : Fin n ↦ b + γ) (fun _ ↦ b) j
    have hm : pbMass (fun _ : Fin n ↦ b + γ) j = pbMass (fun _ : Fin n ↦ b) j := by
      linarith
    exact (pbMass_const_eq_iff hjn (b + γ) b).mp hm

theorem homogeneous_localMinOn_interior_is_switch {n : ℕ} (hn : 2 ≤ n) {γ b : ℝ}
    (hγ : 0 < γ) (hb : b ∈ Set.Ioo 0 (1 - γ))
    (hmin : IsLocalMinOn (homogeneousObjective n γ) (Set.Icc 0 (1 - γ)) b) :
    ∃ j, 1 ≤ j ∧ j < n ∧ IsSwitch n j γ (b + γ) b :=
  homogeneous_localMin_is_switch hn hγ hb (hmin.isLocalMin (Icc_mem_nhds hb.1 hb.2))

theorem pbTail_antitone {n : ℕ} {p : Fin n → ℝ} (hp : ValidParameters p) :
    Antitone (pbTail p) := by
  intro k l hkl
  rw [pbTail_eq_sum_mass, pbTail_eq_sum_mass]
  apply sum_le_sum_of_subset_of_nonneg
  · intro j hj
    exact mem_Icc.mpr ⟨hkl.trans (mem_Icc.mp hj).1, (mem_Icc.mp hj).2⟩
  · intro j _ _
    exact pbMass_nonneg hp j

theorem homogeneous_activeThresholds_left {n : ℕ} (hn : 2 ≤ n) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    activeThresholds (fun _ : Fin n ↦ 0 + γ) (fun _ ↦ (0 : ℝ)) = {1} := by
  have hp : ValidParameters (fun _ : Fin n ↦ γ) := fun _ ↦ ⟨hγ0.le, hγ1.le⟩
  have hd (k : ℕ) (hk : 1 ≤ k) :
      tailDiff (fun _ : Fin n ↦ 0 + γ) (fun _ ↦ 0) k = pbTail (fun _ : Fin n ↦ γ) k := by
    simp [tailDiff, pbTail_const_zero, show k ≠ 0 by omega]
  have hmax : tailObjective (fun _ : Fin n ↦ 0 + γ) (fun _ ↦ 0) =
      pbTail (fun _ : Fin n ↦ γ) 1 := by
    apply le_antisymm
    · rw [tailObjective_le_iff _ _ (by omega)]
      intro k hk
      rw [hd k (mem_Icc.mp hk).1]
      exact pbTail_antitone hp (mem_Icc.mp hk).1
    · rw [← hd 1 le_rfl]
      exact tailDiff_le_tailObjective _ _ (mem_Icc.mpr ⟨le_rfl, by omega⟩)
  have hstrict : pbTail (fun _ : Fin n ↦ γ) 2 < pbTail (fun _ : Fin n ↦ γ) 1 := by
    have hmass := pbMass_const_pos_of_interior n 1 (by omega) hγ0 hγ1
    have htail := pbTail_sub_succ (fun _ : Fin n ↦ γ) 1
    linarith
  apply eq_singleton_iff_unique_mem.mpr
  constructor
  · exact (mem_activeThresholds _ _ 1).mpr ⟨le_rfl, by omega, (hd 1 le_rfl).trans hmax.symm⟩
  · intro k hk
    have hk' := (mem_activeThresholds _ _ k).mp hk
    by_contra hk1
    have hge : 2 ≤ k := by omega
    have hlt := (pbTail_antitone hp hge).trans_lt hstrict
    rw [← hd k hk'.1, hk'.2.2, hmax] at hlt
    exact lt_irrefl _ hlt

private theorem nonneg_derivative_of_localMinOn_left {f : ℝ → ℝ} {d a b : ℝ}
    (hab : a < b) (hmin : IsLocalMinOn f (Set.Icc a b) a) (hd : HasDerivAt f d a) : 0 ≤ d := by
  have htan : (1 : ℝ) ∈ posTangentConeAt (Set.Icc a b) a := by
    apply mem_posTangentConeAt_of_frequently_mem
    have hsmall : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < b - a :=
      nhdsWithin_le_nhds (eventually_lt_nhds (sub_pos.mpr hab))
    have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
    apply Eventually.frequently
    filter_upwards [hsmall, hpos] with t ht ht0
    simp only [smul_eq_mul, mul_one, Set.mem_Icc]
    constructor <;> linarith
  have h := hmin.hasFDerivWithinAt_nonneg hd.hasFDerivAt.hasFDerivWithinAt htan
  simpa using h

theorem not_isLocalMinOn_homogeneousObjective_left {n : ℕ} (hn : 2 ≤ n) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    ¬IsLocalMinOn (homogeneousObjective n γ) (Set.Icc 0 (1 - γ)) 0 := by
  intro hmin
  have hunique := homogeneous_activeThresholds_left hn hγ0 hγ1
  have hevent := homogeneousObjective_eventually_eq_of_unique hunique
  have hlocal := hmin.congr (hevent.filter_mono nhdsWithin_le_nhds)
    (show (0 : ℝ) ∈ Set.Icc 0 (1 - γ) from ⟨le_rfl, by linarith⟩)
  have hder := hasDerivAt_homogeneousTailDiff n 0 γ 0
  have hnonneg := nonneg_derivative_of_localMinOn_left (by linarith : (0 : ℝ) < 1 - γ) hlocal hder
  simp only [zero_add, pbMass_zero, prod_const, card_univ, Fintype.card_fin, sub_zero, one_pow] at hnonneg
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hp : (1 - γ) ^ (n - 1) < (1 : ℝ) :=
    pow_lt_one₀ (by linarith) (by linarith) (by omega)
  exact not_lt_of_ge hnonneg (mul_neg_of_pos_of_neg hnpos (sub_neg.mpr hp))

theorem homogeneousObjective_reflection (n : ℕ) (γ b : ℝ) :
    homogeneousObjective n γ (1 - γ - b) = homogeneousObjective n γ b := by
  unfold homogeneousObjective
  have hp : (fun _ : Fin n ↦ 1 - γ - b + γ) = (fun _ ↦ 1 - b) := by funext i; ring
  have hq : (fun _ : Fin n ↦ 1 - γ - b) = (fun _ ↦ 1 - (b + γ)) := by funext i; ring
  rw [hp, hq]
  exact tailObjective_reflection (fun _ : Fin n ↦ b + γ) (fun _ ↦ b)

theorem not_isLocalMinOn_homogeneousObjective_right {n : ℕ} (hn : 2 ≤ n) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    ¬IsLocalMinOn (homogeneousObjective n γ) (Set.Icc 0 (1 - γ)) (1 - γ) := by
  intro hmin
  let g : ℝ → ℝ := fun t ↦ 1 - γ - t
  have hmin' : IsLocalMinOn (homogeneousObjective n γ) (Set.Icc 0 (1 - γ)) (g 0) := by
    simpa [g] using hmin
  have hmap : Set.Icc 0 (1 - γ) ⊆ g ⁻¹' Set.Icc 0 (1 - γ) := by
    intro t ht
    change 0 ≤ 1 - γ - t ∧ 1 - γ - t ≤ 1 - γ
    constructor <;> linarith [ht.1, ht.2]
  have hcomp := hmin'.comp_continuousOn hmap (by fun_prop : ContinuousOn g (Set.Icc 0 (1 - γ)))
    (show (0 : ℝ) ∈ Set.Icc 0 (1 - γ) from ⟨le_rfl, by linarith⟩)
  have heq : homogeneousObjective n γ ∘ g = homogeneousObjective n γ := by
    funext t
    exact homogeneousObjective_reflection n γ t
  rw [heq] at hcomp
  exact not_isLocalMinOn_homogeneousObjective_left hn hγ0 hγ1 hcomp

theorem homogeneous_localMinOn_is_switch {n : ℕ} (hn : 2 ≤ n) {γ b : ℝ}
    (hγ0 : 0 < γ) (hγ1 : γ < 1) (hb : b ∈ Set.Icc 0 (1 - γ))
    (hmin : IsLocalMinOn (homogeneousObjective n γ) (Set.Icc 0 (1 - γ)) b) :
    ∃ j, 1 ≤ j ∧ j < n ∧ IsSwitch n j γ (b + γ) b := by
  have hb0 : 0 < b := by
    apply lt_of_le_of_ne hb.1
    intro heq
    subst b
    exact not_isLocalMinOn_homogeneousObjective_left hn hγ0 hγ1 hmin
  have hb1 : b < 1 - γ := by
    apply lt_of_le_of_ne hb.2
    intro heq
    rw [heq] at hmin
    exact not_isLocalMinOn_homogeneousObjective_right hn hγ0 hγ1 hmin
  exact homogeneous_localMinOn_interior_is_switch hn hγ0 ⟨hb0, hb1⟩ hmin

theorem homogeneous_minimizer_is_switch {n : ℕ} (hn : 2 ≤ n) {γ b : ℝ}
    (hγ0 : 0 < γ) (hγ1 : γ < 1) (hb : b ∈ Set.Icc 0 (1 - γ))
    (hmin : IsMinOn (homogeneousObjective n γ) (Set.Icc 0 (1 - γ)) b) :
    ∃ j, 1 ≤ j ∧ j < n ∧ IsSwitch n j γ (b + γ) b :=
  homogeneous_localMinOn_is_switch hn hγ0 hγ1 hb (IsMinOn.localize hmin)

theorem exists_homogeneous_minimizing_switch {n : ℕ} (hn : 2 ≤ n) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    ∃ j b, 1 ≤ j ∧ j < n ∧ IsSwitch n j γ (b + γ) b ∧
      IsMinOn (homogeneousObjective n γ) (Set.Icc 0 (1 - γ)) b := by
  obtain ⟨b, hb, hmin⟩ := isCompact_Icc.exists_isMinOn
    (Set.nonempty_Icc.mpr (by linarith : (0 : ℝ) ≤ 1 - γ))
    (continuous_homogeneousObjective n γ).continuousOn
  obtain ⟨j, hj, hjn, hswitch⟩ := homogeneous_minimizer_is_switch hn hγ0 hγ1 hb hmin
  exact ⟨j, b, hj, hjn, hswitch, hmin⟩

end

end PoissonBinomialComparison

-- SwitchIntegral
namespace PoissonBinomialComparison

open MeasureTheory

theorem intervalIntegrable_switchMass {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    IntervalIntegrable (switchMass n j) volume 0 γ :=
  ((continuousOn_switchMass hj hjn).mono (Set.Icc_subset_Icc le_rfl hγ1)).intervalIntegrable_of_Icc hγ0

theorem hasDerivAt_switchValue_add_mul_mass {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    HasDerivAt (fun u ↦ switchValue n j u + u * switchMass n j u)
      (((n : ℝ) + 1) * switchMass n j γ) γ := by
  have hF := (hasDerivAt_switchValue hj hjn hγ0 hγ1).differentiableAt.hasDerivAt
  have hf := (hasDerivAt_switchMass hj hjn hγ0 hγ1).differentiableAt.hasDerivAt
  convert! hF.add ((hasDerivAt_id γ).mul hf) using 1
  · rw [deriv_switchValue_eq_mass_sub hj hjn hγ0 hγ1]
    simp only [id_eq]
    ring

theorem switchValue_eq_integral_mass {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    switchValue n j γ = ((n : ℝ) + 1) * (∫ u in (0 : ℝ)..γ, switchMass n j u) -
      γ * switchMass n j γ := by
  have hF := (continuousOn_switchValue hj hjn).mono (Set.Icc_subset_Icc le_rfl hγ1)
  have hf := (continuousOn_switchMass hj hjn).mono (Set.Icc_subset_Icc le_rfl hγ1)
  have hcont : ContinuousOn (fun u ↦ switchValue n j u + u * switchMass n j u)
      (Set.Icc 0 γ) := hF.add (continuousOn_id.mul hf)
  have hint : IntervalIntegrable (fun u ↦ ((n : ℝ) + 1) * switchMass n j u) volume 0 γ :=
    (intervalIntegrable_switchMass hj hjn hγ0 hγ1).const_mul _
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hγ0 hcont
    (fun u hu ↦ hasDerivAt_switchValue_add_mul_mass hj hjn hu.1 (lt_of_lt_of_le hu.2 hγ1)) hint
  rw [intervalIntegral.integral_const_mul] at hFTC
  simp only [switchValue_zero, zero_mul, add_zero, sub_zero] at hFTC
  linarith

theorem integral_switchMass {n j : ℕ} (hj : 0 < j) (hjn : j < n) :
    (∫ u in (0 : ℝ)..1, switchMass n j u) = 1 / ((n : ℝ) + 1) := by
  have h := switchValue_eq_integral_mass hj hjn (γ := 1) zero_le_one le_rfl
  rw [switchValue_one hj hjn.le, switchMass_one hjn] at h
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  apply (eq_div_iff hn).2
  linarith

end PoissonBinomialComparison

-- SwitchOrdering
namespace PoissonBinomialComparison

open Set MeasureTheory

private theorem decay_ratio_strictAntiOn {f g A B : ℝ → ℝ}
    (hf : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt f (-A x * f x) x)
    (hg : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt g (-B x * g x) x)
    (hfp : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < f x)
    (hgp : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < g x)
    (hAB : ∀ x ∈ Ioo (0 : ℝ) 1, B x < A x) :
    StrictAntiOn (fun x ↦ f x / g x) (Ioo (0 : ℝ) 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioo 0 1)
  · intro x hx
    exact ((hf x hx).div (hg x hx) (hgp x hx).ne').continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioo] at hx
    change deriv (f / g) x < 0
    rw [((hf x hx).div (hg x hx) (hgp x hx).ne').deriv]
    apply div_neg_of_neg_of_pos _ (sq_pos_of_pos (hgp x hx))
    have hp := mul_pos (sub_pos.mpr (hAB x hx)) (mul_pos (hfp x hx) (hgp x hx))
    nlinarith

theorem integral_endpoint_strict_comparison {f g A B : ℝ → ℝ} {N γ : ℝ}
    (hN : 0 < N) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hfc : ContinuousOn f (Icc 0 1)) (hgc : ContinuousOn g (Icc 0 1))
    (hf : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt f (-A x * f x) x)
    (hg : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt g (-B x * g x) x)
    (hfp : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < f x)
    (hgp : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < g x)
    (hBp : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < B x)
    (hAB : ∀ x ∈ Ioo (0 : ℝ) 1, B x < A x)
    (hone : f 1 = g 1)
    (hnorm : (∫ x in (0 : ℝ)..1, f x) = ∫ x in (0 : ℝ)..1, g x) :
    (N + 1) * (∫ x in (0 : ℝ)..γ, g x) - γ * g γ <
      (N + 1) * (∫ x in (0 : ℝ)..γ, f x) - γ * f γ := by
  let h := fun x ↦ f x - g x
  have hc : ContinuousOn h (Icc 0 1) := hfc.sub hgc
  have hfi := hfc.intervalIntegrable_of_Icc (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
  have hgi := hgc.intervalIntegrable_of_Icc (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
  have hci := hc.intervalIntegrable_of_Icc (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
  have hsub : Icc (0 : ℝ) γ ⊆ Icc (0 : ℝ) 1 := fun x hx ↦ ⟨hx.1, hx.2.trans hγ1.le⟩
  have hsub' : Icc γ (1 : ℝ) ⊆ Icc (0 : ℝ) 1 := fun x hx ↦ ⟨hγ0.le.trans hx.1, hx.2⟩
  have hfiγ := (hfc.mono hsub).intervalIntegrable_of_Icc (μ := volume) hγ0.le
  have hgiγ := (hgc.mono hsub).intervalIntegrable_of_Icc (μ := volume) hγ0.le
  have hciγ := (hc.mono hsub).intervalIntegrable_of_Icc (μ := volume) hγ0.le
  have hciγ' := (hc.mono hsub').intervalIntegrable_of_Icc (μ := volume) hγ1.le
  have htotal : (∫ x in (0 : ℝ)..1, h x) = 0 := by
    rw [show h = fun x ↦ f x - g x from rfl, intervalIntegral.integral_sub hfi hgi, hnorm]
    ring
  have hr := decay_ratio_strictAntiOn hf hg hfp hgp hAB
  have hγmem : γ ∈ Ioo (0 : ℝ) 1 := ⟨hγ0, hγ1⟩
  have hgoal : 0 < (N + 1) * (∫ x in (0 : ℝ)..γ, h x) - γ * h γ := by
    by_cases hpos : 0 < h γ
    · have hpos_before : ∀ x ∈ Ioo (0 : ℝ) γ, 0 < h x := by
        intro x hx
        have hx' : x ∈ Ioo (0 : ℝ) 1 := ⟨hx.1, hx.2.trans hγ1⟩
        have hrγ : 1 < f γ / g γ := (one_lt_div (hgp γ hγmem)).mpr (by dsimp [h] at hpos; linarith)
        have hrx := hr hx' hγmem hx.2
        have : g x < f x := (one_lt_div (hgp x hx')).mp (hrγ.trans hrx)
        dsimp [h]
        linarith
      have hanti : StrictAntiOn h (Icc (0 : ℝ) γ) := by
        apply strictAntiOn_of_deriv_neg (convex_Icc 0 γ) (hc.mono hsub)
        intro x hx
        rw [interior_Icc] at hx
        have hx' : x ∈ Ioo (0 : ℝ) 1 := ⟨hx.1, hx.2.trans hγ1⟩
        change deriv (f - g) x < 0
        rw [((hf x hx').sub (hg x hx')).deriv]
        have hAx : 0 < A x := (hBp x hx').trans (hAB x hx')
        have h1 := mul_pos hAx (hpos_before x hx)
        have h2 := mul_pos (sub_pos.mpr (hAB x hx')) (hgp x hx')
        dsimp [h] at h1
        nlinarith
      have hbound : γ * h γ ≤ ∫ x in (0 : ℝ)..γ, h x := by
        have hi := intervalIntegral.integral_mono_on hγ0.le
          (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ ↦ h γ) volume 0 γ) hciγ
          (fun x hx ↦ hanti.antitoneOn hx ⟨hγ0.le, le_rfl⟩ hx.2)
        simpa using hi
      have hprod := mul_pos (mul_pos hN hγ0) hpos
      nlinarith
    · have hneg_after : ∀ x ∈ Ioo γ (1 : ℝ), h x < 0 := by
        intro x hx
        have hx' : x ∈ Ioo (0 : ℝ) 1 := ⟨hγ0.trans hx.1, hx.2⟩
        have hrγ : f γ / g γ ≤ 1 := (div_le_one (hgp γ hγmem)).mpr (by dsimp [h] at hpos; linarith)
        have hrx := hr hγmem hx' hx.1
        have : f x < g x := (div_lt_one (hgp x hx')).mp (hrx.trans_le hrγ)
        dsimp [h]
        linarith
      have hnegative : (∫ x in γ..(1 : ℝ), h x) < 0 := by
        have hi := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
          (g := fun _ ↦ (0 : ℝ)) hγ1 (hc.mono hsub') continuousOn_const
          (fun x hx ↦ ?_) ?_
        · simpa using hi
        · by_cases hx1 : x = 1
          · simp [h, hx1, hone]
          · exact (hneg_after x ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩).le
        · refine ⟨(γ + 1) / 2, ⟨by linarith, by linarith⟩, ?_⟩
          exact hneg_after _ ⟨by linarith, by linarith⟩
      have hadd := intervalIntegral.integral_add_adjacent_intervals hciγ hciγ'
      rw [htotal] at hadd
      have hpositive : 0 < ∫ x in (0 : ℝ)..γ, h x := by linarith
      have hp := mul_pos (by linarith : 0 < N + 1) hpositive
      have hn := mul_nonpos_of_nonneg_of_nonpos hγ0.le (le_of_not_gt hpos)
      linarith
  rw [show h = fun x ↦ f x - g x from rfl, intervalIntegral.integral_sub hfiγ hgiγ] at hgoal
  dsimp at hgoal
  linarith

theorem switchValue_strict_order {n i j : ℕ} (hi : 0 < i) (hij : i < j)
    (hj : j ≤ n / 2) {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    switchValue n j γ < switchValue n i γ := by
  have hj0 : 0 < j := by omega
  have hjn : j < n := by omega
  have hin : i < n := by omega
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  let A := fun x ↦ (n : ℝ) * switchRatio n i x / (x * (1 - switchRatio n i x))
  let B := fun x ↦ (n : ℝ) * switchRatio n j x / (x * (1 - switchRatio n j x))
  have hrate : ∀ x ∈ Ioo (0 : ℝ) 1, B x < A x := by
    intro x hx
    have hRi := switchRatio_bounds hi hin hx.1 hx.2
    have hRj := switchRatio_bounds hj0 hjn hx.1 hx.2
    have hR := switchRatio_strict_order hi hij hj hx.1 hx.2
    apply (div_lt_div_iff₀ (mul_pos hx.1 (sub_pos.mpr hRj.2))
      (mul_pos hx.1 (sub_pos.mpr hRi.2))).mpr
    have hp := mul_pos (mul_pos hn hx.1) (sub_pos.mpr hR)
    nlinarith
  have hf : ∀ x ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (switchMass n i) (-A x * switchMass n i x) x := by
    intro x hx
    simpa [A, neg_div] using hasDerivAt_switchMass hi hin hx.1 hx.2
  have hg : ∀ x ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (switchMass n j) (-B x * switchMass n j x) x := by
    intro x hx
    simpa [B, neg_div] using hasDerivAt_switchMass hj0 hjn hx.1 hx.2
  have hcomp := integral_endpoint_strict_comparison hn hγ0 hγ1
    (continuousOn_switchMass hi hin) (continuousOn_switchMass hj0 hjn)
    hf hg (fun x hx ↦ switchMass_pos hi hin hx.1 hx.2)
    (fun x hx ↦ switchMass_pos hj0 hjn hx.1 hx.2)
    (fun x hx ↦ div_pos (mul_pos hn (switchRatio_bounds hj0 hjn hx.1 hx.2).1)
      (mul_pos hx.1 (sub_pos.mpr (switchRatio_bounds hj0 hjn hx.1 hx.2).2)))
    hrate (by simp [switchMass_one hin, switchMass_one hjn])
    (by rw [integral_switchMass hi hin, integral_switchMass hj0 hjn])
  simpa only [switchValue_eq_integral_mass hi hin hγ0.le hγ1.le,
    switchValue_eq_integral_mass hj0 hjn hγ0.le hγ1.le] using hcomp

theorem switchValue_central_lt {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    (hjc : j ≠ n / 2) (hjrc : j ≠ n - n / 2)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    switchValue n (n / 2) γ < switchValue n j γ := by
  by_cases hjhalf : j ≤ n / 2
  · exact switchValue_strict_order hj (by omega) le_rfl hγ0 hγ1
  · rw [← switchValue_reflection hj hjn hγ0 hγ1]
    exact switchValue_strict_order (by omega : 0 < n - j)
      (by omega : n - j < n / 2) le_rfl hγ0 hγ1

theorem switchValue_central_le {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    switchValue n (n / 2) γ ≤ switchValue n j γ := by
  by_cases hjc : j = n / 2
  · subst j
    exact le_rfl
  by_cases hjrc : j = n - n / 2
  · subst j
    rw [switchValue_reflection (by omega : 0 < n / 2) (by omega : n / 2 < n) hγ0 hγ1]
  exact (switchValue_central_lt hj hjn hjc hjrc hγ0 hγ1).le

theorem switchValue_eq_central_iff {n j : ℕ} (hj : 0 < j) (hjn : j < n)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    switchValue n j γ = switchValue n (n / 2) γ ↔
      j = n / 2 ∨ j = n - n / 2 := by
  constructor
  · intro heq
    by_contra h
    push Not at h
    exact (switchValue_central_lt hj hjn h.1 h.2 hγ0 hγ1).ne heq.symm
  · rintro (rfl | rfl)
    · rfl
    · exact switchValue_reflection (by omega : 0 < n / 2) (by omega : n / 2 < n) hγ0 hγ1

end PoissonBinomialComparison

-- HomogeneousMinimum
namespace PoissonBinomialComparison

noncomputable section

theorem IsSwitch.tailObjective_eq_switchValue {n j : ℕ} {γ a b : ℝ}
    (h : IsSwitch n j γ a b) (hj : 0 < j) (hjn : j < n) :
    tailObjective (fun _ : Fin n ↦ a) (fun _ ↦ b) = switchValue n j γ := by
  obtain ⟨ha, hb⟩ := h.eq_switchPair hj hjn
  rw [ha, hb]
  exact tailObjective_switchPair hj hjn (by linarith [h.2.1, h.2.2.2.1])
    (by linarith [h.1, h.2.2.1, h.2.2.2.1])

theorem benchmark_mul_gap {n : ℕ} (hn : 0 < n) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    benchmark n (n * γ) = switchValue n (n / 2) γ := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [benchmark_eq_switchValue (mul_pos hn0 hγ0) (by nlinarith)]
  congr 1
  field_simp

theorem switchValue_le_homogeneousObjective {n : ℕ} (hn : 2 ≤ n) {γ b : ℝ}
    (hγ0 : 0 < γ) (hγ1 : γ < 1) (hb : b ∈ Set.Icc 0 (1 - γ)) :
    switchValue n (n / 2) γ ≤ homogeneousObjective n γ b := by
  obtain ⟨j, c, hj, hjn, hs, hmin⟩ := exists_homogeneous_minimizing_switch hn hγ0 hγ1
  have heq : homogeneousObjective n γ c = switchValue n j γ :=
    hs.tailObjective_eq_switchValue (by omega) hjn
  exact (switchValue_central_le (by omega) hjn hγ0 hγ1).trans (heq ▸ hmin hb)

theorem homogeneousObjective_eq_central_iff {n : ℕ} (hn : 2 ≤ n) {γ b : ℝ}
    (hγ0 : 0 < γ) (hγ1 : γ < 1) (hb : b ∈ Set.Icc 0 (1 - γ)) :
    homogeneousObjective n γ b = switchValue n (n / 2) γ ↔
      IsSwitch n (n / 2) γ (b + γ) b ∨
      IsSwitch n (n - n / 2) γ (b + γ) b := by
  constructor
  · intro heq
    have hmin : IsMinOn (homogeneousObjective n γ) (Set.Icc 0 (1 - γ)) b := by
      intro c hc
      rw [heq]
      exact switchValue_le_homogeneousObjective hn hγ0 hγ1 hc
    obtain ⟨j, hj, hjn, hs⟩ := homogeneous_minimizer_is_switch hn hγ0 hγ1 hb hmin
    have hval := hs.tailObjective_eq_switchValue (by omega) hjn
    have hindex := (switchValue_eq_central_iff (by omega) hjn hγ0 hγ1).mp
      (hval.symm.trans heq)
    rcases hindex with rfl | rfl
    · exact Or.inl hs
    · exact Or.inr hs
  · rintro (hs | hs)
    · exact hs.tailObjective_eq_switchValue (by omega) (by omega)
    · exact (hs.tailObjective_eq_switchValue (by omega) (by omega)).trans
        ((switchValue_eq_central_iff (by omega : 0 < n - n / 2)
          (by omega) hγ0 hγ1).mpr (Or.inr rfl))

theorem homogeneous_minimum {n : ℕ} (hn : 2 ≤ n) {a b : ℝ}
    (hb0 : 0 ≤ b) (hba : b ≤ a) (ha1 : a ≤ 1) :
    benchmark n (n * (a - b)) ≤ tailObjective (fun _ : Fin n ↦ a) (fun _ ↦ b) := by
  have hγ0 : 0 ≤ a - b := sub_nonneg.mpr hba
  have hγ1 : a - b ≤ 1 := by linarith
  rcases hγ0.eq_or_lt with hz | hpos
  · have hab : a = b := by linarith
    subst a
    simp [benchmark]
  rcases hγ1.eq_or_lt with hone | hlt
  · have ha : a = 1 := by linarith
    have hb : b = 0 := by linarith
    subst a b
    simp only [sub_zero, mul_one, benchmark_at_dimension (show 0 < n by omega),
      tailObjective_const_one_zero (show 0 < n by omega), le_refl]
  · rw [benchmark_mul_gap (show 0 < n by omega) hpos hlt]
    have hh := switchValue_le_homogeneousObjective hn hpos hlt
      (show b ∈ Set.Icc 0 (1 - (a - b)) from ⟨hb0, by linarith⟩)
    simpa only [homogeneousObjective, add_sub_cancel] using hh

theorem homogeneous_minimum_eq_iff {n : ℕ} (hn : 2 ≤ n) {a b : ℝ}
    (hb0 : 0 ≤ b) (ha1 : a ≤ 1) (hgap0 : 0 < a - b) (hgap1 : a - b < 1) :
    tailObjective (fun _ : Fin n ↦ a) (fun _ ↦ b) = benchmark n (n * (a - b)) ↔
      IsSwitch n (n / 2) (a - b) a b ∨ IsSwitch n (n - n / 2) (a - b) a b := by
  rw [benchmark_mul_gap (show 0 < n by omega) hgap0 hgap1]
  have hh := homogeneousObjective_eq_central_iff hn hgap0 hgap1
    (show b ∈ Set.Icc 0 (1 - (a - b)) from ⟨hb0, by linarith⟩)
  simpa only [homogeneousObjective, add_sub_cancel] using hh

end

end PoissonBinomialComparison

-- MinimizerReduction
namespace PoissonBinomialComparison

open Finset Set
open scoped BigOperators

def IsGapMinimizer {n : ℕ} (p q : Fin n → ℝ) : Prop :=
  ∀ r s : Fin n → ℝ, AdmissiblePair r s → meanGap r s = meanGap p q →
    tailObjective p q ≤ tailObjective r s

theorem IsGapMinimizer.isLocalMinOn {n : ℕ} {p q : Fin n → ℝ} (hm : IsGapMinimizer p q) :
    IsLocalMinOn (fun x : (Fin n → ℝ) × (Fin n → ℝ) => tailObjective x.1 x.2)
      (feasiblePairs n (meanGap p q)) (p,q) := by
  apply IsMinOn.localize
  intro x hx
  exact hm x.1 x.2 hx.1 hx.2

theorem IsGapMinimizer.le_benchmark {n : ℕ} (hn : 2 ≤ n) {p q : Fin n → ℝ}
    (hm : IsGapMinimizer p q) (hgap0 : 0 < meanGap p q) (hgapn : meanGap p q < n) :
    tailObjective p q ≤ benchmark n (meanGap p q) := by
  have hn0 : (0 : ℝ) < n := by positivity
  have hj : 0 < n / 2 := by omega
  have hjn : n / 2 < n := by omega
  have hg0 : 0 < meanGap p q / n := div_pos hgap0 hn0
  have hg1 : meanGap p q / n < 1 := (div_lt_one hn0).mpr hgapn
  have hh := hm _ _ (switchPair_admissible hj hjn hg0 hg1)
    (show meanGap (fun _ : Fin n => switchUpper n (n/2) (meanGap p q/n))
      (fun _ => switchLower n (n/2) (meanGap p q/n)) = meanGap p q by
      rw [meanGap_switchPair hj hjn hg0 hg1]; field_simp)
  rw [tailObjective_switchPair hj hjn hg0 hg1, ← benchmark_eq_switchValue hgap0 hgapn] at hh
  exact hh

theorem IsGapMinimizer.three_le_positiveGapCoordinates {n : ℕ} (hn : 3 ≤ n)
    {p q : Fin n → ℝ} (h : AdmissiblePair p q) (hm : IsGapMinimizer p q)
    (hgap0 : 0 < meanGap p q) (hgapn : meanGap p q < n) :
    3 ≤ (positiveGapCoordinates p q).card := by
  by_contra hc
  have hlow := two_gap_lower_bound (by omega : 1 ≤ n) h (by omega)
  have hupp := hm.le_benchmark (by omega) hgap0 hgapn
  have hstrict := (benchmark_strict_bounds hn hgap0 hgapn).2.trans_le (min_le_left _ _)
  linarith

theorem IsGapMinimizer.tailObjective_lt_one {n : ℕ} (hn : 3 ≤ n)
    {p q : Fin n → ℝ} (hm : IsGapMinimizer p q)
    (hgap0 : 0 < meanGap p q) (hgapn : meanGap p q < n) : tailObjective p q < 1 :=
  (hm.le_benchmark (by omega) hgap0 hgapn).trans_lt
    ((benchmark_strict_bounds hn hgap0 hgapn).2.trans_le (min_le_right _ _))

theorem IsGapMinimizer.no_common_deterministic {n : ℕ} (hn : 3 ≤ n)
    (hind : ∀ r s : Fin (n-1) → ℝ, AdmissiblePair r s →
      benchmark (n-1) (meanGap r s) ≤ tailObjective r s)
    {p q : Fin n → ℝ} (h : AdmissiblePair p q) (hm : IsGapMinimizer p q)
    (hgap0 : 0 < meanGap p q) (i : Fin n) (heq : p i = q i) :
    p i ≠ 0 ∧ p i ≠ 1 := by
  have hfalse (hd : p i = 0 ∨ p i = 1) : False := by
    obtain ⟨r,s,hrs,hgap,hobj⟩ := exists_deleted_deterministic_pair (by omega) h i heq hd
    have hlow := hind r s hrs
    rw [hgap,hobj] at hlow
    have hbound := meanGap_le_dimension hrs
    rw [hgap] at hbound
    have himprove := dimension_improvement (by omega : 2 ≤ n-1) hgap0 hbound
    have hn' : n-1+1 = n := by omega
    rw [hn'] at himprove
    obtain ⟨r',s',hrs',hgap',hobj'⟩ := himprove
    have hmin := hm r' s' hrs' hgap'
    linarith
  exact ⟨fun hz => hfalse (Or.inl hz), fun ho => hfalse (Or.inr ho)⟩

theorem IsGapMinimizer.parameter_bounds {n : ℕ} (hn : 3 ≤ n)
    (hind : ∀ r s : Fin (n-1) → ℝ, AdmissiblePair r s →
      benchmark (n-1) (meanGap r s) ≤ tailObjective r s)
    {p q : Fin n → ℝ} (h : AdmissiblePair p q) (hm : IsGapMinimizer p q)
    (hgap0 : 0 < meanGap p q) : ∀ i, 0 < p i ∧ q i < 1 := by
  intro i
  have hp := h.1 i
  have hq := h.2.1 i
  have hqp := h.2.2 i
  constructor
  · by_contra hz
    have hp0 : p i = 0 := by linarith
    have heq : p i = q i := by linarith
    exact (hm.no_common_deterministic hn hind h hgap0 i heq).1 hp0
  · by_contra ho
    have hp1 : p i = 1 := by linarith
    have heq : p i = q i := by linarith
    exact (hm.no_common_deterministic hn hind h hgap0 i heq).2 hp1

theorem IsGapMinimizer.reflection {n : ℕ} {p q : Fin n → ℝ} (hm : IsGapMinimizer p q) :
    IsGapMinimizer (fun i => 1-q i) (fun i => 1-p i) := by
  intro r s h hgap
  rw [meanGap_reflection] at hgap
  have hh := hm _ _ (admissiblePair_reflection h)
    (by rw [meanGap_reflection]; exact hgap)
  simpa only [tailObjective_reflection] using hh

theorem pbTail_at_dimension (n : ℕ) (p : Fin n → ℝ) : pbTail p n = ∏ i, p i := by
  rw [pbTail_eq_sum_mass]
  simp only [Finset.Icc_self, sum_singleton]
  unfold pbMass pbMassOn
  have hs : (univ : Finset (Fin n)).powersetCard n = {Finset.univ} := by
    simpa using powersetCard_self (univ : Finset (Fin n))
  rw [hs]
  simp [bernoulliWeight]

theorem tailObjective_one_left {n : ℕ} (hn : 0 < n) {q : Fin n → ℝ}
    (hq : ValidParameters q) :
    tailObjective (fun _ : Fin n => 1) q = 1 - ∏ i, q i := by
  have hd : tailDiff (fun _ : Fin n => 1) q n = 1 - ∏ i, q i := by
    simp [tailDiff, pbTail_at_dimension]
  apply le_antisymm
  · apply (tailObjective_le_iff _ _ hn _).mpr
    intro k hk
    have hkn := (mem_Icc.mp hk).2
    simp only [tailDiff, pbTail_const_one, if_pos hkn]
    rw [← pbTail_at_dimension n q]
    exact sub_le_sub_left (pbTail_antitone hq hkn) 1
  · rw [← hd]
    exact tailDiff_le_tailObjective _ _ (mem_Icc.mpr ⟨hn,le_rfl⟩)

theorem product_le_mean_pow {n : ℕ} (hn : 0 < n) (q : Fin n → ℝ)
    (hq : ∀ i, 0 ≤ q i) : (∏ i, q i) ≤ ((∑ i, q i) / n)^n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hmean := Real.geom_mean_le_arith_mean_weighted univ
    (fun _ : Fin n => (1 : ℝ)/n) q (fun _ _ => by positivity)
    (by simp [hn0.ne']) (fun i _ => hq i)
  have hp := pow_le_pow_left₀ (prod_nonneg (fun i _ => Real.rpow_nonneg (hq i) _)) hmean n
  rw [← Finset.prod_pow] at hp
  have hpow (i : Fin n) : (q i ^ ((1 : ℝ)/n))^n = q i := by
    rw [← Real.rpow_mul_natCast (hq i), one_div_mul_cancel hn0.ne', Real.rpow_one]
  simp only [hpow] at hp
  have hsum : (∑ i : Fin n, (1 : ℝ)/n * q i) = (∑ i, q i)/n := by
    rw [← mul_sum]
    ring
  rwa [hsum] at hp

theorem benchmark_lt_homogeneous_one_left {n : ℕ} (hn : 2 ≤ n) {b : ℝ}
    (hb0 : 0 < b) (hb1 : b < 1) :
    benchmark n (n * (1-b)) < tailObjective (fun _ : Fin n => 1) (fun _ => b) := by
  have hle := homogeneous_minimum hn hb0.le hb1.le (a := 1) le_rfl
  apply lt_of_le_of_ne hle
  intro he
  have hh := (homogeneous_minimum_eq_iff hn hb0.le (a := 1) le_rfl
    (by linarith) (by linarith)).mp he.symm
  rcases hh with hh | hh <;> exact (lt_irrefl (1 : ℝ)) hh.2.2.1

theorem IsGapMinimizer.upper_ne_one {n : ℕ} (hn : 3 ≤ n) {p q : Fin n → ℝ}
    (h : AdmissiblePair p q) (hm : IsGapMinimizer p q)
    (hgap0 : 0 < meanGap p q) (hgapn : meanGap p q < n) : p ≠ (fun _ => 1) := by
  intro hp
  subst p
  have hn0 : (0 : ℝ) < n := by positivity
  let b := (∑ i, q i) / n
  have hgap : meanGap (fun _ : Fin n => 1) q = n * (1-b) := by
    simp only [meanGap, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    dsimp [b]
    field_simp
  have hb0 : 0 < b := by rw [hgap] at hgapn; nlinarith
  have hb1 : b < 1 := by rw [hgap] at hgap0; nlinarith
  have hprod := product_le_mean_pow (by omega : 0 < n) q (fun i => (h.2.1 i).1)
  have hle : tailObjective (fun _ : Fin n => 1) (fun _ => b) ≤
      tailObjective (fun _ : Fin n => 1) q := by
    rw [tailObjective_one_left (by omega) (fun _ => ⟨hb0.le,hb1.le⟩),
      tailObjective_one_left (by omega) h.2.1]
    simpa only [prod_const, card_univ, Fintype.card_fin] using sub_le_sub_left hprod 1
  have hstrict := benchmark_lt_homogeneous_one_left (by omega : 2 ≤ n) hb0 hb1
  have hmin := hm.le_benchmark (by omega) hgap0 hgapn
  rw [hgap] at hmin
  linarith

theorem IsGapMinimizer.lower_ne_zero {n : ℕ} (hn : 3 ≤ n) {p q : Fin n → ℝ}
    (h : AdmissiblePair p q) (hm : IsGapMinimizer p q)
    (hgap0 : 0 < meanGap p q) (hgapn : meanGap p q < n) : q ≠ (fun _ => 0) := by
  have hh := hm.reflection.upper_ne_one hn (admissiblePair_reflection h)
    (by rwa [meanGap_reflection]) (by rwa [meanGap_reflection])
  intro hq
  apply hh
  simp [hq]

end PoissonBinomialComparison

-- CommonMinimizer
namespace PoissonBinomialComparison

open Finset

noncomputable section

variable {n : ℕ} {p q : Fin n → ℝ}

theorem IsGapMinimizer.not_pure_common_stationarity (hn : 3 ≤ n)
    (hind : ∀ r s : Fin (n-1) → ℝ, AdmissiblePair r s →
      benchmark (n-1) (meanGap r s) ≤ tailObjective r s)
    (h : AdmissiblePair p q) (hm : IsGapMinimizer p q) (hgap : 0 < meanGap p q)
    {k : ℕ} (hk : k ∈ activeThresholds p q) (i : Fin n) (hi : p i = q i)
    (hgrad : randomizedGradient p 1 k i = randomizedGradient q 1 k i)
    (hpos : 0 < randomizedGradient p 1 k i) : False := by
  have hk0 := ((mem_activeThresholds p q k).mp hk).1
  have hmass : pbMassOn p (univ.erase i) (k-1) = pbMassOn q (univ.erase i) (k-1) := by
    simpa [randomizedGradient,randomizedSlopeOn,show k ≠ 0 by omega] using hgrad
  have hmasspos : 0 < pbMassOn q (univ.erase i) (k-1) := by
    rw [hgrad] at hpos
    simpa [randomizedGradient,randomizedSlopeOn,show k ≠ 0 by omega] using hpos
  obtain ⟨r,s,hrs,hgap',hobj⟩ := exists_deleted_pair_of_stationary_active h i hi hk hmass hmasspos
  have hlow := hind r s hrs
  rw [hgap',hobj] at hlow
  have hbound := meanGap_le_dimension hrs
  rw [hgap'] at hbound
  have himprove := dimension_improvement (by omega : 2 ≤ n-1) hgap hbound
  rw [show n-1+1 = n by omega] at himprove
  obtain ⟨r',s',hrs',hg',ht'⟩ := himprove
  have hmin := hm r' s' hrs' hg'
  linarith

theorem common_coordinates_of_kkt (hn : 3 ≤ n)
    (hind : ∀ r s : Fin (n-1) → ℝ, AdmissiblePair r s →
      benchmark (n-1) (meanGap r s) ≤ tailObjective r s)
    (h : AdmissiblePair p q) (hm : IsGapMinimizer p q) (hgap : 0 < meanGap p q)
    (hp : ∀ i, 0 < p i) (hq : ∀ i, q i < 1)
    {k : ℕ} {w c : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hc : 0 < c)
    (hk : k ∈ activeThresholds p q) (hlast : w = 1 ∨ k+1 ∈ activeThresholds p q)
    (hcommon : ∃ i, p i = q i)
    (hgrad : ∀ i, p i = q i → randomizedGradient p w k i = randomizedGradient q w k i ∧
      c ≤ randomizedGradient p w k i) :
    k+1 ∈ activeThresholds p q ∧ 0 < w ∧ w < 1 ∧
      pbMass p k = pbMass q k ∧ 0 < pbMass p k ∧ c ≤ pbMass p k ∧
      ∀ i, p i = q i → p i = w ∧
        randomizedGradient p w k i = pbMass p k ∧ randomizedGradient q w k i = pbMass p k := by
  obtain ⟨i,hi⟩ := hcommon
  have hg := hgrad i hi
  have hpos := hc.trans_le hg.2
  have hwne : w ≠ 1 := by
    intro hw
    subst w
    exact hm.not_pure_common_stationarity hn hind h hgap hk i hi hg.1 hpos
  have hk1 := hlast.resolve_left hwne
  have hk' := (mem_activeThresholds p q k).mp hk
  have hk1' := (mem_activeThresholds p q (k+1)).mp hk1
  have hkn : k < n := by omega
  have hdiff := tailDiff_sub_succ p q k
  rw [hk'.2.2,hk1'.2.2,sub_self] at hdiff
  have htie : pbMass p k = pbMass q k := by linarith
  have hparam (j : Fin n) (hj : p j = q j) : p j = w := by
    have hs : ∃ l, l ≠ j ∧ q l < p l := by
      obtain ⟨l,hl⟩ := exists_strict_coordinate_of_meanGap_pos h hgap
      refine ⟨l,?_,hl⟩
      intro heq
      subst l
      linarith
    exact common_parameter_eq_weight h hp hq hw0 hw1 hk'.1 hkn htie j hj hs
      (hgrad j hj).1 (hc.trans_le (hgrad j hj).2)
  have hiw := hparam i hi
  have hmass := randomizedGradient_eq_mass_of_parameter_eq hk'.1 i hiw
  have hmp : 0 < pbMass p k := by rwa [hmass] at hpos
  have hmc : c ≤ pbMass p k := by simpa only [hmass] using hg.2
  refine ⟨hk1, hiw ▸ hp i, ?_, htie,hmp,hmc,?_⟩
  · rw [← hiw,hi]
    exact hq i
  · intro j hj
    have hjw := hparam j hj
    have hmj := randomizedGradient_eq_mass_of_parameter_eq hk'.1 j hjw
    exact ⟨hjw,hmj, (hgrad j hj).1.symm.trans hmj⟩

end

end PoissonBinomialComparison

-- OneVectorConstant
namespace PoissonBinomialComparison

open Finset

noncomputable section

variable {ι : Type*} [DecidableEq ι]

private theorem valid_update_insert {p : ι → ℝ} {s : Finset ι} {e : ι}
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    ∀ i ∈ insert e s, 0 ≤ Function.update p e w i ∧ Function.update p e w i ≤ 1 := by
  intro i hi
  by_cases hie : i = e
  · subst i
    simpa using And.intro hw0 hw1
  · rw [Function.update_of_ne hie]
    exact hp i ((mem_insert.mp hi).resolve_left hie)

private theorem order_update_insert {p q : ι → ℝ} {s : Finset ι} {e : ι}
    (hpq : ∀ i ∈ s, q i ≤ p i) (w : ℝ) :
    ∀ i ∈ insert e s, Function.update q e w i ≤ Function.update p e w i := by
  intro i hi
  by_cases hie : i = e
  · subst i
    simp
  · rw [Function.update_of_ne hie, Function.update_of_ne hie]
    exact hpq i ((mem_insert.mp hi).resolve_left hie)

theorem randomizedSlopeOn_likelihoodRatio {p q : ι → ℝ} {s : Finset ι} {e : ι}
    (he : e ∉ s) (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1)
    (hq : ∀ i ∈ s, 0 ≤ q i ∧ q i ≤ 1) (hpq : ∀ i ∈ s, q i ≤ p i)
    {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) {a b : ℕ} (hab : a ≤ b) :
    randomizedSlopeOn p s w a * randomizedSlopeOn q s w b ≤
      randomizedSlopeOn p s w b * randomizedSlopeOn q s w a := by
  have h := pbMassIntOn_likelihoodRatio (insert e s)
    (valid_update_insert hq hw0 hw1) (valid_update_insert hp hw0 hw1)
    (order_update_insert hpq w) (a : ℤ) (b : ℤ) (by omega)
  simpa only [pbMassIntOn_natCast, ← randomizedSlopeOn_eq_adjoin p he,
    ← randomizedSlopeOn_eq_adjoin q he] using h

theorem randomizedSlopeOn_strict_adjacent {p q : ι → ℝ} {s : Finset ι} {e : ι}
    (he : e ∉ s) (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1)
    (hq : ∀ i ∈ s, 0 ≤ q i ∧ q i ≤ 1) (hpq : ∀ i ∈ s, q i ≤ p i)
    (hstrict : ∃ i ∈ s, q i < p i)
    {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (k : ℕ)
    (hq0 : 0 < randomizedSlopeOn q s w k)
    (hq1 : 0 < randomizedSlopeOn q s w (k + 1))
    (hp1 : 0 < randomizedSlopeOn p s w (k + 1)) :
    randomizedSlopeOn p s w k * randomizedSlopeOn q s w (k + 1) <
      randomizedSlopeOn p s w (k + 1) * randomizedSlopeOn q s w k := by
  have hs : ∃ i ∈ insert e s, Function.update q e w i < Function.update p e w i := by
    obtain ⟨i, hi, hqi⟩ := hstrict
    have hie : i ≠ e := by intro hh; subst i; exact he hi
    exact ⟨i, mem_insert_of_mem hi, by simpa [Function.update_of_ne hie] using hqi⟩
  have hc : (k : ℤ) + 1 = ((k + 1 : ℕ) : ℤ) := by omega
  have h := pbMassIntOn_strict_adjacent (insert e s)
    (valid_update_insert hq hw0 hw1) (valid_update_insert hp hw0 hw1)
    (order_update_insert hpq w) hs (k : ℤ)
    (by simpa only [pbMassIntOn_natCast, ← randomizedSlopeOn_eq_adjoin q he] using hq0)
    (by simpa only [hc, pbMassIntOn_natCast, ← randomizedSlopeOn_eq_adjoin q he] using hq1)
    (by simpa only [hc, pbMassIntOn_natCast, ← randomizedSlopeOn_eq_adjoin p he] using hp1)
  simpa only [hc, pbMassIntOn_natCast, ← randomizedSlopeOn_eq_adjoin p he,
    ← randomizedSlopeOn_eq_adjoin q he] using h

theorem randomizedSlopeOn_nonneg {p : ι → ℝ} {s : Finset ι}
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) {w : ℝ}
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (k : ℕ) : 0 ≤ randomizedSlopeOn p s w k := by
  unfold randomizedSlopeOn
  apply add_nonneg (mul_nonneg (sub_nonneg.mpr hw1) (pbMassOn_nonneg hp k))
  apply mul_nonneg hw0
  split
  · exact le_rfl
  · exact pbMassOn_nonneg hp (k - 1)

variable {n : ℕ} {p q : Fin n → ℝ}

theorem randomizedMixedCoefficient_nonneg_of_upper_kkt (hp : ValidParameters p)
    {i j : Fin n} {w c : ℝ} {k : ℕ} (hne : p i ≠ p j)
    (hpi : randomizedGradient p w k i ≤ c) (hpj : randomizedGradient p w k j ≤ c)
    (hfi : p i < 1 → randomizedGradient p w k i = c)
    (hfj : p j < 1 → randomizedGradient p w k j = c) :
    0 ≤ randomizedMixedCoefficient p w k i j := by
  have hij : i ≠ j := fun heq ↦ hne (congrArg p heq)
  have hd := randomizedGradient_sub p hij w k
  rcases lt_or_gt_of_ne hne with hijp | hjip
  · have heq := hfi (hijp.trans_le (hp j).2)
    have hprod : 0 ≤ (p j - p i) * randomizedMixedCoefficient p w k i j := by linarith
    exact nonneg_of_mul_nonneg_right hprod (sub_pos.mpr hijp)
  · have heq := hfj (hjip.trans_le (hp i).2)
    have hprod : 0 ≤ (p i - p j) * randomizedMixedCoefficient p w k i j := by nlinarith
    exact nonneg_of_mul_nonneg_right hprod (sub_pos.mpr hjip)

theorem randomizedMixedCoefficient_nonpos_of_lower_kkt (hq : ValidParameters q)
    {i j : Fin n} {w c : ℝ} {k : ℕ} (hne : q i ≠ q j)
    (hqi : randomizedGradient q w k i ≤ c) (hqj : randomizedGradient q w k j ≤ c)
    (hfi : 0 < q i → randomizedGradient q w k i = c)
    (hfj : 0 < q j → randomizedGradient q w k j = c) :
    randomizedMixedCoefficient q w k i j ≤ 0 := by
  have hij : i ≠ j := fun heq ↦ hne (congrArg q heq)
  have hd := randomizedGradient_sub q hij w k
  rcases lt_or_gt_of_ne hne with hijq | hjiq
  · have heq := hfj ((hq i).1.trans_lt hijq)
    have hprod : (q j - q i) * randomizedMixedCoefficient q w k i j ≤ 0 := by linarith
    exact nonpos_of_mul_nonpos_right hprod (sub_pos.mpr hijq)
  · have heq := hfi ((hq j).1.trans_lt hjiq)
    have hprod : (q i - q j) * randomizedMixedCoefficient q w k i j ≤ 0 := by nlinarith
    exact nonpos_of_mul_nonpos_right hprod (sub_pos.mpr hjiq)

theorem randomizedGradient_eq_double_delete (p : Fin n → ℝ) {i j : Fin n}
    (hij : i ≠ j) (w : ℝ) (k : ℕ) :
    randomizedGradient p w k i =
      randomizedSlopeOn p ((univ.erase i).erase j) w k +
        p j * randomizedMixedCoefficient p w k i j := by
  have hs : insert j ((univ.erase i).erase j) = univ.erase i := by
    apply insert_erase
    simp [hij.symm]
  simpa only [hs, randomizedGradient, randomizedMixedCoefficient] using
    randomizedSlopeOn_insert p (notMem_erase j (univ.erase i)) w k

theorem pair_eq_or_eq_of_kkt (h : AdmissiblePair p q) {w c : ℝ}
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hc : 0 < c) {k : ℕ} (hk : 1 ≤ k)
    {i j : Fin n} (hstrict : ∃ t, t ≠ i ∧ t ≠ j ∧ q t < p t)
    (hpi : randomizedGradient p w k i ≤ c) (hpj : randomizedGradient p w k j ≤ c)
    (hq_i : randomizedGradient q w k i ≤ c) (hq_j : randomizedGradient q w k j ≤ c)
    (hfpi : p i < 1 → randomizedGradient p w k i = c)
    (hfpj : p j < 1 → randomizedGradient p w k j = c)
    (hfqi : 0 < q i → randomizedGradient q w k i = c)
    (hfqj : 0 < q j → randomizedGradient q w k j = c) :
    p i = p j ∨ q i = q j := by
  by_contra hnot
  push Not at hnot
  have hij : i ≠ j := fun heq ↦ hnot.1 (congrArg p heq)
  let s := ((univ : Finset (Fin n)).erase i).erase j
  let Ap := randomizedSlopeOn p s w (k - 1)
  let Bp := randomizedSlopeOn p s w k
  let Aq := randomizedSlopeOn q s w (k - 1)
  let Bq := randomizedSlopeOn q s w k
  have hCp := randomizedMixedCoefficient_nonneg_of_upper_kkt h.1 hnot.1 hpi hpj hfpi hfpj
  have hCq := randomizedMixedCoefficient_nonpos_of_lower_kkt h.2.1 hnot.2 hq_i hq_j hfqi hfqj
  have hcp : randomizedMixedCoefficient p w k i j = Ap - Bp := by
    simp [randomizedMixedCoefficient, randomizedCoefficientOn, show k ≠ 0 by omega, Ap, Bp, s]
  have hcq : randomizedMixedCoefficient q w k i j = Aq - Bq := by
    simp [randomizedMixedCoefficient, randomizedCoefficientOn, show k ≠ 0 by omega, Aq, Bq, s]
  rw [hcp] at hCp
  rw [hcq] at hCq
  have hswap : ((univ : Finset (Fin n)).erase j).erase i = s := by
    exact erase_right_comm
  have hGi := randomizedGradient_eq_double_delete p hij w k
  have hGj := randomizedGradient_eq_double_delete p hij.symm w k
  have hQi := randomizedGradient_eq_double_delete q hij w k
  have hQj := randomizedGradient_eq_double_delete q hij.symm w k
  rw [hcp] at hGi
  rw [hcq] at hQi
  have hcp' : randomizedMixedCoefficient p w k j i = Ap - Bp := by
    simpa only [randomizedMixedCoefficient, hswap] using hcp
  have hcq' : randomizedMixedCoefficient q w k j i = Aq - Bq := by
    simpa only [randomizedMixedCoefficient, hswap] using hcq
  rw [hcp', hswap] at hGj
  rw [hcq', hswap] at hQj
  change randomizedGradient p w k i = Bp + p j * (Ap - Bp) at hGi
  change randomizedGradient p w k j = Bp + p i * (Ap - Bp) at hGj
  change randomizedGradient q w k i = Bq + q j * (Aq - Bq) at hQi
  change randomizedGradient q w k j = Bq + q i * (Aq - Bq) at hQj
  have hAp : 0 < Ap := by
    have hbound_i : randomizedGradient p w k i ≤ Ap := by
      have hh := mul_nonneg (sub_nonneg.mpr (h.1 j).2) hCp
      nlinarith
    have hbound_j : randomizedGradient p w k j ≤ Ap := by
      have hh := mul_nonneg (sub_nonneg.mpr (h.1 i).2) hCp
      nlinarith
    rcases lt_or_gt_of_ne hnot.1 with hpij | hpji
    · rw [hfpi (hpij.trans_le (h.1 j).2)] at hbound_i
      exact hc.trans_le hbound_i
    · rw [hfpj (hpji.trans_le (h.1 i).2)] at hbound_j
      exact hc.trans_le hbound_j
  have hBq : 0 < Bq := by
    have hbound_i : randomizedGradient q w k i ≤ Bq := by
      have hh := mul_nonpos_of_nonneg_of_nonpos (h.2.1 j).1 hCq
      linarith
    have hbound_j : randomizedGradient q w k j ≤ Bq := by
      have hh := mul_nonpos_of_nonneg_of_nonpos (h.2.1 i).1 hCq
      linarith
    rcases lt_or_gt_of_ne hnot.2 with hqij | hqji
    · rw [hfqj ((h.2.1 i).1.trans_lt hqij)] at hbound_j
      exact hc.trans_le hbound_j
    · rw [hfqi ((h.2.1 j).1.trans_lt hqji)] at hbound_i
      exact hc.trans_le hbound_i
  have hps : ∀ t ∈ s, 0 ≤ p t ∧ p t ≤ 1 := fun t _ ↦ h.1 t
  have hqs : ∀ t ∈ s, 0 ≤ q t ∧ q t ≤ 1 := fun t _ ↦ h.2.1 t
  have hpqs : ∀ t ∈ s, q t ≤ p t := fun t _ ↦ h.2.2 t
  have hie : i ∉ s := by simp [s]
  have hweak : Ap * Bq ≤ Bp * Aq :=
    randomizedSlopeOn_likelihoodRatio hie hps hqs hpqs hw0 hw1 (by omega)
  have hBpnonneg : 0 ≤ Bp := randomizedSlopeOn_nonneg hps hw0 hw1 k
  have hAqnonneg : 0 ≤ Aq := randomizedSlopeOn_nonneg hqs hw0 hw1 (k - 1)
  have hproduct : 0 < Bp * Aq := (mul_pos hAp hBq).trans_le hweak
  have hBp : 0 < Bp := pos_of_mul_pos_left hproduct hAqnonneg
  have hAq : 0 < Aq := pos_of_mul_pos_right hproduct hBpnonneg
  have hs : ∃ t ∈ s, q t < p t := by
    obtain ⟨t, hti, htj, ht⟩ := hstrict
    exact ⟨t, by simp [s, hti, htj], ht⟩
  have hpred : k - 1 + 1 = k := by omega
  have hlt : Ap * Bq < Bp * Aq := by
    have hh := randomizedSlopeOn_strict_adjacent hie hps hqs hpqs hs hw0 hw1 (k - 1)
      hAq (by simpa only [hpred] using hBq) (by simpa only [hpred] using hBp)
    simpa only [hpred] using hh
  have hreverse : Bp * Aq ≤ Ap * Bq := by
    calc
      Bp * Aq ≤ Ap * Aq := mul_le_mul_of_nonneg_right (by linarith) hAq.le
      _ ≤ Ap * Bq := mul_le_mul_of_nonneg_left (by linarith) hAp.le
  exact not_lt_of_ge hreverse hlt

theorem constant_on_or_constant_on_of_pairwise {α : Type*} (s : Finset α)
    (f g : α → ℝ)
    (hpair : ∀ i ∈ s, ∀ j ∈ s, f i = f j ∨ g i = g j) :
    (∃ a, ∀ i ∈ s, f i = a) ∨ (∃ b, ∀ i ∈ s, g i = b) := by
  by_cases hf : ∀ i ∈ s, ∀ j ∈ s, f i = f j
  · left
    by_cases hs : s.Nonempty
    · obtain ⟨j, hj⟩ := hs
      exact ⟨f j, fun i hi ↦ hf i hi j hj⟩
    · exact ⟨0, fun i hi ↦ False.elim (hs ⟨i, hi⟩)⟩
  · push Not at hf
    obtain ⟨i, hi, j, hj, hij⟩ := hf
    have hgij : g i = g j := (hpair i hi j hj).resolve_left hij
    right
    refine ⟨g i, ?_⟩
    intro t ht
    by_cases hti : f t = f i
    · have htj : f t ≠ f j := by intro heq; exact hij (hti.symm.trans heq)
      exact ((hpair t ht j hj).resolve_left htj).trans hgij.symm
    · exact (hpair t ht i hi).resolve_left hti

theorem exists_constant_vector_of_kkt (h : AdmissiblePair p q) {I : Finset (Fin n)}
    (hcard : 3 ≤ I.card) (hchanging : ∀ i ∈ I, q i < p i)
    {w c : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hc : 0 < c) {k : ℕ} (hk : 1 ≤ k)
    (hupper : ∀ i ∈ I, randomizedGradient p w k i ≤ c ∧
      (p i < 1 → randomizedGradient p w k i = c))
    (hlower : ∀ i ∈ I, randomizedGradient q w k i ≤ c ∧
      (0 < q i → randomizedGradient q w k i = c)) :
    (∃ a, ∀ i ∈ I, p i = a) ∨ (∃ b, ∀ i ∈ I, q i = b) := by
  apply constant_on_or_constant_on_of_pairwise I p q
  intro i hi j hj
  have hpaircard : ({i, j} : Finset (Fin n)).card < I.card := by
    have hle := card_insert_le i ({j} : Finset (Fin n))
    simp only [card_singleton] at hle
    omega
  obtain ⟨t, ht, htpair⟩ := exists_mem_notMem_of_card_lt_card hpaircard
  have hti : t ≠ i := by intro heq; subst t; exact htpair (by simp)
  have htj : t ≠ j := by intro heq; subst t; exact htpair (by simp)
  exact pair_eq_or_eq_of_kkt h hw0 hw1 hc hk
    ⟨t, hti, htj, hchanging t ht⟩
    (hupper i hi).1 (hupper j hj).1 (hlower i hi).1 (hlower j hj).1
    (hupper i hi).2 (hupper j hj).2 (hlower i hi).2 (hlower j hj).2

end

end PoissonBinomialComparison

-- UpperInterior
namespace PoissonBinomialComparison

open Finset

variable {ι : Type*} [DecidableEq ι]

theorem pbMassIntOn_union_zero_parameters (p : ι → ℝ) (s t : Finset ι)
    (hz : ∀ i ∈ t, i ∉ s → p i = 0) (k : ℤ) :
    pbMassIntOn p (s ∪ t) k = pbMassIntOn p s k := by
  induction t using Finset.induction_on with
  | empty => simp
  | @insert i t hi ih =>
    have hz' : ∀ j ∈ t, j ∉ s → p j = 0 := fun j hj => hz j (mem_insert_of_mem hj)
    rw [union_insert]
    by_cases him : i ∈ s ∪ t
    · rw [insert_eq_of_mem him, ih hz']
    · rw [pbMassIntOn_insert p him, hz i (mem_insert_self i t)
        (fun hs => him (mem_union_left t hs))]
      simpa using ih hz'

theorem pbMassIntOn_univ_lt_of_two_positive {n : ℕ} {p : Fin n → ℝ}
    (hp : ValidParameters p) (s : Finset (Fin n)) {i j : Fin n}
    (hi : i ∉ s) (hj : j ∉ s) (hij : i ≠ j)
    (hpi : 0 < p i) (hpj : 0 < p j) (k : ℤ)
    (hk : 0 < pbMassIntOn p s k)
    (hadj : pbMassIntOn p s (k-1) ≤ pbMassIntOn p s k) :
    pbMassIntOn p univ k < pbMassIntOn p s k := by
  have hU (t : Finset (Fin n)) : t ∪ univ = univ := union_eq_right.mpr (subset_univ t)
  rcases hadj.eq_or_lt with heq | hlt
  · simpa only [hU] using pbMassIntOn_union_lt_of_two_positive_of_tie s univ hi hj hij
      (fun l _ => hp l) hpi hpj k hk heq
  · have hstrict := pbMassIntOn_insert_lt hi hpi k hlt
    have hprefix := (pbMassIntOn_cross s (fun l _ => hp l)).prefix_order
      (pbMassIntOn_nonneg (fun l _ => hp l)) hk hadj
    have hprefix' := pbMassIntOn_insert_prefix_order hi (hp i) k hprefix
    have hle := (pbMassIntOn_union_prefix_order (insert i s) univ
      (fun l _ => hp l) k hprefix').1
    simp only [hU] at hle
    exact hle.trans_lt hstrict

theorem pbMass_lt_of_upper_one_block {n k : ℕ} {p q : Fin n → ℝ}
    (h : AdmissiblePair p q) (hk : k < n) (s : Finset (Fin n))
    (hcommon : ∀ i ∈ s, p i = q i) (hone : ∀ i ∉ s, p i = 1)
    {i j : Fin n} (hi : i ∉ s) (hj : j ∉ s) (hij : i ≠ j)
    (hqi : q i < 1) (hqj : q j < 1) (hpos : 0 < pbMass p k)
    (hadj : pbMass p (k+1) ≤ pbMass p k) : pbMass q k < pbMass p k := by
  let P : Fin n → ℝ := fun l => 1-p l
  let Q : Fin n → ℝ := fun l => 1-q l
  have hQ : ValidParameters Q := fun l => ⟨sub_nonneg.mpr (h.2.1 l).2,
    by dsimp [Q]; linarith [(h.2.1 l).1]⟩
  have hbase (z : ℤ) : pbMassIntOn Q s z = pbMassIntOn P univ z := by
    rw [pbMassIntOn_congr (q := P) (fun l hl => by dsimp [P,Q]; rw [hcommon l hl])]
    have hz : ∀ l ∈ (univ : Finset (Fin n)), l ∉ s → P l = 0 := by
      intro l _ hl
      simp [P,hone l hl]
    simpa only [union_eq_right.mpr (subset_univ s)] using (pbMassIntOn_union_zero_parameters P s univ hz z).symm
  have href (l : ℕ) (hl : l ≤ n) : pbMassIntOn P univ (n-l : ℕ) = pbMass p l := by
    simp only [pbMassIntOn_natCast]
    change pbMass (fun l => 1-p l) (n-l) = _
    rw [pbMass_complement p (n-l) (by omega), Nat.sub_sub_self hl]
  have hcount : ((n-k : ℕ) : ℤ)-1 = ((n-(k+1) : ℕ) : ℤ) := by omega
  have hbasepos : 0 < pbMassIntOn Q s (n-k : ℕ) := by rw [hbase,href k hk.le]; exact hpos
  have hbaseadj : pbMassIntOn Q s (((n-k : ℕ) : ℤ)-1) ≤ pbMassIntOn Q s (n-k : ℕ) := by
    rw [hcount,hbase,hbase,href (k+1) (by omega),href k hk.le]
    exact hadj
  have hlt := pbMassIntOn_univ_lt_of_two_positive hQ s hi hj hij
    (show 0 < Q i from sub_pos.mpr hqi) (show 0 < Q j from sub_pos.mpr hqj)
    (n-k : ℕ) hbasepos hbaseadj
  rw [hbase,href k hk.le,pbMassIntOn_natCast] at hlt
  change pbMass (fun l => 1-q l) (n-k) < _ at hlt
  rwa [pbMass_complement q (n-k) (by omega),Nat.sub_sub_self hk.le] at hlt

theorem randomizedGradient_of_parameter_one {n k : ℕ} {p : Fin n → ℝ}
    (hk : 1 ≤ k) (j : Fin n) (hj : p j = 1) (w : ℝ) :
    randomizedGradient p w k j = w * pbMass p k + (1-w) * pbMass p (k+1) := by
  have h0 := pbMass_delete_succ p j (k-1)
  have h1 := pbMass_delete_succ p j k
  simp only [hj, sub_self, zero_mul, one_mul, zero_add, show k-1+1 = k by omega] at h0 h1
  simp only [randomizedGradient,randomizedSlopeOn,show k ≠ 0 by omega,ite_false]
  rw [h0,h1]
  ring

theorem upper_adjacent_le_of_gradient_order {n k : ℕ} {p : Fin n → ℝ}
    (hk : 1 ≤ k) {w : ℝ} (hw : w < 1) (i j : Fin n)
    (hi : p i = w) (hj : p j = 1)
    (hgrad : randomizedGradient p w k j ≤ randomizedGradient p w k i) :
    pbMass p (k+1) ≤ pbMass p k := by
  rw [randomizedGradient_eq_mass_of_parameter_eq hk i hi,
    randomizedGradient_of_parameter_one hk j hj] at hgrad
  nlinarith

theorem upper_one_block_impossible {n k : ℕ} {p q : Fin n → ℝ}
    (h : AdmissiblePair p q) (hk0 : 1 ≤ k) (hkn : k < n)
    (s : Finset (Fin n)) (hcommon : ∀ i ∈ s, p i = q i)
    (hone : ∀ i ∉ s, p i = 1) {w : ℝ} (hw : w < 1)
    (c i j : Fin n) (hc : p c = w) (hi : i ∉ s) (hj : j ∉ s) (hij : i ≠ j)
    (hqi : q i < 1) (hqj : q j < 1) (hpos : 0 < pbMass p k)
    (hgrad : randomizedGradient p w k i ≤ randomizedGradient p w k c)
    (htie : pbMass p k = pbMass q k) : False := by
  have hadj := upper_adjacent_le_of_gradient_order hk0 hw c i hc (hone i hi) hgrad
  have hlt := pbMass_lt_of_upper_one_block h hkn s hcommon hone hi hj hij hqi hqj hpos hadj
  rw [htie] at hlt
  exact (lt_irrefl _) hlt

theorem homogeneous_upper_changing_lt_one {n k : ℕ} {p q : Fin n → ℝ}
    (h : AdmissiblePair p q) (hk0 : 1 ≤ k) (hkn : k < n)
    (hcard : 2 ≤ (positiveGapCoordinates p q).card) {a w : ℝ} (hw : w < 1)
    (hconst : ∀ i, q i < p i → p i = a)
    (hcommon : ∀ i, p i = q i → p i = w)
    (hnotone : p ≠ (fun _ => 1)) (hpos : 0 < pbMass p k)
    (hgrad : ∀ i c, q i < p i → p c = q c →
      randomizedGradient p w k i ≤ randomizedGradient p w k c)
    (htie : pbMass p k = pbMass q k) : a < 1 := by
  obtain ⟨i,hi,j,hj,hij⟩ := one_lt_card.mp (show 1 < (positiveGapCoordinates p q).card by omega)
  have hi' : q i < p i := (mem_filter.mp hi).2
  have hj' : q j < p j := (mem_filter.mp hj).2
  have ha : a ≤ 1 := by rw [← hconst i hi']; exact (h.1 i).2
  by_contra hlt
  have ha1 : a = 1 := by linarith
  have hex : ∃ c, p c ≠ 1 := by
    by_contra hh
    push Not at hh
    exact hnotone (funext hh)
  obtain ⟨c,hc⟩ := hex
  have hccommon : p c = q c := by
    by_contra hcne
    have hcstrict : q c < p c := lt_of_le_of_ne (h.2.2 c) (Ne.symm hcne)
    exact hc ((hconst c hcstrict).trans ha1)
  let s := (univ : Finset (Fin n)).filter (fun l => p l = q l)
  have hsc : ∀ l ∈ s, p l = q l := fun l hl => (mem_filter.mp hl).2
  have hsone : ∀ l ∉ s, p l = 1 := by
    intro l hl
    have hne : p l ≠ q l := by simpa [s] using hl
    exact (hconst l (lt_of_le_of_ne (h.2.2 l) hne.symm)).trans ha1
  have his : i ∉ s := by simp [s,ne_of_gt hi']
  have hjs : j ∉ s := by simp [s,ne_of_gt hj']
  exact upper_one_block_impossible h hk0 hkn s hsc hsone hw c i j
    (hcommon c hccommon) his hjs hij (by rw [← ha1,← hconst i hi']; exact hi')
    (by rw [← ha1,← hconst j hj']; exact hj') hpos (hgrad i c hi' hccommon) htie

end PoissonBinomialComparison

-- MinimizerHomogeneitySetup
namespace PoissonBinomialComparison

open Finset

noncomputable section

variable {n : ℕ} {p q : Fin n → ℝ}

theorem IsGapMinimizer.one_changing_vector_constant (hn : 3 ≤ n)
    (hind : ∀ r s : Fin (n-1) → ℝ, AdmissiblePair r s →
      benchmark (n-1) (meanGap r s) ≤ tailObjective r s)
    (h : AdmissiblePair p q) (hm : IsGapMinimizer p q)
    (hg0 : 0 < meanGap p q) (hgn : meanGap p q < n) :
    (∃ a : ℝ, ∀ i, q i < p i → p i = a) ∨
      (∃ b : ℝ, ∀ i, q i < p i → q i = b) := by
  have hb := hm.parameter_bounds hn hind h hg0
  obtain ⟨k,w,c,_,_,hw0,hw1,hc,_,_,_,hchanging,_⟩ :=
    exists_tail_kkt h (fun i ↦ (hb i).1) (fun i ↦ (hb i).2) hg0
      (hm.tailObjective_lt_one hn hg0 hgn) hm.isLocalMinOn
  have hcard := hm.three_le_positiveGapCoordinates hn h hg0 hgn
  have hI : ∀ i ∈ positiveGapCoordinates p q, q i < p i := fun i hi ↦ (mem_filter.mp hi).2
  have hcst := exists_constant_vector_of_kkt h hcard hI hw0 hw1 hc
    (by assumption)
    (fun i hi ↦ ⟨(hchanging i (hI i hi)).1,(hchanging i (hI i hi)).2.2.1⟩)
    (fun i hi ↦ ⟨(hchanging i (hI i hi)).2.1,(hchanging i (hI i hi)).2.2.2⟩)
  simpa [positiveGapCoordinates] using hcst

theorem IsGapMinimizer.upper_changing_constant_interior (hn : 3 ≤ n)
    (hind : ∀ r s : Fin (n-1) → ℝ, AdmissiblePair r s →
      benchmark (n-1) (meanGap r s) ≤ tailObjective r s)
    (h : AdmissiblePair p q) (hm : IsGapMinimizer p q)
    (hg0 : 0 < meanGap p q) (hgn : meanGap p q < n)
    {a : ℝ} (hconst : ∀ i, q i < p i → p i = a) : 0 < a ∧ a < 1 := by
  obtain ⟨i,hi⟩ := exists_strict_coordinate_of_meanGap_pos h hg0
  have hb := hm.parameter_bounds hn hind h hg0
  have ha0 : 0 < a := hconst i hi ▸ (hb i).1
  have ha1 : a ≤ 1 := hconst i hi ▸ (h.1 i).2
  refine ⟨ha0,?_⟩
  by_cases hcommon : ∃ j, p j = q j
  · obtain ⟨k,w,c,hk0,hkn,hw0,hw1,hc,hk,hlast,_,hchanging,hcommonGrad⟩ :=
      exists_tail_kkt h (fun i ↦ (hb i).1) (fun i ↦ (hb i).2) hg0
        (hm.tailObjective_lt_one hn hg0 hgn) hm.isLocalMinOn
    have hgrad : ∀ j, p j = q j → randomizedGradient p w k j = randomizedGradient q w k j ∧
        c ≤ randomizedGradient p w k j := by
      intro j hj
      obtain ⟨ν,hν,hP,hQ⟩ := hcommonGrad j hj
      exact ⟨hP.trans hQ.symm,by linarith⟩
    obtain ⟨hk1,_,hwlt,htie,hpos,_,hparams⟩ := common_coordinates_of_kkt hn hind h hm hg0
      (fun i ↦ (hb i).1) (fun i ↦ (hb i).2) hw0 hw1 hc hk hlast hcommon hgrad
    have hk1n := ((mem_activeThresholds p q (k+1)).mp hk1).2.1
    exact homogeneous_upper_changing_lt_one h hk0 (by omega)
      (by have := hm.three_le_positiveGapCoordinates hn h hg0 hgn; omega) hwlt hconst
      (fun j hj ↦ (hparams j hj).1) (hm.upper_ne_one hn h hg0 hgn) hpos
      (fun j l hj hl ↦ (hchanging j hj).1.trans (hgrad l hl).2) htie
  · apply lt_of_le_of_ne ha1
    intro ha
    apply hm.upper_ne_one hn h hg0 hgn
    funext j
    have hj : q j < p j := lt_of_le_of_ne (h.2.2 j) (by
      intro heq
      exact hcommon ⟨j,heq.symm⟩)
    exact (hconst j hj).trans ha

theorem IsGapMinimizer.lower_changing_constant_interior (hn : 3 ≤ n)
    (hind : ∀ r s : Fin (n-1) → ℝ, AdmissiblePair r s →
      benchmark (n-1) (meanGap r s) ≤ tailObjective r s)
    (h : AdmissiblePair p q) (hm : IsGapMinimizer p q)
    (hg0 : 0 < meanGap p q) (hgn : meanGap p q < n)
    {b : ℝ} (hconst : ∀ i, q i < p i → q i = b) : 0 < b ∧ b < 1 := by
  have hh := hm.reflection.upper_changing_constant_interior hn hind (admissiblePair_reflection h)
    (by simpa only [meanGap_reflection] using hg0)
    (by simpa only [meanGap_reflection] using hgn)
    (a := 1-b) (by
      intro i hi
      have hqi : q i < p i := by linarith
      simp only [hconst i hqi])
  constructor <;> linarith [hh.1,hh.2]

end

end PoissonBinomialComparison

-- HomogeneousBlockMode
namespace PoissonBinomialComparison

open scoped BigOperators
open Finset

noncomputable section

variable {ι : Type*} [DecidableEq ι]

theorem homogeneousBlockMass_exists_pos {p : ι → ℝ} {s : Finset ι}
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) (M : ℕ) {t : ℝ}
    (ht : 0 ≤ t ∧ t ≤ 1) : ∃ k, 0 < homogeneousBlockMass p s M t k := by
  induction M with
  | zero => exact pbMassIntOn_exists_pos s hp
  | succ M ih =>
    exact bernoulliConvolve_exists_pos (homogeneousBlockMass_nonneg hp M ht) ih ht.1 ht.2

private theorem homogeneousBlockMass_succ_pos_iff {p : ι → ℝ} {s : Finset ι}
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) (M : ℕ) {t : ℝ}
    (ht : 0 < t ∧ t < 1) (k : ℤ) :
    0 < homogeneousBlockMass p s (M + 1) t k ↔
      0 < homogeneousBlockMass p s M t k ∨ 0 < homogeneousBlockMass p s M t (k - 1) := by
  have h0 := homogeneousBlockMass_nonneg hp M ⟨ht.1.le, ht.2.le⟩ k
  have h1 := homogeneousBlockMass_nonneg hp M ⟨ht.1.le, ht.2.le⟩ (k - 1)
  rw [homogeneousBlockMass_succ]
  constructor
  · intro h
    by_contra hn
    push Not at hn
    have hz0 := le_antisymm hn.1 h0
    have hz1 := le_antisymm hn.2 h1
    simp [hz0, hz1] at h
  · rintro (h | h)
    · exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr ht.2) h) (mul_nonneg ht.1.le h1)
    · exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr ht.2.le) h0) (mul_pos ht.1 h)

theorem homogeneousBlockMass_pos_iff {p : ι → ℝ} {s : Finset ι}
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) (M : ℕ) {a b : ℝ}
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (k : ℤ) :
    0 < homogeneousBlockMass p s M a k ↔ 0 < homogeneousBlockMass p s M b k := by
  induction M generalizing k with
  | zero => rfl
  | succ M ih =>
    rw [homogeneousBlockMass_succ_pos_iff hp M ha,
      homogeneousBlockMass_succ_pos_iff hp M hb, ih k, ih (k - 1)]

theorem homogeneousBlockMass_likelihoodRatio {p : ι → ℝ} {s : Finset ι}
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) (M : ℕ) {a b : ℝ}
    (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1) (hab : a ≤ b) :
    LikelihoodRatioLE (homogeneousBlockMass p s M a) (homogeneousBlockMass p s M b) := by
  induction M with
  | zero => exact LikelihoodRatioLE.refl _
  | succ M ih =>
    exact (ih.convolve ha.1 ha.2).trans
      (bernoulliConvolve_likelihoodRatio (homogeneousBlockMass_cross hp M hb) hab)
      (homogeneousBlockMass_nonneg hp (M + 1) ha)
      (homogeneousBlockMass_nonneg hp (M + 1) hb)
      (bernoulliConvolve_exists_pos (homogeneousBlockMass_nonneg hp M hb)
        (homogeneousBlockMass_exists_pos hp M hb) ha.1 ha.2)

theorem homogeneousBlockMass_strict_adjacent {p : ι → ℝ} {s : Finset ι}
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) (M : ℕ) {a b : ℝ}
    (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1) (hab : a < b) (k : ℤ)
    (ha0 : 0 < homogeneousBlockMass p s (M + 1) a k)
    (ha1 : 0 < homogeneousBlockMass p s (M + 1) a (k + 1))
    (hb1 : 0 < homogeneousBlockMass p s (M + 1) b (k + 1)) :
    homogeneousBlockMass p s (M + 1) b k * homogeneousBlockMass p s (M + 1) a (k + 1) <
      homogeneousBlockMass p s (M + 1) b (k + 1) * homogeneousBlockMass p s (M + 1) a k := by
  have hstep := bernoulliConvolve_strict_adjacent
    (homogeneousBlockMass_nonneg hp M ha) (homogeneousBlockMass_cross hp M ha)
    (homogeneousBlockMass_strictLogConcavity hp M ha) ha.1 ha.2 hab k ha0 ha1
  have hrest := (homogeneousBlockMass_likelihoodRatio hp M ha hb hab.le).convolve hb.1 hb.2
  exact hrest.strict_adjacent_trans (homogeneousBlockMass_nonneg hp (M + 1) ha)
    (bernoulliConvolve_nonneg (homogeneousBlockMass_nonneg hp M ha) hb.1 hb.2) k hstep hb1

theorem homogeneousBlockMass_adjacent_sign_mono {p : ι → ℝ} {s : Finset ι}
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) (M : ℕ) {a b : ℝ}
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hab : a ≤ b) (k : ℤ)
    (hadj : homogeneousBlockMass p s M a (k - 1) ≤ homogeneousBlockMass p s M a k) :
    homogeneousBlockMass p s M b (k - 1) ≤ homogeneousBlockMass p s M b k := by
  by_cases hpos : 0 < homogeneousBlockMass p s M a k
  · have hlr := homogeneousBlockMass_likelihoodRatio hp M ⟨ha.1.le, ha.2.le⟩
      ⟨hb.1.le, hb.2.le⟩ hab (k - 1) k (by omega)
    have hmul := mul_le_mul_of_nonneg_left hadj
      (homogeneousBlockMass_nonneg hp M ⟨hb.1.le, hb.2.le⟩ k)
    exact (mul_le_mul_iff_left₀ hpos).mp (hlr.trans hmul)
  · have hzero : homogeneousBlockMass p s M a k = 0 :=
      le_antisymm (le_of_not_gt hpos) (homogeneousBlockMass_nonneg hp M ⟨ha.1.le, ha.2.le⟩ k)
    have hprev : ¬0 < homogeneousBlockMass p s M a (k - 1) := by rw [hzero] at hadj; exact not_lt.mpr hadj
    have hprevb : ¬0 < homogeneousBlockMass p s M b (k - 1) :=
      fun hh ↦ hprev ((homogeneousBlockMass_pos_iff hp M ha hb (k - 1)).mpr hh)
    exact (le_of_not_gt hprevb).trans (homogeneousBlockMass_nonneg hp M ⟨hb.1.le, hb.2.le⟩ k)

theorem homogeneousBlockMass_deriv_nonpos_mono {p : ι → ℝ} {s : Finset ι}
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) (M : ℕ) {a b : ℝ}
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hab : a ≤ b) (k : ℤ)
    (hd : deriv (fun t ↦ homogeneousBlockMass p s M t k) a ≤ 0) :
    deriv (fun t ↦ homogeneousBlockMass p s M t k) b ≤ 0 := by
  cases M with
  | zero => simp
  | succ M =>
    rw [deriv_homogeneousBlockMass_succ] at hd ⊢
    have hM : (0 : ℝ) < (M + 1 : ℕ) := by exact_mod_cast Nat.succ_pos M
    have hadj : homogeneousBlockMass p s M a (k - 1) ≤ homogeneousBlockMass p s M a k := by
      nlinarith
    exact mul_nonpos_of_nonneg_of_nonpos hM.le
      (sub_nonpos.mpr (homogeneousBlockMass_adjacent_sign_mono hp M ha hb hab k hadj))

private theorem homogeneousBlockMass_deleted_tie {p : ι → ℝ} {s : Finset ι}
    (M : ℕ) (u : ℝ) (k : ℤ)
    (hpos : 0 < homogeneousBlockMass p s (M + 1) u k)
    (hd : deriv (fun t ↦ homogeneousBlockMass p s (M + 1) t k) u = 0) :
    homogeneousBlockMass p s M u (k - 1) = homogeneousBlockMass p s M u k ∧
      0 < homogeneousBlockMass p s M u k := by
  rw [deriv_homogeneousBlockMass_succ] at hd
  have hM : (M + 1 : ℝ) ≠ 0 := by positivity
  have heq : homogeneousBlockMass p s M u (k - 1) = homogeneousBlockMass p s M u k := by
    have hz := (mul_eq_zero.mp hd).resolve_left (by exact_mod_cast hM)
    exact sub_eq_zero.mp hz
  refine ⟨heq, ?_⟩
  rw [homogeneousBlockMass_succ, heq] at hpos
  nlinarith

theorem homogeneousBlockMass_deriv_neg_after_critical {p : ι → ℝ} {s : Finset ι}
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) (M : ℕ) {u t : ℝ}
    (hu : 0 < u ∧ u < 1) (ht : u < t ∧ t < 1) (k : ℤ)
    (hpos : 0 < homogeneousBlockMass p s (M + 2) u k)
    (hd : deriv (fun v ↦ homogeneousBlockMass p s (M + 2) v k) u = 0) :
    deriv (fun v ↦ homogeneousBlockMass p s (M + 2) v k) t < 0 := by
  obtain ⟨heq, hupper⟩ := homogeneousBlockMass_deleted_tie (M + 1) u k hpos hd
  have ht' : 0 < t ∧ t < 1 := ⟨hu.1.trans ht.1, ht.2⟩
  have hnew := (homogeneousBlockMass_pos_iff hp (M + 1) hu ht' k).mp hupper
  have hstrict := homogeneousBlockMass_strict_adjacent hp M ⟨hu.1.le, hu.2.le⟩
    ⟨ht'.1.le, ht'.2.le⟩ ht.1 (k - 1) (by rw [heq]; exact hupper)
    (by simpa using hupper) (by simpa using hnew)
  simp only [sub_add_cancel, heq] at hstrict
  have hadj := (mul_lt_mul_iff_left₀ hupper).mp hstrict
  rw [show M + 2 = (M + 1) + 1 by omega, deriv_homogeneousBlockMass_succ]
  exact mul_neg_of_pos_of_neg (by positivity) (sub_neg.mpr hadj)

theorem homogeneousBlockMass_deriv_pos_before_critical {p : ι → ℝ} {s : Finset ι}
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) (M : ℕ) {u t : ℝ}
    (hu : 0 < u ∧ u < 1) (ht : 0 < t ∧ t < u) (k : ℤ)
    (hpos : 0 < homogeneousBlockMass p s (M + 2) u k)
    (hd : deriv (fun v ↦ homogeneousBlockMass p s (M + 2) v k) u = 0) :
    0 < deriv (fun v ↦ homogeneousBlockMass p s (M + 2) v k) t := by
  obtain ⟨heq, hupper⟩ := homogeneousBlockMass_deleted_tie (M + 1) u k hpos hd
  have ht' : 0 < t ∧ t < 1 := ⟨ht.1, ht.2.trans hu.2⟩
  have htupper := (homogeneousBlockMass_pos_iff hp (M + 1) hu ht' k).mp hupper
  have htlower := (homogeneousBlockMass_pos_iff hp (M + 1) hu ht' (k - 1)).mp
    (by rw [heq]; exact hupper)
  have hstrict := homogeneousBlockMass_strict_adjacent hp M ⟨ht'.1.le, ht'.2.le⟩
    ⟨hu.1.le, hu.2.le⟩ ht.2 (k - 1) htlower
    (by simpa using htupper) (by simpa using hupper)
  simp only [sub_add_cancel, heq] at hstrict
  have hadj := (mul_lt_mul_iff_right₀ hupper).mp hstrict
  rw [show M + 2 = (M + 1) + 1 by omega, deriv_homogeneousBlockMass_succ]
  exact mul_pos (by positivity) (sub_pos.mpr hadj)

theorem homogeneousBlockMass_one_eq_of_deriv_eq_zero (p : ι → ℝ) (s : Finset ι)
    (u t : ℝ) (k : ℤ)
    (hd : deriv (fun v ↦ homogeneousBlockMass p s 1 v k) u = 0) :
    homogeneousBlockMass p s 1 t k = homogeneousBlockMass p s 1 u k := by
  rw [deriv_homogeneousBlockMass_succ] at hd
  norm_num only [homogeneousBlockMass_zero, Nat.zero_add, Nat.cast_one, one_mul] at hd
  have heq := sub_eq_zero.mp hd
  simp only [homogeneousBlockMass_succ, homogeneousBlockMass_zero, heq]
  ring

theorem homogeneousBlockMass_lt_of_critical {p : ι → ℝ} {s : Finset ι}
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) (M : ℕ) {u t : ℝ}
    (hu : 0 < u ∧ u < 1) (ht : 0 ≤ t ∧ t ≤ 1) (htu : t ≠ u) (k : ℤ)
    (hpos : 0 < homogeneousBlockMass p s (M + 2) u k)
    (hd : deriv (fun v ↦ homogeneousBlockMass p s (M + 2) v k) u = 0) :
    homogeneousBlockMass p s (M + 2) t k < homogeneousBlockMass p s (M + 2) u k := by
  have hdiff : Differentiable ℝ (fun v ↦ homogeneousBlockMass p s (M + 2) v k) :=
    fun v ↦ (hasDerivAt_homogeneousBlockMass p s (M + 2) v k).differentiableAt
  have hcont := hdiff.continuous
  rcases lt_or_gt_of_ne htu with htu | hut
  · have hmono : StrictMonoOn (fun v ↦ homogeneousBlockMass p s (M + 2) v k)
        (Set.Icc 0 u) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc 0 u) hcont.continuousOn
      intro x hx
      rw [interior_Icc] at hx
      exact homogeneousBlockMass_deriv_pos_before_critical hp M hu hx k hpos hd
    exact hmono ⟨ht.1, htu.le⟩ ⟨hu.1.le, le_rfl⟩ htu
  · have hanti : StrictAntiOn (fun v ↦ homogeneousBlockMass p s (M + 2) v k)
        (Set.Icc u 1) := by
      apply strictAntiOn_of_deriv_neg (convex_Icc u 1) hcont.continuousOn
      intro x hx
      rw [interior_Icc] at hx
      exact homogeneousBlockMass_deriv_neg_after_critical hp M hu hx k hpos hd
    exact hanti ⟨le_rfl, hu.2.le⟩ ⟨hut.le, ht.2⟩ hut

theorem homogeneousBlockMass_le_of_critical {p : ι → ℝ} {s : Finset ι}
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) (M : ℕ) {u t : ℝ}
    (hu : 0 < u ∧ u < 1) (ht : 0 ≤ t ∧ t ≤ 1) (k : ℤ)
    (hpos : 0 < homogeneousBlockMass p s M u k)
    (hd : deriv (fun v ↦ homogeneousBlockMass p s M v k) u = 0) :
    homogeneousBlockMass p s M t k ≤ homogeneousBlockMass p s M u k := by
  cases M with
  | zero => simp
  | succ M =>
    cases M with
    | zero => exact (homogeneousBlockMass_one_eq_of_deriv_eq_zero p s u t k hd).le
    | succ M =>
      by_cases htu : t = u
      · simp [htu]
      · exact (homogeneousBlockMass_lt_of_critical hp M hu ht htu k hpos hd).le

theorem homogeneousBlockMass_exists_critical_between {p : ι → ℝ} {s : Finset ι}
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) (M : ℕ) {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b < 1) (k : ℤ)
    (hpos : 0 < homogeneousBlockMass p s M a k)
    (heq : homogeneousBlockMass p s M a k = homogeneousBlockMass p s M b k) :
    ∃ u, a < u ∧ u < b ∧ 0 < homogeneousBlockMass p s M u k ∧
      deriv (fun v ↦ homogeneousBlockMass p s M v k) u = 0 := by
  have hdiff : Differentiable ℝ (fun v ↦ homogeneousBlockMass p s M v k) :=
    fun v ↦ (hasDerivAt_homogeneousBlockMass p s M v k).differentiableAt
  obtain ⟨u, hu, hd⟩ := exists_deriv_eq_zero hab hdiff.continuous.continuousOn heq
  exact ⟨u, hu.1, hu.2, (homogeneousBlockMass_pos_iff hp M
    ⟨ha, hab.trans hb⟩ ⟨ha.trans hu.1, hu.2.trans hb⟩ k).mp hpos, hd⟩

theorem homogeneousBlockMass_exists_unique_critical_of_eq {p : ι → ℝ} {s : Finset ι}
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) (M : ℕ) {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b < 1) (k : ℤ)
    (hpos : 0 < homogeneousBlockMass p s (M + 2) a k)
    (heq : homogeneousBlockMass p s (M + 2) a k = homogeneousBlockMass p s (M + 2) b k) :
    ∃! u, a < u ∧ u < b ∧ deriv (fun v ↦ homogeneousBlockMass p s (M + 2) v k) u = 0 := by
  obtain ⟨u, hau, hub, hupos, hdu⟩ :=
    homogeneousBlockMass_exists_critical_between hp (M + 2) ha hab hb k hpos heq
  refine ⟨u, ⟨hau, hub, hdu⟩, ?_⟩
  rintro y ⟨hay, hyb, hdy⟩
  have hu : 0 < u ∧ u < 1 := ⟨ha.trans hau, hub.trans hb⟩
  rcases lt_trichotomy y u with hyu | he | huy
  · have h := homogeneousBlockMass_deriv_pos_before_critical hp M hu
      ⟨ha.trans hay, hyu⟩ k hupos hdu
    rw [hdy] at h
    exact False.elim (lt_irrefl _ h)
  · exact he
  · have h := homogeneousBlockMass_deriv_neg_after_critical hp M hu
      ⟨huy, hyb.trans hb⟩ k hupos hdu
    rw [hdy] at h
    exact False.elim (lt_irrefl _ h)

end

end PoissonBinomialComparison

-- LowerHomogeneity
namespace PoissonBinomialComparison

open scoped Topology
open Finset Set

noncomputable section

variable {ι : Type*} [DecidableEq ι] {p : ι → ℝ} {s : Finset ι}

theorem homogeneousBlockMass_add_prefix (M b : ℕ) {t : ℝ}
    (ht : 0 ≤ t ∧ t ≤ 1) (k : ℤ)
    (hprefix : ∀ j ≤ k, homogeneousBlockMass p s M t (j - 1) ≤ homogeneousBlockMass p s M t j) :
    homogeneousBlockMass p s (M + b) t k ≤ homogeneousBlockMass p s M t k ∧
      ∀ j ≤ k, homogeneousBlockMass p s (M + b) t (j - 1) ≤
        homogeneousBlockMass p s (M + b) t j := by
  induction b with
  | zero => simpa using And.intro (le_refl (homogeneousBlockMass p s M t k)) hprefix
  | succ b ih =>
    have hadj := ih.2 k le_rfl
    constructor
    · rw [show M + (b + 1) = (M + b) + 1 by omega, homogeneousBlockMass_succ]
      have hstep : (1 - t) * homogeneousBlockMass p s (M + b) t k +
          t * homogeneousBlockMass p s (M + b) t (k - 1) ≤ homogeneousBlockMass p s (M + b) t k := by
        nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr hadj)]
      exact hstep.trans ih.1
    · intro j hj
      rw [show M + (b + 1) = (M + b) + 1 by omega,
        homogeneousBlockMass_succ, homogeneousBlockMass_succ]
      exact add_le_add
        (mul_le_mul_of_nonneg_left (ih.2 j hj) (sub_nonneg.mpr ht.2))
        (mul_le_mul_of_nonneg_left (ih.2 (j - 1) (by omega)) ht.1)

theorem homogeneousBlockMass_add_pos (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1)
    (M b : ℕ) {t : ℝ} (ht : 0 < t ∧ t < 1) (k : ℤ)
    (hk : 0 < homogeneousBlockMass p s M t k) :
    0 < homogeneousBlockMass p s (M + b) t k := by
  induction b with
  | zero => simpa using hk
  | succ b ih =>
    rw [show M + (b + 1) = (M + b) + 1 by omega, homogeneousBlockMass_succ]
    exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr ht.2) ih)
      (mul_nonneg ht.1.le (homogeneousBlockMass_nonneg hp _ ⟨ht.1.le, ht.2.le⟩ _))

theorem homogeneousBlockMass_lt_after_nonpos (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1)
    (M : ℕ) {v a : ℝ} (hv : 0 < v) (hva : v < a) (ha : a < 1) (k : ℤ)
    (hk : 0 < homogeneousBlockMass p s (M + 2) v k)
    (hd : deriv (fun t ↦ homogeneousBlockMass p s (M + 2) t k) v ≤ 0) :
    homogeneousBlockMass p s (M + 2) a k < homogeneousBlockMass p s (M + 2) v k := by
  have hdiff : Differentiable ℝ (fun t ↦ homogeneousBlockMass p s (M + 2) t k) :=
    fun t ↦ (hasDerivAt_homogeneousBlockMass p s _ t k).differentiableAt
  have hanti : AntitoneOn (fun t ↦ homogeneousBlockMass p s (M + 2) t k) (Icc v a) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc v a) hdiff.continuous.continuousOn hdiff.differentiableOn
    intro t ht
    rw [interior_Icc] at ht
    exact homogeneousBlockMass_deriv_nonpos_mono hp _ ⟨hv, hva.trans ha⟩
      ⟨hv.trans ht.1, ht.2.trans ha⟩ ht.1.le k hd
  have hle := hanti ⟨le_rfl, hva.le⟩ ⟨hva.le, le_rfl⟩ hva.le
  apply lt_of_le_of_ne hle
  intro heq
  obtain ⟨u, hvu, hua, hupos, hdu⟩ := homogeneousBlockMass_exists_critical_between hp _ hv hva ha k hk heq.symm
  have hlt := homogeneousBlockMass_lt_of_critical hp M ⟨hv.trans hvu, hua.trans ha⟩
    ⟨hv.le, (hva.trans ha).le⟩ hvu.ne k hupos hdu
  exact not_lt_of_ge (hanti ⟨le_rfl, hva.le⟩ ⟨hvu.le, hua.le⟩ hvu.le) hlt

theorem homogeneousBlockMass_succ_adjacent_lt_of_tie
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) (M : ℕ) {t : ℝ}
    (ht : 0 < t ∧ t ≤ 1) (k : ℤ) (hk : 0 < homogeneousBlockMass p s M t k)
    (heq : homogeneousBlockMass p s M t (k - 1) = homogeneousBlockMass p s M t k) :
    homogeneousBlockMass p s (M + 1) t (k - 1) < homogeneousBlockMass p s (M + 1) t k := by
  have hlc := homogeneousBlockMass_strictLogConcavity hp M ⟨ht.1.le, ht.2⟩ (k - 1)
    (by rw [heq]; exact hk)
  simp only [sub_add_cancel, heq, pow_two] at hlc
  have hprev := (mul_lt_mul_iff_left₀ hk).mp hlc
  simp only [homogeneousBlockMass_succ, heq]
  nlinarith [mul_pos ht.1 (sub_pos.mpr hprev)]

theorem lower_two_values_block_lt (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1)
    {M b : ℕ} (hM : 1 ≤ M) (hr : 3 ≤ M + b + 1) {v a : ℝ}
    (hv : 0 < v) (hva : v < a) (ha : a < 1) (k : ℤ)
    (hk : 0 < homogeneousBlockMass p s M v k)
    (hd : deriv (fun t ↦ homogeneousBlockMass p s M t k) v = 0) :
    homogeneousBlockMass p s (M + b) a k < homogeneousBlockMass p s M v k := by
  have hv' : 0 < v ∧ v < 1 := ⟨hv, hva.trans ha⟩
  have ha' : 0 < a ∧ a < 1 := ⟨hv.trans hva, ha⟩
  have ha0 : 0 ≤ a ∧ a ≤ 1 := ⟨ha'.1.le, ha.le⟩
  by_cases hM1 : M = 1
  · subst M
    have hb : 1 ≤ b := by omega
    have hconst := homogeneousBlockMass_one_eq_of_deriv_eq_zero p s v a k hd
    have hk1 : 0 < homogeneousBlockMass p s 1 a k := by rwa [hconst]
    have htie : pbMassIntOn p s (k - 1) = pbMassIntOn p s k := by
      simpa only [deriv_homogeneousBlockMass_succ, homogeneousBlockMass_zero,
        Nat.zero_add, Nat.cast_one, one_mul, sub_eq_zero] using hd
    have hk0 : 0 < homogeneousBlockMass p s 0 a k := by
      simpa only [homogeneousBlockMass_succ, homogeneousBlockMass_zero, htie,
        show (1 - a) * pbMassIntOn p s k + a * pbMassIntOn p s k = pbMassIntOn p s k by ring] using hk1
    have hadj := homogeneousBlockMass_succ_adjacent_lt_of_tie hp 0 ⟨ha'.1, ha.le⟩ k hk0 htie
    have hprefix := (homogeneousBlockMass_cross hp 1 ha0).prefix_order
      (homogeneousBlockMass_nonneg hp 1 ha0) hk1 hadj.le
    have hlt : homogeneousBlockMass p s 2 a k < homogeneousBlockMass p s 1 a k := by
      rw [show 2 = 1 + 1 by rfl, homogeneousBlockMass_succ]
      nlinarith [mul_pos ha'.1 (sub_pos.mpr hadj)]
    have hprefix2 := (homogeneousBlockMass_add_prefix 1 1 ha0 k hprefix).2
    have hle := (homogeneousBlockMass_add_prefix 2 (b - 1) ha0 k hprefix2).1
    rw [show 2 + (b - 1) = 1 + b by omega] at hle
    exact (hle.trans_lt hlt).trans_eq hconst
  · obtain ⟨L, rfl⟩ : ∃ L, M = L + 2 := ⟨M - 2, by omega⟩
    have hlt := homogeneousBlockMass_lt_of_critical hp L hv' ha0 hva.ne' k hk hd
    have hpos := (homogeneousBlockMass_pos_iff hp (L + 2) hv' ha' k).mp hk
    have hder := homogeneousBlockMass_deriv_neg_after_critical hp L hv' ⟨hva, ha⟩ k hk hd
    have hadj := homogeneousBlockMass_adjacent_le_of_deriv_nonpos hp (L + 1) ha0 k hpos hder.le
    have hprefix := (homogeneousBlockMass_cross hp (L + 2) ha0).prefix_order
      (homogeneousBlockMass_nonneg hp (L + 2) ha0) hpos hadj
    exact (homogeneousBlockMass_add_prefix (L + 2) b ha0 k hprefix).1.trans_lt hlt

theorem lower_positive_and_zero_block_lt (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1)
    {M b : ℕ} (hM : 1 ≤ M) (hb : 1 ≤ b) (hr : 3 ≤ M + b) {v a : ℝ}
    (hv : 0 < v) (hva : v < a) (ha : a < 1) (k : ℤ)
    (hk : 0 < homogeneousBlockMass p s (M - 1) v k)
    (hzero : homogeneousBlockMass p s M v k ≤ homogeneousBlockMass p s (M - 1) v k) :
    homogeneousBlockMass p s (M + b - 1) a k < homogeneousBlockMass p s (M - 1) v k := by
  have hv' : 0 < v ∧ v < 1 := ⟨hv, hva.trans ha⟩
  have hv0 : 0 ≤ v ∧ v ≤ 1 := ⟨hv.le, (hva.trans ha).le⟩
  have hadj : homogeneousBlockMass p s (M - 1) v (k - 1) ≤ homogeneousBlockMass p s (M - 1) v k := by
    rw [show M = (M - 1) + 1 by omega, homogeneousBlockMass_succ] at hzero
    simp only [Nat.add_sub_cancel] at hzero
    nlinarith
  have hprefix := (homogeneousBlockMass_cross hp (M - 1) hv0).prefix_order
    (homogeneousBlockMass_nonneg hp (M - 1) hv0) hk hadj
  have hle := (homogeneousBlockMass_add_prefix (M - 1) b hv0 k hprefix).1
  have hpos := homogeneousBlockMass_add_pos hp (M - 1) b hv' k hk
  rw [show M - 1 + b = M + b - 1 by omega] at hle hpos
  have hdeleted := (homogeneousBlockMass_add_prefix (M - 1) (b - 1) hv0 k hprefix).2 k le_rfl
  have hd : deriv (fun t ↦ homogeneousBlockMass p s (M + b - 1) t k) v ≤ 0 := by
    rw [deriv_homogeneousBlockMass]
    apply mul_nonpos_of_nonneg_of_nonpos (by positivity)
    apply sub_nonpos.mpr
    convert! hdeleted using 1 <;> congr 2 <;> omega
  have hlt := homogeneousBlockMass_lt_after_nonpos hp (M + b - 3) hv hva ha k
    (by simpa only [show M + b - 3 + 2 = M + b - 1 by omega] using hpos)
    (by simpa only [show M + b - 3 + 2 = M + b - 1 by omega] using hd)
  rw [show M + b - 3 + 2 = M + b - 1 by omega] at hlt
  exact hlt.trans_le hle

theorem not_lower_two_values_stationary
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) {M b : ℕ}
    (hM : 1 ≤ M) (hr : 3 ≤ M + b + 1) {v a c : ℝ}
    (hv : 0 < v) (hva : v < a) (ha : a < 1) (hc : 0 < c) (k : ℤ)
    (hvgrad : homogeneousBlockMass p s M v k = c)
    (hagrad : homogeneousBlockMass p s (M + b) a k = c)
    (hd : deriv (fun t ↦ homogeneousBlockMass p s M t k) v = 0) : False := by
  have hlt := lower_two_values_block_lt hp hM hr hv hva ha k (by rwa [hvgrad]) hd
  rw [hvgrad, hagrad] at hlt
  exact lt_irrefl _ hlt

theorem not_lower_positive_and_zero_stationary
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) {M b : ℕ}
    (hM : 1 ≤ M) (hb : 1 ≤ b) (hr : 3 ≤ M + b) {v a c : ℝ}
    (hv : 0 < v) (hva : v < a) (ha : a < 1) (hc : 0 < c) (k : ℤ)
    (hvgrad : homogeneousBlockMass p s (M - 1) v k = c)
    (hzero : homogeneousBlockMass p s M v k ≤ c)
    (hagrad : homogeneousBlockMass p s (M + b - 1) a k = c) : False := by
  have hlt := lower_positive_and_zero_block_lt hp hM hb hr hv hva ha k
    (by rwa [hvgrad]) (by rwa [hvgrad])
  rw [hvgrad, hagrad] at hlt
  exact lt_irrefl _ hlt

end

end PoissonBinomialComparison

-- OtherVectorValues
namespace PoissonBinomialComparison

open Finset

noncomputable section

variable {ι : Type*} [DecidableEq ι]

def randomizedMassIntOn (p : ι → ℝ) (s : Finset ι) (w : ℝ) (k : ℤ) : ℝ :=
  bernoulliConvolve (pbMassIntOn p s) w k

@[simp] theorem randomizedMassIntOn_natCast (p : ι → ℝ) (s : Finset ι) (w : ℝ) (k : ℕ) :
    randomizedMassIntOn p s w k = randomizedSlopeOn p s w k := by
  cases k with
  | zero => simp [randomizedMassIntOn, bernoulliConvolve, randomizedSlopeOn, pbMassIntOn]
  | succ k =>
    have heq : ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) := by omega
    simp only [randomizedMassIntOn, bernoulliConvolve, heq, pbMassIntOn_natCast,
      randomizedSlopeOn, Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel]

theorem randomizedMassIntOn_of_neg (p : ι → ℝ) (s : Finset ι) (w : ℝ)
    {k : ℤ} (hk : k < 0) : randomizedMassIntOn p s w k = 0 := by
  simp [randomizedMassIntOn, bernoulliConvolve, pbMassIntOn_of_neg p s hk,
    pbMassIntOn_of_neg p s (by omega : k - 1 < 0)]

theorem randomizedMassIntOn_insert (p : ι → ℝ) {s : Finset ι} {i : ι}
    (hi : i ∉ s) (w : ℝ) (k : ℤ) :
    randomizedMassIntOn p (insert i s) w k =
      (1 - p i) * randomizedMassIntOn p s w k +
        p i * randomizedMassIntOn p s w (k - 1) := by
  simp only [randomizedMassIntOn, bernoulliConvolve, pbMassIntOn_insert p hi]
  ring

theorem randomizedMassIntOn_nonneg {p : ι → ℝ} {s : Finset ι}
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (k : ℤ) : 0 ≤ randomizedMassIntOn p s w k :=
  bernoulliConvolve_nonneg (pbMassIntOn_nonneg hp) hw0 hw1 k

theorem randomizedMassIntOn_cross {p : ι → ℝ} (s : Finset ι)
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    MassCrossInequalities (randomizedMassIntOn p s w) :=
  (pbMassIntOn_cross s hp).convolve hw0 (sub_nonneg.mpr hw1)

theorem randomizedMassIntOn_strictLogConcavity {p : ι → ℝ} (s : Finset ι)
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    StrictMassLogConcavity (randomizedMassIntOn p s w) :=
  StrictMassLogConcavity.convolve (pbMassIntOn_nonneg hp) (pbMassIntOn_cross s hp)
    (pbMassIntOn_strictLogConcavity s hp) hw0 (sub_nonneg.mpr hw1)

theorem randomizedCoefficientOn_eq_int (p : ι → ℝ) (s : Finset ι) (w : ℝ) (k : ℕ) :
    randomizedCoefficientOn p s w k =
      randomizedMassIntOn p s w ((k : ℤ) - 1) - randomizedMassIntOn p s w k := by
  cases k with
  | zero =>
    have hz : randomizedMassIntOn p s w (0 : ℤ) = randomizedSlopeOn p s w 0 :=
      randomizedMassIntOn_natCast p s w 0
    simp [randomizedCoefficientOn, randomizedMassIntOn_of_neg, hz]
  | succ k =>
    have heq : ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) := by omega
    simp only [randomizedCoefficientOn, Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel,
      heq, randomizedMassIntOn_natCast]

variable {n : ℕ} {q : Fin n → ℝ}

theorem not_three_distinct_of_equal_positive_gradients (hq : ValidParameters q)
    {w c : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hc : 0 < c)
    (k : ℕ) {i j l : Fin n} (hijq : q i ≠ q j) (hilq : q i ≠ q l) (hjlq : q j ≠ q l)
    (hGi : randomizedGradient q w k i = c)
    (hGj : randomizedGradient q w k j = c)
    (hGl : randomizedGradient q w k l = c) : False := by
  have hij : i ≠ j := fun heq ↦ hijq (congrArg q heq)
  have hil : i ≠ l := fun heq ↦ hilq (congrArg q heq)
  have hjl : j ≠ l := fun heq ↦ hjlq (congrArg q heq)
  have hCij : randomizedMixedCoefficient q w k i j = 0 := by
    have hd := randomizedGradient_sub q hij w k
    rw [hGi, hGj, sub_self] at hd
    exact (mul_eq_zero.mp hd.symm).resolve_left (sub_ne_zero.mpr hijq.symm)
  have hCil : randomizedMixedCoefficient q w k i l = 0 := by
    have hd := randomizedGradient_sub q hil w k
    rw [hGi, hGl, sub_self] at hd
    exact (mul_eq_zero.mp hd.symm).resolve_left (sub_ne_zero.mpr hilq.symm)
  let s := (((univ : Finset (Fin n)).erase i).erase j).erase l
  have hj : j ∉ s := by simp [s]
  have hl : l ∉ s := by simp [s]
  have hsij : insert l s = (univ.erase i).erase j := by
    apply insert_erase
    simp [hil.symm, hjl.symm]
  have hsil : insert j s = (univ.erase i).erase l := by
    ext t
    by_cases hti : t = i <;> by_cases htj : t = j <;> by_cases htl : t = l <;>
      simp_all [s]
  have hsi : insert j (insert l s) = univ.erase i := by
    rw [hsij]
    apply insert_erase
    simp [hij.symm]
  let X := randomizedMassIntOn q s w ((k : ℤ) - 2)
  let Y := randomizedMassIntOn q s w ((k : ℤ) - 1)
  let Z := randomizedMassIntOn q s w k
  have heq (t : Fin n) (ht : t ∉ s) :
      randomizedCoefficientOn q (insert t s) w k =
        (1 - q t) * (Y - Z) + q t * (X - Y) := by
    rw [randomizedCoefficientOn_eq_int, randomizedMassIntOn_insert q ht,
      randomizedMassIntOn_insert q ht]
    dsimp [X, Y, Z]
    rw [show (k : ℤ) - 1 - 1 = (k : ℤ) - 2 by omega]
    ring
  have hlzero : (1 - q l) * (Y - Z) + q l * (X - Y) = 0 := by
    rw [← heq l hl, hsij]
    exact hCij
  have hjzero : (1 - q j) * (Y - Z) + q j * (X - Y) = 0 := by
    rw [← heq j hj, hsil]
    exact hCil
  have hab : X - Y = Y - Z := by
    have hh : (q j - q l) * ((X - Y) - (Y - Z)) = 0 := by nlinarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr hjlq))
  rw [hab] at hjzero
  have hYZ : Y = Z := by nlinarith [hjzero]
  have hXY : X = Y := by linarith
  have hgrad : randomizedGradient q w k i = Y := by
    change randomizedSlopeOn q (univ.erase i) w k = Y
    rw [← randomizedMassIntOn_natCast, ← hsi,
      randomizedMassIntOn_insert q (by simp [hjl, hj]),
      randomizedMassIntOn_insert q hl, randomizedMassIntOn_insert q hl]
    change (1 - q j) * ((1 - q l) * Z + q l * Y) +
      q j * ((1 - q l) * Y + q l * randomizedMassIntOn q s w ((k : ℤ) - 1 - 1)) = Y
    rw [show (k : ℤ) - 1 - 1 = (k : ℤ) - 2 by omega]
    change (1 - q j) * ((1 - q l) * Z + q l * Y) +
      q j * ((1 - q l) * Y + q l * X) = Y
    rw [hXY, ← hYZ]
    ring
  have hY : 0 < Y := by linarith
  have hLC := randomizedMassIntOn_strictLogConcavity s (fun t _ ↦ hq t) hw0 hw1
    ((k : ℤ) - 1) hY
  have hcast : (k : ℤ) - 1 + 1 = (k : ℤ) := by omega
  have hcast' : (k : ℤ) - 1 - 1 = (k : ℤ) - 2 := by omega
  change randomizedMassIntOn q s w ((k : ℤ) - 1 - 1) *
    randomizedMassIntOn q s w ((k : ℤ) - 1 + 1) < Y ^ 2 at hLC
  rw [hcast, hcast'] at hLC
  change X * Z < Y ^ 2 at hLC
  rw [hXY, ← hYZ] at hLC
  nlinarith

theorem card_values_le_two_of_equal_positive_gradients (hq : ValidParameters q)
    {I : Finset (Fin n)} {w c : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hc : 0 < c)
    (k : ℕ) (hgrad : ∀ i ∈ I, randomizedGradient q w k i = c) :
    (I.image q).card ≤ 2 := by
  classical
  by_contra hnot
  obtain ⟨a, ha, b, hb, d, hd, hab, had, hbd⟩ := two_lt_card.mp (lt_of_not_ge hnot)
  obtain ⟨i, hi, rfl⟩ := mem_image.mp ha
  obtain ⟨j, hj, rfl⟩ := mem_image.mp hb
  obtain ⟨l, hl, rfl⟩ := mem_image.mp hd
  exact not_three_distinct_of_equal_positive_gradients hq hw0 hw1 hc k hab had hbd
    (hgrad i hi) (hgrad j hj) (hgrad l hl)

end

end PoissonBinomialComparison

-- BlockCoordinates
namespace PoissonBinomialComparison

open Finset

noncomputable section

def binomialBackgroundMass (s : ℕ) (w : ℝ) (M : ℕ) (t : ℝ) (k : ℤ) : ℝ :=
  homogeneousBlockMass (fun _ : Fin (s + 1) ↦ w) univ M t k

variable {ι : Type*} [DecidableEq ι]

theorem randomizedMassIntOn_union_zero (p : ι → ℝ) (S Z : Finset ι) (w : ℝ)
    (hz : ∀ i ∈ Z, p i = 0) (k : ℤ) :
    randomizedMassIntOn p (S ∪ Z) w k = randomizedMassIntOn p S w k := by
  induction Z using Finset.induction_on with
  | empty => simp
  | @insert i Z hi ih =>
    rw [union_insert]
    by_cases him : i ∈ S ∪ Z
    · rw [insert_eq_of_mem him]
      exact ih (fun j hj ↦ hz j (mem_insert_of_mem hj))
    · rw [randomizedMassIntOn_insert p him, hz i (mem_insert_self _ _)]
      simp only [sub_zero, one_mul, zero_mul, add_zero]
      exact ih (fun j hj ↦ hz j (mem_insert_of_mem hj))

theorem randomizedMassIntOn_common (p : ι → ℝ) (C : Finset ι) (w : ℝ)
    (hc : ∀ i ∈ C, p i = w) (k : ℤ) :
    randomizedMassIntOn p C w k =
      pbMassIntOn (fun _ : Fin (C.card + 1) ↦ w) univ k := by
  rw [← homogeneousBlockMass_empty_eq_pbMassInt p]
  induction C using Finset.induction_on generalizing k with
  | empty => simp [randomizedMassIntOn, bernoulliConvolve, homogeneousBlockMass_succ]
  | @insert i C hi ih =>
    rw [card_insert_of_notMem hi, randomizedMassIntOn_insert p hi, hc i (mem_insert_self _ _),
      homogeneousBlockMass_succ]
    rw [ih (fun j hj ↦ hc j (mem_insert_of_mem hj)), ih (fun j hj ↦ hc j (mem_insert_of_mem hj))]

theorem randomizedMassIntOn_common_union (p : ι → ℝ) (C H : Finset ι) (w t : ℝ)
    (hdisj : Disjoint C H) (hc : ∀ i ∈ C, p i = w) (hh : ∀ i ∈ H, p i = t) (k : ℤ) :
    randomizedMassIntOn p (C ∪ H) w k = binomialBackgroundMass C.card w H.card t k := by
  induction H using Finset.induction_on generalizing k with
  | empty => simpa [binomialBackgroundMass] using randomizedMassIntOn_common p C w hc k
  | @insert i H hi ih =>
    have hiC : i ∉ C := fun hic ↦ disjoint_left.mp hdisj hic (mem_insert_self _ _)
    have hdisj' : Disjoint C H := hdisj.mono_right (subset_insert _ _)
    have hh' : ∀ j ∈ H, p j = t := fun j hj ↦ hh j (mem_insert_of_mem hj)
    rw [union_insert, randomizedMassIntOn_insert p (by simp [hiC, hi]),
      hh i (mem_insert_self _ _), card_insert_of_notMem hi]
    simp only [binomialBackgroundMass, homogeneousBlockMass_succ]
    rw [ih hdisj' hh', ih hdisj' hh']
    rfl

theorem randomizedMassIntOn_pattern (p : ι → ℝ) (C H Z : Finset ι) (w t : ℝ)
    (hdisj : Disjoint C H) (hc : ∀ i ∈ C, p i = w) (hh : ∀ i ∈ H, p i = t)
    (hz : ∀ i ∈ Z, p i = 0) (k : ℤ) :
    randomizedMassIntOn p (C ∪ H ∪ Z) w k = binomialBackgroundMass C.card w H.card t k := by
  rw [randomizedMassIntOn_union_zero p (C ∪ H) Z w hz,
    randomizedMassIntOn_common_union p C H w t hdisj hc hh]

theorem pbMassIntOn_common_card (p : ι → ℝ) (C : Finset ι) (w : ℝ)
    (hc : ∀ i ∈ C, p i = w) (k : ℤ) :
    pbMassIntOn p C k = pbMassIntOn (fun _ : Fin C.card ↦ w) univ k := by
  rw [← homogeneousBlockMass_empty_eq_pbMassInt p]
  symm
  simpa using homogeneousBlockMass_eq_union p ∅ C (by simp) w hc k

theorem binomialBackgroundMass_eq_insert_common (p : ι → ℝ) (C : Finset ι)
    {z : ι} (hz : z ∉ C) (w : ℝ) (hc : ∀ i ∈ C, p i = w) (hzv : p z = w)
    (M : ℕ) (t : ℝ) (k : ℤ) :
    binomialBackgroundMass C.card w M t k = homogeneousBlockMass p (insert z C) M t k := by
  induction M generalizing k with
  | zero =>
    simp only [binomialBackgroundMass, homogeneousBlockMass_zero]
    rw [← homogeneousBlockMass_empty_eq_pbMassInt p]
    have hh := homogeneousBlockMass_eq_union p ∅ (insert z C) (by simp) w
      (fun i hi ↦ by rcases mem_insert.mp hi with rfl | hi; exact hzv; exact hc i hi) k
    rw [card_insert_of_notMem hz] at hh
    simpa using hh
  | succ M ih =>
    simp only [binomialBackgroundMass, homogeneousBlockMass_succ] at ih ⊢
    rw [ih, ih]

variable {n : ℕ}

theorem randomizedGradient_pattern (p : Fin n → ℝ) (C H Z : Finset (Fin n)) (i : Fin n)
    (w t : ℝ) (k : ℕ) (hpart : univ.erase i = C ∪ H ∪ Z)
    (hdisj : Disjoint C H) (hc : ∀ j ∈ C, p j = w) (hh : ∀ j ∈ H, p j = t)
    (hz : ∀ j ∈ Z, p j = 0) :
    randomizedGradient p w k i = binomialBackgroundMass C.card w H.card t k := by
  rw [randomizedGradient, ← randomizedMassIntOn_natCast, hpart]
  exact randomizedMassIntOn_pattern p C H Z w t hdisj hc hh hz k

theorem randomizedMixedCoefficient_pattern (p : Fin n → ℝ) (C H Z : Finset (Fin n))
    (i j : Fin n) (w t : ℝ) (k : ℕ) (hpart : (univ.erase i).erase j = C ∪ H ∪ Z)
    (hdisj : Disjoint C H) (hc : ∀ l ∈ C, p l = w) (hh : ∀ l ∈ H, p l = t)
    (hz : ∀ l ∈ Z, p l = 0) :
    randomizedMixedCoefficient p w k i j =
      binomialBackgroundMass C.card w H.card t ((k : ℤ) - 1) -
        binomialBackgroundMass C.card w H.card t k := by
  rw [randomizedMixedCoefficient, randomizedCoefficientOn_eq_int, hpart]
  rw [randomizedMassIntOn_pattern p C H Z w t hdisj hc hh hz,
    randomizedMassIntOn_pattern p C H Z w t hdisj hc hh hz]

theorem not_two_positive_coordinate_pattern (p q : Fin n → ℝ)
    (C H Z : Finset (Fin n)) (i : Fin n) {w u v a c : ℝ} (k : ℕ)
    (hpart : univ = insert i (C ∪ H ∪ Z)) (hi : i ∉ C ∪ H ∪ Z)
    (hCH : Disjoint C H) (hCZ : Disjoint C Z) (hHZ : Disjoint H Z)
    (hH : H.Nonempty) (hr : 3 ≤ H.card + Z.card + 1)
    (hw : 0 ≤ w ∧ w ≤ 1) (hu : 0 < u) (huv : u < v) (hva : v < a) (ha : a < 1)
    (hc : 0 < c) (hpC : ∀ l ∈ C, p l = w) (hqC : ∀ l ∈ C, q l = w)
    (hpI : ∀ l ∈ H ∪ Z, p l = a) (hqi : q i = u)
    (hqH : ∀ l ∈ H, q l = v) (hqZ : ∀ l ∈ Z, q l = 0)
    (hpiGrad : randomizedGradient p w k i = c)
    (hqiGrad : randomizedGradient q w k i = c)
    (hqHGrad : ∀ l ∈ H, randomizedGradient q w k l = c) : False := by
  have hdel : univ.erase i = C ∪ H ∪ Z := by rw [hpart, erase_insert hi]
  have hvg := randomizedGradient_pattern q C H Z i w v k hdel hCH hqC hqH hqZ
  have hag := randomizedGradient_pattern p C (H ∪ Z) ∅ i w a k
    (by simpa [union_assoc] using hdel) (disjoint_union_right.mpr ⟨hCH, hCZ⟩)
    hpC hpI (by simp)
  rw [card_union_of_disjoint hHZ] at hag
  obtain ⟨j, hj⟩ := hH
  have hij : i ≠ j := by intro heq; subst j; exact hi (by simp [hj])
  have hjC : j ∉ C := fun hjC ↦ disjoint_left.mp hCH hjC hj
  have hjZ : j ∉ Z := fun hjZ ↦ disjoint_left.mp hHZ hj hjZ
  have hdel2 : (univ.erase i).erase j = C ∪ H.erase j ∪ Z := by
    rw [hdel, erase_union_distrib, erase_union_distrib, erase_eq_of_notMem hjC, erase_eq_of_notMem hjZ]
  have hcoef := randomizedMixedCoefficient_pattern q C (H.erase j) Z i j w v k hdel2
    (hCH.mono_right (erase_subset _ _)) hqC
    (fun l hl ↦ hqH l (mem_erase.mp hl).2) hqZ
  rw [card_erase_of_mem hj] at hcoef
  have hgrad := randomizedGradient_sub q hij w k
  rw [hqiGrad, hqHGrad j hj, hqH j hj, hqi, sub_self] at hgrad
  have hcoef0 : randomizedMixedCoefficient q w k i j = 0 :=
    (mul_eq_zero.mp hgrad.symm).resolve_left (sub_pos.mpr huv).ne'
  have hd : deriv (fun t ↦ binomialBackgroundMass C.card w H.card t k) v = 0 := by
    simp only [binomialBackgroundMass, deriv_homogeneousBlockMass]
    change (H.card : ℝ) *
      (binomialBackgroundMass C.card w (H.card - 1) v ((k : ℤ) - 1) -
        binomialBackgroundMass C.card w (H.card - 1) v k) = 0
    rw [← hcoef, hcoef0, mul_zero]
  exact not_lower_two_values_stationary (fun _ _ ↦ hw) (by simpa using card_pos.mpr ⟨j, hj⟩)
    hr (hu.trans huv) hva ha hc k (hvg.symm.trans hqiGrad) (hag.symm.trans hpiGrad) hd

theorem not_positive_zero_coordinate_pattern (p q : Fin n → ℝ)
    (C H Z : Finset (Fin n)) {w v a c : ℝ} (k : ℕ)
    (hpart : univ = C ∪ H ∪ Z)
    (hCH : Disjoint C H) (hCZ : Disjoint C Z) (hHZ : Disjoint H Z)
    (hH : H.Nonempty) (hZ : Z.Nonempty) (hr : 3 ≤ H.card + Z.card)
    (hw : 0 ≤ w ∧ w ≤ 1) (hv : 0 < v) (hva : v < a) (ha : a < 1)
    (hc : 0 < c) (hpC : ∀ l ∈ C, p l = w) (hqC : ∀ l ∈ C, q l = w)
    (hpI : ∀ l ∈ H ∪ Z, p l = a)
    (hqH : ∀ l ∈ H, q l = v) (hqZ : ∀ l ∈ Z, q l = 0)
    (hpHGrad : ∀ l ∈ H, randomizedGradient p w k l = c)
    (hqHGrad : ∀ l ∈ H, randomizedGradient q w k l = c)
    (hqZGrad : ∀ l ∈ Z, randomizedGradient q w k l ≤ c) : False := by
  obtain ⟨i, hi⟩ := hH
  obtain ⟨j, hj⟩ := hZ
  have hiC : i ∉ C := fun hic ↦ disjoint_left.mp hCH hic hi
  have hiZ : i ∉ Z := fun hiz ↦ disjoint_left.mp hHZ hi hiz
  have hjC : j ∉ C := fun hjc ↦ disjoint_left.mp hCZ hjc hj
  have hjH : j ∉ H := fun hjh ↦ disjoint_left.mp hHZ hjh hj
  have hdeli : univ.erase i = C ∪ H.erase i ∪ Z := by
    rw [hpart, erase_union_distrib, erase_union_distrib, erase_eq_of_notMem hiC, erase_eq_of_notMem hiZ]
  have hdelj : univ.erase j = C ∪ H ∪ Z.erase j := by
    rw [hpart, erase_union_distrib, erase_union_distrib, erase_eq_of_notMem hjC, erase_eq_of_notMem hjH]
  have hvg := randomizedGradient_pattern q C (H.erase i) Z i w v k hdeli
    (hCH.mono_right (erase_subset _ _)) hqC (fun l hl ↦ hqH l (mem_erase.mp hl).2) hqZ
  rw [card_erase_of_mem hi] at hvg
  have hzg := randomizedGradient_pattern q C H (Z.erase j) j w v k hdelj hCH hqC hqH
    (fun l hl ↦ hqZ l (mem_erase.mp hl).2)
  have hag := randomizedGradient_pattern p C (H.erase i ∪ Z) ∅ i w a k
    (by simpa [union_assoc] using hdeli)
    (disjoint_union_right.mpr ⟨hCH.mono_right (erase_subset _ _), hCZ⟩)
    hpC (fun l hl ↦ hpI l (by
      rcases mem_union.mp hl with hl | hl
      · exact mem_union_left _ (mem_erase.mp hl).2
      · exact mem_union_right _ hl)) (by simp)
  rw [card_union_of_disjoint (hHZ.mono_left (erase_subset _ _)), card_erase_of_mem hi] at hag
  have hcard : H.card - 1 + Z.card = H.card + Z.card - 1 := by
    have hh := card_pos.mpr ⟨i, hi⟩
    omega
  rw [hcard] at hag
  exact not_lower_positive_and_zero_stationary (fun _ _ ↦ hw)
    (by simpa using card_pos.mpr ⟨i, hi⟩) (by simpa using card_pos.mpr ⟨j, hj⟩)
    hr hv hva ha hc k (hvg.symm.trans (hqHGrad i hi))
    (by change binomialBackgroundMass C.card w H.card v k ≤ c; rw [← hzg]; exact hqZGrad j hj) (hag.symm.trans (hpHGrad i hi))

end

end PoissonBinomialComparison

-- LowerCoordinateClassification
namespace PoissonBinomialComparison

open Finset

noncomputable section

variable {n : ℕ} {p q : Fin n → ℝ}

theorem lower_positive_values_equal_of_no_smaller_repeat
    (hq : ValidParameters q) (I C : Finset (Fin n))
    (hpart : univ = C ∪ I) (hCI : Disjoint C I) (hr : 3 ≤ I.card)
    {w a c : ℝ} (hw : 0 ≤ w ∧ w ≤ 1) (ha : a < 1) (hc : 0 < c) (k : ℕ)
    (hpC : ∀ i ∈ C, p i = w) (hqC : ∀ i ∈ C, q i = w)
    (hpI : ∀ i ∈ I, p i = a) (hqI : ∀ i ∈ I, q i < a)
    (hpgrad : ∀ i ∈ I, randomizedGradient p w k i = c)
    (hqgrad : ∀ i ∈ I, 0 < q i → randomizedGradient q w k i = c)
    (hsmall : ∀ i ∈ I, ∀ j ∈ I, ∀ l ∈ I,
      0 < q i → q i = q j → q i < q l → i = j) :
    ∀ i ∈ I, ∀ j ∈ I, 0 < q i → 0 < q j → q i = q j := by
  classical
  have hexclude : ∀ i ∈ I, ∀ j ∈ I, 0 < q i → q i < q j → False := by
    intro i hi j hj hqi hij
    let H := I.filter (fun l ↦ q l = q j)
    let Z := I.filter (fun l ↦ q l = 0)
    have hqi0 : q i ≠ 0 := hqi.ne'
    have hqj : 0 < q j := hqi.trans hij
    have hvalues : ∀ l ∈ I, q l = 0 ∨ q l = q i ∨ q l = q j := by
      intro l hl
      by_cases hz : q l = 0
      · exact Or.inl hz
      by_cases hui : q l = q i
      · exact Or.inr (Or.inl hui)
      by_cases hvj : q l = q j
      · exact Or.inr (Or.inr hvj)
      have hql : 0 < q l := lt_of_le_of_ne (hq l).1 (Ne.symm hz)
      exact False.elim (not_three_distinct_of_equal_positive_gradients hq hw.1 hw.2 hc k
        hij.ne (Ne.symm hui) (Ne.symm hvj) (hqgrad i hi hqi) (hqgrad j hj hqj) (hqgrad l hl hql))
    have hsmallonly : ∀ l ∈ I, q l = q i → l = i := by
      intro l hl heq
      exact hsmall l hl i hi j hj (by rwa [heq]) heq (by rwa [heq])
    have hI : I = insert i (H ∪ Z) := by
      ext l
      simp only [mem_insert, mem_union, H, Z, mem_filter]
      constructor
      · intro hl
        rcases hvalues l hl with hz | hu | hv
        · exact Or.inr (Or.inr ⟨hl, hz⟩)
        · exact Or.inl (hsmallonly l hl hu)
        · exact Or.inr (Or.inl ⟨hl, hv⟩)
      · rintro (rfl | hl | hl)
        · exact hi
        · exact hl.1
        · exact hl.1
    have hHsub : H ⊆ I := filter_subset _ _
    have hZsub : Z ⊆ I := filter_subset _ _
    have hHZ : Disjoint H Z := by
      apply disjoint_left.mpr
      intro l hlH hlZ
      have hu := (mem_filter.mp hlH).2
      have hz := (mem_filter.mp hlZ).2
      exact hqj.ne' (hu.symm.trans hz)
    have hiC : i ∉ C := fun hic ↦ disjoint_left.mp hCI hic hi
    have hin : i ∉ C ∪ H ∪ Z := by
      simp only [mem_union, not_or]
      exact ⟨⟨hiC, by simp [H, hij.ne]⟩, by simp [Z, hqi0]⟩
    have hcard : I.card = H.card + Z.card + 1 := by
      rw [hI, card_insert_of_notMem (by simp [H, Z, hij.ne, hqi0])]
      rw [card_union_of_disjoint hHZ]
    have hpatt : univ = insert i (C ∪ H ∪ Z) := by
      rw [hpart, hI]
      ext l
      simp only [mem_union, mem_insert]
      tauto
    exact not_two_positive_coordinate_pattern p q C H Z i k hpatt hin
      (hCI.mono_right hHsub) (hCI.mono_right hZsub) hHZ
      ⟨j, by simp [H, hj]⟩ (by omega) hw hqi hij (hqI j hj) ha hc hpC hqC
      (fun l hl ↦ hpI l (by rcases mem_union.mp hl with hl | hl; exact hHsub hl; exact hZsub hl))
      rfl (fun l hl ↦ (mem_filter.mp hl).2) (fun l hl ↦ (mem_filter.mp hl).2)
      (hpgrad i hi) (hqgrad i hi hqi)
      (fun l hl ↦ hqgrad l (hHsub hl) (by rw [(mem_filter.mp hl).2]; exact hqj))
  intro i hi j hj hqi hqj
  rcases lt_trichotomy (q i) (q j) with hij | heq | hji
  · exact False.elim (hexclude i hi j hj hqi hij)
  · exact heq
  · exact False.elim (hexclude j hj i hi hqj hji)

theorem lower_changing_coordinates_constant
    (hq : ValidParameters q) (I C : Finset (Fin n))
    (hpart : univ = C ∪ I) (hCI : Disjoint C I) (hr : 3 ≤ I.card)
    {w a c : ℝ} (hw : 0 ≤ w ∧ w ≤ 1) (ha : a < 1) (hc : 0 < c) (k : ℕ)
    (hpC : ∀ i ∈ C, p i = w) (hqC : ∀ i ∈ C, q i = w)
    (hpI : ∀ i ∈ I, p i = a) (hqI : ∀ i ∈ I, q i < a)
    (hpgrad : ∀ i ∈ I, randomizedGradient p w k i = c)
    (hqgrad : ∀ i ∈ I, 0 < q i → randomizedGradient q w k i = c)
    (hqzero : ∀ i ∈ I, q i = 0 → randomizedGradient q w k i ≤ c)
    (hsmall : ∀ i ∈ I, ∀ j ∈ I, ∀ l ∈ I,
      0 < q i → q i = q j → q i < q l → i = j) :
    ∃ b : ℝ, 0 ≤ b ∧ b < a ∧ ∀ i ∈ I, q i = b := by
  classical
  obtain ⟨i, hi⟩ : I.Nonempty := card_pos.mp (by omega)
  by_cases hpositive : ∃ j ∈ I, 0 < q j
  · obtain ⟨j, hj, hqj⟩ := hpositive
    have hequal := lower_positive_values_equal_of_no_smaller_repeat hq I C hpart hCI hr
      hw ha hc k hpC hqC hpI hqI hpgrad hqgrad hsmall
    have hvalues : ∀ l ∈ I, q l = 0 ∨ q l = q j := by
      intro l hl
      by_cases hz : q l = 0
      · exact Or.inl hz
      · exact Or.inr (hequal l hl j hj (lt_of_le_of_ne (hq l).1 (Ne.symm hz)) hqj)
    have hnozero : ∀ l ∈ I, q l ≠ 0 := by
      intro l hl hlzero
      let H := I.filter (fun x ↦ q x = q j)
      let Z := I.filter (fun x ↦ q x = 0)
      have hI : I = H ∪ Z := by
        ext x
        simp only [H, Z, mem_filter, mem_union]
        constructor
        · intro hx
          rcases hvalues x hx with hz | hv
          · exact Or.inr ⟨hx, hz⟩
          · exact Or.inl ⟨hx, hv⟩
        · rintro (h | h) <;> exact h.1
      have hHsub : H ⊆ I := filter_subset _ _
      have hZsub : Z ⊆ I := filter_subset _ _
      have hHZ : Disjoint H Z := by
        apply disjoint_left.mpr
        intro x hxH hxZ
        exact hqj.ne' ((mem_filter.mp hxH).2.symm.trans (mem_filter.mp hxZ).2)
      have hcard : I.card = H.card + Z.card := by rw [hI, card_union_of_disjoint hHZ]
      exact not_positive_zero_coordinate_pattern p q C H Z k
        (by rw [hpart, hI, union_assoc]) (hCI.mono_right hHsub) (hCI.mono_right hZsub) hHZ
        ⟨j, by simp [H, hj]⟩ ⟨l, by simp [Z, hl, hlzero]⟩ (by omega)
        hw hqj (hqI j hj) ha hc hpC hqC
        (fun x hx ↦ hpI x (by rw [hI]; exact hx))
        (fun x hx ↦ (mem_filter.mp hx).2) (fun x hx ↦ (mem_filter.mp hx).2)
        (fun x hx ↦ hpgrad x (hHsub hx))
        (fun x hx ↦ hqgrad x (hHsub hx) (by rw [(mem_filter.mp hx).2]; exact hqj))
        (fun x hx ↦ hqzero x (hZsub hx) (mem_filter.mp hx).2)
    refine ⟨q j, hqj.le, hqI j hj, ?_⟩
    intro l hl
    exact (hvalues l hl).resolve_left (hnozero l hl)
  · refine ⟨0, le_rfl, ?_, ?_⟩
    · have hqi : q i = 0 := le_antisymm (le_of_not_gt (fun hp ↦ hpositive ⟨i, hi, hp⟩)) (hq i).1
      simpa only [hqi] using hqI i hi
    · intro l hl
      exact le_antisymm (le_of_not_gt (fun hp ↦ hpositive ⟨l, hl, hp⟩)) (hq l).1

end

end PoissonBinomialComparison

-- NoCommonCoordinates
namespace PoissonBinomialComparison

open Finset

variable {ι : Type*} [DecidableEq ι]

theorem homogeneous_blocks_common_multiplier_impossible
    {p : ι → ℝ} {s : Finset ι} {z : ι} (hz : z ∉ s)
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) (M : ℕ) {a b w : ℝ}
    (hb0 : 0 < b) (hba : b < a) (ha1 : a < 1)
    (hw0 : 0 < w) (hw1 : w < 1) (hpz : p z = w) (k : ℤ)
    (hbprev : 0 < homogeneousBlockMass p s (M+2) b (k-1))
    (hbk : 0 < homogeneousBlockMass p s (M+2) b k)
    (heq : homogeneousBlockMass p (insert z s) (M+2) b k =
      homogeneousBlockMass p (insert z s) (M+2) a k)
    (hνa : 0 ≤ (a-w) * (homogeneousBlockMass p s (M+2) a (k-1) -
      homogeneousBlockMass p s (M+2) a k))
    (hνb : 0 ≤ (b-w) * (homogeneousBlockMass p s (M+2) b (k-1) -
      homogeneousBlockMass p s (M+2) b k)) : False := by
  have ha : 0 < a ∧ a < 1 := ⟨hb0.trans hba,ha1⟩
  have hb : 0 < b ∧ b < 1 := ⟨hb0,hba.trans ha1⟩
  have hps : ∀ i ∈ insert z s, 0 ≤ p i ∧ p i ≤ 1 := by
    intro i hi
    rcases mem_insert.mp hi with rfl | hi
    · rw [hpz]; exact ⟨hw0.le,hw1.le⟩
    · exact hp i hi
  have hapos := (homogeneousBlockMass_pos_iff hp (M+2) hb ha k).mp hbk
  have hgpos : 0 < homogeneousBlockMass p (insert z s) (M+2) b k := by
    rw [homogeneousBlockMass_insert p hz,hpz]
    exact add_pos (mul_pos (sub_pos.mpr hw1) hbk) (mul_pos hw0 hbprev)
  obtain ⟨u,hbu,hua,hupos,hdu⟩ := homogeneousBlockMass_exists_critical_between
    hps (M+2) hb0 hba ha1 k hgpos heq
  have hu : 0 < u ∧ u < 1 := ⟨hb0.trans hbu,hua.trans ha1⟩
  have hda := homogeneousBlockMass_deriv_neg_after_critical hps M hu ⟨hua,ha1⟩ k hupos hdu
  have hdb := homogeneousBlockMass_deriv_pos_before_critical hps M hu ⟨hb0,hbu⟩ k hupos hdu
  rw [show M+2 = (M+1)+1 by omega,deriv_homogeneousBlockMass_succ] at hda hdb
  have hDa : homogeneousBlockMass p (insert z s) (M+1) a (k-1) <
      homogeneousBlockMass p (insert z s) (M+1) a k := by
    have hM : (0 : ℝ) < (M+1+1 : ℕ) := by positivity
    nlinarith
  have hDb : homogeneousBlockMass p (insert z s) (M+1) b k <
      homogeneousBlockMass p (insert z s) (M+1) b (k-1) := by
    have hM : (0 : ℝ) < (M+1+1 : ℕ) := by positivity
    nlinarith
  rcases le_or_gt w b with hwb | hbw
  · have hwa : w < a := hwb.trans_lt hba
    have hA : homogeneousBlockMass p s (M+2) a k ≤
        homogeneousBlockMass p s (M+2) a (k-1) := by
      nlinarith
    have hlr := bernoulliConvolve_likelihoodRatio
      (homogeneousBlockMass_cross hp (M+1) ⟨ha.1.le,ha.2.le⟩) hwa.le (k-1) k (by omega)
    have hDa0 := homogeneousBlockMass_nonneg hps (M+1) ⟨ha.1.le,ha.2.le⟩ (k-1)
    have hDa1 : 0 < homogeneousBlockMass p (insert z s) (M+1) a k := hDa0.trans_lt hDa
    have hform (l : ℤ) : bernoulliConvolve (homogeneousBlockMass p s (M+1) a) w l =
        homogeneousBlockMass p (insert z s) (M+1) a l := by
      simp only [homogeneousBlockMass_insert p hz,hpz,bernoulliConvolve]
    rw [hform,hform] at hlr
    change homogeneousBlockMass p s (M+2) a (k-1) *
      homogeneousBlockMass p (insert z s) (M+1) a k ≤
      homogeneousBlockMass p s (M+2) a k *
      homogeneousBlockMass p (insert z s) (M+1) a (k-1) at hlr
    nlinarith only [hlr, mul_pos (sub_pos.mpr hDa) hapos,
      mul_nonneg hDa1.le (sub_nonneg.mpr hA)]
  · rcases le_or_gt a w with haw | hwa
    · have hbw' : b < w := hba.trans_le haw
      have hB : homogeneousBlockMass p s (M+2) b (k-1) ≤
          homogeneousBlockMass p s (M+2) b k := by nlinarith
      have hlr := bernoulliConvolve_likelihoodRatio
        (homogeneousBlockMass_cross hp (M+1) ⟨hb.1.le,hb.2.le⟩) hbw'.le (k-1) k (by omega)
      have hform (l : ℤ) : bernoulliConvolve (homogeneousBlockMass p s (M+1) b) w l =
          homogeneousBlockMass p (insert z s) (M+1) b l := by
        simp only [homogeneousBlockMass_insert p hz,hpz,bernoulliConvolve]
      rw [hform,hform] at hlr
      change homogeneousBlockMass p (insert z s) (M+1) b (k-1) *
        homogeneousBlockMass p s (M+2) b k ≤
        homogeneousBlockMass p (insert z s) (M+1) b k *
        homogeneousBlockMass p s (M+2) b (k-1) at hlr
      have hDb0 := homogeneousBlockMass_nonneg hps (M+1) ⟨hb.1.le,hb.2.le⟩ k
      nlinarith only [hlr, mul_pos (sub_pos.mpr hDb) hbk, mul_nonneg hDb0 (sub_nonneg.mpr hB)]
    · have hA : homogeneousBlockMass p s (M+2) a k ≤
          homogeneousBlockMass p s (M+2) a (k-1) := by nlinarith
      have hB : homogeneousBlockMass p s (M+2) b (k-1) ≤
          homogeneousBlockMass p s (M+2) b k := by nlinarith
      have hstrict := homogeneousBlockMass_strict_adjacent hp (M+1)
        ⟨hb.1.le,hb.2.le⟩ ⟨ha.1.le,ha.2.le⟩ hba (k-1) hbprev
        (by simpa using hbk) (by simpa using hapos)
      simp only [sub_add_cancel] at hstrict
      nlinarith only [hstrict, mul_nonneg hapos.le (sub_nonneg.mpr hB),
        mul_nonneg hbk.le (sub_nonneg.mpr hA)]

end PoissonBinomialComparison

-- CommonHomogeneousCoordinates
namespace PoissonBinomialComparison

open Finset

private theorem block_congr_background {ι : Type*} [DecidableEq ι]
    {p q : ι → ℝ} {s : Finset ι} (h : ∀ i ∈ s, p i = q i)
    (M : ℕ) (t : ℝ) (k : ℤ) :
    homogeneousBlockMass p s M t k = homogeneousBlockMass q s M t k := by
  induction M generalizing k with
  | zero => exact pbMassIntOn_congr h k
  | succ M ih => simp only [homogeneousBlockMass_succ, ih]

private theorem mass_pos_interior {ι : Type*} [DecidableEq ι]
    {p : ι → ℝ} (s : Finset ι) (hp : ∀ i ∈ s, 0 < p i ∧ p i < 1)
    {k : ℕ} (hk : k ≤ s.card) : 0 < pbMassOn p s k := by
  apply pbMassOn_positive_between s (fun i hi => ⟨(hp i hi).1.le,(hp i hi).2.le⟩)
    (Nat.zero_le k) hk
  · rw [pbMassOn_zero]
    exact prod_pos fun i hi => sub_pos.mpr (hp i hi).2
  · rw [pbMassOn_card_eq_prod]
    exact prod_pos fun i hi => (hp i hi).1

theorem IsGapMinimizer.no_common_of_changing_constants {n : ℕ} (hn : 3 ≤ n)
    (hind : ∀ r s : Fin (n-1) → ℝ, AdmissiblePair r s →
      benchmark (n-1) (meanGap r s) ≤ tailObjective r s)
    {p q : Fin n → ℝ} (h : AdmissiblePair p q) (hm : IsGapMinimizer p q)
    (hg0 : 0 < meanGap p q) (hgn : meanGap p q < n)
    {a b : ℝ} (hpa : ∀ i, q i < p i → p i = a)
    (hqb : ∀ i, q i < p i → q i = b) : ∀ i, q i < p i := by
  have ha := hm.upper_changing_constant_interior hn hind h hg0 hgn hpa
  have hb := hm.lower_changing_constant_interior hn hind h hg0 hgn hqb
  obtain ⟨i,hi⟩ := exists_strict_coordinate_of_meanGap_pos h hg0
  have hba : b < a := by simpa only [hpa i hi,hqb i hi] using hi
  by_contra hnot
  push Not at hnot
  obtain ⟨l,hl⟩ := hnot
  have hlcommon : p l = q l := le_antisymm hl (h.2.2 l)
  have hbds := hm.parameter_bounds hn hind h hg0
  obtain ⟨k,w,c,hk0,hkn,hw0,hw1,hc,hactive,hlast,_,hchanging,hcommonGrad⟩ :=
    exists_tail_kkt h (fun j => (hbds j).1) (fun j => (hbds j).2) hg0
      (hm.tailObjective_lt_one hn hg0 hgn) hm.isLocalMinOn
  have hgrad : ∀ j, p j = q j → randomizedGradient p w k j = randomizedGradient q w k j ∧
      c ≤ randomizedGradient p w k j := by
    intro j hj
    obtain ⟨ν,hν,hP,hQ⟩ := hcommonGrad j hj
    exact ⟨hP.trans hQ.symm,by linarith⟩
  obtain ⟨hactive1,hwpos,hwlt,htie,_,hcmass,hparams⟩ :=
    common_coordinates_of_kkt hn hind h hm hg0 (fun j => (hbds j).1)
      (fun j => (hbds j).2) hw0 hw1 hc hactive hlast ⟨l,hlcommon⟩ hgrad
  have hkn' : k < n := by have := ((mem_activeThresholds p q (k+1)).mp hactive1).2.1; omega
  let C := (univ : Finset (Fin n)).filter (fun j => p j = q j)
  let I := positiveGapCoordinates p q
  let H := I.erase i
  have hiI : i ∈ I := by simp [I,positiveGapCoordinates,hi]
  have hiC : i ∉ C := by simp [C,ne_of_gt hi]
  have hC (j : Fin n) (hj : j ∈ C) : p j = q j := (mem_filter.mp hj).2
  have hI (j : Fin n) (hj : j ∈ I) : q j < p j := (mem_filter.mp hj).2
  have hpart : univ.erase i = C ∪ H := by
    ext j
    simp only [mem_erase,mem_univ,and_true,true_and,mem_union,H,C,mem_filter,mem_univ,true_and]
    constructor
    · intro hji
      rcases (h.2.2 j).eq_or_lt with heq | hlt
      · exact Or.inl heq.symm
      · exact Or.inr ⟨hji,by simp [I,positiveGapCoordinates,hlt]⟩
    · rintro (heq | ⟨hji,_⟩)
      · intro heji; subst j; exact hi.ne' heq
      · exact hji
  have hdisj : Disjoint C H := by
    apply disjoint_left.mpr
    intro j hjC hjH
    have hh := hI j (mem_erase.mp hjH).2
    rw [hC j hjC] at hh
    exact lt_irrefl _ hh
  have hcard : 2 ≤ H.card := by
    have hh := hm.three_le_positiveGapCoordinates hn h hg0 hgn
    change 3 ≤ I.card at hh
    simpa only [H,card_erase_of_mem hiI] using (show 2 ≤ I.card-1 by omega)
  have hsize : H.card-2+2 = H.card := by omega
  have hcP : ∀ j ∈ C, p j = w := fun j hj => (hparams j (hC j hj)).1
  have hcQ : ∀ j ∈ C, q j = w := fun j hj => (hC j hj).symm.trans (hcP j hj)
  have hhP : ∀ j ∈ H, p j = a := fun j hj => hpa j (hI j (mem_erase.mp hj).2)
  have hhQ : ∀ j ∈ H, q j = b := fun j hj => hqb j (hI j (mem_erase.mp hj).2)
  let P : Fin n → ℝ := fun _ => w
  have bridge (v : Fin n → ℝ) (t : ℝ) (hvC : ∀ j ∈ C, v j = w)
      (hvH : ∀ j ∈ H, v j = t) (z : ℤ) :
      homogeneousBlockMass P C H.card t z = pbMassIntOn v (univ.erase i) z := by
    rw [block_congr_background (q := v) (fun j hj => (hvC j hj).symm)]
    rw [homogeneousBlockMass_eq_union v C H hdisj t hvH,← hpart]
  have gradbridge (v : Fin n → ℝ) (t : ℝ) (hvC : ∀ j ∈ C, v j = w)
      (hvH : ∀ j ∈ H, v j = t) :
      homogeneousBlockMass P (insert i C) H.card t k = randomizedGradient v w k i := by
    rw [randomizedGradient_pattern v C H ∅ i w t k (by simpa using hpart)
      hdisj hvC hvH (by simp)]
    exact (binomialBackgroundMass_eq_insert_common P C hiC w (fun _ _ => rfl) rfl _ _ _).symm
  have hgP : randomizedGradient p w k i = c := (hchanging i hi).2.2.1 (by rw [hpa i hi]; exact ha.2)
  have hgQ : randomizedGradient q w k i = c := (hchanging i hi).2.2.2 (by rw [hqb i hi]; exact hb.1)
  have hqinterior : ∀ j, 0 < q j ∧ q j < 1 := by
    intro j
    rcases (h.2.2 j).eq_or_lt with heq | hlt
    · have hwj := (hparams j heq.symm).1
      rw [heq,hwj]; exact ⟨hwpos,hwlt⟩
    · rw [hqb j hlt]; exact hb
  have hpred : (k : ℤ)-1 = ((k-1 : ℕ) : ℤ) := by omega
  have hpos (z : ℕ) (hz : z ≤ n-1) : 0 < homogeneousBlockMass P C H.card b z := by
    rw [bridge q b hcQ hhQ,pbMassIntOn_natCast]
    exact mass_pos_interior _ (fun j _ => hqinterior j) (by simpa using hz)
  have hnu (v : Fin n → ℝ) (t : ℝ) (hvi : v i = t)
      (hvC : ∀ j ∈ C, v j = w) (hvH : ∀ j ∈ H, v j = t)
      (hgv : randomizedGradient v w k i = c) (hmv : c ≤ pbMass v k) :
      0 ≤ (t-w) * (homogeneousBlockMass P C H.card t ((k : ℤ)-1) -
        homogeneousBlockMass P C H.card t k) := by
    rw [hpred,bridge v t hvC hvH,bridge v t hvC hvH,pbMassIntOn_natCast,pbMassIntOn_natCast]
    have hrec := pbMass_delete_succ v i (k-1)
    rw [show k-1+1=k by omega,hvi] at hrec
    simp only [randomizedGradient,randomizedSlopeOn,show k ≠ 0 by omega,ite_false] at hgv
    nlinarith only [hrec,hgv,hmv]
  apply homogeneous_blocks_common_multiplier_impossible hiC (fun _ _ => ⟨hw0,hw1⟩)
    (H.card-2) hb.1 hba ha.2 hwpos hwlt (show P i=w from rfl) (k : ℤ)
  · rw [hsize,hpred]; exact hpos (k-1) (by omega)
  · rw [hsize]; exact hpos k (by omega)
  · rw [hsize,gradbridge q b hcQ hhQ,gradbridge p a hcP hhP,hgP,hgQ]
  · rw [hsize]; exact hnu p a (hpa i hi) hcP hhP hgP hcmass
  · rw [hsize]; exact hnu q b (hqb i hi) hcQ hhQ hgQ (by rwa [← htie])

theorem IsGapMinimizer.homogeneous_of_changing_constants {n : ℕ} (hn : 3 ≤ n)
    (hind : ∀ r s : Fin (n-1) → ℝ, AdmissiblePair r s →
      benchmark (n-1) (meanGap r s) ≤ tailObjective r s)
    {p q : Fin n → ℝ} (h : AdmissiblePair p q) (hm : IsGapMinimizer p q)
    (hg0 : 0 < meanGap p q) (hgn : meanGap p q < n)
    {a b : ℝ} (hpa : ∀ i, q i < p i → p i = a)
    (hqb : ∀ i, q i < p i → q i = b) :
    p = (fun _ => a) ∧ q = (fun _ => b) := by
  have hc := hm.no_common_of_changing_constants hn hind h hg0 hgn hpa hqb
  exact ⟨funext (fun i => hpa i (hc i)),funext (fun i => hqb i (hc i))⟩

end PoissonBinomialComparison

-- SplitSecondVariation
namespace PoissonBinomialComparison

open Finset Filter
open scoped Topology

noncomputable section

variable {n : ℕ} {q : Fin n → ℝ}

theorem randomized_double_delete_masses_eq {w c : ℝ} (k : ℕ) {i j : Fin n}
    (hneq : q i ≠ q j) (hGi : randomizedGradient q w k i = c)
    (hGj : randomizedGradient q w k j = c) :
    randomizedMassIntOn q ((univ.erase i).erase j) w ((k : ℤ) - 1) = c ∧
      randomizedMassIntOn q ((univ.erase i).erase j) w k = c := by
  have hij : i ≠ j := fun heq ↦ hneq (congrArg q heq)
  have hC : randomizedMixedCoefficient q w k i j = 0 := by
    have hd := randomizedGradient_sub q hij w k
    rw [hGi, hGj, sub_self] at hd
    exact (mul_eq_zero.mp hd.symm).resolve_left (sub_ne_zero.mpr hneq.symm)
  have hgrad := randomizedGradient_eq_double_delete q hij w k
  rw [hGi, hC, mul_zero, add_zero] at hgrad
  have hB : randomizedMassIntOn q ((univ.erase i).erase j) w k = c := by
    rw [randomizedMassIntOn_natCast]
    exact hgrad.symm
  change randomizedCoefficientOn q ((univ.erase i).erase j) w k = 0 at hC
  rw [randomizedCoefficientOn_eq_int, hB] at hC
  exact ⟨by linarith, hB⟩

theorem randomizedMixedCoefficient_neg_of_repeated_smaller (hq : ValidParameters q)
    {w c : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hc : 0 < c)
    (k : ℕ) {i j l : Fin n} (hij : i ≠ j) (heq : q i = q j) (hlt : q i < q l)
    (hGi : randomizedGradient q w k i = c)
    (hGl : randomizedGradient q w k l = c) :
    randomizedMixedCoefficient q w k i j < 0 := by
  have hil : i ≠ l := fun hh ↦ hlt.ne (congrArg q hh)
  have hjl : j ≠ l := by intro hh; exact hlt.ne (heq.trans (congrArg q hh))
  let s := (((univ : Finset (Fin n)).erase i).erase j).erase l
  have hj : j ∉ s := by simp [s]
  have hl : l ∉ s := by simp [s]
  have hsij : insert l s = (univ.erase i).erase j := by
    apply insert_erase
    simp [hil.symm, hjl.symm]
  have hsil : insert j s = (univ.erase i).erase l := by
    ext t
    by_cases hti : t = i <;> by_cases htj : t = j <;> by_cases htl : t = l <;>
      simp_all [s]
  let f := randomizedMassIntOn q s w
  have hconv (t : Fin n) (ht : t ∉ s) (a : ℤ) :
      randomizedMassIntOn q (insert t s) w a = bernoulliConvolve f (q t) a := by
    exact randomizedMassIntOn_insert q ht w a
  obtain ⟨hA, hB⟩ := randomized_double_delete_masses_eq k hlt.ne hGi hGl
  rw [← hsil, hconv j hj] at hA hB
  have hApos : 0 < bernoulliConvolve f (q j) ((k : ℤ) - 1) := by rwa [hA]
  have hBpos : 0 < bernoulliConvolve f (q j) ((k : ℤ) - 1 + 1) := by
    simpa only [sub_add_cancel] using (hB ▸ hc : 0 < bernoulliConvolve f (q j) k)
  have hdet := bernoulliConvolve_strict_adjacent
    (randomizedMassIntOn_nonneg (fun t (_ : t ∈ s) ↦ hq t) hw0 hw1)
    (randomizedMassIntOn_cross s (fun t _ ↦ hq t) hw0 hw1)
    (randomizedMassIntOn_strictLogConcavity s (fun t _ ↦ hq t) hw0 hw1)
    (hq j).1 (hq j).2 (by linarith : q j < q l) ((k : ℤ) - 1) hApos hBpos
  change bernoulliConvolve f (q l) ((k : ℤ) - 1) *
    bernoulliConvolve f (q j) ((k : ℤ) - 1 + 1) <
      bernoulliConvolve f (q l) ((k : ℤ) - 1 + 1) *
        bernoulliConvolve f (q j) ((k : ℤ) - 1) at hdet
  simp only [sub_add_cancel, hA, hB] at hdet
  have hsign := (mul_lt_mul_iff_left₀ hc).mp hdet
  change randomizedCoefficientOn q ((univ.erase i).erase j) w k < 0
  rw [randomizedCoefficientOn_eq_int, ← hsij, hconv l hl, hconv l hl]
  exact sub_neg.mpr hsign

theorem double_deleted_second_difference_ne_zero (hq : ValidParameters q)
    {w c : ℝ} (hc : 0 < c) (k : ℕ) {i j : Fin n}
    (hneq : q i ≠ q j) (hGi : randomizedGradient q w k i = c)
    (hGj : randomizedGradient q w k j = c) :
    pbMassIntOn q ((univ.erase i).erase j) ((k : ℤ) - 2) -
        2 * pbMassIntOn q ((univ.erase i).erase j) ((k : ℤ) - 1) +
          pbMassIntOn q ((univ.erase i).erase j) k ≠ 0 := by
  intro hzero
  let s := ((univ : Finset (Fin n)).erase i).erase j
  let X := pbMassIntOn q s ((k : ℤ) - 2)
  let Y := pbMassIntOn q s ((k : ℤ) - 1)
  let Z := pbMassIntOn q s k
  change X - 2 * Y + Z = 0 at hzero
  obtain ⟨hA, hB⟩ := randomized_double_delete_masses_eq k hneq hGi hGj
  change (1 - w) * Y + w * pbMassIntOn q s ((k : ℤ) - 1 - 1) = c at hA
  rw [show (k : ℤ) - 1 - 1 = (k : ℤ) - 2 by omega] at hA
  change (1 - w) * Y + w * X = c at hA
  change (1 - w) * Z + w * Y = c at hB
  have hXY : X - Y = Y - Z := by linarith
  have hXZ : X = 2 * Y - Z := by linarith
  rw [hXZ] at hA
  have hYZ : Y = Z := by nlinarith [hA, hB]
  have hXY' : X = Y := by linarith
  have hY : Y = c := by rw [← hYZ] at hB; nlinarith [hB]
  have hpos : 0 < pbMassIntOn q s ((k : ℤ) - 1) := by change 0 < Y; rwa [hY]
  have hLC := pbMassIntOn_strictLogConcavity s (fun t _ ↦ hq t) ((k : ℤ) - 1) hpos
  rw [show (k : ℤ) - 1 - 1 = (k : ℤ) - 2 by omega,
    show (k : ℤ) - 1 + 1 = (k : ℤ) by omega] at hLC
  change X * Z < Y ^ 2 at hLC
  rw [hXY', ← hYZ] at hLC
  nlinarith

theorem mass_tie_transfer_coefficient_ne_zero (hq : ValidParameters q)
    {w c : ℝ} (hc : 0 < c) (k : ℕ) {i j : Fin n}
    (hneq : q i ≠ q j) (hGi : randomizedGradient q w k i = c)
    (hGj : randomizedGradient q w k j = c) :
    -(q j - q i) *
      (pbMassIntOn q ((univ.erase i).erase j) ((k : ℤ) - 2) -
        2 * pbMassIntOn q ((univ.erase i).erase j) ((k : ℤ) - 1) +
          pbMassIntOn q ((univ.erase i).erase j) k) ≠ 0 :=
  mul_ne_zero (neg_ne_zero.mpr (sub_ne_zero.mpr hneq.symm))
    (double_deleted_second_difference_ne_zero hq hc k hneq hGi hGj)

theorem exists_tie_preserving_curve {G : ℝ × ℝ → ℝ} {b : ℝ} (hb : b ≠ 0)
    (hG : HasStrictFDerivAt G (b • ContinuousLinearMap.snd ℝ ℝ ℝ) (0, 0)) :
    ∃ s : ℝ → ℝ, s 0 = 0 ∧ HasDerivAt s 0 0 ∧
      ∀ᶠ t in 𝓝 (0 : ℝ), G (t, s t) = G (0, 0) := by
  let L := b • ContinuousLinearMap.snd ℝ ℝ ℝ
  have hL : L ∘L ContinuousLinearMap.inr ℝ ℝ ℝ = b • ContinuousLinearMap.id ℝ ℝ := by
    ext
    simp [L]
  have hinv1 : (b • ContinuousLinearMap.id ℝ ℝ) ∘L (b⁻¹ • ContinuousLinearMap.id ℝ ℝ) =
      ContinuousLinearMap.id ℝ ℝ := by ext; simp [hb]
  have hinv2 : (b⁻¹ • ContinuousLinearMap.id ℝ ℝ) ∘L (b • ContinuousLinearMap.id ℝ ℝ) =
      ContinuousLinearMap.id ℝ ℝ := by ext; simp [hb]
  have hinv : (L ∘L ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible := by
    rw [hL]
    exact ContinuousLinearMap.IsInvertible.of_inverse hinv1 hinv2
  let s := hG.implicitFunctionOfProdDomain hinv
  have hs0 : s 0 = 0 :=
    (hG.eventually_apply_eq_iff_implicitFunctionOfProdDomain hinv).self_of_nhds.mp rfl
  have hs : HasDerivAt s 0 0 := by
    have hd := (hG.hasStrictFDerivAt_implicitFunctionOfProdDomain hinv).hasFDerivAt.hasDerivAt
    have hzero : L ∘L ContinuousLinearMap.inl ℝ ℝ ℝ = 0 := by ext; simp [L]
    change HasDerivAt s ((-(L ∘L ContinuousLinearMap.inr ℝ ℝ ℝ).inverse ∘L
      (L ∘L ContinuousLinearMap.inl ℝ ℝ ℝ)) 1) 0 at hd
    simpa only [hzero, ContinuousLinearMap.comp_zero, neg_zero, zero_apply] using hd
  exact ⟨s, hs0, hs, hG.eventually_apply_implicitFunctionOfProdDomain hinv⟩

theorem quadratic_decrease_along_tangent_curve {J A B : ℝ × ℝ → ℝ} {C : ℝ}
    (hC : C < 0) (hA : ContinuousAt A (0, 0)) (hB : ContinuousAt B (0, 0))
    (hJ : ∀ z, J z = J (0, 0) + C * z.1 ^ 2 + z.1 * z.2 * A z + z.2 ^ 2 * B z)
    {s : ℝ → ℝ} (hs0 : s 0 = 0) (hs : HasDerivAt s 0 0) :
    ∀ᶠ t in 𝓝[≠] (0 : ℝ), J (t, s t) < J (0, 0) := by
  have ht : Tendsto (fun t : ℝ ↦ t) (𝓝[≠] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hst : Tendsto s (𝓝[≠] 0) (𝓝 0) := by
    simpa only [hs0] using hs.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hratio : Tendsto (fun t ↦ s t / t) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    simpa [hs0, smul_eq_mul, div_eq_mul_inv, mul_comm] using hs.tendsto_slope_zero
  have hAt := hA.tendsto.comp (ht.prodMk_nhds hst)
  have hBt := hB.tendsto.comp (ht.prodMk_nhds hst)
  have hlim : Tendsto (fun t ↦ C + (s t / t) * A (t, s t) + (s t / t)^2 * B (t, s t))
      (𝓝[≠] (0 : ℝ)) (𝓝 C) := by
    simpa using (tendsto_const_nhds.add (hratio.mul hAt)).add ((hratio.pow 2).mul hBt)
  have hneg := hlim.eventually (Iio_mem_nhds hC)
  filter_upwards [hneg, self_mem_nhdsWithin] with t hneg htne
  have ht0 : t ≠ 0 := htne
  have heq : J (t, s t) - J (0, 0) =
      t^2 * (C + (s t / t) * A (t, s t) + (s t / t)^2 * B (t, s t)) := by
    rw [hJ (t, s t)]
    dsimp
    field_simp
    ring
  have hlt := mul_neg_of_pos_of_neg (sq_pos_of_ne_zero ht0) hneg
  rw [← heq] at hlt
  linarith

theorem exists_tie_preserving_decreasing_curve {G J A B : ℝ × ℝ → ℝ} {b C : ℝ}
    (hb : b ≠ 0) (hG : HasStrictFDerivAt G (b • ContinuousLinearMap.snd ℝ ℝ ℝ) (0, 0))
    (hC : C < 0) (hA : ContinuousAt A (0, 0)) (hB : ContinuousAt B (0, 0))
    (hJ : ∀ z, J z = J (0, 0) + C * z.1 ^ 2 + z.1 * z.2 * A z + z.2 ^ 2 * B z) :
    ∃ s : ℝ → ℝ, s 0 = 0 ∧ HasDerivAt s 0 0 ∧
      (∀ᶠ t in 𝓝 (0 : ℝ), G (t, s t) = G (0, 0)) ∧
      ∀ᶠ t in 𝓝[≠] (0 : ℝ), J (t, s t) < J (0, 0) := by
  obtain ⟨s, hs0, hs, heq⟩ := exists_tie_preserving_curve hb hG
  exact ⟨s, hs0, hs, heq, quadratic_decrease_along_tangent_curve hC hA hB hJ hs0 hs⟩

end

end PoissonBinomialComparison

-- SplitPerturbation
namespace PoissonBinomialComparison

open Finset Filter
open scoped Topology

noncomputable section

variable {ι : Type*} [DecidableEq ι]

theorem randomizedCoefficientOn_insert (p : ι → ℝ) {s : Finset ι} {i : ι}
    (hi : i ∉ s) (w : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    randomizedCoefficientOn p (insert i s) w k = randomizedCoefficientOn p s w k +
      p i * (randomizedCoefficientOn p s w (k - 1) - randomizedCoefficientOn p s w k) := by
  unfold randomizedCoefficientOn
  simp only [show k ≠ 0 by omega, ite_false]
  rw [randomizedSlopeOn_insert p hi, randomizedSlopeOn_insert p hi]
  unfold randomizedCoefficientOn
  simp only [show k ≠ 0 by omega, ite_false]
  ring

theorem randomizedTailOn_insert_three (p : ι → ℝ) {s : Finset ι} {i j l : ι}
    (hi : i ∉ s) (hj : j ∉ s) (hl : l ∉ s)
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) (w : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    randomizedTailOn p (insert i (insert j (insert l s))) w k =
      randomizedTailOn p s w k + (p i + p j + p l) * randomizedSlopeOn p s w k +
      (p i * p j + p i * p l + p j * p l) * randomizedCoefficientOn p s w k +
      p i * p j * p l *
        (randomizedCoefficientOn p s w (k - 1) - randomizedCoefficientOn p s w k) := by
  rw [randomizedTailOn_insert_insert p (by simp [hi, hil]) (by simp [hj, hjl]) hij,
    randomizedTailOn_insert p hl, randomizedSlopeOn_insert p hl,
    randomizedCoefficientOn_insert p hl w hk]
  ring

theorem pbMassIntOn_insert_three (p : ι → ℝ) {s : Finset ι} {i j l : ι}
    (hi : i ∉ s) (hj : j ∉ s) (hl : l ∉ s)
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) (k : ℤ) :
    pbMassIntOn p (insert i (insert j (insert l s))) k =
      pbMassIntOn p s k + (p i + p j + p l) *
        (pbMassIntOn p s (k - 1) - pbMassIntOn p s k) +
      (p i * p j + p i * p l + p j * p l) *
        (pbMassIntOn p s (k - 2) - 2 * pbMassIntOn p s (k - 1) + pbMassIntOn p s k) +
      p i * p j * p l *
        (pbMassIntOn p s (k - 3) - 3 * pbMassIntOn p s (k - 2) +
          3 * pbMassIntOn p s (k - 1) - pbMassIntOn p s k) := by
  simp only [pbMassIntOn_insert p (by simp [hi, hij, hil] : i ∉ insert j (insert l s)),
    pbMassIntOn_insert p (by simp [hj, hjl] : j ∉ insert l s), pbMassIntOn_insert p hl]
  rw [show k - 1 - 1 = k - 2 by omega, show k - 2 - 1 = k - 3 by omega]
  ring

variable {n : ℕ}

def splitTransfer (q : Fin n → ℝ) (i j l : Fin n) (z : ℝ × ℝ) : Fin n → ℝ :=
  Function.update (Function.update (Function.update q i (q i + z.1 + z.2)) j (q j - z.1)) l (q l - z.2)

@[simp] theorem splitTransfer_zero (q : Fin n → ℝ) (i j l : Fin n) :
    splitTransfer q i j l (0, 0) = q := by simp [splitTransfer]

theorem continuous_splitTransfer (q : Fin n → ℝ) (i j l : Fin n) :
    Continuous (splitTransfer q i j l) := by unfold splitTransfer; fun_prop

private theorem splitTransfer_congr (q : Fin n → ℝ) {i j l : Fin n} (z : ℝ × ℝ)
    {s : Finset (Fin n)} (hi : i ∉ s) (hj : j ∉ s) (hl : l ∉ s) :
    ∀ t ∈ s, splitTransfer q i j l z t = q t := by
  intro t ht
  have hti : t ≠ i := fun hh ↦ hi (hh ▸ ht)
  have htj : t ≠ j := fun hh ↦ hj (hh ▸ ht)
  have htl : t ≠ l := fun hh ↦ hl (hh ▸ ht)
  simp [splitTransfer, Function.update_of_ne hti, Function.update_of_ne htj, Function.update_of_ne htl]

private theorem SplitPerturbation_randomizedTailOn_congr' {p q : Fin n → ℝ} {s : Finset (Fin n)}
    (h : ∀ t ∈ s, p t = q t) (w : ℝ) (k : ℕ) :
    randomizedTailOn p s w k = randomizedTailOn q s w k := by
  simp only [randomizedTailOn, pbTailOn_congr h]

private theorem SplitPerturbation_randomizedSlopeOn_congr' {p q : Fin n → ℝ} {s : Finset (Fin n)}
    (h : ∀ t ∈ s, p t = q t) (w : ℝ) (k : ℕ) :
    randomizedSlopeOn p s w k = randomizedSlopeOn q s w k := by
  simp only [randomizedSlopeOn, pbMassOn_congr h]

private theorem SplitPerturbation_randomizedCoefficientOn_congr' {p q : Fin n → ℝ} {s : Finset (Fin n)}
    (h : ∀ t ∈ s, p t = q t) (w : ℝ) (k : ℕ) :
    randomizedCoefficientOn p s w k = randomizedCoefficientOn q s w k := by
  simp only [randomizedCoefficientOn, SplitPerturbation_randomizedSlopeOn_congr' h]

theorem sum_splitTransfer (q : Fin n → ℝ) {i j l : Fin n}
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) (z : ℝ × ℝ) :
    ∑ t, splitTransfer q i j l z t = ∑ t, q t := by
  have hsum (f : Fin n → ℝ) (t : Fin n) (a : ℝ) :
      ∑ x, Function.update f t a x = a + ∑ x, f x - f t := by
    rw [sum_update_of_mem (mem_univ _), sdiff_singleton_eq_erase,
      sum_erase_eq_sub (mem_univ _)]
    ring
  simp only [splitTransfer, hsum, Function.update_of_ne hil.symm,
    Function.update_of_ne hjl.symm, Function.update_of_ne hij.symm]
  ring

theorem randomizedTail_splitTransfer (q : Fin n → ℝ) {i j l : Fin n}
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) (heq : q i = q j)
    {w c : ℝ} {k : ℕ} (hk : 1 ≤ k) (hneq : q i ≠ q l)
    (hGi : randomizedGradient q w k i = c) (hGl : randomizedGradient q w k l = c)
    (z : ℝ × ℝ) :
    let s := (((univ : Finset (Fin n)).erase i).erase j).erase l
    let D := randomizedCoefficientOn q s w (k - 1) - randomizedCoefficientOn q s w k
    randomizedTail (splitTransfer q i j l z) w k - randomizedTail q w k =
      -randomizedMixedCoefficient q w k i j * z.1^2 -
        z.1*z.2*(randomizedMixedCoefficient q w k i j - D*z.1 - D*z.2) := by
  dsimp only
  let s := (((univ : Finset (Fin n)).erase i).erase j).erase l
  let D := randomizedCoefficientOn q s w (k - 1) - randomizedCoefficientOn q s w k
  have hi : i ∉ s := by simp [s]
  have hj : j ∉ s := by simp [s]
  have hl : l ∉ s := by simp [s]
  have hsij : insert l s = (univ.erase i).erase j := by
    apply insert_erase
    simp [hil.symm, hjl.symm]
  have hsil : insert j s = (univ.erase i).erase l := by
    ext t
    by_cases hti : t = i <;> by_cases htj : t = j <;> by_cases htl : t = l <;>
      simp_all [s]
  have hfull : insert i (insert j (insert l s)) = univ := by
    rw [hsij, insert_erase (by simp [hij.symm]), insert_erase (mem_univ i)]
  have hCil : randomizedMixedCoefficient q w k i l = 0 := by
    have hd := randomizedGradient_sub q hil w k
    rw [hGi, hGl, sub_self] at hd
    exact (mul_eq_zero.mp hd.symm).resolve_left (sub_ne_zero.mpr hneq.symm)
  change randomizedCoefficientOn q ((univ.erase i).erase l) w k = 0 at hCil
  rw [← hsil, randomizedCoefficientOn_insert q hj w hk, ← heq] at hCil
  have hbase : randomizedCoefficientOn q s w k = -q i * D := by
    change randomizedCoefficientOn q s w k + q i * D = 0 at hCil
    linarith
  have hCij : randomizedMixedCoefficient q w k i j = randomizedCoefficientOn q s w k + q l * D := by
    change randomizedCoefficientOn q ((univ.erase i).erase j) w k = _
    rw [← hsij, randomizedCoefficientOn_insert q hl w hk]
  have hold := randomizedTailOn_insert_three q hi hj hl hij hil hjl w hk
  have hnew := randomizedTailOn_insert_three (splitTransfer q i j l z) hi hj hl hij hil hjl w hk
  have hcongr := splitTransfer_congr q z hi hj hl
  rw [hfull] at hold hnew
  simp only [SplitPerturbation_randomizedTailOn_congr' hcongr, SplitPerturbation_randomizedSlopeOn_congr' hcongr,
    SplitPerturbation_randomizedCoefficientOn_congr' hcongr] at hnew
  simp only [splitTransfer, Function.update_of_ne hil, Function.update_of_ne hij,
    Function.update_of_ne hjl, Function.update_self] at hnew
  change randomizedTail (splitTransfer q i j l z) w k = _ at hnew
  change randomizedTail q w k = _ at hold
  rw [hnew, hold, hCij]
  change _ = -(randomizedCoefficientOn q s w k + q l * D) * z.1^2 -
    z.1*z.2*(randomizedCoefficientOn q s w k + q l * D - D*z.1 - D*z.2)
  change _ + _ + _ + _ * D - (_ + _ + _ + _ * D) = _
  rw [hbase, ← heq]
  ring

theorem pbMass_splitTransfer (q : Fin n → ℝ) {i j l : Fin n}
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) (heq : q i = q j)
    (k : ℕ) (z : ℝ × ℝ) :
    let s := (((univ : Finset (Fin n)).erase i).erase j).erase l
    let C := pbMassIntOn q s ((k : ℤ) - 2) - 2 * pbMassIntOn q s ((k : ℤ) - 1) + pbMassIntOn q s k
    let D := pbMassIntOn q s ((k : ℤ) - 3) - 3 * pbMassIntOn q s ((k : ℤ) - 2) +
      3 * pbMassIntOn q s ((k : ℤ) - 1) - pbMassIntOn q s k
    pbMass (splitTransfer q i j l z) k - pbMass q k =
      (q l - q i) * (C + q i * D) * z.2 - (C + q l * D) * z.1^2 -
      (C + q l * D) * z.1*z.2 - (C + q i * D) * z.2^2 + D*z.1^2*z.2 + D*z.1*z.2^2 := by
  dsimp only
  let s := (((univ : Finset (Fin n)).erase i).erase j).erase l
  have hi : i ∉ s := by simp [s]
  have hj : j ∉ s := by simp [s]
  have hl : l ∉ s := by simp [s]
  have hsij : insert l s = (univ.erase i).erase j := by
    apply insert_erase
    simp [hil.symm, hjl.symm]
  have hfull : insert i (insert j (insert l s)) = univ := by
    rw [hsij, insert_erase (by simp [hij.symm]), insert_erase (mem_univ i)]
  have hold := pbMassIntOn_insert_three q hi hj hl hij hil hjl (k : ℤ)
  have hnew := pbMassIntOn_insert_three (splitTransfer q i j l z) hi hj hl hij hil hjl (k : ℤ)
  have hcongr := splitTransfer_congr q z hi hj hl
  rw [hfull, pbMassIntOn_natCast] at hold hnew
  simp only [pbMassIntOn_congr hcongr] at hnew
  simp only [splitTransfer, Function.update_of_ne hil, Function.update_of_ne hij,
    Function.update_of_ne hjl, Function.update_self] at hnew
  change pbMass (splitTransfer q i j l z) k = _ at hnew
  change pbMass q k = _ at hold
  rw [hnew, hold, ← heq]
  ring

theorem hasStrictFDerivAt_pbMass_splitTransfer (q : Fin n → ℝ) {i j l : Fin n}
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) (heq : q i = q j) (k : ℕ) :
    HasStrictFDerivAt (fun z ↦ pbMass (splitTransfer q i j l z) k)
      (((q l - q i) *
        (pbMassIntOn q ((univ.erase i).erase l) ((k : ℤ) - 2) -
          2 * pbMassIntOn q ((univ.erase i).erase l) ((k : ℤ) - 1) +
            pbMassIntOn q ((univ.erase i).erase l) k)) • ContinuousLinearMap.snd ℝ ℝ ℝ) (0, 0) := by
  let s := (((univ : Finset (Fin n)).erase i).erase j).erase l
  let C := pbMassIntOn q s ((k : ℤ) - 2) - 2 * pbMassIntOn q s ((k : ℤ) - 1) + pbMassIntOn q s k
  let D := pbMassIntOn q s ((k : ℤ) - 3) - 3 * pbMassIntOn q s ((k : ℤ) - 2) +
      3 * pbMassIntOn q s ((k : ℤ) - 1) - pbMassIntOn q s k
  have hj : j ∉ s := by simp [s]
  have hsil : insert j s = (univ.erase i).erase l := by
    ext t
    by_cases hti : t = i <;> by_cases htj : t = j <;> by_cases htl : t = l <;>
      simp_all [s]
  have hcoef : pbMassIntOn q ((univ.erase i).erase l) ((k : ℤ) - 2) -
      2 * pbMassIntOn q ((univ.erase i).erase l) ((k : ℤ) - 1) +
        pbMassIntOn q ((univ.erase i).erase l) k = C + q i * D := by
    rw [← hsil]
    simp only [pbMassIntOn_insert q hj]
    dsimp [C, D]
    rw [show (k : ℤ) - 2 - 1 = (k : ℤ) - 3 by omega,
      show (k : ℤ) - 1 - 1 = (k : ℤ) - 2 by omega, ← heq]
    ring
  rw [hcoef]
  have ht : HasStrictFDerivAt (fun z : ℝ × ℝ ↦ z.1)
      (ContinuousLinearMap.fst ℝ ℝ ℝ) (0, 0) := hasStrictFDerivAt_fst
  have hs : HasStrictFDerivAt (fun z : ℝ × ℝ ↦ z.2)
      (ContinuousLinearMap.snd ℝ ℝ ℝ) (0, 0) := hasStrictFDerivAt_snd
  have hpoly := ((((((hasStrictFDerivAt_const (pbMass q k) (0, 0)).add
    (hs.const_mul ((q l - q i) * (C + q i * D)))).sub
    ((ht.mul ht).const_mul (C + q l * D))).sub
    ((ht.mul hs).const_mul (C + q l * D))).sub
    ((hs.mul hs).const_mul (C + q i * D))).add
    (((ht.mul ht).mul hs).const_mul D)).add (((ht.mul hs).mul hs).const_mul D)
  simp only [Pi.mul_apply, mul_zero, zero_smul,
    smul_zero, zero_add, add_zero, sub_zero] at hpoly
  convert! hpoly using 1
  · funext z
    have hh := pbMass_splitTransfer q hij hil hjl heq k z
    change pbMass (splitTransfer q i j l z) k - pbMass q k =
      (q l - q i) * (C + q i * D) * z.2 - (C + q l * D) * z.1^2 -
      (C + q l * D) * z.1*z.2 - (C + q i * D) * z.2^2 + D*z.1^2*z.2 + D*z.1*z.2^2 at hh
    dsimp
    nlinarith only [hh]

theorem splitTransfer_eventually_feasible {p q : Fin n → ℝ} (h : AdmissiblePair p q)
    {i j l : Fin n} (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    (hi0 : 0 < q i) (hj0 : 0 < q j) (hl0 : 0 < q l)
    (hi : q i < p i) (hj : q j < p j) (hl : q l < p l) :
    ∀ᶠ z in 𝓝 ((0, 0) : ℝ × ℝ), (p, splitTransfer q i j l z) ∈
      feasiblePairs n (meanGap p q) := by
  have hcoords : ∀ t : Fin n, ∀ᶠ z in 𝓝 ((0, 0) : ℝ × ℝ),
      0 ≤ splitTransfer q i j l z t ∧ splitTransfer q i j l z t ≤ p t := by
    intro t
    by_cases ht : t = i ∨ t = j ∨ t = l
    · have h0 : 0 < q t := by rcases ht with rfl | rfl | rfl <;> assumption
      have h1 : q t < p t := by rcases ht with rfl | rfl | rfl <;> assumption
      have hct : ContinuousAt (fun z ↦ splitTransfer q i j l z t) (0, 0) :=
        ((continuous_apply t).comp (continuous_splitTransfer q i j l)).continuousAt
      have he0 := continuousAt_const.eventually_lt hct (by simpa using h0)
      have he1 := hct.eventually_lt continuousAt_const (by simpa using h1)
      filter_upwards [he0, he1] with z hz0 hz1
      exact ⟨hz0.le, hz1.le⟩
    · push Not at ht
      exact Eventually.of_forall fun z ↦ by
        simpa [splitTransfer, Function.update_of_ne ht.1, Function.update_of_ne ht.2.1,
          Function.update_of_ne ht.2.2] using And.intro (h.2.1 t).1 (h.2.2 t)
  have hall := (eventually_all).mpr hcoords
  filter_upwards [hall] with z hz
  refine ⟨⟨h.1, ?_, ?_⟩, ?_⟩
  · intro t
    exact ⟨(hz t).1, (hz t).2.trans (h.1 t).2⟩
  · exact fun t ↦ (hz t).2
  · simp only [meanGap, sum_splitTransfer q hij hil hjl]

theorem eq_of_repeated_smaller_at_localMin {p q : Fin n → ℝ}
    (h : AdmissiblePair p q)
    (hmin : IsLocalMinOn (fun x : (Fin n → ℝ) × (Fin n → ℝ) ↦ tailObjective x.1 x.2)
      (feasiblePairs n (meanGap p q)) (p, q))
    {k : ℕ} (hk : 1 ≤ k) {w c : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hc : 0 < c)
    (hactive : (activeThresholds p q = {k} ∧ w = 1) ∨ activeThresholds p q = {k, k + 1})
    {i j l : Fin n} (hi0 : 0 < q i) (heq : q i = q j) (hlt : q i < q l)
    (hi : q i < p i) (hj : q j < p j) (hl : q l < p l)
    (hGi : randomizedGradient q w k i = c) (hGl : randomizedGradient q w k l = c) : i = j := by
  by_contra hij
  have hil : i ≠ l := fun hh ↦ hlt.ne (congrArg q hh)
  have hjl : j ≠ l := by intro hh; exact hlt.ne (heq.trans (congrArg q hh))
  let G : ℝ × ℝ → ℝ := fun z ↦ pbMass p k - pbMass (splitTransfer q i j l z) k
  let J : ℝ × ℝ → ℝ := fun z ↦ randomizedTail p w k - randomizedTail (splitTransfer q i j l z) w k
  let b := -(q l - q i) * (pbMassIntOn q ((univ.erase i).erase l) ((k : ℤ) - 2) -
      2 * pbMassIntOn q ((univ.erase i).erase l) ((k : ℤ) - 1) +
        pbMassIntOn q ((univ.erase i).erase l) k)
  let C := randomizedMixedCoefficient q w k i j
  let s0 := (((univ : Finset (Fin n)).erase i).erase j).erase l
  let D := randomizedCoefficientOn q s0 w (k - 1) - randomizedCoefficientOn q s0 w k
  have hb : b ≠ 0 := mass_tie_transfer_coefficient_ne_zero h.2.1 hc k hlt.ne hGi hGl
  have hG : HasStrictFDerivAt G (b • ContinuousLinearMap.snd ℝ ℝ ℝ) (0, 0) := by
    have hd := (hasStrictFDerivAt_pbMass_splitTransfer q hij hil hjl heq k).const_sub (pbMass p k)
    convert! hd using 1
    dsimp [b]
    apply ContinuousLinearMap.ext
    intro z
    simp only [smul_apply, neg_apply, smul_eq_mul]
    ring
  have hC : C < 0 := randomizedMixedCoefficient_neg_of_repeated_smaller h.2.1 hw0 hw1 hc
    k hij heq hlt hGi hGl
  have hJ : ∀ z, J z = J (0, 0) + C*z.1^2 + z.1*z.2*(C-D*z.1-D*z.2) + z.2^2*0 := by
    intro z
    have hh := randomizedTail_splitTransfer q hij hil hjl heq hk hlt.ne hGi hGl z
    change randomizedTail (splitTransfer q i j l z) w k - randomizedTail q w k =
      -C*z.1^2-z.1*z.2*(C-D*z.1-D*z.2) at hh
    dsimp [J]
    rw [splitTransfer_zero]
    linarith
  obtain ⟨s, hs0, hs, htie, hdec⟩ := exists_tie_preserving_decreasing_curve hb hG hC
    (by fun_prop : ContinuousAt (fun z : ℝ × ℝ ↦ C-D*z.1-D*z.2) (0, 0))
    continuousAt_const hJ
  have hcurve : Tendsto (fun t ↦ (t, s t)) (𝓝 (0 : ℝ)) (𝓝 (0, 0)) := by
    exact tendsto_id.prodMk_nhds (by simpa [hs0] using hs.continuousAt.tendsto)
  let Q := fun t ↦ splitTransfer q i j l (t, s t)
  have hQ : Tendsto (fun t ↦ (p, Q t)) (𝓝 (0 : ℝ)) (𝓝 (p, q)) := by
    have hQt := (continuous_splitTransfer q i j l).continuousAt.tendsto.comp hcurve
    simpa only [Function.comp_def, splitTransfer_zero, Q] using tendsto_const_nhds.prodMk_nhds hQt
  have hfeas := (splitTransfer_eventually_feasible h hij hil hjl hi0
    (heq ▸ hi0) (hi0.trans hlt) hi hj hl).filter_mono hcurve
  have hwithin : Tendsto (fun t ↦ (p, Q t)) (𝓝[≠] (0 : ℝ))
      (𝓝[feasiblePairs n (meanGap p q)] (p, q)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hQ.mono_left nhdsWithin_le_nhds,
      hfeas.filter_mono nhdsWithin_le_nhds⟩
  have hle : ∀ᶠ t in 𝓝[≠] (0 : ℝ), tailObjective p q ≤ tailObjective p (Q t) :=
    hwithin.eventually hmin
  have hkm : k ∈ activeThresholds p q := by
    rcases hactive with ⟨hh, _⟩ | hh <;> simp [hh]
  have hkr : k ∈ Icc 1 n := mem_Icc.mpr ⟨hk, ((mem_activeThresholds p q k).mp hkm).2.1⟩
  have hbase : J (0, 0) = tailObjective p q := by
    dsimp [J]
    rw [splitTransfer_zero, randomizedDiff_eq]
    have he := ((mem_activeThresholds p q k).mp hkm).2.2
    rcases hactive with ⟨_, rfl⟩ | hh
    · simpa using he
    · have hk1 : k + 1 ∈ activeThresholds p q := by simp [hh]
      rw [he, ((mem_activeThresholds p q (k+1)).mp hk1).2.2]
      ring
  have hobj : ∀ᶠ t in 𝓝 (0 : ℝ), tailObjective p (Q t) = J (t, s t) := by
    rcases hactive with ⟨hh, hw⟩ | hh
    · have hloc := tailObjective_eventually_eq_max hkm hkr (by simp [hh])
      have he := hQ.eventually hloc
      filter_upwards [he] with t ht
      simpa [J, randomizedDiff_eq, hw] using ht
    · have hk1 : k + 1 ∈ activeThresholds p q := by simp [hh]
      have hk1r : k + 1 ∈ Icc 1 n := mem_Icc.mpr
        ⟨by omega, ((mem_activeThresholds p q (k+1)).mp hk1).2.1⟩
      have hloc := tailObjective_eventually_eq_max hkm hk1r (by rw [hh])
      have htie0 : G (0, 0) = 0 := by
        have hd := tailDiff_sub_succ p q k
        rw [((mem_activeThresholds p q k).mp hkm).2.2,
          ((mem_activeThresholds p q (k+1)).mp hk1).2.2] at hd
        simpa [G] using hd.symm
      filter_upwards [hQ.eventually hloc, htie] with t ht hgt
      have hmass : pbMass p k - pbMass (Q t) k = 0 := hgt.trans htie0
      have hdiff : tailDiff p (Q t) k = tailDiff p (Q t) (k+1) := by
        have hd := tailDiff_sub_succ p (Q t) k
        linarith
      rw [hdiff, max_self] at ht
      change tailObjective p (Q t) = randomizedTail p w k - randomizedTail (Q t) w k
      rw [ht, randomizedDiff_eq, hdiff]
      ring
  obtain ⟨t, ht⟩ := (hle.and (hdec.and (hobj.filter_mono nhdsWithin_le_nhds))).exists
  rw [ht.2.2, ← hbase] at ht
  exact not_lt_of_ge ht.1 ht.2.1

end

end PoissonBinomialComparison

-- GlobalHomogeneity
namespace PoissonBinomialComparison

open Finset

noncomputable section

variable {n : ℕ} {p q : Fin n → ℝ}

theorem IsGapMinimizer.lower_constant_of_upper_constant_of_no_smaller_repeat
    (hn : 3 ≤ n)
    (hind : ∀ r s : Fin (n - 1) → ℝ, AdmissiblePair r s →
      benchmark (n - 1) (meanGap r s) ≤ tailObjective r s)
    (h : AdmissiblePair p q) (hm : IsGapMinimizer p q)
    (hg0 : 0 < meanGap p q) (hgn : meanGap p q < n)
    {a : ℝ} (hpa : ∀ i, q i < p i → p i = a)
    (hsmall : ∀ i j l, q i < p i → q j < p j → q l < p l →
      0 < q i → q i = q j → q i < q l → i = j) :
    ∃ b : ℝ, 0 < b ∧ b < a ∧ ∀ i, q i < p i → q i = b := by
  classical
  have ha := hm.upper_changing_constant_interior hn hind h hg0 hgn hpa
  have hb := hm.parameter_bounds hn hind h hg0
  obtain ⟨k, w, c, _, _, hw0, hw1, hc, hk, hlast, _, hchange, hcomm⟩ :=
    exists_tail_kkt h (fun i ↦ (hb i).1) (fun i ↦ (hb i).2) hg0
      (hm.tailObjective_lt_one hn hg0 hgn) hm.isLocalMinOn
  have hgrad : ∀ i, p i = q i → randomizedGradient p w k i = randomizedGradient q w k i ∧
      c ≤ randomizedGradient p w k i := by
    intro i hi
    obtain ⟨ν, hν, hpν, hqν⟩ := hcomm i hi
    exact ⟨hpν.trans hqν.symm, by linarith⟩
  have hcommon : ∀ i, p i = q i → p i = w := by
    intro i hi
    obtain ⟨_, _, _, _, _, _, hall⟩ := common_coordinates_of_kkt hn hind h hm hg0
      (fun i ↦ (hb i).1) (fun i ↦ (hb i).2) hw0 hw1 hc hk hlast ⟨i, hi⟩ hgrad
    exact (hall i hi).1
  let I := positiveGapCoordinates p q
  let C := univ \ I
  have hI : ∀ i, i ∈ I ↔ q i < p i := by simp [I, positiveGapCoordinates]
  have hC : ∀ i, i ∈ C ↔ p i = q i := by
    intro i
    simp only [C, mem_sdiff, mem_univ, true_and, hI]
    exact ⟨fun hn ↦ le_antisymm (le_of_not_gt hn) (h.2.2 i), fun heq ↦ by rw [heq]; exact lt_irrefl _⟩
  have hpart : univ = C ∪ I := by simp [C]
  have hCI : Disjoint C I := by
    apply disjoint_left.mpr
    intro i hiC hiI
    exact (mem_sdiff.mp hiC).2 hiI
  have hcard : 3 ≤ I.card := hm.three_le_positiveGapCoordinates hn h hg0 hgn
  obtain ⟨b, _, hba, hqb⟩ := lower_changing_coordinates_constant h.2.1 I C hpart hCI hcard
    ⟨hw0, hw1⟩ ha.2 hc k
    (fun i hi ↦ hcommon i ((hC i).mp hi))
    (fun i hi ↦ ((hC i).mp hi).symm.trans (hcommon i ((hC i).mp hi)))
    (fun i hi ↦ hpa i ((hI i).mp hi))
    (fun i hi ↦ by rw [← hpa i ((hI i).mp hi)]; exact (hI i).mp hi)
    (fun i hi ↦ (hchange i ((hI i).mp hi)).2.2.1 (by rw [hpa i ((hI i).mp hi)]; exact ha.2))
    (fun i hi hqi ↦ (hchange i ((hI i).mp hi)).2.2.2 hqi)
    (fun i hi _ ↦ (hchange i ((hI i).mp hi)).2.1)
    (fun i hi j hj l hl ↦ hsmall i j l ((hI i).mp hi) ((hI j).mp hj) ((hI l).mp hl))
  have hqb' : ∀ i, q i < p i → q i = b := fun i hi ↦ hqb i ((hI i).mpr hi)
  exact ⟨b, (hm.lower_changing_constant_interior hn hind h hg0 hgn hqb').1, hba, hqb'⟩

theorem IsGapMinimizer.no_repeated_smaller_lower (hn : 3 ≤ n)
    (hind : ∀ r s : Fin (n - 1) → ℝ, AdmissiblePair r s →
      benchmark (n - 1) (meanGap r s) ≤ tailObjective r s)
    (h : AdmissiblePair p q) (hm : IsGapMinimizer p q)
    (hg0 : 0 < meanGap p q) (hgn : meanGap p q < n) :
    ∀ i j l, q i < p i → q j < p j → q l < p l →
      0 < q i → q i = q j → q i < q l → i = j := by
  have hb := hm.parameter_bounds hn hind h hg0
  obtain ⟨k, w, c, hk0, _, hw0, hw1, hc, _, _, _, hset, hchange, _⟩ :=
    exists_tail_kkt_with_activeSet h (fun i ↦ (hb i).1) (fun i ↦ (hb i).2) hg0
      (hm.tailObjective_lt_one hn hg0 hgn) hm.isLocalMinOn
  intro i j l hi hj hl hi0 heq hlt
  exact eq_of_repeated_smaller_at_localMin h hm.isLocalMinOn hk0 hw0 hw1 hc hset
    hi0 heq hlt hi hj hl ((hchange i hi).2.2.2 hi0) ((hchange l hl).2.2.2 (hi0.trans hlt))

theorem IsGapMinimizer.lower_constant_of_upper_constant (hn : 3 ≤ n)
    (hind : ∀ r s : Fin (n - 1) → ℝ, AdmissiblePair r s →
      benchmark (n - 1) (meanGap r s) ≤ tailObjective r s)
    (h : AdmissiblePair p q) (hm : IsGapMinimizer p q)
    (hg0 : 0 < meanGap p q) (hgn : meanGap p q < n)
    {a : ℝ} (hpa : ∀ i, q i < p i → p i = a) :
    ∃ b : ℝ, 0 < b ∧ b < a ∧ ∀ i, q i < p i → q i = b :=
  hm.lower_constant_of_upper_constant_of_no_smaller_repeat hn hind h hg0 hgn hpa
    (hm.no_repeated_smaller_lower hn hind h hg0 hgn)

theorem IsGapMinimizer.homogeneous (hn : 3 ≤ n)
    (hind : ∀ r s : Fin (n - 1) → ℝ, AdmissiblePair r s →
      benchmark (n - 1) (meanGap r s) ≤ tailObjective r s)
    (h : AdmissiblePair p q) (hm : IsGapMinimizer p q)
    (hg0 : 0 < meanGap p q) (hgn : meanGap p q < n) :
    ∃ a b : ℝ, 0 < b ∧ b < a ∧ a < 1 ∧ p = (fun _ ↦ a) ∧ q = (fun _ ↦ b) := by
  rcases hm.one_changing_vector_constant hn hind h hg0 hgn with ⟨a, hpa⟩ | ⟨b, hqb⟩
  · obtain ⟨b, hb0, hba, hqb⟩ := hm.lower_constant_of_upper_constant hn hind h hg0 hgn hpa
    have ha := hm.upper_changing_constant_interior hn hind h hg0 hgn hpa
    exact ⟨a, b, hb0, hba, ha.2, hm.homogeneous_of_changing_constants hn hind h hg0 hgn hpa hqb⟩
  · have hpa' : ∀ i, 1 - p i < 1 - q i → 1 - q i = 1 - b := by
      intro i hi
      rw [hqb i (by linarith)]
    obtain ⟨b', hb'0, hb'a, hqb'⟩ := hm.reflection.lower_constant_of_upper_constant hn hind
      (admissiblePair_reflection h) (by simpa only [meanGap_reflection] using hg0)
      (by simpa only [meanGap_reflection] using hgn) hpa'
    have hpa : ∀ i, q i < p i → p i = 1 - b' := by
      intro i hi
      have hh := hqb' i (by linarith)
      linarith
    have hb := hm.lower_changing_constant_interior hn hind h hg0 hgn hqb
    refine ⟨1 - b', b, hb.1, ?_, ?_, hm.homogeneous_of_changing_constants hn hind h hg0 hgn hpa hqb⟩
    · linarith
    · linarith

end

end PoissonBinomialComparison

-- BenchmarkAttainment
namespace PoissonBinomialComparison

noncomputable section

theorem benchmark_two {Δ : ℝ} (h0 : 0 ≤ Δ) (h2 : Δ ≤ 2) :
    benchmark 2 Δ = Δ / 2 := by
  rcases eq_or_lt_of_le h0 with h | hpos
  · subst Δ
    norm_num [benchmark_zero]
  rcases eq_or_lt_of_le h2 with h | hlt
  · subst Δ
    norm_num [benchmark]
  have ht : ∀ t : ℝ, pbTail (fun _ : Fin 2 ↦ t) 1 = 2*t - t^2 := by
    intro t
    norm_num [pbTail_const, Finset.sum_Icc_succ_top]
    ring
  have hs := switchPair_even (m := 1) (by decide) (γ := Δ / 2)
    (by linarith) (by linarith)
  rw [benchmark_eq_switchValue hpos (by simpa using hlt)]
  change tailDiff (fun _ : Fin 2 ↦ switchUpper 2 1 (Δ/2)) (fun _ ↦ switchLower 2 1 (Δ/2)) 1 = Δ/2
  rw [tailDiff, hs.1, hs.2, ht, ht]
  ring

theorem benchmark_le_of_homogeneous_minimizers {n : ℕ} (hn : 2 ≤ n)
    (hhom : ∀ p q : Fin n → ℝ, AdmissiblePair p q → IsGapMinimizer p q →
      0 < meanGap p q → meanGap p q < n →
      ∃ a b : ℝ, p = (fun _ ↦ a) ∧ q = (fun _ ↦ b))
    {p q : Fin n → ℝ} (h : AdmissiblePair p q) :
    benchmark n (meanGap p q) ≤ tailObjective p q := by
  have hg0 := meanGap_nonneg h
  have hgn := meanGap_le_dimension h
  rcases hg0.eq_or_lt with hz | hpos
  · rw [← hz,benchmark_zero,tailObjective_eq_zero_of_meanGap_eq_zero h hz.symm]
  rcases hgn.eq_or_lt with heq | hlt
  · rw [heq,benchmark_at_dimension (by omega),
      tailObjective_eq_one_of_meanGap_eq_dimension h (by omega) heq]
  · obtain ⟨r,s,hrs,hgap,hmin⟩ := exists_tailObjective_minimizer (meanGap p q) hg0 hgn
    have hm : IsGapMinimizer r s := by
      intro u v huv hδ
      exact hmin u v huv (hδ.trans hgap)
    obtain ⟨a,b,rfl,rfl⟩ := hhom r s hrs hm (hgap ▸ hpos) (hgap ▸ hlt)
    have hi : Fin n := ⟨0,by omega⟩
    have hh := homogeneous_minimum hn (hrs.2.1 hi).1 (hrs.2.2 hi) (hrs.1 hi).2
    rw [← meanGap_const,hgap] at hh
    exact hh.trans (hmin p q h rfl)

end

end PoissonBinomialComparison

-- GlobalComparison
namespace PoissonBinomialComparison

noncomputable section

theorem benchmark_le_tailObjective {n : ℕ} (hn : 2 ≤ n)
    {p q : Fin n → ℝ} (h : AdmissiblePair p q) :
    benchmark n (meanGap p q) ≤ tailObjective p q := by
  induction n, hn using Nat.le_induction with
  | base =>
    rw [benchmark_two (meanGap_nonneg h) (by simpa using meanGap_le_dimension h)]
    exact twoDimensional_lower_bound p q
  | succ n hn ih =>
    apply benchmark_le_of_homogeneous_minimizers (by omega) ?_ h
    intro r s hrs hm hg0 hgn
    have hind : ∀ u v : Fin (n+1-1) → ℝ, AdmissiblePair u v →
        benchmark (n+1-1) (meanGap u v) ≤ tailObjective u v := by
      rw [show n+1-1=n by omega]
      exact fun _ _ huv ↦ ih huv
    obtain ⟨a,b,_,_,_,hp,hq⟩ := hm.homogeneous (by omega) hind hrs hg0 hgn
    exact ⟨a,b,hp,hq⟩

end

end PoissonBinomialComparison

namespace PoissonBoardWork

open OMA.S_mo_477402 PoissonBinomialComparison

theorem tail_eq_pbTail {n : ℕ} (p : Fin n → ℝ) (k : ℕ) :
    tail p k = pbTail p k := by
  simp only [tail, pbTail, pbTailOn, bernoulliWeight, Finset.powerset_univ,
    Finset.sum_filter, Finset.compl_eq_univ_sdiff]

theorem meanGap_eq_sum_sub {n : ℕ} (p q : Fin n → ℝ) :
    meanGap p q = ∑ i, (p i - q i) :=
  (Finset.sum_sub_distrib p q).symm

theorem exists_threshold_of_le_objective {n : ℕ} {p q : Fin n → ℝ} {b : ℝ}
    (hn : 0 < n) (h : b ≤ tailObjective p q) :
    ∃ k ∈ Finset.range (n+2), b ≤ |tail p k - tail q k| := by
  obtain ⟨k, hk, hmax⟩ := Finset.exists_mem_eq_sup'
    (Finset.nonempty_Icc.mpr hn) (tailDiff p q)
  have hle : k ≤ n := (Finset.mem_Icc.mp hk).2
  refine ⟨k, Finset.mem_range.mpr (by omega), ?_⟩
  rw [tailObjective, dif_pos hn, hmax] at h
  rw [tail_eq_pbTail, tail_eq_pbTail]
  exact h.trans (le_abs_self _)

end PoissonBoardWork

namespace PoissonBoardWork

open PoissonBinomialComparison OMA.S_mo_477402

private theorem binTail_eq_pbTail_const (n k : ℕ) (t : ℝ) :
    binTail n t k = pbTail (fun _ : Fin n ↦ t) k :=
  (pbTail_const n k t).symm

private theorem board_benchmark_even (n : ℕ) (hn : 2 ≤ n) (he : Even n)
    (d : ℝ) (hd0 : 0 ≤ d) (hdn : d ≤ n) :
    binTail n (1 / 2 + (d / n) / 2) (n / 2) -
      binTail n (1 / 2 - (d / n) / 2) (n / 2) = benchmark n d := by
  obtain ⟨m, hm⟩ := he
  have hn' : n = 2 * m := by omega
  clear hm
  subst n
  have hmpos : 0 < m := by omega
  have hnpos : 0 < 2 * m := by omega
  have hnreal : (0 : ℝ) < ((2 * m : ℕ) : ℝ) := by exact_mod_cast hnpos
  simp only [show 2 * m / 2 = m by omega, binTail_eq_pbTail_const]
  rcases eq_or_lt_of_le hd0 with hzero | hpos
  · subst d
    simp [benchmark_zero]
  rcases eq_or_lt_of_le hdn with hfull | hlt
  · subst d
    rw [div_self hnreal.ne', benchmark_at_dimension hnpos]
    norm_num only
    rw [pbTail_const_one, pbTail_const_zero]
    simp [show m ≤ 2 * m by omega, hmpos.ne']
  · have hs := switchPair_even hmpos (div_pos hpos hnreal) ((div_lt_one hnreal).mpr hlt)
    rw [benchmark_eq_switchValue hpos hlt, show 2 * m / 2 = m by omega,
      switchValue, tailDiff, hs.1, hs.2]
    rw [show (1 : ℝ) / 2 + d / (2 * m : ℕ) / 2 = (1 + d / (2 * m : ℕ)) / 2 by ring,
      show (1 : ℝ) / 2 - d / (2 * m : ℕ) / 2 = (1 - d / (2 * m : ℕ)) / 2 by ring]

end PoissonBoardWork

open PoissonBinomialComparison PoissonBoardWork in
theorem OMA.solution : type_of% @OMA.S_mo_477402.main := by
  intro n p q hn he hpq
  have h : AdmissiblePair p q := (admissiblePair_iff p q).mpr hpq
  dsimp only
  apply exists_threshold_of_le_objective (by omega)
  rw [← meanGap_eq_sum p q,
    board_benchmark_even n hn he _ (meanGap_nonneg h) (meanGap_le_dimension h)]
  exact benchmark_le_tailObjective hn h
