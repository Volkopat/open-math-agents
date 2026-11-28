import OMAStatements.S_oeis_a177258

-- Problem: A177258: Number of derangements of {1,2,...,n} having no adjacent transpositions.
-- Upstream: formal-conjectures statements/oeis-a177258.lean:0 (declaration OMA.S_oeis_a177258.main)
-- Credit: @thtsben2 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.Proof_oeis_a177258

open OMA.S_oeis_a177258
open scoped BigOperators

private lemma choose_sub_succ_eq (n s : ℕ) :
    (n + 1 - s).choose (s + 1) = (n - s).choose (s + 1) + (n - s).choose s := by
  by_cases h : s ≤ n
  · rw [show n + 1 - s = (n - s) + 1 by omega, Nat.choose_succ_succ, add_comm]
  · have hs : 0 < s := by omega
    rw [Nat.choose_eq_zero_of_lt (by omega), Nat.choose_eq_zero_of_lt (by omega),
      Nat.choose_eq_zero_of_lt (by omega)]

private lemma mul_sub_choose (a t : ℕ) :
    (a + 1 - t) * (a + 1).choose t = (a + 1) * a.choose t := by
  by_cases ht0 : t = 0
  · subst ht0; simp
  · by_cases hta : a + 1 < t
    · rw [Nat.choose_eq_zero_of_lt hta, Nat.choose_eq_zero_of_lt (by omega)]; ring
    · by_cases hteq : t = a + 1
      · subst hteq; simp
      · have hle : t ≤ a := by omega
        have hle1 : t ≤ a + 1 := by omega
        rw [← Nat.choose_symm hle1, ← Nat.choose_symm hle]
        have hsub : a + 1 - t = (a - t) + 1 := by omega
        rw [hsub, Nat.mul_comm, Nat.add_one_mul_choose_eq a (a - t), Nat.mul_comm]

private lemma succ_mul_choose_sub (n s : ℕ) :
    (s + 1) * (n + 1 - s).choose (s + 1) = (n + 1 - s) * (n - s).choose s := by
  by_cases h : s ≤ n
  · rw [show n + 1 - s = (n - s) + 1 by omega, Nat.mul_comm (s + 1),
      ← Nat.add_one_mul_choose_eq (n - s) s]
  · have hs : 0 < s := by omega
    rw [Nat.choose_eq_zero_of_lt (by omega), Nat.choose_eq_zero_of_lt (by omega)]
    ring

private def w (n : ℕ) : ℤ :=
  ∑ t ∈ Finset.range (n + 1), (-1 : ℤ) ^ t * ((n - t).choose t : ℤ)

private lemma w_add_two (n : ℕ) : w (n + 2) = w (n + 1) - w n := by
  unfold w
  rw [Finset.sum_range_succ' (fun t => (-1 : ℤ) ^ t * ((n + 2 - t).choose t : ℤ)) (n + 2)]
  simp only [Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one]
  have hterm : ∀ s ∈ Finset.range (n + 2),
      (-1 : ℤ) ^ (s + 1) * ((n + 2 - (s + 1)).choose (s + 1) : ℤ) =
        (-((-1 : ℤ) ^ s * ((n - s).choose (s + 1) : ℤ))) +
        (-((-1 : ℤ) ^ s * ((n - s).choose s : ℤ))) := by
    intro s _
    rw [show n + 2 - (s + 1) = n + 1 - s by omega, choose_sub_succ_eq n s,
      pow_succ', Nat.cast_add]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
  simp only [Finset.sum_neg_distrib]
  rw [Finset.sum_range_succ (fun s => (-1 : ℤ) ^ s * ((n - s).choose (s + 1) : ℤ)) (n + 1)]
  rw [Finset.sum_range_succ (fun s => (-1 : ℤ) ^ s * ((n - s).choose s : ℤ)) (n + 1)]
  have hzero1 : ((n - (n + 1)).choose (n + 2) : ℤ) = 0 := by
    rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]
  have hzero2 : ((n - (n + 1)).choose (n + 1) : ℤ) = 0 := by
    rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]
  rw [hzero1, hzero2, mul_zero, add_zero, add_zero]
  have hw1 : ∑ t ∈ Finset.range (n + 2), (-1 : ℤ) ^ t * ((n + 1 - t).choose t : ℤ) =
      1 - ∑ s ∈ Finset.range (n + 1), (-1 : ℤ) ^ s * ((n - s).choose (s + 1) : ℤ) := by
    rw [Finset.sum_range_succ' (fun t => (-1 : ℤ) ^ t * ((n + 1 - t).choose t : ℤ)) (n + 1)]
    simp only [Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one]
    have hsub1 : ∀ s ∈ Finset.range (n + 1),
        (-1 : ℤ) ^ (s + 1) * ((n + 1 - (s + 1)).choose (s + 1) : ℤ) =
          -((-1 : ℤ) ^ s * ((n - s).choose (s + 1) : ℤ)) := by
      intro s _
      rw [show n + 1 - (s + 1) = n - s by omega, pow_succ']
      ring
    rw [Finset.sum_congr rfl hsub1, Finset.sum_neg_distrib]
    ring
  rw [hw1]
  ring

private def u (n : ℕ) : ℤ := (-1 : ℤ) ^ n * w n

private lemma u_add_two (n : ℕ) : u (n + 2) + u (n + 1) + u n = 0 := by
  simp only [u, w_add_two, pow_add]
  ring

private lemma u_eq_sum (n : ℕ) :
    u n = ∑ t ∈ Finset.range (n + 1),
      (-1 : ℤ) ^ t * (((n - t).choose t : ℤ) * (-1 : ℤ) ^ (n - 2 * t)) := by
  unfold u w
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  by_cases h : 2 * t ≤ n
  · have hpow : (-1 : ℤ) ^ n = (-1 : ℤ) ^ (n - 2 * t) := by
      calc (-1 : ℤ) ^ n = (-1 : ℤ) ^ ((n - 2 * t) + 2 * t) := by rw [Nat.sub_add_cancel h]
        _ = (-1 : ℤ) ^ (n - 2 * t) * ((-1 : ℤ) ^ 2) ^ t := by rw [pow_add, pow_mul]
        _ = (-1 : ℤ) ^ (n - 2 * t) := by norm_num
    rw [hpow]
    ring
  · have hlt : n - t < t := by omega
    rw [Nat.choose_eq_zero_of_lt hlt, Nat.cast_zero]
    ring

private def b (n : ℕ) : ℤ :=
  ∑ t ∈ Finset.range (n + 1),
    (-1 : ℤ) ^ t * (((n - t).choose t : ℤ) * (numDerangements (n - 2 * t) : ℤ))

private def R (n : ℕ) : ℤ :=
  ∑ t ∈ Finset.range (n + 1),
    (-1 : ℤ) ^ t * (t : ℤ) * (((n - 1 - t).choose t : ℤ) * (numDerangements (n - 1 - 2 * t) : ℤ))

private lemma b_succ (n : ℕ) : b (n + 1) = (n + 1 : ℤ) * b n - R (n + 1) + u (n + 1) := by
  unfold b R
  rw [u_eq_sum (n + 1)]
  have hbn : (∑ t ∈ Finset.range (n + 2), (-1 : ℤ) ^ t * (((n - t).choose t : ℤ) * (numDerangements (n - 2 * t) : ℤ))) =
      ∑ t ∈ Finset.range (n + 1), (-1 : ℤ) ^ t * (((n - t).choose t : ℤ) * (numDerangements (n - 2 * t) : ℤ)) := by
    rw [Finset.sum_range_succ]
    have hzero : ((n - (n + 1)).choose (n + 1) : ℤ) = 0 := by
      rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]
    rw [hzero, zero_mul, mul_zero, add_zero]
  rw [← hbn]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht_le : t ≤ n + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
  by_cases hgt : n + 1 < 2 * t
  · have h1 : n + 1 - t < t := by omega
    have h2 : n - t < t := by omega
    rw [show n + 1 - 1 - t = n - t by omega]
    simp only [Nat.choose_eq_zero_of_lt h1, Nat.choose_eq_zero_of_lt h2, Nat.cast_zero, zero_mul,
      mul_zero, sub_zero, add_zero]
  · by_cases heq : 2 * t = n + 1
    · have h2 : n - t < t := by omega
      rw [show n + 1 - 2 * t = 0 by omega, numDerangements_zero, Nat.cast_one,
        pow_zero, mul_one, show n + 1 - 1 - t = n - t by omega,
        Nat.choose_eq_zero_of_lt h2]
      simp only [Nat.cast_zero, zero_mul, mul_zero, sub_zero, zero_add]
    · have hlt : 2 * t < n + 1 := by omega
      have htn : t ≤ n := by omega
      have hsub1 : n + 1 - 2 * t = (n - 2 * t) + 1 := by omega
      rw [hsub1, numDerangements_succ (n - 2 * t)]
      have hch := mul_sub_choose (n - t) t
      rw [show n - t + 1 = n + 1 - t by omega, show n + 1 - t - t = n - 2 * t + 1 by omega] at hch
      have hchZ : ((n - 2 * t + 1 : ℕ) : ℤ) * ((n + 1 - t).choose t : ℤ) =
          ((n + 1 - t : ℕ) : ℤ) * ((n - t).choose t : ℤ) := by exact_mod_cast hch
      rw [show n + 1 - 1 - t = n - t by omega, show n + 1 - 1 - 2 * t = n - 2 * t by omega]
      zify [ht_le, show 2 * t ≤ n by omega] at hchZ ⊢
      rw [pow_succ']
      linear_combination (numDerangements (n - 2 * t) : ℤ) * (-1 : ℤ) ^ t * hchZ

private lemma R_add_three (n : ℕ) : R (n + 3) = - (n + 1 : ℤ) * b n + R (n + 1) := by
  unfold R b
  rw [Finset.sum_range_succ' (fun t => (-1 : ℤ) ^ t * (t : ℤ) *
    (((n + 3 - 1 - t).choose t : ℤ) * (numDerangements (n + 3 - 1 - 2 * t) : ℤ))) (n + 3)]
  simp only [Nat.cast_zero, mul_zero, zero_mul, add_zero]
  have hbn : (∑ t ∈ Finset.range (n + 3), (-1 : ℤ) ^ t * (((n - t).choose t : ℤ) * (numDerangements (n - 2 * t) : ℤ))) =
      ∑ t ∈ Finset.range (n + 1), (-1 : ℤ) ^ t * (((n - t).choose t : ℤ) * (numDerangements (n - 2 * t) : ℤ)) := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have hz1 : ((n - (n + 1)).choose (n + 1) : ℤ) = 0 := by rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]
    have hz2 : ((n - (n + 2)).choose (n + 2) : ℤ) = 0 := by rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]
    simp only [hz1, hz2, zero_mul, mul_zero, add_zero]
  have hRn : (∑ t ∈ Finset.range (n + 3), (-1 : ℤ) ^ t * (t : ℤ) *
        (((n + 1 - 1 - t).choose t : ℤ) * (numDerangements (n + 1 - 1 - 2 * t) : ℤ))) =
      ∑ t ∈ Finset.range (n + 2), (-1 : ℤ) ^ t * (t : ℤ) *
        (((n + 1 - 1 - t).choose t : ℤ) * (numDerangements (n + 1 - 1 - 2 * t) : ℤ)) := by
    rw [Finset.sum_range_succ]
    have hz3 : ((n + 1 - 1 - (n + 2)).choose (n + 2) : ℤ) = 0 := by rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]
    simp only [hz3, zero_mul, mul_zero, add_zero]
  rw [← hbn, ← hRn]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hs_le : s ≤ n + 2 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
  by_cases hsn : n + 1 < s
  · have h1 : n + 3 - 1 - (s + 1) < s + 1 := by omega
    have h2 : n - s < s := by omega
    simp only [Nat.choose_eq_zero_of_lt h1, show n + 1 - 1 - s = n - s by omega,
      Nat.choose_eq_zero_of_lt h2, Nat.cast_zero, zero_mul, mul_zero, add_zero]
  · have hle : s ≤ n + 1 := by omega
    have hch := succ_mul_choose_sub n s
    have hchZ : ((s + 1 : ℕ) : ℤ) * ((n + 1 - s).choose (s + 1) : ℤ) =
        ((n + 1 - s : ℕ) : ℤ) * ((n - s).choose s : ℤ) := by exact_mod_cast hch
    rw [show n + 3 - 1 - (s + 1) = n + 1 - s by omega,
      show n + 3 - 1 - 2 * (s + 1) = n - 2 * s by omega,
      show n + 1 - 1 - s = n - s by omega,
      show n + 1 - 1 - 2 * s = n - 2 * s by omega, pow_succ']
    zify [hle] at hchZ ⊢
    linear_combination -((-1 : ℤ) ^ s * (numDerangements (n - 2 * s) : ℤ) * hchZ)

private lemma b_add_two (n : ℕ) :
    b (n + 2) = (n + 2 : ℤ) * b (n + 1) + b n + u (n + 2) - u n := by
  rcases n with _ | k
  · simp only [b, u, w, Finset.sum_range_succ, Finset.sum_range_zero, numDerangements_zero,
      numDerangements_add_two]
    decide
  · have h1 := b_succ (k + 2)
    have h2 := b_succ k
    have h3 := R_add_three k
    push_cast at h1 h2 h3 ⊢
    linarith

private lemma b_add_four (n : ℕ) :
    b (n + 4) = (n + 3 : ℤ) * (b (n + 3) + b (n + 2) + b (n + 1)) + b n := by
  have h4 := b_add_two (n + 2)
  have h3 := b_add_two (n + 1)
  have h2 := b_add_two n
  have hu2 := u_add_two (n + 2)
  have hu0 := u_add_two n
  push_cast at h4 h3 h2 hu2 hu0 ⊢
  linarith

-- Combinatorial part: (a n : ℤ) = b n

private def adjSwap {n : ℕ} (σ : Equiv.Perm (Fin n)) (e : Fin (n - 1)) : Prop :=
  σ ⟨e.val, by omega⟩ = ⟨e.val + 1, by omega⟩ ∧ σ ⟨e.val + 1, by omega⟩ = ⟨e.val, by omega⟩

private def ValidM (n : ℕ) (M : Finset (Fin (n - 1))) : Prop :=
  ∀ e₁ ∈ M, ∀ e₂ ∈ M, e₁.val + 1 ≠ e₂.val

private def covered {n : ℕ} (M : Finset (Fin (n - 1))) : Finset (Fin n) :=
  M.biUnion fun e => {⟨e.val, by omega⟩, ⟨e.val + 1, by omega⟩}

private lemma mem_covered_iff {n : ℕ} (M : Finset (Fin (n - 1))) (x : Fin n) :
    x ∈ covered M ↔ ∃ e ∈ M, x.val = e.val ∨ x.val = e.val + 1 := by
  simp only [covered, Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]

private lemma card_covered {n : ℕ} {M : Finset (Fin (n - 1))} (hM : ValidM n M) :
    (covered M).card = 2 * M.card := by
  have hpair : ∀ e : Fin (n - 1),
      ({(⟨e.val, by omega⟩ : Fin n), ⟨e.val + 1, by omega⟩} : Finset (Fin n)).card = 2 :=
    fun e => Finset.card_pair (Fin.ne_of_val_ne (by simp))
  unfold covered
  rw [Finset.card_biUnion]
  · simp only [hpair, Finset.sum_const, smul_eq_mul, mul_comm]
  · intro e₁ he₁ e₂ he₂ hne
    change Disjoint _ _
    rw [Finset.disjoint_iff_ne]
    intro x hx y hy hxy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    have h1 := hM e₁ he₁ e₂ he₂
    have h2 := hM e₂ he₂ e₁ he₁
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp only [Fin.ext_iff] at hxy
    · exact hne (Fin.ext hxy)
    · exact h2 hxy.symm
    · exact h1 hxy
    · exact hne (Fin.ext (by omega))

private noncomputable def swapFun (n : ℕ) (M : Finset (Fin (n - 1))) (x : Fin n) : Fin n := by
  classical
  exact if h1 : ∃ e ∈ M, x.val = e.val then ⟨x.val + 1, by obtain ⟨e, _, he⟩ := h1; omega⟩
  else if h2 : ∃ e ∈ M, x.val = e.val + 1 then ⟨x.val - 1, by omega⟩
  else x

private lemma swapFun_eq_add {n : ℕ} {M : Finset (Fin (n - 1))} {x : Fin n}
    (h1 : ∃ e ∈ M, x.val = e.val) :
    swapFun n M x = ⟨x.val + 1, by obtain ⟨e, _, he⟩ := h1; omega⟩ := by
  classical
  unfold swapFun
  exact dif_pos h1

private lemma swapFun_eq_sub {n : ℕ} {M : Finset (Fin (n - 1))} {x : Fin n}
    (h1 : ¬ ∃ e ∈ M, x.val = e.val) (h2 : ∃ e ∈ M, x.val = e.val + 1) :
    swapFun n M x = ⟨x.val - 1, by omega⟩ := by
  classical
  unfold swapFun
  rw [dif_neg h1, dif_pos h2]

private lemma swapFun_eq_self {n : ℕ} {M : Finset (Fin (n - 1))} {x : Fin n}
    (h1 : ¬ ∃ e ∈ M, x.val = e.val) (h2 : ¬ ∃ e ∈ M, x.val = e.val + 1) :
    swapFun n M x = x := by
  classical
  unfold swapFun
  rw [dif_neg h1, dif_neg h2]

private lemma swapFun_involutive {n : ℕ} {M : Finset (Fin (n - 1))} (hM : ValidM n M) :
    Function.Involutive (swapFun n M) := by
  intro x
  by_cases h1 : ∃ e ∈ M, x.val = e.val
  · obtain ⟨e, he, hxe⟩ := h1
    rw [swapFun_eq_add ⟨e, he, hxe⟩]
    have hnot : ¬ ∃ e' ∈ M, (⟨x.val + 1, by omega⟩ : Fin n).val = e'.val := by
      rintro ⟨e', he', heq⟩
      exact hM e he e' he' (by simp only at heq; omega)
    have hyes : ∃ e' ∈ M, (⟨x.val + 1, by omega⟩ : Fin n).val = e'.val + 1 :=
      ⟨e, he, by simp only; omega⟩
    rw [swapFun_eq_sub hnot hyes]
    exact Fin.ext (by simp)
  · by_cases h2 : ∃ e ∈ M, x.val = e.val + 1
    · obtain ⟨e, he, hxe⟩ := h2
      rw [swapFun_eq_sub h1 ⟨e, he, hxe⟩]
      have hyes : ∃ e' ∈ M, (⟨x.val - 1, by omega⟩ : Fin n).val = e'.val :=
        ⟨e, he, by simp only; omega⟩
      rw [swapFun_eq_add hyes]
      exact Fin.ext (by simp only; omega)
    · rw [swapFun_eq_self h1 h2, swapFun_eq_self h1 h2]

private noncomputable def swapPerm {n : ℕ} {M : Finset (Fin (n - 1))} (hM : ValidM n M) :
    Equiv.Perm (Fin n) :=
  ⟨swapFun n M, swapFun n M, swapFun_involutive hM, swapFun_involutive hM⟩

private lemma swapPerm_invol {n : ℕ} {M : Finset (Fin (n - 1))} (hM : ValidM n M) (x : Fin n) :
    swapPerm hM (swapPerm hM x) = x :=
  swapFun_involutive hM x

private lemma swapPerm_mul_self {n : ℕ} {M : Finset (Fin (n - 1))} (hM : ValidM n M) :
    swapPerm hM * swapPerm hM = 1 :=
  Equiv.Perm.ext fun x => swapPerm_invol hM x

private lemma swapPerm_adjSwap {n : ℕ} {M : Finset (Fin (n - 1))} (hM : ValidM n M)
    {e : Fin (n - 1)} (he : e ∈ M) : adjSwap (swapPerm hM) e := by
  classical
  constructor
  · change swapFun n M ⟨e.val, by omega⟩ = ⟨e.val + 1, by omega⟩
    unfold swapFun
    rw [dif_pos ⟨e, he, rfl⟩]
  · change swapFun n M ⟨e.val + 1, by omega⟩ = ⟨e.val, by omega⟩
    unfold swapFun
    have hnot : ¬ ∃ e' ∈ M, (⟨e.val + 1, by omega⟩ : Fin n).val = e'.val := by
      rintro ⟨e', he', heq⟩
      exact hM e he e' he' (by simp only at heq; omega)
    rw [dif_neg hnot, dif_pos ⟨e, he, rfl⟩]
    exact Fin.ext (by simp)

private lemma swapPerm_ne_of_mem {n : ℕ} {M : Finset (Fin (n - 1))} (hM : ValidM n M)
    {x : Fin n} (hx : x ∈ covered M) : swapPerm hM x ≠ x := by
  classical
  rw [mem_covered_iff] at hx
  rcases hx with ⟨e, he, hxe | hxe⟩
  · change swapFun n M x ≠ x
    unfold swapFun
    rw [dif_pos ⟨e, he, hxe⟩]
    exact Fin.ne_of_val_ne (by simp)
  · have hnot : ¬ ∃ e' ∈ M, x.val = e'.val := by
      rintro ⟨e', he', heq⟩
      exact hM e he e' he' (by omega)
    change swapFun n M x ≠ x
    unfold swapFun
    rw [dif_neg hnot, dif_pos ⟨e, he, hxe⟩]
    exact Fin.ne_of_val_ne (by simp only; omega)

private lemma swapPerm_eq_of_notMem {n : ℕ} {M : Finset (Fin (n - 1))} (hM : ValidM n M)
    {x : Fin n} (hx : x ∉ covered M) : swapPerm hM x = x := by
  classical
  rw [mem_covered_iff] at hx
  have h1 : ¬ ∃ e ∈ M, x.val = e.val := fun ⟨e, he, h⟩ => hx ⟨e, he, Or.inl h⟩
  have h2 : ¬ ∃ e ∈ M, x.val = e.val + 1 := fun ⟨e, he, h⟩ => hx ⟨e, he, Or.inr h⟩
  change swapFun n M x = x
  unfold swapFun
  rw [dif_neg h1, dif_neg h2]

private lemma swapPerm_mem_covered {n : ℕ} {M : Finset (Fin (n - 1))} (hM : ValidM n M)
    {x : Fin n} (hx : x ∈ covered M) : swapPerm hM x ∈ covered M := by
  rw [mem_covered_iff] at hx ⊢
  rcases hx with ⟨e, he, hxe | hxe⟩
  · have h := (swapPerm_adjSwap hM he).1
    have hx' : x = ⟨e.val, by omega⟩ := Fin.ext hxe
    rw [hx', h]
    exact ⟨e, he, Or.inr rfl⟩
  · have h := (swapPerm_adjSwap hM he).2
    have hx' : x = ⟨e.val + 1, by omega⟩ := Fin.ext hxe
    rw [hx', h]
    exact ⟨e, he, Or.inl rfl⟩

private lemma eq_swapPerm_of_adjSwap {n : ℕ} {M : Finset (Fin (n - 1))} (hM : ValidM n M)
    {σ : Equiv.Perm (Fin n)} (hσ : ∀ e ∈ M, adjSwap σ e)
    {x : Fin n} (hx : x ∈ covered M) : σ x = swapPerm hM x := by
  rw [mem_covered_iff] at hx
  rcases hx with ⟨e, he, hxe | hxe⟩
  · have hx' : x = ⟨e.val, by omega⟩ := Fin.ext hxe
    rw [hx', (hσ e he).1, (swapPerm_adjSwap hM he).1]
  · have hx' : x = ⟨e.val + 1, by omega⟩ := Fin.ext hxe
    rw [hx', (hσ e he).2, (swapPerm_adjSwap hM he).2]

private noncomputable def permRestrictEquiv {n : ℕ} {M : Finset (Fin (n - 1))} (hM : ValidM n M) :
    { σ : derangements (Fin n) // ∀ e ∈ M, adjSwap σ.1 e } ≃
      derangements { x : Fin n // x ∉ covered M } := by
  classical
  refine Equiv.trans ?_ (derangements.subtypeEquiv (fun x : Fin n => x ∉ covered M)).symm
  refine
    { toFun := fun ⟨σ, hσ⟩ => ⟨swapPerm hM * σ.1, ?_⟩
      invFun := fun ⟨f, hf⟩ => ⟨⟨swapPerm hM * f, ?_⟩, ?_⟩
      left_inv := fun ⟨σ, hσ⟩ => Subtype.ext (Subtype.ext (Equiv.Perm.ext fun x => by
        change swapPerm hM ((swapPerm hM * σ.1) x) = σ.1 x
        rw [Equiv.Perm.mul_apply, swapPerm_invol hM]))
      right_inv := fun ⟨f, hf⟩ => Subtype.ext (Equiv.Perm.ext fun x => by
        change swapPerm hM ((swapPerm hM * f) x) = f x
        rw [Equiv.Perm.mul_apply, swapPerm_invol hM]) }
  · intro a
    simp only [not_not, Function.mem_fixedPoints_iff, Equiv.Perm.mul_apply]
    constructor
    · intro ha
      rw [eq_swapPerm_of_adjSwap hM hσ ha]
      exact swapPerm_invol hM a
    · intro ha
      by_contra hnot
      have hcov : σ.1 a ∉ covered M := by
        intro hmem
        have hpre := swapPerm_mem_covered hM hmem
        have hEq := eq_swapPerm_of_adjSwap hM hσ hpre
        rw [swapPerm_invol hM] at hEq
        have hinj := σ.1.injective (hEq.symm)
        rw [← hinj] at hpre
        exact hnot hpre
      rw [swapPerm_eq_of_notMem hM hcov] at ha
      exact σ.2 a ha
  · intro a
    simp only [Equiv.Perm.mul_apply]
    by_cases ha : a ∈ covered M
    · have hfa : f a = a := (hf a).mp (not_not.mpr ha)
      rw [hfa]
      exact swapPerm_ne_of_mem hM ha
    · have hfne : f a ≠ a := by
        intro heq
        exact ha (not_not.mp ((hf a).mpr heq))
      have hcov : f a ∉ covered M := by
        intro hmem
        have hfix : f (f a) = f a := (hf (f a)).mp (not_not.mpr hmem)
        exact hfne (f.injective hfix)
      rw [swapPerm_eq_of_notMem hM hcov]
      exact hfne
  · intro e he
    have he1 : (⟨e.val, by omega⟩ : Fin n) ∈ covered M :=
      (mem_covered_iff M _).mpr ⟨e, he, Or.inl rfl⟩
    have he2 : (⟨e.val + 1, by omega⟩ : Fin n) ∈ covered M :=
      (mem_covered_iff M _).mpr ⟨e, he, Or.inr rfl⟩
    have hf1 : f ⟨e.val, by omega⟩ = ⟨e.val, by omega⟩ := (hf _).mp (not_not.mpr he1)
    have hf2 : f ⟨e.val + 1, by omega⟩ = ⟨e.val + 1, by omega⟩ := (hf _).mp (not_not.mpr he2)
    constructor
    · simp only [Equiv.Perm.mul_apply, hf1]
      exact (swapPerm_adjSwap hM he).1
    · simp only [Equiv.Perm.mul_apply, hf2]
      exact (swapPerm_adjSwap hM he).2

open Classical in
private lemma card_filter_adjSwap {n : ℕ} (M : Finset (Fin (n - 1))) :
    ((Finset.univ : Finset (↥(derangements (Fin n)))).filter (fun σ => ∀ e ∈ M, adjSwap σ.1 e)).card =
      if ValidM n M then numDerangements (n - 2 * M.card) else 0 := by
  classical
  by_cases hM : ValidM n M
  · rw [if_pos hM]
    have h1 : ((Finset.univ : Finset (↥(derangements (Fin n)))).filter
          (fun σ => ∀ e ∈ M, adjSwap σ.1 e)).card =
        Fintype.card { σ : derangements (Fin n) // ∀ e ∈ M, adjSwap σ.1 e } := by
      rw [Fintype.card_subtype]
    rw [h1, Fintype.card_congr (permRestrictEquiv hM), card_derangements_eq_numDerangements]
    have hcard : Fintype.card { x : Fin n // x ∉ covered M } = n - 2 * M.card := by
      rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe, card_covered hM]
    rw [hcard]
  · rw [if_neg hM, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro σ _ hσ
    apply hM
    intro e₁ he₁ e₂ he₂ heq
    have h1 := (hσ e₁ he₁).2
    have h2 := (hσ e₂ he₂).1
    have harg : (⟨e₁.val + 1, by omega⟩ : Fin n) = ⟨e₂.val, by omega⟩ := Fin.ext heq
    rw [harg, h2] at h1
    have hval := congrArg Fin.val h1
    simp only at hval
    omega

private noncomputable def validSets (n t : ℕ) : Finset (Finset (Fin (n - 1))) := by
  classical
  exact Finset.univ.filter fun M => ValidM n M ∧ M.card = t

private lemma validSets_card (n t : ℕ) : (validSets n t).card = (n - t).choose t := by
  classical
  induction n using Nat.strong_induction_on generalizing t with
  | _ n ih =>
    rcases n with _ | _ | _ | m
    · rcases t with _ | t
      · have : validSets 0 0 = {∅} := by
          ext M; simp [validSets, ValidM, Finset.eq_empty_of_isEmpty]
        rw [this]; simp
      · have : validSets 0 (t + 1) = ∅ := by
          ext M; simp [validSets, Finset.eq_empty_of_isEmpty]
        rw [this, Finset.card_empty, Nat.choose_eq_zero_of_lt (by omega)]
    · rcases t with _ | t
      · have : validSets 1 0 = {∅} := by
          ext M; simp [validSets, ValidM, Finset.eq_empty_of_isEmpty]
        rw [this]; simp
      · have : validSets 1 (t + 1) = ∅ := by
          ext M; simp [validSets, Finset.eq_empty_of_isEmpty]
        rw [this, Finset.card_empty, Nat.choose_eq_zero_of_lt (by omega)]
    · rcases t with _ | _ | t
      · have : validSets 2 0 = {∅} := by
          ext M; simp only [validSets, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_singleton, Finset.card_eq_zero]
          exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨fun e he => by rw [h] at he; simp at he, h⟩⟩
        rw [this]; simp
      · have : validSets 2 1 = {Finset.univ} := by
          ext M; simp only [validSets, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_singleton]
          constructor
          · rintro ⟨_, hc⟩
            have hc1 : M.card = (Finset.univ : Finset (Fin 1)).card := by simp [hc]
            exact Finset.eq_of_subset_of_card_le (Finset.subset_univ M) hc1.ge
          · intro hM; rw [hM]; refine ⟨?_, by simp⟩
            intro e₁ _ e₂ _; omega
        rw [this]; simp
      · have : validSets 2 (t + 2) = ∅ := by
          ext M; simp only [validSets, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.notMem_empty, iff_false]
          rintro ⟨_, hc⟩
          have hle := Finset.card_le_univ M
          simp only [Fintype.card_fin] at hle
          omega
        rw [this, Finset.card_empty, Nat.choose_eq_zero_of_lt (by omega)]
    · rcases t with _ | t
      · have : validSets (m + 3) 0 = {∅} := by
          ext M; simp only [validSets, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_singleton, Finset.card_eq_zero]
          exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨fun e he => by rw [h] at he; simp at he, h⟩⟩
        rw [this]; simp
      · let last : Fin (m + 3 - 1) := ⟨m + 1, by omega⟩
        have hsplit : (validSets (m + 3) (t + 1)).card =
            ((validSets (m + 3) (t + 1)).filter (fun M => last ∉ M)).card +
            ((validSets (m + 3) (t + 1)).filter (fun M => last ∈ M)).card := by
          have hs := (Finset.card_filter_add_card_filter_not (fun M : Finset (Fin (m + 3 - 1)) => last ∈ M)
            (s := validSets (m + 3) (t + 1))).symm
          omega
        have hs0 : ((validSets (m + 3) (t + 1)).filter (fun M => last ∉ M)).card =
            (validSets (m + 2) (t + 1)).card := by
          refine Finset.card_bij (fun M _ => M.preimage Fin.castSucc (Fin.castSucc_injective _).injOn) ?_ ?_ ?_
          · intro M hM
            simp only [Finset.mem_filter, validSets, Finset.mem_univ, true_and] at hM ⊢
            rcases hM with ⟨⟨hV, hc⟩, hnl⟩
            have himg : (M.preimage Fin.castSucc (Fin.castSucc_injective _).injOn).image Fin.castSucc = M := by
              ext e; simp only [Finset.mem_image, Finset.mem_preimage]
              constructor
              · rintro ⟨a, ha, rfl⟩; exact ha
              · intro he
                have hlt : e.val < m + 1 := by
                  by_contra hge
                  apply hnl
                  have : e = last := Fin.ext (by simp only [last]; omega)
                  rwa [← this]
                exact ⟨⟨e.val, hlt⟩, he, Fin.ext rfl⟩
            refine ⟨?_, ?_⟩
            · intro e₁ he₁ e₂ he₂
              simp only [Finset.mem_preimage] at he₁ he₂
              exact hV _ he₁ _ he₂
            · have hc2 := congrArg Finset.card himg
              rw [Finset.card_image_of_injective _ (Fin.castSucc_injective _), hc] at hc2
              exact hc2
          · intro M₁ hM₁ M₂ hM₂ heq
            simp only [Finset.mem_filter] at hM₁ hM₂
            ext e
            by_cases hlt : e.val < m + 1
            · have he1 : (⟨e.val, hlt⟩ : Fin (m + 1)) ∈ M₁.preimage Fin.castSucc (Fin.castSucc_injective _).injOn ↔ e ∈ M₁ := by
                simp only [Finset.mem_preimage]; rfl
              have he2 : (⟨e.val, hlt⟩ : Fin (m + 1)) ∈ M₂.preimage Fin.castSucc (Fin.castSucc_injective _).injOn ↔ e ∈ M₂ := by
                simp only [Finset.mem_preimage]; rfl
              rw [← he1, ← he2, heq]
            · have he_last : e = last := Fin.ext (by simp only [last]; omega)
              rw [he_last]; simp [hM₁.2, hM₂.2]
          · intro M' hM'
            simp only [validSets, Finset.mem_filter, Finset.mem_univ, true_and] at hM'
            refine ⟨M'.image Fin.castSucc, ?_, ?_⟩
            · simp only [Finset.mem_filter, validSets, Finset.mem_univ, true_and]
              refine ⟨⟨?_, ?_⟩, ?_⟩
              · intro e₁ he₁ e₂ he₂
                simp only [Finset.mem_image] at he₁ he₂
                rcases he₁ with ⟨a₁, ha₁, rfl⟩; rcases he₂ with ⟨a₂, ha₂, rfl⟩
                exact hM'.1 a₁ ha₁ a₂ ha₂
              · rw [Finset.card_image_of_injective _ (Fin.castSucc_injective _), hM'.2]
              · simp only [Finset.mem_image]
                rintro ⟨a, _, ha⟩
                have := congrArg Fin.val ha
                simp only [Fin.val_castSucc, last] at this
                omega
            · ext x; simp [Finset.mem_preimage, Finset.mem_image]
        have hs1 : ((validSets (m + 3) (t + 1)).filter (fun M => last ∈ M)).card =
            (validSets (m + 1) t).card := by
          let emb : Fin m → Fin (m + 2) := fun e => ⟨e.val, by omega⟩
          have hemb_inj : Function.Injective emb := fun a b h => Fin.ext (by simpa [emb] using congrArg Fin.val h)
          refine Finset.card_bij (fun M _ => M.preimage emb hemb_inj.injOn) ?_ ?_ ?_
          · intro M hM
            simp only [Finset.mem_filter, validSets, Finset.mem_univ, true_and] at hM ⊢
            rcases hM with ⟨⟨hV, hc⟩, hlast⟩
            have hno_prev : (⟨m, by omega⟩ : Fin (m + 2)) ∉ M := fun hprev =>
              hV _ hprev _ hlast (by simp [last])
            have himg : insert last ((M.preimage emb hemb_inj.injOn).image emb) = M := by
              ext e; simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_preimage]
              constructor
              · rintro (rfl | ⟨a, ha, rfl⟩) <;> assumption
              · intro he
                by_cases hle : e.val < m
                · exact Or.inr ⟨⟨e.val, hle⟩, he, Fin.ext rfl⟩
                · left
                  have hne_m : e.val ≠ m := fun hm =>
                    hno_prev (by rw [show (⟨m, by omega⟩ : Fin (m + 2)) = e from Fin.ext hm.symm]; exact he)
                  exact Fin.ext (by simp only [last]; omega)
            refine ⟨?_, ?_⟩
            · intro e₁ he₁ e₂ he₂
              simp only [Finset.mem_preimage] at he₁ he₂
              exact hV _ he₁ _ he₂
            · have hnl : last ∉ (M.preimage emb hemb_inj.injOn).image emb := by
                simp only [Finset.mem_image]
                rintro ⟨a, _, ha⟩
                have := congrArg Fin.val ha
                simp only [emb, last] at this
                omega
              have hcard := congrArg Finset.card himg
              rw [Finset.card_insert_of_notMem hnl, Finset.card_image_of_injective _ hemb_inj, hc] at hcard
              omega
          · intro M₁ hM₁ M₂ hM₂ heq
            simp only [Finset.mem_filter, validSets, Finset.mem_univ, true_and] at hM₁ hM₂
            have h1_no : (⟨m, by omega⟩ : Fin (m + 2)) ∉ M₁ := fun hp =>
              hM₁.1.1 _ hp _ hM₁.2 (by simp [last])
            have h2_no : (⟨m, by omega⟩ : Fin (m + 2)) ∉ M₂ := fun hp =>
              hM₂.1.1 _ hp _ hM₂.2 (by simp [last])
            ext e
            by_cases hlt : e.val < m
            · have hx1 : (⟨e.val, hlt⟩ : Fin m) ∈ M₁.preimage emb hemb_inj.injOn ↔ e ∈ M₁ := by
                simp only [Finset.mem_preimage]; rfl
              have hx2 : (⟨e.val, hlt⟩ : Fin m) ∈ M₂.preimage emb hemb_inj.injOn ↔ e ∈ M₂ := by
                simp only [Finset.mem_preimage]; rfl
              rw [← hx1, ← hx2, heq]
            · by_cases he_m : e.val = m
              · have he' : e = ⟨m, by omega⟩ := Fin.ext he_m
                rw [he']; simp [h1_no, h2_no]
              · have he' : e = last := Fin.ext (by simp only [last]; omega)
                rw [he']; simp [hM₁.2, hM₂.2]
          · intro M' hM'
            simp only [validSets, Finset.mem_filter, Finset.mem_univ, true_and] at hM'
            refine ⟨insert last (M'.image emb), ?_, ?_⟩
            · have hnl : last ∉ M'.image emb := by
                simp only [Finset.mem_image]; rintro ⟨a, _, ha⟩
                have := congrArg Fin.val ha
                simp only [emb, last] at this; omega
              simp only [Finset.mem_filter, validSets, Finset.mem_univ, true_and, Finset.mem_insert,
                true_or, and_true]
              refine ⟨?_, ?_⟩
              · intro e₁ he₁ e₂ he₂
                simp only [Finset.mem_insert, Finset.mem_image] at he₁ he₂
                rcases he₁ with rfl | ⟨a₁, ha₁, rfl⟩ <;> rcases he₂ with rfl | ⟨a₂, ha₂, rfl⟩
                · simp [last]
                · simp only [last, emb]; omega
                · simp only [emb, last]; omega
                · exact hM'.1 a₁ ha₁ a₂ ha₂
              · rw [Finset.card_insert_of_notMem hnl, Finset.card_image_of_injective _ hemb_inj, hM'.2]
            · ext a
              simp only [Finset.mem_preimage, Finset.mem_insert, Finset.mem_image]
              constructor
              · rintro (h | ⟨b, hb, hab⟩)
                · have := congrArg Fin.val h; simp only [emb, last] at this; omega
                · rwa [← hemb_inj hab]
              · intro ha; exact Or.inr ⟨a, ha, rfl⟩
        rw [hsplit, hs0, hs1, ih (m + 2) (by omega) (t + 1), ih (m + 1) (by omega) t]
        have hstep := choose_sub_succ_eq (m + 2) t
        rw [show m + 2 - (t + 1) = m + 1 - t by omega, show m + 1 - t = m + 1 - t by rfl,
          show m + 3 - (t + 1) = m + 2 - t by omega] at *
        have hch : (m + 2 - t).choose (t + 1) = (m + 1 - t).choose (t + 1) + (m + 1 - t).choose t := by
          simpa only [show m + 1 + 1 - t = m + 2 - t by omega] using choose_sub_succ_eq (m + 1) t
        omega

private lemma a_eq_b (n : ℕ) : (a n : ℤ) = b n := by
  classical
  have ha1 : a n = ((Finset.univ : Finset (derangements (Fin n))).filter
      (fun σ => ∀ e : Fin (n - 1), ¬ adjSwap σ.1 e)).card := by
    unfold a
    refine Finset.card_bij (fun σ hσ => ⟨σ, (Finset.mem_filter.mp hσ).2.1⟩) ?_ ?_ ?_
    · intro σ hσ
      rw [Finset.mem_filter] at hσ ⊢
      refine ⟨Finset.mem_univ _, fun e ⟨h1, h2⟩ => ?_⟩
      exact hσ.2.2 ⟨e.val, by omega⟩ ⟨e.val + 1, by omega⟩ (by simp) ⟨h1, h2⟩
    · intro σ₁ _ σ₂ _ h; exact congrArg Subtype.val h
    · intro σ hσ
      rw [Finset.mem_filter] at hσ
      refine ⟨σ.1, ?_, by ext; rfl⟩
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, σ.2, fun i j hij ⟨h1, h2⟩ => ?_⟩
      have hi : i.val < n - 1 := by omega
      have h_i : i = ⟨i.val, by omega⟩ := Fin.ext rfl
      have h_j : j = ⟨i.val + 1, by omega⟩ := Fin.ext hij
      exact hσ.2 ⟨i.val, hi⟩ ⟨by rwa [← h_i, ← h_j], by rwa [← h_i, ← h_j]⟩
  have ha2 : (a n : ℤ) = ∑ σ : derangements (Fin n),
      ∏ e : Fin (n - 1), (1 - if adjSwap σ.1 e then (1 : ℤ) else 0) := by
    rw [ha1, Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    by_cases h : ∀ e : Fin (n - 1), ¬ adjSwap σ.1 e
    · rw [if_pos h, Finset.prod_eq_one]
      · simp
      · intro e _; rw [if_neg (h e), sub_zero]
    · rw [if_neg h]
      obtain ⟨e, he⟩ := not_forall.mp h
      rw [not_not] at he
      rw [Finset.prod_eq_zero (Finset.mem_univ e)]
      · simp
      · rw [if_pos he, sub_self]
  rw [ha2]
  have hprod : ∀ σ : derangements (Fin n),
      (∏ e : Fin (n - 1), (1 - if adjSwap σ.1 e then (1 : ℤ) else 0)) =
        ∑ M : Finset (Fin (n - 1)), (-1 : ℤ) ^ M.card *
          if ∀ e ∈ M, adjSwap σ.1 e then 1 else 0 := by
    intro σ
    rw [Finset.prod_sub (fun _ => (1 : ℤ)) (fun e => if adjSwap σ.1 e then (1 : ℤ) else 0) Finset.univ]
    rw [Finset.powerset_univ]
    refine Finset.sum_congr rfl fun M _ => ?_
    rw [Finset.prod_const_one, mul_one]
    congr 1
    by_cases hM : ∀ e ∈ M, adjSwap σ.1 e
    · rw [if_pos hM, Finset.prod_eq_one]
      intro e he; rw [if_pos (hM e he)]
    · rw [if_neg hM]
      push Not at hM
      obtain ⟨e, he, hne⟩ := hM
      have hz : (∏ x ∈ M, if adjSwap σ.1 x then (1 : ℤ) else 0) = 0 :=
        Finset.prod_eq_zero he (if_neg hne)
      exact hz
  simp_rw [hprod]
  rw [Finset.sum_comm]
  have hswap : (∑ M : Finset (Fin (n - 1)), ∑ σ : ↥(derangements (Fin n)),
        (-1 : ℤ) ^ M.card * if ∀ e ∈ M, adjSwap σ.1 e then 1 else 0) =
      ∑ M : Finset (Fin (n - 1)), (-1 : ℤ) ^ M.card *
        if ValidM n M then (numDerangements (n - 2 * M.card) : ℤ) else 0 := by
    refine Finset.sum_congr rfl fun M _ => ?_
    rw [← Finset.mul_sum, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hc : (((Finset.univ : Finset (↥(derangements (Fin n)))).filter
          (fun σ => ∀ e ∈ M, adjSwap σ.1 e)).card : ℤ) =
        if ValidM n M then (numDerangements (n - 2 * M.card) : ℤ) else 0 := by
      have hc0 := card_filter_adjSwap M
      by_cases hM : ValidM n M
      · rw [if_pos hM] at hc0 ⊢; exact_mod_cast hc0
      · rw [if_neg hM] at hc0 ⊢; exact_mod_cast hc0
    rw [hc]
  rw [hswap]
  unfold b
  have hgroup : (∑ M : Finset (Fin (n - 1)), (-1 : ℤ) ^ M.card *
        if ValidM n M then (numDerangements (n - 2 * M.card) : ℤ) else 0) =
      ∑ t ∈ Finset.range (n + 1), ∑ M ∈ validSets n t,
        (-1 : ℤ) ^ t * (numDerangements (n - 2 * t) : ℤ) := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun M : Finset (Fin (n - 1)) => M.card)
      (f := fun M : Finset (Fin (n - 1)) => (-1 : ℤ) ^ M.card *
        if ValidM n M then (numDerangements (n - 2 * M.card) : ℤ) else 0)
      (s := Finset.univ) (t := Finset.range (n + 1))]
    · refine Finset.sum_congr rfl fun t _ => ?_
      have hsub : ((Finset.univ : Finset (Finset (Fin (n - 1)))).filter (fun M => M.card = t)).filter
            (fun M => ValidM n M) = validSets n t := by
        ext M; simp [validSets, and_comm]
      have hrhs : (∑ M ∈ validSets n t, (-1 : ℤ) ^ t * (numDerangements (n - 2 * t) : ℤ)) =
          ∑ M ∈ (Finset.univ : Finset (Finset (Fin (n - 1)))).filter (fun M => M.card = t),
            if ValidM n M then (-1 : ℤ) ^ t * (numDerangements (n - 2 * t) : ℤ) else 0 := by
        rw [← hsub, Finset.sum_filter]
      rw [hrhs]
      refine Finset.sum_congr rfl fun M hM => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hM
      rw [hM]
      split_ifs <;> simp
    · intro M _
      have hle : M.card ≤ (Finset.univ : Finset (Fin (n - 1))).card := Finset.card_le_univ M
      rw [Finset.card_univ, Fintype.card_fin] at hle
      rw [Finset.mem_range]
      omega
  rw [hgroup]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.sum_const, nsmul_eq_mul, validSets_card n t]
  ring

end OMA.Proof_oeis_a177258

theorem OMA.solution : type_of% @OMA.S_oeis_a177258.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  have hb := OMA.Proof_oeis_a177258.b_add_four m
  rw [← OMA.Proof_oeis_a177258.a_eq_b (m + 4),
    ← OMA.Proof_oeis_a177258.a_eq_b (m + 3),
    ← OMA.Proof_oeis_a177258.a_eq_b (m + 2),
    ← OMA.Proof_oeis_a177258.a_eq_b (m + 1),
    ← OMA.Proof_oeis_a177258.a_eq_b m] at hb
  simp only [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega,
    show m + 4 - 3 = m + 1 by omega, show m + 4 - 4 = m by omega]
  zify
  linarith
