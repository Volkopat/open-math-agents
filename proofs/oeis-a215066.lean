import OMAStatements.S_oeis_a215066
import Mathlib

/-!
# Proof of OEIS A215066 Conjectures

Because `exp((2*k - 1)*x) - 1 = (exp(x) - 1) * ∑_{t=0}^{2*k-2} exp(t*x)`, the operator
`evalStep m P y = ∑_{S ⊆ {1..m}} (-1)^(m - |S|) P(y + ∑_{k ∈ S} (2*k - 1))`
is an integer sum of `m`-th forward differences `Δ^m P`:
1. `w m n = 0` for all `m > n`, and `(m! : ℤ) ∣ w m n` for all `m, n`.
2. Modulo any `M >= 1`, all `m >= M` terms vanish (`M ∣ m! ∣ w m n`), so
   `a(n) ≡ ∑_{m < M} w m n (mod M)`, a fixed integer combination of `c^n` with `c : ℕ`.
3. All three claims follow immediately from Euler's theorem and Fermat's little theorem.
-/

namespace OeisA215066Proof

open Finset

private def Δ (g : ℤ → ℤ) (j : ℕ) (x : ℤ) : ℤ :=
  ∑ r ∈ Finset.range (j + 1), (-1 : ℤ) ^ (j - r) * (Nat.choose j r : ℤ) * g (x + r)

private lemma Δ_zero (g : ℤ → ℤ) (x : ℤ) : Δ g 0 x = g x := by
  simp [Δ]

private lemma Δ_succ (g : ℤ → ℤ) (j : ℕ) (x : ℤ) :
    Δ g (j + 1) x = Δ g j (x + 1) - Δ g j x := by
  unfold Δ
  rw [Finset.sum_range_succ (f := fun r => (-1 : ℤ) ^ (j + 1 - r) * (Nat.choose (j + 1) r : ℤ) * g (x + r))]
  rw [Finset.sum_range_succ' (f := fun r => (-1 : ℤ) ^ (j + 1 - r) * (Nat.choose (j + 1) r : ℤ) * g (x + r))]
  rw [Finset.sum_range_succ (f := fun r => (-1 : ℤ) ^ (j - r) * (Nat.choose j r : ℤ) * g (x + 1 + r))]
  rw [Finset.sum_range_succ' (f := fun r => (-1 : ℤ) ^ (j - r) * (Nat.choose j r : ℤ) * g (x + r))]
  simp only [Nat.sub_self, pow_zero, Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_zero,
             Nat.choose_zero_right, Nat.cast_zero, add_zero, Nat.cast_add]
  have hlast : x + ((j : ℤ) + 1) = x + 1 + (j : ℤ) := by ring
  rw [hlast]
  have hmid : ∑ r ∈ Finset.range j,
      (-1 : ℤ) ^ (j + 1 - (r + 1)) * (Nat.choose (j + 1) (r + 1) : ℤ) * g (x + ((r : ℤ) + 1)) =
      (∑ r ∈ Finset.range j, (-1 : ℤ) ^ (j - r) * (Nat.choose j r : ℤ) * g (x + 1 + (r : ℤ))) -
      (∑ r ∈ Finset.range j, (-1 : ℤ) ^ (j - (r + 1)) * (Nat.choose j (r + 1) : ℤ) * g (x + ((r : ℤ) + 1))) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    have hrj : r < j := Finset.mem_range.mp hr
    have h1 : j + 1 - (r + 1) = j - r := by omega
    have h2 : j - r = (j - (r + 1)) + 1 := by omega
    have harg : x + ((r : ℤ) + 1) = x + 1 + (r : ℤ) := by ring
    rw [h1, Nat.choose_succ_succ, Nat.succ_eq_add_one, Nat.cast_add, harg, h2, pow_succ]
    ring
  rw [hmid, pow_succ]
  ring

private lemma Δ_shift (g : ℤ → ℤ) (j : ℕ) (x : ℤ) :
    Δ (fun y => g (y + 1)) j x = Δ g j x + Δ g (j + 1) x := by
  have h1 : Δ (fun y => g (y + 1)) j x = Δ g j (x + 1) := by
    unfold Δ
    apply Finset.sum_congr rfl
    intro r _
    congr 1; ring
  rw [h1, Δ_succ]
  ring

private lemma Δ_add (g₁ g₂ : ℤ → ℤ) (j : ℕ) (x : ℤ) :
    Δ (fun y => g₁ y + g₂ y) j x = Δ g₁ j x + Δ g₂ j x := by
  unfold Δ
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  ring

private lemma Δ_sub (g₁ g₂ : ℤ → ℤ) (j : ℕ) (x : ℤ) :
    Δ (fun y => g₁ y - g₂ y) j x = Δ g₁ j x - Δ g₂ j x := by
  unfold Δ
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r _
  ring

private lemma Δ_const_mul (a : ℤ) (g : ℤ → ℤ) (j : ℕ) (x : ℤ) :
    Δ (fun y => a * g y) j x = a * Δ g j x := by
  unfold Δ
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  ring

private lemma Δ_step_eq_succ (g : ℤ → ℤ) (j : ℕ) (x : ℤ) :
    Δ (fun y => g (y + 1) - g y) j x = Δ g (j + 1) x := by
  rw [Δ_sub, Δ_shift]
  ring

private lemma Δ_pow_eq_zero_of_lt (d j : ℕ) (hdj : d < j) :
    ∀ x : ℤ, Δ (fun y => y ^ d) j x = 0 := by
  induction d using Nat.strong_induction_on generalizing j with
  | h d ih =>
    intro x
    cases j with
    | zero => omega
    | succ j =>
      rw [Δ_succ]
      cases d with
      | zero =>
        have hconst : ∀ m : ℕ, ∀ y : ℤ, Δ (fun _ => (1 : ℤ)) m y = if m = 0 then 1 else 0 := by
          intro m
          induction m with
          | zero => intro y; simp [Δ]
          | succ m ihm => intro y; rw [Δ_succ, ihm, ihm]; simp
        simp only [pow_zero]
        rw [hconst, hconst]; simp
      | succ d =>
        have hbin : (fun y : ℤ => (y + 1) ^ (d + 1) - y ^ (d + 1)) =
            fun y : ℤ => ∑ i ∈ Finset.range (d + 1), (Nat.choose (d + 1) i : ℤ) * y ^ i := by
          ext y
          rw [add_pow, Finset.sum_range_succ]
          simp only [one_pow, mul_one, Nat.choose_self, Nat.cast_one, add_sub_cancel_right]
          apply Finset.sum_congr rfl
          intro i _; ring
        have hstep : Δ (fun y => y ^ (d + 1)) j (x + 1) - Δ (fun y => y ^ (d + 1)) j x =
            Δ (fun y => (y + 1) ^ (d + 1) - y ^ (d + 1)) j x := by
          rw [Δ_sub]
          congr 1
          unfold Δ
          apply Finset.sum_congr rfl
          intro r _; congr 2; ring
        rw [hstep, hbin]
        have hsum : ∀ s : Finset ℕ, (∀ i ∈ s, i < d + 1) → (∀ i ∈ s, i < j) →
            Δ (fun y => ∑ i ∈ s, (Nat.choose (d + 1) i : ℤ) * y ^ i) j x = 0 := by
          intro s
          induction s using Finset.induction_on with
          | empty => intro _ _; simp [Δ]
          | @insert a s ha ihs =>
            intro hltd hlt
            have hfun : (fun y : ℤ => ∑ i ∈ insert a s, (Nat.choose (d + 1) i : ℤ) * y ^ i) =
                fun y : ℤ => (Nat.choose (d + 1) a : ℤ) * y ^ a +
                  ∑ i ∈ s, (Nat.choose (d + 1) i : ℤ) * y ^ i := by
              ext y; rw [Finset.sum_insert ha]
            rw [hfun, Δ_add, Δ_const_mul,
                ih a (hltd a (Finset.mem_insert_self a s)) j (hlt a (Finset.mem_insert_self a s)) x,
                mul_zero, zero_add]
            exact ihs (fun i hi => hltd i (Finset.mem_insert_of_mem hi))
              (fun i hi => hlt i (Finset.mem_insert_of_mem hi))
        exact hsum (Finset.range (d + 1))
          (fun i hi => Finset.mem_range.mp hi)
          (fun i hi => by have := Finset.mem_range.mp hi; omega)

private lemma Δ_pow_zero_eq_stirling (n j : ℕ) :
    Δ (fun y => y ^ n) j 0 = (j.factorial * Nat.stirlingSecond n j : ℕ) := by
  induction n generalizing j with
  | zero =>
    cases j with
    | zero => simp [Δ]
    | succ j =>
      rw [Δ_pow_eq_zero_of_lt 0 (j + 1) (by omega) 0]
      simp [Nat.stirlingSecond_zero_succ]
  | succ n ih =>
    cases j with
    | zero =>
      simp [Δ, zero_pow (Nat.succ_ne_zero n)]
    | succ j =>
      have hrec : Δ (fun y => y ^ (n + 1)) (j + 1) 0 =
          ((j + 1 : ℕ) : ℤ) * (Δ (fun y => y ^ n) (j + 1) 0 + Δ (fun y => y ^ n) j 0) := by
        have hstep1 : Δ (fun y => y ^ (n + 1)) (j + 1) 0 =
            ((j + 1 : ℕ) : ℤ) * Δ (fun y => (y + 1) ^ n) j 0 := by
          unfold Δ
          simp only [zero_add]
          rw [Finset.sum_range_succ' (f := fun r => (-1 : ℤ) ^ (j + 1 - r) * (Nat.choose (j + 1) r : ℤ) * (r : ℤ) ^ (n + 1))]
          simp only [Nat.cast_zero, zero_pow (Nat.succ_ne_zero n), mul_zero, add_zero]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro r _
          have hsub : j + 1 - (r + 1) = j - r := by omega
          have hch : (r + 1) * Nat.choose (j + 1) (r + 1) = (j + 1) * Nat.choose j r := by
            have := Nat.add_one_mul_choose_eq j r
            linarith
          have hchz : ((r + 1 : ℕ) : ℤ) * (Nat.choose (j + 1) (r + 1) : ℤ) =
              ((j + 1 : ℕ) : ℤ) * (Nat.choose j r : ℤ) := by
            exact_mod_cast hch
          rw [hsub, pow_succ ((r + 1 : ℕ) : ℤ) n]
          push_cast
          calc (-1 : ℤ) ^ (j - r) * (Nat.choose (j + 1) (r + 1) : ℤ) * (((r : ℤ) + 1) ^ n * ((r : ℤ) + 1))
              = (-1 : ℤ) ^ (j - r) * (((r + 1 : ℕ) : ℤ) * (Nat.choose (j + 1) (r + 1) : ℤ)) * ((r : ℤ) + 1) ^ n := by
                push_cast; ring
            _ = (-1 : ℤ) ^ (j - r) * (((j + 1 : ℕ) : ℤ) * (Nat.choose j r : ℤ)) * ((r : ℤ) + 1) ^ n := by
                rw [hchz]
            _ = ((j : ℤ) + 1) * ((-1 : ℤ) ^ (j - r) * (Nat.choose j r : ℤ) * ((r : ℤ) + 1) ^ n) := by
                push_cast; ring
        rw [hstep1, Δ_shift (fun y => y ^ n) j 0]
        ring
      rw [hrec, ih (j + 1), ih j, Nat.stirlingSecond_succ_succ, Nat.factorial_succ]
      push_cast
      ring

private lemma fact_dvd_Δ_pow (n j : ℕ) (x : ℤ) :
    (j.factorial : ℤ) ∣ Δ (fun y => y ^ n) j x := by
  have hshift : Δ (fun y => y ^ n) j x =
      ∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℤ) * x ^ (n - i) * Δ (fun y => y ^ i) j 0 := by
    unfold Δ
    simp only [zero_add]
    have hbin : ∀ r : ℕ, (x + (r : ℤ)) ^ n =
        ∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℤ) * x ^ (n - i) * (r : ℤ) ^ i := by
      intro r
      rw [add_comm x (r : ℤ), add_pow]
      apply Finset.sum_congr rfl
      intro i _
      ring
    simp_rw [hbin, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro r _
    ring
  rw [hshift]
  apply Finset.dvd_sum
  intro i _
  rw [Δ_pow_zero_eq_stirling]
  push_cast
  exact dvd_mul_of_dvd_right (dvd_mul_right _ _) _

private def evalStep (m : ℕ) (P : ℤ → ℤ) (y : ℤ) : ℤ :=
  ∑ S ∈ (Finset.Icc 1 m).powerset,
    (-1 : ℤ) ^ (m - S.card) * P (y + ∑ k ∈ S, (2 * (k : ℤ) - 1))

private lemma evalStep_zero (P : ℤ → ℤ) (y : ℤ) : evalStep 0 P y = P y := by
  simp [evalStep]

private lemma evalStep_succ_diff (m : ℕ) (P : ℤ → ℤ) (y : ℤ) :
    evalStep (m + 1) P y = evalStep m P (y + (2 * (m + 1 : ℤ) - 1)) - evalStep m P y := by
  unfold evalStep
  have hIcc : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have hnotmem : m + 1 ∉ Finset.Icc 1 m := by simp
  rw [hIcc, Finset.powerset_insert, Finset.sum_union]
  · rw [Finset.sum_image]
    · rw [add_comm, sub_eq_add_neg, ← Finset.sum_neg_distrib]
      congr 1
      · apply Finset.sum_congr rfl
        intro S hS
        have hSsub : S ⊆ Finset.Icc 1 m := Finset.mem_powerset.mp hS
        have hnotS : m + 1 ∉ S := fun h => hnotmem (hSsub h)
        have hcard : (insert (m + 1) S).card = S.card + 1 := Finset.card_insert_of_notMem hnotS
        have hsub : m + 1 - (S.card + 1) = m - S.card := by omega
        have hsum : ∑ k ∈ insert (m + 1) S, (2 * (k : ℤ) - 1) =
            (2 * ((m + 1 : ℕ) : ℤ) - 1) + ∑ k ∈ S, (2 * (k : ℤ) - 1) :=
          Finset.sum_insert hnotS
        rw [hcard, hsub, hsum]
        congr 2
        push_cast; ring
      · apply Finset.sum_congr rfl
        intro S hS
        have hSsub : S ⊆ Finset.Icc 1 m := Finset.mem_powerset.mp hS
        have hcardle : S.card ≤ m := by
          calc S.card ≤ (Finset.Icc 1 m).card := Finset.card_le_card hSsub
            _ = m := by simp
        have hsub : m + 1 - S.card = (m - S.card) + 1 := by omega
        rw [hsub, pow_succ]
        ring
    · intro S₁ hS₁ S₂ hS₂ h
      have h1 : m + 1 ∉ S₁ := fun hm => hnotmem (Finset.mem_powerset.mp hS₁ hm)
      have h2 : m + 1 ∉ S₂ := fun hm => hnotmem (Finset.mem_powerset.mp hS₂ hm)
      have := congrArg (fun T => T.erase (m + 1)) h
      simpa [Finset.erase_insert h1, Finset.erase_insert h2] using this
  · rw [Finset.disjoint_left]
    intro T hT1 hT2
    rcases Finset.mem_image.mp hT2 with ⟨S, _, rfl⟩
    have hsub := Finset.mem_powerset.mp hT1
    exact hnotmem (hsub (Finset.mem_insert_self (m + 1) S))

private lemma evalStep_succ_sum (m : ℕ) (P : ℤ → ℤ) (y : ℤ) :
    evalStep (m + 1) P y =
    ∑ t ∈ Finset.range (2 * m + 1), evalStep m (fun z => P (z + 1) - P z) (y + t) := by
  rw [evalStep_succ_diff]
  have htel : ∀ (Q : ℤ → ℤ) (N : ℕ) (x : ℤ),
      Q (x + N) - Q x = ∑ t ∈ Finset.range N, (Q (x + t + 1) - Q (x + t)) := by
    intro Q N x
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, ← ih]
      push_cast
      have : x + ((N : ℤ) + 1) = x + (N : ℤ) + 1 := by ring
      rw [this]
      ring
  have harg : y + (2 * (m + 1 : ℤ) - 1) = y + ((2 * m + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [harg, htel (evalStep m P) (2 * m + 1) y]
  apply Finset.sum_congr rfl
  intro t _
  unfold evalStep
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro S _
  have h1 : y + (t : ℤ) + 1 + ∑ k ∈ S, (2 * (k : ℤ) - 1) =
      (y + (t : ℤ) + ∑ k ∈ S, (2 * (k : ℤ) - 1)) + 1 := by ring
  rw [h1]
  ring

private lemma dvd_evalStep_of_dvd_Δ (m : ℕ) :
    ∀ (P : ℤ → ℤ) (d : ℤ), (∀ x : ℤ, d ∣ Δ P m x) → ∀ y : ℤ, d ∣ evalStep m P y := by
  induction m with
  | zero =>
    intro P d h y
    rw [evalStep_zero]
    simpa [Δ_zero] using h y
  | succ m ih =>
    intro P d h y
    rw [evalStep_succ_sum]
    apply Finset.dvd_sum
    intro t _
    apply ih (fun z => P (z + 1) - P z) d
    intro x
    rw [Δ_step_eq_succ]
    exact h x

private lemma evalStep_eq_zero_of_Δ_eq_zero (m : ℕ) :
    ∀ (P : ℤ → ℤ), (∀ x : ℤ, Δ P m x = 0) → ∀ y : ℤ, evalStep m P y = 0 := by
  induction m with
  | zero =>
    intro P h y
    rw [evalStep_zero]
    simpa [Δ_zero] using h y
  | succ m ih =>
    intro P h y
    rw [evalStep_succ_sum]
    apply Finset.sum_eq_zero
    intro t _
    apply ih (fun z => P (z + 1) - P z)
    intro x
    rw [Δ_step_eq_succ]
    exact h x

private lemma w_eq_evalStep (m n : ℕ) :
    OMA.S_oeis_a215066.w m n = evalStep m (fun y => y ^ n) 0 := by
  unfold OMA.S_oeis_a215066.w evalStep
  simp only [zero_add]

private lemma fact_dvd_w (m n : ℕ) : (m.factorial : ℤ) ∣ OMA.S_oeis_a215066.w m n := by
  rw [w_eq_evalStep]
  exact dvd_evalStep_of_dvd_Δ m (fun y => y ^ n) (m.factorial : ℤ) (fact_dvd_Δ_pow n m) 0

private lemma w_eq_zero_of_gt {m n : ℕ} (h : n < m) : OMA.S_oeis_a215066.w m n = 0 := by
  rw [w_eq_evalStep]
  exact evalStep_eq_zero_of_Δ_eq_zero m (fun y => y ^ n) (Δ_pow_eq_zero_of_lt n m h) 0

private lemma a_eq_sum_mod (M n : ℕ) (hM : 1 ≤ M) :
    OMA.S_oeis_a215066.a n ≡ ∑ m ∈ Finset.range M, OMA.S_oeis_a215066.w m n [ZMOD M] := by
  rw [← ZMod.intCast_eq_intCast_iff]
  unfold OMA.S_oeis_a215066.a
  push_cast
  by_cases h : n + 1 ≤ M
  · have hsplit : Finset.range M = Finset.range (n + 1) ∪ (Finset.range M \ Finset.range (n + 1)) := by
      ext x; simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_range]; omega
    rw [hsplit, Finset.sum_union disjoint_sdiff_self_right]
    have htail : ∑ m ∈ Finset.range M \ Finset.range (n + 1), (OMA.S_oeis_a215066.w m n : ZMod M) = 0 := by
      apply Finset.sum_eq_zero
      intro m hm
      simp only [Finset.mem_sdiff, Finset.mem_range] at hm
      rw [w_eq_zero_of_gt (by omega), Int.cast_zero]
    rw [htail, add_zero]
  · have hsplit : Finset.range (n + 1) = Finset.range M ∪ (Finset.range (n + 1) \ Finset.range M) := by
      ext x; simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_range]; omega
    rw [hsplit, Finset.sum_union disjoint_sdiff_self_right]
    have htail : ∑ m ∈ Finset.range (n + 1) \ Finset.range M, (OMA.S_oeis_a215066.w m n : ZMod M) = 0 := by
      apply Finset.sum_eq_zero
      intro m hm
      simp only [Finset.mem_sdiff, Finset.mem_range] at hm
      have hdvd : (M : ℤ) ∣ OMA.S_oeis_a215066.w m n :=
        dvd_trans (Int.natCast_dvd_natCast.mpr (Nat.dvd_factorial hM (by omega))) (fact_dvd_w m n)
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).mpr hdvd
    rw [htail, add_zero]

private lemma pow_add_totient_modEq (r : ℕ) :
    ∀ k : ℕ, 1 ≤ k → ∀ n : ℕ, k ≤ n → r ^ (n + Nat.totient k) ≡ r ^ n [MOD k] := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk n hn
    by_cases hk1 : k = 1
    · subst hk1; exact Nat.modEq_one
    · set p := k.minFac
      have hp : p.Prime := Nat.minFac_prime (by omega)
      set e := k.factorization p
      have he_pos : 1 ≤ e :=
        (Nat.Prime.dvd_iff_one_le_factorization hp (by omega)).mp (Nat.minFac_dvd k)
      set q := p ^ e
      have hq_dvd : q ∣ k := Nat.ordProj_dvd k p
      set m := k / q
      have hqm : q * m = k := Nat.mul_div_cancel' hq_dvd
      have hcop : Nat.Coprime q m := by
        have hpm : ¬ p ∣ m := by
          intro hpm
          have hpow1 : p ^ (e + 1) ∣ k := by
            rcases hpm with ⟨t, ht⟩
            refine ⟨t, ?_⟩
            calc k = p ^ e * m := hqm.symm
              _ = p ^ e * (p * t) := by rw [ht]
              _ = p ^ (e + 1) * t := by rw [pow_succ]; ring
          have hle := (Nat.Prime.pow_dvd_iff_le_factorization hp (by omega)).mp hpow1
          omega
        exact (hp.coprime_iff_not_dvd.mpr hpm).pow_left e
      have hm_pos : 1 ≤ m := by
        rcases Nat.eq_zero_or_pos m with h0 | hpos
        · rw [h0, mul_zero] at hqm; omega
        · exact hpos
      have hm_lt : m < k := by
        have hq_gt1 : 1 < q := one_lt_pow₀ hp.one_lt (by omega)
        nlinarith
      suffices h : r ^ (n + Nat.totient k) ≡ r ^ n [MOD q * m] by rwa [hqm] at h
      rw [← Nat.modEq_and_modEq_iff_modEq_mul hcop]
      constructor
      · by_cases hpr : p ∣ r
        · have he_le : e ≤ n := by
            have h1 : e < p ^ e := Nat.lt_pow_self hp.one_lt
            have h2 : q ≤ k := Nat.le_of_dvd (by omega) hq_dvd
            omega
          have hd1 : q ∣ r ^ n := by
            rcases hpr with ⟨t, rfl⟩
            rw [mul_pow]
            exact dvd_mul_of_dvd_left (pow_dvd_pow p he_le) _
          have hd2 : q ∣ r ^ (n + Nat.totient k) :=
            dvd_trans hd1 (pow_dvd_pow r (Nat.le_add_right n _))
          rw [Nat.ModEq, Nat.mod_eq_zero_of_dvd hd1, Nat.mod_eq_zero_of_dvd hd2]
        · have hcop_rq : Nat.Coprime r q := (hp.coprime_iff_not_dvd.mpr hpr).symm.pow_right e
          have heuler : r ^ Nat.totient q ≡ 1 [MOD q] := Nat.ModEq.pow_totient hcop_rq
          have htdvd : Nat.totient q ∣ Nat.totient k := Nat.totient_dvd_of_dvd hq_dvd
          rcases htdvd with ⟨t, ht⟩
          have hphi : r ^ Nat.totient k ≡ 1 [MOD q] := by
            rw [ht, pow_mul]
            simpa using heuler.pow t
          rw [pow_add]
          simpa using (Nat.ModEq.refl (r ^ n)).mul hphi
      · have hm_dvd : m ∣ k := ⟨q, by linarith⟩
        have htdvd : Nat.totient m ∣ Nat.totient k := Nat.totient_dvd_of_dvd hm_dvd
        rcases htdvd with ⟨t, ht⟩
        rw [ht]
        have hiter : ∀ s : ℕ, r ^ (n + Nat.totient m * s) ≡ r ^ n [MOD m] := by
          intro s
          induction s with
          | zero => simp [Nat.ModEq]
          | succ s ihs =>
            have hstep : r ^ (n + Nat.totient m * s + Nat.totient m) ≡
                r ^ (n + Nat.totient m * s) [MOD m] :=
              ih m hm_lt hm_pos (n + Nat.totient m * s) (by omega)
            rw [show n + Nat.totient m * (s + 1) = n + Nat.totient m * s + Nat.totient m by ring]
            exact hstep.trans ihs
        exact hiter t

private lemma neg_one_pow_totient_zmod (k : ℕ) (hk : 1 ≤ k) :
    ((-1 : ZMod k) ^ Nat.totient k) = 1 := by
  by_cases hk1 : k = 1
  · subst hk1; exact Subsingleton.elim _ _
  · by_cases hk2 : k = 2
    · subst hk2; decide
    · have heven : Even (Nat.totient k) := Nat.totient_even (by omega)
      rcases heven with ⟨t, ht⟩
      rw [ht, ← two_mul, pow_mul]
      norm_num

private lemma int_pow_gauss_zmod (c : ℤ) (p n r : ℕ) (hp : p.Prime) (hn : 1 ≤ n) (hr : 1 ≤ r) :
    (c : ZMod (p ^ r)) ^ (n * p ^ r) = (c : ZMod (p ^ r)) ^ (n * p ^ (r - 1)) := by
  by_cases hpc : (p : ℤ) ∣ c
  · have hge : r ≤ n * p ^ (r - 1) := by
      have h1 : r ≤ 2 ^ (r - 1) := by
        cases r with
        | zero => omega
        | succ r' =>
          rw [Nat.add_sub_cancel]
          have := Nat.lt_two_pow_self (n := r')
          omega
      have h2 : 2 ^ (r - 1) ≤ p ^ (r - 1) := Nat.pow_le_pow_left hp.two_le (r - 1)
      nlinarith
    have hle : n * p ^ (r - 1) ≤ n * p ^ r :=
      Nat.mul_le_mul_left n (Nat.pow_le_pow_right hp.pos (by omega))
    have hd1 : ((p ^ r : ℕ) : ℤ) ∣ c ^ (n * p ^ (r - 1)) := by
      rcases hpc with ⟨t, rfl⟩
      rw [mul_pow, Nat.cast_pow]
      exact dvd_mul_of_dvd_left (pow_dvd_pow (p : ℤ) hge) _
    have hd2 : ((p ^ r : ℕ) : ℤ) ∣ c ^ (n * p ^ r) :=
      dvd_trans hd1 (pow_dvd_pow c hle)
    have hz1 : (c : ZMod (p ^ r)) ^ (n * p ^ (r - 1)) = 0 := by
      rw [← Int.cast_pow]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hd1
    have hz2 : (c : ZMod (p ^ r)) ^ (n * p ^ r) = 0 := by
      rw [← Int.cast_pow]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hd2
    rw [hz1, hz2]
  · have hcop_nat : Nat.Coprime c.natAbs (p ^ r) := by
      have hndvd : ¬ p ∣ c.natAbs := fun h => hpc (Int.natCast_dvd.mpr h)
      exact (hp.coprime_iff_not_dvd.mpr hndvd).symm.pow_right r
    have heuler_nat : c.natAbs ^ Nat.totient (p ^ r) ≡ 1 [MOD p ^ r] :=
      Nat.ModEq.pow_totient hcop_nat
    have hphi_eq : Nat.totient (p ^ r) = p ^ (r - 1) * (p - 1) := Nat.totient_prime_pow hp hr
    have hdiff : n * p ^ r = n * p ^ (r - 1) + n * Nat.totient (p ^ r) := by
      rw [hphi_eq]
      have hpow : p ^ r = p ^ (r - 1) * p := by
        have : r = (r - 1) + 1 := by omega
        conv_lhs => rw [this, pow_succ]
      have hp1 : p = 1 + (p - 1) := by have := hp.two_le; omega
      have h2 : p ^ (r - 1) * p = p ^ (r - 1) + p ^ (r - 1) * (p - 1) := by
        nth_rw 2 [hp1]; ring
      rw [hpow, h2]; ring
    rw [hdiff, pow_add]
    have hunit : (c : ZMod (p ^ r)) ^ (n * Nat.totient (p ^ r)) = 1 := by
      have hsign : (c : ZMod (p ^ r)) ^ Nat.totient (p ^ r) = 1 := by
        by_cases hc0 : 0 ≤ c
        · have heq : (c.natAbs : ℤ) = c := Int.natAbs_of_nonneg hc0
          rw [← heq, Int.cast_natCast, ← Nat.cast_pow]
          simpa using (ZMod.natCast_eq_natCast_iff _ _ (p ^ r)).mpr heuler_nat
        · have heq : -(c.natAbs : ℤ) = c := by omega
          rw [← heq, Int.cast_neg, Int.cast_natCast, neg_eq_neg_one_mul, mul_pow]
          have h1 : ((c.natAbs : ZMod (p ^ r)) ^ Nat.totient (p ^ r)) = 1 := by
            rw [← Nat.cast_pow]
            simpa using (ZMod.natCast_eq_natCast_iff _ _ (p ^ r)).mpr heuler_nat
          rw [h1, mul_one]
          exact neg_one_pow_totient_zmod (p ^ r) (Nat.one_le_pow r p hp.pos)
      rw [mul_comm, pow_mul, hsign, one_pow]
    rw [hunit, mul_one]

private lemma zmod_pow_add_pred {p n : ℕ} (hp : p.Prime) (hn : 1 ≤ n) (x : ZMod p) :
    x ^ (n + (p - 1)) = x ^ n := by
  have : Fact p.Prime := ⟨hp⟩
  by_cases hx : x = 0
  · subst hx
    rw [zero_pow (by omega), zero_pow (by omega)]
  · rw [pow_add, ZMod.pow_card_sub_one_eq_one hx, mul_one]

end OeisA215066Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a215066.main := by
  refine ⟨?_, ?_, ?_⟩
  · intro p n r hp hn hr
    have hM : 1 ≤ p ^ r := Nat.one_le_pow r p hp.pos
    have h1 := OeisA215066Proof.a_eq_sum_mod (p ^ r) (n * p ^ r) hM
    have h2 := OeisA215066Proof.a_eq_sum_mod (p ^ r) (n * p ^ (r - 1)) hM
    refine h1.trans (Int.ModEq.trans ?_ h2.symm)
    rw [← ZMod.intCast_eq_intCast_iff]
    push_cast
    apply Finset.sum_congr rfl
    intro m _
    unfold OMA.S_oeis_a215066.w
    push_cast
    apply Finset.sum_congr rfl
    intro S _
    congr 1
    have hc := OeisA215066Proof.int_pow_gauss_zmod (∑ k ∈ S, (2 * (k : ℤ) - 1)) p n r hp hn hr
    push_cast at hc
    exact hc
  · intro p n hp hn
    have h1 := OeisA215066Proof.a_eq_sum_mod p (n + (p - 1)) hp.pos
    have h2 := OeisA215066Proof.a_eq_sum_mod p n hp.pos
    refine h1.trans (Int.ModEq.trans ?_ h2.symm)
    rw [← ZMod.intCast_eq_intCast_iff]
    push_cast
    apply Finset.sum_congr rfl
    intro m _
    unfold OMA.S_oeis_a215066.w
    push_cast
    apply Finset.sum_congr rfl
    intro S _
    congr 1
    exact OeisA215066Proof.zmod_pow_add_pred hp hn _
  · intro k hk
    refine ⟨k, fun n hn => ?_⟩
    have h1 := OeisA215066Proof.a_eq_sum_mod k (n + Nat.totient k) hk
    have h2 := OeisA215066Proof.a_eq_sum_mod k n hk
    refine h1.trans (Int.ModEq.trans ?_ h2.symm)
    rw [← ZMod.intCast_eq_intCast_iff]
    push_cast
    apply Finset.sum_congr rfl
    intro m _
    unfold OMA.S_oeis_a215066.w
    push_cast
    apply Finset.sum_congr rfl
    intro S hS
    congr 1
    have hSsub : S ⊆ Finset.Icc 1 m := Finset.mem_powerset.mp hS
    set c : ℕ := ∑ j ∈ S, (2 * j - 1)
    have hc_eq : (∑ j ∈ S, (2 * (j : ZMod k) - 1)) = (c : ZMod k) := by
      dsimp only [c]
      rw [Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have hj1 : 1 ≤ j := (Finset.mem_Icc.mp (hSsub hj)).1
      rw [Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    rw [hc_eq]
    simpa using (ZMod.natCast_eq_natCast_iff _ _ k).mpr
      (OeisA215066Proof.pow_add_totient_modEq c k hk n hn)
