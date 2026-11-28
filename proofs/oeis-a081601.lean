import OMAStatements.S_oeis_a081601
import Mathlib

-- Problem: OEIS A081601, conjecture of Gutkovskiy: the generating function of the numbers m
-- such that 3 does not divide S(m) = Sum_{k=0..m} C(2k, k) is
-- (x/(1 - x)) * Sum_{k>=0} 3^(k+1) x^(2^k)/(1 + x^(2^k)), that is,
-- a(n) = Sum_k 3^(k+1) * (binary digit k of n - 1) = 3 * A005836(n).
-- Statement: statements/oeis-a081601.lean (declaration OMA.S_oeis_a081601.main)
-- Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)
--
-- Proof. Let c(q) = C(2q, q). Lucas' theorem for p = 3 gives c(3q) == c(q), c(3q+1) == 2 c(q)
-- and c(3q+2) == 0 (mod 3). Thus c(3q) + c(3q+1) + c(3q+2) == 0, and by induction
-- S(3q+2) == 0, S(3q+1) == 0 and S(3q) == c(q) (mod 3). So 3 does not divide S(m) if and only
-- if m = 3q and 3 does not divide c(q).
-- Let F(j) = Sum_k 3^k * (binary digit k of j), so F(j) = (j mod 2) + 3 F(j div 2). The function
-- F is strictly increasing, 3 does not divide c(F(j)), and each q such that 3 does not divide
-- c(q) is a value of F (strong induction with the three congruences). So j -> 3 F(j) is the
-- increasing enumeration of the set, and a(n) = 3 F(n - 1).

namespace OMA.A081601

open Finset OMA.S_oeis_a081601

/-- Sum of the binary digits of j with weights 3^k, for k < N. -/
def H (N j : ℕ) : ℕ := ∑ k ∈ range N, 3 ^ k * (j / 2 ^ k % 2)

/-- A005836: the binary expansion of j, read in base 3. -/
def F (j : ℕ) : ℕ := H (j + 1) j

lemma H_stab (j d : ℕ) : H (j + d) j = H j j := by
  induction d with
  | zero => rfl
  | succ d ih =>
    have h0 : j / 2 ^ (j + d) = 0 :=
      Nat.div_eq_of_lt (lt_of_le_of_lt (Nat.le_add_right j d) Nat.lt_two_pow_self)
    have h1 : H (j + (d + 1)) j = H (j + d) j + 3 ^ (j + d) * (j / 2 ^ (j + d) % 2) := by
      rw [← add_assoc]; unfold H; rw [sum_range_succ]
    rw [h1, ih, h0]; simp

lemma H_succ (N j : ℕ) : H (N + 1) j = j % 2 + 3 * H N (j / 2) := by
  unfold H
  rw [sum_range_succ', mul_sum]
  simp only [pow_zero, Nat.div_one, one_mul]
  rw [add_comm]
  congr 1
  apply sum_congr rfl
  intro k _
  rw [Nat.div_div_eq_div_mul, pow_succ, pow_succ, mul_comm (2 ^ k) 2]
  ring

lemma F_rec (j : ℕ) : F j = j % 2 + 3 * F (j / 2) := by
  unfold F
  rw [H_succ]
  have h1 : H j (j / 2) = H (j / 2) (j / 2) := by
    have h := H_stab (j / 2) (j - j / 2)
    rwa [show j / 2 + (j - j / 2) = j by omega] at h
  have h2 : H (j / 2 + 1) (j / 2) = H (j / 2) (j / 2) := H_stab _ 1
  rw [h1, h2]

lemma F_zero : F 0 = 0 := by
  have := F_rec 0
  simp at this
  omega

lemma F_lt : ∀ b a : ℕ, a < b → F a < F b := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    intro a hab
    rw [F_rec a, F_rec b]
    by_cases h : a / 2 < b / 2
    · have := ih (b / 2) (by omega) (a / 2) h
      omega
    · have e : a / 2 = b / 2 := by omega
      rw [e]; omega

lemma luc0 (q : ℕ) : (2 * (3 * q)).choose (3 * q) % 3 = (2 * q).choose q % 3 := by
  have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := 2 * (3 * q)) (k := 3 * q)
    (p := 3)
  have e1 : 2 * (3 * q) % 3 = 0 := by omega
  have e2 : 3 * q % 3 = 0 := by omega
  have e3 : 2 * (3 * q) / 3 = 2 * q := by omega
  have e4 : 3 * q / 3 = q := by omega
  rw [e1, e2, e3, e4] at h
  have h' : (2 * (3 * q)).choose (3 * q) ≡ (2 * q).choose q [MOD 3] := by simpa using h
  exact h'

lemma luc1 (q : ℕ) :
    (2 * (3 * q + 1)).choose (3 * q + 1) % 3 = (2 * (2 * q).choose q) % 3 := by
  have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := 2 * (3 * q + 1))
    (k := 3 * q + 1) (p := 3)
  have e1 : 2 * (3 * q + 1) % 3 = 2 := by omega
  have e2 : (3 * q + 1) % 3 = 1 := by omega
  have e3 : 2 * (3 * q + 1) / 3 = 2 * q := by omega
  have e4 : (3 * q + 1) / 3 = q := by omega
  rw [e1, e2, e3, e4] at h
  have h' : (2 * (3 * q + 1)).choose (3 * q + 1) ≡ 2 * (2 * q).choose q [MOD 3] := by
    simpa using h
  exact h'

lemma luc2 (q : ℕ) : (2 * (3 * q + 2)).choose (3 * q + 2) % 3 = 0 := by
  have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := 2 * (3 * q + 2))
    (k := 3 * q + 2) (p := 3)
  have e1 : 2 * (3 * q + 2) % 3 = 1 := by omega
  have e2 : (3 * q + 2) % 3 = 2 := by omega
  rw [e1, e2] at h
  have h' : (2 * (3 * q + 2)).choose (3 * q + 2) ≡ 0 [MOD 3] := by simpa using h
  exact h'

/-- The sum Sum_{k=0..m} C(2k, k). -/
def S (m : ℕ) : ℕ := ∑ k ∈ range (m + 1), (2 * k).choose k

lemma S_succ (m : ℕ) : S (m + 1) = S m + (2 * (m + 1)).choose (m + 1) := by
  unfold S; rw [sum_range_succ]

lemma S2 (q : ℕ) : S (3 * q + 2) % 3 = 0 := by
  induction q with
  | zero => decide
  | succ q ih =>
    have s1 : S (3 * (q + 1)) = S (3 * q + 2) + (2 * (3 * (q + 1))).choose (3 * (q + 1)) := by
      have h := S_succ (3 * q + 2)
      rwa [show 3 * q + 2 + 1 = 3 * (q + 1) by ring] at h
    have s2 : S (3 * (q + 1) + 1)
        = S (3 * (q + 1)) + (2 * (3 * (q + 1) + 1)).choose (3 * (q + 1) + 1) := S_succ _
    have s3 : S (3 * (q + 1) + 2)
        = S (3 * (q + 1) + 1) + (2 * (3 * (q + 1) + 2)).choose (3 * (q + 1) + 2) := S_succ _
    have h0 := luc0 (q + 1)
    have h1 := luc1 (q + 1)
    have h2 := luc2 (q + 1)
    omega

lemma pred (m : ℕ) : ¬ 3 ∣ S m ↔ m % 3 = 0 ∧ ¬ 3 ∣ (2 * (m / 3)).choose (m / 3) := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 3 ∧ m = 3 * q + r :=
    ⟨m / 3, m % 3, Nat.mod_lt _ (by norm_num), by omega⟩
  have hS2 := S2 q
  have e2 : S (3 * q + 2) = S (3 * q + 1) + (2 * (3 * q + 2)).choose (3 * q + 2) := S_succ _
  have e1 : S (3 * q + 1) = S (3 * q) + (2 * (3 * q + 1)).choose (3 * q + 1) := S_succ _
  have h1 := luc1 q
  have h2 := luc2 q
  have hq : (3 * q + r) / 3 = q := by omega
  rw [hq]
  interval_cases r
  · simp only [add_zero] at *
    omega
  · omega
  · omega

lemma F_good (j : ℕ) : ¬ 3 ∣ (2 * F j).choose (F j) := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    by_cases hj : j = 0
    · rw [hj, F_zero]; decide
    · have h := ih (j / 2) (by omega)
      have hr := F_rec j
      have h0 := luc0 (F (j / 2))
      have h1 := luc1 (F (j / 2))
      rcases Nat.mod_two_eq_zero_or_one j with hm | hm
      · have e : F j = 3 * F (j / 2) := by omega
        rw [e]; omega
      · have e : F j = 3 * F (j / 2) + 1 := by omega
        rw [e]; omega

lemma F_surj (q : ℕ) : ¬ 3 ∣ (2 * q).choose q → ∃ j, F j = q := by
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    intro hq
    by_cases h0 : q = 0
    · exact ⟨0, by rw [F_zero, h0]⟩
    · obtain ⟨q', r, hr, rfl⟩ : ∃ q' r, r < 3 ∧ q = 3 * q' + r :=
        ⟨q / 3, q % 3, Nat.mod_lt _ (by norm_num), by omega⟩
      have l0 := luc0 q'
      have l1 := luc1 q'
      have l2 := luc2 q'
      interval_cases r
      · simp only [add_zero] at *
        obtain ⟨j', hj'⟩ := ih q' (by omega) (by omega)
        refine ⟨2 * j', ?_⟩
        rw [F_rec]
        have e1 : 2 * j' % 2 = 0 := by omega
        have e2 : 2 * j' / 2 = j' := by omega
        rw [e1, e2, hj']; ring
      · obtain ⟨j', hj'⟩ := ih q' (by omega) (by omega)
        refine ⟨2 * j' + 1, ?_⟩
        rw [F_rec]
        have e1 : (2 * j' + 1) % 2 = 1 := by omega
        have e2 : (2 * j' + 1) / 2 = j' := by omega
        rw [e1, e2, hj']; ring
      · exfalso; omega

theorem main' (n : ℕ) (hn : 1 ≤ n) :
    a n = ∑ k ∈ range n, 3 ^ (k + 1) * ((n - 1) / 2 ^ k % 2) := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  have hmono : StrictMono (fun i => 3 * F i) :=
    strictMono_nat_of_lt_succ (fun i => by have := F_lt (i + 1) i (Nat.lt_succ_self i); omega)
  have hP : ∀ m, (¬ 3 ∣ ∑ k ∈ range (m + 1), (2 * k).choose k) ↔ ∃ i, 3 * F i = m := by
    intro m
    have h := pred m
    unfold S at h
    rw [h]
    constructor
    · rintro ⟨h3, hg⟩
      obtain ⟨i, hi⟩ := F_surj _ hg
      exact ⟨i, by omega⟩
    · rintro ⟨i, rfl⟩
      have e : 3 * F i / 3 = F i := by omega
      rw [e]
      exact ⟨by omega, F_good i⟩
  have hinf : (Set.ofPred (fun m => ¬ 3 ∣ ∑ k ∈ range (m + 1), (2 * k).choose k)).Infinite := by
    have hsub : Set.range (fun i => 3 * F i)
        ⊆ Set.ofPred (fun m => ¬ 3 ∣ ∑ k ∈ range (m + 1), (2 * k).choose k) := by
      rintro _ ⟨i, rfl⟩
      exact (hP _).2 ⟨i, rfl⟩
    exact (Set.infinite_range_of_injective hmono.injective).mono hsub
  have key := Nat.nth_comp_of_strictMono (n := j) hmono
    (p := fun m => ¬ 3 ∣ ∑ k ∈ range (m + 1), (2 * k).choose k)
    (fun k hk => (hP k).1 hk) (fun hfi => absurd hfi hinf)
  have htrue : (fun i => ¬ 3 ∣ ∑ k ∈ range (3 * F i + 1), (2 * k).choose k) = fun _ => True := by
    funext i
    exact eq_true ((hP _).2 ⟨i, rfl⟩)
  rw [htrue, Nat.nth_true] at key
  unfold a
  rw [Nat.add_sub_cancel, ← key]
  show 3 * F j = _
  unfold F H
  rw [mul_sum]
  apply sum_congr rfl
  intro k _
  rw [pow_succ]; ring

end OMA.A081601

theorem OMA.solution : type_of% @OMA.S_oeis_a081601.main :=
  fun n hn => OMA.A081601.main' n hn
