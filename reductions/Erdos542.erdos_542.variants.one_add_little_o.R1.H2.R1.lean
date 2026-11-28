import OMAReductions.R_Erdos542_erdos_542_variants_one_add_little_o_R1
import Mathlib

-- Reduction Erdos542.erdos_542.variants.one_add_little_o.R1.H2.R1 of step Erdos542.erdos_542.variants.one_add_little_o.R1.H2
-- Credit: @rickmanelius

/-!
# Erdős 542 with a fixed member: the case `s = 4` proved, split by primality

The step asks, for each fixed `s ≥ 4`, that every `A ⊆ [1, n]` with `lcm(a, b) > n` for distinct
`a, b ∈ A` and `s ∈ A` satisfies `∑ 1 / a ≤ 1 + o(1)`.

Proved below, with no hypothesis (`case_four`): the case `s = 4`, in the stronger form
`∑ 1 / a ≤ 1` for `n ≥ 400`. Since `lcm(4, a) > n`, every other member `a` is odd with `4 a > n`,
or twice an odd number with `2 a > n` (a multiple of `4` would give `lcm(4, a) = a ≤ n`). Its odd
part lies in `(n / 4, n]`, and taking odd parts is injective on the other members: an odd `b` and
`2 b` cannot both lie in `A`, as `lcm(b, 2 b) = 2 b ≤ n`. Hence
`∑ 1 / a ≤ 1 / 4 + ∑_{n / 4 < b ≤ n, b odd} 1 / b ≤ 1 / 4 + (1 / m + log (n / m)) / 2` with
`m = ⌊n / 4⌋` (`odd_tail`, from `1 / c ≤ log c - log (c - 1)`), and the right side tends to
`1 / 4 + log 2 ≈ 0.943`. The same odd-part map works for any member `2 ^ j`, but the bound
`2 ^ (-j) + (j / 2) log 2` it gives exceeds `1` from `j = 3` on.

The other fixed members are left as two hypotheses, each the step restricted to them:
* `H1`: a fixed prime member `p ≥ 5`; every other member then lies in `(n / p, n]` and is prime to
  `p`.
* `H2`: a fixed composite member `s ≥ 6`.
-/

namespace OMA.R_Erdos542_erdos_542_variants_one_add_little_o_R1_H2_R1

open Finset

/-- The target for sets with a fixed prime member `p ≥ 5`. -/
def H1 : Prop :=
  ∀ p : ℕ, p.Prime → 5 ≤ p → ∃ o : ℕ → ℝ, Filter.Tendsto o Filter.atTop (nhds 0) ∧
    ∀ (n : ℕ) (A : Finset ℕ), Erdos542.IsLcmFree n A → p ∈ A →
      ∑ a ∈ A, (1 : ℝ) / a ≤ 1 + o n

/-- The target for sets with a fixed composite member `s ≥ 6`. -/
def H2 : Prop :=
  ∀ s : ℕ, 6 ≤ s → ¬ s.Prime → ∃ o : ℕ → ℝ, Filter.Tendsto o Filter.atTop (nhds 0) ∧
    ∀ (n : ℕ) (A : Finset ℕ), Erdos542.IsLcmFree n A → s ∈ A →
      ∑ a ∈ A, (1 : ℝ) / a ≤ 1 + o n

/-- `1 / c ≤ log c - log (c - 1)` for `c ≥ 2`. -/
lemma inv_le_log_sub {c : ℕ} (hc : 2 ≤ c) :
    (1 : ℝ) / c ≤ Real.log c - Real.log ((c : ℝ) - 1) := by
  have hc1 : (2 : ℝ) ≤ c := by exact_mod_cast hc
  have hpos : (0 : ℝ) < (c : ℝ) - 1 := by linarith
  have hcpos : (0 : ℝ) < c := by linarith
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((c : ℝ) - 1) / c by positivity)
  rw [Real.log_div hpos.ne' hcpos.ne'] at h
  have e : ((c : ℝ) - 1) / c - 1 = -(1 / c) := by field_simp; ring
  linarith

/-- Telescoping: `∑_{m < c ≤ n} 1 / c ≤ log n - log m`. -/
lemma tail_le_log (m : ℕ) (hm : 1 ≤ m) (n : ℕ) (hmn : m ≤ n) :
    ∑ c ∈ Ioc m n, (1 : ℝ) / c ≤ Real.log n - Real.log m := by
  induction n, hmn using Nat.le_induction with
  | base => simp
  | succ n hmn ih =>
    rw [Finset.sum_Ioc_succ_top hmn]
    have h := inv_le_log_sub (c := n + 1) (by omega)
    push_cast at h ⊢
    have e : ((n : ℝ) + 1 - 1) = n := by ring
    rw [e] at h
    linarith

/-- Odd terms only: `∑_{m < b ≤ n, b odd} 1 / b ≤ (1 / m + log n - log m) / 2`, by comparing each
odd `b` with the even `b - 1`. -/
lemma odd_tail (m n : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n) :
    ∑ b ∈ (Ioc m n).filter Odd, (1 : ℝ) / b ≤ (1 / m + (Real.log n - Real.log m)) / 2 := by
  set O := (Ioc m n).filter Odd with hO
  set E := O.image (fun b => b - 1) with hE
  have hsumE : ∑ c ∈ E, (1 : ℝ) / c = ∑ b ∈ O, (1 : ℝ) / ((b - 1 : ℕ) : ℝ) := by
    rw [hE, sum_image]
    intro b hb b' hb' h
    simp only [Finset.mem_coe, hO, mem_filter, mem_Ioc] at hb hb'
    simp only at h
    omega
  have hle : ∑ b ∈ O, (1 : ℝ) / b ≤ ∑ b ∈ O, (1 : ℝ) / ((b - 1 : ℕ) : ℝ) := by
    apply sum_le_sum
    intro b hb
    simp only [hO, mem_filter, mem_Ioc] at hb
    have hb1 : 1 ≤ b - 1 := by omega
    have h1 : ((b - 1 : ℕ) : ℝ) ≤ b := by exact_mod_cast Nat.sub_le b 1
    have hpos : (0 : ℝ) < ((b - 1 : ℕ) : ℝ) := by exact_mod_cast hb1
    exact one_div_le_one_div_of_le hpos h1
  have hdisj : Disjoint O E := by
    rw [Finset.disjoint_left]
    intro b hb hbE
    simp only [hE, mem_image] at hbE
    obtain ⟨b', hb', hbb⟩ := hbE
    simp only [hO, mem_filter, mem_Ioc] at hb hb'
    obtain ⟨_, x, hx⟩ := hb
    obtain ⟨⟨h1, _⟩, y, hy⟩ := hb'
    omega
  have hsub : O ∪ E ⊆ Icc m n := by
    intro c hc
    rw [mem_union] at hc
    rcases hc with hc | hc
    · simp only [hO, mem_filter, mem_Ioc] at hc
      rw [mem_Icc]
      omega
    · simp only [hE, mem_image, hO, mem_filter, mem_Ioc] at hc
      obtain ⟨b, ⟨⟨h1, h2⟩, _⟩, rfl⟩ := hc
      rw [mem_Icc]
      omega
  have hIcc : ∑ c ∈ Icc m n, (1 : ℝ) / c = 1 / m + ∑ c ∈ Ioc m n, (1 : ℝ) / c := by
    rw [← Finset.add_sum_Ioc_eq_sum_Icc hmn]
  have hU : ∑ c ∈ O ∪ E, (1 : ℝ) / c ≤ ∑ c ∈ Icc m n, (1 : ℝ) / c :=
    sum_le_sum_of_subset_of_nonneg hsub (fun c _ _ => by positivity)
  rw [sum_union hdisj] at hU
  have htail := tail_le_log m hm n hmn
  linarith [hsumE, hle, hU, hIcc, htail]

/-- `(1 / m + log n - log m) / 2 ≤ 3 / 4` when `m = ⌊n / 4⌋ ≥ 100`. -/
lemma quarter_bound (n : ℕ) (hn : 400 ≤ n) :
    (1 / ((n / 4 : ℕ) : ℝ) + (Real.log n - Real.log ((n / 4 : ℕ) : ℝ))) / 2 ≤ 3 / 4 := by
  set m := n / 4 with hm
  have hm100 : 100 ≤ m := by omega
  have hnm : n ≤ 4 * (m + 1) := by omega
  have hmR : (100 : ℝ) ≤ m := by exact_mod_cast hm100
  have hmpos : (0 : ℝ) < m := by linarith
  have hnR : (n : ℝ) ≤ 4 * ((m : ℝ) + 1) := by exact_mod_cast hnm
  have hnpos : (0 : ℝ) < n := by
    have : (400 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have h1 : Real.log n ≤ Real.log 4 + Real.log ((m : ℝ) + 1) := by
    rw [← Real.log_mul (by norm_num) (by linarith)]
    exact Real.log_le_log hnpos hnR
  have h2 : Real.log ((m : ℝ) + 1) - Real.log m ≤ 1 / m := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((m : ℝ) + 1) / m by positivity)
    rw [Real.log_div (by linarith) hmpos.ne'] at h
    have e : ((m : ℝ) + 1) / m - 1 = 1 / m := by field_simp; ring
    linarith
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hl2 := Real.log_two_lt_d9
  have hinv : 1 / (m : ℝ) ≤ 1 / 100 := one_div_le_one_div_of_le (by norm_num) hmR
  linarith

/-- The case `4 ∈ A` for `n ≥ 400`. Every other member `a` is odd with `n < 4 a` or twice an odd
number with `n < 2 a`, since `lcm 4 a > n`. Its odd part `φ a` lies in `(n / 4, n]`, and `φ` is
injective on the other members: an odd `b` and `2 b` cannot both lie in `A`, as
`lcm b (2 b) = 2 b ≤ n`. So `∑ 1 / a ≤ 1 / 4 + ∑_{n / 4 < b ≤ n, b odd} 1 / b ≤ 1 / 4 + 3 / 4`. -/
lemma four_mem_le_one (n : ℕ) (hn : 400 ≤ n) (A : Finset ℕ) (hA : Erdos542.IsLcmFree n A)
    (h4 : 4 ∈ A) : ∑ a ∈ A, (1 : ℝ) / a ≤ 1 := by
  obtain ⟨hAsub, hpair⟩ := hA
  have hmem : ∀ a ∈ A, 1 ≤ a ∧ a ≤ n := fun a ha => mem_Icc.mp (hAsub ha)
  have hshape : ∀ a ∈ A, a ≠ 4 → (a % 2 = 1 ∧ n < 4 * a) ∨ (a % 4 = 2 ∧ n < 2 * a) := by
    intro a ha hne
    have hlt : n < Nat.lcm 4 a := hpair h4 ha (Ne.symm hne)
    obtain ⟨ha1, haN⟩ := hmem a ha
    rcases Nat.even_or_odd a with ⟨b, hb⟩ | hodd
    · by_cases h4a : 4 ∣ a
      · exfalso
        have hd : Nat.lcm 4 a ∣ a := Nat.lcm_dvd h4a (dvd_refl a)
        have := Nat.le_of_dvd (by omega) hd
        omega
      · right
        refine ⟨by omega, ?_⟩
        have hd : Nat.lcm 4 a ∣ 2 * a := Nat.lcm_dvd ⟨b, by omega⟩ (dvd_mul_left a 2)
        have := Nat.le_of_dvd (by omega) hd
        omega
    · left
      refine ⟨Nat.odd_iff.mp hodd, ?_⟩
      have hd : Nat.lcm 4 a ∣ 4 * a := Nat.lcm_dvd (dvd_mul_right 4 a) (dvd_mul_left a 4)
      have := Nat.le_of_dvd (by omega) hd
      omega
  set φ : ℕ → ℕ := fun a => if a % 2 = 1 then a else a / 2 with hφ
  have hφo : ∀ a, a % 2 = 1 → φ a = a := fun a h => by simp [hφ, h]
  have hφe : ∀ a, a % 2 ≠ 1 → φ a = a / 2 := fun a h => by simp [hφ, h]
  have hφprop : ∀ a ∈ A.erase 4, φ a % 2 = 1 ∧ n < 4 * φ a ∧ φ a ≤ n ∧ 1 ≤ φ a ∧ φ a ≤ a := by
    intro a ha
    rw [mem_erase] at ha
    obtain ⟨hne, haA⟩ := ha
    obtain ⟨ha1, haN⟩ := hmem a haA
    rcases hshape a haA hne with ⟨hodd, hlt⟩ | ⟨h2, hlt⟩
    · rw [hφo a hodd]
      omega
    · rw [hφe a (by omega)]
      omega
  have hinj : ∀ a ∈ A.erase 4, ∀ a' ∈ A.erase 4, φ a = φ a' → a = a' := by
    intro a ha a' ha' h
    rw [mem_erase] at ha ha'
    by_contra hne
    have hlcm : n < Nat.lcm a a' := hpair ha.2 ha'.2 hne
    obtain ⟨ha1, haN⟩ := hmem a ha.2
    obtain ⟨ha1', haN'⟩ := hmem a' ha'.2
    rcases hshape a ha.2 ha.1 with ⟨hodd, _⟩ | ⟨h2, _⟩ <;>
      rcases hshape a' ha'.2 ha'.1 with ⟨hodd', _⟩ | ⟨h2', _⟩
    · rw [hφo a hodd, hφo a' hodd'] at h
      exact hne h
    · rw [hφo a hodd, hφe a' (by omega)] at h
      have hd : Nat.lcm a a' ∣ a' := Nat.lcm_dvd ⟨2, by omega⟩ dvd_rfl
      have := Nat.le_of_dvd (by omega) hd
      omega
    · rw [hφe a (by omega), hφo a' hodd'] at h
      have hd : Nat.lcm a a' ∣ a := Nat.lcm_dvd dvd_rfl ⟨2, by omega⟩
      have := Nat.le_of_dvd (by omega) hd
      omega
    · rw [hφe a (by omega), hφe a' (by omega)] at h
      exact hne (by omega)
  have hsplit : ∑ a ∈ A, (1 : ℝ) / a = 1 / 4 + ∑ a ∈ A.erase 4, (1 : ℝ) / a := by
    rw [← Finset.add_sum_erase A _ h4]
    norm_num
  have hle1 : ∑ a ∈ A.erase 4, (1 : ℝ) / a ≤ ∑ a ∈ A.erase 4, (1 : ℝ) / (φ a : ℕ) := by
    apply sum_le_sum
    intro a ha
    obtain ⟨_, _, _, h1, hle⟩ := hφprop a ha
    exact one_div_le_one_div_of_le (by exact_mod_cast h1) (by exact_mod_cast hle)
  have himg : ∑ a ∈ A.erase 4, (1 : ℝ) / (φ a : ℕ) = ∑ b ∈ (A.erase 4).image φ, (1 : ℝ) / b := by
    rw [sum_image hinj]
  have hBsub : (A.erase 4).image φ ⊆ (Ioc (n / 4) n).filter Odd := by
    intro b hb
    rw [mem_image] at hb
    obtain ⟨a, ha, rfl⟩ := hb
    obtain ⟨hodd, hlt, hle, _, _⟩ := hφprop a ha
    rw [mem_filter, mem_Ioc]
    exact ⟨⟨by omega, hle⟩, Nat.odd_iff.mpr hodd⟩
  have hB2 : ∑ b ∈ (A.erase 4).image φ, (1 : ℝ) / b ≤
      ∑ b ∈ (Ioc (n / 4) n).filter Odd, (1 : ℝ) / b :=
    sum_le_sum_of_subset_of_nonneg hBsub (fun _ _ _ => by positivity)
  have hodd := odd_tail (n / 4) n (by omega) (by omega)
  have hq := quarter_bound n hn
  linarith

/-- The case of a fixed member `4`. -/
theorem case_four : ∃ o : ℕ → ℝ, Filter.Tendsto o Filter.atTop (nhds 0) ∧
    ∀ (n : ℕ) (A : Finset ℕ), Erdos542.IsLcmFree n A → 4 ∈ A →
      ∑ a ∈ A, (1 : ℝ) / a ≤ 1 + o n := by
  refine ⟨fun n => if n < 400 then (n : ℝ) else 0, ?_, ?_⟩
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop 400] with n hn
    simp [show ¬ n < 400 by omega]
  · intro n A hA h4
    by_cases hn : n < 400
    · simp only [hn, if_true]
      have hcard : A.card ≤ n := by
        have := card_le_card hA.1
        simpa using this
      have hterm : ∀ a ∈ A, (1 : ℝ) / a ≤ 1 := by
        intro a ha
        have h1 : (1 : ℝ) ≤ a := by exact_mod_cast (mem_Icc.mp (hA.1 ha)).1
        rw [div_le_one (by linarith)]
        exact h1
      have hs := sum_le_sum hterm
      simp only [sum_const, nsmul_eq_mul, mul_one] at hs
      have hc : (A.card : ℝ) ≤ n := by exact_mod_cast hcard
      linarith
    · simp only [hn, if_false, add_zero]
      exact four_mem_le_one n (by omega) A hA h4

theorem main : H1 → H2 → OMA.R_Erdos542_erdos_542_variants_one_add_little_o_R1.H2 := by
  intro h1 h2 s hs
  rcases Nat.lt_or_ge s 5 with h | h
  · obtain rfl : s = 4 := by omega
    exact case_four
  · by_cases hp : s.Prime
    · exact h1 s hp h
    · have h6 : 6 ≤ s := by
        rcases Nat.lt_or_ge s 6 with h' | h'
        · exfalso
          obtain rfl : s = 5 := by omega
          exact hp (by norm_num)
        · exact h'
      exact h2 s h6 hp

end OMA.R_Erdos542_erdos_542_variants_one_add_little_o_R1_H2_R1
