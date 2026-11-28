import OMAStatements.S_oeis_a164005
import Mathlib.Tactic

-- Problem: A164005: Zero together with row 5 of the array in A163280.
-- Upstream: formal-conjectures statements/oeis-a164005.lean:0 (declaration OMA.S_oeis_a164005.main)
-- Credit: @LordDavidDev (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA

open OMA.S_oeis_a164005

/-- If `lowerDiv j = n` with `n > 0` and `j ≠ 0`, then `n` is itself an admissible divisor of `j`:
`n ∣ j` and `n * n ≤ j`. -/
lemma mem_of_lowerDiv {j n : ℕ} (hj : j ≠ 0) (hn : 0 < n) (h : lowerDiv j = n) :
    n ∣ j ∧ n * n ≤ j := by
  unfold lowerDiv at h
  set s := (Nat.divisors j).filter (fun d => d * d ≤ j) with hs
  have hmem1 : 1 ∈ s := by
    rw [hs, Finset.mem_filter, Nat.mem_divisors]
    exact ⟨⟨one_dvd j, hj⟩, by omega⟩
  have hle : n ∈ s := by
    by_contra hnot
    have hall : ∀ d ∈ s, d < n := by
      intro d hd
      have hdle : d ≤ n := by
        rw [← h]
        exact Finset.le_sup (f := id) hd
      rcases lt_or_eq_of_le hdle with h' | h'
      · exact h'
      · exact absurd (h' ▸ hd) hnot
    have hlt : s.sup id < n := by
      rw [Finset.sup_lt_iff hn]
      exact hall
    omega
  rw [hs, Finset.mem_filter, Nat.mem_divisors] at hle
  exact ⟨hle.1.1, hle.2⟩

/-- For `n ≥ 3` and `n ≤ m ≤ n + 4`, the largest divisor of `n * m` that is at most its square
root is exactly `n`. The only possible larger candidate is `n + 1`, which exceeds `√(nᵐ)` except
when `m = n + 1`, and in that case it is coprime to `n` and would have to divide `m`. -/
lemma lowerDiv_mul (n m : ℕ) (hn : 3 ≤ n) (hm1 : n ≤ m) (hm2 : m ≤ n + 4) :
    lowerDiv (n * m) = n := by
  unfold lowerDiv
  have hprod : n * m ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
  set s := (Nat.divisors (n * m)).filter (fun d => d * d ≤ n * m) with hs
  have hmem : n ∈ s := by
    rw [hs, Finset.mem_filter, Nat.mem_divisors]
    exact ⟨⟨dvd_mul_right n m, hprod⟩, by nlinarith⟩
  have hle : ∀ d ∈ s, d ≤ n := by
    intro d hd
    rw [hs, Finset.mem_filter, Nat.mem_divisors] at hd
    obtain ⟨⟨hdvd, -⟩, hdsq⟩ := hd
    by_contra hgt
    push_neg at hgt
    have hlt : d < n + 2 := by
      by_contra hge
      push_neg at hge
      nlinarith
    have hd1 : d = n + 1 := by omega
    subst hd1
    have hcop : Nat.Coprime (n + 1) n := by
      have := Nat.coprime_self_add_left (m := n) (n := 1)
      simpa using this.mpr (Nat.coprime_one_left n)
    have hdiv : (n + 1) ∣ m := by
      have h' : (n + 1) ∣ n * m := hdvd
      exact hcop.dvd_of_dvd_mul_left (by rwa [mul_comm] at h')
    obtain ⟨k, hk⟩ := hdiv
    have hkpos : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h0 | h
      · rw [h0, mul_zero] at hk; omega
      exact h
    have hk1 : k = 1 := by
      by_contra hne
      have h2 : 2 ≤ k := by omega
      nlinarith
    subst hk1
    simp only [mul_one] at hk
    nlinarith
  have hsup : s.sup id = n := by
    apply le_antisymm
    · rw [Finset.sup_le_iff]
      intro d hd
      exact hle d hd
    · have := Finset.le_sup (f := id) hmem
      simpa using this
  exact hsup



/-- For `n ≥ 3`, exactly four numbers below `n * (n + 4)` have `lowerDiv` equal to `n`. -/
lemma count_lowerDiv (n : ℕ) (hn : 3 ≤ n) :
    Nat.count (fun j => lowerDiv j = n) (n * (n + 4)) = 4 := by
  rw [Nat.count_eq_card_filter_range]
  have hset : {x ∈ Finset.range (n * (n + 4)) | lowerDiv x = n}
      = ({n * n, n * (n + 1), n * (n + 2), n * (n + 3)} : Finset ℕ) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hlt, hP⟩
      have hjne : j ≠ 0 := by
        rintro rfl
        simp [lowerDiv] at hP
        omega
      obtain ⟨hdvd, hsq⟩ := mem_of_lowerDiv hjne (by omega) hP
      obtain ⟨m, rfl⟩ := hdvd
      have hm1 : n ≤ m := by
        by_contra hlt2
        push_neg at hlt2
        nlinarith
      have hm2 : m < n + 4 := by
        by_contra hge
        push_neg at hge
        nlinarith
      have hm3 : m = n ∨ m = n + 1 ∨ m = n + 2 ∨ m = n + 3 := by omega
      rcases hm3 with h | h | h | h <;> subst h
      · left; ring
      · right; left; ring
      · right; right; left; ring
      · right; right; right; ring
    · rintro (h | h | h | h)
      · subst h
        exact ⟨by nlinarith, lowerDiv_mul n n hn le_rfl (by omega)⟩
      · subst h
        exact ⟨by nlinarith, lowerDiv_mul n (n + 1) hn (by omega) (by omega)⟩
      · subst h
        exact ⟨by nlinarith, lowerDiv_mul n (n + 2) hn (by omega) (by omega)⟩
      · subst h
        exact ⟨by nlinarith, lowerDiv_mul n (n + 3) hn (by omega) (by omega)⟩
  rw [hset, Finset.card_eq_four]
  exact ⟨n * n, n * (n + 1), n * (n + 2), n * (n + 3),
    by nlinarith, by nlinarith, by nlinarith, by nlinarith, by nlinarith, by nlinarith, rfl⟩


end OMA

open OMA.S_oeis_a164005

/-- The conjecture: row 5 of A163280 equals A100451 shifted. -/
theorem OMA.solution : type_of% @OMA.S_oeis_a164005.main := by
  intro n
  by_cases h0 : n = 0
  · subst h0
    simp [a, A100451]
  have ha : a n = Nat.nth (fun j => lowerDiv j = n) 4 := by
    simp only [a, T, if_neg h0]
  rw [ha]
  rcases (by omega : n = 1 ∨ n = 2 ∨ 3 ≤ n) with h1 | h2 | h3
  · subst h1
    have hP : lowerDiv 7 = 1 := by decide
    have hc : Nat.count (fun j => lowerDiv j = 1) 7 = 4 := by decide
    have hnth := Nat.nth_count (p := fun j => lowerDiv j = 1) hP
    rw [hc] at hnth
    rw [hnth]
    simp [A100451]
  · subst h2
    have hP : lowerDiv 14 = 2 := by decide
    have hc : Nat.count (fun j => lowerDiv j = 2) 14 = 4 := by decide
    have hnth := Nat.nth_count (p := fun j => lowerDiv j = 2) hP
    rw [hc] at hnth
    rw [hnth]
    simp only [A100451, if_neg (show ¬ (4 : ℕ) ≤ 2 by norm_num), show (4 : ℕ) - 2 = 2 by norm_num]
    norm_num
  · have hP : lowerDiv (n * (n + 4)) = n := lowerDiv_mul n (n + 4) h3 (by omega) (by omega)
    have hc : Nat.count (fun j => lowerDiv j = n) (n * (n + 4)) = 4 := count_lowerDiv n h3
    have hnth := Nat.nth_count (p := fun j => lowerDiv j = n) hP
    rw [hc] at hnth
    rw [hnth]
    simp only [A100451]
    rw [if_neg (show ¬ (n + 2 ≤ 2) by omega), show n + 2 - 2 = n by omega]
    have h2 : ((n + 2) ^ 2 - 2) / n = n + 4 := by
      have he : (n + 2) ^ 2 - 2 = n * (n + 4) + 2 := by
        rw [Nat.sub_eq_iff_eq_add (by nlinarith)]
        ring
      rw [he]
      refine Nat.div_eq_of_lt_le ?_ ?_ <;> nlinarith
    rw [h2]
