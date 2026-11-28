import OMAReductions.R_Arxiv_2501_03234_conjecture_1_1_R1_H1_R1

/-!
Step `Arxiv.2501.03234.conjecture_1_1.R1.H1.R1.H1`: carry-free extraction of the cyclic triple
correlation of a binary word.

Expanding, `P = A ^ 2 * R = ∑ w i * w j * w k * B ^ (i + j + (n - 1 - k))` over `i, j, k < n`.
Every exponent fibre has at most `n ^ 2 < B` triples (the pair `(i, j)` determines `k`), so
`P` has no carries in base `B` and its `m`-th digit is the weight of the fibre over `m`
(`digit_extract`). The fibre over `n - 1` is `k = i + j`, the fibre over `2 n - 1` is
`k = i + j - n`, and together they give `k = (i + j) % n`.
-/

namespace OMA.ArxivTripleDigits

open Finset

/-- If every exponent fibre has total weight below `B`, the `m`-th base-`B` digit of
`∑ t x * B ^ e x` is the weight of the fibre over `m`. -/
theorem digit_extract {ι : Type*} (B : ℕ) (hB : 0 < B) : ∀ (m : ℕ) (s : Finset ι) (t e : ι → ℕ),
    (∀ v, ∑ x ∈ s.filter (fun x => e x = v), t x < B) →
    ((∑ x ∈ s, t x * B ^ e x) / B ^ m) % B = ∑ x ∈ s.filter (fun x => e x = m), t x := by
  intro m
  induction m with
  | zero =>
    intro s t e hb
    have h1 : ∑ x ∈ s.filter (fun x => e x = 0), t x * B ^ e x
        = ∑ x ∈ s.filter (fun x => e x = 0), t x := by
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [(Finset.mem_filter.mp hx).2, pow_zero, mul_one]
    have hQ : ∑ x ∈ s.filter (fun x => ¬ e x = 0), t x * B ^ e x
        = B * ∑ x ∈ s.filter (fun x => ¬ e x = 0), t x * B ^ (e x - 1) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x hx => ?_
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Finset.mem_filter.mp hx).2
      rw [hk, pow_succ, Nat.succ_sub_one]
      ring
    rw [pow_zero, Nat.div_one, ← Finset.sum_filter_add_sum_filter_not s (fun x => e x = 0), h1, hQ,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hb 0)]
  | succ m ih =>
    intro s t e hb
    have h1 : ∑ x ∈ s.filter (fun x => e x = 0), t x * B ^ e x
        = ∑ x ∈ s.filter (fun x => e x = 0), t x := by
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [(Finset.mem_filter.mp hx).2, pow_zero, mul_one]
    have hQ : ∑ x ∈ s.filter (fun x => ¬ e x = 0), t x * B ^ e x
        = B * ∑ x ∈ s.filter (fun x => ¬ e x = 0), t x * B ^ (e x - 1) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x hx => ?_
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Finset.mem_filter.mp hx).2
      rw [hk, pow_succ, Nat.succ_sub_one]
      ring
    have hdiv : (∑ x ∈ s, t x * B ^ e x) / B ^ (m + 1)
        = (∑ x ∈ s.filter (fun x => ¬ e x = 0), t x * B ^ (e x - 1)) / B ^ m := by
      rw [pow_succ', ← Nat.div_div_eq_div_mul,
        ← Finset.sum_filter_add_sum_filter_not s (fun x => e x = 0), h1, hQ,
        Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt (hb 0), zero_add]
    have hfib : ∀ v, (s.filter (fun x => ¬ e x = 0)).filter (fun x => e x - 1 = v)
        = s.filter (fun x => e x = v + 1) := by
      intro v
      ext x
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨⟨hx, h0⟩, h1⟩; exact ⟨hx, by omega⟩
      · rintro ⟨hx, h1⟩; exact ⟨⟨hx, by omega⟩, by omega⟩
    rw [hdiv, ih (s.filter (fun x => ¬ e x = 0)) t (fun x => e x - 1)
      (fun v => by rw [hfib v]; exact hb (v + 1)), hfib m]

end OMA.ArxivTripleDigits

open Finset in
theorem OMA.solution : OMA.R_Arxiv_2501_03234_conjecture_1_1_R1_H1_R1.H1 := by
  intro n B w hn hB hw
  simp only
  have hB0 : 0 < B := by
    have : 0 < n ^ 2 := by positivity
    omega
  set T : Finset ((ℕ × ℕ) × ℕ) := (range n ×ˢ range n) ×ˢ range n with hT
  set t : (ℕ × ℕ) × ℕ → ℕ := fun x => w x.1.1 * w x.1.2 * w x.2 with ht
  set e : (ℕ × ℕ) × ℕ → ℕ := fun x => x.1.1 + x.1.2 + (n - 1 - x.2) with he
  have hP : (∑ i ∈ range n, w i * B ^ i) ^ 2 * ∑ i ∈ range n, w i * B ^ (n - 1 - i)
      = ∑ x ∈ T, t x * B ^ e x := by
    rw [hT, Finset.sum_product, Finset.sum_product, sq, Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [ht, he, pow_add]
    ring
  have hfib : ∀ v, ∑ x ∈ T.filter (fun x => e x = v), t x < B := by
    intro v
    calc ∑ x ∈ T.filter (fun x => e x = v), t x ≤ ∑ x ∈ T.filter (fun x => e x = v), 1 := by
          refine Finset.sum_le_sum fun x hx => ?_
          have hxT := (Finset.mem_filter.mp hx).1
          simp only [hT, Finset.mem_product, Finset.mem_range] at hxT
          have h1 := hw _ hxT.1.1
          have h2 := hw _ hxT.1.2
          have h3 := hw _ hxT.2
          simp only [ht]
          calc w x.1.1 * w x.1.2 * w x.2 ≤ 1 * 1 * 1 :=
                Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
            _ = 1 := by norm_num
      _ = (T.filter (fun x => e x = v)).card := by simp
      _ ≤ (range n ×ˢ range n).card := by
          apply Finset.card_le_card_of_injOn (fun x => x.1)
          · intro x hx
            have hxT := (Finset.mem_filter.mp hx).1
            simp only [hT, Finset.mem_product] at hxT
            simpa [Finset.mem_product] using hxT.1
          · intro x hx y hy hxy
            have hx' := Finset.mem_filter.mp hx
            have hy' := Finset.mem_filter.mp hy
            simp only [hT, Finset.mem_product, Finset.mem_range, he] at hx' hy'
            simp only at hxy
            have hk : x.2 = y.2 := by
              have e1 := hx'.2
              have e2 := hy'.2
              rw [hxy] at e1
              omega
            exact Prod.ext hxy hk
      _ = n ^ 2 := by simp [sq]
      _ < B := hB
  have hlow : ∑ x ∈ T.filter (fun x => e x = n - 1), t x
      = ∑ p ∈ range n ×ˢ range n,
          if p.1 + p.2 < n then w p.1 * w p.2 * w (p.1 + p.2) else 0 := by
    rw [Finset.sum_filter, hT, Finset.sum_product]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hc : ∀ k ∈ range n, (if e (p, k) = n - 1 then t (p, k) else 0)
        = if p.1 + p.2 = k then w p.1 * w p.2 * w k else 0 := by
      intro k hk
      rw [Finset.mem_range] at hk
      simp only [he, ht]
      by_cases h : p.1 + p.2 = k
      · rw [if_pos (by omega), if_pos h]
      · rw [if_neg (by omega), if_neg h]
    rw [Finset.sum_congr rfl hc, Finset.sum_ite_eq]
    simp only [Finset.mem_range]
  have hhigh : ∑ x ∈ T.filter (fun x => e x = 2 * n - 1), t x
      = ∑ p ∈ range n ×ˢ range n,
          if n ≤ p.1 + p.2 then w p.1 * w p.2 * w (p.1 + p.2 - n) else 0 := by
    rw [Finset.sum_filter, hT, Finset.sum_product]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
    have hc : ∀ k ∈ range n, (if e (p, k) = 2 * n - 1 then t (p, k) else 0)
        = if p.1 + p.2 - n = k ∧ n ≤ p.1 + p.2 then w p.1 * w p.2 * w k else 0 := by
      intro k hk
      rw [Finset.mem_range] at hk
      simp only [he, ht]
      by_cases h : p.1 + p.2 - n = k ∧ n ≤ p.1 + p.2
      · rw [if_pos (by omega), if_pos h]
      · rw [if_neg (by omega), if_neg h]
    rw [Finset.sum_congr rfl hc]
    by_cases hn' : n ≤ p.1 + p.2
    · simp only [hn', and_true, if_true]
      rw [Finset.sum_ite_eq]
      rw [if_pos (by rw [Finset.mem_range]; omega)]
    · simp only [hn', and_false, if_false, Finset.sum_const_zero]
  rw [hP, OMA.ArxivTripleDigits.digit_extract B hB0 (n - 1) T t e hfib,
    OMA.ArxivTripleDigits.digit_extract B hB0 (2 * n - 1) T t e hfib, hlow, hhigh,
    ← Finset.sum_add_distrib, Finset.sum_product]
  refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hi hj
  by_cases h : i + j < n
  · rw [if_pos h, if_neg (by omega), add_zero, Nat.mod_eq_of_lt h]
  · rw [if_neg h, if_pos (by omega), zero_add]
    congr 1
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
