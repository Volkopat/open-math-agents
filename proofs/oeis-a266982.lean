import OMAStatements.S_oeis_a266982

open Finset OMA.S_oeis_a266982

private def rb (b : Bool) (j : ℤ) : Bool := if j = 0 ∨ j = 1 then !b else b

private lemma pat (t : ℕ) (ht : 0 < t) (i : ℤ) : cell t i = rb (decide (t % 2 = 1)) (i + t) := by
  have hr (l c r : Bool) : rule81 l c r = (!r && (l || !c)) := by cases l <;> cases c <;> cases r <;> decide
  induction t generalizing i with
  | zero => omega
  | succ t ih =>
    by_cases h0 : t = 0
    · subst h0; simp only [cell, hr, rb]; by_cases h1 : i = -1 <;> by_cases h2 : i = 0 <;> by_cases h3 : i = 1 <;> simp_all
    · have hf : decide ((t + 1) % 2 = 1) = !decide (t % 2 = 1) := by
        by_cases h : t % 2 = 1
        · simp [h, show (t + 1) % 2 = 0 by omega]
        · simp [h, show (t + 1) % 2 = 1 by omega]
      rw [cell, ih (by omega), ih (by omega), ih (by omega), hf, Nat.cast_succ,
        show i - 1 + (t : ℤ) = i + t - 1 by ring, show i + 1 + (t : ℤ) = i + t + 1 by ring, ← add_assoc]
      cases decide (t % 2 = 1) <;> simp only [hr, rb] <;> split_ifs <;> first | rfl | omega

theorem OMA.solution : type_of% @OMA.S_oeis_a266982.main := by
  refine ⟨by decide, fun n hn => ?_⟩
  have h1 : a n = (n - 2).sqrt % 2 := by
    obtain ⟨t, ht⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.sqrt_pos.2 hn).ne'
    let j := n - (t + 1) ^ 2
    have hlo : (t + 1) ^ 2 ≤ n := by simpa only [ht, Nat.succ_eq_add_one] using Nat.sqrt_le' n
    have hhi : n < (t + 1 + 1) ^ 2 := by simpa only [ht, Nat.succ_eq_add_one] using Nat.lt_succ_sqrt' n
    have ha : a n = (rb (decide ((t + 1) % 2 = 1)) j).toNat := by simp only [a, ht, pat (t + 1) (by omega), sub_add_cancel, j]
    rw [ha]
    by_cases hj : j < 2
    · have hs : (n - 2).sqrt = t := by
        symm; apply Nat.eq_sqrt'.2; constructor
        · by_cases hz : t = 0
          · simp [hz]
          · have : t ^ 2 + 2 ≤ n := by nlinarith [show 1 ≤ t by omega]
            omega
        · have : 0 < (t + 1) ^ 2 := by positivity
          dsimp [j] at hj; omega
      rw [hs, rb, if_pos (by omega : (j : ℤ) = 0 ∨ (j : ℤ) = 1)]
      by_cases ho : (t + 1) % 2 = 1 <;> simp [ho] <;> omega
    · have hs : (n - 2).sqrt = t + 1 := Eq.symm (Nat.eq_sqrt'.2 (by omega))
      rw [hs, rb, if_neg (by omega : ¬((j : ℤ) = 0 ∨ (j : ℤ) = 1))]
      by_cases ho : (t + 1) % 2 = 1 <;> simp [ho] <;> omega
  rw [h1]; symm
  let m := n - 2
  let P := (Ioc 0 m ×ˢ Ioc 0 m).filter fun x => x.1 * x.2 ≤ m
  let U := P.filter fun x => x.1 < x.2
  let L := P.filter fun x => x.2 < x.1
  let D := P.filter fun x => x.1 = x.2
  have hc : P.card = ∑ i ∈ Ioc 0 m, m / i := by
    simp only [P, card_eq_sum_ones, sum_filter, sum_product]
    refine sum_congr rfl fun i hi => ?_
    have hi' := (mem_Ioc.1 hi).1
    have hr : (Ioc 0 m).filter (fun j => i * j ≤ m) = Ioc 0 (m / i) := by
      ext j; simp only [mem_filter, mem_Ioc]
      have hd : j ≤ m / i ↔ i * j ≤ m := by simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hi' : j ≤ m / i ↔ j * i ≤ m)
      exact ⟨fun ⟨⟨a, _⟩, b⟩ => ⟨a, hd.2 b⟩, fun ⟨a, b⟩ => ⟨⟨a, b.trans (Nat.div_le_self _ _)⟩, hd.1 b⟩⟩
    change (∑ j ∈ Ioc 0 m, if i * j ≤ m then 1 else 0) = m / i
    rw [← sum_filter, hr]; simp
  have hsp : U.card + L.card + D.card = P.card := by
    simp only [U, L, D, card_eq_sum_ones, sum_filter, ← sum_add_distrib]
    exact sum_congr rfl fun _ _ => by split_ifs <;> omega
  have hsw : U.card = L.card := card_equiv (Equiv.prodComm ℕ ℕ) fun ⟨_, _⟩ => by
    simp [U, L, P, Nat.mul_comm, and_comm, and_assoc, and_left_comm]
  have hdg : D.card = m.sqrt := by
    rw [show m.sqrt = (Ioc 0 m.sqrt).card by simp]
    refine card_bij' (fun x _ => x.1) (fun i _ => (i, i)) ?_ ?_ ?_ ?_
    · rintro ⟨i, j⟩ h; simp only [D, P, mem_filter, mem_product, mem_Ioc] at h ⊢; obtain ⟨⟨⟨⟨a, _⟩, _⟩, b⟩, rfl⟩ := h; exact ⟨a, Nat.le_sqrt.2 b⟩
    · intro i h; obtain ⟨a, b⟩ := mem_Ioc.1 h; simp [D, P, a, b.trans (Nat.sqrt_le_self m), Nat.le_sqrt.1 b]
    · rintro ⟨i, j⟩ h; exact Prod.ext rfl (mem_filter.1 h).2
    · intro _ _; rfl
  change (∑ i ∈ Ioc 0 m, m / i) % 2 = m.sqrt % 2
  omega
