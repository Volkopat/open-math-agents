import FormalConjectures.OEIS.«108864»
import Mathlib.Tactic.NormNum.Prime

/-! Shorter disproof of `OeisA108864.conjecture` via 815634435. -/

open OeisA108864

private lemma gsub (n r : ℕ) (ds : List ℕ) (h : (ds.filter fun d => decide (d ∣ n)).sum ≤ r) :
    ds.foldl (fun m d => if d ∣ n ∧ d ≤ m then m - d else m) r =
      r - (ds.filter fun d => decide (d ∣ n)).sum := by
  induction ds generalizing r with
  | nil => simp
  | cons d ds ih =>
    by_cases hd : d ∣ n <;> simp [hd] at h ⊢
    · rw [if_pos (by omega), ih _ (by omega)]; omega
    · exact ih _ h

private lemma sig_p (p m : ℕ) (hp : p.Prime) (hc : p.Coprime m) :
    ArithmeticFunction.sigma 1 (p * m) = (p + 1) * ArithmeticFunction.sigma 1 m := by
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hc,
    ArithmeticFunction.sigma_one_apply, hp.divisors]
  simp [hp.ne_one.symm, add_comm]

private lemma pdef (n : ℕ) (h1 : 0 < ∑ d ∈ n.properDivisors, d)
    (h2 : ∑ d ∈ n.properDivisors, d ≤ n) :
    perfectDeficiency n = n - ∑ d ∈ n.properDivisors, d := by
  let ds := (List.range n).filter fun d => decide (d ∣ n)
  have hs : ds.sum = ∑ d ∈ n.properDivisors, d := by
    have : ds.toFinset = n.properDivisors := by ext; simp [ds, Nat.mem_properDivisors, and_comm]
    rw [← this]; simpa [ds] using (List.sum_toFinset (id : ℕ → ℕ) (List.nodup_range.filter _ : ds.Nodup)).symm
  rw [perfectDeficiency, List.range_succ, List.foldl_append, gsub n n (List.range n) (hs ▸ h2), hs]
  simp [show ¬ n ≤ n - ∑ d ∈ n.properDivisors, d by omega]

set_option maxRecDepth 15000 in
set_option maxHeartbeats 1500000 in
theorem OMA.disproof : ¬ (type_of% @OeisA108864.conjecture) := by
  intro hall
  let n := 815634435
  have hs : ∑ d ∈ n.properDivisors, d = 815634429 := by
    have hσ : ArithmeticFunction.sigma 1 n = 1631268864 := by
      rw [show n = 3 * (5 * (7 * (11 * (547 * (1291 * 1))))) by rfl]
      repeat rw [sig_p _ _ (by norm_num) (by decide)]
      norm_num
    rw [ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self] at hσ
    omega
  have hn : A n := ⟨by decide, by rw [pdef _ (by omega) (by omega), hs]; decide⟩
  let S : Finset ℕ :=
    {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 18, 20, 21, 22, 24,
      26, 28, 30, 32, 40, 42, 44, 50, 52, 60, 64, 68, 72, 110, 120, 126, 128, 130,
      136, 144, 150, 152, 180, 184, 204, 228, 256, 315, 462, 496, 512, 528, 592,
      656, 750, 884, 1012, 1024, 1155}
  have hS : ∀ d ∈ S, d < n ∧ A d := by decide +kernel
  have hc : 58 < Nat.count A n := by
    rw [Nat.count_eq_card_filter_range]
    exact lt_of_lt_of_le (by decide : 58 < S.card) <| Finset.card_le_card fun d hd =>
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hS d hd).1, (hS d hd).2⟩
  have he := hall (Nat.count A n) hc
  rw [a, Nat.nth_count hn] at he
  exact (by decide : ¬Even n) he
