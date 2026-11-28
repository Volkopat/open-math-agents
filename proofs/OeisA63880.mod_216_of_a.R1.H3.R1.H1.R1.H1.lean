import OMAReductions.R_OeisA63880_mod_216_of_a_R1_H3_R1_H1_R1

-- Step OeisA63880.mod_216_of_a.R1.H3.R1.H1.R1.H1
-- Parity: an odd square has an odd number of divisors, all odd, so its divisor sum is odd;
-- hence 7 * sigma is odd while 10 * usigma is even.

namespace OMA.OddSquareSigmaH1

theorem odd_sigma_of_odd_square {t : ℕ} (ho : Odd t) (hs : IsSquare t) :
    Odd (ArithmeticFunction.sigma 1 t) := by
  obtain ⟨r, rfl⟩ := hs
  have hr : r ≠ 0 := by
    rintro rfl
    simp at ho
  have ht : r * r ≠ 0 := mul_ne_zero hr hr
  rw [ArithmeticFunction.sigma_one_apply, Finset.odd_sum_iff_odd_card_odd]
  have hfil : (r * r).divisors.filter (fun x => Odd x) = (r * r).divisors := by
    apply Finset.filter_true_of_mem
    intro d hd
    exact Odd.of_dvd_nat ho (Nat.dvd_of_mem_divisors hd)
  rw [hfil, Nat.card_divisors ht]
  apply Finset.prod_induction _ (fun n => Odd n) (fun a b ha hb => ha.mul hb) odd_one
  intro p _
  rw [Nat.factorization_mul hr hr]
  exact ⟨r.factorization p, by simp; ring⟩

end OMA.OddSquareSigmaH1

theorem OMA.solution : OMA.R_OeisA63880_mod_216_of_a_R1_H3_R1_H1_R1.H1 := by
  intro t ho _ _ _ hs heq
  obtain ⟨k, hk⟩ := OMA.OddSquareSigmaH1.odd_sigma_of_odd_square ho hs
  omega
