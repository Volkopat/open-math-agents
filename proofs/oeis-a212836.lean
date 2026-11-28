import OMAStatements.S_oeis_a212836

/-!
Fix the middle letter of the word. At either boundary of the alphabet
there are n choices for each endpoint. At each of the n-1 interior
letters there are n+1 choices for each endpoint.
-/

namespace AvoidAdjacentExtremes

open OMA.S_oeis_a212836

private lemma adj_comm (n x y : ℕ) : adj n x y ↔ adj n y x := by
  unfold adj
  tauto

private def allowed (n : ℕ) (b : Fin (n+1)) : Finset (Fin (n+1)) :=
  Finset.univ.filter fun x => ¬ adj n b x

private theorem middle_count (n : ℕ) (b : Fin (n+1)) :
    ((Finset.univ.filter (good n)).filter (fun f => f 1 = b)).card =
      (allowed n b).card ^ 2 := by
  classical
  rw [pow_two, ← Finset.card_product]
  apply Finset.card_bij (fun f _ => (f 0, f 2))
  · intro f hf
    obtain ⟨hf, hb⟩ := Finset.mem_filter.mp hf
    obtain ⟨h₀, h₂⟩ := (Finset.mem_filter.mp hf).2
    simpa [allowed, ← hb, adj_comm n (f 1) (f 0)] using And.intro h₀ h₂
  · intro f hf g hg e
    obtain ⟨_, hf⟩ := Finset.mem_filter.mp hf
    obtain ⟨_, hg⟩ := Finset.mem_filter.mp hg
    funext i
    fin_cases i
    · exact congrArg Prod.fst e
    · exact hf.trans hg.symm
    · exact congrArg Prod.snd e
  · rintro ⟨x,y⟩ hxy
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp hxy
    have hx' := (Finset.mem_filter.mp hx).2
    have hy' := (Finset.mem_filter.mp hy).2
    refine ⟨![x,b,y], ?_, rfl⟩
    simpa [good, adj_comm n (x : ℕ) b] using And.intro hx' hy'

private theorem choices (n : ℕ) (hn : 0 < n) (b : Fin (n+1)) :
    (allowed n b).card = if (b : ℕ) = 0 ∨ (b : ℕ) = n then n else n+1 := by
  classical
  by_cases hb : (b : ℕ) = 0
  · have he : allowed n b = Finset.univ.erase (Fin.last n) := by
      ext x
      simp only [allowed, Finset.mem_filter, Finset.mem_univ, true_and, adj,
        hb, Finset.mem_erase, and_true, ne_eq, Fin.ext_iff, Fin.val_last]
      omega
    simp [he, hb]
  by_cases ht : (b : ℕ) = n
  · have he : allowed n b = Finset.univ.erase 0 := by
      ext x
      simp only [allowed, Finset.mem_filter, Finset.mem_univ, true_and, adj,
        ht, Finset.mem_erase, and_true, ne_eq, Fin.ext_iff, Fin.val_zero]
      omega
    simp [he, ht]
  have he : allowed n b = Finset.univ := by
    ext x
    simp [allowed, adj, hb, ht]
  simp [he, hb, ht]

private theorem count (n : ℕ) (hn : 1 ≤ n) :
    (a n : ℤ) = (n : ℤ)^3 + 3*(n : ℤ)^2 - n - 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k+1 := ⟨n-1, by omega⟩
  have h : a (k+1) = ∑ b : Fin ((k+1)+1), (allowed (k+1) b).card ^ 2 := by
    simp_rw [← middle_count]
    simpa [a] using (Finset.sum_card_fiberwise_eq_card_filter
      (Finset.univ.filter (good (k+1))) Finset.univ (fun f => f 1)).symm
  simp_rw [choices (k+1) (by omega)] at h
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc] at h
  have middle (b : Fin k) : (b : ℕ) ≠ k := by omega
  simp [Fin.val_succ, middle] at h
  rw [h]
  push_cast
  ring


private theorem countQ (n : ℕ) (hn : 1 ≤ n) :
    (a n : ℚ) = (n : ℚ)^3 + 3*(n : ℚ)^2 - n - 1 := by
  exact_mod_cast count n hn

private theorem backward (n : ℕ) (hn : 4 < n) :
    (a n : ℤ) = 4 * a (n-1) - 6 * a (n-2) + 4 * a (n-3) - a (n-4) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k+5 := ⟨n-5, by omega⟩
  simp only [show k+5-1 = k+4 by omega, show k+5-2 = k+3 by omega,
    show k+5-3 = k+2 by omega, show k+5-4 = k+1 by omega]
  rw [count _ (by omega), count _ (by omega), count _ (by omega),
    count _ (by omega), count _ (by omega)]
  push_cast
  ring

open PowerSeries in
private theorem generating :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1-X)^4 =
      X*(2+9*X-6*X^2+X^3) := by
  let F := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ))
  change F * _ = _
  suffices H : F - (4:ℕ) • (F*X^1) + (6:ℕ) • (F*X^2)
      - (4:ℕ) • (F*X^3) + F*X^4 =
      (2:ℕ) • (X^1 : PowerSeries ℚ) + (9:ℕ) • X^2 - (6:ℕ) • X^3 + X^4 by
    simp only [nsmul_eq_mul, Nat.cast_ofNat] at H
    linear_combination H
  ext n
  simp only [map_add, map_sub, map_nsmul]
  simp only [nsmul_eq_mul, Nat.cast_ofNat, coeff_mul_X_pow', coeff_X_pow, F, coeff_mk]
  rcases n with _ | _ | _ | _ | _ | k
  · norm_num
  · norm_num [countQ]
  · norm_num [countQ]
  · norm_num [countQ]
  · norm_num [countQ]
  have recQ := congrArg (fun z : ℤ => (z : ℚ)) (backward (k+5) (by omega))
  push_cast at recQ
  simp [show 1 ≤ k+5 by omega, show 2 ≤ k+5 by omega, show 3 ≤ k+5 by omega,
    show 4 ≤ k+5 by omega, show k+5 ≠ 2 by omega,
    show k+5 ≠ 3 by omega, show k+5 ≠ 4 by omega]
  linarith

theorem result : type_of% @OMA.S_oeis_a212836.main := ⟨count, generating, backward⟩

end AvoidAdjacentExtremes

theorem OMA.solution : type_of% @OMA.S_oeis_a212836.main := AvoidAdjacentExtremes.result
