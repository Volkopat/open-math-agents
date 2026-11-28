import OMAStatements.S_oeis_a191450

-- Problem: A191450, closed form of the dispersion of 3n-1 (Jeffery's conjecture).
-- t(n) = A032766(n) = n + floor(n/2), and iterating x -> 3x - 1 gives 2 s^j(v) = (2v - 1) 3^j + 1.
-- Credit: @bnb9001

namespace OMA_A191450_Proof

open OMA.S_oeis_a191450

theorem f_strictMono : StrictMono (fun n : ℕ => n + n / 2) := by
  apply strictMono_nat_of_lt_succ; intro n; omega

theorem A032766_eq (n : ℕ) : A032766 n = n + n / 2 := by
  have hinf : (Set.ofPred (fun x : ℕ => x % 3 = 0 ∨ x % 3 = 1)).Infinite :=
    Set.infinite_of_injective_forall_mem f_strictMono.injective (fun k => by
      show (k + k / 2) % 3 = 0 ∨ (k + k / 2) % 3 = 1; omega)
  have hk : ∀ hf : (Set.ofPred (fun x : ℕ => x % 3 = 0 ∨ x % 3 = 1)).Finite,
      n < hf.toFinset.card := fun hf => absurd hf hinf
  refine (Nat.eq_nth_of_strictMonoOn_of_mapsTo_of_surjOn (fun n => n + n / 2) ?_ ?_ ?_ hk).symm
  · intro x hx
    refine ⟨2 * (x / 3) + x % 3, fun hf => absurd hf hinf, ?_⟩
    have : x % 3 = 0 ∨ x % 3 = 1 := hx
    simp only; omega
  · intro j _; show (j + j / 2) % 3 = 0 ∨ (j + j / 2) % 3 = 1; omega
  · exact f_strictMono.strictMonoOn _

theorem inT_iff (x : ℕ) : InT x ↔ 0 < x ∧ x % 3 ≠ 2 := by
  constructor
  · rintro ⟨h0, h⟩
    refine ⟨h0, fun h2 => h (x / 3 + 1) (by omega) (by omega)⟩
  · rintro ⟨h0, h2⟩
    exact ⟨h0, fun m hm heq => h2 (by omega)⟩

theorem g_strictMono : StrictMono (fun i : ℕ => (i + 1) + (i + 1) / 2) := by
  apply strictMono_nat_of_lt_succ; intro n; omega

theorem t_eq (n : ℕ) (hn : 1 ≤ n) : t n = n + n / 2 := by
  have hinf : (Set.ofPred InT).Infinite :=
    Set.infinite_of_injective_forall_mem g_strictMono.injective (fun k => by
      show InT ((k + 1) + (k + 1) / 2); rw [inT_iff]; omega)
  have hk : ∀ hf : (Set.ofPred InT).Finite, n - 1 < hf.toFinset.card := fun hf => absurd hf hinf
  unfold t
  have := (Nat.eq_nth_of_strictMonoOn_of_mapsTo_of_surjOn (fun i => (i + 1) + (i + 1) / 2)
    ?_ ?_ ?_ hk)
  · rw [← this]; simp only; rw [Nat.sub_add_cancel hn]
  · intro x hx
    have := (inT_iff x).mp hx
    refine ⟨2 * (x / 3) + x % 3 - 1, fun hf => absurd hf hinf, ?_⟩
    simp only; omega
  · intro j _; show InT ((j + 1) + (j + 1) / 2); rw [inT_iff]; omega
  · exact g_strictMono.strictMonoOn _

theorem iter_s (v : ℕ) (hv : 1 ≤ v) : ∀ j, 2 * ((s^[j] v : ℕ) : ℤ) = (2 * v - 1) * 3 ^ j + 1 ∧ 1 ≤ s^[j] v := by
  intro j
  induction j with
  | zero => simp; omega
  | succ j ih =>
    obtain ⟨h1, h2⟩ := ih
    rw [Function.iterate_succ_apply']
    have hs : s (s^[j] v) = 3 * s^[j] v - 1 := rfl
    rw [hs]
    refine ⟨?_, by omega⟩
    rw [Nat.cast_sub (by omega)]
    push_cast
    rw [pow_succ]
    linear_combination 3 * h1

end OMA_A191450_Proof

open OMA.S_oeis_a191450 OMA_A191450_Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a191450.main := by
  intro n k hn hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  unfold D
  rw [Nat.add_sub_cancel, t_eq n hn, A032766_eq]
  have hv : 1 ≤ n + n / 2 := by omega
  obtain ⟨h1, -⟩ := iter_s (n + n / 2) hv j
  have : (3 + (2 * ((n + n / 2 : ℕ) : ℤ) - 1) * 3 ^ (j + 1)) = 6 * ((s^[j] (n + n / 2) : ℕ) : ℤ) := by
    rw [pow_succ]; linear_combination (-3) * h1
  rw [this, Int.mul_ediv_cancel_left _ (by norm_num)]
