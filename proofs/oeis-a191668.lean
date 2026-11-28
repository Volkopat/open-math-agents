import OMAStatements.S_oeis_a191668

-- Problem: A191668, closed form of the dispersion of 4k+2.
-- t(n) = floor((4n+1)/3), and iterating x -> 4x - 2 gives 3 s^j(v) = (3v - 2) 4^j + 2.
-- Credit: @bnb9001

namespace OMA_A191668_Proof

open OMA.S_oeis_a191668

theorem inT_iff (x : ℕ) : InT x ↔ 0 < x ∧ x % 4 ≠ 2 := by
  constructor
  · rintro ⟨h0, h⟩
    refine ⟨h0, fun h2 => h (x / 4 + 1) (by omega) (by omega)⟩
  · rintro ⟨h0, h2⟩
    exact ⟨h0, fun m hm heq => h2 (by omega)⟩

theorem g_strictMono : StrictMono (fun i : ℕ => (4 * (i + 1) + 1) / 3) := by
  apply strictMono_nat_of_lt_succ; intro n; omega

theorem t_eq (n : ℕ) (hn : 1 ≤ n) : t n = (4 * n + 1) / 3 := by
  have hinf : (Set.ofPred InT).Infinite :=
    Set.infinite_of_injective_forall_mem g_strictMono.injective (fun k => by
      show InT ((4 * (k + 1) + 1) / 3); rw [inT_iff]; omega)
  have hk : ∀ hf : (Set.ofPred InT).Finite, n - 1 < hf.toFinset.card := fun hf => absurd hf hinf
  unfold t
  have := (Nat.eq_nth_of_strictMonoOn_of_mapsTo_of_surjOn (fun i => (4 * (i + 1) + 1) / 3)
    ?_ ?_ ?_ hk)
  · rw [← this]; simp only; rw [Nat.sub_add_cancel hn]
  · intro x hx
    obtain ⟨hx0, hx2⟩ := (inT_iff x).mp hx
    have hq := Nat.div_add_mod x 4
    set q := x / 4
    have hr : x % 4 = 0 ∨ x % 4 = 1 ∨ x % 4 = 3 := by omega
    rcases hr with hr | hr | hr
    · refine ⟨3 * q - 1, fun hf => absurd hf hinf, ?_⟩
      show (4 * (3 * q - 1 + 1) + 1) / 3 = x
      have : 1 ≤ q := by omega
      rw [Nat.sub_add_cancel (by omega)]; omega
    · refine ⟨3 * q, fun hf => absurd hf hinf, ?_⟩
      show (4 * (3 * q + 1) + 1) / 3 = x
      omega
    · refine ⟨3 * q + 1, fun hf => absurd hf hinf, ?_⟩
      show (4 * (3 * q + 1 + 1) + 1) / 3 = x
      omega
  · intro j _; show InT ((4 * (j + 1) + 1) / 3); rw [inT_iff]; omega
  · exact g_strictMono.strictMonoOn _

theorem iter_s (v : ℕ) (hv : 1 ≤ v) :
    ∀ j, 3 * ((s^[j] v : ℕ) : ℤ) = (3 * v - 2) * 4 ^ j + 2 ∧ 1 ≤ s^[j] v := by
  intro j
  induction j with
  | zero => simp; omega
  | succ j ih =>
    obtain ⟨h1, h2⟩ := ih
    rw [Function.iterate_succ_apply']
    have hs : s (s^[j] v) = 4 * s^[j] v - 2 := rfl
    rw [hs]
    refine ⟨?_, by omega⟩
    rw [Nat.cast_sub (by omega)]
    push_cast
    rw [pow_succ]
    linear_combination 4 * h1

end OMA_A191668_Proof

open OMA.S_oeis_a191668 OMA_A191668_Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a191668.main := by
  intro n k hn hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  unfold D
  rw [Nat.add_sub_cancel, t_eq n hn]
  have hv : 1 ≤ (4 * n + 1) / 3 := by omega
  obtain ⟨h1, -⟩ := iter_s ((4 * n + 1) / 3) hv j
  have : (8 + (3 * (((4 * n + 1) / 3 : ℕ) : ℤ) - 2) * 4 ^ (j + 1)) =
      12 * ((s^[j] ((4 * n + 1) / 3) : ℕ) : ℤ) := by
    rw [pow_succ]; linear_combination (-4) * h1
  rw [this, Int.mul_ediv_cancel_left _ (by norm_num)]
