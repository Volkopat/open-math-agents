import FormalConjectures.Wikipedia.ButsonHadamardMatrix

/-!
# Butson's prime divisibility theorem

The original proof by @TheWaler (#209) groups the products of two orthogonal rows by
powers of a primitive root. Mathlib's `IsPrimitiveRoot.sum_eq_zero_iff_forall_eq`
then gives equality of the multiplicities directly. Their sum is the matrix order.
-/

open scoped Polynomial

theorem OMA.solution : type_of% @ButsonHadamardMatrix.butson_prime_divisibility := by
  intro p n hp hn hex
  rcases hex with ⟨M, _, hpow, horth⟩
  have hr01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp
  have hsum_zero : ∑ j : Fin n, M ⟨0, by omega⟩ j * star (M ⟨1, by omega⟩ j) = 0 := by
    have h01 := congr_fun (congr_fun horth ⟨0, by omega⟩) ⟨1, by omega⟩
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, hr01] using h01
  set a : Fin n → ℂ := fun j => M ⟨0, by omega⟩ j * star (M ⟨1, by omega⟩ j)
  have ha_pow : ∀ j : Fin n, a j ^ p = 1 := by
    intro j
    change (M ⟨0, by omega⟩ j * star (M ⟨1, by omega⟩ j)) ^ p = 1
    rw [mul_pow, ← star_pow, hpow ⟨0, by omega⟩ j, hpow ⟨1, by omega⟩ j, star_one, one_mul]
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / p)
  have hζ : IsPrimitiveRoot ζ p := Complex.isPrimitiveRoot_exp p hp.ne_zero
  have : NeZero p := ⟨hp.ne_zero⟩
  have hex_exp : ∀ j : Fin n, ∃ r < p, ζ ^ r = a j :=
    fun j => hζ.eq_pow_of_pow_eq_one (ha_pow j)
  choose f hf_lt hf_eq using hex_exp
  set c : ℕ → ℕ := fun r => (Finset.univ.filter (fun j : Fin n => f j = r)).card
  have hcard_sum : ∑ r ∈ Finset.range p, c r = n := by
    have h := Finset.sum_card_fiberwise_eq_card_filter (s := (Finset.univ : Finset (Fin n)))
      (t := Finset.range p) (g := f)
    have hfilter : (Finset.univ.filter (fun j : Fin n => f j ∈ Finset.range p)) = Finset.univ := by
      ext j
      simp [hf_lt j]
    rw [hfilter, Finset.card_univ, Fintype.card_fin] at h
    exact h
  have hζ_sum : ∑ r ∈ Finset.range p, (c r : ℂ) * ζ ^ r = 0 := by
    have hmaps : ∀ j ∈ (Finset.univ : Finset (Fin n)), f j ∈ Finset.range p :=
      fun j _ => Finset.mem_range.mpr (hf_lt j)
    have hfib := Finset.sum_fiberwise_of_maps_to (s := (Finset.univ : Finset (Fin n)))
      (t := Finset.range p) (g := f) (f := a) hmaps
    rw [hsum_zero] at hfib
    rw [← hfib]
    refine Finset.sum_congr rfl ?_
    intro r _
    have hterm : ∑ j ∈ Finset.univ.filter (fun j : Fin n => f j = r), a j =
        ∑ _j ∈ Finset.univ.filter (fun j : Fin n => f j = r), ζ ^ r := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      rw [← hf_eq j, (Finset.mem_filter.mp hj).2]
    rw [hterm, Finset.sum_const, nsmul_eq_mul]
  have hc : ∀ i j : Fin p, (c i : ℚ) = (c j : ℚ) :=
    (hζ.sum_eq_zero_iff_forall_eq hp (fun i => (c i : ℚ))).mp (by
      simpa [← Fin.sum_univ_eq_sum_range] using hζ_sum)
  have hc_const : ∀ r ∈ Finset.range p, c r = c 0 := by
    intro r hr
    exact_mod_cast hc ⟨r, Finset.mem_range.mp hr⟩ ⟨0, hp.pos⟩
  refine ⟨c 0, ?_⟩
  rw [← hcard_sum, Finset.sum_congr rfl hc_const, Finset.sum_const, Finset.card_range, smul_eq_mul]
