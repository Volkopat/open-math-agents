import OMAStatements.S_oeis_a256852

-- Problem: A256852, a(n) <= 2 (uniqueness of two-square representations of a prime).
-- Credit: @bnb9001

namespace OMA_A256852_Proof

open OMA.S_oeis_a256852

lemma ne_zero_of_sq_add {p x y : ℕ} (hp : p.Prime) (h : x ^ 2 + y ^ 2 = p) : x ≠ 0 := by
  rintro rfl
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add] at h
  subst h
  rw [sq] at hp
  rcases Nat.prime_mul_iff.1 hp with ⟨-, h1⟩ | ⟨-, h1⟩ <;> subst h1 <;> exact Nat.not_prime_one (by simpa using hp)

lemma two_sq_unique {p x y u v : ℕ} (hp : p.Prime) (h1 : x ^ 2 + y ^ 2 = p) (h2 : u ^ 2 + v ^ 2 = p) :
    (x = u ∧ y = v) ∨ (x = v ∧ y = u) := by
  have hx := ne_zero_of_sq_add hp h1
  have hy := ne_zero_of_sq_add hp (by rw [add_comm] at h1; exact h1)
  have hu := ne_zero_of_sq_add hp h2
  have hv := ne_zero_of_sq_add hp (by rw [add_comm] at h2; exact h2)
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have H1 : (x : ℤ) ^ 2 + y ^ 2 = p := by exact_mod_cast h1
  have H2 : (u : ℤ) ^ 2 + v ^ 2 = p := by exact_mod_cast h2
  have X1 : (1 : ℤ) ≤ x := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hx
  have Y1 : (1 : ℤ) ≤ y := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hy
  have U1 : (1 : ℤ) ≤ u := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hu
  have V1 : (1 : ℤ) ≤ v := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hv
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have hdiv : (p : ℤ) ∣ ((x : ℤ) * v - u * y) * ((x : ℤ) * v + u * y) :=
    ⟨(x : ℤ) ^ 2 - u ^ 2, by linear_combination (x : ℤ) ^ 2 * H2 - (u : ℤ) ^ 2 * H1⟩
  have hpp : (p : ℤ) ^ 2 = ((x : ℤ) ^ 2 + y ^ 2) * ((u : ℤ) ^ 2 + v ^ 2) := by rw [H1, H2]; ring
  have id1 : ((x : ℤ) * v - u * y) ^ 2 + ((x : ℤ) * u + y * v) ^ 2 = (p : ℤ) ^ 2 := by
    rw [hpp]; ring
  have id2 : ((x : ℤ) * v + u * y) ^ 2 + ((x : ℤ) * u - y * v) ^ 2 = (p : ℤ) ^ 2 := by
    rw [hpp]; ring
  rcases hpz.dvd_or_dvd hdiv with ⟨k, hk⟩ | ⟨k, hk⟩
  · rcases eq_or_ne k 0 with rfl | hk0
    · rw [mul_zero] at hk
      have hs : ((x : ℤ) * u + y * v) ^ 2 = (p : ℤ) ^ 2 := by rw [hk] at id1; linarith
      have hpos : 0 ≤ (x : ℤ) * u + y * v := by positivity
      have hs' : (x : ℤ) * u + y * v = p := (pow_left_inj₀ hpos hp0.le two_ne_zero).1 hs
      have hz : ((x : ℤ) - u) ^ 2 + ((y : ℤ) - v) ^ 2 = 0 := by
        linear_combination H1 + H2 - 2 * hs'
      have e1 : ((x : ℤ) - u) ^ 2 = 0 := by linarith [sq_nonneg ((x : ℤ) - u), sq_nonneg ((y : ℤ) - v)]
      have e2 : ((y : ℤ) - v) ^ 2 = 0 := by linarith [sq_nonneg ((x : ℤ) - u), sq_nonneg ((y : ℤ) - v)]
      left
      constructor
      · have : (x : ℤ) = u := by have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 e1; linarith
        exact_mod_cast this
      · have : (y : ℤ) = v := by have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 e2; linarith
        exact_mod_cast this
    · exfalso
      have hk1 : 1 ≤ k ^ 2 := by
        have : 0 < k ^ 2 := by positivity
        omega
      have hge : ((x : ℤ) * v - u * y) ^ 2 ≥ (p : ℤ) ^ 2 := by
        rw [hk, mul_pow]
        exact le_mul_of_one_le_right (sq_nonneg _) hk1
      have hxu : 0 < ((x : ℤ) * u + y * v) ^ 2 := by positivity
      linarith
  · have hpos : 0 < (x : ℤ) * v + u * y := by positivity
    have hk1 : 1 ≤ k := by
      by_contra hcon
      rw [not_le] at hcon
      have : (p : ℤ) * k ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hp0.le (by omega)
      linarith
    have hge : (x : ℤ) * v + u * y ≥ p := by rw [hk]; exact le_mul_of_one_le_right hp0.le hk1
    have hge2 : ((x : ℤ) * v + u * y) ^ 2 ≥ (p : ℤ) ^ 2 := pow_le_pow_left₀ hp0.le hge 2
    have hz2 : ((x : ℤ) * u - y * v) ^ 2 = 0 := by linarith [sq_nonneg ((x : ℤ) * u - y * v)]
    have hs : ((x : ℤ) * v + u * y) ^ 2 = (p : ℤ) ^ 2 := by linarith
    have heq : (x : ℤ) * v + u * y = p := (pow_left_inj₀ hpos.le hp0.le two_ne_zero).1 hs
    have hz : ((x : ℤ) - v) ^ 2 + ((y : ℤ) - u) ^ 2 = 0 := by
      linear_combination H1 + H2 - 2 * heq
    have e1 : ((x : ℤ) - v) ^ 2 = 0 := by linarith [sq_nonneg ((x : ℤ) - v), sq_nonneg ((y : ℤ) - u)]
    have e2 : ((y : ℤ) - u) ^ 2 = 0 := by linarith [sq_nonneg ((x : ℤ) - v), sq_nonneg ((y : ℤ) - u)]
    right
    constructor
    · have : (x : ℤ) = v := by have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 e1; linarith
      exact_mod_cast this
    · have : (y : ℤ) = u := by have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 e2; linarith
      exact_mod_cast this

lemma count_le_two {p : ℕ} (hp : p.Prime) : count p ≤ 2 := by
  unfold count
  set S := (Finset.Icc 1 p ×ˢ Finset.Icc 1 p).filter (fun ab => ab.1 ^ 2 + ab.2 ^ 4 = p) with hS
  rcases S.eq_empty_or_nonempty with h | ⟨⟨a0, b0⟩, h0⟩
  · rw [h]; simp
  · have h0' : a0 ^ 2 + (b0 ^ 2) ^ 2 = p := by
      rw [hS, Finset.mem_filter] at h0; rw [← pow_mul]; exact h0.2
    have hsub : S ⊆ {(a0, b0), (b0 ^ 2, Nat.sqrt a0)} := by
      rintro ⟨a, b⟩ hab
      rw [hS, Finset.mem_filter] at hab
      have hab' : a ^ 2 + (b ^ 2) ^ 2 = p := by rw [← pow_mul]; exact hab.2
      simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
      rcases two_sq_unique hp hab' h0' with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · left
        exact ⟨ha, Nat.pow_left_injective (by norm_num) hb⟩
      · right
        refine ⟨ha, ?_⟩
        rw [← hb, Nat.sqrt_eq']
    calc S.card ≤ ({(a0, b0), (b0 ^ 2, Nat.sqrt a0)} : Finset (ℕ × ℕ)).card := Finset.card_le_card hsub
      _ ≤ 2 := Finset.card_le_two

end OMA_A256852_Proof

open OMA_A256852_Proof OMA.S_oeis_a256852 in
theorem OMA.solution : type_of% @OMA.S_oeis_a256852.main :=
  fun n _ => count_le_two (Nat.prime_nth_prime _)
