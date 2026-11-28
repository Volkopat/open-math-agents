import OMAStatements.S_oeis_a204558

/-! Proof. Row `m` is an arithmetic progression (for `m = 2t+1`: `(2t+1)(2t²+1) + 2(2t+1)i`; for
`m = 2t+2`: `(2t+2)(t+1)(2t+1) + (2t+2)i`), because the previous row ends just below its first
term; `Nat.nth` of such a set is computed from `Set.range` and strict monotonicity. By induction this
gives the last entries, hence `a(2t+1) = (2t+1)²(2t²+2t+1)` and `a(2t+2) = 2(t+1)²(2t+1)(2t+3)`,
which is the closed form. The generating function follows coefficientwise from these values. -/

namespace OMA.S_oeis_a204558

lemma nth_ap {p : ℕ → Prop} (x0 D : ℕ) (hD : 0 < D) (h : ∀ x, p x ↔ ∃ i, x = x0 + D * i) (i : ℕ) :
    Nat.nth p i = x0 + D * i := by
  have hf : StrictMono (fun i => x0 + D * i) := by
    intro u v huv; simp only; nlinarith
  have hr : Set.range (fun i => x0 + D * i) = Set.ofPred p := by
    ext x; simp only [Set.mem_range, Set.mem_ofPred, h x]; constructor
    · rintro ⟨i, rfl⟩; exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩; exact ⟨i, rfl⟩
  have hinf : (Set.ofPred p).Infinite := by
    rw [← hr]; exact Set.infinite_range_of_injective hf.injective
  have := (StrictMono.range_inj (Nat.nth_strictMono hinf) hf).mp (by rw [Nat.range_nth_of_infinite hinf, hr])
  exact congrFun this i

def Fe : ℕ → ℕ
  | 0 => 0
  | u + 1 => (2*u+2)*(2*u+1)*(u+2)

def Fo (t : ℕ) : ℕ := (2*t+1)*(2*t^2+4*t+1)

lemma Fe_le (t : ℕ) : (2*t+1)*(2*t^2+1) ≤ Fe t + 2*(2*t+1) ∧ Fe t < (2*t+1)*(2*t^2+1) := by
  rcases t with _ | u
  · simp [Fe]
  · simp only [Fe]; constructor <;> nlinarith

lemma rowO (t : ℕ) (i : ℕ) : Nat.nth (P (2*t+1) (Fe t)) i = (2*t+1)*(2*t^2+1) + (2*(2*t+1)) * i := by
  apply nth_ap _ _ (by omega)
  intro x
  obtain ⟨h1, h2⟩ := Fe_le t
  constructor
  · rintro ⟨hL, ⟨j, rfl⟩, hp⟩
    have hj : j % 2 = 1 := by
      rw [Nat.mul_mod] at hp
      have : (2*t+1) % 2 = 1 := by omega
      rw [this, one_mul, Nat.mod_mod] at hp; omega
    have hs : (2*t^2+1) ≤ j := by
      by_contra hc
      have : j + 2 ≤ 2*t^2+1 := by
        have : (2*t^2+1) % 2 = 1 := by omega
        omega
      nlinarith
    obtain ⟨i, hi⟩ : ∃ i, j = 2*t^2+1 + 2*i := ⟨(j - (2*t^2+1))/2, by omega⟩
    exact ⟨i, by subst hi; ring⟩
  · rintro ⟨i, rfl⟩
    refine ⟨by nlinarith, ⟨2*t^2+1+2*i, by ring⟩, ?_⟩
    have : (2*t+1)*(2*t^2+1) + 2*(2*t+1)*i = 2*(2*t^3+t^2+t+(2*t+1)*i) + 1 := by ring
    rw [this]; omega

lemma rowE (t : ℕ) (i : ℕ) : Nat.nth (P (2*t+2) (Fo t)) i = (2*t+2)*((t+1)*(2*t+1)) + (2*t+2) * i := by
  apply nth_ap _ _ (by omega)
  intro x
  have h1 : (2*t+2)*((t+1)*(2*t+1)) ≤ Fo t + (2*t+2) := by simp only [Fo]; nlinarith
  have h2 : Fo t < (2*t+2)*((t+1)*(2*t+1)) := by simp only [Fo]; nlinarith
  constructor
  · rintro ⟨hL, ⟨j, rfl⟩, hp⟩
    have hs : (t+1)*(2*t+1) ≤ j := by
      by_contra hc
      have : j + 1 ≤ (t+1)*(2*t+1) := by omega
      nlinarith
    obtain ⟨i, hi⟩ : ∃ i, j = (t+1)*(2*t+1) + i := ⟨j - (t+1)*(2*t+1), by omega⟩
    exact ⟨i, by subst hi; ring⟩
  · rintro ⟨i, rfl⟩
    refine ⟨by nlinarith, ⟨(t+1)*(2*t+1)+i, by ring⟩, ?_⟩
    have : (2*t+2)*((t+1)*(2*t+1)) + (2*t+2)*i = 2*((t+1)*((t+1)*(2*t+1)) + (t+1)*i) := by ring
    rw [this]; omega

lemma last_eq : ∀ t, last (2*t) = Fe t ∧ last (2*t+1) = Fo t
  | 0 => by
    refine ⟨rfl, ?_⟩
    show Nat.nth (P (2*0+1) (last (2*0))) (2*0) = Fo 0
    rw [show last (2*0) = Fe 0 from rfl, rowO]; simp [Fo]
  | t + 1 => by
    obtain ⟨_, ho⟩ := last_eq t
    have he : last (2*(t+1)) = Fe (t+1) := by
      show Nat.nth (P (2*t+1+1) (last (2*t+1))) (2*t+1) = Fe (t+1)
      rw [ho, show 2*t+1+1 = 2*t+2 by ring, rowE]; simp only [Fe]; ring
    refine ⟨he, ?_⟩
    show Nat.nth (P (2*(t+1)+1) (last (2*(t+1)))) (2*(t+1)) = Fo (t+1)
    rw [he, rowO]; simp only [Fo]; ring

lemma sumAP (n x0 D : ℕ) : ∑ k ∈ Finset.Icc 1 n, (x0 + D * (k - 1)) = n * x0 + D * (n * (n - 1) / 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    rcases n with _ | n
    · simp
    · have : (n+1+1) * (n+1+1-1) / 2 = (n+1) * (n+1-1) / 2 + (n+1) := by
        rw [show n+1+1-1 = n+1 by omega, show n+1-1 = n by omega]
        have : (n+2)*(n+1) = (n+1)*n + 2*(n+1) := by ring
        rw [this, Nat.add_mul_div_left _ _ (by norm_num)]
      rw [this, show n+1+1-1 = n+1 by omega]; ring

lemma aO (t : ℕ) : a (2*t+1) = (2*t+1)^2 * (2*t^2+2*t+1) := by
  have hT : ∀ k, T (2*t+1) k = (2*t+1)*(2*t^2+1) + (2*(2*t+1)) * (k-1) := by
    intro k; simp only [T, show 2*t+1-1 = 2*t by omega, (last_eq t).1, rowO]
  simp only [a, hT, sumAP]
  have : (2*t+1)*(2*t+1-1)/2 = (2*t+1)*t := by
    rw [show 2*t+1-1 = 2*t by omega, show (2*t+1)*(2*t) = 2*((2*t+1)*t) by ring, Nat.mul_div_cancel_left _ (by norm_num)]
  rw [this]; ring

lemma aE (t : ℕ) : a (2*t+2) = 2*(t+1)^2*(2*t+1)*(2*t+3) := by
  have hT : ∀ k, T (2*t+2) k = (2*t+2)*((t+1)*(2*t+1)) + (2*t+2) * (k-1) := by
    intro k; simp only [T, show 2*t+2-1 = 2*t+1 by omega, (last_eq t).2, rowE]
  simp only [a, hT, sumAP]
  have : (2*t+2)*(2*t+2-1)/2 = (t+1)*(2*t+1) := by
    rw [show 2*t+2-1 = 2*t+1 by omega, show (2*t+2)*(2*t+1) = 2*((t+1)*(2*t+1)) by ring, Nat.mul_div_cancel_left _ (by norm_num)]
  rw [this]; ring

lemma a_zero : a 0 = 0 := by simp [a]

lemma closed (n : ℕ) (hn : 1 ≤ n) : (a n : ℚ) = ((n : ℚ) ^ 2 * (-(-1 : ℚ) ^ n + (n : ℚ) ^ 2)) / 2 := by
  obtain ⟨t, rfl | rfl⟩ : ∃ t, n = 2*t+1 ∨ n = 2*t+2 := ⟨(n-1)/2, by omega⟩
  · have e : (-1:ℚ)^(2*t+1) = -1 := by rw [pow_succ, pow_mul]; norm_num
    rw [aO, e]; push_cast; ring
  · have e : (-1:ℚ)^(2*t+2) = 1 := by rw [show 2*t+2 = 2*(t+1) by ring, pow_mul]; norm_num
    rw [aE, e]; push_cast; ring

/-- integer values, by parity -/
lemma aZ (u : ℕ) : (a (2*u) : ℤ) = 2*(u:ℤ)^2*(2*u-1)*(2*u+1) ∧ (a (2*u+1) : ℤ) = (2*(u:ℤ)+1)^2*(2*u^2+2*u+1) := by
  refine ⟨?_, by rw [aO]; push_cast; ring⟩
  rcases u with _ | t
  · simp [a_zero]
  · rw [show 2*(t+1) = 2*t+2 by ring, aE]; push_cast; ring

open PowerSeries in
lemma gf : PowerSeries.mk (fun n => (a n : ℤ)) * ((X - 1) ^ 5 * (X + 1) ^ 3) =
      -X * (X ^ 6 + 4 * X ^ 5 + 31 * X ^ 4 + 24 * X ^ 3 + 31 * X ^ 2 + 4 * X + 1) := by
  set A := PowerSeries.mk (fun n => (a n : ℤ)) with hA
  have hQ : A * ((X - 1) ^ 5 * (X + 1) ^ 3) = A * X^8 - 2 * (A * X^7) - 2 * (A * X^6) + 6 * (A * X^5)
      - 6 * (A * X^3) + 2 * (A * X^2) + 2 * (A * X^1) - A := by ring
  rw [hQ, show (-X * (X ^ 6 + 4 * X ^ 5 + 31 * X ^ 4 + 24 * X ^ 3 + 31 * X ^ 2 + 4 * X + 1) : ℤ⟦X⟧)
        = -(X^7 + C 4 * X^6 + C 31 * X^5 + C 24 * X^4 + C 31 * X^3 + C 4 * X^2 + X) by simp only [map_ofNat]; ring]
  have v0 : (a 0 : ℤ) = 0 := by rw [a_zero]; rfl
  have v1 : (a 1 : ℤ) = 1 := by have := (aZ 0).2; norm_num at this; exact_mod_cast this
  have v2 : (a 2 : ℤ) = 6 := by have := (aZ 1).1; norm_num at this; exact_mod_cast this
  have v3 : (a 3 : ℤ) = 45 := by have := (aZ 1).2; norm_num at this; exact_mod_cast this
  have v4 : (a 4 : ℤ) = 120 := by have := (aZ 2).1; norm_num at this; exact_mod_cast this
  have v5 : (a 5 : ℤ) = 325 := by have := (aZ 2).2; norm_num at this; exact_mod_cast this
  have v6 : (a 6 : ℤ) = 630 := by have := (aZ 3).1; norm_num at this; exact_mod_cast this
  have v7 : (a 7 : ℤ) = 1225 := by have := (aZ 3).2; norm_num at this; exact_mod_cast this
  ext n
  rw [show (2:ℤ⟦X⟧) = C (2:ℤ) by simp, show (6:ℤ⟦X⟧) = C (6:ℤ) by simp]
  simp only [map_sub, map_add, map_neg, coeff_C_mul, coeff_mul_X_pow', hA, coeff_mk]
  rcases Nat.lt_or_ge n 8 with h | h
  · interval_cases n <;> simp only [map_add, map_neg, map_sub, coeff_C_mul, coeff_C, coeff_X_pow, coeff_X, coeff_one, a_zero,
      v0, v1, v2, v3, v4, v5, v6, v7, Nat.cast_zero] <;> norm_num [coeff_C, map_ofNat]
  · obtain ⟨N, rfl⟩ : ∃ N, n = N + 8 := ⟨n - 8, by omega⟩
    simp only [coeff_C_mul, coeff_X_pow, coeff_X, map_add, map_neg, map_sub, coeff_C,
      show 4 ≤ N+8 by omega, show ¬ (N+8-2 = 0) by omega, show ¬ (N+8-3 = 0) by omega, show ¬ (N+8-4 = 0) by omega,
      show ¬ (N+8-5 = 0) by omega, show ¬ (N+8-6 = 0) by omega, if_true,
      show ¬ (N+8 = 7) by omega, show ¬ (N+8 = 6) by omega, show ¬ (N+8 = 5) by omega, show ¬ (N+8 = 4) by omega,
      show ¬ (N+8 = 3) by omega, show ¬ (N+8 = 2) by omega, show ¬ (N+8 = 1) by omega, if_false, mul_zero,
      add_zero, neg_zero]
    simp only [show 8 ≤ N+8 by omega, show 7 ≤ N+8 by omega, show 6 ≤ N+8 by omega, show 5 ≤ N+8 by omega,
      show 3 ≤ N+8 by omega, show 2 ≤ N+8 by omega, show 1 ≤ N+8 by omega, if_true]
    rcases Nat.even_or_odd' N with ⟨u, rfl | rfl⟩
    · rw [show 2*u+8-8 = 2*u by omega, show 2*u+8-7 = 2*(u+0)+1 by omega, show 2*u+8-6 = 2*(u+1) by omega,
        show 2*u+8-5 = 2*(u+1)+1 by omega, show 2*u+8-3 = 2*(u+2)+1 by omega, show 2*u+8-2 = 2*(u+3) by omega,
        show 2*u+8-1 = 2*(u+3)+1 by omega, show 2*u+8 = 2*(u+4) by omega]
      rw [(aZ u).1, (aZ (u+0)).2, (aZ (u+1)).1, (aZ (u+1)).2, (aZ (u+2)).2, (aZ (u+3)).1, (aZ (u+3)).2, (aZ (u+4)).1]
      push_cast; ring
    · rw [show 2*u+1+8-8 = 2*u+1 by omega, show 2*u+1+8-7 = 2*(u+1) by omega, show 2*u+1+8-6 = 2*(u+1)+1 by omega,
        show 2*u+1+8-5 = 2*(u+2) by omega, show 2*u+1+8-3 = 2*(u+3) by omega, show 2*u+1+8-2 = 2*(u+3)+1 by omega,
        show 2*u+1+8-1 = 2*(u+4) by omega, show 2*u+1+8 = 2*(u+4)+1 by omega]
      rw [(aZ u).2, (aZ (u+1)).1, (aZ (u+1)).2, (aZ (u+2)).1, (aZ (u+3)).1, (aZ (u+3)).2, (aZ (u+4)).1, (aZ (u+4)).2]
      push_cast; ring

theorem solution_main :
    (∀ n : ℕ, 1 ≤ n → (a n : ℚ) = ((n : ℚ) ^ 2 * (-(-1 : ℚ) ^ n + (n : ℚ) ^ 2)) / 2) ∧
    (PowerSeries.mk (fun n => (a n : ℤ)) * ((PowerSeries.X - 1) ^ 5 * (PowerSeries.X + 1) ^ 3) =
      -PowerSeries.X * (PowerSeries.X ^ 6 + 4 * PowerSeries.X ^ 5 + 31 * PowerSeries.X ^ 4 + 24 * PowerSeries.X ^ 3
        + 31 * PowerSeries.X ^ 2 + 4 * PowerSeries.X + 1)) := ⟨closed, gf⟩

end OMA.S_oeis_a204558

theorem OMA.solution : type_of% @OMA.S_oeis_a204558.main := OMA.S_oeis_a204558.solution_main
