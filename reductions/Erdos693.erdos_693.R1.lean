import FormalConjectures.ErdosProblems.«693»

/-!
# Reduction of Erdős Problem 693
Credit: @Pixelstorm44

The product (n-1)(n+1) separates the two ranges. Below it, use the short
factor q and count its possible complementary divisors in a grid block.
Above it, test crossings of the longer divisor d directly. In the lower
range rounding supplies a hit whenever the quotient by n+1 is small.
-/

namespace OMA.R_Erdos693_erdos_693_R1

open Filter Erdos693

/-- Below the square, some short factor has a complementary divisor in the
intersection of the open divisor window with the block's quotient interval. -/
def H1 : Prop := ∃ C : ℕ, ∀ᶠ n : ℕ in atTop, ∃ B : ℕ,
    3 ≤ B ∧ (B : ℝ) ≤ (Real.log n) ^ C ∧
    ∀ m : ℕ, B ∣ m → B < m / (n + 1) → m + B ≤ n^2 - 1 →
      ∃ q : ℕ, 0 < q ∧ q < n ∧
        max n (m / q) < min (2*n - 1) ((m+B)/q)

/-- Above the square, a divisor crosses a multiple in every full grid block.
The block width exponent is uniform in the polynomial cutoff. -/
def H2 : Prop := ∃ C : ℕ, ∀ k : ℕ, 2 ≤ k → ∀ᶠ n : ℕ in atTop, ∃ B : ℕ,
    3 ≤ B ∧ (B : ℝ) ≤ (Real.log n) ^ C ∧
    ∀ m : ℕ, B ∣ m → n^2 - 1 ≤ m → m + B ≤ n^k →
      ∃ d : ℕ, n < d ∧ d < 2*n ∧ m / d < (m+B)/d

private lemma rounded_hit {m n B : ℕ} (hn : 5 ≤ n) (hm : n ≤ m)
    (hb : 3 ≤ B) (hsmall : m / (n+1) ≤ B) :
    ∃ z d : ℕ, m < z ∧ z ≤ m+B ∧ n < d ∧ d < 2*n ∧ d ∣ z := by
  by_cases hfirst : m+1 < 2*n
  · exact ⟨m+1, m+1, by omega, by omega, by omega, hfirst, dvd_refl _⟩
  by_cases hsecond : m < 2*(n+1)
  · exact ⟨(n+1)*2, n+1, by omega, by omega, by omega, by omega, dvd_mul_right _ _⟩
  let q := m / (n+1)
  have hq : 2 ≤ q := (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
  have hqp : 0 < q := by omega
  have hlo : n+1 ≤ m/q := (Nat.le_div_iff_mul_le hqp).2 (Nat.mul_div_le _ _)
  have hnext : m < (n+1)*(q+1) := Nat.lt_mul_div_succ _ (by omega)
  have hsize : (n+1)*(q+1)+q ≤ (2*n)*q := by
    obtain ⟨a, ha⟩ := Nat.exists_eq_add_of_le hn
    obtain ⟨b, hb'⟩ := Nat.exists_eq_add_of_le hq
    rw [ha, hb']
    nlinarith
  have hhi : m/q+1 < 2*n := by
    by_contra! h
    have := Nat.mul_le_mul_right q h
    have := Nat.div_mul_le_self m q
    nlinarith
  refine ⟨(m/q+1)*q, m/q+1, ?_, ?_, by omega, hhi, dvd_mul_right _ _⟩
  · simpa [Nat.mul_comm] using Nat.lt_mul_div_succ m hqp
  · have : q ≤ B := hsmall
    nlinarith [Nat.div_mul_le_self m q]

private lemma next_block {x y B : ℕ} (hp : 0 < B) (hgap : x+2*B < y) :
    ∃ m : ℕ, B ∣ m ∧ x ≤ m ∧ m+B < y := by
  refine ⟨B*(x/B+1), dvd_mul_right _ _, (Nat.lt_mul_div_succ x hp).le, ?_⟩
  nlinarith [Nat.mul_div_le x B]

private lemma absorb {L : ℝ} {B C D : ℕ} (hL : 2 ≤ L) (hB : (B : ℝ) ≤ L^C)
    (hCD : C ≤ D) : 2*(B : ℝ) ≤ L^(D+1) := by
  rw [pow_succ]
  have h := pow_le_pow_right₀ (by linarith : 1 ≤ L) hCD
  calc
    2*(B : ℝ) ≤ 2*L^D := by linarith
    _ ≤ L^D*L := by nlinarith [mul_nonneg (pow_nonneg (by linarith : 0 ≤ L) D)
                                            (sub_nonneg.mpr hL)]

theorem main : H1 → H2 → type_of% @Erdos693.erdos_693 := by
  rintro ⟨C, hC⟩ ⟨D, hD⟩
  refine ⟨max C D + 1, ?_⟩
  intro k hk
  have logs : ∀ᶠ n : ℕ in atTop, (2 : ℝ) ≤ Real.log n :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 2
  filter_upwards [hC, hD k hk, logs, eventually_ge_atTop 5] with n h₁ h₂ hlog hn
  obtain ⟨A, hA, hAC, low⟩ := h₁
  obtain ⟨B, hB, hBD, high⟩ := h₂
  intro x y hxy
  obtain ⟨hx, hy, hlt, hempty⟩ := hxy
  have endpoints {t : ℕ} (ht : t ∈ divisorWindowSet k n) : n ≤ t ∧ t ≤ n^k :=
    Finset.mem_Icc.mp (Finset.mem_filter.mp ht).1
  have hx' := (endpoints hx).1
  have hy' := (endpoints hy).2
  have exclude {z d : ℕ} (hxz : x < z) (hzy : z < y) (hd : n < d)
      (hd' : d < 2*n) (hdz : d ∣ z) : False := by
    apply hempty z _ hxz hzy
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩,
      d, Finset.mem_filter.mpr ⟨Finset.mem_Ioo.mpr ⟨hd, hd'⟩, hdz⟩⟩
  by_cases hl : y ≤ n^2-1
  · suffices hs : y ≤ x+2*A by
      have h := absorb hlog hAC (le_max_left C D)
      have : (y : ℝ) ≤ (x : ℝ)+2*(A : ℝ) := by exact_mod_cast hs
      linarith
    by_contra! hg
    obtain ⟨m, hm, hxm, hmy⟩ := next_block (by omega : 0 < A) hg
    by_cases hsmall : m/(n+1) ≤ A
    · obtain ⟨z,d,hz,hz',hd,hd',hdz⟩ := rounded_hit hn (by omega) hA hsmall
      exact exclude (lt_of_le_of_lt hxm hz) (by omega) hd hd' hdz
    obtain ⟨q,hq,_,hc⟩ := low m hm (by omega) (by omega)
    let d := max n (m/q)+1
    have hd : n < d := by dsimp [d]; omega
    have hd' : d < 2*n := by dsimp [d]; omega
    have hqd : m/q < d := by dsimp [d]; omega
    have hprod := (Nat.div_lt_iff_lt_mul hq).1 hqd
    have hupper : d ≤ (m+A)/q := by dsimp [d]; omega
    have hu := (Nat.le_div_iff_mul_le hq).1 hupper
    exact exclude (lt_of_le_of_lt hxm hprod) (by omega) hd hd' (dvd_mul_right d q)
  · have hsplit : n^2-1 ≤ x := by
      by_contra! h
      have hfac : n^2-1 = (n+1)*(n-1) := by
        obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hn
        apply Nat.sub_eq_of_eq_add
        have hs : 5+a-1 = 4+a := by omega
        rw [hs]
        ring
      exact exclude h (by omega) (by omega : n < n+1) (by omega) (hfac ▸ dvd_mul_right _ _)
    suffices hs : y ≤ x+2*B by
      have h := absorb hlog hBD (le_max_right C D)
      have : (y : ℝ) ≤ (x : ℝ)+2*(B : ℝ) := by exact_mod_cast hs
      linarith
    by_contra! hg
    obtain ⟨m, hm, hxm, hmy⟩ := next_block (by omega : 0 < B) hg
    obtain ⟨d, hd, hd', hc⟩ := high m hm (by omega) (by omega)
    have hdp : 0 < d := by omega
    have hlo := Nat.lt_mul_div_succ m hdp
    have hu := (Nat.le_div_iff_mul_le hdp).1 (Nat.succ_le_of_lt hc)
    rw [Nat.mul_comm (m / d + 1) d] at hu
    exact exclude (lt_of_le_of_lt hxm hlo) (by omega) hd hd' (dvd_mul_right _ _)

end OMA.R_Erdos693_erdos_693_R1
