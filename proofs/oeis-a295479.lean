import OMAStatements.S_oeis_a295479
import Mathlib

/-!
# OEIS A295479: a(n/2) is an integer for every natural number n, with x! = Gamma(x+1)

Credit: @Squee451. The proof was found with Claude (claude-fable-5-2) and Codex; the Lean text was
written by Codex.

Outline. Numerator coefficients U = (24, 4, 1), denominator coefficients V = (12, 8, 7, 2); both lists have
the same sum and the same number of odd entries. (1) n = 2m: a(m) is a ratio of ordinary factorials.
(2) n odd: for odd h, Gamma(h/2 + 1) = h! * sqrt(pi) / (2^h * ((h-1)/2)!); the sqrt(pi) factors
cancel because U and V have equally many odd entries, and a(n/2) becomes 2^(e*n) times a ratio of
factorials of floors floor(c*n/2), with e >= 0. (3) Landau's criterion: by Legendre's formula the
p-adic valuation of such a ratio is a sum over j >= 1 of the step function F(t) = sum of floor(u*t)
minus sum of floor(v*t) at t = m/p^j; F has period 1 (equal coefficient sums) and is constant on
cells [j/L, (j+1)/L) with L the lcm of the coefficients, so F >= 0 is a finite check, done
separately for the even and the odd case. Hence every prime valuation is nonnegative and the ratio
is an integer.
-/

open OMA.S_oeis_a295479

namespace OMA.A295479Proof

-- Reduction of rational floor sums to a finite common-denominator certificate.
lemma floor_scale (L c m q : ℕ) (hL : 0 < L) (hc : 0 < c) (hd : c ∣ L) :
    c * m / q = (L * m / q) / (L / c) := by
  have hdpos : 0 < L / c := Nat.div_pos (Nat.le_of_dvd hL hd) hc
  have he : L / c * c = L := Nat.div_mul_cancel hd
  rw [Nat.div_div_eq_div_mul]
  calc
    c * m / q = (L / c) * (c * m) / ((L / c) * q) :=
      (Nat.mul_div_mul_left (c * m) q hdpos).symm
    _ = L * m / (q * (L / c)) := by rw [← mul_assoc, he, mul_comm (L / c) q]

lemma floor_period (L c J : ℕ) (hL : 0 < L) (hc : 0 < c) (hd : c ∣ L) :
    J / (L / c) = J % L / (L / c) + c * (J / L) := by
  have hdpos : 0 < L / c := Nat.div_pos (Nat.le_of_dvd hL hd) hc
  have he : L / c * c = L := Nat.div_mul_cancel hd
  calc
    J / (L / c) = (J % L + (L / c) * (c * (J / L))) / (L / c) := by
      rw [← mul_assoc, he, Nat.mod_add_div]
    _ = J % L / (L / c) + c * (J / L) := by
      rw [Nat.add_mul_div_left _ _ hdpos]

lemma floor_sum_period (C : List ℕ) (L J : ℕ) (hL : 0 < L)
    (hC : ∀ c ∈ C, 0 < c ∧ c ∣ L) :
    (C.map fun c => J / (L / c)).sum =
      (C.map fun c => J % L / (L / c)).sum + C.sum * (J / L) := by
  induction C with
  | nil => simp
  | cons c C ih =>
    have hc := hC c (by simp)
    have ht : ∀ x ∈ C, 0 < x ∧ x ∣ L := fun x hx => hC x (by simp [hx])
    simp only [List.map_cons, List.sum_cons]
    rw [floor_period L c J hL hc.1 hc.2, ih ht]
    ring

lemma landau_floor (A B : List ℕ) (L : ℕ) (hL : 0 < L)
    (hA : ∀ c ∈ A, 0 < c ∧ c ∣ L) (hB : ∀ c ∈ B, 0 < c ∧ c ∣ L)
    (hs : A.sum = B.sum)
    (hcheck : ∀ j < L, (B.map fun c => j / (L / c)).sum ≤
      (A.map fun c => j / (L / c)).sum)
    (m q : ℕ) :
    (B.map fun c => c * m / q).sum ≤ (A.map fun c => c * m / q).sum := by
  have hmap (C : List ℕ) (hC : ∀ c ∈ C, 0 < c ∧ c ∣ L) :
      C.map (fun c => c * m / q) = C.map (fun c => (L * m / q) / (L / c)) := by
    apply List.map_congr_left
    intro c hc
    exact floor_scale L c m q hL (hC c hc).1 (hC c hc).2
  rw [hmap A hA, hmap B hB, floor_sum_period A L _ hL hA,
    floor_sum_period B L _ hL hB, hs]
  exact Nat.add_le_add_right (hcheck _ (Nat.mod_lt _ hL)) _

lemma factorial_prod_ne_zero (C : List ℕ) : (C.map Nat.factorial).prod ≠ 0 := by
  induction C with
  | nil => simp
  | cons c C ih =>
    simpa only [List.map_cons, List.prod_cons] using
      (mul_ne_zero (Nat.factorial_ne_zero c) ih)

lemma factorial_prod_valuation (C : List ℕ) (p b : ℕ) (hp : p.Prime)
    (hb : ∀ c ∈ C, Nat.log p c < b) :
    padicValNat p (C.map Nat.factorial).prod =
      ∑ i ∈ Finset.Ico 1 b, (C.map fun c => c / p ^ i).sum := by
  have : Fact p.Prime := ⟨hp⟩
  induction C with
  | nil => simp
  | cons c C ih =>
    have hc := hb c (by simp)
    have ht : ∀ x ∈ C, Nat.log p x < b := fun x hx => hb x (by simp [hx])
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    rw [padicValNat.mul (Nat.factorial_ne_zero c) (factorial_prod_ne_zero C),
      padicValNat_factorial hc, ih ht, Finset.sum_add_distrib]

lemma factorial_prod_dvd (A B : List ℕ)
    (hfloor : ∀ q : ℕ, 0 < q →
      (B.map fun b => b / q).sum ≤ (A.map fun a => a / q).sum) :
    (B.map Nat.factorial).prod ∣ (A.map Nat.factorial).prod := by
  apply (Nat.factorization_prime_le_iff_dvd
    (factorial_prod_ne_zero B) (factorial_prod_ne_zero A)).mp
  intro p hp
  rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp]
  have hbound (C : List ℕ) (hC : C.sum ≤ A.sum + B.sum) :
      ∀ c ∈ C, Nat.log p c < A.sum + B.sum + 1 := by
    intro c hc
    have hcs := List.single_le_sum (fun x _ => Nat.zero_le x) c hc
    exact lt_of_le_of_lt ((Nat.log_le_self p c).trans (hcs.trans hC))
      (Nat.lt_succ_self _)
  rw [factorial_prod_valuation B p (A.sum + B.sum + 1) hp (hbound B (by omega)),
    factorial_prod_valuation A p (A.sum + B.sum + 1) hp (hbound A (by omega))]
  exact Finset.sum_le_sum (fun i _ => hfloor (p ^ i) (pow_pos hp.pos i))

lemma gamma_half_factorial (k : ℕ) :
    Real.Gamma (((2 * k + 1 : ℕ) : ℝ) / 2 + 1) =
      ((2 * k + 1).factorial : ℝ) * Real.sqrt Real.pi /
        ((2 : ℝ) ^ (2 * k + 1) * (k.factorial : ℝ)) := by
  have harg : (((2 * k + 1 : ℕ) : ℝ) / 2 + 1) = (k + 1 : ℕ) + (1 : ℝ) / 2 := by
    push_cast
    ring
  rw [harg, Real.Gamma_nat_add_half]
  have hi : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
  rw [hi, Nat.factorial_eq_mul_doubleFactorial, Nat.doubleFactorial_two_mul]
  push_cast
  rw [show 2 * k + 1 = k + (k + 1) by omega, pow_add]
  have hk : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  field_simp
  ring

lemma landau_factorial_dvd (A B : List ℕ) (L : ℕ) (hL : 0 < L)
    (hA : ∀ c ∈ A, 0 < c ∧ c ∣ L) (hB : ∀ c ∈ B, 0 < c ∧ c ∣ L)
    (hs : A.sum = B.sum)
    (hcheck : ∀ j < L, (B.map fun c => j / (L / c)).sum ≤
      (A.map fun c => j / (L / c)).sum)
    (n d : ℕ) :
    (B.map fun c => (c * n / d).factorial).prod ∣
      (A.map fun c => (c * n / d).factorial).prod := by
  have hf : ∀ q : ℕ, 0 < q →
      ((B.map fun c => c * n / d).map fun x => x / q).sum ≤
      ((A.map fun c => c * n / d).map fun x => x / q).sum := by
    intro q _
    simpa only [List.map_map, Function.comp_def, Nat.div_div_eq_div_mul] using
      landau_floor A B L hL hA hB hs hcheck n (d * q)
  simpa only [List.map_map, Function.comp_def] using
    factorial_prod_dvd (A.map fun c => c * n / d) (B.map fun c => c * n / d) hf

-- The two 168-cell certificates for the original and transformed coefficient lists.
lemma even_divisibility (m : ℕ) :
    ((12 * m).factorial * (8 * m).factorial * (7 * m).factorial * (2 * m).factorial) ∣
      ((24 * m).factorial * (4 * m).factorial * m.factorial) := by
  have hc : ∀ j : Fin 168,
      ([12, 8, 7, 2].map fun c => j.val / (168 / c)).sum ≤
      ([24, 4, 1].map fun c => j.val / (168 / c)).sum := by decide +kernel
  have hd := landau_factorial_dvd [24, 4, 1] [12, 8, 7, 2] 168 (by decide)
    (by norm_num) (by norm_num) (by norm_num)
    (fun j hj => hc ⟨j, hj⟩) m 1
  simpa [List.map_cons, List.prod_cons, mul_assoc] using hd

lemma odd_divisibility (n : ℕ) :
    ((7 * n).factorial * (6 * n).factorial * (4 * n).factorial * (n / 2).factorial) ∣
      ((12 * n).factorial * (7 * n / 2).factorial * (2 * n).factorial) := by
  have hc : ∀ j : Fin 168,
      ([14, 12, 8, 1].map fun c => j.val / (168 / c)).sum ≤
      ([24, 7, 4].map fun c => j.val / (168 / c)).sum := by decide +kernel
  have hd := landau_factorial_dvd [24, 7, 4] [14, 12, 8, 1] 168 (by decide)
    (by norm_num) (by norm_num) (by norm_num)
    (fun j hj => hc ⟨j, hj⟩) n 2
  have h24 : 24 * n / 2 = 12 * n := by omega
  have h14 : 14 * n / 2 = 7 * n := by omega
  have h12 : 12 * n / 2 = 6 * n := by omega
  have h8 : 8 * n / 2 = 4 * n := by omega
  have h4 : 4 * n / 2 = 2 * n := by omega
  simpa [h24, h14, h12, h8, h4, mul_assoc] using hd

lemma fac_nat (k : ℕ) : fac (k : ℝ) = (k.factorial : ℝ) :=
  Real.Gamma_nat_eq_factorial k

lemma fac_half_odd (n : ℕ) (hn : n % 2 = 1) :
    fac ((n : ℝ) / 2) = (n.factorial : ℝ) * Real.sqrt Real.pi /
      ((2 : ℝ) ^ n * ((n / 2).factorial : ℝ)) := by
  have he : 2 * (n / 2) + 1 = n := by omega
  simpa only [he, fac] using gamma_half_factorial (n / 2)

lemma integer_of_dvd (N D : ℕ) (hD : D ≠ 0) (h : D ∣ N) :
    ∃ z : ℤ, (N : ℝ) / D = (z : ℝ) := by
  obtain ⟨k, rfl⟩ := h
  refine ⟨(k : ℤ), ?_⟩
  have hd : (D : ℝ) ≠ 0 := by exact_mod_cast hD
  push_cast
  field_simp

lemma even_value (m : ℕ) :
    a (((2 * m : ℕ) : ℝ) / 2) =
      ((24 * m).factorial * (4 * m).factorial * m.factorial : ℕ) /
        (((12 * m).factorial * (8 * m).factorial * (7 * m).factorial *
          (2 * m).factorial : ℕ) : ℝ) := by
  have hm : ((2 * m : ℕ) : ℝ) / 2 = (m : ℝ) := by push_cast; ring
  rw [hm, a]
  have hfac (c : ℕ) : fac ((c : ℝ) * m) = ((c * m).factorial : ℝ) := by
    rw [← Nat.cast_mul, fac_nat]
  have h24 := hfac 24
  have h4 := hfac 4
  have h12 := hfac 12
  have h8 := hfac 8
  have h7 := hfac 7
  have h2 := hfac 2
  norm_num only [Nat.cast_ofNat] at h24 h4 h12 h8 h7 h2
  rw [h24, h4, h12, h8, h7, h2, fac_nat]
  push_cast
  rfl

lemma half_value (n : ℕ) :
    a ((n : ℝ) / 2) =
      ((12 * n).factorial : ℝ) * (2 * n).factorial * fac ((n : ℝ) / 2) /
        ((6 * n).factorial * (4 * n).factorial * fac (((7 * n : ℕ) : ℝ) / 2) *
          (n.factorial : ℝ)) := by
  have he (c : ℕ) : fac ((2 * c : ℕ) * ((n : ℝ) / 2)) = ((c * n).factorial : ℝ) := by
    have hi : ((2 * c : ℕ) : ℝ) * ((n : ℝ) / 2) = ((c * n : ℕ) : ℝ) := by
      push_cast
      ring
    rw [hi, fac_nat]
  have h7 : (7 : ℝ) * ((n : ℝ) / 2) = ((7 * n : ℕ) : ℝ) / 2 := by
    push_cast
    ring
  have h24 := he 12
  have h4 := he 2
  have h12 := he 6
  have h8 := he 4
  have h2 := he 1
  norm_num only [Nat.cast_ofNat, Nat.reduceMul, one_mul] at h24 h4 h12 h8 h2
  rw [a, h24, h4, h12, h8, h2, h7]

lemma odd_value (n : ℕ) (hn : n % 2 = 1) :
    a ((n : ℝ) / 2) =
      ((2 ^ (6 * n) * ((12 * n).factorial * (7 * n / 2).factorial *
        (2 * n).factorial) : ℕ) : ℝ) /
        (((7 * n).factorial * (6 * n).factorial * (4 * n).factorial *
          (n / 2).factorial : ℕ) : ℝ) := by
  have h7 : (7 * n) % 2 = 1 := by omega
  rw [half_value, fac_half_odd n hn, fac_half_odd (7 * n) h7]
  have hp : (2 : ℝ) ^ (7 * n) = 2 ^ n * 2 ^ (6 * n) := by
    rw [show 7 * n = n + 6 * n by omega, pow_add]
  rw [hp]
  have hf (k : ℕ) : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hs : Real.sqrt Real.pi ≠ 0 := Real.sqrt_ne_zero'.mpr Real.pi_pos
  push_cast
  field_simp

end OMA.A295479Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a295479.main := by
  intro n
  obtain ⟨m, he | ho⟩ := Nat.even_or_odd' n
  · subst n
    rw [OMA.A295479Proof.even_value]
    exact OMA.A295479Proof.integer_of_dvd _ _ (by positivity)
      (OMA.A295479Proof.even_divisibility m)
  · have hn : n % 2 = 1 := by omega
    rw [OMA.A295479Proof.odd_value n hn]
    exact OMA.A295479Proof.integer_of_dvd _ _ (by positivity)
      (dvd_mul_of_dvd_right (OMA.A295479Proof.odd_divisibility n) (2 ^ (6 * n)))
