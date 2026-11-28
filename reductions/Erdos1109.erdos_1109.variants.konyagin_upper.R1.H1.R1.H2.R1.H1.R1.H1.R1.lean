import OMAReductions.R_Erdos1109_erdos_1109_variants_konyagin_upper_R1_H1_R1_H2_R1_H1_R1
import Mathlib

/-!
# Close quadruples of primitive square-denominator fractions

The elementary counting argument is Konyagin's Lemma 2. The separate estimate
for prime solutions of the three-index identities is his Lemma 1, attributed
there to Bombieri and Zannier.
-/

/- Determinants and numerator recovery for Konyagin's close prime-square fractions. -/

namespace Erdos1109QuadrupleAlgebra

section

variable (minor : (Fin 4 → ℕ) → (Fin 4 → ℕ) → Fin 4 → Fin 4 → ℤ)

/-- The denominator's squared coordinate vector satisfies the three-index identities. -/
theorem relation
    (minor_formula : ∀ p a i j, minor p a i j =
      (a j : ℤ) * (p i : ℤ)^2 - (a i : ℤ) * (p j : ℤ)^2) (p a : Fin 4 → ℕ) (i j k : Fin 4) :
    (p i : ℤ)^2 * minor p a j k - (p j : ℤ)^2 * minor p a i k +
      (p k : ℤ)^2 * minor p a i j = 0 := by
  simp only [minor_formula]
  ring

/-- The six bounded differences satisfy one quadratic relation. -/
theorem plucker
    (minor_formula : ∀ p a i j, minor p a i j =
      (a j : ℤ) * (p i : ℤ)^2 - (a i : ℤ) * (p j : ℤ)^2) (p a : Fin 4 → ℕ) :
    minor p a 0 1 * minor p a 2 3 - minor p a 0 2 * minor p a 1 3 +
      minor p a 0 3 * minor p a 1 2 = 0 := by
  simp only [minor_formula]
  ring

/-- An exact minor, together with two coprime denominators, determines both numerators
in their complete residue intervals. -/
theorem recover_numerators {d e a b c f : ℕ} (hd : 0 < d)
    (hde : Nat.Coprime d e) (ha : a < d) (hc : c < d)
    (hm : (b : ℤ) * d - (a : ℤ) * e = (f : ℤ) * d - (c : ℤ) * e) :
    a = c ∧ b = f := by
  have hprod : ((a : ℤ) - c) * e = ((b : ℤ) - f) * d := by
    linear_combination -hm
  have hdiv : (d : ℤ) ∣ ((a : ℤ) - c) * e := by
    refine ⟨(b : ℤ) - f, ?_⟩
    rw [hprod, mul_comm]
  have hsub := Int.dvd_of_dvd_mul_left_of_gcd_one hdiv (show Int.gcd (d : ℤ) (e : ℤ) = 1 from hde)
  have hlt : Int.natAbs ((a : ℤ) - c) < Int.natAbs (d : ℤ) := by
    simp only [Int.natAbs_natCast]
    omega
  have hzero := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hsub hlt
  have hac : a = c := by omega
  rw [hzero, zero_mul, eq_comm, mul_eq_zero] at hprod
  exact ⟨hac, by obtain hab | hd' := hprod <;> omega⟩

/-- The ordered close-fraction condition makes a cross difference positive and bounded. -/
theorem minor_between {d e a b : ℕ} {Y Z : ℝ} (hd : 0 < d) (he : 0 < e)
    (hlt : (a : ℝ) / d < (b : ℝ) / e) (hclose : (b : ℝ) / e - (a : ℝ) / d ≤ Y/Z)
    (hY : 0 ≤ Y) (hZ : 0 < Z) (hprod : (d : ℝ) * e ≤ Z) :
    0 < (b : ℤ) * d - (a : ℤ) * e ∧ (((b : ℤ) * d - (a : ℤ) * e : ℤ) : ℝ) ≤ Y := by
  have hdr : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have her : (0 : ℝ) < e := Nat.cast_pos.mpr he
  have hcross := (div_lt_div_iff₀ hdr her).mp hlt
  constructor
  · exact_mod_cast (sub_pos.mpr hcross)
  · push_cast
    have hscaled := mul_le_mul_of_nonneg_right hclose (mul_nonneg hdr.le her.le)
    have hn : ((b : ℝ) / e - (a : ℝ) / d) * (d * e) = b*d-a*e := by field_simp
    rw [hn] at hscaled
    exact hscaled.trans ((mul_le_mul_of_nonneg_left hprod (div_nonneg hY hZ.le)).trans_eq
      (div_mul_cancel₀ Y hZ.ne'))

/-- A cluster narrower than the reciprocal of the largest denominator must use different primes. -/
theorem distinct_denominators_and_bounded_minors
    (minor_formula : ∀ p a i j, minor p a i j =
      (a j : ℤ) * (p i : ℤ)^2 - (a i : ℤ) * (p j : ℤ)^2) (p a : Fin 4 → ℕ) {Z Y : ℝ}
    (hp : ∀ i, (p i).Prime) (hden : ∀ i, (p i : ℝ)^2 ≤ Z)
    (hY : 0 ≤ Y) (hYZ : Y < Z)
    (horder : StrictMono (fun i => (a i : ℝ) / (p i : ℝ)^2))
    (hspan : (a 3 : ℝ) / (p 3 : ℝ)^2 - (a 0 : ℝ) / (p 0 : ℝ)^2 ≤ Y/Z^2) :
    Function.Injective p ∧ ∀ i j : Fin 4, i < j → 0 < minor p a i j ∧ (minor p a i j : ℝ) ≤ Y := by
  have hZ : 0 < Z := lt_of_le_of_lt hY hYZ
  have hb (i j : Fin 4) :
      (a j : ℝ)/(p j : ℝ)^2 - (a i : ℝ)/(p i : ℝ)^2 ≤ Y/Z^2 := by
    have hi := horder.monotone (Fin.zero_le i)
    have hj := horder.monotone (show j ≤ 3 by exact Fin.le_last j)
    exact (sub_le_sub hj hi).trans hspan
  constructor
  · intro i j heq
    by_contra hn
    have hs (i j : Fin 4) (hij : i < j) (he : p i = p j) : False := by
      have hp0 : 0 < (p i : ℝ)^2 := by positivity [show 0 < (p i : ℝ) by exact_mod_cast (hp i).pos]
      have hh := horder hij
      simp only [← he] at hh
      have haij : a i < a j := by exact_mod_cast (div_lt_div_iff_of_pos_right hp0).mp hh
      have haij' : (a i : ℝ)+1 ≤ a j := by exact_mod_cast Nat.succ_le_of_lt haij
      have hgap := hb i j
      simp only [← he, ← sub_div] at hgap
      have hlo : 1/(p i : ℝ)^2 ≤ ((a j : ℝ)-a i)/(p i : ℝ)^2 :=
        div_le_div_of_nonneg_right (by linarith) hp0.le
      have hdiv : 1/Z ≤ Y/Z^2 := (one_div_le_one_div_of_le hp0 (hden i)).trans (hlo.trans hgap)
      have hbad : Y/Z^2 < 1/Z := by
        rw [div_lt_iff₀ (sq_pos_of_pos hZ)]
        have hf : (1/Z)*Z^2 = Z := by field_simp
        rwa [hf]
      exact (not_lt_of_ge hdiv) hbad
    rcases lt_or_gt_of_ne hn with h | h
    · exact hs i j h heq
    · exact hs j i h heq.symm
  · intro i j hij
    have hd : 0 < (p i)^2 := pow_pos (hp i).pos _
    have he : 0 < (p j)^2 := pow_pos (hp j).pos _
    have hm : ((p i ^ 2 : ℕ) : ℝ) * ((p j ^ 2 : ℕ) : ℝ) ≤ Z^2 := by
      push_cast
      simpa [pow_two] using mul_le_mul (hden i) (hden j) (by positivity) hZ.le
    have h := minor_between hd he (by exact_mod_cast horder hij) (by exact_mod_cast hb i j)
      hY (sq_pos_of_pos hZ) hm
    simpa [minor_formula] using h

/-- With different prime-square denominators, the first three cross differences against
one fixed entry determine all four numerators. -/
theorem all_numerators_unique
    (minor_formula : ∀ p a i j, minor p a i j =
      (a j : ℤ) * (p i : ℤ)^2 - (a i : ℤ) * (p j : ℤ)^2) (p a b : Fin 4 → ℕ) (hp : ∀ i, (p i).Prime)
    (hpi : Function.Injective p) (ha : a 0 < p 0 ^ 2) (hb : b 0 < p 0 ^ 2)
    (hm : ∀ j : Fin 4, j ≠ 0 → minor p a 0 j = minor p b 0 j) : a = b := by
  have hpair (j : Fin 4) (hj : j ≠ 0) : a 0 = b 0 ∧ a j = b j := by
    have hpc := (Nat.coprime_primes (hp 0) (hp j)).2 (fun h => hj (hpi h).symm)
    have hpow : ((p 0)^2).Coprime ((p j)^2) := hpc.pow 2 2
    exact recover_numerators (pow_pos (hp 0).pos _) hpow ha hb (by simpa [minor_formula] using hm j hj)
  funext i
  by_cases hi : i = 0
  · subst i
    exact (hpair 1 (by decide)).1
  · exact (hpair i hi).2


end

end Erdos1109QuadrupleAlgebra

/- Finite fiber counting for the divisor starts in Konyagin's close-quadruple lemma. -/

namespace Erdos1109QuadrupleFibers

open Erdos1109QuadrupleAlgebra (plucker relation all_numerators_unique)
open scoped Classical

/-- The projection to the prime tuple bounds each start fiber, provided the two projections
together determine the original candidate. -/
theorem card_le_of_start_fibers {ι κ : Type*} [DecidableEq ι]
    (Q : Finset ι) (D₁ D₂ D₃ : Finset ℕ) (start : ι → ℕ × ℕ × ℕ)
    (primes : ι → κ) (primeChoices : (ℕ × ℕ × ℕ) → Finset κ) (P : ℕ)
    (hStarts : ∀ q ∈ Q, start q ∈ D₁ ×ˢ (D₂ ×ˢ D₃))
    (hPrime : ∀ q ∈ Q, primes q ∈ primeChoices (start q))
    (hInj : Set.InjOn (fun q => (start q, primes q)) (Q : Set ι))
    (hCount : ∀ d ∈ D₁ ×ˢ (D₂ ×ˢ D₃), (primeChoices d).card ≤ P) :
    Q.card ≤ D₁.card * D₂.card * D₃.card * P := by
  classical
  calc
    Q.card ≤ P * (D₁ ×ˢ (D₂ ×ˢ D₃)).card := by
      refine Finset.card_le_mul_card_image_of_maps_to hStarts P ?_
      intro d hd
      refine (Finset.card_le_card_of_injOn primes ?_ ?_).trans (hCount d hd)
      · intro q hq
        obtain ⟨hq, he⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hq)
        apply Finset.mem_coe.mpr
        simpa only [he] using hPrime q hq
      · intro q hq r hr hpr
        obtain ⟨hq, heq⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hq)
        obtain ⟨hr, her⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hr)
        exact hInj (Finset.mem_coe.mpr hq) (Finset.mem_coe.mpr hr)
          (Prod.ext (heq.trans her.symm) hpr)
    _ = D₁.card * D₂.card * D₃.card * P := by
      simp only [Finset.card_product]
      ac_rfl

/-- With the products fixed, each start is a divisor of the corresponding product. -/
theorem card_le_divisor_product {ι κ : Type*} [DecidableEq ι]
    (Q : Finset ι) (s₁ s₂ : ℕ) (hs₁ : 0 < s₁) (hs₂ : 0 < s₂)
    (start : ι → ℕ × ℕ × ℕ) (primes : ι → κ)
    (primeChoices : (ℕ × ℕ × ℕ) → Finset κ) (P : ℕ)
    (hDiv : ∀ q ∈ Q, (start q).1 ∣ s₁ ∧ (start q).2.1 ∣ s₂ ∧
      (start q).2.2 ∣ s₁ + s₂)
    (hPrime : ∀ q ∈ Q, primes q ∈ primeChoices (start q))
    (hInj : Set.InjOn (fun q => (start q, primes q)) (Q : Set ι))
    (hCount : ∀ d ∈ s₁.divisors ×ˢ (s₂.divisors ×ˢ (s₁ + s₂).divisors),
      (primeChoices d).card ≤ P) :
    Q.card ≤ s₁.divisors.card * s₂.divisors.card * (s₁ + s₂).divisors.card * P := by
  refine card_le_of_start_fibers Q _ _ _ start primes primeChoices P ?_ hPrime hInj hCount
  intro q hq
  obtain ⟨h₁, h₂, h₃⟩ := hDiv q hq
  exact Finset.mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨h₁, hs₁.ne'⟩,
    Finset.mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨h₂, hs₂.ne'⟩,
      Nat.mem_divisors.mpr ⟨h₃, (Nat.add_pos_left hs₁ s₂).ne'⟩⟩⟩

section

variable (minor : (Fin 4 → ℕ) → (Fin 4 → ℕ) → Fin 4 → Fin 4 → ℤ)

private theorem eq_of_pos_of_natAbs_eq {x y : ℤ}
    (hx : 0 < x) (hy : 0 < y) (h : x.natAbs = y.natAbs) : x = y :=
  (Int.natAbs_eq_natAbs_iff.mp h).resolve_right (by omega)

/-- The two complementary products and their divisor starts determine all six minors. -/
theorem minor_eq_of_starts
    (minor_formula : ∀ p a i j, minor p a i j =
      (a j : ℤ) * (p i : ℤ)^2 - (a i : ℤ) * (p j : ℤ)^2) {p a q b : Fin 4 → ℕ}
    (hp : ∀ i j, i < j → 0 < minor p a i j)
    (hq : ∀ i j, i < j → 0 < minor q b i j)
    (hStart :
      ((minor p a 0 1).natAbs, (minor p a 0 3).natAbs, (minor p a 0 2).natAbs) =
        ((minor q b 0 1).natAbs, (minor q b 0 3).natAbs, (minor q b 0 2).natAbs))
    (h₁ : minor p a 0 1 * minor p a 2 3 = minor q b 0 1 * minor q b 2 3)
    (h₂ : minor p a 0 3 * minor p a 1 2 = minor q b 0 3 * minor q b 1 2) :
    ∀ i j, i < j → minor p a i j = minor q b i j := by
  have h01 : minor p a 0 1 = minor q b 0 1 :=
    eq_of_pos_of_natAbs_eq (hp _ _ (by decide)) (hq _ _ (by decide))
      (congrArg Prod.fst hStart)
  have h03 : minor p a 0 3 = minor q b 0 3 :=
    eq_of_pos_of_natAbs_eq (hp _ _ (by decide)) (hq _ _ (by decide))
      (congrArg (fun d : ℕ × ℕ × ℕ => d.2.1) hStart)
  have h02 : minor p a 0 2 = minor q b 0 2 :=
    eq_of_pos_of_natAbs_eq (hp _ _ (by decide)) (hq _ _ (by decide))
      (congrArg (fun d : ℕ × ℕ × ℕ => d.2.2) hStart)
  have h23 : minor p a 2 3 = minor q b 2 3 :=
    mul_left_cancel₀ (hq 0 1 (by decide)).ne' (by simpa only [h01] using h₁)
  have h12 : minor p a 1 2 = minor q b 1 2 :=
    mul_left_cancel₀ (hq 0 3 (by decide)).ne' (by simpa only [h03] using h₂)
  have h₃ : minor p a 0 2 * minor p a 1 3 = minor q b 0 2 * minor q b 1 3 := by
    linarith only [plucker minor minor_formula p a, plucker minor minor_formula q b, h₁, h₂]
  have h13 : minor p a 1 3 = minor q b 1 3 :=
    mul_left_cancel₀ (hq 0 2 (by decide)).ne' (by simpa only [h02] using h₃)
  intro i j hij
  fin_cases i <;> fin_cases j <;> first
    | exact h01
    | exact h02
    | exact h03
    | exact h12
    | exact h13
    | exact h23
    | exact False.elim ((by decide : ¬ _ < _) hij)

/-- The fixed-product step of Konyagin's Lemma 2, conditional only on a uniform
bound for the size of the prime-tuple solution sets. -/
theorem card_le_fixed_minor_products
    (minor_formula : ∀ p a i j, minor p a i j =
      (a j : ℤ) * (p i : ℤ)^2 - (a i : ℤ) * (p j : ℤ)^2)
    (Q : Finset ((Fin 4 → ℕ) × (Fin 4 → ℕ))) (base : Finset (Fin 4 → ℕ))
    (s₁ s₂ P : ℕ) (hs₁ : 0 < s₁) (hs₂ : 0 < s₂)
    (hBase : ∀ q ∈ Q, q.1 ∈ base)
    (hPrime : ∀ q ∈ Q, ∀ i, (q.1 i).Prime)
    (hDistinct : ∀ q ∈ Q, Function.Injective q.1)
    (hNumerator : ∀ q ∈ Q, q.2 0 < q.1 0 ^ 2)
    (hPositive : ∀ q ∈ Q, ∀ i j, i < j → 0 < minor q.1 q.2 i j)
    (hS₁ : ∀ q ∈ Q, minor q.1 q.2 0 1 * minor q.1 q.2 2 3 = (s₁ : ℤ))
    (hS₂ : ∀ q ∈ Q, minor q.1 q.2 0 3 * minor q.1 q.2 1 2 = (s₂ : ℤ))
    (hSolutions : ∀ d : Fin 4 → Fin 4 → ℤ, (∀ i j, i < j → 0 < d i j) → (base.filter (fun p => ∀ i j k, i < j → j < k →
      (p i : ℤ)^2 * d j k - (p j : ℤ)^2 * d i k + (p k : ℤ)^2 * d i j = 0)).card ≤ P) :
    Q.card ≤ s₁.divisors.card * s₂.divisors.card * (s₁ + s₂).divisors.card * P := by
  classical
  let start (q : (Fin 4 → ℕ) × (Fin 4 → ℕ)) :=
    ((minor q.1 q.2 0 1).natAbs, (minor q.1 q.2 0 3).natAbs, (minor q.1 q.2 0 2).natAbs)
  let solutions (d : Fin 4 → Fin 4 → ℤ) := base.filter fun p => ∀ i j k, i < j → j < k →
      (p i : ℤ)^2 * d j k - (p j : ℤ)^2 * d i k + (p k : ℤ)^2 * d i j = 0
  let choices (d : ℕ × ℕ × ℕ) : Finset (Fin 4 → ℕ) :=
    if h : ∃ q ∈ Q, start q = d
    then solutions (minor h.choose.1 h.choose.2) else ∅
  have hMinors {q r} (hq : q ∈ Q) (hr : r ∈ Q) (h : start q = start r) :
      ∀ i j, i < j → minor q.1 q.2 i j = minor r.1 r.2 i j :=
    minor_eq_of_starts minor minor_formula (hPositive q hq) (hPositive r hr) h
      ((hS₁ q hq).trans (hS₁ r hr).symm) ((hS₂ q hq).trans (hS₂ r hr).symm)
  refine card_le_divisor_product Q s₁ s₂ hs₁ hs₂ start Prod.fst choices P ?_ ?_ ?_ ?_
  · intro q hq
    have hS₃ : minor q.1 q.2 0 2 * minor q.1 q.2 1 3 = ((s₁ + s₂ : ℕ) : ℤ) := by
      push_cast
      linarith only [plucker minor minor_formula q.1 q.2, hS₁ q hq, hS₂ q hq]
    refine ⟨⟨(minor q.1 q.2 2 3).natAbs, ?_⟩, ⟨(minor q.1 q.2 1 2).natAbs, ?_⟩,
      ⟨(minor q.1 q.2 1 3).natAbs, ?_⟩⟩
    · simpa only [Int.natAbs_mul, Int.natAbs_natCast, start] using
        (congrArg Int.natAbs (hS₁ q hq)).symm
    · simpa only [Int.natAbs_mul, Int.natAbs_natCast, start] using
        (congrArg Int.natAbs (hS₂ q hq)).symm
    · simpa only [Int.natAbs_mul, Int.natAbs_natCast, start] using
        (congrArg Int.natAbs hS₃).symm
  · intro q hq
    have h : ∃ r ∈ Q, start r = start q := ⟨q, hq, rfl⟩
    simp only [choices, dif_pos h, solutions, Finset.mem_filter]
    refine ⟨hBase q hq, ?_⟩
    intro i j k hij hjk
    have hEq := hMinors h.choose_spec.1 hq h.choose_spec.2
    rw [hEq i j hij, hEq i k (hij.trans hjk), hEq j k hjk]
    exact relation minor minor_formula q.1 q.2 i j k
  · rintro ⟨p, a⟩ hqa ⟨q, b⟩ hqb h
    obtain rfl : p = q := congrArg Prod.snd h
    refine Prod.ext (show (p, a).1 = (p, b).1 from rfl) ?_
    refine all_numerators_unique minor minor_formula p a b (hPrime _ hqa)
      (hDistinct _ hqa) (hNumerator _ hqa) (hNumerator _ hqb) ?_
    intro i hi
    exact hMinors hqa hqb (congrArg Prod.fst h) 0 i (Fin.pos_iff_ne_zero.mpr hi)
  · intro d _
    by_cases h : ∃ q ∈ Q, start q = d
    · simpa only [choices, dif_pos h] using hSolutions _ (hPositive _ h.choose_spec.1)
    · simp only [choices, dif_neg h, Finset.card_empty, Nat.zero_le]

/-- Summing over the possible pairs of complementary products gives the fourth power
of the minor bound. All nonzero divisors being counted are divisors of numbers at most
the square of that bound. -/
theorem card_le_bounded_minors
    (minor_formula : ∀ p a i j, minor p a i j =
      (a j : ℤ) * (p i : ℤ)^2 - (a i : ℤ) * (p j : ℤ)^2)
    (Q : Finset ((Fin 4 → ℕ) × (Fin 4 → ℕ))) (base : Finset (Fin 4 → ℕ))
    (Y D P : ℕ)
    (hBase : ∀ q ∈ Q, q.1 ∈ base)
    (hPrime : ∀ q ∈ Q, ∀ i, (q.1 i).Prime)
    (hDistinct : ∀ q ∈ Q, Function.Injective q.1)
    (hNumerator : ∀ q ∈ Q, q.2 0 < q.1 0 ^ 2)
    (hMinor : ∀ q ∈ Q, ∀ i j, i < j →
      0 < minor q.1 q.2 i j ∧ minor q.1 q.2 i j ≤ (Y : ℤ))
    (hDivisors : ∀ d : ℕ, 0 < d → d ≤ Y^2 → d.divisors.card ≤ D)
    (hSolutions : ∀ d : Fin 4 → Fin 4 → ℤ, (∀ i j, i < j → 0 < d i j) → (base.filter (fun p => ∀ i j k, i < j → j < k →
      (p i : ℤ)^2 * d j k - (p j : ℤ)^2 * d i k + (p k : ℤ)^2 * d i j = 0)).card ≤ P) :
    Q.card ≤ Y^4 * D^3 * P := by
  classical
  let s (q : (Fin 4 → ℕ) × (Fin 4 → ℕ)) : ℕ × ℕ :=
    ((minor q.1 q.2 0 1 * minor q.1 q.2 2 3).natAbs,
      (minor q.1 q.2 0 3 * minor q.1 q.2 1 2).natAbs)
  let T := (Finset.Icc 1 (Y^2) ×ˢ Finset.Icc 1 (Y^2)).filter
    fun d : ℕ × ℕ => d.1 + d.2 ≤ Y^2
  have hCast {q} (hq : q ∈ Q) :
      (((s q).1 : ℤ) = minor q.1 q.2 0 1 * minor q.1 q.2 2 3) ∧
      (((s q).2 : ℤ) = minor q.1 q.2 0 3 * minor q.1 q.2 1 2) := by
    constructor
    · exact Int.natAbs_of_nonneg (mul_nonneg (hMinor q hq 0 1 (by decide)).1.le
        (hMinor q hq 2 3 (by decide)).1.le)
    · exact Int.natAbs_of_nonneg (mul_nonneg (hMinor q hq 0 3 (by decide)).1.le
        (hMinor q hq 1 2 (by decide)).1.le)
  have hMaps : ∀ q ∈ Q, s q ∈ T := by
    intro q hq
    obtain ⟨hCast₁, hCast₂⟩ := hCast hq
    have hPos₁ : 0 < (s q).1 := by
      exact_mod_cast (hCast₁ ▸ mul_pos (hMinor q hq 0 1 (by decide)).1
        (hMinor q hq 2 3 (by decide)).1 : (0 : ℤ) < (s q).1)
    have hPos₂ : 0 < (s q).2 := by
      exact_mod_cast (hCast₂ ▸ mul_pos (hMinor q hq 0 3 (by decide)).1
        (hMinor q hq 1 2 (by decide)).1 : (0 : ℤ) < (s q).2)
    have hSumZ : ((s q).1 : ℤ) + (s q).2 ≤ (Y : ℤ)^2 := by
      rw [hCast₁, hCast₂]
      have hbound := mul_le_mul (hMinor q hq 0 2 (by decide)).2
        (hMinor q hq 1 3 (by decide)).2 (hMinor q hq 1 3 (by decide)).1.le
        (Int.natCast_nonneg Y)
      rw [← pow_two] at hbound
      linarith only [plucker minor minor_formula q.1 q.2, hbound]
    have hSum : (s q).1 + (s q).2 ≤ Y^2 := by exact_mod_cast hSumZ
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨
      Finset.mem_Icc.mpr ⟨hPos₁, (Nat.le_add_right _ _).trans hSum⟩,
      Finset.mem_Icc.mpr ⟨hPos₂, (Nat.le_add_left _ _).trans hSum⟩⟩, hSum⟩
  have hT : T.card ≤ Y^4 := by
    calc
      T.card ≤ (Finset.Icc 1 (Y^2) ×ˢ Finset.Icc 1 (Y^2)).card :=
        Finset.card_filter_le _ _
      _ = Y^4 := by simp [Finset.card_product, Nat.card_Icc, pow_succ, mul_assoc]
  calc
    Q.card ≤ (D^3 * P) * T.card := by
      refine Finset.card_le_mul_card_image_of_maps_to hMaps (D^3 * P) ?_
      intro d hd
      obtain ⟨hd, hSum⟩ := Finset.mem_filter.mp hd
      obtain ⟨hd₁, hd₂⟩ := Finset.mem_product.mp hd
      obtain ⟨hp₁, hB₁⟩ := Finset.mem_Icc.mp hd₁
      obtain ⟨hp₂, hB₂⟩ := Finset.mem_Icc.mp hd₂
      let Qd := Q.filter (fun q => s q = d)
      have hQd {q} (hq : q ∈ Qd) : q ∈ Q := (Finset.mem_filter.mp hq).1
      have hProducts {q} (hq : q ∈ Qd) :
          minor q.1 q.2 0 1 * minor q.1 q.2 2 3 = (d.1 : ℤ) ∧
          minor q.1 q.2 0 3 * minor q.1 q.2 1 2 = (d.2 : ℤ) := by
        have he := (Finset.mem_filter.mp hq).2
        obtain ⟨h₁, h₂⟩ := hCast (hQd hq)
        exact ⟨by simpa only [he] using h₁.symm, by simpa only [he] using h₂.symm⟩
      have hBound := card_le_fixed_minor_products minor minor_formula Qd base d.1 d.2 P hp₁ hp₂
        (fun q hq => hBase q (hQd hq)) (fun q hq => hPrime q (hQd hq))
        (fun q hq => hDistinct q (hQd hq)) (fun q hq => hNumerator q (hQd hq))
        (fun q hq i j hij => (hMinor q (hQd hq) i j hij).1)
        (fun _ hq => (hProducts hq).1) (fun _ hq => (hProducts hq).2) hSolutions
      refine hBound.trans ?_
      rw [pow_succ, pow_two]
      exact Nat.mul_le_mul_right P (Nat.mul_le_mul
        (Nat.mul_le_mul (hDivisors _ hp₁ hB₁) (hDivisors _ hp₂ hB₂))
        (hDivisors _ (Nat.add_pos_left hp₁ _) hSum))
    _ ≤ (D^3 * P) * Y^4 := Nat.mul_le_mul_left _ hT
    _ = Y^4 * D^3 * P := by ac_rfl

end

end Erdos1109QuadrupleFibers

namespace OMA.R_Erdos1109_erdos_1109_variants_konyagin_upper_R1_H1_R1_H2_R1_H1_R1_H1_R1

open Filter Finset
open scoped Topology
open Erdos1109QuadrupleAlgebra (distinct_denominators_and_bounded_minors)
open Erdos1109QuadrupleFibers (card_le_bounded_minors)

/-- The uniform subpower bound on prime tuples satisfying the identities of a fixed
positive array of minors. -/
def H1 : Prop := by
  classical
  exact ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    let X := ⌊(N : ℝ)^(4/15 : ℝ)⌋₊
    let primes := (Finset.range (X+1)).filter Nat.Prime
    let base := (Fintype.piFinset (fun _ : Fin 4 => primes)).filter Function.Injective
    ∀ d : Fin 4 → Fin 4 → ℤ, (∀ i j, i < j → 0 < d i j) →
      ((base.filter fun p => ∀ i j k, i < j → j < k →
        (p i : ℤ)^2 * d j k - (p j : ℤ)^2 * d i k + (p k : ℤ)^2 * d i j = 0).card : ℝ)
        ≤ (N : ℝ)^(ε/2)

/-- The uniform subpower divisor bound in the range containing the complementary products. -/
def H2 : Prop := ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
  ∀ m ≤ N^2, (m.divisors.card : ℝ) ≤ (N : ℝ)^(ε/6)

/-- A close ordered quadruple gives a distinct-prime octuple counted by Konyagin's
minor identities. -/
theorem main : H1 → H2 → OMA.R_Erdos1109_erdos_1109_variants_konyagin_upper_R1_H1_R1_H2_R1_H1_R1.H1 := by
  classical
  let minor (p a : Fin 4 → ℕ) (i j : Fin 4) : ℤ :=
    (a j : ℤ) * (p i : ℤ)^2 - (a i : ℤ) * (p j : ℤ)^2
  have minor_formula (p a : Fin 4 → ℕ) (i j : Fin 4) : minor p a i j =
      (a j : ℤ) * (p i : ℤ)^2 - (a i : ℤ) * (p j : ℤ)^2 := rfl
  intro hPrime hDivisor ε hε
  filter_upwards [hPrime ε hε, hDivisor ε hε, eventually_ge_atTop 1] with N hPrime hDivisor hN
  intro Y hY hYZ
  let X := ⌊(N : ℝ)^(4/15 : ℝ)⌋₊
  let primes := (Finset.range (X+1)).filter Nat.Prime
  let base := (Fintype.piFinset (fun _ : Fin 4 => primes)).filter Function.Injective
  let J := primes.sigma (fun p => (range (p*p)).filter (fun r => N < p^4 ∧ ¬p ∣ r))
  let α (j : Sigma (fun _ : ℕ => ℕ)) : ℝ := (j.2 : ℝ) / (j.1*j.1 : ℕ)
  let δ := Y / (N : ℝ)^(16/15 : ℝ)
  let Q := (J ×ˢ (J ×ˢ (J ×ˢ J))).filter fun q =>
    α q.1 < α q.2.1 ∧ α q.2.1 < α q.2.2.1 ∧ α q.2.2.1 < α q.2.2.2 ∧
    α q.2.2.2 - α q.1 ≤ δ
  change (Q.card : ℝ) ≤ _
  let entries (q : Sigma (fun _ : ℕ => ℕ) × Sigma (fun _ : ℕ => ℕ) ×
      Sigma (fun _ : ℕ => ℕ) × Sigma (fun _ : ℕ => ℕ)) : Fin 4 → Sigma (fun _ : ℕ => ℕ) :=
    ![q.1, q.2.1, q.2.2.1, q.2.2.2]
  let encode (q : Sigma (fun _ : ℕ => ℕ) × Sigma (fun _ : ℕ => ℕ) ×
      Sigma (fun _ : ℕ => ℕ) × Sigma (fun _ : ℕ => ℕ)) : (Fin 4 → ℕ) × (Fin 4 → ℕ) :=
    (fun i => (entries q i).1, fun i => (entries q i).2)
  let octuples := Q.image encode
  have hencode : Function.Injective encode := by
    intro q r h
    have hentry (i : Fin 4) : entries q i = entries r i :=
      Sigma.ext (congrFun (congrArg Prod.fst h) i) (heq_of_eq (congrFun (congrArg Prod.snd h) i))
    exact Prod.ext (hentry 0) (Prod.ext (hentry 1) (Prod.ext (hentry 2) (hentry 3)))
  have hcard : octuples.card = Q.card := Finset.card_image_iff.mpr hencode.injOn
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans_le hNr
  have hYnonneg : 0 ≤ Y := zero_le_one.trans hY
  let Z := (N : ℝ)^(8/15 : ℝ)
  have hδ : δ = Y/Z^2 := by
    dsimp [δ, Z]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
    norm_num
  have hSmall (q) (hq : q ∈ Q) :
      (encode q).1 ∈ base ∧
      (∀ i, ((encode q).1 i).Prime) ∧ Function.Injective (encode q).1 ∧
      (encode q).2 0 < (encode q).1 0 ^ 2 ∧
      ∀ i j, i < j → 0 < minor (encode q).1 (encode q).2 i j ∧
        minor (encode q).1 (encode q).2 i j ≤ (⌊Y⌋₊ : ℤ) := by
    let p := (encode q).1
    let a := (encode q).2
    obtain ⟨hJ, h01, h12, h23, hspan⟩ := mem_filter.mp hq
    obtain ⟨hq₀, hJ⟩ := mem_product.mp hJ
    obtain ⟨hq₁, hJ⟩ := mem_product.mp hJ
    obtain ⟨hq₂, hq₃⟩ := mem_product.mp hJ
    have hj (i : Fin 4) : entries q i ∈ J := by
      fin_cases i <;> first | exact hq₀ | exact hq₁ | exact hq₂ | exact hq₃
    have hp (i : Fin 4) : p i ∈ primes := (mem_sigma.mp (hj i)).1
    have hpPrime (i : Fin 4) : (p i).Prime := (mem_filter.mp (hp i)).2
    have hden (i : Fin 4) : (p i : ℝ)^2 ≤ Z := by
      have hpi : p i ≤ X := Nat.lt_succ_iff.mp (mem_range.mp (mem_filter.mp (hp i)).1)
      have hpi' : (p i : ℝ) ≤ (N : ℝ)^(4/15 : ℝ) :=
        (Nat.cast_le.mpr hpi).trans (Nat.floor_le (by positivity))
      calc
        _ ≤ ((N : ℝ)^(4/15 : ℝ))^2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hpi' 2
        _ = _ := by
          dsimp [Z]
          rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
          norm_num
    have ha₀ : a 0 < p 0 ^ 2 := by
      simpa only [a, p, encode, pow_two] using
        (mem_range.mp (mem_filter.mp (mem_sigma.mp (hj 0)).2).1)
    have hα (i : Fin 4) : α (entries q i) = (a i : ℝ) / (p i : ℝ)^2 := by
      simp only [α, a, p, encode, Nat.cast_mul, pow_two]
    have hOrder : StrictMono (fun i => (a i : ℝ) / (p i : ℝ)^2) := by
      rw [Fin.strictMono_iff_lt_succ]
      intro i
      rw [← hα, ← hα]
      fin_cases i <;> first | exact h01 | exact h12 | exact h23
    have hSpan : (a 3 : ℝ) / (p 3 : ℝ)^2 - (a 0 : ℝ) / (p 0 : ℝ)^2 ≤ Y/Z^2 := by
      rw [← hα, ← hα, ← hδ]
      exact hspan
    obtain ⟨hinj, hm⟩ :=
      distinct_denominators_and_bounded_minors minor minor_formula p a hpPrime hden hYnonneg hYZ hOrder hSpan
    refine ⟨mem_filter.mpr ⟨Fintype.mem_piFinset.mpr hp, hinj⟩, hpPrime, hinj, ha₀, ?_⟩
    intro i j hij
    obtain ⟨hp, hy⟩ := hm i j hij
    exact ⟨hp, by rwa [Int.natCast_floor_eq_floor hYnonneg, Int.le_floor]⟩
  have hOct {q} (hq : q ∈ octuples) :
      q.1 ∈ base ∧ (∀ i, (q.1 i).Prime) ∧ Function.Injective q.1 ∧ q.2 0 < q.1 0 ^ 2 ∧
      ∀ i j, i < j → 0 < minor q.1 q.2 i j ∧
        minor q.1 q.2 i j ≤ (⌊Y⌋₊ : ℤ) := by
    obtain ⟨r, hr, rfl⟩ := mem_image.mp hq
    exact hSmall r hr
  have hyN : ⌊Y⌋₊ ≤ N :=
    Nat.floor_le_of_le (hYZ.le.trans (Real.rpow_le_self_of_one_le hNr (by norm_num)))
  let D := ⌊(N : ℝ)^(ε/6)⌋₊
  let B := ⌊(N : ℝ)^(ε/2)⌋₊
  have hD (m : ℕ) (_ : 0 < m) (hm : m ≤ ⌊Y⌋₊^2) : m.divisors.card ≤ D :=
    Nat.le_floor (hDivisor m (hm.trans (pow_le_pow_left' hyN 2)))
  have hB (d : Fin 4 → Fin 4 → ℤ) (hd : ∀ i j, i < j → 0 < d i j) :
      (base.filter (fun p => ∀ i j k, i < j → j < k →
      (p i : ℤ)^2 * d j k - (p j : ℤ)^2 * d i k + (p k : ℤ)^2 * d i j = 0)).card ≤ B :=
    Nat.le_floor (hPrime d hd)
  have hCount := card_le_bounded_minors minor minor_formula octuples base ⌊Y⌋₊ D B
    (fun _ hq => (hOct hq).1) (fun _ hq => (hOct hq).2.1)
    (fun _ hq => (hOct hq).2.2.1) (fun _ hq => (hOct hq).2.2.2.1)
    (fun _ hq => (hOct hq).2.2.2.2) hD hB
  have hD' : (D : ℝ) ≤ (N : ℝ)^(ε/6) := Nat.floor_le (by positivity)
  have hB' : (B : ℝ) ≤ (N : ℝ)^(ε/2) := Nat.floor_le (by positivity)
  have hPow : ((N : ℝ)^(ε/6))^3 * (N : ℝ)^(ε/2) = (N : ℝ)^ε := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le, ← Real.rpow_add hNpos]
    congr 1
    push_cast
    ring
  calc
    (Q.card : ℝ) = octuples.card := by rw [hcard]
    _ ≤ (⌊Y⌋₊ : ℝ)^4 * (D : ℝ)^3 * (B : ℝ) := by exact_mod_cast hCount
    _ ≤ Y^4 * ((N : ℝ)^(ε/6))^3 * (N : ℝ)^(ε/2) := by
      exact mul_le_mul (mul_le_mul
        (pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.floor_le hYnonneg) 4)
        (pow_le_pow_left₀ (Nat.cast_nonneg _) hD' 3) (by positivity) (by positivity))
        hB' (by positivity) (by positivity)
    _ = (N : ℝ)^ε * Y^4 := by rw [mul_assoc, hPow, mul_comm]

end OMA.R_Erdos1109_erdos_1109_variants_konyagin_upper_R1_H1_R1_H2_R1_H1_R1_H1_R1
