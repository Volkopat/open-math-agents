import OMAReductions.R_Erdos976_erdos_976_variants_tenenbaum_R1

/-! Weighted moments on ordinary integers and the polynomial sieve.

Tenenbaum, "Sur une question d'Erdős et Schinzel, II" (1990), §2: (2.6),
(2.7) compare a divisor-window maximum with its integral moments; (2.14)
bounds their weighted series at fixed large moment order. The separate
polynomial sieve is the one-polynomial special case of Nair–Tenenbaum's
short-sum bound used in Dartyge–Martin–Tenenbaum, "Polynomial values free
of large prime factors" (2001), proof of (2.12). Its constant may depend
on the polynomial, including its fixed prime divisors. -/

namespace OMA.R_Erdos976_erdos_976_variants_tenenbaum_R1_H2_R1
open Finset Real Filter MeasureTheory
open scoped Classical


/-- The two deterministic window estimates of Hall and Tenenbaum. -/
def H1 : Prop :=
  let delta (b : ℕ) := sSup (Set.range (fun u : ℝ =>
    (b.divisors.filter (fun d : ℕ => u < d ∧ (d:ℝ) ≤ exp 1*u)).card))
  let moment (b q : ℕ) := ∫ t : ℝ,
    (∑ d ∈ b.divisors, (Set.Ico (log d-1) (log d)).indicator (fun _ => (1:ℝ)) t)^q
  (∀ a b : ℕ, delta (a*b) ≤ delta a * b.divisors.card) ∧
    ∀ b q : ℕ, (delta b:ℝ)^(q+1) ≤ (2:ℝ)^q * moment b (q+1)

/-- Hall–Tenenbaum's weighted ordinary-integer moment, in the fixed-large-q
form with an arbitrary loss in the logarithmic exponent. -/
def H2 : Prop :=
  let roots (f : Polynomial ℤ) (d : ℕ) := Nat.count (fun a : ℕ => (d:ℤ) ∣ f.eval (a:ℤ)) d
  let moment (b q : ℕ) := ∫ t : ℝ,
    (∑ d ∈ b.divisors, (Set.Ico (log d-1) (log d)).indicator (fun _ => (1:ℝ)) t)^q
  ∀ f : Polynomial ℤ, Irreducible f → 2 ≤ f.natDegree → ∀ ε : ℝ, 0 < ε →
    ∃ q : ℕ, ∀ᶠ n : ℕ in atTop,
      (∑ b ∈ Icc 1 n, (roots f b:ℝ) * (moment b (q+1))^(3/(2*((q:ℝ)+1)):ℝ) / b) ≤
        (log n)^(2*sqrt 2-3/2+ε)

/-- The fixed-polynomial divisor-bounded sieve transfer. The function being
sieved can be any nonnegative weight with the displayed multiplicative growth.
The sieve removes one logarithm relative to the weighted harmonic sum. -/
def H3 : Prop :=
  let roots (f : Polynomial ℤ) (d : ℕ) := Nat.count (fun a : ℕ => (d:ℤ) ∣ f.eval (a:ℤ)) d
  ∀ f : Polynomial ℤ, Irreducible f → 2 ≤ f.natDegree → ∀ w : ℕ → ℝ,
    (∀ b, 0 ≤ w b) → (∀ a b, w (a*b) ≤ w a * (b.divisors.card:ℝ)^(3/2:ℝ)) →
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ n : ℕ in atTop,
      (∑ m ∈ Icc 1 n,w (f.eval (m:ℤ)).natAbs) ≤
        B*((n:ℝ)/log n)*(∑ b ∈ Icc 1 n,(roots f b:ℝ)*w b/b)

theorem main : H1 → H2 → H3 → OMA.R_Erdos976_erdos_976_variants_tenenbaum_R1.H2 := by
  rintro ⟨prod,compare⟩ average sieve f hf hd η hη
  let delta (b : ℕ) := sSup (Set.range (fun u : ℝ =>
    (b.divisors.filter (fun d : ℕ => u < d ∧ (d:ℝ) ≤ exp 1*u)).card))
  let moment (b q : ℕ) := ∫ t : ℝ,
    (∑ d ∈ b.divisors, (Set.Ico (log d-1) (log d)).indicator (fun _ => (1:ℝ)) t)^q
  let roots (f : Polynomial ℤ) (d : ℕ) := Nat.count (fun a : ℕ => (d:ℤ) ∣ f.eval (a:ℤ)) d
  let w (b : ℕ) := (delta b:ℝ)^(3/2:ℝ)
  obtain ⟨B,hB,sieved⟩ := sieve f hf hd w (fun _ => by dsimp [w]; positivity) (by
    intro a b
    dsimp only [w]
    rw [← Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
    exact_mod_cast prod a b)
  obtain ⟨q,avg⟩ := average f hf hd (η/2) (by linarith)
  let r := 3/(2*((q:ℝ)+1))
  let D := ((2:ℝ)^q)^r
  have rpos : 0<r := by dsimp [r]; positivity
  have dpos : 0<D := by dsimp [D]; positivity
  have weight (b : ℕ) : w b ≤ D*(moment b (q+1))^r := by
    have h := compare b q
    have mpos : 0 ≤ moment b (q+1) := by
      by_contra! neg
      exact (not_lt_of_ge (h.trans' (by positivity))) (mul_neg_of_pos_of_neg (by positivity) neg)
    have rat : ((q+1:ℕ):ℝ)*r = 3/2 := by dsimp [r]; push_cast; field_simp
    calc w b = (((delta b:ℝ)^(q+1))^r) := by
          dsimp [w]; rw [←Real.rpow_natCast,←Real.rpow_mul (by positivity),rat]
         _ ≤ ((2:ℝ)^q*moment b (q+1))^r := Real.rpow_le_rpow (by positivity) h rpos.le
         _ = _ := Real.mul_rpow (by positivity) mpos
  have harm (n : ℕ) : (∑ b ∈ Icc 1 n,(roots f b:ℝ)*w b/b) ≤
      D*(∑ b ∈ Icc 1 n,(roots f b:ℝ)*(moment b (q+1))^r/b) := by
    rw [mul_sum]
    apply sum_le_sum
    intro b _
    calc _ ≤ (roots f b:ℝ)*(D*(moment b (q+1))^r)/b := by gcongr; exact weight b
         _ = _ := by ring
  have grow := ((tendsto_rpow_atTop (by linarith : 0<η/2)).comp
    (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually_ge_atTop (B*D)
  filter_upwards [sieved,avg,grow,eventually_ge_atTop (2:ℕ)] with n hs ha hg hn
  have lpos : 0<log n := log_pos (by exact_mod_cast (show 1<n by omega))
  change _ ≤ (log n)^(2*sqrt 2-3/2+η/2) at ha
  change B*D ≤ (log n)^(η/2) at hg
  change (∑ b ∈ Icc 1 n,(roots f b:ℝ)*(moment b (q+1))^r/b) ≤ _ at ha
  have z := (harm n).trans (mul_le_mul_of_nonneg_left ha dpos.le)
  refine hs.trans ((mul_le_mul_of_nonneg_left z (by positivity)).trans ?_)
  calc B*(n/log n)*(D*(log n)^(2*sqrt 2-3/2+η/2)) =
        (n:ℝ)*((B*D)*(log n)^(2*sqrt 2-3/2+η/2))/log n := by ring
       _ ≤ (n:ℝ)*((log n)^(η/2)*(log n)^(2*sqrt 2-3/2+η/2))/log n := by gcongr
       _ = (n:ℝ)*(log n)^(2*sqrt 2-5/2+η) := by
          rw [←Real.rpow_add lpos,show η/2+(2*sqrt 2-3/2+η/2) = (2*sqrt 2-5/2+η)+1 by ring,
            Real.rpow_add_one lpos.ne']
          field_simp

end OMA.R_Erdos976_erdos_976_variants_tenenbaum_R1_H2_R1
