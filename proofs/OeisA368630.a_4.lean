import FormalConjectures.OEIS.«368630»

namespace OMA.A368630
open PowerSeries
open OeisA368630

/-- The source equation with constant term one and exponents $r,s$. -/
def Original (r s : ℕ) (F : ℚ⟦X⟧) : Prop :=
  F.constantCoeff = 1 ∧
    F.subst (X * (F⁻¹) ^ r) = (exp ℚ).subst (X * F ^ s)

lemma constantCoeff_subst_of_zero (F G : ℚ⟦X⟧) (hG : G.constantCoeff = 0) :
    PowerSeries.constantCoeff (F.subst G) = F.constantCoeff := by
  change MvPowerSeries.constantCoeff (F.subst G) = F.constantCoeff
  rw [PowerSeries.constantCoeff_subst (HasSubst.of_constantCoeff_zero' hG)]
  simp only [map_pow]
  change (∑ᶠ d : ℕ, coeff d F • (G.constantCoeff ^ d)) = F.constantCoeff
  rw [finsum_eq_single (a := 0)]
  · simp
  · intro d hd
    simp [hG, hd]

/-- Every solution of the original equation admits the auxiliary series stated in OEIS. -/
theorem original_auxiliary {r s : ℕ} {F : ℚ⟦X⟧} (hF : Original r s F) :
    ∃ B : ℚ⟦X⟧, B.constantCoeff = 1 ∧
      B = F.subst (X * B ^ r) ∧
      F = (exp ℚ).subst (X * B ^ (r + s)) := by
  let G : ℚ⟦X⟧ := X * (F⁻¹) ^ r
  have hG0 : G.constantCoeff = 0 := by simp [G]
  have hG1 : G.coeff 1 = 1 := by
    simp [G, PowerSeries.constantCoeff_inv, hF.1]
  have hGu : IsUnit (G.coeff 1) := hG1 ▸ isUnit_one
  let H := G.substInvOfIsUnit hGu
  have hH0 : H.constantCoeff = 0 := by simp [H]
  have hG : HasSubst G := HasSubst.of_constantCoeff_zero' hG0
  have hH : HasSubst H := HasSubst.of_constantCoeff_zero' hH0
  have hGH : G.subst H = X := PowerSeries.subst_substInvOfIsUnit_right G hG0 hGu
  let B : ℚ⟦X⟧ := F.subst H
  have hB0 : B.constantCoeff = 1 := by
    rw [constantCoeff_subst_of_zero F H hH0, hF.1]
  have hinv : F⁻¹ * F = 1 := PowerSeries.inv_mul_cancel F (by rw [hF.1]; norm_num)
  have hcancel : G * F ^ r = X := by
    dsimp [G]
    rw [mul_assoc, ← mul_pow, hinv, one_pow, mul_one]
  have hHB : H = X * B ^ r := by
    have hc := congrArg (fun K : ℚ⟦X⟧ => K.subst H) hcancel
    rw [subst_mul hH, subst_pow hH, hGH, subst_X hH] at hc
    simpa [B] using hc.symm
  refine ⟨B, hB0, ?_, ?_⟩
  · change F.subst H = F.subst (X * B ^ r)
    rw [hHB]
  · have he := congrArg (fun K : ℚ⟦X⟧ => K.subst H) hF.2
    rw [subst_comp_subst_apply hG hH, hGH, X_subst] at he
    have hS : HasSubst (X * F ^ s) := by
      apply HasSubst.of_constantCoeff_zero'
      simp
    rw [subst_comp_subst_apply hS hH, subst_mul hH, subst_X hH, subst_pow hH] at he
    change F = (exp ℚ).subst (H * B ^ s) at he
    rw [he]
    congr 1
    rw [hHB, pow_add, mul_assoc]

/-- The auxiliary equations imply the original equation, without a recurrence assumption. -/
theorem auxiliary_original {r s : ℕ} {F B : ℚ⟦X⟧}
    (hB0 : B.constantCoeff = 1)
    (hB : B = F.subst (X * B ^ r))
    (hF : F = (exp ℚ).subst (X * B ^ (r + s))) : Original r s F := by
  let H : ℚ⟦X⟧ := X * B ^ r
  have hH0 : H.constantCoeff = 0 := by simp [H]
  have hH : HasSubst H := HasSubst.of_constantCoeff_zero' hH0
  have hF0 : F.constantCoeff = 1 := by
    rw [hF, constantCoeff_subst_of_zero]
    · simp
    · simp
  let G : ℚ⟦X⟧ := X * (F⁻¹) ^ r
  have hG0 : G.constantCoeff = 0 := by simp [G]
  have hG : HasSubst G := HasSubst.of_constantCoeff_zero' hG0
  have hFB : F.subst H = B := hB.symm
  have hi : B * (F⁻¹).subst H = 1 := by
    have he := congrArg (fun K : ℚ⟦X⟧ => K.subst H)
      (PowerSeries.mul_inv_cancel F (by rw [hF0]; norm_num))
    have hone : (1 : ℚ⟦X⟧).subst H = 1 := by
      rw [← coe_substAlgHom hH]
      exact map_one _
    simpa only [subst_mul hH, hFB, hone] using he
  have hGH : G.subst H = X := by
    dsimp [G]
    rw [subst_mul hH, subst_X hH, subst_pow hH]
    change (X * B ^ r) * subst H F⁻¹ ^ r = X
    rw [mul_assoc, ← mul_pow, hi, one_pow, mul_one]
  have hH1 : H.coeff 1 = 1 := by simp [H, hB0]
  have hHu : IsUnit (H.coeff 1) := hH1 ▸ isUnit_one
  let J := H.substInvOfIsUnit hHu
  have hJ : HasSubst J := HasSubst.substInvOfIsUnit H hHu
  have hHJ : H.subst J = X := subst_substInvOfIsUnit_right H hH0 hHu
  have hGJ : G = J := by
    have he := congrArg (fun K : ℚ⟦X⟧ => K.subst J) hGH
    rwa [subst_comp_subst_apply hH hJ, hHJ, X_subst, subst_X hJ] at he
  have hHG : H.subst G = X := by simpa only [hGJ] using hHJ
  have hBG : B.subst G = F := by
    rw [hB, subst_comp_subst_apply hH hG, hHG, X_subst]
  refine ⟨hF0, ?_⟩
  have hK : HasSubst (X * B ^ (r + s)) := by
    apply HasSubst.of_constantCoeff_zero'
    simp
  have he := congrArg (fun K : ℚ⟦X⟧ => K.subst G) hF
  rw [subst_comp_subst_apply hK hG, subst_mul hG, subst_X hG, subst_pow hG, hBG] at he
  rw [he]
  congr 1
  dsimp [G]
  rw [pow_add]
  have hiF : F⁻¹ * F = 1 := PowerSeries.inv_mul_cancel F (by rw [hF0]; norm_num)
  calc
    X * F⁻¹ ^ r * (F ^ r * F ^ s) = X * ((F⁻¹ * F) ^ r) * F ^ s := by ring
    _ = X * F ^ s := by rw [hiF, one_pow, mul_one]

namespace Causal
variable {R : Type*}

/-- A coefficient operator is causal if output $n$ only uses input indices below $n$. -/
def IsCausal (T : (ℕ → R) → ℕ → R) : Prop :=
  ∀ n a b, (∀ k, k < n → a k = b k) → T a n = T b n

/-- Coefficient recursion for a causal operator. -/
def fixedPoint (T : (ℕ → R) → ℕ → R) (seed : ℕ → R) (n : ℕ) : R :=
  T (fun k => if _h : k < n then fixedPoint T seed k else seed k) n
termination_by n

lemma fixedPoint_eq (T : (ℕ → R) → ℕ → R) (hT : IsCausal T) (seed : ℕ → R)
    (n : ℕ) : fixedPoint T seed n = T (fixedPoint T seed) n := by
  rw [fixedPoint]
  apply hT
  intro k hk
  simp [hk]

/-- A causal coefficient operator has exactly one fixed point. -/
theorem exists_unique_fixed_point (T : (ℕ → R) → ℕ → R) (hT : IsCausal T)
    (seed : ℕ → R) : ∃! a : ℕ → R, T a = a := by
  have hf : T (fixedPoint T seed) = fixedPoint T seed := by
    funext n
    exact (fixedPoint_eq T hT seed n).symm
  refine ⟨fixedPoint T seed, hf, ?_⟩
  intro a ha
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    calc
      a n = T a n := (congrFun ha n).symm
      _ = T (fixedPoint T seed) n := hT n a (fixedPoint T seed) (fun k hk => ih k hk)
      _ = fixedPoint T seed n := congrFun hf n
end Causal

namespace Hurwitz
open Finset
variable {R : Type*} [CommRing R]
/-- Differentiation shifts an EGF coefficient sequence. -/
def shift (a : ℕ → R) (n : ℕ) := a (n + 1)
/-- The EGF product, recursively specified by its constant term and the product rule. -/
def product (a b : ℕ → R) : ℕ → R
  | 0 => a 0 * b 0
  | n + 1 => product (shift a) b n + product a (shift b) n
@[simp] lemma product_zero (a b : ℕ → R) : product a b 0 = a 0 * b 0 := rfl
lemma product_succ (a b : ℕ → R) (n : ℕ) :
    product a b (n + 1) = product (shift a) b n + product a (shift b) n := rfl
lemma product_comm (a b : ℕ → R) : product a b = product b a := by
  funext n
  induction n generalizing a b with
  | zero => simp [mul_comm]
  | succ n ih => rw [product_succ, product_succ, ih (shift a) b, ih a (shift b), add_comm]
lemma map_product {S : Type*} [CommRing S] (φ : R →+* S) (a b : ℕ → R) :
    φ ∘ product a b = product (φ ∘ a) (φ ∘ b) := by
  funext n
  change φ (product a b n) = product (φ ∘ a) (φ ∘ b) n
  induction n generalizing a b with
  | zero => simp
  | succ n ih =>
    change φ (product (shift a) b n + product a (shift b) n) = _
    rw [map_add, ih, ih]
    rfl

/-- Derivatives at zero, rather than ordinary coefficients. -/
noncomputable def jet (F : ℚ⟦X⟧) (n : ℕ) : ℚ := n.factorial * F.coeff n
lemma jet_zero (F : ℚ⟦X⟧) : jet F 0 = F.constantCoeff := by simp [jet]
lemma jet_derivative (F : ℚ⟦X⟧) : jet (derivative ℚ F) = shift (jet F) := by
  funext n
  simp only [jet, shift, coeff_derivative, Nat.factorial_succ, Nat.cast_mul]
  push_cast
  ring
lemma jet_add (F G : ℚ⟦X⟧) : jet (F + G) = jet F + jet G := by
  funext n
  simp [jet, mul_add]
lemma jet_product (F G : ℚ⟦X⟧) : jet (F * G) = product (jet F) (jet G) := by
  funext n
  induction n generalizing F G with
  | zero => simp [jet_zero]
  | succ n ih =>
    change shift (jet (F * G)) n = _
    rw [← jet_derivative, (derivative ℚ).leibniz]
    simp only [smul_eq_mul]
    rw [jet_add]
    simp only [Pi.add_apply, product_succ]
    rw [ih, ih, jet_derivative, jet_derivative]
    rw [product_comm (jet G) (shift (jet F)), add_comm]

lemma jet_egf (a : ℕ → ℤ) : jet (egf a) = Int.castRingHom ℚ ∘ a := by
  funext n
  simp only [jet, egf, coeff_mk, Function.comp_apply, Int.coe_castRingHom]
  have hn : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  field_simp

def unitSequence : ℕ → R := fun n => if n = 0 then 1 else 0
lemma jet_X_mul_succ (F : ℚ⟦X⟧) (n : ℕ) :
    jet (X * F) (n + 1) = (n + 1) * jet F n := by
  simp only [jet, coeff_succ_X_mul, Nat.factorial_succ, Nat.cast_mul]
  push_cast
  ring

lemma product_congr (a b c d : ℕ → R) (n : ℕ)
    (ha : ∀ k ≤ n, a k = c k) (hb : ∀ k ≤ n, b k = d k) :
    product a b n = product c d n := by
  induction n generalizing a b c d with
  | zero => simp [ha 0 le_rfl, hb 0 le_rfl]
  | succ n ih =>
    rw [product_succ, product_succ]
    congr 1
    · apply ih
      · exact fun k hk => ha _ (by omega)
      · exact fun k hk => hb k (by omega)
    · apply ih
      · exact fun k hk => ha k (by omega)
      · exact fun k hk => hb _ (by omega)

/-- Powers in the integer EGF algebra. -/
def power (a : ℕ → R) : ℕ → ℕ → R
  | 0 => unitSequence
  | k + 1 => product (power a k) a

lemma power_congr (a b : ℕ → R) (k n : ℕ) (h : ∀ i ≤ n, a i = b i) :
    power a k n = power b k n := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    apply product_congr
    · intro i hi; exact ih i (fun j hj => h j (hj.trans hi))
    · exact h

lemma map_power {S : Type*} [CommRing S] (φ : R →+* S) (a : ℕ → R) (k : ℕ) :
    φ ∘ power a k = power (φ ∘ a) k := by
  induction k with
  | zero => funext n; simp [power, unitSequence, Function.comp_apply]
  | succ k ih => change φ ∘ product (power a k) a = _; rw [map_product, ih]; rfl

/-- Rational series reconstructed from its derivatives at zero. -/
noncomputable def qegf (a : ℕ → ℚ) : ℚ⟦X⟧ := mk fun n => a n / n.factorial

lemma jet_qegf (a : ℕ → ℚ) : jet (qegf a) = a := by
  funext n
  simp only [jet, qegf, coeff_mk]
  have hn : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  field_simp

lemma jet_injective : Function.Injective jet := by
  intro F G h
  ext n
  have he := congrFun h n
  exact mul_left_cancel₀ (by exact_mod_cast n.factorial_ne_zero) he

lemma qegf_jet (F : ℚ⟦X⟧) : qegf (jet F) = F :=
  jet_injective (jet_qegf _)

lemma jet_one : jet (1 : ℚ⟦X⟧) = unitSequence := by
  funext n
  cases n <;> simp [jet, unitSequence]

lemma jet_pow (F : ℚ⟦X⟧) (k : ℕ) : jet (F ^ k) = power (jet F) k := by
  induction k with
  | zero => simpa [power] using jet_one
  | succ k ih => rw [pow_succ, jet_product, ih]; rfl

/-- Finite ordinary coefficient formula for substitution by $xD(x)$. -/
theorem coeff_subst_X_mul (F D : ℚ⟦X⟧) (n : ℕ) :
    coeff n (F.subst (X * D)) =
      ∑ k ∈ range (n + 1), coeff k F * coeff (n - k) (D ^ k) := by
  classical
  have hg : HasSubst (X * D) := HasSubst.of_constantCoeff_zero' (by simp)
  rw [coeff_subst' hg]
  have hs : Function.support (fun k : ℕ => coeff k F • coeff n ((X * D) ^ k)) ⊆
      (range (n + 1) : Set ℕ) := by
    intro k hk
    by_contra hkn
    have hle : ¬k ≤ n := fun hk => hkn (mem_range.mpr (by omega))
    exact hk (by simp [mul_pow, coeff_X_pow_mul', hle])
  rw [finsum_eq_sum_of_support_subset _ hs]
  apply sum_congr rfl
  intro k hk
  have hle : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
  simp [mul_pow, coeff_X_pow_mul', hle, smul_eq_mul]

/-- The finite substitution formula with factorials absorbed into integer EGF coefficients. -/
theorem jet_subst_X_mul (F D : ℚ⟦X⟧) (n : ℕ) :
    jet (F.subst (X * D)) n =
      ∑ k ∈ range (n + 1), (n.choose k : ℚ) * jet F k * jet (D ^ k) (n - k) := by
  simp only [jet, coeff_subst_X_mul, mul_sum]
  apply sum_congr rfl
  intro k hk
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
  have hf : (n.factorial : ℚ) = n.choose k * (k.factorial : ℚ) * (n - k).factorial := by
    exact_mod_cast (Nat.choose_mul_factorial_mul_factorial hkn).symm
  rw [hf]
  ring

/-- Integral EGF substitution by $xD(x)$. -/
def composition (a d : ℕ → R) (n : ℕ) : R :=
  ∑ k ∈ range (n + 1), (n.choose k : R) * a k * power d k (n - k)

lemma jet_subst_qegf (a d : ℕ → ℚ) :
    jet ((qegf a).subst (X * qegf d)) = composition a d := by
  funext n
  rw [jet_subst_X_mul]
  simp only [jet_qegf, jet_pow, composition]

lemma qegf_composition (a d : ℕ → ℚ) :
    qegf (composition a d) = (qegf a).subst (X * qegf d) := by
  apply jet_injective
  rw [jet_qegf, jet_subst_qegf]

lemma map_composition {S : Type*} [CommRing S] (φ : R →+* S) (a d : ℕ → R) :
    φ ∘ composition a d = composition (φ ∘ a) (φ ∘ d) := by
  funext n
  simp only [composition, Function.comp_apply, map_sum, map_mul, map_natCast]
  apply sum_congr rfl
  intro k hk
  rw [← map_power]
  rfl



/-- The EGF coefficients of the derivative of $xC(x)$. -/
def logDerivative (c : ℕ → R) (n : ℕ) : R := (n + 1) * c n

def expOperator (c a : ℕ → R) : ℕ → R
  | 0 => 1
  | n + 1 => product a (logDerivative c) n

lemma expOperator_causal (c : ℕ → R) : Causal.IsCausal (expOperator c) := by
  intro n a b h
  cases n with
  | zero => rfl
  | succ n =>
    apply product_congr
    · exact fun k hk => h k (by omega)
    · intro k hk; rfl

/-- Integral EGF exponential $\exp(xC(x))$, defined without division. -/
def expSequence (c : ℕ → R) : ℕ → R :=
  Causal.fixedPoint (expOperator c) 0

lemma expSequence_zero (c : ℕ → R) : expSequence c 0 = 1 := by
  exact Causal.fixedPoint_eq _ (expOperator_causal c) 0 0

lemma expSequence_succ (c : ℕ → R) (n : ℕ) :
    expSequence c (n + 1) = product (expSequence c) (logDerivative c) n := by
  exact Causal.fixedPoint_eq _ (expOperator_causal c) 0 (n + 1)

lemma expSequence_congr (a b : ℕ → R) (n : ℕ) (h : ∀ k < n, a k = b k) :
    expSequence a n = expSequence b n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => rw [expSequence_zero, expSequence_zero]
    | succ n =>
      rw [expSequence_succ, expSequence_succ]
      apply product_congr
      · intro k hk
        apply ih k (by omega)
        intro j hj
        exact h j (hj.trans (by omega))
      · intro k hk
        simp only [logDerivative]
        rw [h k (by omega)]

lemma map_expSequence {S : Type*} [CommRing S] (φ : R →+* S) (c : ℕ → R) :
    φ ∘ expSequence c = expSequence (φ ∘ c) := by
  funext n
  change φ (expSequence c n) = expSequence (φ ∘ c) n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [expSequence_zero]
    | succ n =>
      rw [expSequence_succ, expSequence_succ]
      change (φ ∘ product (expSequence c) (logDerivative c)) n = _
      rw [map_product]
      apply product_congr
      · exact fun k hk => ih k (by omega)
      · intro k hk
        simp [logDerivative, Function.comp_apply]

lemma jet_logDerivative (c : ℕ → ℚ) :
    jet (derivative ℚ (X * qegf c)) = logDerivative c := by
  funext n
  rw [jet_derivative]
  change jet (X * qegf c) (n + 1) = _
  rw [jet_X_mul_succ, jet_qegf]
  rfl

/-- Identification of the division-free exponential with the rational exponential series. -/
theorem jet_exp_X_qegf (c : ℕ → ℚ) :
    jet ((exp ℚ).subst (X * qegf c)) = expSequence c := by
  let G : ℚ⟦X⟧ := X * qegf c
  let E : ℚ⟦X⟧ := (exp ℚ).subst G
  have hG0 : G.constantCoeff = 0 := by simp [G]
  have hG : HasSubst G := HasSubst.of_constantCoeff_zero' hG0
  have hd : derivative ℚ E = E * derivative ℚ G := by
    dsimp [E]
    rw [derivative_subst hG, derivative_exp]
  have he0 : jet E 0 = 1 := by
    rw [jet_zero]
    exact (constantCoeff_subst_of_zero (exp ℚ) G hG0).trans (by simp)
  have hr (n : ℕ) : jet E (n + 1) = product (jet E) (logDerivative c) n := by
    change shift (jet E) n = _
    rw [← jet_derivative, hd, jet_product]
    change product (jet E) (jet (derivative ℚ (X * qegf c))) n = _
    rw [jet_logDerivative]
  funext n
  change jet E n = expSequence c n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => rw [he0, expSequence_zero]
    | succ n =>
      rw [hr, expSequence_succ]
      apply product_congr
      · exact fun k hk => ih k (by omega)
      · intro k hk; rfl

lemma qegf_expSequence (c : ℕ → ℚ) :
    qegf (expSequence c) = (exp ℚ).subst (X * qegf c) := by
  apply jet_injective
  rw [jet_qegf, jet_exp_X_qegf]

lemma egf_power (b : ℕ → ℤ) (k : ℕ) : egf (power b k) = egf b ^ k := by
  apply jet_injective
  rw [jet_egf, jet_pow, jet_egf, map_power]

lemma egf_composition (a d : ℕ → ℤ) :
    egf (composition a d) = (egf a).subst (X * egf d) := by
  change qegf (Int.castRingHom ℚ ∘ composition a d) =
    (qegf (Int.castRingHom ℚ ∘ a)).subst (X * qegf (Int.castRingHom ℚ ∘ d))
  rw [map_composition, qegf_composition]

lemma egf_expSequence (c : ℕ → ℤ) :
    egf (expSequence c) = (exp ℚ).subst (X * egf c) := by
  change qegf (Int.castRingHom ℚ ∘ expSequence c) =
    (exp ℚ).subst (X * qegf (Int.castRingHom ℚ ∘ c))
  rw [map_expSequence, qegf_expSequence]


lemma composition_zero (a d : ℕ → R) : composition a d 0 = a 0 := by
  simp [composition, power, unitSequence]

/-- The auxiliary source operator on integral EGF coefficients. -/
def auxiliaryOperator (r : ℕ) (b : ℕ → R) : ℕ → R :=
  composition (expSequence (power b 3)) (power b r)

lemma map_auxiliaryOperator {S : Type*} [CommRing S] (φ : R →+* S) (r : ℕ)
    (b : ℕ → R) :
    φ ∘ auxiliaryOperator r b = auxiliaryOperator r (φ ∘ b) := by
  simp only [auxiliaryOperator, map_composition, map_expSequence, map_power]

/-- A coefficient of the source operator uses only strictly earlier input coefficients. -/
theorem auxiliaryOperator_causal (r : ℕ) : Causal.IsCausal (auxiliaryOperator r (R := R)) := by
  intro n a b h
  unfold auxiliaryOperator composition
  apply sum_congr rfl
  intro k hk
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
  cases k with
  | zero => simp [power, expSequence_zero]
  | succ k =>
    have ho : expSequence (power a 3) (k + 1) = expSequence (power b 3) (k + 1) := by
      apply expSequence_congr
      intro i hi
      apply power_congr
      intro j hj
      exact h j (lt_of_le_of_lt hj (lt_of_lt_of_le hi hkn))
    have hi : power (power a r) (k + 1) (n - (k + 1)) =
        power (power b r) (k + 1) (n - (k + 1)) := by
      apply power_congr
      intro i hi
      apply power_congr
      intro j hj
      apply h
      omega
    rw [ho, hi]

lemma jet_subst_X (F D : ℚ⟦X⟧) :
    jet (F.subst (X * D)) = composition (jet F) (jet D) := by
  simpa only [qegf_jet] using jet_subst_qegf (jet F) (jet D)

lemma jet_exp_X_power (B : ℚ⟦X⟧) (k : ℕ) :
    jet ((exp ℚ).subst (X * B ^ k)) = expSequence (power (jet B) k) := by
  have h := jet_exp_X_qegf (jet (B ^ k))
  rw [qegf_jet, jet_pow] at h
  exact h
end Hurwitz

namespace Source
open Hurwitz PowerSeries

/-- The unique integral auxiliary fixed point for the complementary-exponent family. -/
def b (r : ℕ) : ℕ → ℤ := Causal.fixedPoint (auxiliaryOperator r) 0

lemma b_fixed (r : ℕ) : auxiliaryOperator r (b r) = b r := by
  funext n
  exact (Causal.fixedPoint_eq _ (auxiliaryOperator_causal r) 0 n).symm

/-- EGF coefficients of the normalized source solution. -/
def a (r : ℕ) : ℕ → ℤ := expSequence (power (b r) 3)

lemma b_zero (r : ℕ) : b r 0 = 1 := by
  rw [← congrFun (b_fixed r) 0]
  exact (composition_zero _ _).trans (expSequence_zero _)

lemma generating_function (r : ℕ) :
    egf (a r) = (exp ℚ).subst (X * egf (b r) ^ 3) := by
  rw [a, egf_expSequence, egf_power]

lemma auxiliary_function (r : ℕ) :
    egf (b r) = (egf (a r)).subst (X * egf (b r) ^ r) := by
  conv_lhs => rw [← b_fixed r]
  change egf (composition (a r) (power (b r) r)) = _
  rw [egf_composition, egf_power]

/-- The constructed integer EGF satisfies the original source equation. -/
theorem original (r s : ℕ) (hrs : r + s = 3) : Original r s (egf (a r)) := by
  apply auxiliary_original (B := egf (b r))
  · simpa [← jet_zero, jet_egf, Function.comp_apply] using
      congrArg (Int.castRingHom ℚ) (b_zero r)
  · exact auxiliary_function r
  · rw [hrs]
    exact generating_function r

/-- Every normalized rational source solution is the constructed integer EGF. -/
theorem eq_egf {r s : ℕ} (hrs : r + s = 3) {F : ℚ⟦X⟧} (hF : Original r s F) :
    F = egf (a r) := by
  obtain ⟨B, _, hB, hA⟩ := original_auxiliary hF
  have hAj : jet F = expSequence (power (jet B) 3) := by
    rw [hA, hrs, jet_exp_X_power]
  have hBj : auxiliaryOperator r (jet B) = jet B := by
    have he := congrArg jet hB
    rw [jet_subst_X, jet_pow, hAj] at he
    exact he.symm
  have hm : auxiliaryOperator r (Int.castRingHom ℚ ∘ b r) = Int.castRingHom ℚ ∘ b r := by
    rw [← map_auxiliaryOperator, b_fixed]
  have heq : jet B = Int.castRingHom ℚ ∘ b r :=
    (Causal.exists_unique_fixed_point (auxiliaryOperator r) (auxiliaryOperator_causal r)
      (0 : ℕ → ℚ)).unique hBj hm
  apply jet_injective
  rw [hAj, jet_egf, heq, ← map_power, ← map_expSequence]
  rfl

end Source

lemma isGeneratingSequence_iff (c : ℕ → ℤ) :
    IsGeneratingSequence c ↔ Original 2 1 (egf c) := by
  simp only [IsGeneratingSequence, Original, pow_one]

lemma egf_injective : Function.Injective egf := fun c d h => by
  funext n
  have he := congrFun (congrArg Hurwitz.jet h) n
  simp only [Hurwitz.jet_egf, Function.comp_apply, Int.coe_castRingHom] at he
  exact_mod_cast he

lemma constructed_spec : IsGeneratingSequence (Source.a 2) :=
  (isGeneratingSequence_iff _).2 (Source.original 2 1 rfl)

theorem exists_unique_sequence_proof : ∃! c : ℕ → ℤ, IsGeneratingSequence c := by
  refine ⟨Source.a 2, constructed_spec, fun c hc => egf_injective ?_⟩
  exact Source.eq_egf (r := 2) (s := 1) rfl ((isGeneratingSequence_iff c).mp hc)

lemma a_eq_constructed : OeisA368630.a = Source.a 2 :=
  exists_unique_sequence_proof.unique
    (Classical.epsilon_spec exists_unique_sequence_proof.exists) constructed_spec

open Hurwitz

lemma primary_b_1 : Source.b 2 1 = 1 := by
  have h := congrFun (Source.b_fixed 2) 1
  norm_num [auxiliaryOperator, composition, Finset.sum_range_succ, power, product,
    shift, logDerivative, unitSequence, expSequence_zero, expSequence_succ,
    Source.b_zero] at h
  exact h.symm

lemma primary_b_2 : Source.b 2 2 = 11 := by
  have h := congrFun (Source.b_fixed 2) 2
  norm_num [auxiliaryOperator, composition, Finset.sum_range_succ, power, product,
    shift, logDerivative, unitSequence, expSequence_zero, expSequence_succ,
    Source.b_zero, primary_b_1] at h
  exact h.symm

lemma primary_b_3 : Source.b 2 3 = 292 := by
  have h := congrFun (Source.b_fixed 2) 3
  norm_num [auxiliaryOperator, composition, Finset.sum_range_succ, power, product,
    shift, logDerivative, unitSequence, expSequence_zero, expSequence_succ,
    Source.b_zero, primary_b_1, primary_b_2] at h
  exact h.symm

lemma constructed_a_4 : Source.a 2 4 = 4933 := by
  norm_num [Source.a, expSequence_succ, expSequence_zero, logDerivative, power,
    product, shift, unitSequence, Source.b_zero, primary_b_1, primary_b_2, primary_b_3]

end OMA.A368630

theorem OMA.solution : type_of% @OeisA368630.a_4 := by
  rw [OMA.A368630.a_eq_constructed]
  exact OMA.A368630.constructed_a_4
