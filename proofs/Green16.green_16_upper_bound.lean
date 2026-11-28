import FormalConjectures.GreensOpenProblems.«16»

/-!
# Green's Open Problem 16: the Schoen–Sisask upper bound

We prove `Green16.green_16_upper_bound`: a subset of `{1, …, N}` with no solution to
`x + 3y = 2z + 2w` in distinct elements has size `O(N exp(-c (log N)^(1/7)))`.

The proof follows T. Schoen and O. Sisask, *Roth's theorem for four variables and additive
structures in sums of sparse sets*, Forum Math. Sigma 4 (2016), adapted to the equation
`x + 3y = 2z + 2w` with distinct variables:

* Bohr sets in `ZMod p`: size, doubling, regular radii, dilations;
* the Croot–Sisask almost-periodicity lemma (via exponential moments) and its `L^∞` form;
* the Fourier step and the local Chang lemma (Riesz products);
* the density increment on Bohr sets (large/small sumset dichotomy) and its iteration;
* the transfer from `{1, …, N}` to `ZMod p` and the final numerics.
-/

section ModBohr

/- # Green 16: Bohr sets in `ZMod p` -/

open Finset

namespace G16

variable {p : ℕ} [Fact p.Prime]

/-- The standard additive character of `ZMod p`. -/
noncomputable def e (x : ZMod p) : ℂ := ZMod.stdAddChar x

lemma e_add (x y : ZMod p) : e (x + y) = e x * e y := AddChar.map_add_eq_mul _ _ _

lemma e_zero : e (0 : ZMod p) = 1 := AddChar.map_zero_eq_one _

lemma norm_e (x : ZMod p) : ‖e x‖ = 1 := AddChar.norm_apply _ _

lemma e_neg (x : ZMod p) : e (-x) = starRingEnd ℂ (e x) := AddChar.map_neg_eq_conj _ _

lemma e_ne_zero (x : ZMod p) : e x ≠ 0 := by
  intro h
  have := norm_e x
  rw [h, norm_zero] at this
  exact zero_ne_one this

lemma e_sub (x y : ZMod p) : e (x - y) = e x * starRingEnd ℂ (e y) := by
  rw [sub_eq_add_neg, e_add, e_neg]

lemma e_nsmul (k : ℕ) (x : ZMod p) : e ((k : ZMod p) * x) = e x ^ k := by
  induction k with
  | zero => simp [e_zero]
  | succ k ih =>
    rw [Nat.cast_succ, add_mul, one_mul, e_add, ih, pow_succ]

lemma sum_e_mul (a : ZMod p) : ∑ x : ZMod p, e (a * x) = if a = 0 then (p : ℂ) else 0 := by
  have h := AddChar.sum_mulShift (R := ZMod p) (R' := ℂ) a (ZMod.isPrimitive_stdAddChar p)
  simp only [ZMod.card] at h
  have h2 : ∑ x : ZMod p, e (a * x) = ∑ x : ZMod p, ZMod.stdAddChar (x * a) :=
    Finset.sum_congr rfl fun x _ => by rw [mul_comm]; rfl
  rw [h2, h]
  split_ifs <;> simp

/-- `‖1 - e (x + y)‖ ≤ ‖1 - e x‖ + ‖1 - e y‖`. -/
lemma norm_one_sub_e_add (x y : ZMod p) : ‖1 - e (x + y)‖ ≤ ‖1 - e x‖ + ‖1 - e y‖ := by
  have h : 1 - e (x + y) = (1 - e x) + e x * (1 - e y) := by rw [e_add]; ring
  rw [h]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_e, one_mul]

lemma norm_one_sub_e_neg (x : ZMod p) : ‖1 - e (-x)‖ = ‖1 - e x‖ := by
  rw [e_neg]
  have : (1 : ℂ) - starRingEnd ℂ (e x) = starRingEnd ℂ (1 - e x) := by simp
  rw [this, RCLike.norm_conj]

lemma norm_one_sub_e_sub (x y : ZMod p) : ‖1 - e (x - y)‖ = ‖e x - e y‖ := by
  have h0 : e y * e (x - y) = e x := by rw [← e_add]; congr 1; ring
  have h : e x - e y = e y * (e (x - y) - 1) := by
    rw [mul_sub, h0, mul_one]
  rw [h, norm_mul, norm_e, one_mul, norm_sub_rev]

open Classical in
/-- The Bohr set with frequency set `R` and radius `ρ`. -/
noncomputable def bohr (R : Finset (ZMod p)) (ρ : ℝ) : Finset (ZMod p) :=
  univ.filter fun x => ∀ a ∈ R, ‖1 - e (a * x)‖ ≤ ρ

lemma mem_bohr {R : Finset (ZMod p)} {ρ : ℝ} {x : ZMod p} :
    x ∈ bohr R ρ ↔ ∀ a ∈ R, ‖1 - e (a * x)‖ ≤ ρ := by
  simp [bohr]

lemma zero_mem_bohr {R : Finset (ZMod p)} {ρ : ℝ} (hρ : 0 ≤ ρ) : (0 : ZMod p) ∈ bohr R ρ := by
  rw [mem_bohr]; intro a _; simp [e_zero, hρ]

lemma neg_mem_bohr {R : Finset (ZMod p)} {ρ : ℝ} {x : ZMod p} (hx : x ∈ bohr R ρ) :
    -x ∈ bohr R ρ := by
  rw [mem_bohr] at hx ⊢
  intro a ha
  rw [mul_neg, norm_one_sub_e_neg]
  exact hx a ha

lemma add_mem_bohr {R : Finset (ZMod p)} {ρ₁ ρ₂ : ℝ} {x y : ZMod p} (hx : x ∈ bohr R ρ₁)
    (hy : y ∈ bohr R ρ₂) : x + y ∈ bohr R (ρ₁ + ρ₂) := by
  rw [mem_bohr] at hx hy ⊢
  intro a ha
  rw [mul_add]
  exact (norm_one_sub_e_add _ _).trans (add_le_add (hx a ha) (hy a ha))

lemma sub_mem_bohr {R : Finset (ZMod p)} {ρ₁ ρ₂ : ℝ} {x y : ZMod p} (hx : x ∈ bohr R ρ₁)
    (hy : y ∈ bohr R ρ₂) : x - y ∈ bohr R (ρ₁ + ρ₂) := by
  rw [sub_eq_add_neg]; exact add_mem_bohr hx (neg_mem_bohr hy)

lemma bohr_mono {R : Finset (ZMod p)} {ρ₁ ρ₂ : ℝ} (h : ρ₁ ≤ ρ₂) : bohr R ρ₁ ⊆ bohr R ρ₂ := by
  intro x hx
  rw [mem_bohr] at hx ⊢
  exact fun a ha => (hx a ha).trans h

lemma bohr_anti {R R' : Finset (ZMod p)} {ρ : ℝ} (h : R ⊆ R') : bohr R' ρ ⊆ bohr R ρ := by
  intro x hx
  rw [mem_bohr] at hx ⊢
  exact fun a ha => hx a (h ha)

lemma card_bohr_mono {R : Finset (ZMod p)} {ρ₁ ρ₂ : ℝ} (h : ρ₁ ≤ ρ₂) :
    (bohr R ρ₁).card ≤ (bohr R ρ₂).card := card_le_card (bohr_mono h)

lemma card_bohr_pos {R : Finset (ZMod p)} {ρ : ℝ} (hρ : 0 ≤ ρ) : 0 < (bohr R ρ).card :=
  card_pos.2 ⟨0, zero_mem_bohr hρ⟩

lemma mem_bohr_union {R R' : Finset (ZMod p)} [DecidableEq (ZMod p)] {ρ : ℝ} {x : ZMod p} :
    x ∈ bohr (R ∪ R') ρ ↔ x ∈ bohr R ρ ∧ x ∈ bohr R' ρ := by
  simp only [mem_bohr, mem_union]
  constructor
  · intro h; exact ⟨fun a ha => h a (Or.inl ha), fun a ha => h a (Or.inr ha)⟩
  · rintro ⟨h1, h2⟩ a (ha | ha)
    · exact h1 a ha
    · exact h2 a ha

/-- If the characters of `x` and `y` are close then `x - y` is in the Bohr set. -/
lemma sub_mem_bohr_of_close {R : Finset (ZMod p)} {ρ : ℝ} {x y : ZMod p}
    (h : ∀ a ∈ R, ‖e (a * x) - e (a * y)‖ ≤ ρ) : x - y ∈ bohr R ρ := by
  rw [mem_bohr]
  intro a ha
  rw [mul_sub, norm_one_sub_e_sub]
  exact h a ha

/-- Multiples: `k x ∈ B_{kρ}`. -/
lemma nsmul_mem_bohr {R : Finset (ZMod p)} {ρ : ℝ} {x : ZMod p} (hx : x ∈ bohr R ρ)
    (k : ℕ) : (k : ZMod p) * x ∈ bohr R (k * ρ) := by
  induction k with
  | zero => simpa using zero_mem_bohr (R := R) (le_refl (0 : ℝ))
  | succ k ih =>
    have : ((k + 1 : ℕ) : ZMod p) * x = (k : ZMod p) * x + x := by push_cast; ring
    rw [this]
    have h2 : ((k + 1 : ℕ) : ℝ) * ρ = k * ρ + ρ := by push_cast; ring
    rw [h2]
    exact add_mem_bohr ih hx

end G16

end ModBohr

section ModBohr2

/- # Green 16: size, doubling and regularity of Bohr sets -/

open Finset

namespace G16

variable {p : ℕ} [Fact p.Prime]

lemma card_Icc_floor_le {u v : ℝ} (h : u ≤ v) : ((Icc ⌊u⌋ ⌊v⌋).card : ℝ) ≤ v - u + 2 := by
  rw [Int.card_Icc]
  have h1 : ⌊u⌋ ≤ ⌊v⌋ := Int.floor_le_floor h
  have h2 : (0 : ℤ) ≤ ⌊v⌋ + 1 - ⌊u⌋ := by omega
  have h3 : (((⌊v⌋ + 1 - ⌊u⌋).toNat : ℤ) : ℝ) = ((⌊v⌋ + 1 - ⌊u⌋ : ℤ) : ℝ) := by
    rw [Int.toNat_of_nonneg h2]
  have h4 : (((⌊v⌋ + 1 - ⌊u⌋).toNat : ℕ) : ℝ) = (((⌊v⌋ + 1 - ⌊u⌋).toNat : ℤ) : ℝ) := by
    norm_cast
  rw [h4, h3]
  push_cast
  have h5 := Int.floor_le v
  have h6 := Int.lt_floor_add_one u
  linarith

/-- Cell counting: a set whose character values fall into few grid cells is covered by few
translates of a Bohr set. -/
lemma card_le_card_bohr_mul_cells (R : Finset (ZMod p)) {ρ : ℝ} (hρ : 0 < ρ)
    (X : Finset (ZMod p)) (I₁ I₂ : Finset ℤ)
    (hI : ∀ x ∈ X, ∀ a ∈ R,
      ⌊(e (a * x)).re / (ρ / 2)⌋ ∈ I₁ ∧ ⌊(e (a * x)).im / (ρ / 2)⌋ ∈ I₂) :
    X.card ≤ (bohr R ρ).card * (I₁.card * I₂.card) ^ R.card := by
  classical
  let f : ZMod p → (R → ℤ × ℤ) := fun x a =>
    (⌊(e ((a : ZMod p) * x)).re / (ρ / 2)⌋, ⌊(e ((a : ZMod p) * x)).im / (ρ / 2)⌋)
  have hmaps : ∀ x ∈ X, f x ∈ Fintype.piFinset (fun _ : R => I₁ ×ˢ I₂) := by
    intro x hx
    rw [Fintype.mem_piFinset]
    intro a
    exact mem_product.2 (hI x hx a a.2)
  have hfib : ∀ b ∈ Fintype.piFinset (fun _ : R => I₁ ×ˢ I₂),
      (X.filter fun x => f x = b).card ≤ (bohr R ρ).card := by
    intro b _
    rcases (X.filter fun x => f x = b).eq_empty_or_nonempty with h | ⟨y, hy⟩
    · simp [h]
    · refine card_le_card_of_injOn (fun x => x - y) ?_ ?_
      · intro x hx
        have hx' := (mem_filter.1 (mem_coe.1 hx)).2
        have hy' := (mem_filter.1 hy).2
        refine mem_coe.2 (sub_mem_bohr_of_close fun a ha => ?_)
        have h1 := congrFun hx' ⟨a, ha⟩
        have h2 := congrFun hy' ⟨a, ha⟩
        have h3 : f x ⟨a, ha⟩ = f y ⟨a, ha⟩ := h1.trans h2.symm
        have hre : ⌊(e (a * x)).re / (ρ / 2)⌋ = ⌊(e (a * y)).re / (ρ / 2)⌋ :=
          congrArg Prod.fst h3
        have him : ⌊(e (a * x)).im / (ρ / 2)⌋ = ⌊(e (a * y)).im / (ρ / 2)⌋ :=
          congrArg Prod.snd h3
        have hre' := Int.abs_sub_lt_one_of_floor_eq_floor hre
        have him' := Int.abs_sub_lt_one_of_floor_eq_floor him
        have hρ2 : 0 < ρ / 2 := by positivity
        rw [← sub_div, abs_div, abs_of_pos hρ2, div_lt_one hρ2] at hre' him'
        have := Complex.norm_le_abs_re_add_abs_im (e (a * x) - e (a * y))
        rw [Complex.sub_re, Complex.sub_im] at this
        linarith
      · intro x _ x' _ h
        simpa using h
  have key := card_le_mul_card_image_of_maps_to hmaps _ hfib
  rw [Fintype.card_piFinset] at key
  simpa [Finset.prod_const, card_product] using key

/-- Size bound for Bohr sets. -/
lemma card_univ_le_bohr (R : Finset (ZMod p)) {ρ : ℝ} (hρ : 0 < ρ) (hρ2 : ρ ≤ 2) :
    (p : ℝ) ≤ (bohr R ρ).card * (8 / ρ) ^ (2 * R.card) := by
  classical
  have hs : (0 : ℝ) < ρ / 2 := by positivity
  set I : Finset ℤ := Icc ⌊(-1 : ℝ) / (ρ / 2)⌋ ⌊(1 : ℝ) / (ρ / 2)⌋ with hI
  have hmem : ∀ u : ℝ, |u| ≤ 1 → ⌊u / (ρ / 2)⌋ ∈ I := by
    intro u hu
    rw [hI, mem_Icc]
    have h1 := abs_le.1 hu
    exact ⟨Int.floor_le_floor (div_le_div_of_nonneg_right h1.1 hs.le),
      Int.floor_le_floor (div_le_div_of_nonneg_right h1.2 hs.le)⟩
  have key := card_le_card_bohr_mul_cells R hρ (univ : Finset (ZMod p)) I I (by
    intro x _ a _
    have hn := norm_e (a * x)
    exact ⟨hmem _ (hn ▸ Complex.abs_re_le_norm _), hmem _ (hn ▸ Complex.abs_im_le_norm _)⟩)
  rw [card_univ, ZMod.card] at key
  have hIc : (I.card : ℝ) ≤ 8 / ρ := by
    have h1 : (-1 : ℝ) / (ρ / 2) ≤ 1 / (ρ / 2) :=
      div_le_div_of_nonneg_right (by norm_num) hs.le
    have h2 := card_Icc_floor_le h1
    have h3 : (1 : ℝ) / (ρ / 2) - -1 / (ρ / 2) + 2 = 4 / ρ + 2 := by field_simp; ring
    have h4 : (2 : ℝ) ≤ 4 / ρ := by rw [le_div_iff₀ hρ]; linarith
    have h5 : (8 : ℝ) / ρ = 4 / ρ + 4 / ρ := by ring
    rw [hI] at *
    linarith
  have key' : (p : ℝ) ≤ ((bohr R ρ).card : ℝ) * ((I.card : ℝ) * I.card) ^ R.card := by
    exact_mod_cast key
  refine key'.trans ?_
  have hIc0 : (0 : ℝ) ≤ I.card := Nat.cast_nonneg _
  have h6 : ((I.card : ℝ) * I.card) ^ R.card ≤ (8 / ρ) ^ (2 * R.card) := by
    rw [pow_mul, sq]
    exact pow_le_pow_left₀ (by positivity) (mul_le_mul hIc hIc hIc0 (hIc0.trans hIc)) _
  exact mul_le_mul_of_nonneg_left h6 (Nat.cast_nonneg _)

/-- Doubling bound for Bohr sets. -/
lemma card_bohr_two_mul_le (R : Finset (ZMod p)) {ρ : ℝ} (hρ : 0 < ρ) :
    (bohr R (2 * ρ)).card ≤ (bohr R ρ).card * 100 ^ R.card := by
  classical
  have hs : (0 : ℝ) < ρ / 2 := by positivity
  set I₁ : Finset ℤ := Icc ⌊(1 - 2 * ρ) / (ρ / 2)⌋ ⌊(1 + 2 * ρ) / (ρ / 2)⌋ with hI₁
  set I₂ : Finset ℤ := Icc ⌊(-(2 * ρ)) / (ρ / 2)⌋ ⌊(2 * ρ) / (ρ / 2)⌋ with hI₂
  have key := card_le_card_bohr_mul_cells R hρ (bohr R (2 * ρ)) I₁ I₂ (by
    intro x hx a ha
    have hx' := mem_bohr.1 hx a ha
    have hre : |(1 - e (a * x)).re| ≤ 2 * ρ := (Complex.abs_re_le_norm _).trans hx'
    have him : |(1 - e (a * x)).im| ≤ 2 * ρ := (Complex.abs_im_le_norm _).trans hx'
    rw [Complex.sub_re, Complex.one_re] at hre
    rw [Complex.sub_im, Complex.one_im, zero_sub, abs_neg] at him
    have hre' := abs_le.1 hre
    have him' := abs_le.1 him
    refine ⟨?_, ?_⟩
    · rw [hI₁, mem_Icc]
      exact ⟨Int.floor_le_floor (div_le_div_of_nonneg_right (by linarith) hs.le),
        Int.floor_le_floor (div_le_div_of_nonneg_right (by linarith) hs.le)⟩
    · rw [hI₂, mem_Icc]
      exact ⟨Int.floor_le_floor (div_le_div_of_nonneg_right (by linarith) hs.le),
        Int.floor_le_floor (div_le_div_of_nonneg_right (by linarith) hs.le)⟩)
  have h1 : I₁.card ≤ 10 := by
    have h := card_Icc_floor_le (u := (1 - 2 * ρ) / (ρ / 2)) (v := (1 + 2 * ρ) / (ρ / 2))
      (div_le_div_of_nonneg_right (by linarith) hs.le)
    have h3 : (1 + 2 * ρ) / (ρ / 2) - (1 - 2 * ρ) / (ρ / 2) + 2 = 10 := by field_simp; ring
    rw [h3] at h
    exact_mod_cast h
  have h2 : I₂.card ≤ 10 := by
    have h := card_Icc_floor_le (u := (-(2 * ρ)) / (ρ / 2)) (v := (2 * ρ) / (ρ / 2))
      (div_le_div_of_nonneg_right (by linarith) hs.le)
    have h3 : (2 * ρ) / (ρ / 2) - (-(2 * ρ)) / (ρ / 2) + 2 = 10 := by field_simp; ring
    rw [h3] at h
    exact_mod_cast h
  refine key.trans (Nat.mul_le_mul_left _ ?_)
  calc (I₁.card * I₂.card) ^ R.card ≤ (10 * 10) ^ R.card :=
        Nat.pow_le_pow_left (Nat.mul_le_mul h1 h2) _
    _ = 100 ^ R.card := by norm_num

/-- Regularity of a Bohr set at scale `κ` with tolerance `η`. -/
def Reg (R : Finset (ZMod p)) (r κ η : ℝ) : Prop :=
  ((bohr R ((1 + κ) * r)).card : ℝ) ≤ (1 + η) * (bohr R ((1 - κ) * r)).card

lemma Reg.card_add_le_sub {R : Finset (ZMod p)} {r κ η : ℝ} (h : Reg R r κ η) (hη : 0 ≤ η)
    {s : ℝ} (hs : s ≤ κ * r) :
    ((bohr R (r + s)).card : ℝ) ≤ (1 + η) * (bohr R (r - s)).card := by
  have h1 : ((bohr R (r + s)).card : ℝ) ≤ (bohr R ((1 + κ) * r)).card := by
    exact_mod_cast card_bohr_mono (by linarith)
  have h2 : ((bohr R ((1 - κ) * r)).card : ℝ) ≤ (bohr R (r - s)).card := by
    exact_mod_cast card_bohr_mono (by linarith)
  exact h1.trans (h.trans (mul_le_mul_of_nonneg_left h2 (by linarith)))

lemma Reg.card_add_le {R : Finset (ZMod p)} {r κ η : ℝ} (h : Reg R r κ η) (hη : 0 ≤ η)
    {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ κ * r) :
    ((bohr R (r + s)).card : ℝ) ≤ (1 + η) * (bohr R r).card := by
  have h2 : ((bohr R (r - s)).card : ℝ) ≤ (bohr R r).card := by
    exact_mod_cast card_bohr_mono (by linarith)
  exact (h.card_add_le_sub hη hs).trans (mul_le_mul_of_nonneg_left h2 (by linarith))

lemma Reg.card_le_sub {R : Finset (ZMod p)} {r κ η : ℝ} (h : Reg R r κ η) (hη : 0 ≤ η)
    {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ κ * r) :
    ((bohr R r).card : ℝ) ≤ (1 + η) * (bohr R (r - s)).card := by
  have h1 : ((bohr R r).card : ℝ) ≤ (bohr R (r + s)).card := by
    exact_mod_cast card_bohr_mono (by linarith)
  exact h1.trans (h.card_add_le_sub hη hs)

lemma exp_half_le_two : Real.exp (1 / 2) ≤ 2 := by
  have h1 : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  have h2 := Real.exp_one_lt_d9
  have h3 := Real.exp_pos (1 / 2)
  nlinarith

/-- Existence of a regular radius. -/
lemma exists_reg (R : Finset (ZMod p)) (D : ℕ) (hRD : R.card ≤ D) (hD : 1 ≤ D) {η : ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1) {r : ℝ} (hr : 0 < r) :
    ∃ r', r / 2 ≤ r' ∧ r' ≤ r ∧ Reg R r' (η / (84 * D)) η := by
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  set κ : ℝ := η / (84 * D) with hκ
  have hκ0 : 0 < κ := by positivity
  have hκ1 : κ ≤ 1 / 84 := by
    rw [hκ, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  set lam : ℝ := (1 + κ) / (1 - κ) with hlam
  have h1κ : 0 < 1 - κ := by linarith
  have hlam1 : 1 ≤ lam := by
    rw [hlam, le_div_iff₀ h1κ]; linarith
  have hlam3 : lam ≤ 1 + 3 * κ := by
    rw [hlam, div_le_iff₀ h1κ]; nlinarith
  set m : ℕ := ⌈1 / η⌉₊ with hm
  have hm1 : 1 / η ≤ m := Nat.le_ceil _
  have hm2 : (m : ℝ) ≤ 1 / η + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  set n : ℕ := 7 * D * m with hn
  -- `lam ^ n ≤ 2`
  have hlamn : lam ^ n ≤ 2 := by
    have h1 : lam ^ n ≤ (Real.exp (3 * κ)) ^ n :=
      pow_le_pow_left₀ (by linarith) (hlam3.trans (by linarith [Real.add_one_le_exp (3 * κ)])) _
    rw [← Real.exp_nat_mul] at h1
    refine h1.trans ((Real.exp_le_exp.2 ?_).trans exp_half_le_two)
    have h2 : (n : ℝ) * (3 * κ) = η * m / 4 := by
      rw [hn, hκ]; push_cast; field_simp; ring
    rw [h2]
    have h3 : η * m ≤ 1 + η := by
      calc η * m ≤ η * (1 / η + 1) := mul_le_mul_of_nonneg_left hm2 hη.le
        _ = 1 + η := by field_simp
    linarith
  -- the counting function
  set N : ℕ → ℝ := fun i => ((bohr R (r / 2 * lam ^ i)).card : ℝ) with hN
  have hN0 : 0 < N 0 := by
    simp only [hN]
    exact_mod_cast card_bohr_pos (by positivity)
  have hex : ∃ i < n, N (i + 1) ≤ (1 + η) * N i := by
    by_contra hcon
    push Not at hcon
    have hind : ∀ i ≤ n, (1 + η) ^ i * N 0 ≤ N i := by
      intro i
      induction i with
      | zero => intro _; simp
      | succ i ih =>
        intro hi
        have h1 := ih (Nat.le_of_succ_le hi)
        have h2 := hcon i (Nat.lt_of_succ_le hi)
        calc (1 + η) ^ (i + 1) * N 0 = (1 + η) * ((1 + η) ^ i * N 0) := by ring
          _ ≤ (1 + η) * N i := mul_le_mul_of_nonneg_left h1 (by linarith)
          _ ≤ N (i + 1) := h2.le
    have h1 := hind n le_rfl
    have h2 : N n ≤ N 0 * (100 : ℝ) ^ D := by
      have h3 : ((bohr R (r / 2 * lam ^ n)).card : ℝ) ≤ (bohr R (2 * (r / 2))).card := by
        exact_mod_cast card_bohr_mono (by nlinarith)
      have h4 : ((bohr R (2 * (r / 2))).card : ℝ) ≤ (bohr R (r / 2)).card * (100 : ℝ) ^ R.card := by
        exact_mod_cast card_bohr_two_mul_le R (by positivity : (0 : ℝ) < r / 2)
      have h5 : (100 : ℝ) ^ R.card ≤ (100 : ℝ) ^ D := pow_le_pow_right₀ (by norm_num) hRD
      simp only [hN, pow_zero, mul_one]
      exact h3.trans (h4.trans (mul_le_mul_of_nonneg_left h5 (Nat.cast_nonneg _)))
    have h6 : (128 : ℝ) ^ D ≤ (1 + η) ^ n := by
      have h7 : (2 : ℝ) ≤ (1 + η) ^ m := by
        have h8 := one_add_mul_le_pow (a := η) (by linarith) m
        have h9 : 1 ≤ (m : ℝ) * η := by
          calc (1 : ℝ) = 1 / η * η := by field_simp
            _ ≤ m * η := mul_le_mul_of_nonneg_right hm1 hη.le
        linarith
      calc (128 : ℝ) ^ D = (2 ^ 7) ^ D := by norm_num
        _ = 2 ^ (7 * D) := by rw [pow_mul]
        _ ≤ ((1 + η) ^ m) ^ (7 * D) := pow_le_pow_left₀ (by norm_num) h7 _
        _ = (1 + η) ^ n := by rw [← pow_mul, hn]; ring_nf
    have h10 : (128 : ℝ) ^ D * N 0 ≤ (100 : ℝ) ^ D * N 0 := by
      calc (128 : ℝ) ^ D * N 0 ≤ (1 + η) ^ n * N 0 := mul_le_mul_of_nonneg_right h6 hN0.le
        _ ≤ N n := h1
        _ ≤ N 0 * (100 : ℝ) ^ D := h2
        _ = (100 : ℝ) ^ D * N 0 := mul_comm _ _
    have h11 : (128 : ℝ) ^ D ≤ (100 : ℝ) ^ D := le_of_mul_le_mul_right h10 hN0
    have h12 : (100 : ℝ) ^ D < (128 : ℝ) ^ D :=
      pow_lt_pow_left₀ (by norm_num) (by norm_num) (by omega)
    linarith
  obtain ⟨i, hi, hNi⟩ := hex
  have hlami : 1 ≤ lam ^ i := one_le_pow₀ hlam1
  have hlami2 : lam ^ (i + 1) ≤ 2 :=
    (pow_le_pow_right₀ hlam1 (Nat.succ_le_of_lt hi)).trans hlamn
  refine ⟨r / 2 * lam ^ i / (1 - κ), ?_, ?_, ?_⟩
  · rw [le_div_iff₀ h1κ]; nlinarith
  · have h1 : r / 2 * lam ^ i / (1 - κ) = r / 2 * lam ^ (i + 1) / (1 + κ) := by
      rw [pow_succ, hlam]; field_simp
    rw [h1, div_le_iff₀ (by linarith)]
    nlinarith
  · unfold Reg
    have h1 : (1 + κ) * (r / 2 * lam ^ i / (1 - κ)) = r / 2 * lam ^ (i + 1) := by
      rw [pow_succ, hlam]; field_simp
    have h2 : (1 - κ) * (r / 2 * lam ^ i / (1 - κ)) = r / 2 * lam ^ i := by
      field_simp
    rw [h1, h2]
    exact hNi

end G16

end ModBohr2

section ModBohr3

/- # Green 16: dilation, separation and non-degeneracy of Bohr sets -/

open Finset

namespace G16

variable {p : ℕ} [Fact p.Prime]

/-- Dilate a frequency set. -/
def dil (c : ZMod p) (R : Finset (ZMod p)) : Finset (ZMod p) := R.image fun a => a * c

lemma card_dil_le (c : ZMod p) (R : Finset (ZMod p)) : (dil c R).card ≤ R.card :=
  card_image_le

lemma mem_bohr_dil {c : ZMod p} {R : Finset (ZMod p)} {ρ : ℝ} {x : ZMod p} :
    x ∈ bohr (dil c R) ρ ↔ c * x ∈ bohr R ρ := by
  simp only [mem_bohr, dil, mem_image, forall_exists_index, and_imp]
  constructor
  · intro h a ha
    have := h (a * c) a ha rfl
    rwa [mul_assoc] at this
  · rintro h _ a ha rfl
    rw [mul_assoc]
    exact h a ha

lemma image_mul_bohr (R : Finset (ZMod p)) (ρ : ℝ) {c : ZMod p} (hc : c ≠ 0) :
    (bohr R ρ).image (fun x => c * x) = bohr (dil c⁻¹ R) ρ := by
  ext x
  rw [mem_image, mem_bohr_dil]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rwa [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  · intro h
    exact ⟨c⁻¹ * x, h, by rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]⟩

lemma card_bohr_dil (R : Finset (ZMod p)) (ρ : ℝ) {c : ZMod p} (hc : c ≠ 0) :
    (bohr (dil c R) ρ).card = (bohr R ρ).card := by
  have h := image_mul_bohr R ρ (inv_ne_zero hc)
  rw [inv_inv] at h
  rw [← h, card_image_of_injective _ (mul_right_injective₀ (inv_ne_zero hc))]

lemma reg_dil {R : Finset (ZMod p)} {r κ η : ℝ} {c : ZMod p} (hc : c ≠ 0) :
    Reg (dil c R) r κ η ↔ Reg R r κ η := by
  unfold Reg
  rw [card_bohr_dil R _ hc, card_bohr_dil R _ hc]

lemma exists_ne_zero_dil {R : Finset (ZMod p)} {c : ZMod p} (hc : c ≠ 0)
    (h : ∃ a ∈ R, a ≠ 0) : ∃ a ∈ dil c R, a ≠ 0 := by
  obtain ⟨a, ha, ha0⟩ := h
  exact ⟨a * c, mem_image_of_mem _ ha, mul_ne_zero ha0 hc⟩

/-- `‖1 - z ^ j‖ ≤ j ‖1 - z‖` on the unit circle. -/
lemma norm_one_sub_pow_le {z : ℂ} (hz : ‖z‖ = 1) (j : ℕ) : ‖1 - z ^ j‖ ≤ j * ‖1 - z‖ := by
  rw [← mul_neg_geom_sum, norm_mul, mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  refine (norm_sum_le _ _).trans ?_
  simp [norm_pow, hz]

/-- Small multiples do not come back closer to `1`. -/
lemma norm_one_sub_le_pow {z : ℂ} (hz : ‖z‖ = 1) (h : ‖1 - z‖ ≤ 1 / 4) {k : ℕ} (hk1 : 1 ≤ k)
    (hk5 : k ≤ 5) : ‖1 - z‖ ≤ ‖1 - z ^ k‖ := by
  rw [← mul_neg_geom_sum, norm_mul]
  refine le_mul_of_one_le_right (norm_nonneg _) ?_
  refine le_trans ?_ (Complex.re_le_norm _)
  rw [Complex.re_sum]
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [Finset.sum_range_succ']
  have h0 : (z ^ 0).re = 1 := by simp
  rw [h0]
  have hnn : ∀ j ∈ range k', 0 ≤ (z ^ (j + 1)).re := by
    intro j hj
    have hj4 : ((j + 1 : ℕ) : ℝ) ≤ 4 := by
      have := mem_range.1 hj
      exact_mod_cast (by omega : j + 1 ≤ 4)
    have h1 := norm_one_sub_pow_le hz (j + 1)
    have h2 : ‖1 - z ^ (j + 1)‖ ≤ 1 := by
      have h3 : ((j + 1 : ℕ) : ℝ) * ‖1 - z‖ ≤ 4 * (1 / 4) :=
        mul_le_mul hj4 h (norm_nonneg _) (by norm_num)
      linarith
    have h4 := (Complex.abs_re_le_norm (1 - z ^ (j + 1))).trans h2
    rw [Complex.sub_re, Complex.one_re] at h4
    have := (abs_le.1 h4).2
    linarith
  have := Finset.sum_nonneg hnn
  linarith

lemma not_mem_bohr_mul {R : Finset (ZMod p)} {ρ' : ℝ} {s : ZMod p} (hs : s ∈ bohr R (1 / 4))
    (hs' : s ∉ bohr R ρ') {k : ℕ} (hk1 : 1 ≤ k) (hk5 : k ≤ 5) :
    (k : ZMod p) * s ∉ bohr R ρ' := by
  rw [mem_bohr] at hs' ⊢
  push Not at hs' ⊢
  obtain ⟨a, ha, hlt⟩ := hs'
  refine ⟨a, ha, lt_of_lt_of_le hlt ?_⟩
  have h1 : a * ((k : ZMod p) * s) = (k : ZMod p) * (a * s) := by ring
  rw [h1, e_nsmul]
  exact norm_one_sub_le_pow (norm_e _) (mem_bohr.1 hs a ha) hk1 hk5

/-- A Bohr set with a nonzero frequency and radius `< 1` is not everything. -/
lemma exists_not_mem_bohr {R : Finset (ZMod p)} {a : ZMod p} (ha : a ∈ R) (ha0 : a ≠ 0) {ρ : ℝ}
    (hρ : ρ < 1) : ∃ x, x ∉ bohr R ρ := by
  by_contra hcon
  push Not at hcon
  have hsum := sum_e_mul (p := p) a
  rw [if_neg ha0] at hsum
  have hre : ∑ x : ZMod p, (e (a * x)).re = 0 := by
    rw [← Complex.re_sum, hsum]; rfl
  have hpos : ∀ x ∈ (univ : Finset (ZMod p)), 0 < (e (a * x)).re := by
    intro x _
    have h1 := mem_bohr.1 (hcon x) a ha
    have h2 := (Complex.abs_re_le_norm (1 - e (a * x))).trans h1
    rw [Complex.sub_re, Complex.one_re] at h2
    have := (abs_le.1 h2).2
    linarith
  have := Finset.sum_pos hpos ⟨0, mem_univ _⟩
  linarith

open Pointwise in
/-- If a Bohr set does not grow, it is trivial or everything. -/
lemma bohr_dichotomy {R : Finset (ZMod p)} {ρ₁ ρ₂ : ℝ} (hρ₁ : 0 ≤ ρ₁) (h2 : 2 * ρ₁ ≤ ρ₂)
    (hsub : bohr R ρ₂ ⊆ bohr R ρ₁) : (bohr R ρ₁).card = 1 ∨ bohr R ρ₁ = univ := by
  classical
  have hne : (bohr R ρ₁).Nonempty := ⟨0, zero_mem_bohr hρ₁⟩
  have hadd : bohr R ρ₁ + bohr R ρ₁ ⊆ bohr R ρ₁ := by
    intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := mem_add.1 hx
    refine hsub (bohr_mono h2 ?_)
    have := add_mem_bohr hy hz
    rwa [← two_mul] at this
  have hcd := ZMod.cauchy_davenport (Fact.out : p.Prime) hne hne
  have hle := card_le_card hadd
  have hpos := card_pos.2 hne
  rcases le_total p ((bohr R ρ₁).card + (bohr R ρ₁).card - 1) with h | h
  · right
    rw [min_eq_left h] at hcd
    apply eq_univ_of_card
    rw [ZMod.card]
    have : (bohr R ρ₁).card ≤ Fintype.card (ZMod p) := card_le_univ _
    rw [ZMod.card] at this
    omega
  · left
    rw [min_eq_right h] at hcd
    omega

end G16

end ModBohr3

section ModCS1

/- # Green 16: moment bounds for random sampling (Croot–Sisask, part 1) -/

open Finset

namespace G16

section CS

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- Indicator function of a finite set, real valued. -/
noncomputable def ind (L : Finset G) (x : G) : ℝ := if x ∈ L then 1 else 0

omit [AddCommGroup G] [Fintype G] in
lemma ind_nonneg (L : Finset G) (x : G) : 0 ≤ ind L x := by
  unfold ind; split_ifs <;> norm_num

omit [AddCommGroup G] [Fintype G] in
lemma ind_le_one (L : Finset G) (x : G) : ind L x ≤ 1 := by
  unfold ind; split_ifs <;> norm_num

/-- `F2 A L x = #{a ∈ A : x + a ∈ L}`. -/
noncomputable def F2 (A L : Finset G) (x : G) : ℝ := ∑ a ∈ A, ind L (x + a)

omit [Fintype G] in
lemma F2_nonneg (A L : Finset G) (x : G) : 0 ≤ F2 A L x :=
  Finset.sum_nonneg fun _ _ => ind_nonneg _ _

omit [Fintype G] in
lemma F2_le_card (A L : Finset G) (x : G) : F2 A L x ≤ A.card := by
  unfold F2
  calc ∑ a ∈ A, ind L (x + a) ≤ ∑ _a ∈ A, (1 : ℝ) := Finset.sum_le_sum fun _ _ => ind_le_one _ _
    _ = A.card := by simp

lemma sum_ind_add (L : Finset G) (a : G) : ∑ x : G, ind L (x + a) = L.card := by
  have h : ∑ x : G, ind L (x + a) = ∑ x : G, ind L x :=
    Fintype.sum_equiv (Equiv.addRight a) _ _ fun x => rfl
  rw [h]
  simp [ind]

lemma sum_F2 (A L : Finset G) : ∑ x : G, F2 A L x = (A.card : ℝ) * L.card := by
  unfold F2
  rw [Finset.sum_comm]
  simp [sum_ind_add]

/-- The empirical count attached to a sample `a`. -/
noncomputable def emp {m : ℕ} (a : Fin m → G) (L : Finset G) (x : G) : ℝ :=
  ∑ i, ind L (x + a i)

omit [AddCommGroup G] [Fintype G] in
lemma exp_mul_ind (L : Finset G) (lam : ℝ) (y : G) :
    Real.exp (lam * ind L y) = 1 + ind L y * (Real.exp lam - 1) := by
  unfold ind; split_ifs <;> simp

omit [Fintype G] in
/-- One-sample exponential moment. -/
lemma sum_exp_ind_le (A L : Finset G) (hA : A.Nonempty) (x : G) {lam : ℝ} (hlam : |lam| ≤ 1) :
    ∑ a ∈ A, Real.exp (lam * (ind L (x + a) - F2 A L x / A.card)) ≤
      A.card * Real.exp (F2 A L x / A.card * lam ^ 2) := by
  have hA0 : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  set μ : ℝ := F2 A L x / A.card with hμ
  have hμ0 : 0 ≤ μ := div_nonneg (F2_nonneg _ _ _) hA0.le
  have h1 : ∀ a ∈ A, Real.exp (lam * (ind L (x + a) - μ)) =
      Real.exp (-(lam * μ)) * (1 + ind L (x + a) * (Real.exp lam - 1)) := by
    intro a _
    rw [← exp_mul_ind, ← Real.exp_add]
    congr 1; ring
  rw [Finset.sum_congr rfl h1, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_mul]
  have h2 : ∑ a ∈ A, ind L (x + a) = μ * A.card := by
    rw [hμ, div_mul_cancel₀ _ hA0.ne']; rfl
  rw [h2]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  have h3 : (A.card : ℝ) + μ * A.card * (Real.exp lam - 1) =
      A.card * (1 + μ * (Real.exp lam - 1)) := by ring
  rw [h3]
  have h4 : 1 + μ * (Real.exp lam - 1) ≤ Real.exp (μ * (Real.exp lam - 1)) := by
    linarith [Real.add_one_le_exp (μ * (Real.exp lam - 1))]
  have h5 := (abs_le.1 (Real.abs_exp_sub_one_sub_id_le hlam)).2
  have h6 : -(lam * μ) + μ * (Real.exp lam - 1) ≤ μ * lam ^ 2 := by
    have : μ * (Real.exp lam - 1 - lam) ≤ μ * lam ^ 2 := mul_le_mul_of_nonneg_left h5 hμ0
    linarith
  calc Real.exp (-(lam * μ)) * (A.card * (1 + μ * (Real.exp lam - 1)))
      ≤ Real.exp (-(lam * μ)) * (A.card * Real.exp (μ * (Real.exp lam - 1))) := by
        gcongr
    _ = A.card * Real.exp (-(lam * μ) + μ * (Real.exp lam - 1)) := by
        rw [Real.exp_add]; ring
    _ ≤ A.card * Real.exp (μ * lam ^ 2) := by
        gcongr

omit [Fintype G] in
/-- Exponential moment of the centred empirical count. -/
lemma sum_exp_emp_le (A L : Finset G) (hA : A.Nonempty) (m : ℕ) (x : G) {lam : ℝ}
    (hlam : |lam| ≤ 1) :
    ∑ a ∈ Fintype.piFinset (fun _ : Fin m => A),
      Real.exp (lam * (emp a L x - m * (F2 A L x / A.card))) ≤
      (A.card : ℝ) ^ m * Real.exp (m * (F2 A L x / A.card) * lam ^ 2) := by
  set μ : ℝ := F2 A L x / A.card with hμ
  have h1 : ∀ a : Fin m → G, Real.exp (lam * (emp a L x - m * μ)) =
      ∏ i, Real.exp (lam * (ind L (x + a i) - μ)) := by
    intro a
    rw [← Real.exp_sum]
    congr 1
    unfold emp
    rw [← Finset.mul_sum, Finset.sum_sub_distrib]
    simp
  simp_rw [h1]
  rw [← Finset.prod_univ_sum (fun _ : Fin m => A)
    (fun _ b => Real.exp (lam * (ind L (x + b) - μ)))]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have h2 := sum_exp_ind_le A L hA x hlam
  have h3 : (A.card : ℝ) ^ m * Real.exp (m * μ * lam ^ 2) =
      (A.card * Real.exp (μ * lam ^ 2)) ^ m := by
    rw [mul_pow, ← Real.exp_nat_mul]; congr 2; ring
  rw [h3]
  exact pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le) h2 m

/-- `u^(2r) ≤ (2r)! (e^u + e^{-u} - 2)`. -/
lemma pow_le_factorial_mul_exp (r : ℕ) (hr : 1 ≤ r) (u : ℝ) :
    u ^ (2 * r) ≤ (2 * r).factorial * (Real.exp u + Real.exp (-u) - 2) := by
  have key : ∀ v : ℝ, 0 ≤ v →
      v ^ (2 * r) ≤ (2 * r).factorial * (Real.exp v + Real.exp (-v) - 2) := by
    intro v hv
    have h1 := Real.sum_le_exp_of_nonneg hv (2 * r + 1)
    have hsub : ({0, 1, 2 * r} : Finset ℕ) ⊆ range (2 * r + 1) := by
      intro i hi
      simp only [mem_insert, mem_singleton] at hi
      rw [mem_range]; omega
    have h2 : ∑ i ∈ ({0, 1, 2 * r} : Finset ℕ), v ^ i / (i.factorial : ℝ) ≤
        ∑ i ∈ range (2 * r + 1), v ^ i / (i.factorial : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => by positivity
    have h3 : ∑ i ∈ ({0, 1, 2 * r} : Finset ℕ), v ^ i / (i.factorial : ℝ) =
        1 + v + v ^ (2 * r) / ((2 * r).factorial : ℝ) := by
      rw [Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp; omega),
        Finset.sum_singleton]
      simp; ring
    have h4 := Real.add_one_le_exp (-v)
    have hf : (0 : ℝ) < (2 * r).factorial := by positivity
    have h5 : v ^ (2 * r) / ((2 * r).factorial : ℝ) ≤ Real.exp v + Real.exp (-v) - 2 := by
      linarith
    rw [div_le_iff₀ hf] at h5
    linarith
  rcases le_total 0 u with h | h
  · exact key u h
  · have := key (-u) (by linarith)
    rw [neg_neg, Even.neg_pow (even_two_mul r)] at this
    linarith

lemma exp_two_mul_le (r : ℕ) : Real.exp (2 * r) ≤ 8 ^ r := by
  have h1 : Real.exp 2 ≤ 8 := by
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    have h3 := Real.exp_one_lt_d9
    have h4 := Real.exp_pos 1
    rw [h2]; nlinarith
  calc Real.exp (2 * r) = Real.exp (r * 2) := by rw [mul_comm]
    _ = Real.exp 2 ^ r := Real.exp_nat_mul _ _
    _ ≤ 8 ^ r := pow_le_pow_left₀ (Real.exp_pos _).le h1 _

/-- `exp (c μ) - 1 ≤ μ (exp c - 1)` for `μ ∈ [0,1]`. -/
lemma exp_mul_sub_one_le {μ c : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) :
    Real.exp (c * μ) - 1 ≤ μ * (Real.exp c - 1) := by
  have h := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ c) (by linarith : 0 ≤ 1 - μ) hμ0
    (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at h
  have h2 : μ * c = c * μ := mul_comm _ _
  rw [h2] at h
  linarith

omit [Fintype G] in
/-- The `2r`-th moment bound for the centred empirical count; here `m = 2 r s²`. -/
lemma sum_pow_emp_le (A L : Finset G) (hA : A.Nonempty) (r s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s)
    (x : G) :
    ∑ a ∈ Fintype.piFinset (fun _ : Fin (2 * r * s ^ 2) => A),
      (emp a L x - (2 * r * s ^ 2 : ℕ) * (F2 A L x / A.card)) ^ (2 * r) ≤
      2 * (2 * r).factorial * (s : ℝ) ^ (2 * r) * (A.card : ℝ) ^ (2 * r * s ^ 2) *
        (F2 A L x / A.card * 8 ^ r) := by
  have hA0 : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  set m : ℕ := 2 * r * s ^ 2 with hm
  set μ : ℝ := F2 A L x / A.card with hμ
  have hμ0 : 0 ≤ μ := div_nonneg (F2_nonneg _ _ _) hA0.le
  have hμ1 : μ ≤ 1 := by
    rw [hμ, div_le_one hA0]; exact F2_le_card _ _ _
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  set lam : ℝ := 1 / s with hlam
  have hlam0 : 0 < lam := by positivity
  have hlam1 : |lam| ≤ 1 := by
    rw [abs_of_pos hlam0, hlam, div_le_one hs0]; exact_mod_cast hs
  have hlam1' : |(-lam)| ≤ 1 := by rwa [abs_neg]
  -- pointwise bound
  have hpt : ∀ a : Fin m → G, (emp a L x - m * μ) ^ (2 * r) ≤
      (2 * r).factorial * (s : ℝ) ^ (2 * r) *
        (Real.exp (lam * (emp a L x - m * μ)) + Real.exp (-lam * (emp a L x - m * μ)) - 2) := by
    intro a
    have h := pow_le_factorial_mul_exp r hr (lam * (emp a L x - m * μ))
    have h2 : (lam * (emp a L x - m * μ)) ^ (2 * r) =
        (emp a L x - m * μ) ^ (2 * r) / (s : ℝ) ^ (2 * r) := by
      rw [mul_pow, hlam, one_div, inv_pow]; field_simp
    rw [h2, div_le_iff₀ (by positivity)] at h
    rw [neg_mul]
    linarith
  refine (Finset.sum_le_sum fun a _ => hpt a).trans ?_
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have e1 := sum_exp_emp_le A L hA m x hlam1
  have e2 := sum_exp_emp_le A L hA m x hlam1'
  have hcard : ∑ _a ∈ Fintype.piFinset (fun _ : Fin m => A), (2 : ℝ) = 2 * (A.card : ℝ) ^ m := by
    rw [Finset.sum_const, Fintype.card_piFinset_const, nsmul_eq_mul]; push_cast; ring
  rw [hcard]
  have hml : (m : ℝ) * μ * lam ^ 2 = 2 * r * μ := by
    rw [hm, hlam]; push_cast; field_simp
  have hml' : (m : ℝ) * μ * (-lam) ^ 2 = 2 * r * μ := by rw [neg_sq, hml]
  rw [hml] at e1
  rw [hml'] at e2
  have h7 : Real.exp (2 * r * μ) - 1 ≤ μ * 8 ^ r := by
    have h8 := exp_mul_sub_one_le (c := 2 * r) hμ0 hμ1
    have h9 := exp_two_mul_le r
    have h10 : μ * (Real.exp (2 * r) - 1) ≤ μ * 8 ^ r :=
      mul_le_mul_of_nonneg_left (by linarith) hμ0
    linarith
  have hAm : (0 : ℝ) ≤ (A.card : ℝ) ^ m := by positivity
  have h11 : (A.card : ℝ) ^ m * Real.exp (2 * r * μ) - (A.card : ℝ) ^ m ≤
      (A.card : ℝ) ^ m * (μ * 8 ^ r) := by
    have := mul_le_mul_of_nonneg_left h7 hAm
    linarith
  have hfac : (0 : ℝ) ≤ (2 * r).factorial * (s : ℝ) ^ (2 * r) := by positivity
  calc ((2 * r).factorial : ℝ) * (s : ℝ) ^ (2 * r) *
        (∑ a ∈ Fintype.piFinset (fun _ : Fin m => A), Real.exp (lam * (emp a L x - m * μ)) +
          ∑ a ∈ Fintype.piFinset (fun _ : Fin m => A), Real.exp (-lam * (emp a L x - m * μ)) -
          2 * (A.card : ℝ) ^ m)
      ≤ ((2 * r).factorial : ℝ) * (s : ℝ) ^ (2 * r) * (2 * ((A.card : ℝ) ^ m * (μ * 8 ^ r))) := by
        apply mul_le_mul_of_nonneg_left _ hfac
        linarith
    _ = 2 * (2 * r).factorial * (s : ℝ) ^ (2 * r) * (A.card : ℝ) ^ m * (μ * 8 ^ r) := by ring

end CS

end G16

end ModCS1

section ModCS2

/- # Green 16: the Croot–Sisask lemma (part 2) -/

open Finset
open scoped Pointwise

namespace G16

section CS

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- The `2r`-th power deviation of the empirical count from its mean. -/
noncomputable def dev (A L : Finset G) (r m : ℕ) (a : Fin m → G) : ℝ :=
  ∑ x : G, (emp a L x - m * (F2 A L x / A.card)) ^ (2 * r)

lemma dev_nonneg (A L : Finset G) (r m : ℕ) (a : Fin m → G) : 0 ≤ dev A L r m a :=
  Finset.sum_nonneg fun _ _ => (even_two_mul r).pow_nonneg _

lemma sum_dev_le (A L : Finset G) (hA : A.Nonempty) (r s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s) :
    ∑ a ∈ Fintype.piFinset (fun _ : Fin (2 * r * s ^ 2) => A), dev A L r (2 * r * s ^ 2) a ≤
      (A.card : ℝ) ^ (2 * r * s ^ 2) *
        (2 * (2 * r).factorial * (s : ℝ) ^ (2 * r) * 8 ^ r * L.card) := by
  have hA0 : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  unfold dev
  rw [Finset.sum_comm]
  refine (Finset.sum_le_sum fun x _ => sum_pow_emp_le A L hA r s hr hs x).trans ?_
  rw [← Finset.mul_sum, ← Finset.sum_mul, ← Finset.sum_div, sum_F2]
  have : (A.card : ℝ) * L.card / A.card = L.card := by field_simp
  rw [this]
  apply le_of_eq; ring

/-- The **Croot–Sisask lemma** in `L^{2r}` form, with `m = 2 r s²` samples. -/
theorem croot_sisask (A L S : Finset G) (hA : A.Nonempty) (r s : ℕ) (hr : 1 ≤ r)
    (hs : 1 ≤ s) :
    ∃ T ⊆ S, (S.card : ℝ) * (A.card : ℝ) ^ (2 * r * s ^ 2) ≤
        2 * T.card * ((A + S).card : ℝ) ^ (2 * r * s ^ 2) ∧
      ∀ t ∈ T, ∀ t' ∈ T,
        (s : ℝ) ^ (2 * r) * ∑ x : G, (F2 A L (x + t - t') - F2 A L x) ^ (2 * r) ≤
          4 * 32 ^ r * (A.card : ℝ) ^ (2 * r) * L.card := by
  classical
  have hA0 : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  set m : ℕ := 2 * r * s ^ 2 with hm
  set P := Fintype.piFinset (fun _ : Fin m => A) with hP
  set E : ℝ := 2 * (2 * r).factorial * (s : ℝ) ^ (2 * r) * 8 ^ r * L.card with hE
  have hE0 : 0 ≤ E := by positivity
  have hsum : ∑ a ∈ P, dev A L r m a ≤ (A.card : ℝ) ^ m * E := sum_dev_le A L hA r s hr hs
  have hPcard : (P.card : ℝ) = (A.card : ℝ) ^ m := by
    rw [hP, Fintype.card_piFinset_const]; push_cast; rfl
  set 𝒢 := P.filter (fun a => dev A L r m a ≤ 2 * E) with h𝒢
  -- at least half of the samples are good
  have hgood : (P.card : ℝ) ≤ 2 * 𝒢.card := by
    by_contra hcon
    push Not at hcon
    set bad := P.filter (fun a => ¬ dev A L r m a ≤ 2 * E) with hbad
    have hsplit : 𝒢.card + bad.card = P.card := by
      rw [h𝒢, hbad]; exact Finset.card_filter_add_card_filter_not _
    have hsplit' : (𝒢.card : ℝ) + bad.card = P.card := by exact_mod_cast hsplit
    have hbadpos : (0 : ℝ) < bad.card := by linarith [(Nat.cast_nonneg 𝒢.card : (0 : ℝ) ≤ _)]
    have hbadne : bad.Nonempty := by
      rw [← Finset.card_pos]; exact_mod_cast hbadpos
    have h1 : ∑ _a ∈ bad, (2 * E) < ∑ a ∈ bad, dev A L r m a := by
      apply Finset.sum_lt_sum_of_nonempty hbadne
      intro a ha
      exact not_le.1 (mem_filter.1 ha).2
    rw [Finset.sum_const, nsmul_eq_mul] at h1
    have h2 : ∑ a ∈ bad, dev A L r m a ≤ ∑ a ∈ P, dev A L r m a :=
      Finset.sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun a _ _ => dev_nonneg _ _ _ _ _
    have h3 : (P.card : ℝ) * E ≤ bad.card * (2 * E) := by nlinarith
    rw [hPcard] at h3
    linarith
  rcases S.eq_empty_or_nonempty with hS | hS
  · exact ⟨∅, by simp, by simp [hS], by simp⟩
  set Q := Fintype.piFinset (fun _ : Fin m => A + S) with hQ
  have hQne : Q.Nonempty := by
    rw [hQ, Fintype.piFinset_nonempty]
    intro _; exact hA.add hS
  have hQcard : (Q.card : ℝ) = ((A + S).card : ℝ) ^ m := by
    rw [hQ, Fintype.card_piFinset_const]; push_cast; rfl
  have hQ0 : (0 : ℝ) < Q.card := by exact_mod_cast hQne.card_pos
  let φ : (Fin m → G) × G → (Fin m → G) := fun z i => z.1 i + z.2
  have hmaps : ∀ z ∈ 𝒢 ×ˢ S, φ z ∈ Q := by
    intro z hz
    rw [mem_product] at hz
    rw [hQ, Fintype.mem_piFinset]
    intro i
    have h1 : z.1 ∈ P := (mem_filter.1 hz.1).1
    rw [hP, Fintype.mem_piFinset] at h1
    exact add_mem_add (h1 i) hz.2
  obtain ⟨y, _, hy⟩ := exists_le_card_fiber_of_nsmul_le_card_of_maps_to
    (b := ((𝒢.card : ℝ) * S.card) / Q.card) hmaps hQne (by
      rw [nsmul_eq_mul, mul_div_cancel₀ _ hQ0.ne', card_product]; push_cast; rfl)
  set T := S.filter (fun t => (fun i => y i - t) ∈ 𝒢) with hT
  have hfib : ((𝒢 ×ˢ S).filter (fun z => φ z = y)).card ≤ T.card := by
    refine card_le_card_of_injOn (fun z => z.2) ?_ ?_
    · intro z hz
      have hz' := mem_filter.1 (mem_coe.1 hz)
      have hz1 := mem_product.1 hz'.1
      refine mem_coe.2 (mem_filter.2 ⟨hz1.2, ?_⟩)
      have : (fun i => y i - z.2) = z.1 := by
        funext i
        have := congrFun hz'.2 i
        simp only [φ] at this
        rw [← this]; abel
      rw [this]; exact hz1.1
    · intro z hz z' hz' h
      have hz1 := (mem_filter.1 (mem_coe.1 hz)).2
      have hz1' := (mem_filter.1 (mem_coe.1 hz')).2
      simp only at h
      refine Prod.ext ?_ h
      funext i
      have e1 := congrFun hz1 i
      have e2 := congrFun hz1' i
      simp only [φ] at e1 e2
      rw [h] at e1
      exact add_right_cancel (e1.trans e2.symm)
  refine ⟨T, filter_subset _ _, ?_, ?_⟩
  · have h1 : (𝒢.card : ℝ) * S.card / Q.card ≤ T.card := hy.trans (by exact_mod_cast hfib)
    rw [div_le_iff₀ hQ0, hQcard] at h1
    rw [hPcard] at hgood
    have hS0 : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
    nlinarith
  · intro t ht t' ht'
    have ha : dev A L r m (fun i => y i - t) ≤ 2 * E := (mem_filter.1 (mem_filter.1 ht).2).2
    have ha' : dev A L r m (fun i => y i - t') ≤ 2 * E :=
      (mem_filter.1 (mem_filter.1 ht').2).2
    set X : ℝ := ∑ x : G, (F2 A L (x + t - t') - F2 A L x) ^ (2 * r) with hX
    have hemp : ∀ x : G, emp (fun i => y i - t) L (x + t - t') = emp (fun i => y i - t') L x := by
      intro x
      unfold emp
      refine Finset.sum_congr rfl fun i _ => ?_
      have : x + t - t' + (y i - t) = x + (y i - t') := by abel
      show ind L (x + t - t' + (y i - t)) = ind L (x + (y i - t'))
      rw [this]
    have hpt : ∀ x : G, ((m : ℝ) / A.card) ^ (2 * r) * (F2 A L (x + t - t') - F2 A L x) ^ (2 * r) ≤
        2 ^ (2 * r - 1) *
          ((emp (fun i => y i - t) L (x + t - t') - m * (F2 A L (x + t - t') / A.card)) ^ (2 * r) +
            (emp (fun i => y i - t') L x - m * (F2 A L x / A.card)) ^ (2 * r)) := by
      intro x
      have h1 : (m : ℝ) / A.card * (F2 A L (x + t - t') - F2 A L x) =
          -(emp (fun i => y i - t) L (x + t - t') - m * (F2 A L (x + t - t') / A.card)) +
            (emp (fun i => y i - t') L x - m * (F2 A L x / A.card)) := by
        rw [hemp x]; field_simp; ring
      rw [← mul_pow, h1]
      have h2 := (even_two_mul r).add_pow_le
        (a := -(emp (fun i => y i - t) L (x + t - t') - m * (F2 A L (x + t - t') / A.card)))
        (b := (emp (fun i => y i - t') L x - m * (F2 A L x / A.card)))
      rwa [Even.neg_pow (even_two_mul r)] at h2
    have hre : ∑ x : G,
        (emp (fun i => y i - t) L (x + t - t') - m * (F2 A L (x + t - t') / A.card)) ^ (2 * r) =
        dev A L r m (fun i => y i - t) := by
      unfold dev
      refine Fintype.sum_equiv (Equiv.addRight (t - t')) _ _ fun x => ?_
      simp only [Equiv.coe_addRight, add_sub_assoc]
    have hsumx : ((m : ℝ) / A.card) ^ (2 * r) * X ≤ 2 ^ (2 * r - 1) * (2 * E + 2 * E) := by
      rw [hX, Finset.mul_sum]
      refine (Finset.sum_le_sum fun x _ => hpt x).trans ?_
      rw [← Finset.mul_sum, Finset.sum_add_distrib, hre]
      have : ∑ x : G, (emp (fun i => y i - t') L x - m * (F2 A L x / A.card)) ^ (2 * r) =
          dev A L r m (fun i => y i - t') := rfl
      rw [this]
      exact mul_le_mul_of_nonneg_left (add_le_add ha ha') (by positivity)
    -- algebra
    have hX0 : 0 ≤ X := Finset.sum_nonneg fun _ _ => (even_two_mul r).pow_nonneg _
    have hfact : ((2 * r).factorial : ℝ) ≤ ((2 * r : ℕ) : ℝ) ^ (2 * r) := by
      exact_mod_cast Nat.factorial_le_pow (2 * r)
    have h2r : (2 : ℝ) ^ (2 * r - 1) * 2 = 2 ^ (2 * r) := by
      rw [← pow_succ]; congr 1; omega
    have hmr : (m : ℝ) = ((2 * r : ℕ) : ℝ) * (s : ℝ) ^ 2 := by rw [hm]; push_cast; ring
    have hr0 : (0 : ℝ) < ((2 * r : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 2 * r)
    rw [div_pow, div_mul_eq_mul_div, div_le_iff₀ (by positivity), hmr, mul_pow] at hsumx
    have h4 : (2 : ℝ) ^ (2 * r) = 4 ^ r := by rw [pow_mul]; norm_num
    have h5 : ((s : ℝ) ^ 2) ^ (2 * r) = (s : ℝ) ^ (2 * r) * (s : ℝ) ^ (2 * r) := by
      rw [← pow_mul, ← pow_add]; congr 1; ring
    have h6 : (32 : ℝ) ^ r = 4 ^ r * 8 ^ r := by rw [← mul_pow]; norm_num
    rw [h5] at hsumx
    have hK : (0 : ℝ) < ((2 * r : ℕ) : ℝ) ^ (2 * r) * (s : ℝ) ^ (2 * r) := by positivity
    refine le_of_mul_le_mul_left ?_ hK
    calc ((2 * r : ℕ) : ℝ) ^ (2 * r) * (s : ℝ) ^ (2 * r) * ((s : ℝ) ^ (2 * r) * X)
        = ((2 * r : ℕ) : ℝ) ^ (2 * r) * ((s : ℝ) ^ (2 * r) * (s : ℝ) ^ (2 * r)) * X := by ring
      _ ≤ 2 ^ (2 * r - 1) * (2 * E + 2 * E) * (A.card : ℝ) ^ (2 * r) := hsumx
      _ = 2 ^ (2 * r - 1) * 2 * (2 * E) * (A.card : ℝ) ^ (2 * r) := by ring
      _ = 4 ^ r * (2 * E) * (A.card : ℝ) ^ (2 * r) := by rw [h2r, h4]
      _ = 4 * 4 ^ r * 8 ^ r * (s : ℝ) ^ (2 * r) * ((2 * r).factorial : ℝ) *
            (A.card : ℝ) ^ (2 * r) * L.card := by rw [hE]; ring
      _ ≤ 4 * 4 ^ r * 8 ^ r * (s : ℝ) ^ (2 * r) * ((2 * r : ℕ) : ℝ) ^ (2 * r) *
            (A.card : ℝ) ^ (2 * r) * L.card := by gcongr
      _ = ((2 * r : ℕ) : ℝ) ^ (2 * r) * (s : ℝ) ^ (2 * r) *
            (4 * 32 ^ r * (A.card : ℝ) ^ (2 * r) * L.card) := by rw [h6]; ring

end CS

end G16

end ModCS2

section ModCS3

/- # Green 16: `L^∞` almost-periodicity for three-fold counts and iterated averaging -/

open Finset
open scoped Pointwise

namespace G16

section CS

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- Three-fold count `#{(a,b) ∈ A × M : x + a + b ∈ L}`. -/
noncomputable def F3 (A M L : Finset G) (x : G) : ℝ := ∑ b ∈ M, F2 A L (x + b)

/-- `L^∞` almost-periodicity of three-fold counts (Croot–Sisask plus Hölder). -/
theorem cs_infty (A M L S : Finset G) (hA : A.Nonempty) (r q : ℕ) (hr : 1 ≤ r) (hq : 1 ≤ q)
    (hLM : (L.card : ℝ) ≤ 4 ^ r * M.card) :
    ∃ T ⊆ S, (S.card : ℝ) * (A.card : ℝ) ^ (2 * r * (32 * q) ^ 2) ≤
        2 * T.card * ((A + S).card : ℝ) ^ (2 * r * (32 * q) ^ 2) ∧
      ∀ t ∈ T, ∀ t' ∈ T, ∀ x : G,
        q * |F3 A M L (x + t - t') - F3 A M L x| ≤ A.card * M.card := by
  obtain ⟨T, hTS, hcard, hap⟩ := croot_sisask A L S hA r (32 * q) hr (by omega)
  refine ⟨T, hTS, hcard, ?_⟩
  intro t ht t' ht' x
  have h := hap t ht t' ht'
  set ΔF : G → ℝ := fun y => F2 A L (y + t - t') - F2 A L y with hΔF
  have hΔ3 : F3 A M L (x + t - t') - F3 A M L x = ∑ b ∈ M, ΔF (x + b) := by
    unfold F3
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    have : x + t - t' + b = x + b + t - t' := by abel
    simp only [hΔF, this]
  obtain ⟨n, hn⟩ : ∃ n, 2 * r = n + 1 := ⟨2 * r - 1, by omega⟩
  have hM0 : (0 : ℝ) ≤ M.card := Nat.cast_nonneg _
  have h1 : |∑ b ∈ M, ΔF (x + b)| ^ (2 * r) ≤
      (M.card : ℝ) ^ n * ∑ b ∈ M, (ΔF (x + b)) ^ (2 * r) := by
    calc |∑ b ∈ M, ΔF (x + b)| ^ (2 * r) ≤ (∑ b ∈ M, |ΔF (x + b)|) ^ (2 * r) :=
          pow_le_pow_left₀ (abs_nonneg _) (Finset.abs_sum_le_sum_abs _ _) _
      _ = (∑ b ∈ M, |ΔF (x + b)|) ^ (n + 1) := by rw [hn]
      _ ≤ (M.card : ℝ) ^ n * ∑ b ∈ M, |ΔF (x + b)| ^ (n + 1) :=
          pow_sum_le_card_mul_sum_pow (fun _ _ => abs_nonneg _) n
      _ = (M.card : ℝ) ^ n * ∑ b ∈ M, (ΔF (x + b)) ^ (2 * r) := by
          rw [← hn]
          congr 1
          exact Finset.sum_congr rfl fun b _ => (even_two_mul r).pow_abs _
  have h2 : ∑ b ∈ M, (ΔF (x + b)) ^ (2 * r) ≤ ∑ y : G, (ΔF y) ^ (2 * r) := by
    calc ∑ b ∈ M, (ΔF (x + b)) ^ (2 * r) ≤ ∑ b : G, (ΔF (x + b)) ^ (2 * r) :=
          Finset.sum_le_univ_sum_of_nonneg fun b => (even_two_mul r).pow_nonneg _
      _ = ∑ y : G, (ΔF y) ^ (2 * r) :=
          Fintype.sum_equiv (Equiv.addLeft x) _ _ fun b => rfl
  have h3 : ((32 * q : ℕ) : ℝ) ^ (2 * r) * |∑ b ∈ M, ΔF (x + b)| ^ (2 * r) ≤
      (M.card : ℝ) ^ n * (4 * 32 ^ r * (A.card : ℝ) ^ (2 * r) * L.card) := by
    calc ((32 * q : ℕ) : ℝ) ^ (2 * r) * |∑ b ∈ M, ΔF (x + b)| ^ (2 * r)
        ≤ ((32 * q : ℕ) : ℝ) ^ (2 * r) * ((M.card : ℝ) ^ n * ∑ y : G, (ΔF y) ^ (2 * r)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
      _ = (M.card : ℝ) ^ n * (((32 * q : ℕ) : ℝ) ^ (2 * r) * ∑ y : G, (ΔF y) ^ (2 * r)) := by
          ring
      _ ≤ (M.card : ℝ) ^ n * (4 * 32 ^ r * (A.card : ℝ) ^ (2 * r) * L.card) :=
          mul_le_mul_of_nonneg_left h (by positivity)
  have h4 : (M.card : ℝ) ^ n * (4 * 32 ^ r * (A.card : ℝ) ^ (2 * r) * L.card) ≤
      4 * 128 ^ r * ((A.card : ℝ) * M.card) ^ (2 * r) := by
    have e1 : (128 : ℝ) ^ r = 32 ^ r * 4 ^ r := by rw [← mul_pow]; norm_num
    calc (M.card : ℝ) ^ n * (4 * 32 ^ r * (A.card : ℝ) ^ (2 * r) * L.card)
        ≤ (M.card : ℝ) ^ n * (4 * 32 ^ r * (A.card : ℝ) ^ (2 * r) * (4 ^ r * M.card)) := by
          gcongr
      _ = 4 * (32 ^ r * 4 ^ r) * (A.card : ℝ) ^ (2 * r) * ((M.card : ℝ) ^ (n + 1)) := by
          rw [pow_succ]; ring
      _ = 4 * 128 ^ r * ((A.card : ℝ) * M.card) ^ (2 * r) := by
          rw [← hn, e1, mul_pow]; ring
  have h5 : ((32 * q : ℕ) : ℝ) ^ (2 * r) = 1024 ^ r * (q : ℝ) ^ (2 * r) := by
    push_cast
    rw [mul_pow, pow_mul]
    norm_num
  have h6 : (4 : ℝ) * 128 ^ r ≤ 1024 ^ r := by
    have e2 : (1024 : ℝ) ^ r = 8 ^ r * 128 ^ r := by rw [← mul_pow]; norm_num
    have e3 : (8 : ℝ) ^ 1 ≤ 8 ^ r := pow_le_pow_right₀ (by norm_num) hr
    rw [e2]
    have : (0 : ℝ) < 128 ^ r := by positivity
    nlinarith
  have h7 : (1024 : ℝ) ^ r * ((q : ℝ) * |∑ b ∈ M, ΔF (x + b)|) ^ (2 * r) ≤
      1024 ^ r * ((A.card : ℝ) * M.card) ^ (2 * r) := by
    calc (1024 : ℝ) ^ r * ((q : ℝ) * |∑ b ∈ M, ΔF (x + b)|) ^ (2 * r)
        = ((32 * q : ℕ) : ℝ) ^ (2 * r) * |∑ b ∈ M, ΔF (x + b)| ^ (2 * r) := by
          rw [h5, mul_pow]; ring
      _ ≤ 4 * 128 ^ r * ((A.card : ℝ) * M.card) ^ (2 * r) := h3.trans h4
      _ ≤ 1024 ^ r * ((A.card : ℝ) * M.card) ^ (2 * r) :=
          mul_le_mul_of_nonneg_right h6 (by positivity)
  have h8 := le_of_mul_le_mul_left h7 (by positivity : (0 : ℝ) < 1024 ^ r)
  rw [hΔ3]
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by omega : 2 * r ≠ 0)).1 h8

/-- Averaging over differences of pairs of elements of `T`. -/
noncomputable def avgT (T : Finset G) (f : G → ℂ) (x : G) : ℂ :=
  (∑ t ∈ T, ∑ t' ∈ T, f (x + t - t')) / ((T.card : ℂ) ^ 2)

omit [Fintype G] [DecidableEq G] in
/-- Iterated averaging preserves almost-periodic functions up to a linear loss. -/
lemma norm_iterate_avgT_sub_le (T : Finset G) (hT : T.Nonempty) (f : G → ℂ) {ε : ℝ}
    (hf : ∀ t ∈ T, ∀ t' ∈ T, ∀ x, ‖f (x + t - t') - f x‖ ≤ ε) (k : ℕ) :
    ∀ x, ‖(avgT T)^[k] f x - f x‖ ≤ k * ε := by
  have hT0 : (0 : ℝ) < T.card := by exact_mod_cast hT.card_pos
  have hTc : (T.card : ℂ) ≠ 0 := by exact_mod_cast hT.card_pos.ne'
  induction k with
  | zero => intro x; simp
  | succ k ih =>
    intro x
    rw [Function.iterate_succ_apply']
    set g := (avgT T)^[k] f with hg
    have h1 : avgT T g x - f x =
        (∑ t ∈ T, ∑ t' ∈ T, (g (x + t - t') - f x)) / ((T.card : ℂ) ^ 2) := by
      unfold avgT
      simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
      field_simp
    rw [h1, norm_div, norm_pow, Complex.norm_natCast, div_le_iff₀ (by positivity)]
    refine (norm_sum_le _ _).trans ?_
    have h2 : ∀ t ∈ T, ‖∑ t' ∈ T, (g (x + t - t') - f x)‖ ≤ T.card * ((k + 1 : ℕ) * ε) := by
      intro t ht
      refine (norm_sum_le _ _).trans ?_
      have h3 : ∀ t' ∈ T, ‖g (x + t - t') - f x‖ ≤ (k + 1 : ℕ) * ε := by
        intro t' ht'
        have e1 : g (x + t - t') - f x =
            (g (x + t - t') - f (x + t - t')) + (f (x + t - t') - f x) := by ring
        rw [e1]
        refine (norm_add_le _ _).trans ?_
        have := ih (x + t - t')
        have := hf t ht t' ht' x
        push_cast
        linarith
      calc ∑ t' ∈ T, ‖g (x + t - t') - f x‖ ≤ ∑ _t' ∈ T, ((k + 1 : ℕ) * ε) :=
            Finset.sum_le_sum h3
        _ = T.card * ((k + 1 : ℕ) * ε) := by rw [Finset.sum_const, nsmul_eq_mul]
    calc ∑ t ∈ T, ‖∑ t' ∈ T, (g (x + t - t') - f x)‖ ≤ ∑ _t ∈ T, (T.card * ((k + 1 : ℕ) * ε)) :=
          Finset.sum_le_sum h2
      _ = (k + 1 : ℕ) * ε * (T.card : ℝ) ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring

end CS

end G16

end ModCS3

section ModFourier

/- # Green 16: the Fourier step -/

open Finset

namespace G16

variable {p : ℕ} [Fact p.Prime]

/-- Character sum over a finite set. -/
noncomputable def hat (L : Finset (ZMod p)) (a : ZMod p) : ℂ := ∑ l ∈ L, e (a * l)

lemma norm_hat_le (L : Finset (ZMod p)) (a : ZMod p) : ‖hat L a‖ ≤ L.card := by
  unfold hat
  refine (norm_sum_le _ _).trans ?_
  simp [norm_e]

lemma sum_e_mul' (w : ZMod p) : ∑ a : ZMod p, e (a * w) = if w = 0 then (p : ℂ) else 0 := by
  rw [← sum_e_mul w]
  exact Finset.sum_congr rfl fun a _ => by rw [mul_comm]

lemma e_mul_sub (a z l : ZMod p) : e (a * z) * starRingEnd ℂ (e (a * l)) = e (a * (z - l)) := by
  rw [mul_sub, e_sub]

/-- Fourier inversion for indicator functions. -/
lemma ind_eq_sum (L : Finset (ZMod p)) (z : ZMod p) :
    ((ind L z : ℝ) : ℂ) = (1 / (p : ℂ)) * ∑ a : ZMod p, e (a * z) * starRingEnd ℂ (hat L a) := by
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have h1 : ∑ a : ZMod p, e (a * z) * starRingEnd ℂ (hat L a) =
      ∑ l ∈ L, ∑ a : ZMod p, e (a * (z - l)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    unfold hat
    rw [map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => e_mul_sub a z l
  rw [h1]
  simp_rw [sum_e_mul', sub_eq_zero]
  rw [Finset.sum_ite_eq]
  by_cases hz : z ∈ L
  · simp [ind, hz, hp]
  · simp [ind, hz]

/-- Parseval for character sums. -/
lemma sum_norm_hat_sq (L : Finset (ZMod p)) :
    ∑ a : ZMod p, ‖hat L a‖ ^ 2 = (p : ℝ) * L.card := by
  have h1 : ∀ a : ZMod p, ((‖hat L a‖ : ℝ) : ℂ) ^ 2 = ∑ l ∈ L, ∑ l' ∈ L, e (a * (l - l')) := by
    intro a
    have : ((‖hat L a‖ : ℝ) : ℂ) ^ 2 = hat L a * starRingEnd ℂ (hat L a) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; rfl
    rw [this]
    unfold hat
    rw [map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l' _ => e_mul_sub a l l'
  have h2 : ((∑ a : ZMod p, ‖hat L a‖ ^ 2 : ℝ) : ℂ) = ((p : ℝ) * L.card : ℝ) := by
    push_cast
    simp_rw [h1]
    rw [Finset.sum_comm]
    have h3 : ∀ l ∈ L, ∑ a : ZMod p, ∑ l' ∈ L, e (a * (l - l')) = (p : ℂ) := by
      intro l hl
      rw [Finset.sum_comm]
      simp_rw [sum_e_mul', sub_eq_zero]
      rw [Finset.sum_ite_eq, if_pos hl]
    rw [Finset.sum_congr rfl h3]
    simp [mul_comm]
  exact_mod_cast h2

/-- Cauchy–Schwarz plus Parseval. -/
lemma sum_norm_hat_mul_le (L M : Finset (ZMod p)) {c : ℝ} (hc : 0 ≤ c)
    (hLM : (L.card : ℝ) ≤ c ^ 2 * M.card) :
    ∑ a : ZMod p, ‖hat L a‖ * ‖hat M a‖ ≤ p * (c * M.card) := by
  have h1 := Finset.sum_mul_sq_le_sq_mul_sq (univ : Finset (ZMod p))
    (fun a => ‖hat L a‖) (fun a => ‖hat M a‖)
  rw [sum_norm_hat_sq, sum_norm_hat_sq] at h1
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg _
  have hM0 : (0 : ℝ) ≤ M.card := Nat.cast_nonneg _
  have h2 : (∑ a : ZMod p, ‖hat L a‖ * ‖hat M a‖) ^ 2 ≤ ((p : ℝ) * (c * M.card)) ^ 2 := by
    refine h1.trans ?_
    have : (p : ℝ) * L.card * (p * M.card) ≤ p * (c ^ 2 * M.card) * (p * M.card) := by
      gcongr
    refine this.trans (le_of_eq ?_)
    ring
  exact (pow_le_pow_iff_left₀ (Finset.sum_nonneg fun _ _ => by positivity) (by positivity)
    (by norm_num : (2 : ℕ) ≠ 0)).1 h2

/-- Trigonometric polynomial with coefficients `c`. -/
noncomputable def trig (c : ZMod p → ℂ) (y : ZMod p) : ℂ := ∑ a : ZMod p, c a * e (a * y)

/-- Fourier coefficients of the three-fold count. -/
noncomputable def coef3 (A M L : Finset (ZMod p)) (a : ZMod p) : ℂ :=
  (1 / (p : ℂ)) * starRingEnd ℂ (hat L a) * hat M a * hat A a

lemma F3_eq_trig (A M L : Finset (ZMod p)) (x : ZMod p) :
    ((F3 A M L x : ℝ) : ℂ) = trig (coef3 A M L) x := by
  have h0 : ((F3 A M L x : ℝ) : ℂ) = ∑ b ∈ M, ∑ a' ∈ A, ∑ a : ZMod p,
      (1 / (p : ℂ)) * (e (a * (x + b + a')) * starRingEnd ℂ (hat L a)) := by
    unfold F3 F2
    push_cast
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a' _ => ?_
    rw [ind_eq_sum, Finset.mul_sum]
  rw [h0]
  rw [Finset.sum_congr rfl fun b _ => Finset.sum_comm]
  rw [Finset.sum_comm]
  unfold trig
  refine Finset.sum_congr rfl fun a _ => ?_
  have h1 : ∀ b a' : ZMod p, (1 / (p : ℂ)) * (e (a * (x + b + a')) * starRingEnd ℂ (hat L a)) =
      ((1 / (p : ℂ)) * starRingEnd ℂ (hat L a) * e (a * x)) * (e (a * b) * e (a * a')) := by
    intro b a'
    have : a * (x + b + a') = a * x + a * b + a * a' := by ring
    rw [this, e_add, e_add]; ring
  simp_rw [h1, ← Finset.mul_sum]
  rw [← Finset.sum_mul]
  unfold coef3 hat
  ring

/-- The multiplier of the averaging operator. -/
noncomputable def theta (T : Finset (ZMod p)) (a : ZMod p) : ℂ :=
  hat T a * starRingEnd ℂ (hat T a) / ((T.card : ℂ) ^ 2)

lemma avgT_trig (T : Finset (ZMod p)) (c : ZMod p → ℂ) :
    avgT T (trig c) = trig (fun a => c a * theta T a) := by
  funext x
  unfold avgT trig theta
  have h1 : ∀ t t' : ZMod p, ∑ a : ZMod p, c a * e (a * (x + t - t')) =
      ∑ a : ZMod p, c a * e (a * x) * (e (a * t) * starRingEnd ℂ (e (a * t'))) := by
    intro t t'
    refine Finset.sum_congr rfl fun a _ => ?_
    have : a * (x + t - t') = a * x + a * t - a * t' := by ring
    rw [this, e_sub, e_add]; ring
  simp_rw [h1]
  have h2 : ∑ t ∈ T, ∑ t' ∈ T, ∑ a : ZMod p,
      c a * e (a * x) * (e (a * t) * starRingEnd ℂ (e (a * t'))) =
      ∑ a : ZMod p, c a * e (a * x) * (hat T a * starRingEnd ℂ (hat T a)) := by
    rw [Finset.sum_congr rfl fun t _ => Finset.sum_comm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul]
    unfold hat
    rw [map_sum]
  rw [h2, Finset.sum_div]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

lemma iterate_avgT_trig (T : Finset (ZMod p)) (c : ZMod p → ℂ) (k : ℕ) :
    (avgT T)^[k] (trig c) = trig (fun a => c a * theta T a ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, avgT_trig]
    congr 1
    funext a
    rw [pow_succ]; ring

lemma norm_theta (T : Finset (ZMod p)) (a : ZMod p) :
    ‖theta T a‖ = ‖hat T a‖ ^ 2 / (T.card : ℝ) ^ 2 := by
  unfold theta
  rw [norm_div, norm_mul, RCLike.norm_conj, norm_pow, Complex.norm_natCast]
  ring

lemma norm_theta_le_one (T : Finset (ZMod p)) (a : ZMod p) : ‖theta T a‖ ≤ 1 := by
  rw [norm_theta]
  rcases T.eq_empty_or_nonempty with h | h
  · simp [h]
  have hT0 : (0 : ℝ) < T.card := by exact_mod_cast h.card_pos
  rw [div_le_one (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_hat_le T a) 2

/-- The Fourier step: iterated averages are almost invariant under shifts annihilating the
large spectrum of `T`. -/
lemma fourier_step (A M L T : Finset (ZMod p)) (hT : T.Nonempty) (r k : ℕ)
    (hLM : (L.card : ℝ) ≤ 4 ^ r * M.card) {ν₀ : ℝ} (hν : 0 ≤ ν₀) (w : ZMod p)
    (hw : ∀ a : ZMod p, (T.card : ℝ) ≤ 2 * ‖hat T a‖ → ‖1 - e (a * w)‖ ≤ ν₀) (x : ZMod p) :
    ‖(avgT T)^[k] (fun y => ((F3 A M L y : ℝ) : ℂ)) (x + w) -
        (avgT T)^[k] (fun y => ((F3 A M L y : ℝ) : ℂ)) x‖ ≤
      A.card * (2 ^ r * M.card) * max ν₀ (2 / 4 ^ k) := by
  have hT0 : (0 : ℝ) < T.card := by exact_mod_cast hT.card_pos
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hfun : (fun y => ((F3 A M L y : ℝ) : ℂ)) = trig (coef3 A M L) := by
    funext y; exact F3_eq_trig A M L y
  rw [hfun, iterate_avgT_trig]
  unfold trig
  rw [← Finset.sum_sub_distrib]
  set mx : ℝ := max ν₀ (2 / 4 ^ k) with hmx
  have hterm : ∀ a : ZMod p,
      ‖coef3 A M L a * theta T a ^ k * e (a * (x + w)) - coef3 A M L a * theta T a ^ k * e (a * x)‖ ≤
        ‖coef3 A M L a‖ * mx := by
    intro a
    have h1 : coef3 A M L a * theta T a ^ k * e (a * (x + w)) -
        coef3 A M L a * theta T a ^ k * e (a * x) =
        coef3 A M L a * (theta T a ^ k * e (a * x) * (e (a * w) - 1)) := by
      rw [mul_add, e_add]; ring
    rw [h1, norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [norm_mul, norm_mul, norm_e, mul_one, norm_pow, norm_sub_rev]
    have hθ0 : 0 ≤ ‖theta T a‖ := norm_nonneg _
    have hθ1 := norm_theta_le_one T a
    rcases le_or_gt (T.card : ℝ) (2 * ‖hat T a‖) with hbig | hsmall
    · calc ‖theta T a‖ ^ k * ‖1 - e (a * w)‖ ≤ 1 * ν₀ :=
            mul_le_mul (pow_le_one₀ hθ0 hθ1) (hw a hbig) (norm_nonneg _) (by norm_num)
        _ ≤ mx := by rw [one_mul]; exact le_max_left _ _
    · have h2 : ‖theta T a‖ ≤ 1 / 4 := by
        rw [norm_theta, div_le_iff₀ (by positivity)]
        have h3 : ‖hat T a‖ ≤ T.card / 2 := by linarith
        have h4 : ‖hat T a‖ ^ 2 ≤ ((T.card : ℝ) / 2) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h3 2
        nlinarith
      have h5 : ‖1 - e (a * w)‖ ≤ 2 := by
        refine (norm_sub_le _ _).trans ?_
        rw [norm_one, norm_e]; norm_num
      calc ‖theta T a‖ ^ k * ‖1 - e (a * w)‖ ≤ (1 / 4) ^ k * 2 :=
            mul_le_mul (pow_le_pow_left₀ hθ0 h2 k) h5 (norm_nonneg _) (by positivity)
        _ = 2 / 4 ^ k := by rw [one_div, inv_pow]; ring
        _ ≤ mx := le_max_right _ _
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun a _ => hterm a).trans ?_)
  rw [← Finset.sum_mul]
  have hmx0 : 0 ≤ mx := le_max_of_le_left hν
  refine mul_le_mul_of_nonneg_right ?_ hmx0
  -- bound the sum of the coefficients
  have hcoef : ∀ a : ZMod p, ‖coef3 A M L a‖ ≤ (A.card : ℝ) / p * (‖hat L a‖ * ‖hat M a‖) := by
    intro a
    unfold coef3
    rw [norm_mul, norm_mul, norm_mul, RCLike.norm_conj, norm_div, norm_one,
      Complex.norm_natCast]
    have := norm_hat_le A a
    have h0 : 0 ≤ 1 / (p : ℝ) * ‖hat L a‖ * ‖hat M a‖ := by positivity
    calc 1 / (p : ℝ) * ‖hat L a‖ * ‖hat M a‖ * ‖hat A a‖
        ≤ 1 / (p : ℝ) * ‖hat L a‖ * ‖hat M a‖ * A.card := mul_le_mul_of_nonneg_left this h0
      _ = (A.card : ℝ) / p * (‖hat L a‖ * ‖hat M a‖) := by ring
  refine (Finset.sum_le_sum fun a _ => hcoef a).trans ?_
  rw [← Finset.mul_sum]
  have h6 := sum_norm_hat_mul_le L M (c := 2 ^ r) (by positivity) (by
    have : ((2 : ℝ) ^ r) ^ 2 = 4 ^ r := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [this]; exact hLM)
  calc (A.card : ℝ) / p * ∑ a : ZMod p, ‖hat L a‖ * ‖hat M a‖
      ≤ (A.card : ℝ) / p * (p * (2 ^ r * M.card)) :=
        mul_le_mul_of_nonneg_left h6 (by positivity)
    _ = A.card * (2 ^ r * M.card) := by field_simp

end G16

end ModFourier

section ModAP1

/- # Green 16: almost-periodicity under shifts annihilating a large spectrum -/

open Finset
open scoped Pointwise

namespace G16

variable {p : ℕ} [Fact p.Prime]

/-- Core almost-periodicity statement: there is a large set `T ⊆ S` such that the three-fold count
is almost invariant under any shift `w` annihilating the `1/2`-large spectrum of `T`. -/
theorem ap_core (A M L S : Finset (ZMod p)) (hA : A.Nonempty) (hS : S.Nonempty) (r q k : ℕ)
    (hr : 1 ≤ r) (hq : 1 ≤ q) (hLM : (L.card : ℝ) ≤ 4 ^ r * M.card) :
    ∃ T ⊆ S, T.Nonempty ∧
      (S.card : ℝ) * (A.card : ℝ) ^ (2 * r * (32 * q) ^ 2) ≤
        2 * T.card * ((A + S).card : ℝ) ^ (2 * r * (32 * q) ^ 2) ∧
      ∀ ν₀ : ℝ, 0 ≤ ν₀ → ∀ w : ZMod p,
        (∀ a : ZMod p, (T.card : ℝ) ≤ 2 * ‖hat T a‖ → ‖1 - e (a * w)‖ ≤ ν₀) →
        ∀ x : ZMod p, |F3 A M L (x + w) - F3 A M L x| ≤
          2 * k * ((A.card : ℝ) * M.card / q) + A.card * (2 ^ r * M.card) * max ν₀ (2 / 4 ^ k) := by
  obtain ⟨T, hTS, hcard, hap⟩ := cs_infty A M L S hA r q hr hq hLM
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hTne : T.Nonempty := by
    by_contra hcon
    rw [not_nonempty_iff_eq_empty] at hcon
    rw [hcon] at hcard
    simp only [card_empty, Nat.cast_zero, mul_zero, zero_mul] at hcard
    have h1 : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
    have h2 : (0 : ℝ) < (A.card : ℝ) ^ (2 * r * (32 * q) ^ 2) := by
      have : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
      positivity
    nlinarith
  refine ⟨T, hTS, hTne, hcard, ?_⟩
  intro ν₀ hν w hw x
  set f : ZMod p → ℂ := fun y => ((F3 A M L y : ℝ) : ℂ) with hf
  set ε : ℝ := (A.card : ℝ) * M.card / q with hε
  have hfap : ∀ t ∈ T, ∀ t' ∈ T, ∀ y, ‖f (y + t - t') - f y‖ ≤ ε := by
    intro t ht t' ht' y
    have h1 := hap t ht t' ht' y
    simp only [hf]
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, hε, le_div_iff₀ hq0]
    linarith
  have hH := norm_iterate_avgT_sub_le T hTne f hfap k
  have hF := fourier_step A M L T hTne r k hLM hν w hw x
  have e1 : ((F3 A M L (x + w) - F3 A M L x : ℝ) : ℂ) =
      (f (x + w) - (avgT T)^[k] f (x + w)) + ((avgT T)^[k] f (x + w) - (avgT T)^[k] f x) +
        ((avgT T)^[k] f x - f x) := by
    simp only [hf]; push_cast; ring
  have e2 : |F3 A M L (x + w) - F3 A M L x| = ‖((F3 A M L (x + w) - F3 A M L x : ℝ) : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  rw [e2, e1]
  refine (norm_add_le _ _).trans ?_
  have h3 := hH (x + w)
  have h4 := hH x
  rw [norm_sub_rev] at h3
  have h5 := norm_add_le (f (x + w) - (avgT T)^[k] f (x + w))
    ((avgT T)^[k] f (x + w) - (avgT T)^[k] f x)
  linarith

end G16

end ModAP1

section ModChang1

/- # Green 16: tools for the local Chang lemma -/

open Finset

namespace G16

variable {p : ℕ} [Fact p.Prime]

lemma e_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod p) :
    e (∑ i ∈ s, f i) = ∏ i ∈ s, e (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [e_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, e_add, ih]

lemma norm_one_sub_e_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod p) :
    ‖1 - e (∑ i ∈ s, f i)‖ ≤ ∑ i ∈ s, ‖1 - e (f i)‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [e_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (norm_one_sub_e_add _ _).trans (by linarith)

lemma sum_mem_bohr {ι : Type*} (s : Finset ι) (f : ι → ZMod p) {R : Finset (ZMod p)} {ρ : ℝ}
    (h : ∀ i ∈ s, f i ∈ bohr R ρ) : ∑ i ∈ s, f i ∈ bohr R (s.card * ρ) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, card_empty, Nat.cast_zero, zero_mul]
    exact zero_mem_bohr le_rfl
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, card_insert_of_notMem ha]
    have h1 := ih fun i hi => h i (mem_insert_of_mem hi)
    have h2 := h a (mem_insert_self a s)
    have h3 := add_mem_bohr h2 h1
    have e1 : ((s.card + 1 : ℕ) : ℝ) * ρ = ρ + s.card * ρ := by push_cast; ring
    rw [e1]; exact h3

/-- `‖1 - e (m x)‖ ≤ ‖1 - e x‖` for `m ∈ {-1, 0, 1}`. -/
lemma norm_one_sub_e_int_mul {m : ℤ} (hm : m = -1 ∨ m = 0 ∨ m = 1) (x : ZMod p) :
    ‖1 - e ((m : ZMod p) * x)‖ ≤ ‖1 - e x‖ := by
  rcases hm with rfl | rfl | rfl
  · simp [norm_one_sub_e_neg]
  · simp [e_zero]
  · simp

/-- Lower bound for averages over the product space. -/
lemma sum_prod_space_ge (R T : Finset (ZMod p)) (rS rb : ℝ) (ℓ : ℕ)
    (hTS : T ⊆ bohr R rS) (g : ZMod p → ℝ) (hg : ∀ x, 0 ≤ g x) :
    ((bohr R rb).card : ℝ) ^ ℓ * ∑ x ∈ T, g x ≤
      ∑ y ∈ Fintype.piFinset (fun _ : Fin ℓ => bohr R rb),
        ∑ y₀ ∈ bohr R (rS + ℓ * rb), g (y₀ + ∑ i, y i) := by
  classical
  have h1 : ((bohr R rb).card : ℝ) ^ ℓ * ∑ x ∈ T, g x =
      ∑ _y ∈ Fintype.piFinset (fun _ : Fin ℓ => bohr R rb), ∑ x ∈ T, g x := by
    rw [Finset.sum_const, Fintype.card_piFinset_const, nsmul_eq_mul]; push_cast; ring
  rw [h1]
  refine Finset.sum_le_sum fun y hy => ?_
  rw [Fintype.mem_piFinset] at hy
  set s : ZMod p := ∑ i, y i with hs
  have hsmem : s ∈ bohr R (ℓ * rb) := by
    have := sum_mem_bohr (univ : Finset (Fin ℓ)) y (R := R) (ρ := rb) fun i _ => hy i
    rwa [card_univ, Fintype.card_fin] at this
  have h2 : ∑ x ∈ T, g x = ∑ y₀ ∈ T.image (fun x => x - s), g (y₀ + s) := by
    rw [Finset.sum_image fun a _ b _ h => sub_left_injective h]
    exact Finset.sum_congr rfl fun x _ => by rw [sub_add_cancel]
  rw [h2]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => hg _
  intro y₀ hy₀
  obtain ⟨x, hx, rfl⟩ := mem_image.1 hy₀
  exact sub_mem_bohr (hTS hx) hsmem

/-- Character sums over the product space factor. -/
lemma sum_prod_space_char (Bp Bb : Finset (ZMod p)) (ℓ : ℕ) (σ : ZMod p) :
    ∑ y ∈ Fintype.piFinset (fun _ : Fin ℓ => Bb), ∑ y₀ ∈ Bp, e (σ * (y₀ + ∑ i, y i)) =
      hat Bp σ * hat Bb σ ^ ℓ := by
  have h1 : ∀ y : Fin ℓ → ZMod p, ∑ y₀ ∈ Bp, e (σ * (y₀ + ∑ i, y i)) =
      hat Bp σ * ∏ i, e (σ * y i) := by
    intro y
    unfold hat
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun y₀ _ => ?_
    rw [mul_add, e_add, Finset.mul_sum, e_sum]
  simp_rw [h1]
  rw [← Finset.mul_sum]
  congr 1
  rw [← Finset.prod_univ_sum (fun _ : Fin ℓ => Bb) (fun _ b => e (σ * b))]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rfl

end G16

end ModChang1

section ModChang2

/- # Green 16: Riesz products -/

open Finset

namespace G16

variable {p : ℕ} [Fact p.Prime]

/-- Coefficients of one factor of a Riesz product. -/
noncomputable def kap (c₀ s₀ : ℝ) (u : ZMod p → ℂ) (l : ZMod p) (j : ℤ) : ℂ :=
  if j = 0 then (c₀ : ℂ) else if j = 1 then ((s₀ / 2 : ℝ) : ℂ) * u l
    else ((s₀ / 2 : ℝ) : ℂ) * starRingEnd ℂ (u l)

/-- The index sets for sign patterns supported on `Λ`. -/
def tJ (Λ : Finset (ZMod p)) (l : ZMod p) : Finset ℤ :=
  if l ∈ Λ then ({-1, 0, 1} : Finset ℤ) else {0}

omit [Fact p.Prime] in
lemma mem_tJ_of_mem {Λ : Finset (ZMod p)} {l : ZMod p} (hl : l ∈ Λ) {j : ℤ} (hj : j ∈ tJ Λ l) :
    j = -1 ∨ j = 0 ∨ j = 1 := by
  simpa [tJ, hl] using hj

omit [Fact p.Prime] in
lemma eq_zero_of_mem_tJ {Λ : Finset (ZMod p)} {l : ZMod p} (hl : l ∉ Λ) {j : ℤ}
    (hj : j ∈ tJ Λ l) : j = 0 := by
  simpa [tJ, hl] using hj

omit [Fact p.Prime] in
lemma zero_mem_tJ (Λ : Finset (ZMod p)) (l : ZMod p) : (0 : ℤ) ∈ tJ Λ l := by
  unfold tJ; split_ifs <;> simp

lemma sum_J (g : ℤ → ℂ) : ∑ j ∈ ({-1, 0, 1} : Finset ℤ), g j = g (-1) + g 0 + g 1 := by
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

lemma sum_J_real (g : ℤ → ℝ) : ∑ j ∈ ({-1, 0, 1} : Finset ℤ), g j = g (-1) + g 0 + g 1 := by
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

lemma riesz_factor (c₀ s₀ : ℝ) (u : ZMod p → ℂ) (l z : ZMod p) :
    (((c₀ + s₀ * (u l * e (l * z)).re : ℝ)) : ℂ) =
      ∑ j ∈ ({-1, 0, 1} : Finset ℤ), kap c₀ s₀ u l j * e ((j : ZMod p) * l * z) := by
  rw [sum_J]
  have h1 : kap c₀ s₀ u l (-1) = ((s₀ / 2 : ℝ) : ℂ) * starRingEnd ℂ (u l) := by
    simp [kap]
  have h2 : kap c₀ s₀ u l 0 = (c₀ : ℂ) := by simp [kap]
  have h3 : kap c₀ s₀ u l 1 = ((s₀ / 2 : ℝ) : ℂ) * u l := by simp [kap]
  rw [h1, h2, h3]
  have e1 : (((-1 : ℤ) : ZMod p)) * l * z = -(l * z) := by push_cast; ring
  have e2 : (((0 : ℤ) : ZMod p)) * l * z = 0 := by push_cast; ring
  have e3 : (((1 : ℤ) : ZMod p)) * l * z = l * z := by push_cast; ring
  rw [e1, e2, e3, e_neg, e_zero]
  push_cast
  rw [Complex.re_eq_add_conj, map_mul]
  ring

/-- Expansion of a Riesz product into characters. -/
lemma riesz_expand (Λ : Finset (ZMod p)) (c₀ s₀ : ℝ) (u : ZMod p → ℂ) (z : ZMod p) :
    ((∏ l ∈ Λ, (c₀ + s₀ * (u l * e (l * z)).re) : ℝ) : ℂ) =
      ∑ m ∈ Fintype.piFinset (tJ Λ),
        (∏ l ∈ Λ, kap c₀ s₀ u l (m l)) * e ((∑ l ∈ Λ, (m l : ZMod p) * l) * z) := by
  classical
  set Gz : ZMod p → ℤ → ℂ := fun l j =>
    if l ∈ Λ then kap c₀ s₀ u l j * e ((j : ZMod p) * l * z) else 1 with hGz
  have h1 : ((∏ l ∈ Λ, (c₀ + s₀ * (u l * e (l * z)).re) : ℝ) : ℂ) =
      ∏ l : ZMod p, ∑ j ∈ tJ Λ l, Gz l j := by
    rw [Complex.ofReal_prod, ← Fintype.prod_ite_mem]
    refine Finset.prod_congr rfl fun l _ => ?_
    by_cases hl : l ∈ Λ
    · simp only [hl, if_true, tJ, hGz]
      exact riesz_factor c₀ s₀ u l z
    · simp [hl, tJ, hGz]
  rw [h1, Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  have h2 : ∏ l : ZMod p, Gz l (m l) =
      ∏ l ∈ Λ, (kap c₀ s₀ u l (m l) * e ((m l : ZMod p) * l * z)) := by
    rw [← Fintype.prod_ite_mem Λ
      (fun l => kap c₀ s₀ u l (m l) * e ((m l : ZMod p) * l * z))]
  rw [h2, Finset.prod_mul_distrib, ← e_sum, Finset.sum_mul]

omit [Fact p.Prime] in
lemma norm_kap_sum_le (c₀ s₀ : ℝ) (hc : 0 ≤ c₀) (hs : 0 ≤ s₀) (u : ZMod p → ℂ)
    (hu : ∀ l, ‖u l‖ ≤ 1) (l : ZMod p) :
    ∑ j ∈ ({-1, 0, 1} : Finset ℤ), ‖kap c₀ s₀ u l j‖ ≤ c₀ + s₀ := by
  rw [sum_J_real]
  have h1 : kap c₀ s₀ u l (-1) = ((s₀ / 2 : ℝ) : ℂ) * starRingEnd ℂ (u l) := by
    simp [kap]
  have h2 : kap c₀ s₀ u l 0 = (c₀ : ℂ) := by simp [kap]
  have h3 : kap c₀ s₀ u l 1 = ((s₀ / 2 : ℝ) : ℂ) * u l := by simp [kap]
  rw [h1, h2, h3, norm_mul, norm_mul, RCLike.norm_conj, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hc, abs_of_nonneg (by positivity : 0 ≤ s₀ / 2)]
  have := hu l
  nlinarith [norm_nonneg (u l)]

/-- The total mass of the coefficients of a Riesz product. -/
lemma sum_norm_riesz_coef_le (Λ : Finset (ZMod p)) (c₀ s₀ : ℝ) (hc : 0 ≤ c₀) (hs : 0 ≤ s₀)
    (u : ZMod p → ℂ) (hu : ∀ l, ‖u l‖ ≤ 1) :
    ∑ m ∈ Fintype.piFinset (tJ Λ), ‖∏ l ∈ Λ, kap c₀ s₀ u l (m l)‖ ≤ (c₀ + s₀) ^ Λ.card := by
  classical
  set N : ZMod p → ℤ → ℝ := fun l j => if l ∈ Λ then ‖kap c₀ s₀ u l j‖ else 1 with hN
  have h1 : ∀ m : ZMod p → ℤ, ‖∏ l ∈ Λ, kap c₀ s₀ u l (m l)‖ = ∏ l : ZMod p, N l (m l) := by
    intro m
    rw [norm_prod, ← Fintype.prod_ite_mem Λ (fun l => ‖kap c₀ s₀ u l (m l)‖)]
  simp_rw [h1]
  rw [← Finset.prod_univ_sum]
  have h2 : ∏ l : ZMod p, ∑ j ∈ tJ Λ l, N l j =
      ∏ l ∈ Λ, ∑ j ∈ ({-1, 0, 1} : Finset ℤ), ‖kap c₀ s₀ u l j‖ := by
    rw [← Fintype.prod_ite_mem Λ
      (fun l => ∑ j ∈ ({-1, 0, 1} : Finset ℤ), ‖kap c₀ s₀ u l j‖)]
    refine Finset.prod_congr rfl fun l _ => ?_
    by_cases hl : l ∈ Λ
    · simp [hl, tJ, hN]
    · simp [hl, tJ, hN]
  rw [h2]
  calc ∏ l ∈ Λ, ∑ j ∈ ({-1, 0, 1} : Finset ℤ), ‖kap c₀ s₀ u l j‖
      ≤ ∏ _l ∈ Λ, (c₀ + s₀) :=
        Finset.prod_le_prod (fun l _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
          fun l _ => norm_kap_sum_le c₀ s₀ hc hs u hu l
    _ = (c₀ + s₀) ^ Λ.card := by rw [Finset.prod_const]

end G16

end ModChang2

section ModChang3

/- # Green 16: the size of dissociated sets in a large spectrum -/

open Finset

namespace G16

variable {p : ℕ} [Fact p.Prime]

/-- Membership in the `1/2`-large spectrum of `X`. -/
def Spec (X : Finset (ZMod p)) (a : ZMod p) : Prop := (X.card : ℝ) ≤ 2 * ‖hat X a‖

/-- `Λ` is dissociated modulo the large spectrum of `Bb`. -/
def Diss (Bb Λ : Finset (ZMod p)) : Prop :=
  ∀ m : ZMod p → ℤ, (∀ l ∈ Λ, m l = -1 ∨ m l = 0 ∨ m l = 1) →
    Spec Bb (∑ l ∈ Λ, (m l : ZMod p) * l) → ∀ l ∈ Λ, m l = 0

lemma exp_half_mul_le {v : ℝ} (hv : |v| ≤ 1) :
    Real.exp (1 / 2 * v) ≤ Real.cosh (1 / 2) + Real.sinh (1 / 2) * v := by
  have hv' := abs_le.1 hv
  have ha : (0 : ℝ) ≤ (1 + v) / 2 := by linarith
  have hb : (0 : ℝ) ≤ (1 - v) / 2 := by linarith
  have hab : (1 + v) / 2 + (1 - v) / 2 = 1 := by ring
  have h := convexOn_exp.2 (Set.mem_univ (1 / 2 : ℝ)) (Set.mem_univ (-(1 / 2) : ℝ)) ha hb hab
  simp only [smul_eq_mul] at h
  have e1 : (1 + v) / 2 * (1 / 2) + (1 - v) / 2 * (-(1 / 2)) = 1 / 2 * v := by ring
  rw [e1] at h
  have e2 : Real.cosh (1 / 2) + Real.sinh (1 / 2) * v =
      (1 + v) / 2 * Real.exp (1 / 2) + (1 - v) / 2 * Real.exp (-(1 / 2)) := by
    rw [Real.cosh_eq, Real.sinh_eq]; ring
  rw [e2]; exact h

lemma u_mul_self (z : ℂ) : starRingEnd ℂ z / (‖z‖ : ℂ) * z = (‖z‖ : ℂ) := by
  by_cases hz : z = 0
  · simp [hz]
  · have h1 : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.2 hz).ne'
    have h2 : z * starRingEnd ℂ z = (‖z‖ : ℂ) * (‖z‖ : ℂ) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
    rw [div_mul_eq_mul_div, div_eq_iff h1, mul_comm, h2]

lemma norm_u_le (z : ℂ) : ‖starRingEnd ℂ z / (‖z‖ : ℂ)‖ ≤ 1 := by
  rw [norm_div, RCLike.norm_conj, Complex.norm_real, norm_norm]
  exact div_self_le_one _

/-- The averaged Riesz product is small when `Λ` is dissociated. -/
lemma sum_riesz_le (Λ Bp Bb : Finset (ZMod p)) (ℓ : ℕ) (c₀ s₀ : ℝ) (hc : 0 ≤ c₀)
    (hs : 0 ≤ s₀) (u : ZMod p → ℂ) (hu : ∀ l, ‖u l‖ ≤ 1) (hdiss : Diss Bb Λ) :
    ∑ y ∈ Fintype.piFinset (fun _ : Fin ℓ => Bb), ∑ y₀ ∈ Bp,
        ∏ l ∈ Λ, (c₀ + s₀ * (u l * e (l * (y₀ + ∑ i, y i))).re) ≤
      (Bp.card : ℝ) * ((Bb.card : ℝ) ^ ℓ * c₀ ^ Λ.card +
        ((Bb.card : ℝ) / 2) ^ ℓ * (c₀ + s₀) ^ Λ.card) := by
  classical
  set X : ℝ := ∑ y ∈ Fintype.piFinset (fun _ : Fin ℓ => Bb), ∑ y₀ ∈ Bp,
        ∏ l ∈ Λ, (c₀ + s₀ * (u l * e (l * (y₀ + ∑ i, y i))).re) with hXdef
  set C : (ZMod p → ℤ) → ℂ := fun m => ∏ l ∈ Λ, kap c₀ s₀ u l (m l) with hC
  set σ : (ZMod p → ℤ) → ZMod p := fun m => ∑ l ∈ Λ, (m l : ZMod p) * l with hσ
  have hX : (X : ℂ) =
      ∑ m ∈ Fintype.piFinset (tJ Λ), C m * (hat Bp (σ m) * hat Bb (σ m) ^ ℓ) := by
    rw [hXdef, Complex.ofReal_sum]
    simp_rw [Complex.ofReal_sum, riesz_expand]
    rw [Finset.sum_congr rfl fun y _ => Finset.sum_comm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp_rw [← Finset.mul_sum]
    rw [sum_prod_space_char]
  have hterm : ∀ m ∈ Fintype.piFinset (tJ Λ),
      ‖C m * (hat Bp (σ m) * hat Bb (σ m) ^ ℓ)‖ ≤
        (if m = 0 then (Bp.card : ℝ) * (Bb.card : ℝ) ^ ℓ * c₀ ^ Λ.card else 0) +
          ‖C m‖ * ((Bp.card : ℝ) * ((Bb.card : ℝ) / 2) ^ ℓ) := by
    intro m hm
    rw [Fintype.mem_piFinset] at hm
    rw [norm_mul, norm_mul, norm_pow]
    have hBp := norm_hat_le Bp (σ m)
    by_cases h0 : ∀ l ∈ Λ, m l = 0
    · have hm0 : m = 0 := by
        funext l
        by_cases hl : l ∈ Λ
        · exact h0 l hl
        · exact eq_zero_of_mem_tJ hl (hm l)
      have hCm : ‖C m‖ = c₀ ^ Λ.card := by
        simp only [hC]
        rw [norm_prod]
        have : ∀ l ∈ Λ, ‖kap c₀ s₀ u l (m l)‖ = c₀ := by
          intro l hl
          rw [h0 l hl]
          simp [kap, abs_of_nonneg hc]
        rw [Finset.prod_congr rfl this, Finset.prod_const]
      rw [if_pos hm0, hCm]
      have hBb := norm_hat_le Bb (σ m)
      have h1 : c₀ ^ Λ.card * (‖hat Bp (σ m)‖ * ‖hat Bb (σ m)‖ ^ ℓ) ≤
          c₀ ^ Λ.card * ((Bp.card : ℝ) * (Bb.card : ℝ) ^ ℓ) := by
        gcongr
      have h2 : 0 ≤ c₀ ^ Λ.card * ((Bp.card : ℝ) * ((Bb.card : ℝ) / 2) ^ ℓ) := by positivity
      linarith
    · push Not at h0
      obtain ⟨l, hl, hml⟩ := h0
      have hnot : ¬ Spec Bb (σ m) := fun hsp =>
        hml (hdiss m (fun l hl => mem_tJ_of_mem hl (hm l)) hsp l hl)
      unfold Spec at hnot
      push Not at hnot
      have hBb : ‖hat Bb (σ m)‖ ≤ (Bb.card : ℝ) / 2 := by linarith
      have hm0 : m ≠ 0 := fun h => hml (by rw [h]; rfl)
      rw [if_neg hm0, zero_add]
      gcongr
  have hXle : X ≤ ‖(X : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact le_abs_self _
  calc X ≤ ‖(X : ℂ)‖ := hXle
    _ ≤ ∑ m ∈ Fintype.piFinset (tJ Λ), ‖C m * (hat Bp (σ m) * hat Bb (σ m) ^ ℓ)‖ := by
        rw [hX]; exact norm_sum_le _ _
    _ ≤ ∑ m ∈ Fintype.piFinset (tJ Λ),
          ((if m = 0 then (Bp.card : ℝ) * (Bb.card : ℝ) ^ ℓ * c₀ ^ Λ.card else 0) +
            ‖C m‖ * ((Bp.card : ℝ) * ((Bb.card : ℝ) / 2) ^ ℓ)) := Finset.sum_le_sum hterm
    _ = (∑ m ∈ Fintype.piFinset (tJ Λ),
          (if m = 0 then (Bp.card : ℝ) * (Bb.card : ℝ) ^ ℓ * c₀ ^ Λ.card else 0)) +
          (∑ m ∈ Fintype.piFinset (tJ Λ), ‖C m‖) *
            ((Bp.card : ℝ) * ((Bb.card : ℝ) / 2) ^ ℓ) := by
        rw [Finset.sum_add_distrib, Finset.sum_mul]
    _ ≤ (Bp.card : ℝ) * (Bb.card : ℝ) ^ ℓ * c₀ ^ Λ.card +
          (c₀ + s₀) ^ Λ.card * ((Bp.card : ℝ) * ((Bb.card : ℝ) / 2) ^ ℓ) := by
        apply add_le_add
        · rw [Finset.sum_ite_eq']
          split_ifs
          · exact le_rfl
          · positivity
        · exact mul_le_mul_of_nonneg_right (sum_norm_riesz_coef_le Λ c₀ s₀ hc hs u hu)
            (by positivity)
    _ = (Bp.card : ℝ) * ((Bb.card : ℝ) ^ ℓ * c₀ ^ Λ.card +
          ((Bb.card : ℝ) / 2) ^ ℓ * (c₀ + s₀) ^ Λ.card) := by ring

/-- The key bound for dissociated subsets of a large spectrum. -/
theorem diss_card_bound (R T : Finset (ZMod p)) (rS rb : ℝ) (ℓ : ℕ)
    (hTS : T ⊆ bohr R rS) (hT : T.Nonempty) (hrb : 0 ≤ rb)
    (Λ : Finset (ZMod p)) (hΛ : ∀ l ∈ Λ, Spec T l) (hdiss : Diss (bohr R rb) Λ)
    (hℓ : Λ.card ≤ ℓ) :
    Real.exp ((Λ.card : ℝ) / 8) * T.card ≤ 2 * (bohr R (rS + ℓ * rb)).card := by
  classical
  have hT0 : (0 : ℝ) < T.card := by exact_mod_cast hT.card_pos
  set n : ℕ := Λ.card with hn
  set Bb := bohr R rb with hBb
  set Bp := bohr R (rS + ℓ * rb) with hBp
  have hBb0 : (0 : ℝ) < Bb.card := by exact_mod_cast card_bohr_pos hrb
  set c₀ : ℝ := Real.cosh (1 / 2) with hc₀
  set s₀ : ℝ := Real.sinh (1 / 2) with hs₀
  have hc1 : 1 ≤ c₀ := Real.one_le_cosh _
  have hs0 : 0 ≤ s₀ := Real.sinh_nonneg_iff.2 (by norm_num)
  have hcs : c₀ + s₀ = Real.exp (1 / 2) := Real.cosh_add_sinh _
  have hc8 : c₀ ≤ Real.exp (1 / 8) := by
    have := Real.cosh_le_exp_half_sq (1 / 2)
    have e : ((1 : ℝ) / 2) ^ 2 / 2 = 1 / 8 := by norm_num
    rwa [e] at this
  set u : ZMod p → ℂ := fun l => starRingEnd ℂ (hat T l) / (‖hat T l‖ : ℂ) with hu
  have hu1 : ∀ l, ‖u l‖ ≤ 1 := fun l => norm_u_le _
  have hv : ∀ l z : ZMod p, |(u l * e (l * z)).re| ≤ 1 := by
    intro l z
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, norm_e, mul_one]; exact hu1 l
  set f : ZMod p → ℝ := fun z => ∑ l ∈ Λ, 1 / 2 * (u l * e (l * z)).re with hf
  -- pointwise Riesz bound
  have hfP : ∀ z, Real.exp (f z) ≤ ∏ l ∈ Λ, (c₀ + s₀ * (u l * e (l * z)).re) := by
    intro z
    simp only [hf]
    rw [Real.exp_sum]
    exact Finset.prod_le_prod (fun l _ => (Real.exp_pos _).le)
      fun l _ => exp_half_mul_le (hv l z)
  -- the mean of `f` over `T`
  have hsumf : (n : ℝ) * T.card / 4 ≤ ∑ x ∈ T, f x := by
    simp only [hf]
    rw [Finset.sum_comm]
    have h1 : ∀ l ∈ Λ, (T.card : ℝ) / 4 ≤ ∑ x ∈ T, 1 / 2 * (u l * e (l * x)).re := by
      intro l hl
      have h2 : ∑ x ∈ T, (u l * e (l * x)).re = ‖hat T l‖ := by
        rw [← Complex.re_sum, ← Finset.mul_sum]
        have : u l * ∑ x ∈ T, e (l * x) = (‖hat T l‖ : ℂ) := u_mul_self (hat T l)
        rw [this, Complex.ofReal_re]
      rw [← Finset.mul_sum, h2]
      have := hΛ l hl
      unfold Spec at this
      linarith
    calc (n : ℝ) * T.card / 4 = ∑ _l ∈ Λ, (T.card : ℝ) / 4 := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ _ := Finset.sum_le_sum h1
  have hTf : (T.card : ℝ) * Real.exp ((n : ℝ) / 4) ≤ ∑ x ∈ T, Real.exp (f x) := by
    set Fb : ℝ := (∑ x ∈ T, f x) / T.card with hFb
    have hFb' : (n : ℝ) / 4 ≤ Fb := by
      rw [hFb, le_div_iff₀ hT0]; linarith
    have h1 : ∀ x ∈ T, Real.exp Fb * (1 + (f x - Fb)) ≤ Real.exp (f x) := by
      intro x _
      have h2 := Real.add_one_le_exp (f x - Fb)
      calc Real.exp Fb * (1 + (f x - Fb)) ≤ Real.exp Fb * Real.exp (f x - Fb) :=
            mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
        _ = Real.exp (f x) := by rw [← Real.exp_add]; congr 1; ring
    have h3 : ∑ x ∈ T, Real.exp Fb * (1 + (f x - Fb)) = T.card * Real.exp Fb := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      have : (T.card : ℝ) * Fb = ∑ x ∈ T, f x := by rw [hFb]; field_simp
      rw [this]; ring
    calc (T.card : ℝ) * Real.exp ((n : ℝ) / 4) ≤ T.card * Real.exp Fb := by
          apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hFb') hT0.le
      _ = ∑ x ∈ T, Real.exp Fb * (1 + (f x - Fb)) := h3.symm
      _ ≤ ∑ x ∈ T, Real.exp (f x) := Finset.sum_le_sum h1
  have hlow := sum_prod_space_ge R T rS rb ℓ hTS (fun z => Real.exp (f z))
    fun z => (Real.exp_pos _).le
  have hup := sum_riesz_le Λ Bp Bb ℓ c₀ s₀ (by linarith) hs0 u hu1 hdiss
  have hmid : ∑ y ∈ Fintype.piFinset (fun _ : Fin ℓ => Bb), ∑ y₀ ∈ Bp,
      Real.exp (f (y₀ + ∑ i, y i)) ≤
      ∑ y ∈ Fintype.piFinset (fun _ : Fin ℓ => Bb), ∑ y₀ ∈ Bp,
        ∏ l ∈ Λ, (c₀ + s₀ * (u l * e (l * (y₀ + ∑ i, y i))).re) :=
    Finset.sum_le_sum fun y _ => Finset.sum_le_sum fun y₀ _ => hfP _
  -- combine
  have hBbℓ : (0 : ℝ) < (Bb.card : ℝ) ^ ℓ := by positivity
  have hmain : (Bb.card : ℝ) ^ ℓ * ((T.card : ℝ) * Real.exp ((n : ℝ) / 4)) ≤
      (Bb.card : ℝ) ^ ℓ * ((Bp.card : ℝ) * (2 * Real.exp ((n : ℝ) / 8))) := by
    have h1 : (Bb.card : ℝ) ^ ℓ * ((T.card : ℝ) * Real.exp ((n : ℝ) / 4)) ≤
        (Bp.card : ℝ) * ((Bb.card : ℝ) ^ ℓ * c₀ ^ n +
          ((Bb.card : ℝ) / 2) ^ ℓ * (c₀ + s₀) ^ n) :=
      (mul_le_mul_of_nonneg_left hTf hBbℓ.le).trans (hlow.trans (hmid.trans hup))
    refine h1.trans ?_
    have h2 : c₀ ^ n ≤ Real.exp ((n : ℝ) / 8) := by
      calc c₀ ^ n ≤ Real.exp (1 / 8) ^ n := pow_le_pow_left₀ (by linarith) hc8 n
        _ = Real.exp ((n : ℝ) / 8) := by rw [← Real.exp_nat_mul]; congr 1; ring
    have h3 : ((Bb.card : ℝ) / 2) ^ ℓ * (c₀ + s₀) ^ n ≤
        (Bb.card : ℝ) ^ ℓ * Real.exp ((n : ℝ) / 8) := by
      rw [hcs, div_pow]
      have h4 : Real.exp (1 / 2) ^ n ≤ 2 ^ ℓ := by
        calc Real.exp (1 / 2) ^ n ≤ 2 ^ n := pow_le_pow_left₀ (Real.exp_pos _).le exp_half_le_two n
          _ ≤ 2 ^ ℓ := pow_le_pow_right₀ (by norm_num) hℓ
      have h5 : (1 : ℝ) ≤ Real.exp ((n : ℝ) / 8) := Real.one_le_exp (by positivity)
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      calc (Bb.card : ℝ) ^ ℓ * Real.exp (1 / 2) ^ n ≤ (Bb.card : ℝ) ^ ℓ * 2 ^ ℓ :=
            mul_le_mul_of_nonneg_left h4 hBbℓ.le
        _ ≤ (Bb.card : ℝ) ^ ℓ * Real.exp ((n : ℝ) / 8) * 2 ^ ℓ := by
            have : (0 : ℝ) < (Bb.card : ℝ) ^ ℓ * 2 ^ ℓ := by positivity
            nlinarith
    have h6 : (Bb.card : ℝ) ^ ℓ * c₀ ^ n ≤ (Bb.card : ℝ) ^ ℓ * Real.exp ((n : ℝ) / 8) :=
      mul_le_mul_of_nonneg_left h2 hBbℓ.le
    have hBp0 : (0 : ℝ) ≤ Bp.card := Nat.cast_nonneg _
    calc (Bp.card : ℝ) * ((Bb.card : ℝ) ^ ℓ * c₀ ^ n + ((Bb.card : ℝ) / 2) ^ ℓ * (c₀ + s₀) ^ n)
        ≤ (Bp.card : ℝ) * ((Bb.card : ℝ) ^ ℓ * Real.exp ((n : ℝ) / 8) +
            (Bb.card : ℝ) ^ ℓ * Real.exp ((n : ℝ) / 8)) :=
          mul_le_mul_of_nonneg_left (add_le_add h6 h3) hBp0
      _ = (Bb.card : ℝ) ^ ℓ * ((Bp.card : ℝ) * (2 * Real.exp ((n : ℝ) / 8))) := by ring
  have hfin := le_of_mul_le_mul_left hmain hBbℓ
  have e4 : Real.exp ((n : ℝ) / 4) = Real.exp ((n : ℝ) / 8) * Real.exp ((n : ℝ) / 8) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [e4] at hfin
  have hE : (0 : ℝ) < Real.exp ((n : ℝ) / 8) := Real.exp_pos _
  have : Real.exp ((n : ℝ) / 8) * (Real.exp ((n : ℝ) / 8) * T.card) ≤
      Real.exp ((n : ℝ) / 8) * (2 * Bp.card) := by linarith
  exact le_of_mul_le_mul_left this hE

end G16

end ModChang3

section ModChang4

/- # Green 16: the local Chang lemma -/

open Finset

namespace G16

variable {p : ℕ} [Fact p.Prime]

lemma diss_empty (Bb : Finset (ZMod p)) : Diss Bb ∅ := by
  intro m _ _ l hl
  exact absurd hl (Finset.notMem_empty l)

lemma Diss.subset {Bb Λ Λ' : Finset (ZMod p)} (h : Diss Bb Λ) (hsub : Λ' ⊆ Λ) : Diss Bb Λ' := by
  classical
  intro m hm hsp l hl
  set m' : ZMod p → ℤ := fun x => if x ∈ Λ' then m x else 0 with hm'
  have h1 : ∑ x ∈ Λ, (m' x : ZMod p) * x = ∑ x ∈ Λ', (m x : ZMod p) * x := by
    rw [← Finset.sum_subset hsub (fun x _ hx => by simp [hm', hx])]
    exact Finset.sum_congr rfl fun x hx => by simp [hm', hx]
  have h2 := h m' (fun x _ => by
    by_cases hx : x ∈ Λ'
    · simp only [hm', hx, if_true]; exact hm x hx
    · simp [hm', hx]) (by rw [h1]; exact hsp) l (hsub hl)
  simpa [hm', hl] using h2

/-- The **local Chang lemma**: the large spectrum of a dense subset `T` of a Bohr set is
annihilated by a Bohr set of small rank. -/
theorem local_chang (R T : Finset (ZMod p)) (rS rb : ℝ) (n₀ : ℕ) (W₀ : Finset (ZMod p))
    (ν₀ : ℝ) (hν : 0 ≤ ν₀) (hrb : 0 ≤ rb) (hTS : T ⊆ bohr R rS) (hT : T.Nonempty)
    (hτ : 2 * ((bohr R (rS + (n₀ + 1 : ℕ) * rb)).card : ℝ) <
      Real.exp (((n₀ + 1 : ℕ) : ℝ) / 8) * T.card)
    (hann : ∀ σ : ZMod p, Spec (bohr R rb) σ → ∀ w ∈ W₀, ‖1 - e (σ * w)‖ ≤ ν₀ / 2) :
    ∃ Λ : Finset (ZMod p), Λ.card ≤ n₀ ∧ ∀ a : ZMod p, Spec T a → ∀ w ∈ W₀,
      w ∈ bohr Λ (ν₀ / (2 * (n₀ + 1))) → ‖1 - e (a * w)‖ ≤ ν₀ := by
  classical
  set Δ : Finset (ZMod p) := univ.filter (Spec T) with hΔ
  set 𝔉 : Finset (Finset (ZMod p)) := Δ.powerset.filter (Diss (bohr R rb)) with h𝔉
  have h𝔉ne : 𝔉.Nonempty :=
    ⟨∅, mem_filter.2 ⟨mem_powerset.2 (empty_subset _), diss_empty _⟩⟩
  obtain ⟨Λ, hΛmem, hΛmax⟩ := Finset.exists_max_image 𝔉 Finset.card h𝔉ne
  have hΛsub : Λ ⊆ Δ := mem_powerset.1 (mem_filter.1 hΛmem).1
  have hΛdiss : Diss (bohr R rb) Λ := (mem_filter.1 hΛmem).2
  have hΛspec : ∀ l ∈ Λ, Spec T l := fun l hl => (mem_filter.1 (hΛsub hl)).2
  have hcard : Λ.card ≤ n₀ := by
    by_contra hcon
    push Not at hcon
    obtain ⟨Λ₀, hΛ₀sub, hΛ₀card⟩ :=
      Finset.exists_subset_card_eq (show n₀ + 1 ≤ Λ.card by omega)
    have := diss_card_bound R T rS rb (n₀ + 1) hTS hT hrb Λ₀
      (fun l hl => hΛspec l (hΛ₀sub hl)) (hΛdiss.subset hΛ₀sub) (by omega)
    rw [hΛ₀card] at this
    linarith
  refine ⟨Λ, hcard, ?_⟩
  intro a ha w hw hwΛ
  have hn1 : (0 : ℝ) < 2 * ((n₀ : ℝ) + 1) := by positivity
  by_cases haΛ : a ∈ Λ
  · have h1 := mem_bohr.1 hwΛ a haΛ
    have h2 : ν₀ / (2 * ((n₀ : ℝ) + 1)) ≤ ν₀ :=
      div_le_self hν (by linarith [(Nat.cast_nonneg n₀ : (0 : ℝ) ≤ n₀)])
    linarith
  · have hins : insert a Λ ∈ Δ.powerset :=
      mem_powerset.2 (insert_subset (mem_filter.2 ⟨mem_univ _, ha⟩) hΛsub)
    have hnd : ¬ Diss (bohr R rb) (insert a Λ) := by
      intro hd
      have := hΛmax (insert a Λ) (mem_filter.2 ⟨hins, hd⟩)
      rw [card_insert_of_notMem haΛ] at this
      omega
    unfold Diss at hnd
    push Not at hnd
    obtain ⟨m, hmJ, hsp, l, hl, hml⟩ := hnd
    rw [Finset.sum_insert haΛ] at hsp
    have hma : m a ≠ 0 := by
      intro h0
      rw [h0] at hsp
      simp only [Int.cast_zero, zero_mul, zero_add] at hsp
      have hl' : l ∈ Λ := by
        rcases mem_insert.1 hl with h | h
        · rw [h] at hml; exact absurd h0 hml
        · exact h
      exact hml (hΛdiss m (fun x hx => hmJ x (mem_insert_of_mem hx)) hsp l hl')
    set σ : ZMod p := (m a : ZMod p) * a + ∑ x ∈ Λ, (m x : ZMod p) * x with hσ
    have h1 := hann σ hsp w hw
    have h2 : (m a : ZMod p) * (a * w) = σ * w + ∑ x ∈ Λ, -((m x : ZMod p) * (x * w)) := by
      rw [hσ, add_mul, Finset.sum_mul, Finset.sum_neg_distrib]
      simp_rw [mul_assoc]
      ring
    have h3 : ‖1 - e ((m a : ZMod p) * (a * w))‖ ≤
        ν₀ / 2 + ∑ _x ∈ Λ, ν₀ / (2 * ((n₀ : ℝ) + 1)) := by
      rw [h2]
      refine (norm_one_sub_e_add _ _).trans
        (add_le_add h1 ((norm_one_sub_e_sum _ _).trans (Finset.sum_le_sum fun x hx => ?_)))
      rw [norm_one_sub_e_neg]
      exact (norm_one_sub_e_int_mul (hmJ x (mem_insert_of_mem hx)) _).trans
        (mem_bohr.1 hwΛ x hx)
    have h4 : ‖1 - e (a * w)‖ = ‖1 - e ((m a : ZMod p) * (a * w))‖ := by
      rcases hmJ a (mem_insert_self a Λ) with h | h | h
      · rw [h]; simp [norm_one_sub_e_neg]
      · exact absurd h hma
      · rw [h]; simp
    rw [h4]
    refine h3.trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have h5 : (Λ.card : ℝ) ≤ (n₀ : ℝ) + 1 := by exact_mod_cast (by omega : Λ.card ≤ n₀ + 1)
    have h6 : (Λ.card : ℝ) * (ν₀ / (2 * ((n₀ : ℝ) + 1))) ≤ ν₀ / 2 := by
      rw [← mul_div_assoc, div_le_iff₀ hn1]
      nlinarith
    linarith

/-- The large spectrum of a regular Bohr set is annihilated by a narrower copy. -/
lemma spec_bohr_annihilate (R : Finset (ZMod p)) (rb κ η : ℝ) (hrb : 0 ≤ rb) (hκ : 0 ≤ κ)
    (hη : 0 ≤ η) (hreg : Reg R rb κ η) (σ : ZMod p) (hσ : Spec (bohr R rb) σ) (w : ZMod p)
    (hw : w ∈ bohr R (κ * rb)) : ‖1 - e (σ * w)‖ ≤ 4 * η := by
  classical
  set B := bohr R rb with hB
  set B' := B.image (fun y => y + w) with hB'
  have hB0 : (0 : ℝ) < B.card := by exact_mod_cast card_bohr_pos hrb
  have hcardB' : B'.card = B.card := card_image_of_injective _ (add_left_injective w)
  have h1 : ∑ y ∈ B, e (σ * (y + w)) = ∑ y ∈ B', e (σ * y) := by
    rw [hB', Finset.sum_image fun a _ b _ h => add_left_injective w h]
  have key : hat B σ * (1 - e (σ * w)) = ∑ y ∈ B \ B', e (σ * y) - ∑ y ∈ B' \ B, e (σ * y) := by
    rw [Finset.sum_sdiff_sub_sum_sdiff, ← h1]
    unfold hat
    rw [mul_sub, mul_one, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun y _ => by rw [mul_add, e_add]
  have hsub : B' \ B ⊆ bohr R (rb + κ * rb) \ B := by
    intro y hy
    rw [mem_sdiff] at hy ⊢
    refine ⟨?_, hy.2⟩
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hy.1
    exact add_mem_bohr hx hw
  have hc1 : ((B' \ B).card : ℝ) ≤ η * B.card := by
    have h2 : ((B' \ B).card : ℝ) ≤ ((bohr R (rb + κ * rb) \ B).card : ℝ) := by
      exact_mod_cast card_le_card hsub
    have h3 : (bohr R (rb + κ * rb) \ B).card = (bohr R (rb + κ * rb)).card - B.card :=
      card_sdiff_of_subset (bohr_mono (by nlinarith))
    have h4 : B.card ≤ (bohr R (rb + κ * rb)).card := card_bohr_mono (by nlinarith)
    have h5 : ((bohr R (rb + κ * rb) \ B).card : ℝ) =
        ((bohr R (rb + κ * rb)).card : ℝ) - B.card := by
      rw [h3, Nat.cast_sub h4]
    have h6 := hreg.card_add_le hη (by nlinarith : 0 ≤ κ * rb) le_rfl
    linarith
  have hc2 : (B \ B').card = (B' \ B).card := card_sdiff_comm hcardB'.symm
  have hnorm : ‖hat B σ * (1 - e (σ * w))‖ ≤ 2 * (η * B.card) := by
    rw [key]
    refine (norm_sub_le _ _).trans ?_
    have n1 : ‖∑ y ∈ B \ B', e (σ * y)‖ ≤ (B \ B').card := by
      refine (norm_sum_le _ _).trans ?_
      simp [norm_e]
    have n2 : ‖∑ y ∈ B' \ B, e (σ * y)‖ ≤ (B' \ B).card := by
      refine (norm_sum_le _ _).trans ?_
      simp [norm_e]
    rw [hc2] at n1
    linarith
  rw [norm_mul] at hnorm
  unfold Spec at hσ
  have hpos : 0 ≤ ‖1 - e (σ * w)‖ := norm_nonneg _
  by_contra hcon
  push Not at hcon
  have : (B.card : ℝ) / 2 * ‖1 - e (σ * w)‖ ≤ ‖hat B σ‖ * ‖1 - e (σ * w)‖ :=
    mul_le_mul_of_nonneg_right (by linarith) hpos
  nlinarith

end G16

end ModChang4

section ModAP2

/- # Green 16: `L^∞` almost-periodicity with Bohr sets -/

open Finset
open scoped Pointwise

namespace G16

variable {p : ℕ} [Fact p.Prime]

/-- Number of convolution powers. -/
def kk (Lg : ℕ) : ℕ := Lg + 4

/-- Accuracy parameter of the Croot–Sisask step. -/
def qq (Lg : ℕ) : ℕ := 120 * kk Lg

/-- Number of samples. -/
def mm (Lg : ℕ) : ℕ := 2 * Lg * (32 * qq Lg) ^ 2

/-- Rank increment. -/
def n0 (Lg : ℕ) : ℕ := 8 * (Lg * mm Lg + 3)

/-- Accuracy of the annihilation of the spectrum. -/
noncomputable def nu0 (Lg : ℕ) : ℝ := 1 / (60 * 2 ^ Lg)

lemma nu0_pos (Lg : ℕ) : 0 < nu0 Lg := by unfold nu0; positivity

lemma two_pow_lt_exp (N : ℕ) : (2 : ℝ) ^ N ≤ Real.exp N := by
  have h1 : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.exp_one_gt_d9
    linarith
  calc (2 : ℝ) ^ N ≤ Real.exp 1 ^ N := pow_le_pow_left₀ (by norm_num) h1 N
    _ = Real.exp N := by rw [← Real.exp_nat_mul, mul_one]

/-- **`L^∞` almost-periodicity relative to Bohr sets.** -/
theorem ap_bohr (Lg : ℕ) (hLg : 1 ≤ Lg) (R : Finset (ZMod p)) (rS : ℝ) (hrS : 0 < rS)
    (κ η : ℝ) (hκ : 0 < κ) (hη : 0 ≤ η) (hη1 : η ≤ 1) (hη8 : 4 * η ≤ nu0 Lg / 2)
    (hregS : Reg R rS κ η) (A M L : Finset (ZMod p)) (hA : A.Nonempty)
    (hAS : ((A + bohr R rS).card : ℝ) ≤ 2 ^ Lg * A.card)
    (hLM : (L.card : ℝ) ≤ 2 ^ Lg * M.card)
    (rb : ℝ) (hrb : 0 < rb) (hrb' : ((n0 Lg + 1 : ℕ) : ℝ) * rb ≤ κ * rS)
    (hregb : Reg R rb κ η) :
    ∃ Λ : Finset (ZMod p), Λ.card ≤ n0 Lg ∧
      ∀ w ∈ bohr R (κ * rb), w ∈ bohr Λ (nu0 Lg / (2 * ((n0 Lg : ℝ) + 1))) →
        ∀ x : ZMod p, |F3 A M L (x + w) - F3 A M L x| ≤ (A.card : ℝ) * M.card / 20 := by
  classical
  have hS : (bohr R rS).Nonempty := ⟨0, zero_mem_bohr hrS.le⟩
  have hA0 : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have hM0 : (0 : ℝ) ≤ M.card := Nat.cast_nonneg _
  have h24 : (2 : ℝ) ^ Lg ≤ 4 ^ Lg := pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have hLM' : (L.card : ℝ) ≤ 4 ^ Lg * M.card :=
    hLM.trans (mul_le_mul_of_nonneg_right h24 hM0)
  have hq1 : 1 ≤ qq Lg := by unfold qq kk; omega
  obtain ⟨T, hTS, hTne, hcard, hap⟩ :=
    ap_core A M L (bohr R rS) hA hS Lg (qq Lg) (kk Lg) hLg hq1 hLM'
  have hT0 : (0 : ℝ) < T.card := by exact_mod_cast hTne.card_pos
  have hmm : 2 * Lg * (32 * qq Lg) ^ 2 = mm Lg := rfl
  rw [hmm] at hcard
  -- `|S| ≤ 2 * 2^(Lg m) |T|`
  have hST : ((bohr R rS).card : ℝ) ≤ 2 * (2 : ℝ) ^ (Lg * mm Lg) * T.card := by
    have h1 : (((A + bohr R rS).card : ℝ)) ^ mm Lg ≤ ((2 : ℝ) ^ Lg * A.card) ^ mm Lg :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hAS _
    have h2 : ((bohr R rS).card : ℝ) * (A.card : ℝ) ^ mm Lg ≤
        2 * T.card * (((2 : ℝ) ^ Lg * A.card) ^ mm Lg) :=
      hcard.trans (mul_le_mul_of_nonneg_left h1 (by positivity))
    rw [mul_pow, ← pow_mul] at h2
    have hAm : (0 : ℝ) < (A.card : ℝ) ^ mm Lg := by positivity
    have h3 : ((bohr R rS).card : ℝ) * (A.card : ℝ) ^ mm Lg ≤
        (2 * (2 : ℝ) ^ (Lg * mm Lg) * T.card) * (A.card : ℝ) ^ mm Lg := by
      calc _ ≤ 2 * T.card * ((2 : ℝ) ^ (Lg * mm Lg) * (A.card : ℝ) ^ mm Lg) := h2
        _ = _ := by ring
    exact le_of_mul_le_mul_right h3 hAm
  -- the hypothesis of the local Chang lemma
  have hτ : 2 * ((bohr R (rS + (n0 Lg + 1 : ℕ) * rb)).card : ℝ) <
      Real.exp (((n0 Lg + 1 : ℕ) : ℝ) / 8) * T.card := by
    have h1 : ((bohr R (rS + (n0 Lg + 1 : ℕ) * rb)).card : ℝ) ≤ (1 + η) * (bohr R rS).card :=
      hregS.card_add_le hη (by positivity) hrb'
    have h2 : ((bohr R (rS + (n0 Lg + 1 : ℕ) * rb)).card : ℝ) ≤ 2 * (bohr R rS).card :=
      h1.trans (mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _))
    have h3 : 2 * ((bohr R (rS + (n0 Lg + 1 : ℕ) * rb)).card : ℝ) ≤
        (2 : ℝ) ^ (Lg * mm Lg + 3) * T.card := by
      have e : (2 : ℝ) ^ (Lg * mm Lg + 3) = 8 * 2 ^ (Lg * mm Lg) := by rw [pow_add]; ring
      rw [e]; linarith
    have h4 : (2 : ℝ) ^ (Lg * mm Lg + 3) < Real.exp (((n0 Lg + 1 : ℕ) : ℝ) / 8) := by
      refine lt_of_le_of_lt (two_pow_lt_exp _) (Real.exp_lt_exp.2 ?_)
      unfold n0
      push_cast
      linarith
    exact lt_of_le_of_lt h3 (mul_lt_mul_of_pos_right h4 hT0)
  have hann : ∀ σ : ZMod p, Spec (bohr R rb) σ → ∀ w ∈ bohr R (κ * rb),
      ‖1 - e (σ * w)‖ ≤ nu0 Lg / 2 := by
    intro σ hσ w hw
    exact (spec_bohr_annihilate R rb κ η hrb.le hκ.le hη hregb σ hσ w hw).trans hη8
  obtain ⟨Λ, hΛcard, hΛ⟩ := local_chang R T rS rb (n0 Lg) (bohr R (κ * rb)) (nu0 Lg)
    (nu0_pos Lg).le hrb.le hTS hTne hτ hann
  refine ⟨Λ, hΛcard, fun w hw hwΛ x => ?_⟩
  have h := hap (nu0 Lg) (nu0_pos Lg).le w (fun a ha => hΛ a ha w hw hwΛ) x
  refine h.trans ?_
  -- numerics
  have hk0 : (0 : ℝ) < kk Lg := by unfold kk; push_cast; positivity
  have e1 : 2 * (kk Lg : ℝ) * ((A.card : ℝ) * M.card / (qq Lg : ℕ)) =
      (A.card : ℝ) * M.card / 60 := by
    unfold qq; push_cast; field_simp; ring
  have h2L : (0 : ℝ) < 2 ^ Lg := by positivity
  have e2 : (2 : ℝ) ^ Lg * max (nu0 Lg) (2 / 4 ^ kk Lg) ≤ 1 / 60 := by
    rw [mul_max_of_nonneg _ _ h2L.le]
    apply max_le
    · unfold nu0; rw [le_div_iff₀ (by norm_num)]; field_simp; norm_num
    · unfold kk
      have e3 : (4 : ℝ) ^ (Lg + 4) = 256 * (2 ^ Lg * 2 ^ Lg) := by
        rw [pow_add, ← mul_pow]; norm_num; ring
      rw [e3]
      have h1 : (1 : ℝ) ≤ 2 ^ Lg := one_le_pow₀ (by norm_num)
      have e5 : (2 : ℝ) ^ Lg * (2 / (256 * (2 ^ Lg * 2 ^ Lg))) = 1 / (128 * 2 ^ Lg) := by
        field_simp; ring
      rw [e5, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
  have hAM : (0 : ℝ) ≤ (A.card : ℝ) * M.card := by positivity
  have e4 : (A.card : ℝ) * (2 ^ Lg * M.card) * max (nu0 Lg) (2 / 4 ^ kk Lg) ≤
      (A.card : ℝ) * M.card / 60 := by
    calc (A.card : ℝ) * (2 ^ Lg * M.card) * max (nu0 Lg) (2 / 4 ^ kk Lg)
        = (A.card : ℝ) * M.card * (2 ^ Lg * max (nu0 Lg) (2 / 4 ^ kk Lg)) := by ring
      _ ≤ (A.card : ℝ) * M.card * (1 / 60) := mul_le_mul_of_nonneg_left e2 hAM
      _ = (A.card : ℝ) * M.card / 60 := by ring
  rw [e1]
  linarith

end G16

end ModAP2

section ModStep1

/- # Green 16: averaging lemmas for the density increment -/

open Finset
open scoped Pointwise

namespace G16

variable {p : ℕ} [Fact p.Prime]

/-- The part of `A - c` inside `X`. -/
def piece (A X : Finset (ZMod p)) (c : ZMod p) : Finset (ZMod p) := X.filter fun x => c + x ∈ A

lemma mem_piece {A X : Finset (ZMod p)} {c x : ZMod p} :
    x ∈ piece A X c ↔ x ∈ X ∧ c + x ∈ A := mem_filter

lemma piece_subset (A X : Finset (ZMod p)) (c : ZMod p) : piece A X c ⊆ X := filter_subset _ _

lemma card_piece_le (A X : Finset (ZMod p)) (c : ZMod p) : (piece A X c).card ≤ X.card :=
  card_le_card (piece_subset A X c)

/-- Averaging over translates inside a regular Bohr set. -/
lemma sum_card_piece_ge (A R : Finset (ZMod p)) (ρ κ η : ℝ) (hη : 0 ≤ η) (hκρ : 0 ≤ κ * ρ)
    (hreg : Reg R ρ κ η) (t s : ZMod p) (X : Finset (ZMod p))
    (hsX : ∀ x ∈ X, s + x ∈ bohr R (κ * ρ)) :
    (((piece A (bohr R ρ) t).card : ℝ) - η * (bohr R ρ).card) * X.card ≤
      ∑ u ∈ bohr R ρ, ((piece A X (t + u + s)).card : ℝ) := by
  classical
  set B := bohr R ρ with hB
  set Bm := bohr R (ρ - κ * ρ) with hBm
  have hBmB : Bm ⊆ B := bohr_mono (by linarith)
  -- the inner count for each `x`
  have hinner : ∀ x ∈ X, ((piece A B t).card : ℝ) - η * B.card ≤
      ((B.filter fun u => t + u + s + x ∈ A).card : ℝ) := by
    intro x hx
    have h1 : (piece A Bm t).card ≤ (B.filter fun u => t + u + s + x ∈ A).card := by
      refine card_le_card_of_injOn (fun v => v - (s + x)) ?_ ?_
      · intro v hv
        have hv' := mem_piece.1 (mem_coe.1 hv)
        refine mem_coe.2 (mem_filter.2 ⟨?_, ?_⟩)
        · have h7 : v - (s + x) ∈ bohr R ((ρ - κ * ρ) + κ * ρ) :=
            sub_mem_bohr hv'.1 (hsX x hx)
          rwa [sub_add_cancel] at h7
        · have : t + (v - (s + x)) + s + x = t + v := by ring
          rw [this]; exact hv'.2
      · intro v _ v' _ h
        simpa using h
    have h2 : (piece A B t).card ≤ (piece A Bm t).card + (B \ Bm).card := by
      have : piece A B t ⊆ piece A Bm t ∪ (B \ Bm) := by
        intro v hv
        have hv' := mem_piece.1 hv
        by_cases hvm : v ∈ Bm
        · exact mem_union_left _ (mem_piece.2 ⟨hvm, hv'.2⟩)
        · exact mem_union_right _ (mem_sdiff.2 ⟨hv'.1, hvm⟩)
      exact (card_le_card this).trans (card_union_le _ _)
    have h3 : ((B \ Bm).card : ℝ) = (B.card : ℝ) - Bm.card := by
      rw [card_sdiff_of_subset hBmB, Nat.cast_sub (card_le_card hBmB)]
    have h4 : (B.card : ℝ) ≤ (1 + η) * Bm.card := hreg.card_le_sub hη hκρ le_rfl
    have h5 : (Bm.card : ℝ) ≤ B.card := by exact_mod_cast card_le_card hBmB
    have h1' : ((piece A Bm t).card : ℝ) ≤ ((B.filter fun u => t + u + s + x ∈ A).card : ℝ) := by
      exact_mod_cast h1
    have h2' : ((piece A B t).card : ℝ) ≤ (piece A Bm t).card + (B \ Bm).card := by
      exact_mod_cast h2
    nlinarith
  have hswap : ∑ u ∈ B, ((piece A X (t + u + s)).card : ℝ) =
      ∑ x ∈ X, ((B.filter fun u => t + u + s + x ∈ A).card : ℝ) := by
    have e1 : ∀ u ∈ B, ((piece A X (t + u + s)).card : ℝ) =
        ∑ x ∈ X, if t + u + s + x ∈ A then (1 : ℝ) else 0 := by
      intro u _
      unfold piece
      rw [Finset.card_filter]; push_cast; rfl
    have e2 : ∀ x ∈ X, ((B.filter fun u => t + u + s + x ∈ A).card : ℝ) =
        ∑ u ∈ B, if t + u + s + x ∈ A then (1 : ℝ) else 0 := by
      intro x _
      rw [Finset.card_filter]; push_cast; rfl
    rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Finset.sum_comm]
  rw [hswap]
  calc (((piece A B t).card : ℝ) - η * B.card) * X.card
      = ∑ _x ∈ X, (((piece A B t).card : ℝ) - η * B.card) := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ _ := Finset.sum_le_sum hinner

lemma sum_ind_shift (W L : Finset (ZMod p)) (c : ZMod p) :
    ∑ w ∈ W, ind L (w + c) = ∑ l ∈ L, ind W (l - c) := by
  classical
  have e1 : ∀ w ∈ W, ind L (w + c) = ∑ l ∈ L, if l = w + c then (1 : ℝ) else 0 := by
    intro w _
    rw [Finset.sum_ite_eq']; rfl
  have e2 : ∀ l ∈ L, ind W (l - c) = ∑ w ∈ W, if w = l - c then (1 : ℝ) else 0 := by
    intro l _
    rw [Finset.sum_ite_eq']; rfl
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun w _ => ?_
  have : l = w + c ↔ w = l - c := by
    constructor
    · intro h; rw [h]; ring
    · intro h; rw [h]; ring
  simp only [this]

/-- From almost-periodicity to a density increment for `M` on a translate of `W`. -/
lemma incr_from_ap (Y M L W : Finset (ZMod p)) (hY : Y.Nonempty)
    (hfull : ∀ a ∈ Y, ∀ b ∈ M, a + b ∈ L)
    (hap : ∀ w ∈ W, |F3 Y M L (0 + w) - F3 Y M L 0| ≤ (Y.card : ℝ) * M.card / 20) :
    ∃ v : ZMod p, (19 / 20 : ℝ) * M.card * W.card ≤
      ((M.filter fun b => v - b ∈ W).card : ℝ) * L.card := by
  classical
  have hY0 : (0 : ℝ) < Y.card := by exact_mod_cast hY.card_pos
  have hF0 : F3 Y M L 0 = (Y.card : ℝ) * M.card := by
    unfold F3 F2
    have : ∀ b ∈ M, ∑ a ∈ Y, ind L (0 + b + a) = Y.card := by
      intro b hb
      have : ∀ a ∈ Y, ind L (0 + b + a) = 1 := by
        intro a ha
        have h := hfull a ha b hb
        have e : 0 + b + a = a + b := by ring
        rw [e]; unfold ind; rw [if_pos h]
      rw [Finset.sum_congr rfl this]; simp
    rw [Finset.sum_congr rfl this]; simp; ring
  have hFw : ∀ w ∈ W, (19 / 20 : ℝ) * (Y.card * M.card) ≤ F3 Y M L w := by
    intro w hw
    have h := (abs_le.1 (hap w hw)).1
    rw [zero_add, hF0] at h
    linarith
  set g : ZMod p → ℝ := fun v => ((M.filter fun b => v - b ∈ W).card : ℝ) with hg
  have hsumW : ∑ w ∈ W, F3 Y M L w = ∑ a ∈ Y, ∑ l ∈ L, g (l - a) := by
    unfold F3 F2
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl fun b _ => Finset.sum_comm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    have e1 : ∀ b ∈ M, ∑ w ∈ W, ind L (w + b + a) = ∑ l ∈ L, ind W (l - a - b) := by
      intro b _
      have := sum_ind_shift W L (b + a)
      have e2 : ∀ w : ZMod p, w + (b + a) = w + b + a := fun w => by ring
      have e3 : ∀ l : ZMod p, l - (b + a) = l - a - b := fun l => by ring
      simp only [e2, e3] at this
      exact this
    rw [Finset.sum_congr rfl e1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [hg]
    rw [Finset.card_filter]
    push_cast
    rfl
  have hlow : (19 / 20 : ℝ) * (Y.card * M.card) * W.card ≤ ∑ w ∈ W, F3 Y M L w := by
    calc (19 / 20 : ℝ) * (Y.card * M.card) * W.card
        = ∑ _w ∈ W, (19 / 20 : ℝ) * (Y.card * M.card) := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ _ := Finset.sum_le_sum hFw
  by_contra hcon
  push Not at hcon
  have hgl : ∀ a ∈ Y, ∀ l ∈ L, g (l - a) * L.card < (19 / 20 : ℝ) * M.card * W.card :=
    fun a _ l _ => hcon (l - a)
  rcases L.eq_empty_or_nonempty with hL | hL
  · have h0 := hcon 0
    subst hL
    simp only [card_empty, Nat.cast_zero, mul_zero, Finset.sum_empty, Finset.sum_const_zero]
      at h0 hsumW
    rw [hsumW] at hlow
    nlinarith
  · have hL0 : (0 : ℝ) < L.card := by exact_mod_cast hL.card_pos
    have h1 : (∑ a ∈ Y, ∑ l ∈ L, g (l - a)) * L.card <
        ∑ _a ∈ Y, ∑ _l ∈ L, (19 / 20 : ℝ) * M.card * W.card := by
      rw [Finset.sum_mul]
      refine Finset.sum_lt_sum_of_nonempty hY fun a ha => ?_
      rw [Finset.sum_mul]
      exact Finset.sum_lt_sum_of_nonempty hL fun l hl => hgl a ha l hl
    simp only [Finset.sum_const, nsmul_eq_mul] at h1
    rw [← hsumW] at h1
    have h2 : (19 / 20 : ℝ) * (Y.card * M.card) * W.card * L.card ≤
        (∑ w ∈ W, F3 Y M L w) * L.card := mul_le_mul_of_nonneg_right hlow hL0.le
    nlinarith

end G16

end ModStep1

section ModStep2

/- # Green 16: density increments from almost-periodicity -/

open Finset
open scoped Pointwise

namespace G16

variable {p : ℕ} [Fact p.Prime]

/-- The regularity tolerance. -/
noncomputable def etaS (Lg : ℕ) : ℝ := nu0 Lg / 8

/-- The regularity scale. -/
noncomputable def kapS (Lg D : ℕ) : ℝ := etaS Lg / (84 * D)

lemma etaS_pos (Lg : ℕ) : 0 < etaS Lg := by unfold etaS; have := nu0_pos Lg; positivity

lemma nu0_le (Lg : ℕ) : nu0 Lg ≤ 1 / 60 := by
  unfold nu0
  have h1 : (1 : ℝ) ≤ 2 ^ Lg := one_le_pow₀ (by norm_num)
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

lemma etaS_le (Lg : ℕ) : etaS Lg ≤ 1 / 480 := by
  unfold etaS; have := nu0_le Lg; linarith

lemma kapS_pos (Lg D : ℕ) (hD : 1 ≤ D) : 0 < kapS Lg D := by
  unfold kapS
  have := etaS_pos Lg
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD
  positivity

lemma kapS_le (Lg D : ℕ) (hD : 1 ≤ D) : kapS Lg D ≤ 1 / 40320 := by
  unfold kapS
  have h1 := etaS_le Lg
  have h2 := etaS_pos Lg
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

/-- A density increment for `M` on a translate of a new Bohr set, obtained from
almost-periodicity. -/
theorem ap_incr (Lg D : ℕ) (hLg : 1 ≤ Lg) (hD : 1 ≤ D) (Γ : Finset (ZMod p))
    (hΓ : Γ.card + n0 Lg ≤ D) (ρ₁ : ℝ) (hρ₁ : 0 < ρ₁)
    (hreg : Reg Γ ρ₁ (kapS Lg D) (etaS Lg))
    (Y M L : Finset (ZMod p)) (hY : Y.Nonempty) (hYsub : Y ⊆ bohr Γ ρ₁)
    (hYd : 2 * ((bohr Γ ρ₁).card : ℝ) ≤ 2 ^ Lg * Y.card)
    (hLM : (L.card : ℝ) ≤ 2 ^ Lg * M.card) (hfull : ∀ a ∈ Y, ∀ b ∈ M, a + b ∈ L) :
    ∃ (Λ : Finset (ZMod p)) (r : ℝ), Λ.card ≤ n0 Lg ∧
      min (kapS Lg D ^ 3 * ρ₁ / (8 * ((n0 Lg : ℝ) + 1))) (nu0 Lg / (4 * ((n0 Lg : ℝ) + 1))) ≤ r ∧
      r ≤ ρ₁ ∧ Reg (Γ ∪ Λ) r (kapS Lg D) (etaS Lg) ∧
      ∃ v : ZMod p, (19 / 20 : ℝ) * M.card * (bohr (Γ ∪ Λ) r).card ≤
        ((M.filter fun b => v - b ∈ bohr (Γ ∪ Λ) r).card : ℝ) * L.card := by
  classical
  set κ : ℝ := kapS Lg D with hκ
  set η : ℝ := etaS Lg with hη
  have hκ0 : 0 < κ := kapS_pos Lg D hD
  have hκ1 : κ ≤ 1 := (kapS_le Lg D hD).trans (by norm_num)
  have hη0 : 0 < η := etaS_pos Lg
  have hη1 : η ≤ 1 := (etaS_le Lg).trans (by norm_num)
  have hΓD : Γ.card ≤ D := by omega
  have hN1 : (0 : ℝ) < (n0 Lg : ℝ) + 1 := by positivity
  obtain ⟨rS, hrS1, hrS2, hregS⟩ := exists_reg Γ D hΓD hD hη0 hη1 (r := κ * ρ₁) (by positivity)
  have hrS0 : 0 < rS := lt_of_lt_of_le (by positivity) hrS1
  have hAS : ((Y + bohr Γ rS).card : ℝ) ≤ 2 ^ Lg * Y.card := by
    have hsub : Y + bohr Γ rS ⊆ bohr Γ (ρ₁ + rS) := by
      intro x hx
      obtain ⟨a, ha, b, hb, rfl⟩ := mem_add.1 hx
      exact add_mem_bohr (hYsub ha) hb
    have h1 : ((Y + bohr Γ rS).card : ℝ) ≤ (bohr Γ (ρ₁ + rS)).card := by
      exact_mod_cast card_le_card hsub
    have h2 := hreg.card_add_le hη0.le hrS0.le hrS2
    have h3 : (0 : ℝ) ≤ (bohr Γ ρ₁).card := Nat.cast_nonneg _
    nlinarith
  obtain ⟨rb, hrb1, hrb2, hregb⟩ := exists_reg Γ D hΓD hD hη0 hη1
    (r := κ * rS / ((n0 Lg : ℝ) + 1)) (by positivity)
  have hrb0 : 0 < rb := lt_of_lt_of_le (by positivity) hrb1
  have hrb' : ((n0 Lg + 1 : ℕ) : ℝ) * rb ≤ κ * rS := by
    push_cast
    rw [le_div_iff₀ hN1] at hrb2
    linarith
  obtain ⟨Λ, hΛcard, hΛ⟩ := ap_bohr Lg hLg Γ rS hrS0 κ η hκ0 hη0.le hη1
    (by rw [hη]; unfold etaS; linarith) hregS Y M L hY hAS hLM rb hrb0 hrb' hregb
  set r' : ℝ := min (κ * rb) (nu0 Lg / (2 * ((n0 Lg : ℝ) + 1))) with hr'
  have hr'0 : 0 < r' := lt_min (by positivity) (div_pos (nu0_pos Lg) (by positivity))
  have hcardU : (Γ ∪ Λ).card ≤ D := (card_union_le _ _).trans (by omega)
  obtain ⟨r, hr1, hr2, hregr⟩ := exists_reg (Γ ∪ Λ) D hcardU hD hη0 hη1 (r := r') hr'0
  refine ⟨Λ, r, hΛcard, ?_, ?_, hregr, ?_⟩
  · refine le_trans ?_ hr1
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    refine le_min ?_ ?_
    · have h1 : kapS Lg D ^ 3 * ρ₁ / (8 * ((n0 Lg : ℝ) + 1)) * 2 ≤ κ * rb := by
        have h2 : κ * (κ * (κ * ρ₁ / 2) / ((n0 Lg : ℝ) + 1) / 2) ≤ κ * rb := by
          apply mul_le_mul_of_nonneg_left _ hκ0.le
          refine le_trans ?_ hrb1
          apply div_le_div_of_nonneg_right _ (by norm_num)
          apply div_le_div_of_nonneg_right _ hN1.le
          exact mul_le_mul_of_nonneg_left hrS1 hκ0.le
        refine le_trans (le_of_eq ?_) h2
        rw [← hκ]; field_simp; ring
      exact le_trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (by norm_num)) h1
    · have h1 : nu0 Lg / (4 * ((n0 Lg : ℝ) + 1)) * 2 = nu0 Lg / (2 * ((n0 Lg : ℝ) + 1)) := by
        field_simp; ring
      exact le_trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (by norm_num)) (le_of_eq h1)
  · have h1 : r ≤ κ * rb := hr2.trans (min_le_left _ _)
    have h2 : rb ≤ κ * rS := by
      refine hrb2.trans (div_le_self (by positivity) ?_)
      linarith [(Nat.cast_nonneg (n0 Lg) : (0 : ℝ) ≤ n0 Lg)]
    have h3 : κ * rb ≤ rb := by nlinarith
    have h4 : κ * rS ≤ rS := by nlinarith
    have h5 : κ * ρ₁ ≤ ρ₁ := by nlinarith
    linarith
  · apply incr_from_ap Y M L _ hY hfull
    intro w hw
    have hw1 : w ∈ bohr Γ (κ * rb) :=
      bohr_mono (hr2.trans (min_le_left _ _)) (bohr_anti subset_union_left hw)
    have hw2 : w ∈ bohr Λ (nu0 Lg / (2 * ((n0 Lg : ℝ) + 1))) :=
      bohr_mono (hr2.trans (min_le_right _ _)) (bohr_anti subset_union_right hw)
    exact hΛ w hw1 hw2 0

/-- Transfer a count on a dilated piece back to a piece of `A`. -/
lemma incr_dilate (A X : Finset (ZMod p)) (c₀ c : ZMod p) (hc : c ≠ 0) (Γ' : Finset (ZMod p))
    (r : ℝ) (v : ZMod p) :
    (((piece A X c₀).image (fun z => c * z)).filter (fun b => v - b ∈ bohr Γ' r)).card ≤
      (piece A (bohr (dil c Γ') r) (c₀ + c⁻¹ * v)).card := by
  classical
  refine card_le_card_of_injOn (fun b => c⁻¹ * b - c⁻¹ * v) ?_ ?_
  · intro b hb
    have hb' := mem_filter.1 (mem_coe.1 hb)
    obtain ⟨z, hz, rfl⟩ := mem_image.1 hb'.1
    have hz' := mem_piece.1 hz
    have e1 : c⁻¹ * (c * z) - c⁻¹ * v = z - c⁻¹ * v := by
      rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
    refine mem_coe.2 (mem_piece.2 ⟨?_, ?_⟩)
    · show c⁻¹ * (c * z) - c⁻¹ * v ∈ bohr (dil c Γ') r
      rw [e1, mem_bohr_dil]
      have e2 : c * (z - c⁻¹ * v) = -(v - c * z) := by
        rw [mul_sub, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]; ring
      rw [e2]
      exact neg_mem_bohr hb'.2
    · show c₀ + c⁻¹ * v + (c⁻¹ * (c * z) - c⁻¹ * v) ∈ A
      rw [e1]
      have : c₀ + c⁻¹ * v + (z - c⁻¹ * v) = c₀ + z := by ring
      rw [this]; exact hz'.2
  · intro b _ b' _ h
    simp only at h
    have h2 : c⁻¹ * b = c⁻¹ * b' := by
      have := congrArg (fun t => t + c⁻¹ * v) h
      simpa using this
    exact mul_left_cancel₀ (inv_ne_zero hc) h2

end G16

end ModStep2

section ModStep3

/- # Green 16: the large/small sumset dichotomy -/

open Finset
open scoped Pointwise

namespace G16

variable {p : ℕ} [Fact p.Prime]

lemma incr_numeric {β B W N η : ℝ} (hβ : 0 < β) (hB : 0 < B) (hW : 0 ≤ W) (hη0 : 0 ≤ η)
    (hη : η ≤ 1 / 480) (h : 19 / 20 * (β * B) * W ≤ N * ((1 / 2 + η) * B)) :
    17 / 10 * β * W ≤ N := by
  have h1 : 19 / 20 * β * W ≤ N * (1 / 2 + η) := by
    have h' : (19 / 20 * β * W) * B ≤ (N * (1 / 2 + η)) * B := by linarith
    exact le_of_mul_le_mul_right h' hB
  have h2 : (17 / 10 * β * W) * (1 / 2 + η) ≤ 19 / 20 * β * W := by
    have hbw : 0 ≤ β * W := by positivity
    nlinarith
  exact le_of_mul_le_mul_right (h2.trans h1) (by linarith : 0 < 1 / 2 + η)

set_option maxHeartbeats 1000000 in
/-- The density increment in the localised configuration. -/
theorem step_cases (Lg D : ℕ) (hLg : 1 ≤ Lg) (hD : 1 ≤ D) (h2 : (2 : ZMod p) ≠ 0)
    (h3 : (3 : ZMod p) ≠ 0) (A R : Finset (ZMod p)) (hR : R.card + n0 Lg ≤ D)
    (hR0 : ∃ a ∈ R, a ≠ 0) (ρ' ρx ρy : ℝ) (hρ' : 0 < ρ') (hρx : 0 < ρx) (hρy : 0 < ρy)
    (hρxle : ρx ≤ kapS Lg D * ρ') (hρyle : 3 * ρy ≤ kapS Lg D * ρ')
    (hreg' : Reg R ρ' (kapS Lg D) (etaS Lg))
    (hregx : Reg (dil (2 : ZMod p)⁻¹ R) ρx (kapS Lg D) (etaS Lg))
    (hregy : Reg (dil (2 : ZMod p)⁻¹ R) ρy (kapS Lg D) (etaS Lg))
    (cx cy cz cw : ZMod p) (β : ℝ) (hβ0 : 0 < β) (hβ : 4 ≤ β * 2 ^ Lg)
    (hdx : β * (bohr (dil (2 : ZMod p)⁻¹ R) ρx).card ≤
      (piece A (bohr (dil (2 : ZMod p)⁻¹ R) ρx) cx).card)
    (hdy : β * (bohr (dil (2 : ZMod p)⁻¹ R) ρy).card ≤
      (piece A (bohr (dil (2 : ZMod p)⁻¹ R) ρy) cy).card)
    (hdz : β * (bohr R ρ').card ≤ (piece A (bohr R ρ') cz).card)
    (hdw : β * (bohr R ρ').card ≤ (piece A (bohr R ρ') cw).card)
    (hnosol : ∀ x' ∈ piece A (bohr (dil (2 : ZMod p)⁻¹ R) ρx) cx,
      ∀ y' ∈ piece A (bohr (dil (2 : ZMod p)⁻¹ R) ρy) cy,
      ∀ z' ∈ piece A (bohr R ρ') cz, ∀ w' ∈ piece A (bohr R ρ') cw,
        x' + 3 * y' ≠ 2 * z' + 2 * w') :
    ∃ (R' : Finset (ZMod p)) (r : ℝ) (t' : ZMod p), R'.card ≤ R.card + n0 Lg ∧
      (∃ a ∈ R', a ≠ 0) ∧
      min (kapS Lg D ^ 3 * min ρx ρy / (8 * ((n0 Lg : ℝ) + 1)))
        (nu0 Lg / (4 * ((n0 Lg : ℝ) + 1))) ≤ r ∧ r ≤ ρ' ∧
      Reg R' r (kapS Lg D) (etaS Lg) ∧
      17 / 10 * β * (bohr R' r).card ≤ (piece A (bohr R' r) t').card := by
  classical
  set κ : ℝ := kapS Lg D with hκ
  set η : ℝ := etaS Lg with hη
  have hκ0 : 0 < κ := kapS_pos Lg D hD
  have hκ1 : κ ≤ 1 / 40320 := kapS_le Lg D hD
  have hη0 : 0 < η := etaS_pos Lg
  have hη1 : η ≤ 1 / 480 := etaS_le Lg
  have hN1 : (0 : ℝ) < (n0 Lg : ℝ) + 1 := by positivity
  have h2i : (2 : ZMod p)⁻¹ ≠ 0 := inv_ne_zero h2
  set Γ := dil (2 : ZMod p)⁻¹ R with hΓ
  have hΓcard : Γ.card ≤ R.card := card_dil_le _ _
  have hΓD : Γ.card + n0 Lg ≤ D := by omega
  have hΓ0 : ∃ a ∈ Γ, a ≠ 0 := exists_ne_zero_dil h2i hR0
  have hcardΓ : ∀ ρ : ℝ, (bohr Γ ρ).card = (bohr R ρ).card := fun ρ => card_bohr_dil R ρ h2i
  have hregΓ' : Reg Γ ρ' κ η := (reg_dil h2i).2 hreg'
  have hmem2 : ∀ {z : ZMod p} {ρ : ℝ}, z ∈ bohr R ρ → 2 * z ∈ bohr Γ ρ := by
    intro z ρ hz
    rw [hΓ, mem_bohr_dil, ← mul_assoc, inv_mul_cancel₀ h2, one_mul]
    exact hz
  set Px := piece A (bohr Γ ρx) cx with hPx
  set Py := piece A (bohr Γ ρy) cy with hPy
  set Pz := piece A (bohr R ρ') cz with hPz
  set Pw := piece A (bohr R ρ') cw with hPw
  set 𝔅 : ℝ := ((bohr R ρ').card : ℝ) with h𝔅
  have h𝔅0 : 0 < 𝔅 := by
    rw [h𝔅]; exact_mod_cast card_bohr_pos hρ'.le
  set Sg := (Pw ×ˢ Py).image (fun q : ZMod p × ZMod p => 2 * q.1 - 3 * q.2) with hSgdef
  set Ω := bohr Γ (ρ' + κ * ρ') with hΩ
  have hSgΩ : Sg ⊆ Ω := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := mem_image.1 hx
    obtain ⟨hq1, hq2⟩ := mem_product.1 hq
    have h1 : 2 * q.1 ∈ bohr Γ ρ' := hmem2 (mem_piece.1 hq1).1
    have h2' : (3 : ZMod p) * q.2 ∈ bohr Γ (3 * ρy) := by
      have := nsmul_mem_bohr (mem_piece.1 hq2).1 3
      simpa using this
    exact sub_mem_bohr h1 (bohr_mono hρyle h2')
  have hΩcard : (Ω.card : ℝ) ≤ (1 + η) * 𝔅 := by
    have := hregΓ'.card_add_le hη0.le (by positivity : 0 ≤ κ * ρ') le_rfl
    rw [hcardΓ ρ'] at this
    exact this
  have h2Lg : (0 : ℝ) < 2 ^ Lg := by positivity
  by_cases hSgc : 𝔅 / 2 ≤ Sg.card
  · -- the large sumset case
    have hm2 : (-2 : ZMod p) ≠ 0 := neg_ne_zero.2 h2
    set M := Pz.image (fun z => (-2 : ZMod p) * z) with hM
    set L := Ω \ Sg with hL
    have hMcard : M.card = Pz.card := card_image_of_injective _ (mul_right_injective₀ hm2)
    have hfull : ∀ a ∈ Px, ∀ b ∈ M, a + b ∈ L := by
      intro a ha b hb
      obtain ⟨z, hz, rfl⟩ := mem_image.1 hb
      refine mem_sdiff.2 ⟨?_, ?_⟩
      · have h1 : (-2 : ZMod p) * z ∈ bohr Γ ρ' := by
          have := neg_mem_bohr (hmem2 (mem_piece.1 hz).1)
          rwa [← neg_mul] at this
        have h4 := add_mem_bohr (mem_piece.1 ha).1 h1
        exact bohr_mono (by linarith) h4
      · intro hmem
        obtain ⟨q, hq, hqe⟩ := mem_image.1 hmem
        obtain ⟨hq1, hq2⟩ := mem_product.1 hq
        exact hnosol a ha q.2 hq2 z hz q.1 hq1 (by linear_combination (-1 : ZMod p) * hqe)
    have hLcard : (L.card : ℝ) ≤ (1 / 2 + η) * 𝔅 := by
      have hle : Sg.card ≤ Ω.card := card_le_card hSgΩ
      rw [hL, card_sdiff_of_subset hSgΩ, Nat.cast_sub hle]
      linarith
    have hMd : β * 𝔅 ≤ M.card := by rw [hMcard]; exact hdz
    have hPx_ne : Px.Nonempty := by
      rw [← card_pos]
      have h5 : (0 : ℝ) < (bohr Γ ρx).card := by exact_mod_cast card_bohr_pos hρx.le
      have : (0 : ℝ) < Px.card := lt_of_lt_of_le (by positivity) hdx
      exact_mod_cast this
    have hYd : 2 * ((bohr Γ ρx).card : ℝ) ≤ 2 ^ Lg * Px.card := by
      have h5 : (0 : ℝ) ≤ (bohr Γ ρx).card := Nat.cast_nonneg _
      calc 2 * ((bohr Γ ρx).card : ℝ) ≤ (β * 2 ^ Lg) * (bohr Γ ρx).card :=
            mul_le_mul_of_nonneg_right (by linarith) h5
        _ = 2 ^ Lg * (β * (bohr Γ ρx).card) := by ring
        _ ≤ 2 ^ Lg * Px.card := mul_le_mul_of_nonneg_left hdx h2Lg.le
    have hLM : (L.card : ℝ) ≤ 2 ^ Lg * M.card := by
      calc (L.card : ℝ) ≤ (1 / 2 + η) * 𝔅 := hLcard
        _ ≤ 1 * 𝔅 := mul_le_mul_of_nonneg_right (by linarith) h𝔅0.le
        _ ≤ (β * 2 ^ Lg) * 𝔅 := mul_le_mul_of_nonneg_right (by linarith) h𝔅0.le
        _ = 2 ^ Lg * (β * 𝔅) := by ring
        _ ≤ 2 ^ Lg * M.card := mul_le_mul_of_nonneg_left hMd h2Lg.le
    obtain ⟨Λ, r, hΛ, hrlow, hrle, hregr, v, hv⟩ := ap_incr Lg D hLg hD Γ hΓD ρx hρx hregx
      Px M L hPx_ne (piece_subset _ _ _) hYd hLM hfull
    have hdil := incr_dilate A (bohr R ρ') cz (-2 : ZMod p) hm2 (Γ ∪ Λ) r v
    refine ⟨dil (-2 : ZMod p) (Γ ∪ Λ), r, cz + (-2 : ZMod p)⁻¹ * v, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (card_dil_le _ _).trans ((card_union_le _ _).trans (by omega))
    · obtain ⟨a, ha, ha0⟩ := hΓ0
      exact exists_ne_zero_dil hm2 ⟨a, mem_union_left _ ha, ha0⟩
    · refine le_trans (min_le_min ?_ le_rfl) hrlow
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity)
    · have : κ * ρ' ≤ ρ' := by nlinarith
      linarith
    · exact (reg_dil hm2).2 hregr
    · rw [card_bohr_dil _ _ hm2]
      have hN : ((M.filter fun b => v - b ∈ bohr (Γ ∪ Λ) r).card : ℝ) ≤
          ((piece A (bohr (dil (-2 : ZMod p) (Γ ∪ Λ)) r) (cz + (-2 : ZMod p)⁻¹ * v)).card : ℝ) :=
        Nat.cast_le.2 hdil
      refine le_trans ?_ hN
      have hW0 : (0 : ℝ) ≤ (bohr (Γ ∪ Λ) r).card := Nat.cast_nonneg _
      have hN0 : (0 : ℝ) ≤ ((M.filter fun b => v - b ∈ bohr (Γ ∪ Λ) r).card : ℝ) :=
        Nat.cast_nonneg _
      refine incr_numeric hβ0 h𝔅0 hW0 hη0.le hη1 ?_
      calc 19 / 20 * (β * 𝔅) * ((bohr (Γ ∪ Λ) r).card : ℝ)
          ≤ 19 / 20 * (M.card : ℝ) * (bohr (Γ ∪ Λ) r).card := by
            apply mul_le_mul_of_nonneg_right _ hW0
            linarith
        _ ≤ ((M.filter fun b => v - b ∈ bohr (Γ ∪ Λ) r).card : ℝ) * L.card := hv
        _ ≤ ((M.filter fun b => v - b ∈ bohr (Γ ∪ Λ) r).card : ℝ) * ((1 / 2 + η) * 𝔅) :=
            mul_le_mul_of_nonneg_left hLcard hN0
  · -- the small sumset case
    push Not at hSgc
    have h3i : (3 : ZMod p)⁻¹ ≠ 0 := inv_ne_zero h3
    have hm3 : (-3 : ZMod p) ≠ 0 := neg_ne_zero.2 h3
    set Γ₃ := dil (3 : ZMod p)⁻¹ Γ with hΓ₃
    have hΓ₃D : Γ₃.card + n0 Lg ≤ D := by
      have : Γ₃.card ≤ Γ.card := card_dil_le _ _
      omega
    have hregy₃ : Reg Γ₃ ρy κ η := (reg_dil h3i).2 hregy
    set Y := Py.image (fun y => (-3 : ZMod p) * y) with hY
    set M := Pw.image (fun w => (2 : ZMod p) * w) with hM
    have hYcard : Y.card = Py.card := card_image_of_injective _ (mul_right_injective₀ hm3)
    have hMcard : M.card = Pw.card := card_image_of_injective _ (mul_right_injective₀ h2)
    have hYsub : Y ⊆ bohr Γ₃ ρy := by
      intro b hb
      obtain ⟨y, hy, rfl⟩ := mem_image.1 hb
      rw [hΓ₃, mem_bohr_dil]
      have e1 : (3 : ZMod p)⁻¹ * (-3 * y) = -y := by
        rw [← mul_assoc, mul_neg, inv_mul_cancel₀ h3]; ring
      rw [e1]
      exact neg_mem_bohr (mem_piece.1 hy).1
    have hfull : ∀ a ∈ Y, ∀ b ∈ M, a + b ∈ Sg := by
      intro a ha b hb
      obtain ⟨y, hy, rfl⟩ := mem_image.1 ha
      obtain ⟨w, hw, rfl⟩ := mem_image.1 hb
      exact mem_image.2 ⟨(w, y), mem_product.2 ⟨hw, hy⟩, by ring⟩
    have hMd : β * 𝔅 ≤ M.card := by rw [hMcard]; exact hdw
    have hPy_pos : (0 : ℝ) < Py.card := by
      have h5 : (0 : ℝ) < (bohr Γ ρy).card := by exact_mod_cast card_bohr_pos hρy.le
      exact lt_of_lt_of_le (by positivity) hdy
    have hY_ne : Y.Nonempty := by
      rw [← card_pos, hYcard]
      exact_mod_cast hPy_pos
    have hYd : 2 * ((bohr Γ₃ ρy).card : ℝ) ≤ 2 ^ Lg * Y.card := by
      rw [hΓ₃, card_bohr_dil Γ ρy h3i, hYcard]
      have h5 : (0 : ℝ) ≤ (bohr Γ ρy).card := Nat.cast_nonneg _
      calc 2 * ((bohr Γ ρy).card : ℝ) ≤ (β * 2 ^ Lg) * (bohr Γ ρy).card :=
            mul_le_mul_of_nonneg_right (by linarith) h5
        _ = 2 ^ Lg * (β * (bohr Γ ρy).card) := by ring
        _ ≤ 2 ^ Lg * Py.card := mul_le_mul_of_nonneg_left hdy h2Lg.le
    have hLM : (Sg.card : ℝ) ≤ 2 ^ Lg * M.card := by
      calc (Sg.card : ℝ) ≤ 𝔅 / 2 := hSgc.le
        _ ≤ 1 * 𝔅 := by linarith
        _ ≤ (β * 2 ^ Lg) * 𝔅 := mul_le_mul_of_nonneg_right (by linarith) h𝔅0.le
        _ = 2 ^ Lg * (β * 𝔅) := by ring
        _ ≤ 2 ^ Lg * M.card := mul_le_mul_of_nonneg_left hMd h2Lg.le
    obtain ⟨Λ, r, hΛ, hrlow, hrle, hregr, v, hv⟩ := ap_incr Lg D hLg hD Γ₃ hΓ₃D ρy hρy hregy₃
      Y M Sg hY_ne hYsub hYd hLM hfull
    have hdil := incr_dilate A (bohr R ρ') cw 2 h2 (Γ₃ ∪ Λ) r v
    refine ⟨dil 2 (Γ₃ ∪ Λ), r, cw + (2 : ZMod p)⁻¹ * v, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have : Γ₃.card ≤ Γ.card := card_dil_le _ _
      exact (card_dil_le _ _).trans ((card_union_le _ _).trans (by omega))
    · obtain ⟨a, ha, ha0⟩ := exists_ne_zero_dil h3i hΓ0
      exact exists_ne_zero_dil h2 ⟨a, mem_union_left _ ha, ha0⟩
    · refine le_trans (min_le_min ?_ le_rfl) hrlow
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
    · have : κ * ρ' ≤ ρ' := by nlinarith
      linarith
    · exact (reg_dil h2).2 hregr
    · rw [card_bohr_dil _ _ h2]
      have hN : ((M.filter fun b => v - b ∈ bohr (Γ₃ ∪ Λ) r).card : ℝ) ≤
          ((piece A (bohr (dil 2 (Γ₃ ∪ Λ)) r) (cw + (2 : ZMod p)⁻¹ * v)).card : ℝ) :=
        Nat.cast_le.2 hdil
      refine le_trans ?_ hN
      have hW0 : (0 : ℝ) ≤ (bohr (Γ₃ ∪ Λ) r).card := Nat.cast_nonneg _
      have hN0 : (0 : ℝ) ≤ ((M.filter fun b => v - b ∈ bohr (Γ₃ ∪ Λ) r).card : ℝ) :=
        Nat.cast_nonneg _
      refine incr_numeric hβ0 h𝔅0 hW0 hη0.le hη1 ?_
      calc 19 / 20 * (β * 𝔅) * ((bohr (Γ₃ ∪ Λ) r).card : ℝ)
          ≤ 19 / 20 * (M.card : ℝ) * (bohr (Γ₃ ∪ Λ) r).card := by
            apply mul_le_mul_of_nonneg_right _ hW0
            linarith
        _ ≤ ((M.filter fun b => v - b ∈ bohr (Γ₃ ∪ Λ) r).card : ℝ) * Sg.card := hv
        _ ≤ ((M.filter fun b => v - b ∈ bohr (Γ₃ ∪ Λ) r).card : ℝ) * ((1 / 2 + η) * 𝔅) := by
            apply mul_le_mul_of_nonneg_left _ hN0
            have : 𝔅 / 2 ≤ (1 / 2 + η) * 𝔅 := by
              have := mul_nonneg hη0.le h𝔅0.le
              linarith
            linarith

end G16

end ModStep3

section ModStep4

/- # Green 16: the density increment step -/

open Finset
open scoped Pointwise

namespace G16

variable {p : ℕ} [Fact p.Prime]

/-- No solutions to `x + 3y = 2z + 2w` in distinct elements. -/
def SolFree (A : Finset (ZMod p)) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, ∀ w ∈ A, x ≠ y → x ≠ z → x ≠ w → y ≠ z → y ≠ w → z ≠ w →
    x + 3 * y ≠ 2 * z + 2 * w

/-- The factor by which the radius shrinks in one step. -/
noncomputable def qS (Lg D : ℕ) : ℝ :=
  min (kapS Lg D ^ 5 / (3840 * ((n0 Lg : ℝ) + 1))) (nu0 Lg / (4 * ((n0 Lg : ℝ) + 1)))

lemma avg_dens (A R : Finset (ZMod p)) (ρ κ η : ℝ) (hη : 0 ≤ η) (hκρ : 0 ≤ κ * ρ)
    (hreg : Reg R ρ κ η) (t s : ZMod p) (X : Finset (ZMod p)) (hX : X.Nonempty)
    (hsX : ∀ x ∈ X, s + x ∈ bohr R (κ * ρ)) (α : ℝ)
    (hdens : α * (bohr R ρ).card ≤ (piece A (bohr R ρ) t).card) :
    (α - η) * (bohr R ρ).card ≤
      ∑ u ∈ bohr R ρ, ((piece A X (t + u + s)).card : ℝ) / X.card := by
  have hX0 : (0 : ℝ) < X.card := by exact_mod_cast hX.card_pos
  have h := sum_card_piece_ge A R ρ κ η hη hκρ hreg t s X hsX
  rw [← Finset.sum_div, le_div_iff₀ hX0]
  refine le_trans ?_ h
  apply mul_le_mul_of_nonneg_right _ hX0.le
  linarith

omit [Fact p.Prime] in
lemma exists_center4 (B : Finset (ZMod p)) (hB : B.Nonempty) (f₁ f₂ f₃ f₄ : ZMod p → ℝ)
    (c : ℝ) (h₁ : c * B.card ≤ ∑ u ∈ B, f₁ u) (h₂ : c * B.card ≤ ∑ u ∈ B, f₂ u)
    (h₃ : c * B.card ≤ ∑ u ∈ B, f₃ u) (h₄ : c * B.card ≤ ∑ u ∈ B, f₄ u) :
    ∃ u ∈ B, 4 * c ≤ f₁ u + f₂ u + f₃ u + f₄ u := by
  by_contra hcon
  push Not at hcon
  have h := Finset.sum_lt_sum_of_nonempty hB hcon
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const,
    nsmul_eq_mul] at h
  linarith

lemma four_dens {a b c d α η : ℝ} (hsum : 4 * (α - η) ≤ a + b + c + d) (ha : a < 11 / 10 * α)
    (hb : b < 11 / 10 * α) (hc : c < 11 / 10 * α) (hd : d < 11 / 10 * α) (hη : 100 * η ≤ α) :
    33 / 50 * α ≤ a ∧ 33 / 50 * α ≤ b ∧ 33 / 50 * α ≤ c ∧ 33 / 50 * α ≤ d := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

set_option maxHeartbeats 2000000 in
/-- **The density increment step.** -/
theorem step (Lg D : ℕ) (hLg : 1 ≤ Lg) (hD : 1 ≤ D) (h2 : (2 : ZMod p) ≠ 0)
    (h3 : (3 : ZMod p) ≠ 0) (A : Finset (ZMod p)) (hsf : SolFree A)
    (R : Finset (ZMod p)) (hR : R.card + n0 Lg ≤ D) (hR0 : ∃ a ∈ R, a ≠ 0)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hreg : Reg R ρ (kapS Lg D) (etaS Lg))
    (t : ZMod p) (α : ℝ) (hα : 16 ≤ α * 2 ^ Lg)
    (hdens : α * (bohr R ρ).card ≤ (piece A (bohr R ρ) t).card) :
    (p : ℝ) ≤ (80 / (kapS Lg D * ρ)) ^ (2 * D) ∨
    ∃ (R' : Finset (ZMod p)) (ρ' : ℝ) (t' : ZMod p), R'.card ≤ R.card + n0 Lg ∧
      (∃ a ∈ R', a ≠ 0) ∧ qS Lg D * ρ ≤ ρ' ∧ ρ' ≤ 1 ∧
      Reg R' ρ' (kapS Lg D) (etaS Lg) ∧
      11 / 10 * α * (bohr R' ρ').card ≤ (piece A (bohr R' ρ') t').card := by
  classical
  set κ : ℝ := kapS Lg D with hκ
  set η : ℝ := etaS Lg with hη
  have hκ0 : 0 < κ := kapS_pos Lg D hD
  have hκ1 : κ ≤ 1 / 40320 := kapS_le Lg D hD
  have hη0 : 0 < η := etaS_pos Lg
  have hη1 : η ≤ 1 / 480 := etaS_le Lg
  have hη1' : η ≤ 1 := hη1.trans (by norm_num)
  have hN1 : (1 : ℝ) ≤ (n0 Lg : ℝ) + 1 := by
    linarith [(Nat.cast_nonneg (n0 Lg) : (0 : ℝ) ≤ n0 Lg)]
  have h2Lg : (0 : ℝ) < 2 ^ Lg := by positivity
  have hα0 : 0 < α := by
    by_contra hneg
    push Not at hneg
    nlinarith
  have hRD : R.card ≤ D := by omega
  obtain ⟨ρ', hρ'1, hρ'2, hreg'⟩ := exists_reg R D hRD hD hη0 hη1' (r := κ * ρ / 40)
    (by positivity)
  have hκρ0 : 0 < κ * ρ := by positivity
  have hρ'0 : 0 < ρ' := lt_of_lt_of_le (by positivity) hρ'1
  have hκρ1 : κ * ρ ≤ 1 / 40320 := by nlinarith
  by_cases hsep : ∃ s, s ∈ bohr R (κ * ρ / 10) ∧ s ∉ bohr R (2 * ρ')
  swap
  · left
    push Not at hsep
    have hsub : bohr R (κ * ρ / 10) ⊆ bohr R (2 * ρ') := fun s hs => hsep s hs
    have hdich := bohr_dichotomy (R := R) (ρ₁ := 2 * ρ') (ρ₂ := κ * ρ / 10) (by positivity)
      (by linarith) hsub
    have hcard1 : (bohr R (2 * ρ')).card = 1 := by
      rcases hdich with h | h
      · exact h
      · exfalso
        obtain ⟨a, ha, ha0⟩ := hR0
        obtain ⟨x, hx⟩ := exists_not_mem_bohr ha ha0 (ρ := 2 * ρ') (by linarith)
        exact hx (h ▸ mem_univ x)
    have hc : ((bohr R (κ * ρ / 10)).card : ℝ) ≤ 1 := by
      have := card_le_card hsub
      rw [hcard1] at this
      exact_mod_cast this
    have hsize := card_univ_le_bohr R (ρ := κ * ρ / 10) (by positivity) (by linarith)
    have e : (8 : ℝ) / (κ * ρ / 10) = 80 / (κ * ρ) := by field_simp; ring
    rw [e] at hsize
    have hbase : (1 : ℝ) ≤ 80 / (κ * ρ) := by
      rw [le_div_iff₀ hκρ0]; linarith
    calc (p : ℝ) ≤ ((bohr R (κ * ρ / 10)).card : ℝ) * (80 / (κ * ρ)) ^ (2 * R.card) := hsize
      _ ≤ 1 * (80 / (κ * ρ)) ^ (2 * R.card) :=
          mul_le_mul_of_nonneg_right hc (by positivity)
      _ ≤ (80 / (κ * ρ)) ^ (2 * D) := by
          rw [one_mul]; exact pow_le_pow_right₀ hbase (by omega)
  · right
    obtain ⟨s, hs1, hs2⟩ := hsep
    have hs14 : s ∈ bohr R (1 / 4) := bohr_mono (by linarith) hs1
    have hk2 : (2 : ZMod p) * s ∉ bohr R (2 * ρ') := by
      simpa using not_mem_bohr_mul hs14 hs2 (k := 2) (by norm_num) (by norm_num)
    have hk3 : (3 : ZMod p) * s ∉ bohr R (2 * ρ') := by
      simpa using not_mem_bohr_mul hs14 hs2 (k := 3) (by norm_num) (by norm_num)
    have hk4 : (4 : ZMod p) * s ∉ bohr R (2 * ρ') := by
      simpa using not_mem_bohr_mul hs14 hs2 (k := 4) (by norm_num) (by norm_num)
    have hk5 : (5 : ZMod p) * s ∉ bohr R (2 * ρ') := by
      simpa using not_mem_bohr_mul hs14 hs2 (k := 5) (by norm_num) (by norm_num)
    have h2i : (2 : ZMod p)⁻¹ ≠ 0 := inv_ne_zero h2
    set Γ := dil (2 : ZMod p)⁻¹ R with hΓ
    have hΓcard : Γ.card ≤ R.card := card_dil_le _ _
    have hΓD : Γ.card ≤ D := hΓcard.trans hRD
    obtain ⟨ρx, hρx1, hρx2, hregx⟩ := exists_reg Γ D hΓD hD hη0 hη1' (r := κ * ρ')
      (by positivity)
    obtain ⟨ρy, hρy1, hρy2, hregy⟩ := exists_reg Γ D hΓD hD hη0 hη1' (r := κ * ρ' / 3)
      (by positivity)
    have hρx0 : 0 < ρx := lt_of_lt_of_le (by positivity) hρx1
    have hρy0 : 0 < ρy := lt_of_lt_of_le (by positivity) hρy1
    have hκρ' : κ * ρ' ≤ ρ' / 40320 := by nlinarith
    -- Bohr sets with dilated frequencies sit inside the original ones
    have hΓR : ∀ {x : ZMod p} {ρ₀ : ℝ}, x ∈ bohr Γ ρ₀ → x ∈ bohr R (2 * ρ₀) := by
      intro x ρ₀ hx
      have h1 : (2 : ZMod p)⁻¹ * x ∈ bohr R ρ₀ := mem_bohr_dil.1 hx
      have h2' := nsmul_mem_bohr h1 2
      have e : ((2 : ℕ) : ZMod p) * ((2 : ZMod p)⁻¹ * x) = x := by
        push_cast
        rw [← mul_assoc, mul_inv_cancel₀ h2, one_mul]
      rw [e] at h2'
      simpa using h2'
    have hDxR : ∀ {x : ZMod p}, x ∈ bohr Γ ρx → x ∈ bohr R ρ' := fun hx =>
      bohr_mono (by linarith) (hΓR hx)
    have hDyR : ∀ {x : ZMod p}, x ∈ bohr Γ ρy → x ∈ bohr R ρ' := fun hx =>
      bohr_mono (by linarith) (hΓR hx)
    have hsk : ∀ k : ℕ, k ≤ 5 → (k : ZMod p) * s ∈ bohr R (κ * ρ / 2) := by
      intro k hk
      have h1 := nsmul_mem_bohr hs1 k
      have hk' : (k : ℝ) ≤ 5 := by exact_mod_cast hk
      exact bohr_mono (by nlinarith) h1
    have hXx : ∀ x ∈ bohr Γ ρx, s + x ∈ bohr R (κ * ρ) := by
      intro x hx
      have h1 := hsk 1 (by norm_num)
      have h4 := add_mem_bohr h1 (hDxR hx)
      simp only [Nat.cast_one, one_mul] at h4
      exact bohr_mono (by linarith) h4
    have hXy : ∀ x ∈ bohr Γ ρy, 3 * s + x ∈ bohr R (κ * ρ) := by
      intro x hx
      have h1 := hsk 3 (by norm_num)
      have h4 := add_mem_bohr h1 (hDyR hx)
      simp only [Nat.cast_ofNat] at h4
      exact bohr_mono (by linarith) h4
    have hXz : ∀ x ∈ bohr R ρ', 5 * s + x ∈ bohr R (κ * ρ) := by
      intro x hx
      have h1 := hsk 5 (by norm_num)
      have h4 := add_mem_bohr h1 hx
      simp only [Nat.cast_ofNat] at h4
      exact bohr_mono (by linarith) h4
    have hXw : ∀ x ∈ bohr R ρ', 0 + x ∈ bohr R (κ * ρ) := by
      intro x hx
      rw [zero_add]
      exact bohr_mono (by linarith) hx
    have hneX : ∀ (Q : Finset (ZMod p)) (r₀ : ℝ), 0 < r₀ → (bohr Q r₀).Nonempty :=
      fun Q r₀ h => ⟨0, zero_mem_bohr h.le⟩
    have hax := avg_dens A R ρ κ η hη0.le hκρ0.le hreg t s (bohr Γ ρx) (hneX _ _ hρx0) hXx α hdens
    have hay := avg_dens A R ρ κ η hη0.le hκρ0.le hreg t (3 * s) (bohr Γ ρy) (hneX _ _ hρy0)
      hXy α hdens
    have haz := avg_dens A R ρ κ η hη0.le hκρ0.le hreg t (5 * s) (bohr R ρ') (hneX _ _ hρ'0)
      hXz α hdens
    have haw := avg_dens A R ρ κ η hη0.le hκρ0.le hreg t 0 (bohr R ρ') (hneX _ _ hρ'0)
      hXw α hdens
    obtain ⟨u, _, hudens⟩ := exists_center4 (bohr R ρ) (hneX _ _ hρ) _ _ _ _ (α - η)
      hax hay haz haw
    have hDx0 : (0 : ℝ) < (bohr Γ ρx).card := by exact_mod_cast card_bohr_pos hρx0.le
    have hDy0 : (0 : ℝ) < (bohr Γ ρy).card := by exact_mod_cast card_bohr_pos hρy0.le
    have hBz0 : (0 : ℝ) < (bohr R ρ').card := by exact_mod_cast card_bohr_pos hρ'0.le
    have hΓ0 : ∃ a ∈ Γ, a ≠ 0 := exists_ne_zero_dil h2i hR0
    have hκ5 : κ ^ 5 ≤ κ ^ 2 := pow_le_pow_of_le_one hκ0.le (by linarith) (by norm_num)
    have hqS : qS Lg D * ρ ≤ κ ^ 5 * ρ / 3840 := by
      unfold qS
      have h1 : min (kapS Lg D ^ 5 / (3840 * ((n0 Lg : ℝ) + 1)))
          (nu0 Lg / (4 * ((n0 Lg : ℝ) + 1))) ≤ κ ^ 5 / 3840 := by
        refine (min_le_left _ _).trans ?_
        rw [← hκ]
        exact div_le_div_of_nonneg_left (by positivity) (by norm_num) (by nlinarith)
      calc _ ≤ κ ^ 5 / 3840 * ρ := mul_le_mul_of_nonneg_right h1 hρ.le
        _ = κ ^ 5 * ρ / 3840 := by ring
    have hκ2ρ : κ ^ 5 * ρ ≤ κ ^ 2 * ρ := mul_le_mul_of_nonneg_right hκ5 hρ.le
    have hκκ : κ ^ 2 * ρ = κ * (κ * ρ) := by ring
    by_cases hbig : (11 / 10 * α * (bohr Γ ρx).card ≤ (piece A (bohr Γ ρx) (t + u + s)).card) ∨
        (11 / 10 * α * (bohr Γ ρy).card ≤ (piece A (bohr Γ ρy) (t + u + 3 * s)).card) ∨
        (11 / 10 * α * (bohr R ρ').card ≤ (piece A (bohr R ρ') (t + u + 5 * s)).card) ∨
        (11 / 10 * α * (bohr R ρ').card ≤ (piece A (bohr R ρ') (t + u + 0)).card)
    · rcases hbig with h | h | h | h
      · refine ⟨Γ, ρx, t + u + s, by omega, hΓ0, ?_, by linarith, hregx, h⟩
        have : κ * (κ * ρ) / 160 ≤ ρx := by nlinarith
        nlinarith
      · refine ⟨Γ, ρy, t + u + 3 * s, by omega, hΓ0, ?_, by linarith, hregy, h⟩
        have : κ * (κ * ρ) / 480 ≤ ρy := by nlinarith
        nlinarith
      · refine ⟨R, ρ', t + u + 5 * s, by omega, hR0, ?_, by linarith, hreg', h⟩
        nlinarith
      · refine ⟨R, ρ', t + u + 0, by omega, hR0, ?_, by linarith, hreg', h⟩
        nlinarith
    · push Not at hbig
      obtain ⟨hbx, hby, hbz, hbw⟩ := hbig
      have hηα : 100 * η ≤ α := by
        have h1 : 100 * η * 2 ^ Lg ≤ α * 2 ^ Lg := by
          have e : η * 2 ^ Lg = 1 / 480 := by
            rw [hη]; unfold etaS nu0; field_simp; ring
          nlinarith
        exact le_of_mul_le_mul_right h1 h2Lg
      obtain ⟨hdx, hdy, hdz, hdw⟩ := four_dens hudens
        ((div_lt_iff₀ hDx0).2 hbx) ((div_lt_iff₀ hDy0).2 hby) ((div_lt_iff₀ hBz0).2 hbz)
        ((div_lt_iff₀ hBz0).2 hbw) hηα
      rw [le_div_iff₀ hDx0] at hdx
      rw [le_div_iff₀ hDy0] at hdy
      rw [le_div_iff₀ hBz0] at hdz hdw
      have hβ0 : 0 < 33 / 50 * α := by positivity
      have hβ : 4 ≤ 33 / 50 * α * 2 ^ Lg := by nlinarith
      have hnosol : ∀ x' ∈ piece A (bohr Γ ρx) (t + u + s),
          ∀ y' ∈ piece A (bohr Γ ρy) (t + u + 3 * s),
          ∀ z' ∈ piece A (bohr R ρ') (t + u + 5 * s), ∀ w' ∈ piece A (bohr R ρ') (t + u + 0),
            x' + 3 * y' ≠ 2 * z' + 2 * w' := by
        intro x' hx' y' hy' z' hz' w' hw' heq
        obtain ⟨hx1, hx2⟩ := mem_piece.1 hx'
        obtain ⟨hy1, hy2⟩ := mem_piece.1 hy'
        obtain ⟨hz1, hz2⟩ := mem_piece.1 hz'
        obtain ⟨hw1, hw2⟩ := mem_piece.1 hw'
        have hx3 := hDxR hx1
        have hy3 := hDyR hy1
        have hsub : ∀ {a b : ZMod p}, a ∈ bohr R ρ' → b ∈ bohr R ρ' → a - b ∈ bohr R (2 * ρ') := by
          intro a b ha hb
          have := sub_mem_bohr ha hb
          rwa [← two_mul] at this
        refine hsf _ hx2 _ hy2 _ hz2 _ hw2 ?_ ?_ ?_ ?_ ?_ ?_ ?_
        · intro h
          apply hk2
          have e : (2 : ZMod p) * s = x' - y' := by linear_combination (-1 : ZMod p) * h
          rw [e]; exact hsub hx3 hy3
        · intro h
          apply hk4
          have e : (4 : ZMod p) * s = x' - z' := by linear_combination (-1 : ZMod p) * h
          rw [e]; exact hsub hx3 hz1
        · intro h
          apply hs2
          have e : s = w' - x' := by linear_combination h
          rw [e]; exact hsub hw1 hx3
        · intro h
          apply hk2
          have e : (2 : ZMod p) * s = y' - z' := by linear_combination (-1 : ZMod p) * h
          rw [e]; exact hsub hy3 hz1
        · intro h
          apply hk3
          have e : (3 : ZMod p) * s = w' - y' := by linear_combination h
          rw [e]; exact hsub hw1 hy3
        · intro h
          apply hk5
          have e : (5 : ZMod p) * s = w' - z' := by linear_combination h
          rw [e]; exact hsub hw1 hz1
        · linear_combination heq
      obtain ⟨R', r, t', hR'card, hR'0, hrlow, hrle, hregr, hincr⟩ :=
        step_cases Lg D hLg hD h2 h3 A R hR hR0 ρ' ρx ρy hρ'0 hρx0 hρy0 hρx2 (by linarith)
          hreg' hregx hregy (t + u + s) (t + u + 3 * s) (t + u + 5 * s) (t + u + 0)
          (33 / 50 * α) hβ0 hβ hdx hdy hdz hdw hnosol
      refine ⟨R', r, t', hR'card, hR'0, ?_, by linarith, hregr, ?_⟩
      · refine le_trans ?_ hrlow
        have hminρ : κ * (κ * ρ) / 480 ≤ min ρx ρy := by
          refine le_min ?_ ?_ <;> nlinarith
        refine le_min ?_ ?_
        · have h1 : qS Lg D * ρ ≤ κ ^ 5 / (3840 * ((n0 Lg : ℝ) + 1)) * ρ := by
            unfold qS
            exact mul_le_mul_of_nonneg_right (min_le_left _ _) hρ.le
          refine h1.trans ?_
          rw [← hκ]
          have h5 : κ ^ 5 / (3840 * ((n0 Lg : ℝ) + 1)) * ρ =
              κ ^ 3 * (κ * (κ * ρ) / 480) / (8 * ((n0 Lg : ℝ) + 1)) := by
            field_simp; ring
          rw [h5]
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left hminρ (by positivity)
        · have h1 : qS Lg D * ρ ≤ nu0 Lg / (4 * ((n0 Lg : ℝ) + 1)) * ρ := by
            unfold qS
            exact mul_le_mul_of_nonneg_right (min_le_right _ _) hρ.le
          refine h1.trans ?_
          have hpos : 0 ≤ nu0 Lg / (4 * ((n0 Lg : ℝ) + 1)) :=
            div_nonneg (nu0_pos Lg).le (by positivity)
          nlinarith
      · refine le_trans ?_ hincr
        have hW0 : (0 : ℝ) ≤ (bohr R' r).card := Nat.cast_nonneg _
        nlinarith

end G16

end ModStep4

section ModIter

/- # Green 16: the iteration -/

open Finset
open scoped Pointwise

namespace G16

variable {p : ℕ} [Fact p.Prime]

/-- The maximal rank of the Bohr sets in the iteration. -/
def DD (Lg : ℕ) : ℕ := 1 + 8 * Lg * n0 Lg

lemma qS_pos (Lg D : ℕ) (hD : 1 ≤ D) : 0 < qS Lg D := by
  unfold qS
  have h1 := kapS_pos Lg D hD
  have h2 := nu0_pos Lg
  exact lt_min (by positivity) (by positivity)

lemma qS_le_one (Lg D : ℕ) : qS Lg D ≤ 1 := by
  unfold qS
  refine (min_le_right _ _).trans ?_
  have h1 := nu0_le Lg
  have h2 := nu0_pos Lg
  have h3 : (0 : ℝ) ≤ n0 Lg := Nat.cast_nonneg _
  rw [div_le_one (by positivity)]
  nlinarith

/-- Some translate of `B` contains at least the average number of points of `A`. -/
lemma exists_translate (A B : Finset (ZMod p)) :
    ∃ t : ZMod p, (A.card : ℝ) * B.card ≤ (piece A B t).card * p := by
  classical
  have hsum : ∑ t : ZMod p, ((piece A B t).card : ℝ) = (A.card : ℝ) * B.card := by
    have e1 : ∀ t : ZMod p, ((piece A B t).card : ℝ) =
        ∑ x ∈ B, if t + x ∈ A then (1 : ℝ) else 0 := by
      intro t
      unfold piece
      rw [Finset.card_filter]; push_cast; rfl
    simp_rw [e1]
    rw [Finset.sum_comm]
    have e2 : ∀ x ∈ B, ∑ t : ZMod p, (if t + x ∈ A then (1 : ℝ) else 0) = A.card := by
      intro x _
      have : ∑ t : ZMod p, (if t + x ∈ A then (1 : ℝ) else 0) =
          ∑ t : ZMod p, (if t ∈ A then (1 : ℝ) else 0) :=
        Fintype.sum_equiv (Equiv.addRight x) _ _ fun t => rfl
      rw [this]; simp
    rw [Finset.sum_congr rfl e2]
    simp [mul_comm]
  by_contra hcon
  push Not at hcon
  have h1 : ∑ t : ZMod p, ((piece A B t).card : ℝ) * p <
      ∑ _t : ZMod p, (A.card : ℝ) * B.card :=
    Finset.sum_lt_sum_of_nonempty ⟨0, mem_univ _⟩ fun t _ => hcon t
  rw [← Finset.sum_mul, hsum, Finset.sum_const, card_univ, ZMod.card, nsmul_eq_mul] at h1
  linarith

lemma pow_eleven_tenths (Lg : ℕ) : (2 : ℝ) ^ Lg ≤ (11 / 10 : ℝ) ^ (8 * Lg) := by
  rw [pow_mul]
  exact pow_le_pow_left₀ (by norm_num) (by norm_num) _

set_option maxHeartbeats 1000000 in
/-- **The main bound in `ZMod p`.** -/
theorem zmod_bound (Lg : ℕ) (hLg : 1 ≤ Lg) (h2 : (2 : ZMod p) ≠ 0) (h3 : (3 : ZMod p) ≠ 0)
    (A : Finset (ZMod p)) (hsf : SolFree A) (hA : 16 * (p : ℝ) ≤ A.card * 2 ^ Lg) :
    (p : ℝ) ≤ (160 / (kapS Lg (DD Lg) * qS Lg (DD Lg) ^ (8 * Lg))) ^ (2 * DD Lg) := by
  classical
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  set D : ℕ := DD Lg with hD
  have hD1 : 1 ≤ D := by rw [hD]; unfold DD; omega
  set κ : ℝ := kapS Lg D with hκ
  set η : ℝ := etaS Lg with hη
  set q : ℝ := qS Lg D with hq
  set J : ℕ := 8 * Lg with hJ
  have hκ0 : 0 < κ := kapS_pos Lg D hD1
  have hη0 : 0 < η := etaS_pos Lg
  have hη1 : η ≤ 1 := (etaS_le Lg).trans (by norm_num)
  have hq0 : 0 < q := qS_pos Lg D hD1
  have hq1 : q ≤ 1 := qS_le_one Lg D
  have hDJ : D = 1 + J * n0 Lg := by rw [hD, hJ]; unfold DD; ring
  set α₀ : ℝ := (A.card : ℝ) / p with hα₀
  have h2Lg : (0 : ℝ) < 2 ^ Lg := by positivity
  have hα16 : 16 ≤ α₀ * 2 ^ Lg := by
    rw [hα₀, div_mul_eq_mul_div, le_div_iff₀ hp0]; linarith
  have hα0 : 0 < α₀ := by
    by_contra hneg
    push Not at hneg
    nlinarith
  have key : ∀ j ≤ J, (p : ℝ) ≤ (160 / (κ * q ^ J)) ^ (2 * D) ∨
      ∃ (R : Finset (ZMod p)) (ρ : ℝ) (t : ZMod p), R.card ≤ 1 + j * n0 Lg ∧
        (∃ a ∈ R, a ≠ 0) ∧ q ^ j / 2 ≤ ρ ∧ ρ ≤ 1 ∧ Reg R ρ κ η ∧
        (11 / 10 : ℝ) ^ j * α₀ * (bohr R ρ).card ≤ (piece A (bohr R ρ) t).card := by
    intro j
    induction j with
    | zero =>
      intro _
      right
      obtain ⟨ρ, hρ1, hρ2, hreg⟩ := exists_reg ({1} : Finset (ZMod p)) D (by simpa using hD1)
        hD1 hη0 hη1 (r := 1) (by norm_num)
      obtain ⟨t, ht⟩ := exists_translate A (bohr ({1} : Finset (ZMod p)) ρ)
      refine ⟨{1}, ρ, t, by simp, ⟨1, by simp, one_ne_zero⟩, by simpa using hρ1, hρ2, hreg, ?_⟩
      rw [pow_zero, one_mul, hα₀, div_mul_eq_mul_div, div_le_iff₀ hp0]
      exact ht
    | succ j ih =>
      intro hj
      rcases ih (by omega) with h | ⟨R, ρ, t, hRc, hR0, hρlow, hρ1, hreg, hdens⟩
      · exact Or.inl h
      · have hρ0 : 0 < ρ := lt_of_lt_of_le (by positivity) hρlow
        have hRD : R.card + n0 Lg ≤ D := by
          rw [hDJ]
          have : (j + 1) * n0 Lg ≤ J * n0 Lg := Nat.mul_le_mul_right _ hj
          have e : (j + 1) * n0 Lg = j * n0 Lg + n0 Lg := by ring
          omega
        have hpj : (1 : ℝ) ≤ (11 / 10 : ℝ) ^ j := one_le_pow₀ (by norm_num)
        have hαj : 16 ≤ (11 / 10 : ℝ) ^ j * α₀ * 2 ^ Lg := by
          have : α₀ * 2 ^ Lg ≤ (11 / 10 : ℝ) ^ j * (α₀ * 2 ^ Lg) :=
            le_mul_of_one_le_left (by positivity) hpj
          linarith
        rcases step Lg D hLg hD1 h2 h3 A hsf R hRD hR0 ρ hρ0 hρ1 hreg t
            ((11 / 10 : ℝ) ^ j * α₀) hαj hdens with
          hterm | ⟨R', ρ', t', hR'c, hR'0, hρ'low, hρ'1, hreg', hdens'⟩
        · left
          refine hterm.trans (pow_le_pow_left₀ (by positivity) ?_ _)
          have hqJj : q ^ J ≤ q ^ j := pow_le_pow_of_le_one hq0.le hq1 (by omega)
          have h5 : κ * q ^ J ≤ 2 * (κ * ρ) := by
            have : q ^ J / 2 ≤ ρ := by linarith
            nlinarith
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
        · right
          refine ⟨R', ρ', t', ?_, hR'0, ?_, hρ'1, hreg', ?_⟩
          · have e : (j + 1) * n0 Lg = j * n0 Lg + n0 Lg := by ring
            omega
          · have h5 : q * (q ^ j / 2) ≤ q * ρ := mul_le_mul_of_nonneg_left hρlow hq0.le
            rw [pow_succ]
            linarith
          · have e : (11 / 10 : ℝ) ^ (j + 1) * α₀ = 11 / 10 * ((11 / 10 : ℝ) ^ j * α₀) := by
              rw [pow_succ]; ring
            rw [e]; exact hdens'
  rcases key J le_rfl with h | ⟨R, ρ, t, _, _, hρlow, _, _, hd⟩
  · exact h
  · exfalso
    have hρ0 : 0 < ρ := lt_of_lt_of_le (by positivity) hρlow
    have hB0 : (0 : ℝ) < (bohr R ρ).card := by exact_mod_cast card_bohr_pos hρ0.le
    have h1 : ((piece A (bohr R ρ) t).card : ℝ) ≤ (bohr R ρ).card := by
      exact_mod_cast card_piece_le A (bohr R ρ) t
    have h3' : (16 : ℝ) ≤ (11 / 10 : ℝ) ^ J * α₀ := by
      have h4 := pow_eleven_tenths Lg
      calc (16 : ℝ) ≤ α₀ * 2 ^ Lg := hα16
        _ ≤ α₀ * (11 / 10 : ℝ) ^ J := mul_le_mul_of_nonneg_left h4 hα0.le
        _ = (11 / 10 : ℝ) ^ J * α₀ := mul_comm _ _
    have h5 : 16 * ((bohr R ρ).card : ℝ) ≤ (11 / 10 : ℝ) ^ J * α₀ * (bohr R ρ).card :=
      mul_le_mul_of_nonneg_right h3' hB0.le
    linarith

end G16

end ModIter

section ModNum

/- # Green 16: numerical bounds for the parameters -/

open Finset

namespace G16

lemma n0_le (Lg : ℕ) (hLg : 1 ≤ Lg) : n0 Lg + 1 ≤ 2 ^ 34 * Lg ^ 4 := by
  have h1 : n0 Lg + 1 ≤ 8 * (Lg * (2 * Lg * (32 * (120 * (5 * Lg))) ^ 2) + 3) + 1 := by
    unfold n0 mm qq kk
    gcongr
    omega
  have h2 : 8 * (Lg * (2 * Lg * (32 * (120 * (5 * Lg))) ^ 2) + 3) + 1 =
      5898240000 * Lg ^ 4 + 25 := by ring
  have h3 : 1 ≤ Lg ^ 4 := Nat.one_le_pow _ _ hLg
  rw [h2] at h1
  have h4 : (2 : ℕ) ^ 34 = 17179869184 := by norm_num
  rw [h4]
  generalize Lg ^ 4 = X at *
  omega

lemma DD_le (Lg : ℕ) (hLg : 1 ≤ Lg) : DD Lg ≤ 2 ^ 37 * Lg ^ 5 := by
  have h1 := n0_le Lg hLg
  unfold DD
  have h2 : 8 * Lg * (n0 Lg + 1) ≤ 8 * Lg * (2 ^ 34 * Lg ^ 4) := Nat.mul_le_mul_left _ h1
  have h3 : 8 * Lg * (2 ^ 34 * Lg ^ 4) = 2 ^ 37 * Lg ^ 5 := by ring
  have h4 : 8 * Lg * (n0 Lg + 1) = 8 * Lg * n0 Lg + 8 * Lg := by ring
  omega

lemma two_pow_mono {n m : ℕ} (h : n ≤ m) : (2 : ℝ) ^ n ≤ 2 ^ m :=
  pow_le_pow_right₀ (by norm_num) h

lemma cast_le_two_pow (Lg : ℕ) : (Lg : ℝ) ≤ 2 ^ Lg := by
  exact_mod_cast (Nat.lt_two_pow_self (n := Lg)).le

lemma DD_real_le (Lg : ℕ) (hLg : 1 ≤ Lg) : (DD Lg : ℝ) ≤ 2 ^ (42 * Lg) := by
  have h1 : (DD Lg : ℝ) ≤ 2 ^ 37 * (Lg : ℝ) ^ 5 := by exact_mod_cast DD_le Lg hLg
  have h2 : (Lg : ℝ) ^ 5 ≤ (2 ^ Lg) ^ 5 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (cast_le_two_pow Lg) 5
  calc (DD Lg : ℝ) ≤ 2 ^ 37 * (Lg : ℝ) ^ 5 := h1
    _ ≤ 2 ^ 37 * (2 ^ Lg) ^ 5 := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = 2 ^ (37 + Lg * 5) := by rw [← pow_mul, ← pow_add]
    _ ≤ 2 ^ (42 * Lg) := two_pow_mono (by omega)

lemma n0_real_le (Lg : ℕ) (hLg : 1 ≤ Lg) : (n0 Lg : ℝ) + 1 ≤ 2 ^ (38 * Lg) := by
  have h1 : (n0 Lg : ℝ) + 1 ≤ 2 ^ 34 * (Lg : ℝ) ^ 4 := by exact_mod_cast n0_le Lg hLg
  have h2 : (Lg : ℝ) ^ 4 ≤ (2 ^ Lg) ^ 4 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (cast_le_two_pow Lg) 4
  calc (n0 Lg : ℝ) + 1 ≤ 2 ^ 34 * (Lg : ℝ) ^ 4 := h1
    _ ≤ 2 ^ 34 * (2 ^ Lg) ^ 4 := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = 2 ^ (34 + Lg * 4) := by rw [← pow_mul, ← pow_add]
    _ ≤ 2 ^ (38 * Lg) := two_pow_mono (by omega)

lemma kapS_ge (Lg : ℕ) (hLg : 1 ≤ Lg) : 1 ≤ kapS Lg (DD Lg) * 2 ^ (59 * Lg) := by
  have hD0 : (0 : ℝ) < DD Lg := by
    have : 1 ≤ DD Lg := by unfold DD; omega
    exact_mod_cast this
  have e : kapS Lg (DD Lg) = 1 / (40320 * 2 ^ Lg * (DD Lg : ℝ)) := by
    unfold kapS etaS nu0; field_simp; ring
  rw [e, div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity), one_mul]
  have h1 := DD_real_le Lg hLg
  calc (40320 : ℝ) * 2 ^ Lg * (DD Lg : ℝ) ≤ 2 ^ 16 * 2 ^ Lg * 2 ^ (42 * Lg) := by
        have : (40320 : ℝ) ≤ 2 ^ 16 := by norm_num
        gcongr
    _ = 2 ^ (16 + Lg + 42 * Lg) := by rw [← pow_add, ← pow_add]
    _ ≤ 2 ^ (59 * Lg) := two_pow_mono (by omega)

lemma qS_ge (Lg : ℕ) (hLg : 1 ≤ Lg) : 1 ≤ qS Lg (DD Lg) * 2 ^ (345 * Lg) := by
  have hD1 : 1 ≤ DD Lg := by unfold DD; omega
  have hκ0 := kapS_pos Lg (DD Lg) hD1
  have hκ := kapS_ge Lg hLg
  have hn := n0_real_le Lg hLg
  have hn0 : (0 : ℝ) < (n0 Lg : ℝ) + 1 := by positivity
  unfold qS
  rw [min_mul_of_nonneg _ _ (by positivity)]
  refine le_min ?_ ?_
  · rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity), one_mul]
    have h1 : (1 : ℝ) ≤ (kapS Lg (DD Lg) * 2 ^ (59 * Lg)) ^ 5 := one_le_pow₀ hκ
    have h2 : (3840 : ℝ) * ((n0 Lg : ℝ) + 1) ≤ 2 ^ (50 * Lg) := by
      calc (3840 : ℝ) * ((n0 Lg : ℝ) + 1) ≤ 2 ^ 12 * 2 ^ (38 * Lg) := by
            have : (3840 : ℝ) ≤ 2 ^ 12 := by norm_num
            gcongr
        _ = 2 ^ (12 + 38 * Lg) := by rw [← pow_add]
        _ ≤ 2 ^ (50 * Lg) := two_pow_mono (by omega)
    have h3 : kapS Lg (DD Lg) ^ 5 * 2 ^ (345 * Lg) =
        (kapS Lg (DD Lg) * 2 ^ (59 * Lg)) ^ 5 * 2 ^ (50 * Lg) := by
      rw [mul_pow, ← pow_mul, mul_assoc, ← pow_add]
      congr 2
      ring
    rw [h3]
    calc (3840 : ℝ) * ((n0 Lg : ℝ) + 1) ≤ 2 ^ (50 * Lg) := h2
      _ ≤ (kapS Lg (DD Lg) * 2 ^ (59 * Lg)) ^ 5 * 2 ^ (50 * Lg) :=
          le_mul_of_one_le_left (by positivity) h1
  · rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity), one_mul]
    have e : nu0 Lg * 2 ^ (345 * Lg) = 2 ^ (345 * Lg) / (60 * 2 ^ Lg) := by
      unfold nu0; field_simp
    rw [e, le_div_iff₀ (by positivity)]
    calc 4 * ((n0 Lg : ℝ) + 1) * (60 * 2 ^ Lg) = 240 * ((n0 Lg : ℝ) + 1) * 2 ^ Lg := by ring
      _ ≤ 2 ^ 8 * 2 ^ (38 * Lg) * 2 ^ Lg := by
          have : (240 : ℝ) ≤ 2 ^ 8 := by norm_num
          gcongr
      _ = 2 ^ (8 + 38 * Lg + Lg) := by rw [← pow_add, ← pow_add]
      _ ≤ 2 ^ (345 * Lg) := two_pow_mono (by omega)

/-- The final numerical bound. -/
theorem num_bound (Lg : ℕ) (hLg : 1 ≤ Lg) :
    (160 / (kapS Lg (DD Lg) * qS Lg (DD Lg) ^ (8 * Lg))) ^ (2 * DD Lg) ≤
      (2 : ℝ) ^ (2 ^ 50 * Lg ^ 7) := by
  have hD1 : 1 ≤ DD Lg := by unfold DD; omega
  set κ : ℝ := kapS Lg (DD Lg) with hκdef
  set q : ℝ := qS Lg (DD Lg) with hqdef
  have hκ0 : 0 < κ := kapS_pos Lg (DD Lg) hD1
  have hq0 : 0 < q := qS_pos Lg (DD Lg) hD1
  have hκ : 1 ≤ κ * 2 ^ (59 * Lg) := kapS_ge Lg hLg
  have hq : 1 ≤ q * 2 ^ (345 * Lg) := qS_ge Lg hLg
  have hbase : 160 / (κ * q ^ (8 * Lg)) ≤ 2 ^ (2827 * Lg ^ 2) := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : (1 : ℝ) ≤ (q * 2 ^ (345 * Lg)) ^ (8 * Lg) := one_le_pow₀ hq
    have h2 : (1 : ℝ) ≤ (κ * 2 ^ (59 * Lg)) * (q * 2 ^ (345 * Lg)) ^ (8 * Lg) :=
      one_le_mul_of_one_le_of_one_le hκ h1
    have h3 : (κ * 2 ^ (59 * Lg)) * (q * 2 ^ (345 * Lg)) ^ (8 * Lg) =
        2 ^ (59 * Lg + 345 * Lg * (8 * Lg)) * (κ * q ^ (8 * Lg)) := by
      rw [mul_pow, ← pow_mul, pow_add]; ring
    rw [h3] at h2
    have h4 : (160 : ℝ) * 2 ^ (59 * Lg + 345 * Lg * (8 * Lg)) ≤ 2 ^ (2827 * Lg ^ 2) := by
      calc (160 : ℝ) * 2 ^ (59 * Lg + 345 * Lg * (8 * Lg))
          ≤ 2 ^ 8 * 2 ^ (59 * Lg + 345 * Lg * (8 * Lg)) := by
            have : (160 : ℝ) ≤ 2 ^ 8 := by norm_num
            gcongr
        _ = 2 ^ (8 + (59 * Lg + 345 * Lg * (8 * Lg))) := by rw [← pow_add]
        _ ≤ 2 ^ (2827 * Lg ^ 2) := by
            apply two_pow_mono
            have h5 : Lg ≤ Lg ^ 2 := by nlinarith
            have h6 : 345 * Lg * (8 * Lg) = 2760 * Lg ^ 2 := by ring
            have h7 : 1 ≤ Lg ^ 2 := Nat.one_le_pow _ _ hLg
            rw [h6]
            generalize Lg ^ 2 = X at *
            omega
    have hκq : 0 < κ * q ^ (8 * Lg) := by positivity
    calc (160 : ℝ) ≤ 160 * (2 ^ (59 * Lg + 345 * Lg * (8 * Lg)) * (κ * q ^ (8 * Lg))) :=
          le_mul_of_one_le_right (by norm_num) h2
      _ = 160 * 2 ^ (59 * Lg + 345 * Lg * (8 * Lg)) * (κ * q ^ (8 * Lg)) := by ring
      _ ≤ 2 ^ (2827 * Lg ^ 2) * (κ * q ^ (8 * Lg)) :=
          mul_le_mul_of_nonneg_right h4 hκq.le
  calc (160 / (κ * q ^ (8 * Lg))) ^ (2 * DD Lg)
      ≤ ((2 : ℝ) ^ (2827 * Lg ^ 2)) ^ (2 * DD Lg) :=
        pow_le_pow_left₀ (by positivity) hbase _
    _ = (2 : ℝ) ^ (2827 * Lg ^ 2 * (2 * DD Lg)) := by rw [← pow_mul]
    _ ≤ (2 : ℝ) ^ (2 ^ 50 * Lg ^ 7) := by
        apply two_pow_mono
        have h1 := DD_le Lg hLg
        calc 2827 * Lg ^ 2 * (2 * DD Lg) ≤ 2827 * Lg ^ 2 * (2 * (2 ^ 37 * Lg ^ 5)) := by
              gcongr
          _ = 2827 * 2 ^ 38 * Lg ^ 7 := by ring
          _ ≤ 2 ^ 12 * 2 ^ 38 * Lg ^ 7 := by gcongr; norm_num
          _ = 2 ^ 50 * Lg ^ 7 := by ring

end G16

end ModNum

section ModFinal

/- # Green 16: the upper bound of Schoen and Sisask -/

open Finset

namespace G16

/-- Transfer from `{1, …, N}` to `ZMod p` and choice of the density parameter. -/
lemma transfer (N : ℕ) (hN : 1 ≤ N) (A : Finset ℕ) (hA : A ⊆ Icc 1 N)
    (hsf : Green16.SolutionFree A) (hne : A.Nonempty) :
    ∃ Lg : ℕ, 1 ≤ Lg ∧ (A.card : ℝ) * 2 ^ Lg ≤ 256 * N ∧
      (N : ℝ) ≤ 2 ^ (2 ^ 50 * Lg ^ 7) := by
  classical
  obtain ⟨p, hp, hp1, hp2⟩ := Nat.exists_prime_lt_and_le_two_mul (4 * N) (by omega)
  have : Fact p.Prime := ⟨hp⟩
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    have := Nat.le_of_dvd (by norm_num) h'
    omega
  have h3 : (3 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((3 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    have := Nat.le_of_dvd (by norm_num) h'
    omega
  have hAN : ∀ x ∈ A, 1 ≤ x ∧ x ≤ N := fun x hx => mem_Icc.1 (hA hx)
  have hinj : ∀ x ∈ A, ∀ y ∈ A, ((x : ℕ) : ZMod p) = (y : ZMod p) → x = y := by
    intro x hx y hy h
    rw [ZMod.natCast_eq_natCast_iff'] at h
    have hx' := hAN x hx
    have hy' := hAN y hy
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h
    exact h
  set Ab : Finset (ZMod p) := A.image (fun n : ℕ => (n : ZMod p)) with hAb
  have hcard : Ab.card = A.card :=
    card_image_of_injOn fun x hx y hy h => hinj x hx y hy h
  have hsfb : SolFree Ab := by
    intro x hx y hy z hz w hw hxy hxz hxw hyz hyw hzw heq
    obtain ⟨x', hx', rfl⟩ := mem_image.1 hx
    obtain ⟨y', hy', rfl⟩ := mem_image.1 hy
    obtain ⟨z', hz', rfl⟩ := mem_image.1 hz
    obtain ⟨w', hw', rfl⟩ := mem_image.1 hw
    have h1 : ((x' + 3 * y' : ℕ) : ZMod p) = ((2 * z' + 2 * w' : ℕ) : ZMod p) := by
      push_cast; exact heq
    have bx := hAN x' hx'
    have by' := hAN y' hy'
    have bz := hAN z' hz'
    have bw := hAN w' hw'
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)] at h1
    have nxy : x' ≠ y' := fun h => hxy (by rw [h])
    have nxz : x' ≠ z' := fun h => hxz (by rw [h])
    have nxw : x' ≠ w' := fun h => hxw (by rw [h])
    have nyz : y' ≠ z' := fun h => hyz (by rw [h])
    have nyw : y' ≠ w' := fun h => hyw (by rw [h])
    have nzw : z' ≠ w' := fun h => hzw (by rw [h])
    exact hsf x' hx' y' hy' z' hz' w' hw' (by simp [nxy, nxz, nxw, nyz, nyw, nzw]) h1
  have hk1 : 1 ≤ A.card := hne.card_pos
  have hkN : A.card ≤ N := by
    have := card_le_card hA
    simpa using this
  have hex : ∃ L : ℕ, 16 * p ≤ A.card * 2 ^ L :=
    ⟨16 * p, (Nat.lt_two_pow_self (n := 16 * p)).le.trans (Nat.le_mul_of_pos_left _ hk1)⟩
  set Lg : ℕ := Nat.find hex with hLgdef
  have hLg : 16 * p ≤ A.card * 2 ^ Lg := Nat.find_spec hex
  have hLg1 : 1 ≤ Lg := by
    by_contra h
    have h0 : Lg = 0 := by omega
    rw [h0] at hLg
    omega
  have hmin : A.card * 2 ^ (Lg - 1) < 16 * p := by
    have := Nat.find_min hex (m := Lg - 1) (by omega)
    omega
  have hk2 : A.card * 2 ^ Lg < 32 * p := by
    have e : 2 ^ Lg = 2 * 2 ^ (Lg - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [e]
    have : A.card * (2 * 2 ^ (Lg - 1)) = 2 * (A.card * 2 ^ (Lg - 1)) := by ring
    omega
  refine ⟨Lg, hLg1, ?_, ?_⟩
  · have h5 : A.card * 2 ^ Lg ≤ 256 * N := by omega
    exact_mod_cast h5
  · have hb := zmod_bound Lg hLg1 h2 h3 Ab hsfb (by rw [hcard]; exact_mod_cast hLg)
    have hn := num_bound Lg hLg1
    have h6 : (N : ℝ) ≤ p := by exact_mod_cast (by omega : N ≤ p)
    exact h6.trans (hb.trans hn)

/-- The quantitative bound for solution-free sets. -/
theorem main_bound : ∃ c > (0 : ℝ), ∀ N : ℕ, 1 ≤ N → ∀ A : Finset ℕ, A ⊆ Icc 1 N →
    Green16.SolutionFree A →
    (A.card : ℝ) ≤ 256 * ((N : ℝ) * Real.exp (-c * (Real.log N) ^ (1 / 7 : ℝ))) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set c₁ : ℝ := 2 ^ 50 * Real.log 2 with hc₁
  have hc₁0 : 0 < c₁ := by positivity
  have hroot : 0 < c₁ ^ (1 / 7 : ℝ) := Real.rpow_pos_of_pos hc₁0 _
  refine ⟨Real.log 2 / c₁ ^ (1 / 7 : ℝ), by positivity, ?_⟩
  intro N hN A hA hsf
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rcases A.eq_empty_or_nonempty with hAe | hne
  · rw [hAe]; simp only [card_empty, Nat.cast_zero]; positivity
  obtain ⟨Lg, hLg1, hk, hNle⟩ := transfer N hN A hA hsf hne
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have h1 : Real.log N ≤ c₁ * (Lg : ℝ) ^ 7 := by
    have := Real.log_le_log hN0 hNle
    rw [Real.log_pow] at this
    rw [hc₁]
    push_cast at this
    linarith
  have h2 : (Real.log N) ^ (1 / 7 : ℝ) ≤ c₁ ^ (1 / 7 : ℝ) * Lg := by
    have h3 := Real.rpow_le_rpow hlogN h1 (by norm_num : (0 : ℝ) ≤ 1 / 7)
    rw [Real.mul_rpow hc₁0.le (by positivity)] at h3
    have h4 : ((Lg : ℝ) ^ 7) ^ (1 / 7 : ℝ) = Lg := by
      have := Real.pow_rpow_inv_natCast (Nat.cast_nonneg Lg) (by norm_num : (7 : ℕ) ≠ 0)
      rw [one_div]
      exact_mod_cast this
    rw [h4] at h3
    exact h3
  have h5 : Real.log 2 / c₁ ^ (1 / 7 : ℝ) * (Real.log N) ^ (1 / 7 : ℝ) ≤ Lg * Real.log 2 := by
    calc Real.log 2 / c₁ ^ (1 / 7 : ℝ) * (Real.log N) ^ (1 / 7 : ℝ)
        ≤ Real.log 2 / c₁ ^ (1 / 7 : ℝ) * (c₁ ^ (1 / 7 : ℝ) * Lg) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = Lg * Real.log 2 := by field_simp
  have h6 : (2 : ℝ) ^ Lg = Real.exp (Lg * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  have h7 : Real.exp (-(Lg * Real.log 2)) ≤
      Real.exp (-(Real.log 2 / c₁ ^ (1 / 7 : ℝ)) * (Real.log N) ^ (1 / 7 : ℝ)) := by
    apply Real.exp_le_exp.2
    linarith
  have h2Lg : (0 : ℝ) < 2 ^ Lg := by positivity
  have h8 : Real.exp (-(Lg * Real.log 2)) = 1 / 2 ^ Lg := by
    rw [Real.exp_neg, ← h6, one_div]
  rw [h8] at h7
  have h9 : (A.card : ℝ) ≤ 256 * N / 2 ^ Lg := by
    rw [le_div_iff₀ h2Lg]; exact hk
  calc (A.card : ℝ) ≤ 256 * N / 2 ^ Lg := h9
    _ = 256 * ((N : ℝ) * (1 / 2 ^ Lg)) := by ring
    _ ≤ 256 * ((N : ℝ) *
          Real.exp (-(Real.log 2 / c₁ ^ (1 / 7 : ℝ)) * (Real.log N) ^ (1 / 7 : ℝ))) := by
        gcongr

end G16

theorem OMA.solution : type_of% @Green16.green_16_upper_bound := by
  obtain ⟨c, hc, h⟩ := G16.main_bound
  refine ⟨c, hc, ?_⟩
  apply Asymptotics.IsBigO.of_bound 256
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  have hmem : Green16.f N ∈ {k : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧
      Green16.SolutionFree A ∧ A.card = k} := by
    apply Nat.sSup_mem
    · refine ⟨0, ∅, Finset.empty_subset _, ?_, rfl⟩
      intro x hx
      exact absurd hx (Finset.notMem_empty x)
    · refine ⟨N, ?_⟩
      rintro k ⟨A, hA, _, rfl⟩
      have := Finset.card_le_card hA
      simpa using this
  obtain ⟨A, hA, hsf, hk⟩ := hmem
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (by positivity), ← hk]
  exact h N hN A hA hsf

end ModFinal
