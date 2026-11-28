import OMAStatements.S_oeis_a364177
import Mathlib

/-! Jacobsthal-Kazandzidis type congruence C(a p^r, b p^r) = C(a p^(r-1), b p^(r-1)) mod p^(3r), p >= 5. Base lemmas adapted from proofs/oeis-a375180.R1.H4.lean. -/

namespace LtsJacobsthal
open Finset

variable {p : ℕ} [hp : Fact p.Prime]

/-- `D p e x` : the rational `x` lies in `p^e * ℤ_(p)`. -/
def D (p e : ℕ) (x : ℚ) : Prop :=
  ∃ a : ℤ, ∃ b : ℕ, ¬ p ∣ b ∧ x * (b : ℚ) = (p : ℚ) ^ e * (a : ℚ)

lemma D.zero (e : ℕ) : D p e 0 := ⟨0, 1, hp.out.not_dvd_one, by simp⟩

omit hp in
lemma D.neg {e : ℕ} {x : ℚ} (hx : D p e x) : D p e (-x) := by
  obtain ⟨a, b, hb, h⟩ := hx
  exact ⟨-a, b, hb, by push_cast; linear_combination -h⟩

lemma D.add {e : ℕ} {x y : ℚ} (hx : D p e x) (hy : D p e y) : D p e (x + y) := by
  obtain ⟨a, b, hb, h⟩ := hx
  obtain ⟨a', b', hb', h'⟩ := hy
  refine ⟨a * b' + a' * b, b * b', ?_, ?_⟩
  · intro hd
    rcases (Nat.Prime.dvd_mul hp.out).mp hd with h1 | h1
    · exact hb h1
    · exact hb' h1
  · push_cast
    linear_combination (b' : ℚ) * h + (b : ℚ) * h'

lemma D.sub {e : ℕ} {x y : ℚ} (hx : D p e x) (hy : D p e y) : D p e (x - y) := by
  rw [sub_eq_add_neg]; exact hx.add hy.neg

lemma D.mul {e f : ℕ} {x y : ℚ} (hx : D p e x) (hy : D p f y) : D p (e + f) (x * y) := by
  obtain ⟨a, b, hb, h⟩ := hx
  obtain ⟨a', b', hb', h'⟩ := hy
  refine ⟨a * a', b * b', ?_, ?_⟩
  · intro hd
    rcases (Nat.Prime.dvd_mul hp.out).mp hd with h1 | h1
    · exact hb h1
    · exact hb' h1
  · push_cast
    rw [pow_add]
    linear_combination (y * (b' : ℚ)) * h + ((p : ℚ) ^ e * (a : ℚ)) * h'

omit hp in
lemma D.le {e f : ℕ} {x : ℚ} (hx : D p e x) (hfe : f ≤ e) : D p f x := by
  obtain ⟨a, b, hb, h⟩ := hx
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hfe
  exact ⟨(p : ℤ) ^ c * a, b, hb, by push_cast; rw [h, pow_add]; ring⟩

lemma D.int (z : ℤ) : D p 0 (z : ℚ) := ⟨z, 1, hp.out.not_dvd_one, by simp⟩

lemma D.nat (n : ℕ) : D p 0 (n : ℚ) := ⟨(n : ℤ), 1, hp.out.not_dvd_one, by simp⟩

lemma D.one : D p 0 (1 : ℚ) := ⟨1, 1, hp.out.not_dvd_one, by simp⟩

lemma D.ppow (e : ℕ) : D p e ((p : ℚ) ^ e) := ⟨1, 1, hp.out.not_dvd_one, by simp⟩

lemma D.mul0 {e : ℕ} {x y : ℚ} (hx : D p e x) (hy : D p 0 y) : D p e (x * y) :=
  (hx.mul hy).le (by omega)

lemma D.mul0' {e : ℕ} {x y : ℚ} (hy : D p 0 y) (hx : D p e x) : D p e (y * x) :=
  (hy.mul hx).le (by omega)

omit hp in
lemma D.inv {u : ℕ} (hu : ¬ p ∣ u) : D p 0 ((u : ℚ)⁻¹) := by
  have hu0 : (u : ℚ) ≠ 0 := by
    intro h
    apply hu
    have h0 : u = 0 := by exact_mod_cast h
    rw [h0]; exact dvd_zero p
  exact ⟨1, u, hu, by rw [inv_mul_cancel₀ hu0]; simp⟩

lemma D.sum {ι : Type*} {e : ℕ} (s : Finset ι) (f : ι → ℚ) (h : ∀ i ∈ s, D p e (f i)) :
    D p e (∑ i ∈ s, f i) :=
  Finset.sum_induction f (D p e) (fun _ _ ha hb => ha.add hb) (D.zero e) h

lemma D.prod {ι : Type*} (s : Finset ι) (f : ι → ℚ) (h : ∀ i ∈ s, D p 0 (f i)) :
    D p 0 (∏ i ∈ s, f i) :=
  Finset.prod_induction f (D p 0) (fun _ _ ha hb => (ha.mul hb).le (by omega)) D.one h

lemma D.pow {e : ℕ} {x : ℚ} (hx : D p e x) (n : ℕ) : D p (e * n) (x ^ n) := by
  induction n with
  | zero => simpa using (D.one (p := p))
  | succ n ih => rw [pow_succ, Nat.mul_succ]; exact ih.mul hx

lemma D.cancel {e c : ℕ} {x : ℚ} (h : D p (e + c) ((p : ℚ) ^ c * x)) : D p e x := by
  obtain ⟨a, b, hb, h⟩ := h
  refine ⟨a, b, hb, ?_⟩
  have hpc : ((p : ℚ) ^ c) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.out.ne_zero)
  apply mul_left_cancel₀ hpc
  rw [pow_add] at h
  linear_combination h

lemma D.ucancel {e u : ℕ} {x : ℚ} (hu : ¬ p ∣ u) (h : D p e ((u : ℚ) * x)) : D p e x := by
  obtain ⟨a, b, hb, h⟩ := h
  refine ⟨a, u * b, ?_, by push_cast; linear_combination h⟩
  intro hd
  rcases (Nat.Prime.dvd_mul hp.out).mp hd with h1 | h1
  · exact hu h1
  · exact hb h1

lemma D.dvd {e : ℕ} {z : ℤ} (h : D p e (z : ℚ)) : (p : ℤ) ^ e ∣ z := by
  obtain ⟨a, b, hb, h⟩ := h
  have h2 : z * (b : ℤ) = (p : ℤ) ^ e * a := by exact_mod_cast h
  have hc : IsCoprime ((p : ℤ) ^ e) (b : ℤ) := by
    have h3 : Nat.Coprime (p ^ e) b :=
      Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hb)
    have h4 := Nat.isCoprime_iff_coprime.mpr h3
    simpa using h4
  exact hc.dvd_of_dvd_mul_right ⟨a, h2⟩

/-! ### index sets -/

/-- the integers `0 < i < L` prime to `p` -/
def U (p L : ℕ) : Finset ℕ := (Finset.range L).filter (fun i => ¬ p ∣ i)

lemma mem_U {p L i : ℕ} : i ∈ U p L ↔ i < L ∧ ¬ p ∣ i := by
  simp [U]

omit hp in
lemma sum_U_blocks {q : ℕ} (hpq : p ∣ q) (f : ℕ → ℚ) (t : ℕ) :
    ∑ i ∈ U p (t * q), f i = ∑ h ∈ Finset.range t, ∑ u ∈ U p q, f (h * q + u) := by
  induction t with
  | zero => simp [U]
  | succ t ih =>
    rw [Finset.sum_range_succ, ← ih]
    unfold U
    rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, add_one_mul,
      Finset.sum_range_add]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    have h1 : p ∣ t * q + x ↔ p ∣ x := Nat.dvd_add_right (dvd_mul_of_dvd_right hpq t)
    simp only [h1]

lemma sum_range_mul_split {M : Type*} [AddCommMonoid M] (m n : ℕ) (hm : 0 < m)
    (f : ℕ → M) :
    ∑ k ∈ Finset.range (m * n), f k =
      ∑ k ∈ (Finset.range (m * n)).filter (fun k => ¬ m ∣ k), f k +
        ∑ c ∈ Finset.range n, f (m * c) := by
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (m * n)) (fun k => m ∣ k), add_comm]
  congr 1
  have h1 : (Finset.range (m * n)).filter (fun k => m ∣ k) =
      (Finset.range n).image (fun c => m * c) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hk, c, rfl⟩
      exact ⟨c, lt_of_mul_lt_mul_left hk (Nat.zero_le m), rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨by nlinarith, dvd_mul_right m c⟩
  rw [h1, Finset.sum_image]
  intro x _ y _ h
  exact Nat.eq_of_mul_eq_mul_left hm h

lemma prod_range_mul_split {M : Type*} [CommMonoid M] (m n : ℕ) (hm : 0 < m)
    (f : ℕ → M) :
    ∏ k ∈ Finset.range (m * n), f k =
      (∏ k ∈ (Finset.range (m * n)).filter (fun k => ¬ m ∣ k), f k) *
        ∏ c ∈ Finset.range n, f (m * c) := by
  rw [← Finset.prod_filter_mul_prod_filter_not (Finset.range (m * n)) (fun k => m ∣ k), mul_comm]
  congr 1
  have h1 : (Finset.range (m * n)).filter (fun k => m ∣ k) =
      (Finset.range n).image (fun c => m * c) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hk, c, rfl⟩
      exact ⟨c, lt_of_mul_lt_mul_left hk (Nat.zero_le m), rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨by nlinarith, dvd_mul_right m c⟩
  rw [h1, Finset.prod_image]
  intro x _ y _ h
  exact Nat.eq_of_mul_eq_mul_left hm h

/-! ### binomials as products -/

/-- `Gp n m = ∏_{0 < i < m} (1 - n / i)` (the factor `i = 0` is `1`). -/
def Gp (n : ℚ) (m : ℕ) : ℚ := ∏ i ∈ Finset.range m, (1 - n / (i : ℚ))

omit hp in
lemma choose_mul_eq (n k : ℕ) :
    (n.choose (k + 1) : ℚ) * ((k : ℚ) + 1) = (n : ℚ) * (-1) ^ k * Gp n (k + 1) := by
  induction k with
  | zero => simp [Gp]
  | succ k ih =>
    have h1 : (n.choose (k + 1 + 1) : ℚ) * ((k : ℚ) + 1 + 1) =
        (n.choose (k + 1) : ℚ) * ((n : ℚ) - ((k : ℚ) + 1)) := by
      rcases le_or_gt (k + 1) n with h | h
      · have h2 := congrArg (Nat.cast (R := ℚ)) (Nat.choose_succ_right_eq n (k + 1))
        push_cast [Nat.cast_sub h] at h2
        linarith
      · rw [Nat.choose_eq_zero_of_lt (by omega : n < k + 1 + 1), Nat.choose_eq_zero_of_lt h]
        simp
    have hG : Gp n (k + 1 + 1) = Gp n (k + 1) * (1 - (n : ℚ) / ((k : ℚ) + 1)) := by
      unfold Gp
      rw [Finset.prod_range_succ]
      push_cast
      ring
    have hk : ((k : ℚ) + 1) ≠ 0 := by positivity
    have h3 : (n : ℚ) * (-1) ^ (k + 1) * (Gp n (k + 1) * (1 - (n : ℚ) / ((k : ℚ) + 1))) =
        ((n : ℚ) * (-1) ^ k * Gp n (k + 1)) * (((n : ℚ) - ((k : ℚ) + 1)) / ((k : ℚ) + 1)) := by
      field_simp
      ring
    have h4 : ((n.choose (k + 1) : ℚ) * ((k : ℚ) + 1)) * (((n : ℚ) - ((k : ℚ) + 1)) / ((k : ℚ) + 1)) =
        (n.choose (k + 1) : ℚ) * ((n : ℚ) - ((k : ℚ) + 1)) := by
      field_simp
    push_cast
    rw [hG, h3, ← ih, h4, ← h1]

omit hp in
lemma choose_mul_eq' (n k : ℕ) (hk : 1 ≤ k) :
    (n.choose k : ℚ) * (k : ℚ) = -((n : ℚ) * (-1) ^ k * Gp n k) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have h := choose_mul_eq n k'
  push_cast
  rw [h, pow_succ]
  ring

/-- `R p x L = ∏_{0 < i < L, p ∤ i} (1 - x / i)` -/
def R (p : ℕ) (x : ℚ) (L : ℕ) : ℚ := ∏ i ∈ U p L, (1 - x / (i : ℚ))

omit hp in
lemma Gp_split (hp0 : 0 < p) (x : ℚ) (j : ℕ) :
    Gp x (p * j) = R p x (p * j) * Gp (x / p) j := by
  unfold Gp R U
  rw [prod_range_mul_split p j hp0]
  congr 1
  refine Finset.prod_congr rfl fun c _ => ?_
  push_cast
  rw [div_div]

lemma choose_ratio (hp2 : p ≠ 2) (n j : ℕ) :
    ((p * n).choose (p * j) : ℚ) = (n.choose j : ℚ) * R p ((p * n : ℕ) : ℚ) (p * j) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [R, U]
  have hp0 : 0 < p := hp.out.pos
  have hodd : Odd p := hp.out.odd_of_ne_two hp2
  have h1 := choose_mul_eq' (p * n) (p * j) (by nlinarith)
  have h2 := choose_mul_eq' n j hj
  have h3 := Gp_split hp0 ((p * n : ℕ) : ℚ) j
  have h4 : ((p * n : ℕ) : ℚ) / (p : ℚ) = (n : ℚ) := by
    push_cast
    field_simp
  have h5 : (-1 : ℚ) ^ (p * j) = (-1) ^ j := by
    rw [pow_mul, hodd.neg_one_pow]
  rw [h3, h4, h5] at h1
  have hpj : ((p * j : ℕ) : ℚ) ≠ 0 := by
    have : 0 < p * j := Nat.mul_pos hp0 hj
    positivity
  have hj0 : (j : ℚ) ≠ 0 := by positivity
  have hpq : (p : ℚ) ≠ 0 := by positivity
  apply mul_right_cancel₀ hpj
  rw [h1]
  push_cast
  have h6 : (n : ℚ) * (-1) ^ j * Gp n j = -((n.choose j : ℚ) * (j : ℚ)) := by rw [h2]; ring
  linear_combination (-(p : ℚ) * R p ((p : ℚ) * (n : ℚ)) (p * j)) * h6

/-! ### expansions of `1/(u+a)^j` -/

lemma D.pow0 {x : ℚ} (hx : D p 0 x) (n : ℕ) : D p 0 (x ^ n) :=
  (hx.pow n).le (Nat.zero_le _)

lemma D.two : D p 0 (2 : ℚ) := by simpa using D.nat (p := p) 2

lemma D.three : D p 0 (3 : ℚ) := by simpa using D.nat (p := p) 3

lemma exp1_D {s : ℕ} {u v a : ℚ} (hu0 : u ≠ 0) (hv0 : v ≠ 0) (h : v = u + a)
    (hu : D p 0 u⁻¹) (hv : D p 0 v⁻¹) (ha : D p s a) :
    D p (4 * s) (v⁻¹ - (u⁻¹ - a * u⁻¹ ^ 2 + a ^ 2 * u⁻¹ ^ 3 - a ^ 3 * u⁻¹ ^ 4)) := by
  have h1 : v⁻¹ - (u⁻¹ - a * u⁻¹ ^ 2 + a ^ 2 * u⁻¹ ^ 3 - a ^ 3 * u⁻¹ ^ 4) =
      a ^ 4 * u⁻¹ ^ 4 * v⁻¹ := by
    subst h
    field_simp
    ring
  rw [h1]
  exact (((ha.pow 4).mul0 (hu.pow0 4)).mul0 hv).le (by omega)

lemma exp2_D {s : ℕ} {u v a : ℚ} (hu0 : u ≠ 0) (hv0 : v ≠ 0) (h : v = u + a)
    (hu : D p 0 u⁻¹) (hu' : D p 0 u) (hv : D p 0 v⁻¹) (ha : D p s a) :
    D p (2 * s) (v⁻¹ ^ 2 - (u⁻¹ ^ 2 - 2 * a * u⁻¹ ^ 3)) := by
  have h1 : v⁻¹ ^ 2 - (u⁻¹ ^ 2 - 2 * a * u⁻¹ ^ 3) =
      a ^ 2 * ((3 * u + 2 * a) * u⁻¹ ^ 3 * v⁻¹ ^ 2) := by
    subst h
    field_simp
    ring
  rw [h1]
  have ha0 : D p 0 a := ha.le (Nat.zero_le _)
  have h2 : D p 0 (3 * u + 2 * a) := (D.three.mul0 hu').add (D.two.mul0 ha0)
  exact ((ha.pow 2).mul0 ((h2.mul0 (hu.pow0 3)).mul0 (hv.pow0 2))).le (by omega)

lemma exp3_D {s : ℕ} {u v a : ℚ} (hu0 : u ≠ 0) (hv0 : v ≠ 0) (h : v = u + a)
    (hu : D p 0 u⁻¹) (hu' : D p 0 u) (hv : D p 0 v⁻¹) (ha : D p s a) :
    D p (2 * s) (v⁻¹ ^ 3 - (u⁻¹ ^ 3 - 3 * a * u⁻¹ ^ 4)) := by
  have h1 : v⁻¹ ^ 3 - (u⁻¹ ^ 3 - 3 * a * u⁻¹ ^ 4) =
      a ^ 2 * ((2 * (3 * u ^ 2) + 2 * (2 * (2 * (u * a))) + 3 * a ^ 2) * u⁻¹ ^ 4 * v⁻¹ ^ 3) := by
    subst h
    field_simp
    ring
  rw [h1]
  have ha0 : D p 0 a := ha.le (Nat.zero_le _)
  have h2 : D p 0 (2 * (3 * u ^ 2) + 2 * (2 * (2 * (u * a))) + 3 * a ^ 2) :=
    ((D.two.mul0 (D.three.mul0 (hu'.pow0 2))).add
      (D.two.mul0 (D.two.mul0 (D.two.mul0 (hu'.mul0 ha0))))).add (D.three.mul0 (ha0.pow0 2))
  exact ((ha.pow 2).mul0 ((h2.mul0 (hu.pow0 4)).mul0 (hv.pow0 3))).le (by omega)

/-! ### products -/

lemma prod_congr_D {ι : Type*} [DecidableEq ι] {e : ℕ} (s : Finset ι) (f g : ι → ℚ)
    (hf : ∀ i ∈ s, D p 0 (f i)) (hg : ∀ i ∈ s, D p 0 (g i)) (h : ∀ i ∈ s, D p e (f i - g i)) :
    D p e (∏ i ∈ s, f i - ∏ i ∈ s, g i) := by
  induction s using Finset.induction_on with
  | empty => simpa using D.zero (p := p) e
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have h1 : f a * ∏ i ∈ s, f i - g a * ∏ i ∈ s, g i =
        (f a - g a) * ∏ i ∈ s, f i + g a * (∏ i ∈ s, f i - ∏ i ∈ s, g i) := by ring
    rw [h1]
    have hs : ∀ i ∈ s, i ∈ insert a s := fun i hi => Finset.mem_insert_of_mem hi
    exact ((h a (Finset.mem_insert_self a s)).mul0 (D.prod s f fun i hi => hf i (hs i hi))).add
      ((hg a (Finset.mem_insert_self a s)).mul0'
        (ih (fun i hi => hf i (hs i hi)) (fun i hi => hg i (hs i hi)) (fun i hi => h i (hs i hi))))

lemma prod_expand2 {ι : Type*} [DecidableEq ι] (hp2 : ¬ p ∣ 2) (s : Finset ι)
    (a : ι → ℚ) (x : ℚ) (hx : D p 0 x) (ha : ∀ i ∈ s, D p 0 (a i)) :
    ∃ W : ℚ, D p 0 W ∧ ∏ i ∈ s, (1 - x * a i) =
      1 - x * (∑ i ∈ s, a i) + x ^ 2 * (((∑ i ∈ s, a i) ^ 2 - ∑ i ∈ s, a i ^ 2) / 2) +
        x ^ 3 * W := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0, D.zero 0, by simp⟩
  | insert b s hb ih =>
    obtain ⟨W, hW, hprod⟩ := ih (fun i hi => ha i (Finset.mem_insert_of_mem hi))
    have hab := ha b (Finset.mem_insert_self b s)
    have hS1 : D p 0 (∑ i ∈ s, a i) :=
      D.sum s a fun i hi => ha i (Finset.mem_insert_of_mem hi)
    have hS2 : D p 0 (∑ i ∈ s, a i ^ 2) :=
      D.sum s _ fun i hi => (ha i (Finset.mem_insert_of_mem hi)).pow0 2
    have h2 : D p 0 ((2 : ℚ)⁻¹) := by simpa using D.inv (p := p) hp2
    have hE : D p 0 (((∑ i ∈ s, a i) ^ 2 - ∑ i ∈ s, a i ^ 2) / 2) := by
      rw [div_eq_mul_inv]
      exact ((hS1.pow0 2).sub hS2).mul0 h2
    refine ⟨W - a b * (((∑ i ∈ s, a i) ^ 2 - ∑ i ∈ s, a i ^ 2) / 2) - x * a b * W, ?_, ?_⟩
    · exact (hW.sub (hab.mul0 hE)).sub ((hx.mul0 hab).mul0 hW)
    · rw [Finset.prod_insert hb, Finset.sum_insert hb, Finset.sum_insert hb, hprod]
      ring

/-! ### symmetries of `U p q` -/

omit hp in
lemma sum_U_reflect {q : ℕ} (hpq : p ∣ q) (f : ℕ → ℚ) :
    ∑ u ∈ U p q, f u = ∑ u ∈ U p q, f (q - u) := by
  symm
  have hmem : ∀ u ∈ U p q, q - u ∈ U p q := by
    intro u hu
    obtain ⟨hlt, hnd⟩ := mem_U.mp hu
    have hu0 : u ≠ 0 := by
      rintro rfl
      exact hnd (dvd_zero p)
    refine mem_U.mpr ⟨by omega, ?_⟩
    intro hd
    have h1 : q - u + u = q := Nat.sub_add_cancel (le_of_lt hlt)
    have h2 : p ∣ q - u + u := by rw [h1]; exact hpq
    exact hnd ((Nat.dvd_add_right hd).mp h2)
  have hinv : ∀ u ∈ U p q, q - (q - u) = u := by
    intro u hu
    obtain ⟨hlt, _⟩ := mem_U.mp hu
    omega
  exact Finset.sum_nbij' (fun u => q - u) (fun u => q - u) hmem hmem hinv hinv
    (fun u _ => rfl)

omit hp in
lemma sum_U_double {q : ℕ} (hp' : p.Prime) (hp2 : ¬ p ∣ 2) (hpq : p ∣ q)
    (hq : Nat.Coprime q 2) (f : ℕ → ℚ) :
    ∑ u ∈ U p q, f (2 * u % q) = ∑ u ∈ U p q, f u := by
  have hinj : Set.InjOn (fun u => 2 * u % q) (U p q : Set ℕ) := by
    intro u hu v hv h
    have hu' := mem_U.mp (Finset.mem_coe.mp hu)
    have hv' := mem_U.mp (Finset.mem_coe.mp hv)
    have h1 : 2 * u ≡ 2 * v [MOD q] := h
    have h2 : u ≡ v [MOD q] := Nat.ModEq.cancel_left_of_coprime hq h1
    exact Nat.ModEq.eq_of_lt_of_lt h2 hu'.1 hv'.1
  have himg : (U p q).image (fun u => 2 * u % q) = U p q := by
    apply Finset.eq_of_subset_of_card_le
    · intro w hw
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
      have hu' := mem_U.mp hu
      have hq0 : 0 < q := by omega
      refine mem_U.mpr ⟨Nat.mod_lt _ hq0, ?_⟩
      intro hd
      have h3 : p ∣ 2 * u := (Nat.dvd_mod_iff hpq).mp hd
      rcases (Nat.Prime.dvd_mul hp').mp h3 with h4 | h4
      · exact hp2 h4
      · exact hu'.2 h4
    · rw [Finset.card_image_of_injOn hinj]
  calc ∑ u ∈ U p q, f (2 * u % q)
      = ∑ w ∈ (U p q).image (fun u => 2 * u % q), f w := by
        rw [Finset.sum_image hinj]
    _ = ∑ u ∈ U p q, f u := by rw [himg]

lemma D_inv_pow_congr {s x y : ℕ} (hx : ¬ p ∣ x) (hy : ¬ p ∣ y)
    (h : D p s ((x : ℚ) - (y : ℚ))) (j : ℕ) :
    D p s (((x : ℚ)⁻¹) ^ j - ((y : ℚ)⁻¹) ^ j) := by
  have hx0 : (x : ℚ) ≠ 0 := by
    intro h0
    apply hx
    have h1 : x = 0 := by exact_mod_cast h0
    rw [h1]; exact dvd_zero p
  have hy0 : (y : ℚ) ≠ 0 := by
    intro h0
    apply hy
    have h1 : y = 0 := by exact_mod_cast h0
    rw [h1]; exact dvd_zero p
  have hxx : (x : ℚ) * (x : ℚ)⁻¹ = 1 := mul_inv_cancel₀ hx0
  have hyy : (y : ℚ) * (y : ℚ)⁻¹ = 1 := mul_inv_cancel₀ hy0
  have h1 : D p s ((x : ℚ)⁻¹ - (y : ℚ)⁻¹) := by
    have h2 : (x : ℚ)⁻¹ - (y : ℚ)⁻¹ = -(((x : ℚ) - (y : ℚ)) * ((x : ℚ)⁻¹ * (y : ℚ)⁻¹)) := by
      linear_combination (y : ℚ)⁻¹ * hxx - (x : ℚ)⁻¹ * hyy
    rw [h2]
    exact (h.mul0 (((D.inv hx).mul (D.inv hy)).le (by omega))).neg
  induction j with
  | zero => simpa using D.zero (p := p) s
  | succ j ih =>
    have h3 : ((x : ℚ)⁻¹) ^ (j + 1) - ((y : ℚ)⁻¹) ^ (j + 1) =
        (x : ℚ)⁻¹ * (((x : ℚ)⁻¹) ^ j - ((y : ℚ)⁻¹) ^ j) +
          ((x : ℚ)⁻¹ - (y : ℚ)⁻¹) * ((y : ℚ)⁻¹) ^ j := by ring
    rw [h3]
    exact ((D.inv hx).mul0' ih).add (h1.mul0 ((D.inv hy).pow0 j))

/-! ### power sums over the units below `p^s` -/

/-- `sg p q j = ∑_{0<u<q, p ∤ u} u^(-j)` -/
def sg (p q j : ℕ) : ℚ := ∑ u ∈ U p q, ((u : ℚ)⁻¹) ^ j

lemma sg_scale (hp2 : ¬ p ∣ 2) {s : ℕ} (hs : 1 ≤ s) (j : ℕ) :
    D p s (((2 : ℚ) ^ j - 1) * sg p (p ^ s) j) := by
  have hpq : p ∣ p ^ s := dvd_pow_self p (by omega)
  have hq2 : Nat.Coprime (p ^ s) 2 :=
    Nat.Coprime.pow_left s ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hp2)
  have h1 : sg p (p ^ s) j = ∑ u ∈ U p (p ^ s), (((2 * u % p ^ s : ℕ) : ℚ)⁻¹) ^ j := by
    unfold sg
    exact (sum_U_double hp.out hp2 hpq hq2 (fun w => ((w : ℚ)⁻¹) ^ j)).symm
  have h2 : D p s (∑ u ∈ U p (p ^ s),
      ((((2 * u % p ^ s : ℕ) : ℚ)⁻¹) ^ j - (((2 * u : ℕ) : ℚ)⁻¹) ^ j)) := by
    apply D.sum
    intro u hu
    have hu' := mem_U.mp hu
    have h2u : ¬ p ∣ 2 * u := by
      intro hd
      rcases (Nat.Prime.dvd_mul hp.out).mp hd with h4 | h4
      · exact hp2 h4
      · exact hu'.2 h4
    have hmod : ¬ p ∣ 2 * u % p ^ s := fun hd => h2u ((Nat.dvd_mod_iff hpq).mp hd)
    apply D_inv_pow_congr hmod h2u
    have h5 : ((2 * u % p ^ s : ℕ) : ℚ) - ((2 * u : ℕ) : ℚ) =
        -((p : ℚ) ^ s * ((2 * u / p ^ s : ℕ) : ℚ)) := by
      have h6 := Nat.div_add_mod (2 * u) (p ^ s)
      have h7 : ((p ^ s * (2 * u / p ^ s) + 2 * u % p ^ s : ℕ) : ℚ) = ((2 * u : ℕ) : ℚ) := by
        rw [h6]
      push_cast at h7 ⊢
      linarith
    rw [h5]
    exact ((D.ppow s).mul0 (D.nat _)).neg
  rw [Finset.sum_sub_distrib, ← h1] at h2
  have h3 : ∑ u ∈ U p (p ^ s), (((2 * u : ℕ) : ℚ)⁻¹) ^ j = ((2 : ℚ)⁻¹) ^ j * sg p (p ^ s) j := by
    unfold sg
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    push_cast
    rw [mul_inv, mul_pow]
  rw [h3] at h2
  have h4 : ((2 : ℚ) ^ j - 1) * sg p (p ^ s) j =
      (2 : ℚ) ^ j * (sg p (p ^ s) j - ((2 : ℚ)⁻¹) ^ j * sg p (p ^ s) j) := by
    have h5 : (2 : ℚ) ^ j * ((2 : ℚ)⁻¹) ^ j = 1 := by
      rw [← mul_pow]; norm_num
    linear_combination (sg p (p ^ s) j) * h5
  rw [h4]
  exact (D.two.pow0 j).mul0' h2

/-- generic shifted sums: `v = u + a` with `a ∈ p^s ℤ_(p)` -/
lemma shift_sums {s : ℕ} (a : ℚ) (ha : D p s a) (v : ℕ → ℚ)
    (hv : ∀ u ∈ U p (p ^ s), v u = (u : ℚ) + a ∧ v u ≠ 0 ∧ D p 0 (v u)⁻¹) :
    D p (4 * s) (∑ u ∈ U p (p ^ s), (v u)⁻¹ -
      (sg p (p ^ s) 1 - a * sg p (p ^ s) 2 + a ^ 2 * sg p (p ^ s) 3 - a ^ 3 * sg p (p ^ s) 4)) ∧
    D p (2 * s) (∑ u ∈ U p (p ^ s), (v u)⁻¹ ^ 2 -
      (sg p (p ^ s) 2 - 2 * a * sg p (p ^ s) 3)) ∧
    D p (2 * s) (∑ u ∈ U p (p ^ s), (v u)⁻¹ ^ 3 -
      (sg p (p ^ s) 3 - 3 * a * sg p (p ^ s) 4)) := by
  have hu : ∀ u ∈ U p (p ^ s), (u : ℚ) ≠ 0 ∧ D p 0 ((u : ℚ)⁻¹) := by
    intro u hu
    obtain ⟨_, hnd⟩ := mem_U.mp hu
    refine ⟨?_, D.inv hnd⟩
    intro h0
    apply hnd
    have h1 : u = 0 := by exact_mod_cast h0
    rw [h1]; exact dvd_zero p
  refine ⟨?_, ?_, ?_⟩
  · have h1 : ∑ u ∈ U p (p ^ s), (v u)⁻¹ -
        (sg p (p ^ s) 1 - a * sg p (p ^ s) 2 + a ^ 2 * sg p (p ^ s) 3 - a ^ 3 * sg p (p ^ s) 4) =
        ∑ u ∈ U p (p ^ s), ((v u)⁻¹ - ((u : ℚ)⁻¹ - a * (u : ℚ)⁻¹ ^ 2 + a ^ 2 * (u : ℚ)⁻¹ ^ 3 -
          a ^ 3 * (u : ℚ)⁻¹ ^ 4)) := by
      simp only [sg, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum, pow_one]
    rw [h1]
    apply D.sum
    intro u hmem
    obtain ⟨h2, h3, h4⟩ := hv u hmem
    exact exp1_D (hu u hmem).1 h3 h2 (hu u hmem).2 h4 ha
  · have h1 : ∑ u ∈ U p (p ^ s), (v u)⁻¹ ^ 2 - (sg p (p ^ s) 2 - 2 * a * sg p (p ^ s) 3) =
        ∑ u ∈ U p (p ^ s), ((v u)⁻¹ ^ 2 - ((u : ℚ)⁻¹ ^ 2 - 2 * a * (u : ℚ)⁻¹ ^ 3)) := by
      simp only [sg, Finset.sum_sub_distrib, Finset.mul_sum]
    rw [h1]
    apply D.sum
    intro u hmem
    obtain ⟨h2, h3, h4⟩ := hv u hmem
    exact exp2_D (hu u hmem).1 h3 h2 (hu u hmem).2 (D.nat u) h4 ha
  · have h1 : ∑ u ∈ U p (p ^ s), (v u)⁻¹ ^ 3 - (sg p (p ^ s) 3 - 3 * a * sg p (p ^ s) 4) =
        ∑ u ∈ U p (p ^ s), ((v u)⁻¹ ^ 3 - ((u : ℚ)⁻¹ ^ 3 - 3 * a * (u : ℚ)⁻¹ ^ 4)) := by
      simp only [sg, Finset.sum_sub_distrib, Finset.mul_sum]
    rw [h1]
    apply D.sum
    intro u hmem
    obtain ⟨h2, h3, h4⟩ := hv u hmem
    exact exp3_D (hu u hmem).1 h3 h2 (hu u hmem).2 (D.nat u) h4 ha
/-! ### derived power sum facts -/

omit hp in
lemma D.congr {e : ℕ} {x y : ℚ} (h : D p e x) (hxy : x = y) : D p e y := hxy ▸ h

lemma sg_D0 (q j : ℕ) : D p 0 (sg p q j) :=
  D.sum _ _ fun _ hu => (D.inv (mem_U.mp hu).2).pow0 j

/-- `Eps p ε`: `ε = 0` and `p ∤ 15`, or `ε = 1` and `p = 5`. -/
def Eps (p ε : ℕ) : Prop := (ε = 0 ∧ ¬ p ∣ 15) ∨ (ε = 1 ∧ p = 5)

omit hp in
lemma Eps.le_one {ε : ℕ} (h : Eps p ε) : ε ≤ 1 := by
  rcases h with ⟨h, _⟩ | ⟨h, _⟩ <;> omega

lemma sg2 (h5 : 5 ≤ p) {s : ℕ} (hs : 1 ≤ s) : D p s (sg p (p ^ s) 2) := by
  have hp2 : ¬ p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega)
  have hp3 : ¬ p ∣ 3 := Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega)
  have h := sg_scale hp2 hs 2
  exact D.ucancel hp3 (h.congr (by push_cast; ring))

lemma sg4 (h5 : 5 ≤ p) {ε : ℕ} (hε : Eps p ε) {s : ℕ} (hs : 1 ≤ s) :
    D p s ((p : ℚ) ^ ε * sg p (p ^ s) 4) := by
  have hp2 : ¬ p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega)
  have hp3 : ¬ p ∣ 3 := Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega)
  have h := sg_scale hp2 hs 4
  rcases hε with ⟨rfl, h15⟩ | ⟨rfl, h55⟩
  · have h6 : D p s (sg p (p ^ s) 4) := D.ucancel h15 (h.congr (by push_cast; ring))
    exact h6.congr (by ring)
  · have h6 : D p s (((3 : ℕ) : ℚ) * ((p : ℚ) ^ 1 * sg p (p ^ s) 4)) := by
      refine h.congr ?_
      rw [h55]
      push_cast
      ring
    exact D.ucancel hp3 h6

lemma refl_sums {s : ℕ} (hs : 1 ≤ s) :
    D p (4 * s) (2 * sg p (p ^ s) 1 + (p : ℚ) ^ s * sg p (p ^ s) 2 +
      ((p : ℚ) ^ s) ^ 2 * sg p (p ^ s) 3 + ((p : ℚ) ^ s) ^ 3 * sg p (p ^ s) 4) ∧
    D p (2 * s) (2 * sg p (p ^ s) 3 + 3 * (p : ℚ) ^ s * sg p (p ^ s) 4) := by
  have hpq : p ∣ p ^ s := dvd_pow_self p (by omega)
  have hv : ∀ u ∈ U p (p ^ s), (-(((p ^ s - u : ℕ) : ℚ))) = (u : ℚ) + (-(p : ℚ) ^ s) ∧
      (-(((p ^ s - u : ℕ) : ℚ))) ≠ 0 ∧ D p 0 (-(((p ^ s - u : ℕ) : ℚ)))⁻¹ := by
    intro u hu
    obtain ⟨hlt, hnd⟩ := mem_U.mp hu
    have hw : ¬ p ∣ p ^ s - u := by
      intro hd
      have h1 : p ^ s - u + u = p ^ s := Nat.sub_add_cancel (le_of_lt hlt)
      have h2 : p ∣ p ^ s - u + u := by rw [h1]; exact hpq
      exact hnd ((Nat.dvd_add_right hd).mp h2)
    have hw0 : ((p ^ s - u : ℕ) : ℚ) ≠ 0 := by
      have h1 : p ^ s - u ≠ 0 := by omega
      exact_mod_cast h1
    refine ⟨?_, neg_ne_zero.mpr hw0, ?_⟩
    · rw [Nat.cast_sub (le_of_lt hlt)]
      push_cast
      ring
    · rw [inv_neg]
      exact (D.inv hw).neg
  obtain ⟨h1, _, h3⟩ :=
    shift_sums (-(p : ℚ) ^ s) (D.ppow s).neg (fun u => -(((p ^ s - u : ℕ) : ℚ))) hv
  have hr1 : ∑ u ∈ U p (p ^ s), (-(((p ^ s - u : ℕ) : ℚ)))⁻¹ = -sg p (p ^ s) 1 := by
    have h := sum_U_reflect hpq (fun w => (w : ℚ)⁻¹ ^ 1)
    simp only [sg]
    rw [h, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [inv_neg, pow_one]
  have hr3 : ∑ u ∈ U p (p ^ s), (-(((p ^ s - u : ℕ) : ℚ)))⁻¹ ^ 3 = -sg p (p ^ s) 3 := by
    have h := sum_U_reflect hpq (fun w => (w : ℚ)⁻¹ ^ 3)
    simp only [sg]
    rw [h, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [inv_neg]
    ring
  rw [hr1] at h1
  rw [hr3] at h3
  exact ⟨h1.neg.congr (by ring), h3.neg.congr (by ring)⟩

lemma sg3 (h5 : 5 ≤ p) {ε : ℕ} (hε : Eps p ε) {s : ℕ} (hs : 1 ≤ s) :
    D p s (sg p (p ^ s) 3) ∧ D p (2 * s) ((p : ℚ) ^ ε * sg p (p ^ s) 3) := by
  have hp2 : ¬ p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega)
  obtain ⟨_, h3⟩ := refl_sums (p := p) hs
  have h4 := sg4 h5 hε hs
  have hσ4 : D p 0 (sg p (p ^ s) 4) := sg_D0 _ _
  constructor
  · have h6 : D p s (((2 : ℕ) : ℚ) * sg p (p ^ s) 3) := by
      have h7 := (h3.le (by omega : s ≤ 2 * s)).sub (D.three.mul0' ((D.ppow s).mul0 hσ4))
      exact h7.congr (by push_cast; ring)
    exact D.ucancel hp2 h6
  · have h6 : D p (2 * s) (((2 : ℕ) : ℚ) * ((p : ℚ) ^ ε * sg p (p ^ s) 3)) := by
      have h7 := (((D.ppow (p := p) ε).le (Nat.zero_le _)).mul0' h3).sub
        (D.three.mul0' (((D.ppow s).mul h4).le (by omega : 2 * s ≤ s + s)))
      exact h7.congr (by push_cast; ring)
    exact D.ucancel hp2 h6

lemma sg1 (h5 : 5 ≤ p) {ε : ℕ} (hε : Eps p ε) {s : ℕ} (hs : 1 ≤ s) :
    D p (4 * s) ((p : ℚ) ^ ε * (2 * sg p (p ^ s) 1 + (p : ℚ) ^ s * sg p (p ^ s) 2)) := by
  obtain ⟨h1, _⟩ := refl_sums (p := p) hs
  obtain ⟨_, h3⟩ := sg3 h5 hε hs
  have h4 := sg4 h5 hε hs
  have h7 := ((((D.ppow (p := p) ε).le (Nat.zero_le _)).mul0' h1).sub
    ((((D.ppow s).pow 2).mul h3).le (by omega : 4 * s ≤ s * 2 + 2 * s))).sub
    ((((D.ppow s).pow 3).mul h4).le (by omega : 4 * s ≤ s * 3 + s))
  exact h7.congr (by ring)

lemma trans_sums {s : ℕ} (hs : 1 ≤ s) (h : ℕ) :
    D p (4 * s) (∑ u ∈ U p (p ^ s), (((h * p ^ s + u : ℕ) : ℚ))⁻¹ -
      (sg p (p ^ s) 1 - ((h : ℚ) * (p : ℚ) ^ s) * sg p (p ^ s) 2 +
        ((h : ℚ) * (p : ℚ) ^ s) ^ 2 * sg p (p ^ s) 3 -
        ((h : ℚ) * (p : ℚ) ^ s) ^ 3 * sg p (p ^ s) 4)) ∧
    D p (2 * s) (∑ u ∈ U p (p ^ s), (((h * p ^ s + u : ℕ) : ℚ))⁻¹ ^ 2 -
      (sg p (p ^ s) 2 - 2 * ((h : ℚ) * (p : ℚ) ^ s) * sg p (p ^ s) 3)) ∧
    D p (2 * s) (∑ u ∈ U p (p ^ s), (((h * p ^ s + u : ℕ) : ℚ))⁻¹ ^ 3 -
      (sg p (p ^ s) 3 - 3 * ((h : ℚ) * (p : ℚ) ^ s) * sg p (p ^ s) 4)) := by
  have hpq : p ∣ p ^ s := dvd_pow_self p (by omega)
  apply shift_sums ((h : ℚ) * (p : ℚ) ^ s) ((D.nat h).mul0' (D.ppow s))
    (fun u => ((h * p ^ s + u : ℕ) : ℚ))
  intro u hu
  obtain ⟨hlt, hnd⟩ := mem_U.mp hu
  have hw : ¬ p ∣ h * p ^ s + u :=
    fun hd => hnd ((Nat.dvd_add_right (dvd_mul_of_dvd_right hpq h)).mp hd)
  refine ⟨by push_cast; ring, ?_, D.inv hw⟩
  intro h0
  have h1 : h * p ^ s + u = 0 := by exact_mod_cast h0
  apply hw
  rw [h1]
  exact dvd_zero p

/-- `h_1(t q) = -(q t^2 / 2) H_2(q)` to precision `4s - ε` -/
lemma hs1_blocks (h5 : 5 ≤ p) {ε : ℕ} (hε : Eps p ε) {s : ℕ} (hs : 1 ≤ s) (t : ℕ) :
    D p (4 * s) ((p : ℚ) ^ ε *
      (2 * sg p (t * p ^ s) 1 + (p : ℚ) ^ s * (t : ℚ) ^ 2 * sg p (p ^ s) 2)) := by
  have hpq : p ∣ p ^ s := dvd_pow_self p (by omega)
  have h1 := sg1 h5 hε hs
  obtain ⟨_, h3⟩ := sg3 h5 hε hs
  have h4 := sg4 h5 hε hs
  have hb : sg p (t * p ^ s) 1 =
      ∑ h ∈ Finset.range t, ∑ u ∈ U p (p ^ s), (((h * p ^ s + u : ℕ) : ℚ))⁻¹ := by
    unfold sg
    rw [sum_U_blocks hpq]
    simp only [pow_one]
  rw [hb]
  clear hb
  induction t with
  | zero => exact (D.zero _).congr (by simp)
  | succ t ih =>
    obtain ⟨hT, _, _⟩ := trans_sums (p := p) hs t
    have hpe : D p 0 ((p : ℚ) ^ ε) := (D.ppow ε).le (Nat.zero_le _)
    have htq : D p s ((t : ℚ) * (p : ℚ) ^ s) := (D.nat t).mul0' (D.ppow s)
    have h7 := ih.add ((((D.two.mul0' (hpe.mul0' hT)).add h1).add
      (D.two.mul0' (((htq.pow 2).mul h3).le (by omega : 4 * s ≤ s * 2 + 2 * s)))).sub
      (D.two.mul0' (((htq.pow 3).mul h4).le (by omega : 4 * s ≤ s * 3 + s))))
    refine h7.congr ?_
    rw [Finset.sum_range_succ]
    push_cast
    ring

/-- `h_2(t q) = t H_2(q)` to precision `2s` -/
lemma hs2_blocks (h5 : 5 ≤ p) {s : ℕ} (hs : 1 ≤ s) (t : ℕ) :
    D p (2 * s) (sg p (t * p ^ s) 2 - (t : ℚ) * sg p (p ^ s) 2) := by
  have hpq : p ∣ p ^ s := dvd_pow_self p (by omega)
  have hε : Eps p (if p = 5 then 1 else 0) := by
    by_cases h : p = 5
    · right; simp [h]
    · left
      refine ⟨by simp [h], ?_⟩
      intro hd
      have h15 : (15 : ℕ) = 3 * 5 := by norm_num
      rw [h15] at hd
      rcases (Nat.Prime.dvd_mul hp.out).mp hd with h1 | h1
      · have := Nat.le_of_dvd (by norm_num) h1; omega
      · have := Nat.le_of_dvd (by norm_num) h1; omega
  obtain ⟨h3, _⟩ := sg3 h5 hε hs
  have hb : sg p (t * p ^ s) 2 =
      ∑ h ∈ Finset.range t, ∑ u ∈ U p (p ^ s), (((h * p ^ s + u : ℕ) : ℚ))⁻¹ ^ 2 := by
    unfold sg
    rw [sum_U_blocks hpq]
  rw [hb]
  clear hb
  induction t with
  | zero => exact (D.zero _).congr (by simp)
  | succ t ih =>
    obtain ⟨_, hT, _⟩ := trans_sums (p := p) hs t
    have h7 := ih.add (hT.sub (D.two.mul0' (((D.nat t).mul0' ((D.ppow s).mul h3)).le
      (by omega : 2 * s ≤ s + s))))
    refine h7.congr ?_
    rw [Finset.sum_range_succ]
    push_cast
    ring

/-! ### the non-unit part: auxiliary sums -/

lemma exists_eps (h5 : 5 ≤ p) : ∃ ε, Eps p ε := by
  by_cases h : p = 5
  · exact ⟨1, Or.inr ⟨rfl, h⟩⟩
  · refine ⟨0, Or.inl ⟨rfl, ?_⟩⟩
    intro hd
    have h15 : (15 : ℕ) = 3 * 5 := by norm_num
    rw [h15] at hd
    rcases (Nat.Prime.dvd_mul hp.out).mp hd with h1 | h1
    · have := Nat.le_of_dvd (by norm_num) h1
      omega
    · have := Nat.le_of_dvd (by norm_num) h1
      omega

lemma sg1' (h5 : 5 ≤ p) {s : ℕ} (hs : 1 ≤ s) : D p (2 * s) (sg p (p ^ s) 1) := by
  have hp2 : ¬ p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega)
  obtain ⟨ε, hε⟩ := exists_eps (p := p) h5
  have hε1 := hε.le_one
  have h1 := sg1 h5 hε hs
  have h2 : D p (4 * s - ε) (2 * sg p (p ^ s) 1 + (p : ℚ) ^ s * sg p (p ^ s) 2) := by
    apply D.cancel (c := ε)
    rw [show 4 * s - ε + ε = 4 * s by omega]
    exact h1
  have h6 : D p (2 * s) (((2 : ℕ) : ℚ) * sg p (p ^ s) 1) := by
    have h7 := (h2.le (by omega : 2 * s ≤ 4 * s - ε)).sub
      (((D.ppow s).mul (sg2 h5 hs)).le (by omega : 2 * s ≤ s + s))
    exact h7.congr (by push_cast; ring)
  exact D.ucancel hp2 h6
/-! ### Wolstenholme type sums below `t p^s` -/

lemma S1_D (h5 : 5 ≤ p) {s : ℕ} (hs : 1 ≤ s) (t : ℕ) : D p (2 * s) (sg p (t * p ^ s) 1) := by
  have hp2 : ¬ p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega)
  obtain ⟨ε, hε⟩ := exists_eps (p := p) h5
  have hε1 := hε.le_one
  have h1 := hs1_blocks h5 hε hs t
  have h2 : D p (4 * s - ε)
      (2 * sg p (t * p ^ s) 1 + (p : ℚ) ^ s * (t : ℚ) ^ 2 * sg p (p ^ s) 2) := by
    apply D.cancel (c := ε)
    rw [show 4 * s - ε + ε = 4 * s by omega]
    exact h1
  have h6 : D p (2 * s) (((2 : ℕ) : ℚ) * sg p (t * p ^ s) 1) := by
    have h7 := (h2.le (by omega : 2 * s ≤ 4 * s - ε)).sub
      ((((D.ppow s).mul0 ((D.nat t).pow0 2)).mul (sg2 h5 hs)).le (by omega : 2 * s ≤ s + s))
    exact h7.congr (by push_cast; ring)
  exact D.ucancel hp2 h6

lemma S2_D (h5 : 5 ≤ p) {s : ℕ} (hs : 1 ≤ s) (t : ℕ) : D p s (sg p (t * p ^ s) 2) := by
  have h := (hs2_blocks h5 hs t).le (by omega : s ≤ 2 * s)
  exact (h.add ((D.nat t).mul0' (sg2 h5 hs))).congr (by ring)

/-- `∏_{0<i<t p^s, p ∤ i} (1 - A p^s / i) ≡ 1 mod p^(3s)` -/
lemma R_D (h5 : 5 ≤ p) {s : ℕ} (hs : 1 ≤ s) (A t : ℕ) :
    D p (3 * s) (R p ((A : ℚ) * (p : ℚ) ^ s) (t * p ^ s) - 1) := by
  have hp2 : ¬ p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega)
  obtain ⟨W, hW, hprod⟩ := prod_expand2 hp2 (U p (t * p ^ s)) (fun i => (A : ℚ) * ((i : ℚ)⁻¹))
    ((p : ℚ) ^ s) ((D.ppow s).le (Nat.zero_le _))
    (fun i hi => (D.nat A).mul0 (D.inv (mem_U.mp hi).2))
  have hR : R p ((A : ℚ) * (p : ℚ) ^ s) (t * p ^ s) =
      ∏ i ∈ U p (t * p ^ s), (1 - (p : ℚ) ^ s * ((A : ℚ) * ((i : ℚ)⁻¹))) := by
    unfold R
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [div_eq_mul_inv]; ring
  have h1 : ∑ i ∈ U p (t * p ^ s), (A : ℚ) * ((i : ℚ)⁻¹) = (A : ℚ) * sg p (t * p ^ s) 1 := by
    unfold sg; rw [Finset.mul_sum]; simp only [pow_one]
  have h2 : ∑ i ∈ U p (t * p ^ s), ((A : ℚ) * ((i : ℚ)⁻¹)) ^ 2 =
      (A : ℚ) ^ 2 * sg p (t * p ^ s) 2 := by
    unfold sg; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [hR, hprod, h1, h2]
  have hS1 := S1_D h5 hs t
  have hS2 := S2_D h5 hs t
  have hi2 : D p 0 ((2 : ℚ)⁻¹) := by simpa using D.inv (p := p) hp2
  have e1 : D p (3 * s) ((p : ℚ) ^ s * ((A : ℚ) * sg p (t * p ^ s) 1)) :=
    ((D.ppow s).mul ((D.nat A).mul0' hS1)).le (by omega)
  have e2 : D p (3 * s) (((p : ℚ) ^ s) ^ 2 *
      (((A : ℚ) * sg p (t * p ^ s) 1) ^ 2 - (A : ℚ) ^ 2 * sg p (t * p ^ s) 2)) := by
    have hin : D p s (((A : ℚ) * sg p (t * p ^ s) 1) ^ 2 - (A : ℚ) ^ 2 * sg p (t * p ^ s) 2) :=
      ((((D.nat A).mul0' hS1).pow 2).le (by omega)).sub (((D.nat A).pow0 2).mul0' hS2)
    exact (((D.ppow s).pow 2).mul hin).le (by omega)
  have e3 : D p (3 * s) (((p : ℚ) ^ s) ^ 3 * W) :=
    (((D.ppow s).pow 3).mul0 hW).le (by omega)
  exact ((e1.neg.add (e2.mul0 hi2)).add e3).congr (by ring)

/-! ### the main theorem -/

/-- Jacobsthal-Kazandzidis type: `C(a p^r, b p^r) ≡ C(a p^(r-1), b p^(r-1)) mod p^(3r)`. -/
theorem jacobsthal (h5 : 5 ≤ p) (a b r : ℕ) (hr : 1 ≤ r) :
    (p : ℤ) ^ (3 * r) ∣ (Nat.choose (a * p ^ r) (b * p ^ r) : ℤ) -
      (Nat.choose (a * p ^ (r - 1)) (b * p ^ (r - 1)) : ℤ) := by
  have hp2 : p ≠ 2 := by omega
  have hc := choose_ratio (p := p) hp2 (a * p ^ (r - 1)) (b * p ^ (r - 1))
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hc ⊢
  have e1 : p * (a * p ^ k) = a * p ^ (k + 1) := by ring
  have e2 : p * (b * p ^ k) = b * p ^ (k + 1) := by ring
  rw [e1, e2] at hc
  have e3 : ((a * p ^ (k + 1) : ℕ) : ℚ) = (a : ℚ) * (p : ℚ) ^ (k + 1) := by push_cast; ring
  rw [e3] at hc
  apply D.dvd
  have hR := R_D h5 (by omega : 1 ≤ k + 1) a b
  refine ((D.nat ((a * p ^ k).choose (b * p ^ k))).mul0' hR).congr ?_
  push_cast
  rw [hc]
  ring

/-- the same with an explicit primality hypothesis -/
theorem jacobsthal' {q : ℕ} (hq : q.Prime) (h5 : 5 ≤ q) (a b r : ℕ) (hr : 1 ≤ r) :
    (q : ℤ) ^ (3 * r) ∣ (Nat.choose (a * q ^ r) (b * q ^ r) : ℤ) -
      (Nat.choose (a * q ^ (r - 1)) (b * q ^ (r - 1)) : ℤ) := by
  have : Fact q.Prime := ⟨hq⟩
  exact jacobsthal h5 a b r hr

end LtsJacobsthal

namespace A364177P
open Finset LtsJacobsthal

private lemma choose_succ_q (m k : ℕ) :
    ((m + 1).choose (k + 1) : ℚ) = (m.choose k : ℚ) * ((m : ℚ) + 1) / ((k : ℚ) + 1) := by
  have h := Nat.add_one_mul_choose_eq m k
  have h' : ((m : ℚ) + 1) * (m.choose k : ℚ) = ((m + 1).choose (k + 1) : ℚ) * ((k : ℚ) + 1) := by
    exact_mod_cast h
  have hk : ((k : ℚ) + 1) ≠ 0 := by positivity
  field_simp
  linarith

private lemma U_succ (p L : ℕ) :
    U p (L + 1) = if p ∣ L then U p L else insert L (U p L) := by
  unfold U
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs <;> simp_all

variable {p : ℕ} [hp : Fact p.Prime]

private lemma lucas_shift (d k : ℕ) :
    ((p * d + k).choose k : ℚ) = ((d + k / p).choose (k / p) : ℚ) *
      ∏ i ∈ U p (k + 1), (1 + ((p * d : ℕ) : ℚ) / (i : ℚ)) := by
  induction k with
  | zero =>
    have : U p 1 = ∅ := by
      ext i; simp [mem_U]; intro h; subst h; exact dvd_zero p
    simp [this]
  | succ k ih =>
    rw [show p * d + (k + 1) = (p * d + k) + 1 by ring, choose_succ_q, ih, U_succ p (k + 1)]
    have hp0 : 0 < p := hp.out.pos
    by_cases hd : p ∣ k + 1
    · rw [if_pos hd]
      have h1 : (k + 1) / p = k / p + 1 := Nat.succ_div_of_dvd hd
      have hkj : k + 1 = p * (k / p + 1) := by
        rw [← h1]; exact (Nat.mul_div_cancel' hd).symm
      rw [h1, show d + (k / p + 1) = (d + k / p) + 1 by ring, choose_succ_q]
      have hq : ((k : ℚ) + 1) = (p : ℚ) * (((k / p : ℕ) : ℚ) + 1) := by exact_mod_cast hkj
      have hp' : (p : ℚ) ≠ 0 := by positivity
      have hj : (((k / p : ℕ) : ℚ) + 1) ≠ 0 := by positivity
      push_cast
      rw [show (p : ℚ) * (d : ℚ) + (k : ℚ) + 1 = (p : ℚ) * (d : ℚ) + ((k : ℚ) + 1) by ring, hq]
      field_simp
      ring
    · rw [if_neg hd, Finset.prod_insert (by simp [mem_U])]
      have h1 : (k + 1) / p = k / p := Nat.succ_div_of_not_dvd hd
      rw [h1]
      have hk : ((k : ℚ) + 1) ≠ 0 := by positivity
      push_cast
      field_simp
      ring

private lemma RZ_D (h5 : 5 ≤ p) {s : ℕ} (hs : 1 ≤ s) (A : ℤ) (t : ℕ) :
    D p (3 * s) (∏ i ∈ U p (t * p ^ s), (1 + (A : ℚ) * (p : ℚ) ^ s / (i : ℚ)) - 1) := by
  have hp2 : ¬ p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega)
  obtain ⟨W, hW, hprod⟩ := prod_expand2 hp2 (U p (t * p ^ s)) (fun i => -(A : ℚ) * ((i : ℚ)⁻¹))
    ((p : ℚ) ^ s) ((D.ppow s).le (Nat.zero_le _))
    (fun i hi => (D.int A).neg.mul0 (D.inv (mem_U.mp hi).2))
  have hR : ∏ i ∈ U p (t * p ^ s), (1 + (A : ℚ) * (p : ℚ) ^ s / (i : ℚ)) =
      ∏ i ∈ U p (t * p ^ s), (1 - (p : ℚ) ^ s * (-(A : ℚ) * ((i : ℚ)⁻¹))) := by
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [div_eq_mul_inv]; ring
  have h1 : ∑ i ∈ U p (t * p ^ s), -(A : ℚ) * ((i : ℚ)⁻¹) = -(A : ℚ) * sg p (t * p ^ s) 1 := by
    unfold sg; rw [Finset.mul_sum]; simp only [pow_one]
  have h2 : ∑ i ∈ U p (t * p ^ s), (-(A : ℚ) * ((i : ℚ)⁻¹)) ^ 2 =
      (A : ℚ) ^ 2 * sg p (t * p ^ s) 2 := by
    unfold sg; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [hR, hprod, h1, h2]
  have hS1 := S1_D h5 hs t
  have hS2 := S2_D h5 hs t
  have hi2 : D p 0 ((2 : ℚ)⁻¹) := by simpa using D.inv (p := p) hp2
  have e1 : D p (3 * s) ((p : ℚ) ^ s * (-(A : ℚ) * sg p (t * p ^ s) 1)) :=
    ((D.ppow s).mul ((D.int A).neg.mul0' hS1)).le (by omega)
  have e2 : D p (3 * s) (((p : ℚ) ^ s) ^ 2 *
      ((-(A : ℚ) * sg p (t * p ^ s) 1) ^ 2 - (A : ℚ) ^ 2 * sg p (t * p ^ s) 2)) := by
    have hin : D p s ((-(A : ℚ) * sg p (t * p ^ s) 1) ^ 2 - (A : ℚ) ^ 2 * sg p (t * p ^ s) 2) :=
      ((((D.int A).neg.mul0' hS1).pow 2).le (by omega)).sub (((D.int A).pow0 2).mul0' hS2)
    exact (((D.ppow s).pow 2).mul hin).le (by omega)
  have e3 : D p (3 * s) (((p : ℚ) ^ s) ^ 3 * W) :=
    (((D.ppow s).pow 3).mul0 hW).le (by omega)
  exact ((e1.neg.add (e2.mul0 hi2)).add e3).congr (by ring)

/-- products over `U p (L + h)` split at a multiple `L` of `p` -/
private lemma prod_U_add (f : ℕ → ℚ) {L : ℕ} (hL : p ∣ L) (h : ℕ) :
    ∏ i ∈ U p (L + h), f i = (∏ i ∈ U p L, f i) * ∏ u ∈ U p h, f (L + u) := by
  induction h with
  | zero =>
    have : U p 0 = ∅ := by simp [U]
    simp [this]
  | succ h ih =>
    rw [show L + (h + 1) = (L + h) + 1 by ring, U_succ p (L + h), U_succ p h]
    have hiff : p ∣ L + h ↔ p ∣ h := (Nat.dvd_add_right hL)
    by_cases hd : p ∣ h
    · rw [if_pos (hiff.mpr hd), if_pos hd, ih]
    · rw [if_neg (fun h' => hd (hiff.mp h')), if_neg hd,
        Finset.prod_insert (by simp [mem_U]), Finset.prod_insert (by simp [mem_U]), ih]
      ring

/-- `g y = ∏_{u ∈ U p H} (1 - y/u)` -/
def gq (p H : ℕ) (y : ℚ) : ℚ := ∏ u ∈ U p H, (1 - y / (u : ℚ))

private lemma U_pos' {L u : ℕ} (hu : u ∈ U p L) : 0 < u := by
  rcases Nat.eq_zero_or_pos u with h | h
  · exact absurd (h ▸ dvd_zero p) (mem_U.mp hu).2
  · exact h

private lemma half_block (H x t c : ℕ) :
    ∏ u ∈ U p H, (1 + ((c : ℚ) * x) / (((t * x + u : ℕ)) : ℚ)) =
      gq p H (-(((t + c : ℕ) : ℚ) * x)) / gq p H (-((t : ℚ) * x)) := by
  unfold gq
  rw [← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun u hu => ?_
  have hu0 : (0 : ℚ) < u := by exact_mod_cast U_pos' hu
  have h1 : (0 : ℚ) < (t : ℚ) * x + u := by positivity
  push_cast
  have hne : (1 : ℚ) - -((t : ℚ) * x) / u ≠ 0 := by
    rw [show (1 : ℚ) - -((t : ℚ) * x) / u = ((t : ℚ) * x + u) / u by field_simp; ring]
    positivity
  rw [eq_div_iff hne]
  field_simp
  ring

/-- reflection split of `U p x` for odd `x` divisible by `p` -/
private lemma U_refl {x : ℕ} (hx : p ∣ x) (hodd : x % 2 = 1) :
    U p x = U p ((x + 1) / 2) ∪ (U p ((x + 1) / 2)).image (fun u => x - u) := by
  ext i
  simp only [Finset.mem_union, Finset.mem_image, mem_U]
  constructor
  · rintro ⟨hi, hni⟩
    by_cases h : i < (x + 1) / 2
    · exact Or.inl ⟨h, hni⟩
    · right
      refine ⟨x - i, ⟨by omega, ?_⟩, by omega⟩
      intro hd
      apply hni
      have := Nat.dvd_sub hx hd
      rwa [show x - (x - i) = i by omega] at this
  · rintro (⟨h1, h2⟩ | ⟨u, ⟨h1, h2⟩, rfl⟩)
    · exact ⟨by omega, h2⟩
    · have hu0 : 0 < u := by
        rcases Nat.eq_zero_or_pos u with h | h
        · exact absurd (h ▸ dvd_zero p) h2
        · exact h
      refine ⟨by omega, ?_⟩
      intro hd
      apply h2
      have := Nat.dvd_sub hx hd
      rwa [show x - (x - u) = u by omega] at this

private lemma U_par (hp2 : p ≠ 2) {x : ℕ} (hx : p ∣ x) (hodd : x % 2 = 1) :
    U p x = (U p ((x + 1) / 2)).image (fun u => 2 * u) ∪
      (U p ((x + 1) / 2)).image (fun u => x - 2 * u) := by
  have hpd : ∀ u, p ∣ 2 * u → p ∣ u := by
    intro u h
    rcases (Nat.Prime.dvd_mul hp.out).mp h with h' | h'
    · exfalso
      have := Nat.le_of_dvd (by norm_num) h'
      have := hp.out.two_le
      omega
    · exact h'
  ext i
  simp only [Finset.mem_union, Finset.mem_image, mem_U]
  constructor
  · rintro ⟨hi, hni⟩
    rcases Nat.even_or_odd i with ⟨w, hw⟩ | ⟨w, hw⟩
    · left
      refine ⟨w, ⟨by omega, ?_⟩, by omega⟩
      intro hd; apply hni; rw [hw, ← two_mul]; exact Dvd.dvd.mul_left hd 2
    · right
      refine ⟨(x - i) / 2, ⟨by omega, ?_⟩, by omega⟩
      intro hd
      apply hni
      have h2 : p ∣ 2 * ((x - i) / 2) := Dvd.dvd.mul_left hd 2
      rw [show 2 * ((x - i) / 2) = x - i by omega] at h2
      have := Nat.dvd_sub hx h2
      rwa [show x - (x - i) = i by omega] at this
  · rintro (⟨u, ⟨h1, h2⟩, rfl⟩ | ⟨u, ⟨h1, h2⟩, rfl⟩)
    · exact ⟨by omega, fun h => h2 (hpd u h)⟩
    · have hu0 : 0 < u := by
        rcases Nat.eq_zero_or_pos u with h | h
        · exact absurd (h ▸ dvd_zero p) h2
        · exact h
      refine ⟨by omega, ?_⟩
      intro hd
      apply h2
      apply hpd
      have := Nat.dvd_sub hx hd
      rwa [show x - (x - 2 * u) = 2 * u by omega] at this

private lemma g_ident (hp2 : p ≠ 2) {x : ℕ} (hx : p ∣ x) (hodd : x % 2 = 1) :
    gq p ((x + 1) / 2) (x : ℚ) = 4 ^ (U p ((x + 1) / 2)).card * gq p ((x + 1) / 2) ((x : ℚ) / 2) := by
  set H := (x + 1) / 2 with hH
  set S := U p H
  have hlt : ∀ u ∈ S, u < H := fun u hu => (mem_U.mp hu).1
  have hpos : ∀ u ∈ S, 0 < u := fun u hu => U_pos' hu
  have hA := U_refl hx hodd
  have hB := U_par hp2 hx hodd
  have dA : Disjoint S (S.image (fun u => x - u)) := by
    rw [Finset.disjoint_left]
    intro i hi hi'
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hi'
    have := hlt _ hi; have := hlt u hu; omega
  have dB : Disjoint (S.image (fun u => 2 * u)) (S.image (fun u => x - 2 * u)) := by
    rw [Finset.disjoint_left]
    intro i hi hi'
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨v, hv, hv'⟩ := Finset.mem_image.mp hi'
    have := hlt v hv; omega
  have iA : Set.InjOn (fun u => x - u) S := by
    intro a ha b hb h; have := hlt a ha; have := hlt b hb; simp only at h; omega
  have iB1 : Set.InjOn (fun u => 2 * u) S := by
    intro a _ b _ h; simp only at h; omega
  have iB2 : Set.InjOn (fun u => x - 2 * u) S := by
    intro a ha b hb h; have := hlt a ha; have := hlt b hb; simp only at h; omega
  have PA : ∏ i ∈ U p x, (i : ℚ) = (∏ u ∈ S, (u : ℚ)) * ∏ u ∈ S, (((x - u : ℕ)) : ℚ) := by
    rw [hA, Finset.prod_union dA, Finset.prod_image iA]
  have PB : ∏ i ∈ U p x, (i : ℚ) = (∏ u ∈ S, ((2 * u : ℕ) : ℚ)) * ∏ u ∈ S, (((x - 2 * u : ℕ)) : ℚ) := by
    rw [hB, Finset.prod_union dB, Finset.prod_image iB1, Finset.prod_image iB2]
  have QA : ∏ u ∈ S, (((x - u : ℕ)) : ℚ) = (-1) ^ S.card * (∏ u ∈ S, (u : ℚ)) * gq p H (x : ℚ) := by
    unfold gq
    rw [Finset.pow_card_mul_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun u hu => ?_
    have := hlt u hu
    have hu0 : (0 : ℚ) < u := by exact_mod_cast hpos u hu
    rw [Nat.cast_sub (by omega)]
    field_simp
    ring
  have QB : ∏ u ∈ S, (((x - 2 * u : ℕ)) : ℚ) =
      (-2) ^ S.card * (∏ u ∈ S, (u : ℚ)) * gq p H ((x : ℚ) / 2) := by
    unfold gq
    rw [Finset.pow_card_mul_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun u hu => ?_
    have := hlt u hu
    have hu0 : (0 : ℚ) < u := by exact_mod_cast hpos u hu
    rw [Nat.cast_sub (by omega)]
    push_cast
    field_simp
    ring
  have Q2 : ∏ u ∈ S, ((2 * u : ℕ) : ℚ) = 2 ^ S.card * ∏ u ∈ S, (u : ℚ) := by
    rw [Finset.pow_card_mul_prod]
    exact Finset.prod_congr rfl fun u _ => by push_cast; ring
  have hP0 : (∏ u ∈ S, (u : ℚ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun u hu => by have := hpos u hu; positivity
  have key := PA.symm.trans PB
  rw [QA, QB, Q2] at key
  have h4 : (4 : ℚ) ^ S.card = (-1) ^ S.card * ((2 : ℚ) ^ S.card * (-2) ^ S.card) := by
    rw [← mul_pow, ← mul_pow]; norm_num
  have hsq : (∏ u ∈ S, (u : ℚ)) ^ 2 ≠ 0 := pow_ne_zero 2 hP0
  have h1 : ((-1 : ℚ) ^ S.card) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  apply mul_left_cancel₀ (mul_ne_zero hsq (pow_ne_zero S.card (by norm_num : (-1 : ℚ) ≠ 0)))
  rw [h4]
  linear_combination key - (∏ u ∈ S, (u : ℚ)) ^ 2 * (2 : ℚ) ^ S.card * (-2 : ℚ) ^ S.card *
    gq p H ((x : ℚ) / 2) * h1

private lemma card_U_pow {r : ℕ} (hr : 1 ≤ r) : (U p (p ^ r)).card = p ^ (r - 1) * (p - 1) := by
  rw [← Nat.totient_prime_pow hp.out (by omega), Nat.totient_eq_card_coprime]
  congr 1
  unfold U
  refine Finset.filter_congr fun i _ => ?_
  rw [Nat.coprime_pow_left_iff (by omega), Nat.Prime.coprime_iff_not_dvd hp.out]

private lemma card_half (hp2 : p ≠ 2) {r : ℕ} (hr : 1 ≤ r) :
    2 * (U p ((p ^ r + 1) / 2)).card = p ^ (r - 1) * (p - 1) := by
  have hx : p ∣ p ^ r := dvd_pow_self p (by omega)
  have hodd : p ^ r % 2 = 1 := Nat.odd_iff.mp ((hp.out.odd_of_ne_two hp2).pow)
  have hA := U_refl hx hodd
  set S := U p ((p ^ r + 1) / 2)
  have hlt : ∀ u ∈ S, u < (p ^ r + 1) / 2 := fun u hu => (mem_U.mp hu).1
  have dA : Disjoint S (S.image (fun u => p ^ r - u)) := by
    rw [Finset.disjoint_left]
    intro i hi hi'
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hi'
    have := hlt _ hi; have := hlt u hu; omega
  have iA : Set.InjOn (fun u => p ^ r - u) S := by
    intro a ha b hb h; have := hlt a ha; have := hlt b hb; simp only at h; omega
  rw [← card_U_pow hr, hA, Finset.card_union_of_disjoint dA, Finset.card_image_of_injOn iA]
  ring

end A364177P

namespace A364177P
open Finset LtsJacobsthal

variable {p : ℕ} [hp : Fact p.Prime]

/-- `Good e w l Z` : `Z ≡ 1 - 2 l w + 2 l^2 w^2 (mod p^e)` -/
def Good (p e : ℕ) (w l Z : ℚ) : Prop := D p e (Z - (1 - 2 * l * w + 2 * l ^ 2 * w ^ 2))

private lemma good_D0 {e r : ℕ} (he : e ≤ 3 * r) {w l Z : ℚ} (hw : D p r w) (hl : D p 0 l)
    (h : Good p e w l Z) : D p 0 Z := by
  have hw0 : D p 0 w := hw.le (Nat.zero_le _)
  have h1 : D p 0 (1 - 2 * l * w + 2 * l ^ 2 * w ^ 2) :=
    (D.one.sub ((D.two.mul0 hl).mul0 hw0)).add ((D.two.mul0 (hl.pow0 2)).mul0 (hw0.pow0 2))
  exact ((h.le (Nat.zero_le _)).add h1).congr (by ring)

private lemma good_mul {r : ℕ} {w l m A B : ℚ} (hw : D p r w) (hl : D p 0 l) (hm : D p 0 m)
    (hA : Good p (3 * r) w l A) (hB : Good p (3 * r) w m B) : Good p (3 * r) w (l + m) (A * B) := by
  have hw0 : D p 0 w := hw.le (Nat.zero_le _)
  have hB0 : D p 0 B := good_D0 le_rfl hw hm hB
  have hPl : D p 0 (1 - 2 * l * w + 2 * l ^ 2 * w ^ 2) :=
    (D.one.sub ((D.two.mul0 hl).mul0 hw0)).add ((D.two.mul0 (hl.pow0 2)).mul0 (hw0.pow0 2))
  have h3 : D p (3 * r) (w ^ 3 * (-4 * l * m * (l + m) + 4 * l ^ 2 * m ^ 2 * w)) := by
    have hc : D p 0 (-4 * l * m * (l + m) + 4 * l ^ 2 * m ^ 2 * w) := by
      have h4 : D p 0 (4 : ℚ) := by simpa using D.nat (p := p) 4
      exact ((((h4.neg.mul0 hl).mul0 hm).mul0 (hl.add hm))).add
        (((h4.mul0 (hl.pow0 2)).mul0 (hm.pow0 2)).mul0 hw0)
    exact ((hw.pow 3).mul0 hc).le (by omega)
  unfold Good at *
  exact ((hA.mul0 hB0).add (hPl.mul0' hB)).add h3 |>.congr (by ring)

private lemma good_pow {r : ℕ} {w l A : ℚ} (hw : D p r w) (hl : D p 0 l)
    (hA : Good p (3 * r) w l A) (k : ℕ) : Good p (3 * r) w ((k : ℚ) * l) (A ^ k) := by
  induction k with
  | zero => unfold Good; simpa using D.zero (p := p) (3 * r)
  | succ k ih =>
    have := good_mul hw ((D.nat k).mul0 hl) hl ih hA
    rw [pow_succ]
    unfold Good at this ⊢
    exact this.congr (by push_cast; ring)

private lemma good_sub {e : ℕ} {w l A B : ℚ} (hA : Good p e w l A) (hB : Good p e w l B) :
    D p e (A - B) := (hA.sub hB).congr (by ring)

/-- the half sum of `1/u^2` is divisible by `p^r` -/
private lemma S2_half (h5 : 5 ≤ p) {r : ℕ} (hr : 1 ≤ r) :
    D p r (∑ u ∈ U p ((p ^ r + 1) / 2), ((u : ℚ)⁻¹) ^ 2) := by
  have hp2 : p ≠ 2 := by omega
  have hp2' : ¬ p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega)
  have hx : p ∣ p ^ r := dvd_pow_self p (by omega)
  have hodd : p ^ r % 2 = 1 := Nat.odd_iff.mp ((hp.out.odd_of_ne_two hp2).pow)
  set x := p ^ r with hxdef
  set S := U p ((x + 1) / 2)
  have hlt : ∀ u ∈ S, u < (x + 1) / 2 := fun u hu => (mem_U.mp hu).1
  have dA : Disjoint S (S.image (fun u => x - u)) := by
    rw [Finset.disjoint_left]
    intro i hi hi'
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hi'
    have := hlt _ hi; have := hlt u hu; omega
  have iA : Set.InjOn (fun u => x - u) S := by
    intro a ha b hb h; have := hlt a ha; have := hlt b hb; simp only at h; omega
  have hfull : sg p x 2 = ∑ u ∈ S, ((u : ℚ)⁻¹) ^ 2 + ∑ u ∈ S, ((((x - u : ℕ)) : ℚ)⁻¹) ^ 2 := by
    unfold sg
    rw [U_refl hx hodd, Finset.sum_union dA, Finset.sum_image iA]
  have hdiff : D p r (∑ u ∈ S, (((((x - u : ℕ)) : ℚ)⁻¹) ^ 2 - ((u : ℚ)⁻¹) ^ 2)) := by
    apply D.sum
    intro u hu
    have hu0 := U_pos' hu
    have hlu := hlt u hu
    have hnu : ¬ p ∣ u := (mem_U.mp hu).2
    have hnv : ¬ p ∣ x - u := by
      intro hd; apply hnu
      have := Nat.dvd_sub hx hd
      rwa [show x - (x - u) = u by omega] at this
    have hv0 : 0 < x - u := by omega
    have hu' : (u : ℚ) ≠ 0 := by positivity
    have hv' : (((x - u : ℕ)) : ℚ) ≠ 0 := by positivity
    have e : ((((x - u : ℕ)) : ℚ)⁻¹) ^ 2 - ((u : ℚ)⁻¹) ^ 2 =
        (x : ℚ) * ((2 * (u : ℚ) - x) * ((u : ℚ)⁻¹) ^ 2 * ((((x - u : ℕ)) : ℚ)⁻¹) ^ 2) := by
      rw [Nat.cast_sub (by omega)] at hv' ⊢
      field_simp
      ring
    rw [e]
    have hxD : D p r (x : ℚ) := by rw [hxdef]; push_cast; exact D.ppow r
    have hc : D p 0 (2 * (u : ℚ) - x) := (D.two.mul0 (D.nat u)).sub (D.nat x)
    exact hxD.mul0 ((hc.mul0 ((D.inv hnu).pow0 2)).mul0 ((D.inv hnv).pow0 2))
  have h2 : D p r (((2 : ℕ) : ℚ) * ∑ u ∈ S, ((u : ℚ)⁻¹) ^ 2) := by
    have := (sg2 h5 hr).sub hdiff
    rw [hfull, Finset.sum_sub_distrib] at this
    exact this.congr (by push_cast; ring)
  exact D.ucancel hp2' h2

/-- `gq` at `l x` is `Good` with `w = x S / 2` -/
private lemma gq_good (h5 : 5 ≤ p) {r : ℕ} (hr : 1 ≤ r) {l : ℚ} (hl : D p 0 l) :
    Good p (3 * r) ((p : ℚ) ^ r * (∑ u ∈ U p ((p ^ r + 1) / 2), (u : ℚ)⁻¹) / 2) l
      (gq p ((p ^ r + 1) / 2) (l * (p : ℚ) ^ r)) := by
  have hp2' : ¬ p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega)
  set S := U p ((p ^ r + 1) / 2)
  have hx : D p r (l * (p : ℚ) ^ r) := hl.mul0' (D.ppow r)
  obtain ⟨W, hW, hprod⟩ := prod_expand2 hp2' S (fun u => (u : ℚ)⁻¹) (l * (p : ℚ) ^ r)
    (hx.le (Nat.zero_le _)) (fun u hu => D.inv (mem_U.mp hu).2)
  have hg : gq p ((p ^ r + 1) / 2) (l * (p : ℚ) ^ r) = ∏ u ∈ S, (1 - l * (p : ℚ) ^ r * (u : ℚ)⁻¹) := by
    unfold gq; exact Finset.prod_congr rfl fun u _ => by rw [div_eq_mul_inv]
  have hS2 := S2_half h5 hr
  have hi2 : D p 0 ((2 : ℚ)⁻¹) := by simpa using D.inv (p := p) hp2'
  unfold Good
  rw [hg, hprod]
  have e1 : D p (3 * r) ((l * (p : ℚ) ^ r) ^ 2 * (∑ u ∈ S, ((u : ℚ)⁻¹) ^ 2) * (2 : ℚ)⁻¹) :=
    (((hx.pow 2).mul hS2).mul0 hi2).le (by omega)
  have e2 : D p (3 * r) ((l * (p : ℚ) ^ r) ^ 3 * W) := ((hx.pow 3).mul0 hW).le (by omega)
  exact (e1.neg.add e2).congr (by ring)

end A364177P

namespace A364177P
open Finset LtsJacobsthal

variable {p : ℕ} [hp : Fact p.Prime]

private lemma D_inv_unit {e : ℕ} {x : ℚ} (he : 1 ≤ e) (h : D p e (x - 1)) : D p 0 x⁻¹ := by
  obtain ⟨a, b, hb, hab⟩ := h
  set c : ℤ := (b : ℤ) + (p : ℤ) ^ e * a with hcdef
  have hpc : ¬ (p : ℤ) ∣ c := by
    intro hd
    apply hb
    have h2 : (p : ℤ) ∣ (p : ℤ) ^ e * a := Dvd.dvd.mul_right (dvd_pow_self _ (by omega)) _
    exact Int.natCast_dvd_natCast.mp ((dvd_add_left h2).mp hd)
  have hc0 : c ≠ 0 := fun h0 => hpc (h0 ▸ dvd_zero _)
  have hxc : x * (b : ℚ) = (c : ℚ) := by
    rw [hcdef]; push_cast; linear_combination hab
  have hx0 : x ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hxc; exact hc0 (by exact_mod_cast hxc.symm)
  have hinv : x⁻¹ * (c : ℚ) = (b : ℚ) := by rw [← hxc]; field_simp
  have hpn : ¬ p ∣ c.natAbs := by
    intro hd; apply hpc
    exact Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr hd)
  rcases Int.natAbs_eq c with hc | hc
  · refine ⟨(b : ℤ), c.natAbs, hpn, ?_⟩
    have h' : (c : ℚ) = ((c.natAbs : ℕ) : ℚ) := by rw [← Int.cast_natCast, ← hc]
    rw [pow_zero, one_mul, Int.cast_natCast]
    linear_combination -x⁻¹ * h' + hinv
  · refine ⟨-(b : ℤ), c.natAbs, hpn, ?_⟩
    have h' : (c : ℚ) = -((c.natAbs : ℕ) : ℚ) := by rw [← Int.cast_natCast, ← Int.cast_neg, ← hc]
    rw [pow_zero, one_mul, Int.cast_neg, Int.cast_natCast]
    linear_combination x⁻¹ * h' - hinv

private lemma D_one_add {e : ℕ} {x : ℚ} (h : D p e (x - 1)) : D p 0 x :=
  ((h.le (Nat.zero_le _)).add D.one).congr (by ring)

private lemma ne0_of {e : ℕ} {z : ℚ} (he : 1 ≤ e) (h : D p e (z - 1)) : z ≠ 0 := by
  intro hz
  obtain ⟨a, b, hb, hab⟩ := h
  rw [hz] at hab
  apply hb
  have h2 : -(b : ℤ) = (p : ℤ) ^ e * a := by
    have h3 : ((-(b : ℤ) : ℤ) : ℚ) = (((p : ℤ) ^ e * a : ℤ) : ℚ) := by
      push_cast; linear_combination hab
    exact_mod_cast h3
  have h3 : (p : ℤ) ∣ (b : ℤ) := by
    have : (p : ℤ) ∣ (p : ℤ) ^ e * a := Dvd.dvd.mul_right (dvd_pow_self _ (by omega)) _
    rw [← h2] at this
    exact (dvd_neg).mp this
  exact Int.natCast_dvd_natCast.mp h3

private lemma good_unit {r : ℕ} {w l Z : ℚ} (hw : D p r w) (hl : D p 0 l)
    (h : Good p (3 * r) w l Z) : D p r (Z - 1) := by
  have h1 : D p r (-2 * l * w + 2 * l ^ 2 * w ^ 2) := by
    have a1 : D p r (-2 * l * w) := ((D.two.neg.mul0 hl).mul0' hw).congr (by ring)
    have a2 : D p r (2 * l ^ 2 * w ^ 2) :=
      ((D.two.mul0 (hl.pow0 2)).mul0' ((hw.pow 2).le (by omega))).congr (by ring)
    exact a1.add a2
  exact ((h.le (by omega)).add h1).congr (by ring)

private lemma good_congr {e : ℕ} {w l l' Z : ℚ} (h : Good p e w l Z) (hl : l = l') :
    Good p e w l' Z := hl ▸ h



omit hp in
private lemma half_odd (A : ℕ) : (2 * A + 1) / 2 = A := by omega

omit hp in
private lemma half_odd' (A : ℕ) : (2 * A + 1 + 1) / 2 = A + 1 := by omega

omit hp in
private lemma odd_mod (A : ℕ) : (2 * A + 1) % 2 = 1 := by omega

/-- the odd case core -/
private lemma odd_core (h5 : 5 ≤ p) (k j : ℕ) :
    ∃ ρ : ℚ, D p (3 * (k + 1)) (ρ - 1) ∧
      (4 : ℚ) ^ (5 * ((2 * j + 1) * p ^ (k + 1))) *
        ((15 * ((2 * j + 1) * p ^ (k + 1) / 2) + 7).choose (5 * ((2 * j + 1) * p ^ (k + 1) / 2) + 2) : ℚ) =
      (4 : ℚ) ^ (5 * ((2 * j + 1) * p ^ k)) *
        ((15 * ((2 * j + 1) * p ^ k / 2) + 7).choose (5 * ((2 * j + 1) * p ^ k / 2) + 2) : ℚ) * ρ := by
  have hp2 : p ≠ 2 := by omega
  have hpos : 0 < p := hp.out.pos
  have hp2' : ¬ p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega)
  have hi2 : D p 0 ((2 : ℚ)⁻¹) := by simpa using D.inv (p := p) hp2'
  obtain ⟨q, hq⟩ : ∃ q, p = 2 * q + 1 := by
    obtain ⟨a, ha⟩ := hp.out.odd_of_ne_two hp2
    exact ⟨a, ha⟩
  obtain ⟨y, hy⟩ := (hp.out.odd_of_ne_two hp2).pow (n := k)
  have hxodd : p ^ (k + 1) % 2 = 1 := Nat.odd_iff.mp ((hp.out.odd_of_ne_two hp2).pow)
  -- instantiate the lemmas first
  have hcard := card_half (p := p) hp2 (by omega : 1 ≤ k + 1)
  simp only [Nat.add_sub_cancel] at hcard
  have hgid := g_ident (p := p) hp2 (dvd_pow_self p (by omega : k + 1 ≠ 0)) hxodd
  push_cast at hgid
  have hRZ := RZ_D h5 (by omega : 1 ≤ k + 1) ((5 * (2 * j + 1) : ℕ) : ℤ) (5 * j + 2)
  have G1 := gq_good h5 (by omega : 1 ≤ k + 1) (D.one (p := p))
  have Gh := gq_good h5 (by omega : 1 ≤ k + 1) hi2
  have Gt := gq_good h5 (by omega : 1 ≤ k + 1) (D.nat (5 * j + 2)).neg
  have Gtc := gq_good h5 (by omega : 1 ≤ k + 1) (D.nat (5 * j + 2 + 5 * (2 * j + 1))).neg
  have hlu := lucas_shift (p := p) (5 * ((2 * j + 1) * p ^ k)) (5 * ((2 * j + 1) * p ^ (k + 1) / 2) + 2)
  have hhb := half_block (p := p) ((p ^ (k + 1) + 1) / 2) (p ^ (k + 1)) (5 * j + 2) (5 * (2 * j + 1))
  have hsplit := prod_U_add (p := p)
    (fun i => 1 + ((p * (5 * ((2 * j + 1) * p ^ k)) : ℕ) : ℚ) / (i : ℚ))
    (Dvd.dvd.mul_left (dvd_pow_self p (by omega : k + 1 ≠ 0)) (5 * j + 2)) ((p ^ (k + 1) + 1) / 2)
  beta_reduce at hsplit
  -- names
  set P := p ^ k with hP
  have hxP : p ^ (k + 1) = p * P := by rw [hP, pow_succ, mul_comm]
  set X : ℚ := (p : ℚ) ^ (k + 1) with hX
  set x := p ^ (k + 1) with hx
  set H := (x + 1) / 2 with hH
  set n := 2 * j + 1 with hn
  set t := 5 * j + 2 with ht
  set M := n * P with hM
  set N := n * x with hN
  set S := U p H with hS
  have hxX : (x : ℚ) = X := by rw [hx, hX]; push_cast; rfl
  have hNM : N = p * M := by rw [hN, hM, hxP]; ring
  -- arithmetic
  have hM2 : M = 2 * (2 * j * y + j + y) + 1 := by rw [hM, hn, hy]; ring
  have hx2 : x = 2 * (2 * q * y + q + y) + 1 := by rw [hxP, hq, hy]; ring
  have hN2 : N = 2 * (n * (2 * q * y + q + y) + j) + 1 := by rw [hN, hx2, hn]; ring
  have hMd : M / 2 = 2 * j * y + j + y := by rw [hM2, half_odd]
  have hNd : N / 2 = n * (2 * q * y + q + y) + j := by rw [hN2, half_odd]
  have hHd : H = 2 * q * y + q + y + 1 := by rw [hH, hx2, half_odd']
  have hMo : M % 2 = 1 := by rw [hM2]; exact odd_mod _
  have hNo : N % 2 = 1 := by rw [hN2]; exact odd_mod _
  have hpM : p * (5 * M) = 5 * N := by rw [hNM]; ring
  have a1 : p * (5 * M) + (5 * (N / 2) + 2) = 15 * (N / 2) + 7 := by rw [hpM]; omega
  have a2 : (5 * (N / 2) + 2) / p = 5 * (M / 2) + 2 := by
    have e : 5 * (N / 2) + 2 = q + (5 * (M / 2) + 2) * p := by
      rw [hNd, hMd, hn, hq]; ring
    rw [e, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt (by omega)]
    ring
  have a3 : 5 * M + (5 * (M / 2) + 2) = 15 * (M / 2) + 7 := by omega
  have a4 : 5 * (N / 2) + 2 + 1 = t * x + H := by
    rw [hNd, hHd, ht, hx2, hn]; ring
  have hc5 : ((p * (5 * M) : ℕ) : ℚ) = ((5 * n : ℕ) : ℚ) * (x : ℚ) := by
    have : p * (5 * M) = 5 * n * x := by rw [hM, hxP]; ring
    rw [this]; push_cast; ring
  rw [a1, a2, a3, a4, hsplit] at hlu
  -- the full blocks
  set RZ := ∏ i ∈ U p (t * x), (1 + (((5 * n : ℕ) : ℤ) : ℚ) * X / (i : ℚ)) with hRZdef
  have hblk : ∏ i ∈ U p (t * x), (1 + ((p * (5 * M) : ℕ) : ℚ) / (i : ℚ)) = RZ := by
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hc5, hxX]; push_cast; ring
  -- the half block
  have hhalf : ∏ u ∈ S, (1 + ((p * (5 * M) : ℕ) : ℚ) / (((t * x + u : ℕ)) : ℚ)) =
      gq p H (-((t + 5 * n : ℕ) : ℚ) * X) / gq p H (-(t : ℚ) * X) := by
    rw [show -((t + 5 * n : ℕ) : ℚ) * X = -(((t + 5 * n : ℕ) : ℚ) * (x : ℚ)) by rw [hxX]; ring,
      show -(t : ℚ) * X = -((t : ℚ) * (x : ℚ)) by rw [hxX]; ring, ← hhb]
    refine Finset.prod_congr rfl fun u _ => ?_
    rw [hc5]
  rw [hblk, hhalf] at hlu
  -- the power of 4
  have h5N : 5 * N = 5 * M + S.card * (2 * (5 * n)) := by
    have e2 : S.card * (2 * (5 * n)) = 5 * n * (P * (p - 1)) := by rw [← hcard]; ring
    rw [e2, hN, hM, hxP]
    obtain ⟨p', hp'⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
    rw [hp']
    simp only [Nat.add_sub_cancel]
    ring
  -- Good facts
  set w := X * (∑ u ∈ S, (u : ℚ)⁻¹) / 2 with hw
  have hwD : D p (k + 1) w := by
    have hS' : D p 0 (∑ u ∈ S, (u : ℚ)⁻¹) := D.sum _ _ fun u hu => D.inv (mem_U.mp hu).2
    exact (((D.ppow (k + 1)).mul0 hS').mul0 hi2).congr (by rw [hw, hX]; ring)
  have hl2 : D p 0 ((2 * (5 * n) : ℕ) : ℚ) := D.nat _
  have Num := good_mul hwD (hl2.mul0 D.one) (D.nat (t + 5 * n)).neg
    (good_pow hwD D.one G1 (2 * (5 * n))) Gtc
  have Den := good_mul hwD (hl2.mul0 hi2) (D.nat t).neg (good_pow hwD hi2 Gh (2 * (5 * n))) Gt
  have Den' := good_congr Den (show ((2 * (5 * n) : ℕ) : ℚ) * (2 : ℚ)⁻¹ + -(t : ℚ) =
      ((2 * (5 * n) : ℕ) : ℚ) * 1 + -((t + 5 * n : ℕ) : ℚ) by push_cast; ring)
  have hND := good_sub Num Den'
  have hDen1 := good_unit hwD ((hl2.mul0 D.one).add (D.nat (t + 5 * n)).neg) Den'
  have hDen0 := ne0_of (by omega) hDen1
  have hDinv := D_inv_unit (by omega) hDen1
  have hNum0 := good_D0 le_rfl hwD ((hl2.mul0 D.one).add (D.nat (t + 5 * n)).neg) Num
  have hGt0 : gq p H (-(t : ℚ) * X) ≠ 0 := by
    intro h0; apply hDen0; rw [h0, mul_zero]
  have hGh0 : gq p H ((2 : ℚ)⁻¹ * X) ≠ 0 := by
    intro h0; apply hDen0; rw [h0, zero_pow (by omega), zero_mul]
  have e1 : gq p H (1 * X) = 4 ^ S.card * gq p H ((2 : ℚ)⁻¹ * X) := by
    rw [one_mul, hgid, show X / 2 = (2 : ℚ)⁻¹ * X by ring]
  refine ⟨RZ * (gq p H (1 * X) ^ (2 * (5 * n)) * gq p H (-((t + 5 * n : ℕ) : ℚ) * X)) *
    (gq p H ((2 : ℚ)⁻¹ * X) ^ (2 * (5 * n)) * gq p H (-(t : ℚ) * X))⁻¹, ?_, ?_⟩
  · have e : ∀ A B C : ℚ, C ≠ 0 → A * B * C⁻¹ - 1 = (A - 1) * B * C⁻¹ + (B - C) * C⁻¹ := by
      intro A B C hC; field_simp; ring
    rw [e _ _ _ hDen0]
    exact (((hRZ.mul0 hNum0).mul0 hDinv)).add (hND.mul0 hDinv)
  · rw [hlu, h5N, pow_add, pow_mul, e1]
    generalize gq p H ((2 : ℚ)⁻¹ * X) = G1' at hGh0 ⊢
    generalize gq p H (-(t : ℚ) * X) = G2' at hGt0 ⊢
    field_simp
    ring

end A364177P

namespace A364177P
open Finset LtsJacobsthal

/-! ### closed forms of `a` -/

private lemma hf_even (j : ℕ) : OMA.S_oeis_a364177.hf (2 * j) = ((j.factorial : ℕ) : ℚ) := by
  unfold OMA.S_oeis_a364177.hf
  rw [if_pos (by omega), show 2 * j / 2 = j by omega]

private lemma hf_odd (j : ℕ) :
    OMA.S_oeis_a364177.hf (2 * j + 1) =
      (((2 * j + 1).factorial : ℕ) : ℚ) / (2 ^ (2 * j + 1) * ((j.factorial : ℕ) : ℚ)) := by
  unfold OMA.S_oeis_a364177.hf
  rw [if_neg (by omega), show (2 * j + 1 + 1) / 2 = j + 1 by omega]
  have h1 := Nat.factorial_eq_mul_doubleFactorial (2 * j)
  rw [Nat.doubleFactorial_two_mul] at h1
  have h1' : (((2 * j + 1).factorial : ℕ) : ℚ) =
      (((2 * j + 1).doubleFactorial : ℕ) : ℚ) * (2 ^ j * ((j.factorial : ℕ) : ℚ)) := by
    exact_mod_cast h1
  rw [h1']
  have : ((j.factorial : ℕ) : ℚ) ≠ 0 := by positivity
  field_simp
  ring

private lemma a_even_fact (K : ℕ) : OMA.S_oeis_a364177.a (2 * K) =
    ((((30 * K).factorial * (5 * K).factorial * (4 * K).factorial : ℕ)) : ℚ) /
      ((((15 * K).factorial * (10 * K).factorial * (8 * K).factorial * (6 * K).factorial : ℕ)) : ℚ) := by
  unfold OMA.S_oeis_a364177.a
  rw [show OMA.S_oeis_a364177.hf (5 * (2 * K)) = (((5 * K).factorial : ℕ) : ℚ) by
      rw [show 5 * (2 * K) = 2 * (5 * K) by ring, hf_even],
    show OMA.S_oeis_a364177.hf (15 * (2 * K)) = (((15 * K).factorial : ℕ) : ℚ) by
      rw [show 15 * (2 * K) = 2 * (15 * K) by ring, hf_even]]
  rw [show 15 * (2 * K) = 30 * K by ring, show 2 * (2 * K) = 4 * K by ring,
    show 5 * (2 * K) = 10 * K by ring, show 4 * (2 * K) = 8 * K by ring,
    show 3 * (2 * K) = 6 * K by ring]
  have f1 : (((15 * K).factorial : ℕ) : ℚ) ≠ 0 := by positivity
  have f2 : (((10 * K).factorial : ℕ) : ℚ) ≠ 0 := by positivity
  have f3 : (((8 * K).factorial : ℕ) : ℚ) ≠ 0 := by positivity
  have f4 : (((6 * K).factorial : ℕ) : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp

private lemma a_even (K : ℕ) : OMA.S_oeis_a364177.a (2 * K) =
    ((30 * K).choose (15 * K) : ℚ) * ((15 * K).choose (5 * K) : ℚ) * ((10 * K).choose (4 * K) : ℚ) /
      (((10 * K).choose (5 * K) : ℚ) * ((8 * K).choose (4 * K) : ℚ)) := by
  rw [a_even_fact]
  rw [Nat.cast_choose ℚ (by omega : 15 * K ≤ 30 * K), Nat.cast_choose ℚ (by omega : 5 * K ≤ 15 * K),
    Nat.cast_choose ℚ (by omega : 4 * K ≤ 10 * K), Nat.cast_choose ℚ (by omega : 5 * K ≤ 10 * K),
    Nat.cast_choose ℚ (by omega : 4 * K ≤ 8 * K)]
  rw [show 30 * K - 15 * K = 15 * K by omega, show 15 * K - 5 * K = 10 * K by omega,
    show 10 * K - 4 * K = 6 * K by omega, show 10 * K - 5 * K = 5 * K by omega,
    show 8 * K - 4 * K = 4 * K by omega]
  have f1 : (((15 * K).factorial : ℕ) : ℚ) ≠ 0 := by positivity
  have f2 : (((10 * K).factorial : ℕ) : ℚ) ≠ 0 := by positivity
  have f3 : (((8 * K).factorial : ℕ) : ℚ) ≠ 0 := by positivity
  have f4 : (((6 * K).factorial : ℕ) : ℚ) ≠ 0 := by positivity
  have f5 : (((5 * K).factorial : ℕ) : ℚ) ≠ 0 := by positivity
  have f6 : (((4 * K).factorial : ℕ) : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp

private lemma a_odd_fact (m : ℕ) : OMA.S_oeis_a364177.a (2 * m + 1) =
    (4 : ℚ) ^ (5 * (2 * m + 1)) *
      ((((15 * m + 7).factorial * (2 * (2 * m + 1)).factorial : ℕ)) : ℚ) /
      ((((5 * m + 2).factorial * (4 * (2 * m + 1)).factorial * (3 * (2 * m + 1)).factorial : ℕ)) : ℚ) := by
  unfold OMA.S_oeis_a364177.a
  rw [show 5 * (2 * m + 1) = 2 * (5 * m + 2) + 1 by ring, show 15 * (2 * m + 1) = 2 * (15 * m + 7) + 1 by ring,
    hf_odd, hf_odd]
  have h4 : (4 : ℚ) ^ (2 * (5 * m + 2) + 1) * 2 ^ (2 * (5 * m + 2) + 1) = 2 ^ (2 * (15 * m + 7) + 1) := by
    rw [show (4 : ℚ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add]
    congr 1
    ring
  have f1 : (((5 * m + 2).factorial : ℕ) : ℚ) ≠ 0 := by positivity
  have f2 : (((15 * m + 7).factorial : ℕ) : ℚ) ≠ 0 := by positivity
  have f3 : (((2 * (5 * m + 2) + 1).factorial : ℕ) : ℚ) ≠ 0 := by positivity
  have f4 : (((2 * (15 * m + 7) + 1).factorial : ℕ) : ℚ) ≠ 0 := by positivity
  have f5 : (((4 * (2 * m + 1)).factorial : ℕ) : ℚ) ≠ 0 := by positivity
  have f6 : (((3 * (2 * m + 1)).factorial : ℕ) : ℚ) ≠ 0 := by positivity
  rw [← h4]
  push_cast
  field_simp

private lemma a_odd (m : ℕ) : OMA.S_oeis_a364177.a (2 * m + 1) =
    (4 : ℚ) ^ (5 * (2 * m + 1)) * ((15 * m + 7).choose (5 * m + 2) : ℚ) *
      ((5 * (2 * m + 1)).choose (2 * (2 * m + 1)) : ℚ) / ((4 * (2 * m + 1)).choose (2 * (2 * m + 1)) : ℚ) := by
  rw [a_odd_fact]
  rw [Nat.cast_choose ℚ (by omega : 5 * m + 2 ≤ 15 * m + 7),
    Nat.cast_choose ℚ (by omega : 2 * (2 * m + 1) ≤ 5 * (2 * m + 1)),
    Nat.cast_choose ℚ (by omega : 2 * (2 * m + 1) ≤ 4 * (2 * m + 1))]
  rw [show 15 * m + 7 - (5 * m + 2) = 5 * (2 * m + 1) by omega,
    show 5 * (2 * m + 1) - 2 * (2 * m + 1) = 3 * (2 * m + 1) by omega,
    show 4 * (2 * m + 1) - 2 * (2 * m + 1) = 2 * (2 * m + 1) by omega]
  have f1 : (((5 * m + 2).factorial : ℕ) : ℚ) ≠ 0 := by positivity
  have f2 : (((5 * (2 * m + 1)).factorial : ℕ) : ℚ) ≠ 0 := by positivity
  have f3 : (((2 * (2 * m + 1)).factorial : ℕ) : ℚ) ≠ 0 := by positivity
  have f4 : (((3 * (2 * m + 1)).factorial : ℕ) : ℚ) ≠ 0 := by positivity
  have f5 : (((4 * (2 * m + 1)).factorial : ℕ) : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp

/-! ### floor inequalities -/

private lemma fl (c d T K q : ℕ) (hd : 0 < d) (h : c * d = T) : c * K / q = T * K / q / d := by
  rw [Nat.div_div_eq_div_mul, ← h, show c * d * K = d * (c * K) by ring,
    show q * d = d * q by ring, Nat.mul_div_mul_left _ _ hd]

private lemma flh (c e T N q : ℕ) (he : 0 < e) (h : c * e = T) :
    c * N / 2 / q = T * N / q / (2 * e) := by
  rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, ← h, show c * e * N = e * (c * N) by ring,
    show q * (2 * e) = e * (2 * q) by ring, Nat.mul_div_mul_left _ _ he]

variable {p : ℕ} [hp : Fact p.Prime]

private lemma val_even (K : ℕ) :
    padicValNat p ((15 * K).factorial * (10 * K).factorial * (8 * K).factorial * (6 * K).factorial) ≤
      padicValNat p ((30 * K).factorial * (5 * K).factorial * (4 * K).factorial) := by
  have f0 := Nat.factorial_ne_zero
  rw [padicValNat.mul (by positivity) (f0 _), padicValNat.mul (by positivity) (f0 _),
    padicValNat.mul (f0 _) (f0 _), padicValNat.mul (by positivity) (f0 _), padicValNat.mul (f0 _) (f0 _)]
  have hB : ∀ z, z ≤ 30 * K → Nat.log p z < 30 * K + 1 := fun z hz =>
    lt_of_le_of_lt (Nat.log_le_self p z) (by omega)
  rw [padicValNat_factorial (hB (15 * K) (by omega)), padicValNat_factorial (hB (10 * K) (by omega)),
    padicValNat_factorial (hB (8 * K) (by omega)), padicValNat_factorial (hB (6 * K) (by omega)),
    padicValNat_factorial (hB (30 * K) (by omega)), padicValNat_factorial (hB (5 * K) (by omega)),
    padicValNat_factorial (hB (4 * K) (by omega))]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  rw [fl 30 4 120 K _ (by norm_num) (by norm_num), fl 5 24 120 K _ (by norm_num) (by norm_num),
    fl 4 30 120 K _ (by norm_num) (by norm_num), fl 15 8 120 K _ (by norm_num) (by norm_num),
    fl 10 12 120 K _ (by norm_num) (by norm_num), fl 8 15 120 K _ (by norm_num) (by norm_num),
    fl 6 20 120 K _ (by norm_num) (by norm_num)]
  generalize 120 * K / p ^ i = L
  have key : ∀ ρ, ρ < 120 → ρ / 8 + ρ / 12 + ρ / 15 + ρ / 20 ≤ ρ / 4 + ρ / 24 + ρ / 30 := by decide
  have := key (L % 120) (Nat.mod_lt _ (by norm_num))
  omega

private lemma val_odd (m : ℕ) :
    padicValNat p ((5 * m + 2).factorial * (4 * (2 * m + 1)).factorial * (3 * (2 * m + 1)).factorial) ≤
      padicValNat p ((15 * m + 7).factorial * (2 * (2 * m + 1)).factorial) := by
  have f0 := Nat.factorial_ne_zero
  rw [padicValNat.mul (by positivity) (f0 _), padicValNat.mul (f0 _) (f0 _),
    padicValNat.mul (f0 _) (f0 _)]
  have hB : ∀ z, z ≤ 30 * m + 30 → Nat.log p z < 30 * m + 31 := fun z hz =>
    lt_of_le_of_lt (Nat.log_le_self p z) (by omega)
  rw [padicValNat_factorial (hB (5 * m + 2) (by omega)),
    padicValNat_factorial (hB (4 * (2 * m + 1)) (by omega)),
    padicValNat_factorial (hB (3 * (2 * m + 1)) (by omega)),
    padicValNat_factorial (hB (15 * m + 7) (by omega)),
    padicValNat_factorial (hB (2 * (2 * m + 1)) (by omega))]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  rw [show 15 * m + 7 = 15 * (2 * m + 1) / 2 by omega, show 5 * m + 2 = 5 * (2 * m + 1) / 2 by omega,
    flh 15 4 60 (2 * m + 1) _ (by norm_num) (by norm_num),
    flh 5 12 60 (2 * m + 1) _ (by norm_num) (by norm_num),
    fl 2 30 60 (2 * m + 1) _ (by norm_num) (by norm_num),
    fl 4 15 60 (2 * m + 1) _ (by norm_num) (by norm_num),
    fl 3 20 60 (2 * m + 1) _ (by norm_num) (by norm_num)]
  generalize 60 * (2 * m + 1) / p ^ i = L
  have key : ∀ ρ, ρ < 120 → ρ / 24 + ρ / 15 + ρ / 20 ≤ ρ / 8 + ρ / 30 := by decide
  have := key (L % 120) (Nat.mod_lt _ (by norm_num))
  omega

private lemma D_frac (A B : ℕ) (hB : B ≠ 0) (h : padicValNat p B ≤ padicValNat p A) :
    D p 0 ((A : ℚ) / B) := by
  obtain ⟨b, hb⟩ := pow_padicValNat_dvd (p := p) (n := B)
  have hvA : p ^ padicValNat p B ∣ A := (pow_dvd_pow p h).trans pow_padicValNat_dvd
  obtain ⟨a', ha'⟩ := hvA
  have hnb : ¬ p ∣ b := by
    intro hd
    apply pow_succ_padicValNat_not_dvd (p := p) hB
    conv_rhs => rw [hb]
    rw [pow_succ]
    exact Nat.mul_dvd_mul_left _ hd
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hb
    exact hB hb
  refine ⟨(a' : ℤ), b, hnb, ?_⟩
  have hpv : ((p : ℚ) ^ padicValNat p B) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  have hb0' : (b : ℚ) ≠ 0 := by exact_mod_cast hb0
  have hBq : (B : ℚ) = (p : ℚ) ^ padicValNat p B * b := by
    conv_lhs => rw [hb]
    push_cast; ring
  rw [hBq, ha']
  push_cast
  field_simp

private lemma a_D0 (h5 : 5 ≤ p) (N : ℕ) : D p 0 (OMA.S_oeis_a364177.a N) := by
  rcases Nat.even_or_odd' N with ⟨K, rfl | rfl⟩
  · rw [a_even_fact]
    exact D_frac _ _ (by positivity) (val_even K)
  · rw [a_odd_fact, mul_div_assoc]
    have h4 : D p 0 ((4 : ℚ) ^ (5 * (2 * K + 1))) := by
      simpa using (D.nat (p := p) (4 ^ (5 * (2 * K + 1))))
    exact h4.mul0 (D_frac _ _ (by positivity) (val_odd K))

/-! ### binomial steps -/

private lemma rho (h5 : 5 ≤ p) (a b r : ℕ) (hr : 1 ≤ r) :
    ∃ ρ : ℚ, D p (3 * r) (ρ - 1) ∧ ((a * p ^ r).choose (b * p ^ r) : ℚ) =
      ((a * p ^ (r - 1)).choose (b * p ^ (r - 1)) : ℚ) * ρ := by
  have hp2 : p ≠ 2 := by omega
  have hc := choose_ratio (p := p) hp2 (a * p ^ (r - 1)) (b * p ^ (r - 1))
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hc ⊢
  have e1 : p * (a * p ^ k) = a * p ^ (k + 1) := by ring
  have e2 : p * (b * p ^ k) = b * p ^ (k + 1) := by ring
  rw [e1, e2] at hc
  have e3 : ((a * p ^ (k + 1) : ℕ) : ℚ) = (a : ℚ) * (p : ℚ) ^ (k + 1) := by push_cast; ring
  rw [e3] at hc
  exact ⟨_, R_D h5 (by omega : 1 ≤ k + 1) a b, hc⟩

private lemma step {e : ℕ} {X Y ρ : ℚ} (hX : D p 0 X) (hρ : D p e (ρ - 1)) (h : Y = X * ρ) :
    D p e (Y - X) := (hX.mul0' hρ).congr (by rw [h]; ring)

private lemma D_to_q {e : ℕ} {z : ℚ} (h : D p e z) :
    ∃ q : ℚ, Nat.Coprime q.den p ∧ z = (p : ℚ) ^ e * q := by
  obtain ⟨a, b, hb, hab⟩ := h
  have hb0 : b ≠ 0 := by rintro rfl; exact hb (dvd_zero p)
  have hb0' : (b : ℚ) ≠ 0 := by exact_mod_cast hb0
  refine ⟨Rat.divInt a b, ?_, ?_⟩
  · have hd : ((Rat.divInt a b).den : ℤ) ∣ (b : ℤ) := Rat.den_dvd a b
    have hd' : (Rat.divInt a b).den ∣ b := Int.natCast_dvd_natCast.mp hd
    refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr ?_)
    exact fun h' => hb (h'.trans hd')
  · rw [Rat.divInt_eq_div]
    push_cast
    field_simp
    linear_combination hab

end A364177P

namespace A364177P
open Finset LtsJacobsthal

private lemma a_odd' (N : ℕ) (hN : N % 2 = 1) : OMA.S_oeis_a364177.a N =
    (4 : ℚ) ^ (5 * N) * ((15 * (N / 2) + 7).choose (5 * (N / 2) + 2) : ℚ) *
      ((5 * N).choose (2 * N) : ℚ) / ((4 * N).choose (2 * N) : ℚ) := by
  obtain ⟨m', rfl⟩ : ∃ m', N = 2 * m' + 1 := ⟨N / 2, by omega⟩
  rw [a_odd, show (2 * m' + 1) / 2 = m' by omega]

variable {p : ℕ} [hp : Fact p.Prime]

private lemma comb5 {e : ℕ} (he : 1 ≤ e) {r1 r2 r3 r4 r5 : ℚ} (d1 : D p e (r1 - 1))
    (d2 : D p e (r2 - 1)) (d3 : D p e (r3 - 1)) (d4 : D p e (r4 - 1)) (d5 : D p e (r5 - 1)) :
    D p e (r1 * r2 * r3 * (r4 * r5)⁻¹ - 1) := by
  have a2 := D_one_add d2
  have a3 := D_one_add d3
  have a5 := D_one_add d5
  have n4 := ne0_of he d4
  have n5 := ne0_of he d5
  have i4 := D_inv_unit he d4
  have i5 := D_inv_unit he d5
  have hnum : D p e (r1 * r2 * r3 - r4 * r5) :=
    ((((d1.mul0 a2).mul0 a3).add ((d2.mul0 a3).add d3)).sub ((d4.mul0 a5).add d5)).congr (by ring)
  have e' : r1 * r2 * r3 * (r4 * r5)⁻¹ - 1 = (r1 * r2 * r3 - r4 * r5) * r4⁻¹ * r5⁻¹ := by
    field_simp
  rw [e']
  exact (hnum.mul0 i4).mul0 i5

private lemma comb3 {e : ℕ} (he : 1 ≤ e) {r0 r1 r2 : ℚ} (d0 : D p e (r0 - 1))
    (d1 : D p e (r1 - 1)) (d2 : D p e (r2 - 1)) :
    D p e (r0 * r1 * r2⁻¹ - 1) := by
  have a1 := D_one_add d1
  have n2 := ne0_of he d2
  have i2 := D_inv_unit he d2
  have hnum : D p e (r0 * r1 - r2) :=
    (((d0.mul0 a1).add d1).sub d2).congr (by ring)
  have e' : r0 * r1 * r2⁻¹ - 1 = (r0 * r1 - r2) * r2⁻¹ := by
    field_simp
  rw [e']
  exact hnum.mul0 i2

theorem main' (h5 : 5 ≤ p) (n r : ℕ) (hn : 1 ≤ n) (hr : 1 ≤ r) :
    ∃ q : ℚ, Nat.Coprime q.den p ∧
      OMA.S_oeis_a364177.a (n * p ^ r) - OMA.S_oeis_a364177.a (n * p ^ (r - 1)) =
        (p : ℚ) ^ (3 * r) * q := by
  apply D_to_q
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hp2 : p ≠ 2 := by omega
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · have hm : 1 ≤ m := by omega
    have eN : 2 * m * p ^ (k + 1) = 2 * (m * p ^ (k + 1)) := by ring
    have eM : 2 * m * p ^ k = 2 * (m * p ^ k) := by ring
    rw [eN, eM, a_even, a_even]
    obtain ⟨ρ1, d1, h1⟩ := rho h5 (30 * m) (15 * m) (k + 1) (by omega)
    obtain ⟨ρ2, d2, h2⟩ := rho h5 (15 * m) (5 * m) (k + 1) (by omega)
    obtain ⟨ρ3, d3, h3⟩ := rho h5 (10 * m) (4 * m) (k + 1) (by omega)
    obtain ⟨ρ4, d4, h4⟩ := rho h5 (10 * m) (5 * m) (k + 1) (by omega)
    obtain ⟨ρ5, d5, h5'⟩ := rho h5 (8 * m) (4 * m) (k + 1) (by omega)
    have f : ∀ c s, c * m * p ^ s = c * (m * p ^ s) := fun c s => by ring
    simp only [Nat.add_sub_cancel, f] at h1 h2 h3 h4 h5'
    rw [h1, h2, h3, h4, h5']
    have hX := a_D0 h5 (2 * (m * p ^ k))
    rw [a_even] at hX
    refine step hX (comb5 (by omega) d1 d2 d3 d4 d5) ?_
    have c4 : (((10 * (m * p ^ k)).choose (5 * (m * p ^ k)) : ℕ) : ℚ) ≠ 0 := by
      have := Nat.choose_pos (by omega : 5 * (m * p ^ k) ≤ 10 * (m * p ^ k)); positivity
    have c5 : (((8 * (m * p ^ k)).choose (4 * (m * p ^ k)) : ℕ) : ℚ) ≠ 0 := by
      have := Nat.choose_pos (by omega : 4 * (m * p ^ k) ≤ 8 * (m * p ^ k)); positivity
    have n4 := ne0_of (by omega) d4
    have n5 := ne0_of (by omega) d5
    field_simp
  · have hpo : Odd p := hp.out.odd_of_ne_two hp2
    have hmo : Odd (2 * m + 1) := ⟨m, rfl⟩
    have hNo : (2 * m + 1) * p ^ (k + 1) % 2 = 1 := Nat.odd_iff.mp (hmo.mul (hpo.pow))
    have hMo : (2 * m + 1) * p ^ k % 2 = 1 := Nat.odd_iff.mp (hmo.mul (hpo.pow))
    rw [a_odd' _ hNo, a_odd' _ hMo]
    obtain ⟨ρ0, d0, h0⟩ := odd_core h5 k m
    obtain ⟨ρ1, d1, h1⟩ := rho h5 (5 * (2 * m + 1)) (2 * (2 * m + 1)) (k + 1) (by omega)
    obtain ⟨ρ2, d2, h2⟩ := rho h5 (4 * (2 * m + 1)) (2 * (2 * m + 1)) (k + 1) (by omega)
    have f : ∀ c s, c * (2 * m + 1) * p ^ s = c * ((2 * m + 1) * p ^ s) := fun c s => by ring
    simp only [Nat.add_sub_cancel, f] at h1 h2
    rw [h1, h2, h0]
    have hX := a_D0 h5 ((2 * m + 1) * p ^ k)
    rw [a_odd' _ hMo] at hX
    refine step hX (comb3 (by omega) d0 d1 d2) ?_
    have c2 : (((4 * ((2 * m + 1) * p ^ k)).choose (2 * ((2 * m + 1) * p ^ k)) : ℕ) : ℚ) ≠ 0 := by
      have := Nat.choose_pos (by omega : 2 * ((2 * m + 1) * p ^ k) ≤ 4 * ((2 * m + 1) * p ^ k))
      positivity
    have n2 := ne0_of (by omega) d2
    field_simp

end A364177P

theorem OMA.solution : type_of% @OMA.S_oeis_a364177.main := by
  intro p hp h5 n r hn hr
  haveI := Fact.mk hp
  exact A364177P.main' h5 n r hn hr
