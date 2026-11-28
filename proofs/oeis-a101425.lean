import OMAStatements.S_oeis_a101425
import Mathlib

-- Orbit counting: 6 * sorted = ordered + 3 * (x = y) + 2 * (x = y = z), then count exponent pairs.

def a101425_S3 {α : Type} (D : Finset α) (h : α → α → α → ℕ) : ℕ :=
  ∑ x ∈ D, ∑ y ∈ D, ∑ z ∈ D, h x y z

def a101425_g (V x y z : ℕ) : ℕ := if x ≤ y ∧ y ≤ z ∧ x * y * z = V then 1 else 0
def a101425_t (V x y z : ℕ) : ℕ := if x * y * z = V then 1 else 0
def a101425_e (V x y z : ℕ) : ℕ := if x = y ∧ x * y * z = V then 1 else 0
def a101425_f (V x y z : ℕ) : ℕ := if x = y ∧ y = z ∧ x * y * z = V then 1 else 0

theorem a101425_swap12 {α : Type} (D : Finset α) (h : α → α → α → ℕ) :
    a101425_S3 D (fun x y z => h y x z) = a101425_S3 D h := by
  unfold a101425_S3
  exact Finset.sum_comm

theorem a101425_swap23 {α : Type} (D : Finset α) (h : α → α → α → ℕ) :
    a101425_S3 D (fun x y z => h x z y) = a101425_S3 D h := by
  unfold a101425_S3
  exact Finset.sum_congr rfl (fun x _ => Finset.sum_comm)

theorem a101425_congr {α : Type} (D : Finset α) (h1 h2 : α → α → α → ℕ)
    (H : ∀ x y z, h1 x y z = h2 x y z) : a101425_S3 D h1 = a101425_S3 D h2 := by
  have e : h1 = h2 := by
    funext x y z
    exact H x y z
  rw [e]

theorem a101425_ite (c : Prop) [Decidable c] :
    (c ∧ (if c then 1 else 0 : ℕ) = 1) ∨ (¬ c ∧ (if c then 1 else 0 : ℕ) = 0) := by
  by_cases h : c <;> simp [h]

theorem a101425_pt (V x y z : ℕ) :
    a101425_g V x y z + a101425_g V y x z + a101425_g V x z y + a101425_g V z x y
      + a101425_g V y z x + a101425_g V z y x
    = a101425_t V x y z + a101425_e V x y z + a101425_e V x z y + a101425_e V y z x
      + 2 * a101425_f V x y z := by
  unfold a101425_g a101425_t a101425_e a101425_f
  have e1 : y * x * z = x * y * z := by ring
  have e2 : x * z * y = x * y * z := by ring
  have e3 : z * x * y = x * y * z := by ring
  have e4 : y * z * x = x * y * z := by ring
  have e5 : z * y * x = x * y * z := by ring
  rw [e1, e2, e3, e4, e5]
  by_cases hV : x * y * z = V
  · simp only [hV, and_true, if_true]
    have a1 := a101425_ite (x ≤ y ∧ y ≤ z)
    have a2 := a101425_ite (y ≤ x ∧ x ≤ z)
    have a3 := a101425_ite (x ≤ z ∧ z ≤ y)
    have a4 := a101425_ite (z ≤ x ∧ x ≤ y)
    have a5 := a101425_ite (y ≤ z ∧ z ≤ x)
    have a6 := a101425_ite (z ≤ y ∧ y ≤ x)
    have a7 := a101425_ite (x = y)
    have a8 := a101425_ite (x = z)
    have a9 := a101425_ite (y = z)
    have a10 := a101425_ite (x = y ∧ y = z)
    omega
  · simp [hV]

theorem a101425_orbit (V : ℕ) (D : Finset ℕ) :
    6 * a101425_S3 D (a101425_g V)
    = a101425_S3 D (a101425_t V) + 3 * a101425_S3 D (a101425_e V)
      + 2 * a101425_S3 D (a101425_f V) := by
  have h1 : a101425_S3 D (fun x y z => a101425_g V y x z) = a101425_S3 D (a101425_g V) :=
    a101425_swap12 D (a101425_g V)
  have h2 : a101425_S3 D (fun x y z => a101425_g V x z y) = a101425_S3 D (a101425_g V) :=
    a101425_swap23 D (a101425_g V)
  have h3 : a101425_S3 D (fun x y z => a101425_g V z x y) = a101425_S3 D (a101425_g V) :=
    (a101425_swap23 D (fun x y z => a101425_g V y x z)).trans h1
  have h4 : a101425_S3 D (fun x y z => a101425_g V y z x) = a101425_S3 D (a101425_g V) :=
    (a101425_swap12 D (fun x y z => a101425_g V x z y)).trans h2
  have h5 : a101425_S3 D (fun x y z => a101425_g V z y x) = a101425_S3 D (a101425_g V) :=
    (a101425_swap23 D (fun x y z => a101425_g V y z x)).trans h4
  have k1 : a101425_S3 D (fun x y z => a101425_e V x z y) = a101425_S3 D (a101425_e V) :=
    a101425_swap23 D (a101425_e V)
  have k2 : a101425_S3 D (fun x y z => a101425_e V y z x) = a101425_S3 D (a101425_e V) :=
    (a101425_swap12 D (fun x y z => a101425_e V x z y)).trans k1
  have hL : a101425_S3 D (fun x y z => a101425_g V x y z + a101425_g V y x z
        + a101425_g V x z y + a101425_g V z x y + a101425_g V y z x + a101425_g V z y x)
      = a101425_S3 D (a101425_g V) + a101425_S3 D (fun x y z => a101425_g V y x z)
        + a101425_S3 D (fun x y z => a101425_g V x z y)
        + a101425_S3 D (fun x y z => a101425_g V z x y)
        + a101425_S3 D (fun x y z => a101425_g V y z x)
        + a101425_S3 D (fun x y z => a101425_g V z y x) := by
    simp only [a101425_S3, Finset.sum_add_distrib]
  have hR : a101425_S3 D (fun x y z => a101425_t V x y z + a101425_e V x y z
        + a101425_e V x z y + a101425_e V y z x + 2 * a101425_f V x y z)
      = a101425_S3 D (a101425_t V) + a101425_S3 D (a101425_e V)
        + a101425_S3 D (fun x y z => a101425_e V x z y)
        + a101425_S3 D (fun x y z => a101425_e V y z x)
        + 2 * a101425_S3 D (a101425_f V) := by
    simp only [a101425_S3, Finset.sum_add_distrib, Finset.mul_sum]
  have hpt : a101425_S3 D (fun x y z => a101425_g V x y z + a101425_g V y x z
        + a101425_g V x z y + a101425_g V z x y + a101425_g V y z x + a101425_g V z y x)
      = a101425_S3 D (fun x y z => a101425_t V x y z + a101425_e V x y z
        + a101425_e V x z y + a101425_e V y z x + 2 * a101425_f V x y z) :=
    a101425_congr D _ _ (a101425_pt V)
  rw [hL, hR, h1, h2, h3, h4, h5, k1, k2] at hpt
  omega

theorem a101425_cub (V : ℕ) :
    OMA.S_oeis_a101425.cuboids V = a101425_S3 V.divisors (a101425_g V) := by
  simp only [OMA.S_oeis_a101425.cuboids, a101425_S3, a101425_g, Finset.card_filter,
    Finset.sum_product]

theorem a101425_divs (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (n : ℕ) :
    (p ^ 5 * q ^ n).divisors
    = (Finset.range 6 ×ˢ Finset.range (n + 1)).image (fun a : ℕ × ℕ => p ^ a.1 * q ^ a.2) := by
  ext x
  simp only [Nat.mem_divisors, Finset.mem_image, Finset.mem_product, Finset.mem_range,
    Prod.exists]
  constructor
  · rintro ⟨hx, -⟩
    obtain ⟨y, z, hy, hz, rfl⟩ := dvd_mul.mp hx
    obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow hp).mp hy
    obtain ⟨j, hj, rfl⟩ := (Nat.dvd_prime_pow hq).mp hz
    exact ⟨i, j, ⟨by omega, by omega⟩, rfl⟩
  · rintro ⟨i, j, ⟨hi, hj⟩, rfl⟩
    exact ⟨Nat.mul_dvd_mul (pow_dvd_pow p (by omega)) (pow_dvd_pow q (by omega)),
      mul_ne_zero (pow_ne_zero _ hp.ne_zero) (pow_ne_zero _ hq.ne_zero)⟩

theorem a101425_uf (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) (a b c d : ℕ)
    (h : p ^ a * q ^ b = p ^ c * q ^ d) : a = c ∧ b = d := by
  have h1 := congrArg (fun m => m.factorization p) h
  have h2 := congrArg (fun m => m.factorization q) h
  simp [Nat.factorization_mul, hp.ne_zero, hq.ne_zero, hp.factorization_pow,
    hq.factorization_pow, hne, hne.symm] at h1 h2
  exact ⟨h1, h2⟩

theorem a101425_inj (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    Function.Injective (fun a : ℕ × ℕ => p ^ a.1 * q ^ a.2) := by
  intro a b h
  obtain ⟨h1, h2⟩ := a101425_uf p q hp hq hne _ _ _ _ h
  exact Prod.ext h1 h2

theorem a101425_phi (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) (a b : ℕ × ℕ) :
    p ^ a.1 * q ^ a.2 = p ^ b.1 * q ^ b.2 ↔ a.1 = b.1 ∧ a.2 = b.2 := by
  constructor
  · exact a101425_uf p q hp hq hne _ _ _ _
  · rintro ⟨h1, h2⟩
    rw [h1, h2]

theorem a101425_prod (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) (n : ℕ)
    (a b c : ℕ × ℕ) :
    p ^ a.1 * q ^ a.2 * (p ^ b.1 * q ^ b.2) * (p ^ c.1 * q ^ c.2) = p ^ 5 * q ^ n
    ↔ a.1 + b.1 + c.1 = 5 ∧ a.2 + b.2 + c.2 = n := by
  constructor
  · intro h
    apply a101425_uf p q hp hq hne
    rw [← h]
    ring
  · rintro ⟨h1, h2⟩
    rw [← h1, ← h2]
    ring

theorem a101425_image {α β : Type} [DecidableEq β] (φ : α → β) (hφ : Function.Injective φ)
    (R : Finset α) (h : β → β → β → ℕ) :
    a101425_S3 (R.image φ) h = a101425_S3 R (fun a b c => h (φ a) (φ b) (φ c)) := by
  unfold a101425_S3
  have hinj : ∀ x ∈ R, ∀ y ∈ R, φ x = φ y → x = y := fun x _ y _ hxy => hφ hxy
  rw [Finset.sum_image hinj]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.sum_image hinj]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Finset.sum_image hinj]

theorem a101425_fact (A B : Finset ℕ) (u v : ℕ → ℕ → ℕ → ℕ) :
    a101425_S3 (A ×ˢ B) (fun a b c => u a.1 b.1 c.1 * v a.2 b.2 c.2)
    = a101425_S3 A u * a101425_S3 B v := by
  simp only [a101425_S3, Finset.sum_product, ← Finset.mul_sum, ← Finset.sum_mul]

theorem a101425_ind (P Q : Prop) [Decidable P] [Decidable Q] :
    (if P ∧ Q then 1 else 0 : ℕ) = (if P then 1 else 0) * (if Q then 1 else 0) := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]

theorem a101425_inner (n s : ℕ) :
    ∑ j ∈ Finset.range (n + 1), (if s + j = n then 1 else 0) = if s ≤ n then 1 else 0 := by
  split_ifs with h
  · rw [Finset.sum_eq_single (n - s)]
    · rw [if_pos (by omega)]
    · intro j _ hj
      rw [if_neg (by omega)]
    · intro hn
      exact absurd (Finset.mem_range.mpr (by omega)) hn
  · apply Finset.sum_eq_zero
    intro j _
    rw [if_neg (by omega)]

theorem a101425_tri (n : ℕ) :
    2 * ∑ k ∈ Finset.range (n + 1), (n + 1 - k) = (n + 1) * (n + 2) := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have h : ∑ k ∈ Finset.range (m + 1), (m + 1 + 1 - k)
        = ∑ k ∈ Finset.range (m + 1), (m + 1 - k) + (m + 1) := by
      have h' : ∀ k ∈ Finset.range (m + 1), m + 1 + 1 - k = (m + 1 - k) + 1 := by
        intro k hk
        have := Finset.mem_range.mp hk
        omega
      rw [Finset.sum_congr rfl h', Finset.sum_add_distrib]
      simp
    rw [h]
    have e : m + 1 + 1 - (m + 1) = 1 := by omega
    rw [e]
    nlinarith [ih]

theorem a101425_JT (n : ℕ) :
    2 * a101425_S3 (Finset.range (n + 1)) (fun j1 j2 j3 => if j1 + j2 + j3 = n then 1 else 0)
    = (n + 1) * (n + 2) := by
  have h1 : ∀ j1 ∈ Finset.range (n + 1), ∑ j2 ∈ Finset.range (n + 1),
      ∑ j3 ∈ Finset.range (n + 1), (if j1 + j2 + j3 = n then 1 else 0) = n + 1 - j1 := by
    intro j1 _
    simp only [a101425_inner]
    rw [← Finset.card_filter]
    have hf : (Finset.range (n + 1)).filter (fun j => j1 + j ≤ n) = Finset.range (n + 1 - j1) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    rw [hf, Finset.card_range]
  unfold a101425_S3
  rw [Finset.sum_congr rfl h1]
  exact a101425_tri n

theorem a101425_JE (n : ℕ) :
    a101425_S3 (Finset.range (n + 1))
      (fun j1 j2 j3 => if j1 = j2 ∧ j1 + j2 + j3 = n then 1 else 0) = n / 2 + 1 := by
  have h1 : ∀ j1 ∈ Finset.range (n + 1), ∑ j2 ∈ Finset.range (n + 1),
      ∑ j3 ∈ Finset.range (n + 1), (if j1 = j2 ∧ j1 + j2 + j3 = n then 1 else 0)
      = if 2 * j1 ≤ n then 1 else 0 := by
    intro j1 hj1
    rw [Finset.sum_eq_single j1]
    · simp only [true_and, a101425_inner]
      split_ifs <;> omega
    · intro j2 _ hne
      apply Finset.sum_eq_zero
      intro j3 _
      rw [if_neg]
      intro h
      exact hne h.1.symm
    · intro h
      exact absurd hj1 h
  unfold a101425_S3
  rw [Finset.sum_congr rfl h1, ← Finset.card_filter]
  have hf : (Finset.range (n + 1)).filter (fun j => 2 * j ≤ n) = Finset.range (n / 2 + 1) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [hf, Finset.card_range]

theorem a101425_T (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) (n : ℕ) :
    a101425_S3 (p ^ 5 * q ^ n).divisors (a101425_t (p ^ 5 * q ^ n))
    = a101425_S3 (Finset.range 6) (fun i1 i2 i3 => if i1 + i2 + i3 = 5 then 1 else 0)
      * a101425_S3 (Finset.range (n + 1))
        (fun j1 j2 j3 => if j1 + j2 + j3 = n then 1 else 0) := by
  rw [a101425_divs p q hp hq n, a101425_image _ (a101425_inj p q hp hq hne), ← a101425_fact]
  refine a101425_congr _ _ _ (fun a b c => ?_)
  unfold a101425_t
  rw [← a101425_ind]
  exact if_congr (a101425_prod p q hp hq hne n a b c) rfl rfl

theorem a101425_E (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) (n : ℕ) :
    a101425_S3 (p ^ 5 * q ^ n).divisors (a101425_e (p ^ 5 * q ^ n))
    = a101425_S3 (Finset.range 6)
        (fun i1 i2 i3 => if i1 = i2 ∧ i1 + i2 + i3 = 5 then 1 else 0)
      * a101425_S3 (Finset.range (n + 1))
        (fun j1 j2 j3 => if j1 = j2 ∧ j1 + j2 + j3 = n then 1 else 0) := by
  rw [a101425_divs p q hp hq n, a101425_image _ (a101425_inj p q hp hq hne), ← a101425_fact]
  refine a101425_congr _ _ _ (fun a b c => ?_)
  unfold a101425_e
  rw [← a101425_ind]
  refine if_congr ?_ rfl rfl
  rw [a101425_prod p q hp hq hne n a b c, a101425_phi p q hp hq hne a b]
  tauto

theorem a101425_F (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) (n : ℕ) :
    a101425_S3 (p ^ 5 * q ^ n).divisors (a101425_f (p ^ 5 * q ^ n))
    = a101425_S3 (Finset.range 6)
        (fun i1 i2 i3 => if i1 = i2 ∧ i2 = i3 ∧ i1 + i2 + i3 = 5 then 1 else 0)
      * a101425_S3 (Finset.range (n + 1))
        (fun j1 j2 j3 => if j1 = j2 ∧ j2 = j3 ∧ j1 + j2 + j3 = n then 1 else 0) := by
  rw [a101425_divs p q hp hq n, a101425_image _ (a101425_inj p q hp hq hne), ← a101425_fact]
  refine a101425_congr _ _ _ (fun a b c => ?_)
  unfold a101425_f
  rw [← a101425_ind]
  refine if_congr ?_ rfl rfl
  rw [a101425_prod p q hp hq hne n a b c, a101425_phi p q hp hq hne a b,
    a101425_phi p q hp hq hne b c]
  tauto

theorem OMA.solution : type_of% @OMA.S_oeis_a101425.main := by
  intro p q hp hq hne n
  have hc := a101425_cub (p ^ 5 * q ^ n)
  have ho := a101425_orbit (p ^ 5 * q ^ n) (p ^ 5 * q ^ n).divisors
  have hT := a101425_T p q hp hq hne n
  have hE := a101425_E p q hp hq hne n
  have hF := a101425_F p q hp hq hne n
  have hJT := a101425_JT n
  have hJE := a101425_JE n
  have c1 : a101425_S3 (Finset.range 6)
      (fun i1 i2 i3 => if i1 + i2 + i3 = 5 then 1 else 0) = 21 := by decide
  have c2 : a101425_S3 (Finset.range 6)
      (fun i1 i2 i3 => if i1 = i2 ∧ i1 + i2 + i3 = 5 then 1 else 0) = 3 := by decide
  have c3 : a101425_S3 (Finset.range 6)
      (fun i1 i2 i3 => if i1 = i2 ∧ i2 = i3 ∧ i1 + i2 + i3 = 5 then 1 else 0) = 0 := by decide
  rw [c1] at hT
  rw [c2, hJE] at hE
  rw [c3, zero_mul] at hF
  rw [hT, hE, hF] at ho
  rw [hc]
  generalize a101425_S3 (p ^ 5 * q ^ n).divisors (a101425_g (p ^ 5 * q ^ n)) = c at ho ⊢
  generalize a101425_S3 (Finset.range (n + 1))
    (fun j1 j2 j3 => if j1 + j2 + j3 = n then 1 else 0) = J at ho hJT
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' n
  · have hd : n / 2 = k := by omega
    have hpow : (-1 : ℤ) ^ n = 1 := Even.neg_one_pow ⟨k, by omega⟩
    rw [hd] at ho
    rw [hpow]
    have h8 : 8 * c = 40 + 48 * n + 14 * n ^ 2 := by nlinarith [ho, hJT, hk]
    have h8z := congrArg (Nat.cast : ℕ → ℤ) h8
    push_cast at h8z
    linarith
  · have hd : n / 2 = k := by omega
    have hpow : (-1 : ℤ) ^ n = -1 := Odd.neg_one_pow ⟨k, hk⟩
    rw [hd] at ho
    rw [hpow]
    have h8 : 8 * c = 34 + 48 * n + 14 * n ^ 2 := by nlinarith [ho, hJT, hk]
    have h8z := congrArg (Nat.cast : ℕ → ℤ) h8
    push_cast at h8z
    linarith
