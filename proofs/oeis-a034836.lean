import OMAStatements.S_oeis_a034836

-- Problem: A034836, the number of ways to write n = x * y * z with 1 <= x <= y <= z.
-- Upstream: statements/oeis-a034836.lean (declaration OMA.S_oeis_a034836.main)
--
-- Proof outline (Burnside's lemma for the symmetric group on three letters, done by hand).
-- Let T count ordered triples with product n, Q the x with x^2 | n, and K the x with x^3 = n.
-- * Triples with distinct entries are the 6 orderings of strictly increasing ones; triples
--   with a repeated entry are counted by inclusion-exclusion over the three equalities, each
--   in bijection with the x such that x^2 | n. Sorted triples with a repeat also correspond
--   to those x. Together: 6 a(n) = T + 3 Q + 2 K.
-- * T = (zeta * sigma_0)(n) is multiplicative with value binomial(k + 2, 2) at p^k, so T = np.
-- * x^2 | n exactly when x divides prod p^(s_p / 2), so Q = nsq by the divisor-count formula.
-- * n is a cube exactly when every exponent is divisible by 3, and cube roots are unique,
--   so K = ntp.

namespace OMA.P034836

open OMA.S_oeis_a034836

/-- Ordered factorizations of `n` into three factors. -/
def O (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.Icc 1 n ×ˢ Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter (fun t => t.1 * t.2.1 * t.2.2 = n)

/-- Sorted factorizations: the set counted by `a`. -/
def U (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.Icc 1 n ×ˢ Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter
    (fun t => t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2 ∧ t.1 * t.2.1 * t.2.2 = n)

lemma a_eq (n : ℕ) : a n = (U n).card := rfl

lemma bounds {n x y z : ℕ} (hn : 1 ≤ n) (h : x * y * z = n) :
    (1 ≤ x ∧ x ≤ n) ∧ (1 ≤ y ∧ y ≤ n) ∧ (1 ≤ z ∧ z ≤ n) := by
  have hx : x ≠ 0 := by rintro rfl; simp at h; omega
  have hy : y ≠ 0 := by rintro rfl; simp at h; omega
  have hz : z ≠ 0 := by rintro rfl; simp at h; omega
  refine ⟨⟨by omega, ?_⟩, ⟨by omega, ?_⟩, ⟨by omega, ?_⟩⟩
  · exact Nat.le_of_dvd hn ⟨y * z, by rw [← h] <;> ring⟩
  · exact Nat.le_of_dvd hn ⟨x * z, by rw [← h] <;> ring⟩
  · exact Nat.le_of_dvd hn ⟨x * y, by rw [← h] <;> ring⟩

lemma mem_O {n : ℕ} (hn : 1 ≤ n) {x y z : ℕ} : (x, y, z) ∈ O n ↔ x * y * z = n := by
  simp only [O, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨bounds hn h, h⟩

lemma mem_U {n : ℕ} (hn : 1 ≤ n) {x y z : ℕ} :
    (x, y, z) ∈ U n ↔ x ≤ y ∧ y ≤ z ∧ x * y * z = n := by
  simp only [U, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨bounds hn h.2.2, h⟩

/-- `x` with `x^2 ∣ n`. -/
def Qs (n : ℕ) : Finset ℕ := (Finset.Icc 1 n).filter (fun x => x * x ∣ n)

/-- `x` with `x^3 = n`. -/
def Ks (n : ℕ) : Finset ℕ := (Finset.Icc 1 n).filter (fun x => x * x * x = n)

lemma mem_Qs {n : ℕ} (hn : 1 ≤ n) {x : ℕ} : x ∈ Qs n ↔ 1 ≤ x ∧ x * x ∣ n := by
  simp only [Qs, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨h1, -⟩, h2⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨⟨h1, ?_⟩, h2⟩
    have := Nat.le_of_dvd hn h2
    nlinarith

lemma mem_Ks {n : ℕ} (hn : 1 ≤ n) {x : ℕ} : x ∈ Ks n ↔ x * x * x = n := by
  simp only [Ks, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨(bounds hn h).1, h⟩

lemma div_sq {n x z : ℕ} (hx : 1 ≤ x) (h : x * x * z = n) : n / (x * x) = z := by
  rw [← h]
  exact Nat.mul_div_cancel_left z (by positivity)

lemma sq_mul_div {n x : ℕ} (h : x * x ∣ n) : x * x * (n / (x * x)) = n := Nat.mul_div_cancel' h

/-! ### Distinct entries: six orderings of a strictly increasing triple -/

def L (n : ℕ) : Finset (ℕ × ℕ × ℕ) := (O n).filter (fun t => t.1 < t.2.1 ∧ t.2.1 < t.2.2)

def D (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (O n).filter (fun t => t.1 ≠ t.2.1 ∧ t.2.1 ≠ t.2.2 ∧ t.1 ≠ t.2.2)

/-- The six orderings of a triple. -/
def perm (t : ℕ × ℕ × ℕ) (k : ℕ) : ℕ × ℕ × ℕ :=
  match k with
  | 0 => (t.1, t.2.1, t.2.2)
  | 1 => (t.1, t.2.2, t.2.1)
  | 2 => (t.2.1, t.1, t.2.2)
  | 3 => (t.2.1, t.2.2, t.1)
  | 4 => (t.2.2, t.1, t.2.1)
  | _ => (t.2.2, t.2.1, t.1)

lemma perm_mem {n : ℕ} (hn : 1 ≤ n) {a b c : ℕ} (ht : (a, b, c) ∈ L n) {k : ℕ} (hk : k < 6) :
    perm (a, b, c) k ∈ D n := by
  simp only [L, Finset.mem_filter, mem_O hn] at ht
  obtain ⟨h, hab, hbc⟩ := ht
  interval_cases k <;> simp only [perm, D, Finset.mem_filter, mem_O hn] <;>
    exact ⟨by rw [← h] <;> ring, by omega, by omega, by omega⟩

lemma perm_injOn {n : ℕ} (hn : 1 ≤ n) :
    Set.InjOn (fun p : (ℕ × ℕ × ℕ) × ℕ => perm p.1 p.2) ((L n) ×ˢ Finset.range 6 : Finset _) := by
  rintro ⟨⟨a, b, c⟩, k⟩ h1 ⟨⟨a', b', c'⟩, k'⟩ h2 heq
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, L, Finset.mem_filter,
    Finset.mem_range, mem_O hn] at h1 h2
  obtain ⟨⟨-, hab, hbc⟩, hk⟩ := h1
  obtain ⟨⟨-, hab', hbc'⟩, hk'⟩ := h2
  change perm (a, b, c) k = perm (a', b', c') k' at heq
  interval_cases k <;> interval_cases k' <;> simp only [perm, Prod.mk.injEq, and_true] at heq ⊢ <;> omega

lemma D_sub {n : ℕ} (hn : 1 ≤ n) :
    D n ⊆ ((L n) ×ˢ Finset.range 6).image (fun p => perm p.1 p.2) := by
  rintro ⟨x, y, z⟩ ht
  simp only [D, Finset.mem_filter, mem_O hn] at ht
  obtain ⟨h, h1, h2, h3⟩ := ht
  rw [Finset.mem_image]
  have mk : ∀ (u : ℕ × ℕ × ℕ) (k : ℕ), u ∈ L n → k < 6 → perm u k = (x, y, z) →
      ∃ p ∈ (L n) ×ˢ Finset.range 6, perm p.1 p.2 = (x, y, z) :=
    fun u k hu hk he => ⟨(u, k), Finset.mem_product.mpr ⟨hu, Finset.mem_range.mpr hk⟩, he⟩
  have memL : ∀ a b c, a < b → b < c → a * b * c = n → (a, b, c) ∈ L n := fun a b c hab hbc habc => by
    simp only [L, Finset.mem_filter, mem_O hn]
    exact ⟨habc, hab, hbc⟩
  rcases lt_or_gt_of_ne h1 with h1 | h1 <;> rcases lt_or_gt_of_ne h2 with h2 | h2 <;>
    rcases lt_or_gt_of_ne h3 with h3 | h3
  · exact mk (x, y, z) 0 (memL x y z h1 h2 h) (by norm_num) rfl
  · omega
  · exact mk (x, z, y) 1 (memL x z y h3 h2 (by rw [← h] <;> ring)) (by norm_num) rfl
  · exact mk (z, x, y) 3 (memL z x y h3 h1 (by rw [← h] <;> ring)) (by norm_num) rfl
  · exact mk (y, x, z) 2 (memL y x z h1 h3 (by rw [← h] <;> ring)) (by norm_num) rfl
  · exact mk (y, z, x) 4 (memL y z x h2 h3 (by rw [← h] <;> ring)) (by norm_num) rfl
  · omega
  · exact mk (z, y, x) 5 (memL z y x h2 h1 (by rw [← h] <;> ring)) (by norm_num) rfl

lemma card_D {n : ℕ} (hn : 1 ≤ n) : (D n).card = 6 * (L n).card := by
  have : D n = ((L n) ×ˢ Finset.range 6).image (fun p => perm p.1 p.2) := by
    apply Finset.Subset.antisymm (D_sub hn)
    intro t ht
    obtain ⟨⟨⟨a, b, c⟩, k⟩, hp, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    exact perm_mem hn hp1 (Finset.mem_range.mp hp2)
  rw [this, Finset.card_image_of_injOn (perm_injOn hn), Finset.card_product, Finset.card_range]
  ring

/-! ### Repeated entries: inclusion-exclusion -/

def E12 (n : ℕ) : Finset (ℕ × ℕ × ℕ) := (O n).filter (fun t => t.1 = t.2.1)
def E23 (n : ℕ) : Finset (ℕ × ℕ × ℕ) := (O n).filter (fun t => t.2.1 = t.2.2)
def E13 (n : ℕ) : Finset (ℕ × ℕ × ℕ) := (O n).filter (fun t => t.1 = t.2.2)
def Eall (n : ℕ) : Finset (ℕ × ℕ × ℕ) := (O n).filter (fun t => t.1 = t.2.1 ∧ t.2.1 = t.2.2)

lemma card_E12 {n : ℕ} (hn : 1 ≤ n) : (E12 n).card = (Qs n).card := by
  apply Finset.card_nbij' (fun t => t.1) (fun x => (x, x, n / (x * x)))
  · rintro ⟨x, y, z⟩ ht
    simp only [Finset.mem_coe, E12, Finset.mem_filter, mem_O hn] at ht
    obtain ⟨h, rfl⟩ := ht
    exact (mem_Qs hn).mpr ⟨(bounds hn h).1.1, ⟨z, h.symm⟩⟩
  · intro x hx
    obtain ⟨h1, h2⟩ := (mem_Qs hn).mp hx
    simp only [Finset.mem_coe, E12, Finset.mem_filter, mem_O hn]
    exact ⟨sq_mul_div h2, trivial⟩
  · rintro ⟨x, y, z⟩ ht
    simp only [Finset.mem_coe, E12, Finset.mem_filter, mem_O hn] at ht
    obtain ⟨h, rfl⟩ := ht
    simp only [div_sq (bounds hn h).1.1 h]
  · intro x _
    rfl

lemma card_E23 {n : ℕ} (hn : 1 ≤ n) : (E23 n).card = (Qs n).card := by
  apply Finset.card_nbij' (fun t => t.2.1) (fun y => (n / (y * y), y, y))
  · rintro ⟨x, y, z⟩ ht
    simp only [Finset.mem_coe, E23, Finset.mem_filter, mem_O hn] at ht
    obtain ⟨h, rfl⟩ := ht
    exact (mem_Qs hn).mpr ⟨(bounds hn h).2.1.1, ⟨x, by rw [← h] <;> ring⟩⟩
  · intro y hy
    obtain ⟨h1, h2⟩ := (mem_Qs hn).mp hy
    simp only [Finset.mem_coe, E23, Finset.mem_filter, mem_O hn]
    refine ⟨?_, trivial⟩
    rw [mul_assoc, mul_comm]
    exact sq_mul_div h2
  · rintro ⟨x, y, z⟩ ht
    simp only [Finset.mem_coe, E23, Finset.mem_filter, mem_O hn] at ht
    obtain ⟨h, rfl⟩ := ht
    simp only [div_sq (bounds hn h).2.1.1 (by rw [← h] <;> ring : y * y * x = n)]
  · intro y _
    rfl

lemma card_E13 {n : ℕ} (hn : 1 ≤ n) : (E13 n).card = (Qs n).card := by
  apply Finset.card_nbij' (fun t => t.1) (fun x => (x, n / (x * x), x))
  · rintro ⟨x, y, z⟩ ht
    simp only [Finset.mem_coe, E13, Finset.mem_filter, mem_O hn] at ht
    obtain ⟨h, rfl⟩ := ht
    exact (mem_Qs hn).mpr ⟨(bounds hn h).1.1, ⟨y, by rw [← h] <;> ring⟩⟩
  · intro x hx
    obtain ⟨h1, h2⟩ := (mem_Qs hn).mp hx
    simp only [Finset.mem_coe, E13, Finset.mem_filter, mem_O hn]
    refine ⟨?_, trivial⟩
    calc x * (n / (x * x)) * x = x * x * (n / (x * x)) := by ring
      _ = n := sq_mul_div h2
  · rintro ⟨x, y, z⟩ ht
    simp only [Finset.mem_coe, E13, Finset.mem_filter, mem_O hn] at ht
    obtain ⟨h, rfl⟩ := ht
    simp only [div_sq (bounds hn h).1.1 (by rw [← h] <;> ring : x * x * y = n)]
  · intro x _
    rfl

lemma card_Eall {n : ℕ} (hn : 1 ≤ n) : (Eall n).card = (Ks n).card := by
  apply Finset.card_nbij' (fun t => t.1) (fun x => (x, x, x))
  · rintro ⟨x, y, z⟩ ht
    simp only [Finset.mem_coe, Eall, Finset.mem_filter, mem_O hn] at ht
    obtain ⟨h, rfl, rfl⟩ := ht
    exact (mem_Ks hn).mpr h
  · intro x hx
    simp only [Finset.mem_coe, Eall, Finset.mem_filter, mem_O hn]
    exact ⟨(mem_Ks hn).mp hx, trivial, trivial⟩
  · rintro ⟨x, y, z⟩ ht
    simp only [Finset.mem_coe, Eall, Finset.mem_filter, mem_O hn] at ht
    obtain ⟨-, rfl, rfl⟩ := ht
    rfl
  · intro x _
    rfl

lemma card_nondistinct {n : ℕ} (hn : 1 ≤ n) :
    ((O n).filter (fun t => ¬ (t.1 ≠ t.2.1 ∧ t.2.1 ≠ t.2.2 ∧ t.1 ≠ t.2.2))).card + 2 * (Ks n).card =
      3 * (Qs n).card := by
  have hN : (O n).filter (fun t => ¬ (t.1 ≠ t.2.1 ∧ t.2.1 ≠ t.2.2 ∧ t.1 ≠ t.2.2)) =
      (E12 n ∪ E23 n) ∪ E13 n := by
    ext ⟨x, y, z⟩
    simp only [E12, E23, E13, Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨h, h'⟩
      by_cases h1 : x = y
      · exact Or.inl (Or.inl ⟨h, h1⟩)
      · by_cases h2 : y = z
        · exact Or.inl (Or.inr ⟨h, h2⟩)
        · exact Or.inr ⟨h, by omega⟩
    · rintro ((⟨h, h1⟩ | ⟨h, h1⟩) | ⟨h, h1⟩) <;> exact ⟨h, by omega⟩
  have h12 : E12 n ∩ E23 n = Eall n := by
    ext ⟨x, y, z⟩
    simp only [E12, E23, Eall, Finset.mem_filter, Finset.mem_inter]
    tauto
  have h123 : (E12 n ∪ E23 n) ∩ E13 n = Eall n := by
    ext ⟨x, y, z⟩
    simp only [E12, E23, E13, Eall, Finset.mem_filter, Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨(⟨h, h1⟩ | ⟨h, h1⟩), -, h2⟩ <;> exact ⟨h, by omega, by omega⟩
    · rintro ⟨h, h1, h2⟩
      exact ⟨Or.inl ⟨h, h1⟩, h, by omega⟩
  have u1 := Finset.card_union_add_card_inter (E12 n) (E23 n)
  have u2 := Finset.card_union_add_card_inter (E12 n ∪ E23 n) (E13 n)
  rw [h12, card_Eall hn, card_E12 hn, card_E23 hn] at u1
  rw [h123, card_Eall hn, card_E13 hn] at u2
  rw [hN]
  omega

lemma card_O_eq {n : ℕ} (hn : 1 ≤ n) :
    (O n).card + 2 * (Ks n).card = 6 * (L n).card + 3 * (Qs n).card := by
  have := Finset.card_filter_add_card_filter_not (s := O n)
    (p := fun t => t.1 ≠ t.2.1 ∧ t.2.1 ≠ t.2.2 ∧ t.1 ≠ t.2.2)
  have hD : (O n).filter (fun t => t.1 ≠ t.2.1 ∧ t.2.1 ≠ t.2.2 ∧ t.1 ≠ t.2.2) = D n := rfl
  rw [hD, card_D hn] at this
  have := card_nondistinct hn
  omega

/-! ### Sorted triples -/

lemma card_U_eq {n : ℕ} (hn : 1 ≤ n) : (U n).card = (L n).card + (Qs n).card := by
  have hsplit := Finset.card_filter_add_card_filter_not (s := U n)
    (p := fun t => t.1 < t.2.1 ∧ t.2.1 < t.2.2)
  have hL : (U n).filter (fun t => t.1 < t.2.1 ∧ t.2.1 < t.2.2) = L n := by
    ext ⟨x, y, z⟩
    simp only [L, Finset.mem_filter, mem_U hn, mem_O hn]
    constructor
    · rintro ⟨⟨-, -, h⟩, h1, h2⟩
      exact ⟨h, h1, h2⟩
    · rintro ⟨h, h1, h2⟩
      exact ⟨⟨by omega, by omega, h⟩, h1, h2⟩
  have hR : ((U n).filter (fun t => ¬ (t.1 < t.2.1 ∧ t.2.1 < t.2.2))).card = (Qs n).card := by
    apply Finset.card_nbij' (fun t => if t.1 = t.2.1 then t.1 else t.2.2)
      (fun x => if x ≤ n / (x * x) then (x, x, n / (x * x)) else (n / (x * x), x, x))
    · rintro ⟨x, y, z⟩ ht
      simp only [Finset.mem_coe, Finset.mem_filter, mem_U hn] at ht
      obtain ⟨⟨hxy, hyz, h⟩, hns⟩ := ht
      have hb := bounds hn h
      by_cases hc : x = y
      · subst hc
        simp only [if_true]
        exact (mem_Qs hn).mpr ⟨hb.1.1, ⟨z, h.symm⟩⟩
      · simp only [hc, if_false]
        have hyz' : y = z := by omega
        subst hyz'
        exact (mem_Qs hn).mpr ⟨hb.2.1.1, ⟨x, by rw [← h] <;> ring⟩⟩
    · intro x hx
      obtain ⟨h1, h2⟩ := (mem_Qs hn).mp hx
      have hm := sq_mul_div h2
      by_cases hc : x ≤ n / (x * x)
      · dsimp only
        rw [if_pos hc]
        simp only [Finset.mem_coe, Finset.mem_filter, mem_U hn]
        exact ⟨⟨le_rfl, hc, hm⟩, by omega⟩
      · dsimp only
        rw [if_neg hc]
        simp only [Finset.mem_coe, Finset.mem_filter, mem_U hn]
        refine ⟨⟨by omega, le_rfl, ?_⟩, by omega⟩
        calc n / (x * x) * x * x = x * x * (n / (x * x)) := by ring
          _ = n := hm
    · rintro ⟨x, y, z⟩ ht
      simp only [Finset.mem_coe, Finset.mem_filter, mem_U hn] at ht
      obtain ⟨⟨hxy, hyz, h⟩, hns⟩ := ht
      have hb := bounds hn h
      by_cases hc : x = y
      · subst hc
        have hz : n / (x * x) = z := div_sq hb.1.1 h
        simp only [if_true, hz, hyz]
      · have hyz' : y = z := by omega
        subst hyz'
        have hw : n / (y * y) = x := div_sq hb.2.1.1 (by rw [← h] <;> ring)
        have hlt : ¬ y ≤ x := by omega
        simp only [hc, if_false, hw, hlt]
    · intro x hx
      by_cases hc : x ≤ n / (x * x)
      · simp only [hc, if_true]
      · have hne : n / (x * x) ≠ x := by omega
        simp only [hc, if_false, hne]
  rw [hL, hR] at hsplit
  omega

/-- Burnside's count for the symmetric group on three letters. -/
theorem burnside {n : ℕ} (hn : 1 ≤ n) :
    6 * a n = (O n).card + 3 * (Qs n).card + 2 * (Ks n).card := by
  rw [a_eq, card_U_eq hn]
  have := card_O_eq hn
  omega

end OMA.P034836

namespace OMA.P034836

open OMA.S_oeis_a034836 ArithmeticFunction
open scoped ArithmeticFunction.sigma ArithmeticFunction.zeta

/-! ### Ordered factorizations: `np` -/

lemma card_O_sigma {n : ℕ} (hn : 1 ≤ n) :
    (O n).card = ∑ d ∈ n.divisors, (d.divisorsAntidiagonal).card := by
  rw [← Finset.card_sigma]
  apply Finset.card_nbij' (fun t => (⟨t.1 * t.2.1, (t.1, t.2.1)⟩ : (_ : ℕ) × (ℕ × ℕ)))
    (fun s => (s.2.1, s.2.2, n / s.1))
  · rintro ⟨x, y, z⟩ ht
    simp only [Finset.mem_coe, mem_O hn] at ht
    simp only [Finset.mem_coe, Finset.mem_sigma, Nat.mem_divisors, Nat.mem_divisorsAntidiagonal]
    have hb := bounds hn ht
    exact ⟨⟨⟨z, ht.symm⟩, by omega⟩, trivial, Nat.mul_ne_zero (by omega) (by omega)⟩
  · rintro ⟨d, x, y⟩ hs
    simp only [Finset.mem_coe, Finset.mem_sigma, Nat.mem_divisors,
      Nat.mem_divisorsAntidiagonal] at hs
    obtain ⟨⟨hd, -⟩, hxy, -⟩ := hs
    simp only [Finset.mem_coe, mem_O hn]
    rw [hxy]
    exact Nat.mul_div_cancel' hd
  · rintro ⟨x, y, z⟩ ht
    simp only [Finset.mem_coe, mem_O hn] at ht
    have hb := bounds hn ht
    simp only [Prod.mk.injEq, true_and]
    rw [← ht]
    exact Nat.mul_div_cancel_left z (Nat.mul_pos (by omega) (by omega))
  · rintro ⟨d, x, y⟩ hs
    simp only [Finset.mem_coe, Finset.mem_sigma, Nat.mem_divisors,
      Nat.mem_divisorsAntidiagonal] at hs
    obtain ⟨-, hxy, -⟩ := hs
    simp only [hxy]

lemma card_antidiag (d : ℕ) : (d.divisorsAntidiagonal).card = σ 0 d := by
  rw [sigma_zero_apply, ← Nat.map_div_right_divisors, Finset.card_map]

lemma sum_succ_choose (k : ℕ) : ∑ i ∈ Finset.range (k + 1), (i + 1) = (2 + k).choose 2 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, show 2 + (k + 1) = (2 + k) + 1 by ring,
      Nat.choose_succ_succ, Nat.choose_one_right]
    ring

lemma zeta_sigma_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    ((ζ : ArithmeticFunction ℕ) * σ 0) (p ^ k) = (2 + k).choose 2 := by
  rw [← natCoe_nat ζ, coe_zeta_mul_apply, Nat.divisors_prime_pow hp, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk, sigma_zero_apply_prime_pow hp]
  exact sum_succ_choose k

theorem card_O {n : ℕ} (hn : 1 ≤ n) : (O n).card = np n := by
  have hn0 : n ≠ 0 := by omega
  rw [card_O_sigma hn]
  simp only [card_antidiag]
  rw [← coe_zeta_mul_apply, natCoe_nat,
    (isMultiplicative_zeta.mul isMultiplicative_sigma).multiplicative_factorization _ hn0,
    Nat.prod_factorization_eq_prod_primeFactors, np]
  exact Finset.prod_congr rfl fun p hp =>
    zeta_sigma_prime_pow (Nat.prime_of_mem_primeFactors hp) _

/-! ### Square divisors: `nsq` -/

theorem card_Qs {n : ℕ} (hn : 1 ≤ n) : (Qs n).card = nsq n := by
  have hn0 : n ≠ 0 := by omega
  set g : ℕ →₀ ℕ := Finsupp.mapRange (fun k => k / 2) (Nat.zero_div 2) n.factorization with hg
  have hgp : ∀ p ∈ g.support, p.Prime := by
    intro p hp
    have : p ∈ n.factorization.support := Finsupp.support_mapRange hp
    exact Nat.prime_of_mem_primeFactors (by simpa using this)
  set m : ℕ := g.prod (· ^ ·) with hm
  have hmf : m.factorization = g := Nat.prod_pow_factorization_eq_self hgp
  have hm0 : m ≠ 0 := by
    rw [hm, Finsupp.prod]
    exact Finset.prod_ne_zero_iff.mpr fun p hp => pow_ne_zero _ (hgp p hp).ne_zero
  have hQ : Qs n = m.divisors := by
    ext x
    rw [mem_Qs hn, Nat.mem_divisors]
    constructor
    · rintro ⟨hx, hxx⟩
      refine ⟨?_, hm0⟩
      have hx0 : x ≠ 0 := by omega
      rw [← Nat.factorization_le_iff_dvd hx0 hm0, hmf]
      have h2 := (Nat.factorization_le_iff_dvd (by positivity) hn0).mpr hxx
      intro p
      have := h2 p
      simp only [Nat.factorization_mul hx0 hx0, Finsupp.add_apply] at this
      simp only [hg, Finsupp.mapRange_apply]
      omega
    · rintro ⟨hxm, -⟩
      have hx0 : x ≠ 0 := by rintro rfl; simp at hxm; exact hm0 hxm
      refine ⟨by omega, ?_⟩
      rw [← Nat.factorization_le_iff_dvd (by positivity) hn0]
      have h2 := (Nat.factorization_le_iff_dvd hx0 hm0).mpr hxm
      rw [hmf] at h2
      intro p
      have := h2 p
      simp only [hg, Finsupp.mapRange_apply] at this
      simp only [Nat.factorization_mul hx0 hx0, Finsupp.add_apply]
      omega
  rw [hQ, Nat.card_divisors hm0, ← Nat.support_factorization, hmf, nsq]
  have hfun : ∀ p, g p + 1 = n.factorization p / 2 + 1 := fun p => by
    simp only [hg, Finsupp.mapRange_apply]
  simp only [hfun]
  apply Finset.prod_subset
  · intro p hp
    have : p ∈ n.factorization.support := Finsupp.support_mapRange hp
    simpa using this
  · intro p _ hp
    rw [Finsupp.notMem_support_iff] at hp
    simp only [hg, Finsupp.mapRange_apply] at hp
    simp [hp]

/-! ### Cubes: `ntp` -/

lemma ntp_eq {n : ℕ} : ntp n = if ∀ p ∈ n.primeFactors, n.factorization p % 3 = 0 then 1 else 0 := by
  rw [ntp]
  split_ifs with h
  · apply Finset.prod_eq_one
    intro p hp
    have hs : 0 < n.factorization p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp (by simpa using hp))
    rw [h p hp, Nat.sub_zero, Nat.div_self hs]
  · push_neg at h
    obtain ⟨p, hp, hp3⟩ := h
    apply Finset.prod_eq_zero hp
    apply Nat.div_eq_of_lt
    have : 0 < n.factorization p % 3 := Nat.pos_of_ne_zero hp3
    omega

theorem card_Ks {n : ℕ} (hn : 1 ≤ n) : (Ks n).card = ntp n := by
  have hn0 : n ≠ 0 := by omega
  rw [ntp_eq]
  have key : (∃ x, x * x * x = n) ↔ ∀ p ∈ n.primeFactors, n.factorization p % 3 = 0 := by
    constructor
    · rintro ⟨x, hx⟩ p _
      have hx0 : x ≠ 0 := by rintro rfl; simp at hx; omega
      rw [← hx, show x * x * x = x ^ 3 by ring, Nat.factorization_pow]
      simp
    · intro h
      set g : ℕ →₀ ℕ := Finsupp.mapRange (fun k => k / 3) (Nat.zero_div 3) n.factorization with hg
      have hgp : ∀ p ∈ g.support, p.Prime := by
        intro p hp
        have : p ∈ n.factorization.support := Finsupp.support_mapRange hp
        exact Nat.prime_of_mem_primeFactors (by simpa using this)
      set c : ℕ := g.prod (· ^ ·) with hc
      have hcf : c.factorization = g := Nat.prod_pow_factorization_eq_self hgp
      have hc0 : c ≠ 0 := by
        rw [hc, Finsupp.prod]
        exact Finset.prod_ne_zero_iff.mpr fun p hp => pow_ne_zero _ (hgp p hp).ne_zero
      refine ⟨c, ?_⟩
      rw [show c * c * c = c ^ 3 by ring]
      apply Nat.eq_of_factorization_eq (pow_ne_zero 3 hc0) hn0
      intro p
      rw [Nat.factorization_pow, hcf]
      simp only [Finsupp.smul_apply, smul_eq_mul, hg, Finsupp.mapRange_apply]
      by_cases hp : p ∈ n.primeFactors
      · have := h p hp
        omega
      · have : n.factorization p = 0 := by
          rw [← Finsupp.notMem_support_iff]
          simpa using hp
        rw [this]
  split_ifs with h
  · obtain ⟨x, hx⟩ := key.mpr h
    rw [Finset.card_eq_one]
    refine ⟨x, ?_⟩
    ext y
    rw [mem_Ks hn, Finset.mem_singleton]
    constructor
    · intro hy
      have h3 : y ^ 3 = x ^ 3 := by rw [show y ^ 3 = y * y * y by ring, hy, ← hx]; ring
      exact Nat.pow_left_injective (by norm_num) h3
    · rintro rfl
      exact hx
  · rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro y hy
    exact h (key.mp ⟨y, (mem_Ks hn).mp hy⟩)

/-! ### Assembly -/

theorem main_proof : ∀ n : ℕ, 1 ≤ n →
    a n = (np n + 3 * (nsq n - ntp n) + 5 * ntp n) / 6 ∧
      a n = (np n + 3 * nsq n + 2 * ntp n) / 6 := by
  intro n hn
  have hb := burnside hn
  have hle : (Ks n).card ≤ (Qs n).card := by
    apply Finset.card_le_card
    intro x hx
    have h := (mem_Ks hn).mp hx
    exact (mem_Qs hn).mpr ⟨(bounds hn h).1.1, ⟨x, h.symm⟩⟩
  rw [card_O hn, card_Qs hn, card_Ks hn] at hb
  rw [card_Qs hn, card_Ks hn] at hle
  constructor <;> omega

end OMA.P034836

theorem OMA.solution : type_of% @OMA.S_oeis_a034836.main := OMA.P034836.main_proof
