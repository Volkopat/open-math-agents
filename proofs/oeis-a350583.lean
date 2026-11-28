import OMAStatements.S_oeis_a350583

-- Problem: A350583: Coefficients of the expansion of Sum_{n,m>=1} (-1)^m*q^(2*n*m+m)/((1+q^n)*(1-q^(2*m-1))) (odd powers only).
-- Upstream: formal-conjectures statements/oeis-a350583.lean:0 (declaration OMA.S_oeis_a350583.main)
-- Credit: @Rahultalanki1 (the owner of the agent is credited as the solver)
-- Proof: Elementary finite-bijection formalization of Qianwen Fang (arXiv:2604.06242) with an explicit sign-reversing involution on the residual divisor sum.
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.P_oeis_a350583

open OMA.S_oeis_a350583

private def box (N : ℕ) : Finset Index :=
  Finset.Iic ((N, N, N, N) : Index)

private def sgn (a b : ℕ) : ℤ :=
  if (a + b) % 2 = 0 then 1 else -1

private lemma sgn_eq_of_mod (a b c d : ℕ) (h : (a + b) % 2 = (c + d) % 2) :
    sgn a b = sgn c d := by
  unfold sgn
  rw [h]

private lemma sgn_neg_of_mod (a b c d : ℕ) (h : (a + b) % 2 ≠ (c + d) % 2) :
    sgn a b = -sgn c d := by
  unfold sgn
  have h1 : (a + b) % 2 = 0 ∨ (a + b) % 2 = 1 := Nat.mod_two_eq_zero_or_one (a + b)
  have h2 : (c + d) % 2 = 0 ∨ (c + d) % 2 = 1 := Nat.mod_two_eq_zero_or_one (c + d)
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> simp_all

private lemma mem_box {N a b c d : ℕ} (ha : a ≤ N) (hb : b ≤ N) (hc : c ≤ N) (hd : d ≤ N) :
    ((a, b, c, d) : Index) ∈ box N := by
  simp [box, Prod.le_def, ha, hb, hc, hd]

private lemma sum_eq_zero_of_involution {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → ℤ) (g : α → α)
    (hg_mem : ∀ x ∈ s, g x ∈ s)
    (hg_inv : ∀ x ∈ s, g (g x) = x)
    (hg_neg : ∀ x ∈ s, f (g x) = -f x) :
    ∑ x ∈ s, f x = 0 := by
  have h1 : ∑ x ∈ s, f (g x) = ∑ x ∈ s, f x :=
    Finset.sum_nbij' g g hg_mem hg_mem hg_inv hg_inv (fun _ _ => rfl)
  have h2 : ∑ x ∈ s, f (g x) = - ∑ x ∈ s, f x := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl hg_neg
  linarith

-- Define the finite index sets inside box N for each series coefficient:
-- All tuples are represented as Index = ℕ × ℕ × ℕ × ℕ.

private def setY (N : ℕ) : Finset Index :=
  (box N).filter fun r => 0 < r.1 ∧ 0 < r.2.1 ∧ geometricDegree r = N

private def setY2 (N : ℕ) : Finset Index :=
  (box N).filter fun r =>
    0 < r.1 ∧ 2 * r.1 ≤ r.2.2.1 ∧ 0 < r.2.2.2 ∧
      r.1 + (2 * r.1 - 1) * r.2.1 + r.2.2.1 * r.2.2.2 = N

private def setZ (N : ℕ) : Finset Index :=
  (box N).filter fun r =>
    0 < r.1 ∧ 0 < r.2.2.1 ∧ r.2.2.1 < 2 * r.1 ∧ 0 < r.2.2.2 ∧
      r.1 + (2 * r.1 - 1) * r.2.1 + r.2.2.1 * r.2.2.2 = N

private def setZodd (N : ℕ) : Finset Index :=
  (box N).filter fun r =>
    0 < r.1 ∧ 0 < r.2.2.1 ∧ r.2.2.1 < 2 * r.1 ∧ r.2.2.1 % 2 = 1 ∧ 0 < r.2.2.2 ∧
      r.1 + (2 * r.1 - 1) * r.2.1 + r.2.2.1 * r.2.2.2 = N

private def setZeven (N : ℕ) : Finset Index :=
  (box N).filter fun r =>
    0 < r.1 ∧ 0 < r.2.2.1 ∧ r.2.2.1 < 2 * r.1 ∧ r.2.2.1 % 2 = 0 ∧ 0 < r.2.2.2 ∧
      r.1 + (2 * r.1 - 1) * r.2.1 + r.2.2.1 * r.2.2.2 = N

private def setD1 (N : ℕ) : Finset Index :=
  (box N).filter fun r =>
    0 < r.1 ∧ 0 < r.2.2.1 ∧ 0 < r.2.2.2 ∧
      r.1 + (2 * r.1 - 1) * r.2.1 + r.2.2.1 * r.2.2.2 = N

private def setD2 (N : ℕ) : Finset Index :=
  (box N).filter fun r =>
    0 < r.1 ∧ 0 < r.2.2.1 ∧ 0 < r.2.2.2 ∧ r.2.2.2 % 2 = 1 ∧
      r.1 + (2 * r.1 - 1) * r.2.1 + r.2.2.1 * r.2.2.2 = N

private def setDdiff (N : ℕ) : Finset Index :=
  (box N).filter fun r =>
    0 < r.1 ∧ 0 < r.2.2.1 ∧ 0 < r.2.2.2 ∧ r.2.2.2 % 2 = 0 ∧
      r.1 + (2 * r.1 - 1) * r.2.1 + r.2.2.1 * r.2.2.2 = N

private def setA (N : ℕ) : Finset Index :=
  (box N).filter fun r =>
    r.1 < r.2.1 ∧
      r.2.1 + 1 + (2 * r.1 + 1) * r.2.2.1 + (2 * r.2.1 + 1) * r.2.2.2 = N

private def setB (N : ℕ) : Finset Index :=
  (box N).filter fun r =>
    r.1 < r.2.1 ∧
      r.1 + 2 * r.2.1 + 2 + (2 * r.1 + 1) * r.2.2.1 + (2 * r.2.1 + 1) * r.2.2.2 = N

private def setB1 (N : ℕ) : Finset Index :=
  (box N).filter fun r =>
    r.2.1 ≤ r.1 ∧
      r.1 + 2 * r.2.1 + 2 + (2 * r.1 + 1) * r.2.2.1 + (2 * r.2.1 + 1) * r.2.2.2 = N

private def setBB1 (N : ℕ) : Finset Index :=
  (box N).filter fun r =>
    r.1 + 2 * r.2.1 + 2 + (2 * r.1 + 1) * r.2.2.1 + (2 * r.2.1 + 1) * r.2.2.2 = N

private def sgn13 (r : Index) : ℤ := sgn r.1 r.2.2.1
private def sgn34 (r : Index) : ℤ := sgn r.2.2.1 r.2.2.2

private lemma geometricCoefficient_eq_sum_setY (N : ℕ) :
    geometricCoefficient N = ∑ r ∈ setY N, geometricSign r := by
  unfold geometricCoefficient setY box
  congr 1

-- Bijection 1: Y <-> Y2
private lemma sum_setY_eq_sum_setY2 (N : ℕ) :
    ∑ r ∈ setY N, geometricSign r = ∑ r ∈ setY2 N, sgn13 r := by
  refine Finset.sum_nbij'
    (fun r => (r.1, r.2.2.2, 2 * r.1 + r.2.2.1, r.2.1))
    (fun r => (r.1, r.2.2.2, r.2.2.1 - 2 * r.1, r.2.1))
    ?_ ?_ ?_ ?_ ?_
  · intro ⟨m, n, k, l⟩ hr
    simp only [setY, setY2, Finset.mem_filter] at hr ⊢
    rcases hr with ⟨_, hm, hn, hdeg⟩
    change 2 * m * n + m + n * k + (2 * m - 1) * l = N at hdeg
    refine ⟨mem_box ?_ ?_ ?_ ?_, hm, by omega, hn, ?_⟩
    · nlinarith
    · have h1 : 1 ≤ 2 * m - 1 := by omega
      nlinarith
    · have h2 : (2 * m + k) * 1 ≤ (2 * m + k) * n := Nat.mul_le_mul_left _ hn
      nlinarith
    · nlinarith
    · have h2m : 1 ≤ 2 * m := by omega
      zify [h2m] at hdeg ⊢
      linarith
  · intro ⟨m, l, r, j⟩ hr
    simp only [setY, setY2, Finset.mem_filter] at hr ⊢
    rcases hr with ⟨_, hm, hr2m, hj, hdeg⟩
    refine ⟨mem_box ?_ ?_ ?_ ?_, hm, hj, ?_⟩
    · omega
    · have h1 : 1 * j ≤ r * j := Nat.mul_le_mul_right _ (by omega)
      omega
    · have h1 : r * 1 ≤ r * j := Nat.mul_le_mul_left _ hj
      omega
    · have h1 : 1 * l ≤ (2 * m - 1) * l := Nat.mul_le_mul_right _ (by omega)
      omega
    · change 2 * m * j + m + j * (r - 2 * m) + (2 * m - 1) * l = N
      have h2m : 1 ≤ 2 * m := by omega
      zify [h2m, hr2m] at hdeg ⊢
      linarith
  · intro ⟨m, n, k, l⟩ _
    refine Prod.ext rfl (Prod.ext rfl (Prod.ext ?_ rfl))
    dsimp only; omega
  · intro ⟨m, l, r, j⟩ hr
    simp only [setY2, Finset.mem_filter] at hr
    refine Prod.ext rfl (Prod.ext rfl (Prod.ext ?_ rfl))
    dsimp only; omega
  · intro ⟨m, n, k, l⟩ _
    dsimp only [geometricSign, sgn13, sgn]
    have hmod : (m + k) % 2 = (m + (2 * m + k)) % 2 := by omega
    rw [hmod]

-- Split D1 = Y2 ⊔ Z
private lemma sum_setD1_eq (N : ℕ) :
    ∑ r ∈ setD1 N, sgn13 r = (∑ r ∈ setY2 N, sgn13 r) + (∑ r ∈ setZ N, sgn13 r) := by
  have hunion : setD1 N = setY2 N ∪ setZ N := by
    ext ⟨m, l, r, j⟩
    simp only [setD1, setY2, setZ, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro ⟨hb, hm, hr, hj, hdeg⟩
      by_cases hlt : r < 2 * m
      · exact Or.inr ⟨hb, hm, hr, hlt, hj, hdeg⟩
      · exact Or.inl ⟨hb, hm, by omega, hj, hdeg⟩
    · rintro (⟨hb, hm, hge, hj, hdeg⟩ | ⟨hb, hm, hr, _, hj, hdeg⟩)
      · exact ⟨hb, hm, by omega, hj, hdeg⟩
      · exact ⟨hb, hm, hr, hj, hdeg⟩
  have hdisj : Disjoint (setY2 N) (setZ N) := by
    rw [Finset.disjoint_left]
    intro ⟨m, l, r, j⟩ h1 h2
    simp only [setY2, setZ, Finset.mem_filter] at h1 h2
    omega
  rw [hunion, Finset.sum_union hdisj]

-- Split Z = Zodd ⊔ Zeven
private lemma sum_setZ_eq (N : ℕ) :
    ∑ r ∈ setZ N, sgn13 r = (∑ r ∈ setZodd N, sgn13 r) + (∑ r ∈ setZeven N, sgn13 r) := by
  have hunion : setZ N = setZodd N ∪ setZeven N := by
    ext ⟨m, l, r, j⟩
    simp only [setZ, setZodd, setZeven, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro ⟨hb, hm, hr, hlt, hj, hdeg⟩
      rcases Nat.mod_two_eq_zero_or_one r with h0 | h1
      · exact Or.inr ⟨hb, hm, hr, hlt, h0, hj, hdeg⟩
      · exact Or.inl ⟨hb, hm, hr, hlt, h1, hj, hdeg⟩
    · rintro (⟨hb, hm, hr, hlt, _, hj, hdeg⟩ | ⟨hb, hm, hr, hlt, _, hj, hdeg⟩)
      · exact ⟨hb, hm, hr, hlt, hj, hdeg⟩
      · exact ⟨hb, hm, hr, hlt, hj, hdeg⟩
  have hdisj : Disjoint (setZodd N) (setZeven N) := by
    rw [Finset.disjoint_left]
    intro ⟨m, l, r, j⟩ h1 h2
    simp only [setZodd, setZeven, Finset.mem_filter] at h1 h2
    omega
  rw [hunion, Finset.sum_union hdisj]

-- Bijection 2a: A <-> Zodd
private lemma sum_setA_eq_sum_setZodd (N : ℕ) :
    ∑ r ∈ setA N, sgn34 r = ∑ r ∈ setZodd N, sgn13 r := by
  refine Finset.sum_nbij'
    (fun r => (r.2.2.2 + r.2.2.1 + 1, r.1, 2 * r.2.2.2 + 1, r.2.1 - r.1))
    (fun r => (r.2.1, r.2.1 + r.2.2.2, r.1 - r.2.2.1 / 2 - 1, r.2.2.1 / 2))
    ?_ ?_ ?_ ?_ ?_
  · intro ⟨i, j, u, v⟩ hr
    simp only [setA, setZodd, Finset.mem_filter] at hr ⊢
    rcases hr with ⟨_, hij, hdeg⟩
    have hEq :
        (v + u + 1) + (2 * (v + u + 1) - 1) * i + (2 * v + 1) * (j - i) = N := by
      zify [Nat.le_of_lt hij] at hdeg ⊢
      have hsub : 1 ≤ 2 * (v + u + 1) := by omega
      rw [Nat.cast_sub hsub]
      push_cast
      linarith
    refine ⟨mem_box ?_ ?_ ?_ ?_, by omega, by omega, by omega, by omega, by omega, hEq⟩
    · have h1 : 1 * u ≤ (2 * i + 1) * u := Nat.mul_le_mul_right _ (by omega)
      have h2 : 1 * v ≤ (2 * j + 1) * v := Nat.mul_le_mul_right _ (by omega)
      omega
    · have h1 : 1 * i ≤ (2 * (v + u + 1) - 1) * i := Nat.mul_le_mul_right _ (by omega)
      omega
    · have h1 : (2 * v + 1) * 1 ≤ (2 * v + 1) * (j - i) := Nat.mul_le_mul_left _ (by omega)
      omega
    · omega
  · intro ⟨m, l, r, j⟩ hr
    simp only [setA, setZodd, Finset.mem_filter] at hr ⊢
    rcases hr with ⟨_, hm, hrg, hlt, hodd, hj, hdeg⟩
    set q := r / 2
    have hr_eq : r = 2 * q + 1 := by omega
    have h2m : 1 ≤ 2 * m := by omega
    have hEq :
        (l + j) + 1 + (2 * l + 1) * (m - q - 1) + (2 * (l + j) + 1) * q = N := by
      have hsub : ((m - q - 1 : ℕ) : ℤ) = (m : ℤ) - (q : ℤ) - 1 := by omega
      have hdeg' : ((m + (2 * m - 1) * l + (2 * q + 1) * j : ℕ) : ℤ) = (N : ℤ) := by
        exact_mod_cast (hr_eq ▸ hdeg)
      zify [h2m] at hdeg' ⊢
      rw [hsub]
      linarith
    refine ⟨mem_box ?_ ?_ ?_ ?_, by omega, hEq⟩
    · have h1 : 1 * l ≤ (2 * m - 1) * l := Nat.mul_le_mul_right _ (by omega)
      omega
    · have h1 : 1 * l ≤ (2 * m - 1) * l := Nat.mul_le_mul_right _ (by omega)
      have h2 : 1 * j ≤ r * j := Nat.mul_le_mul_right _ (by omega)
      omega
    · omega
    · have h1 : r * 1 ≤ r * j := Nat.mul_le_mul_left _ hj
      omega
  · intro ⟨i, j, u, v⟩ hr
    simp only [setA, Finset.mem_filter] at hr
    ext <;> dsimp only <;> try omega
  · intro ⟨m, l, r, j⟩ hr
    simp only [setZodd, Finset.mem_filter] at hr
    ext <;> dsimp only <;> try omega
  · intro ⟨i, j, u, v⟩ _
    dsimp only [sgn34, sgn13]
    apply sgn_eq_of_mod
    omega

-- Bijection 2b: B <-> Zeven
private lemma sum_setB_eq_sum_setZeven (N : ℕ) :
    ∑ r ∈ setB N, sgn34 r = ∑ r ∈ setZeven N, sgn13 r := by
  refine Finset.sum_nbij'
    (fun r => (r.2.2.2 + r.2.2.1 + 2, r.1, 2 * r.2.2.2 + 2, r.2.1 - r.1))
    (fun r => (r.2.1, r.2.1 + r.2.2.2, r.1 - r.2.2.1 / 2 - 1, r.2.2.1 / 2 - 1))
    ?_ ?_ ?_ ?_ ?_
  · intro ⟨i, j, u, v⟩ hr
    simp only [setB, setZeven, Finset.mem_filter] at hr ⊢
    rcases hr with ⟨_, hij, hdeg⟩
    have hEq :
        (v + u + 2) + (2 * (v + u + 2) - 1) * i + (2 * v + 2) * (j - i) = N := by
      zify [Nat.le_of_lt hij] at hdeg ⊢
      have hsub : 1 ≤ 2 * (v + u + 2) := by omega
      rw [Nat.cast_sub hsub]
      push_cast
      linarith
    refine ⟨mem_box ?_ ?_ ?_ ?_, by omega, by omega, by omega, by omega, by omega, hEq⟩
    · have h1 : 1 * u ≤ (2 * i + 1) * u := Nat.mul_le_mul_right _ (by omega)
      have h2 : 1 * v ≤ (2 * j + 1) * v := Nat.mul_le_mul_right _ (by omega)
      omega
    · have h1 : 1 * i ≤ (2 * (v + u + 2) - 1) * i := Nat.mul_le_mul_right _ (by omega)
      omega
    · have h1 : (2 * v + 2) * 1 ≤ (2 * v + 2) * (j - i) := Nat.mul_le_mul_left _ (by omega)
      omega
    · omega
  · intro ⟨m, l, r, j⟩ hr
    simp only [setB, setZeven, Finset.mem_filter] at hr ⊢
    rcases hr with ⟨_, hm, hrg, hlt, heven, hj, hdeg⟩
    set q := r / 2
    have hr_eq : r = 2 * q := by omega
    have h2m : 1 ≤ 2 * m := by omega
    have hEq :
        l + 2 * (l + j) + 2 + (2 * l + 1) * (m - q - 1) +
          (2 * (l + j) + 1) * (q - 1) = N := by
      have hsub1 : ((m - q - 1 : ℕ) : ℤ) = (m : ℤ) - (q : ℤ) - 1 := by omega
      have hsub2 : ((q - 1 : ℕ) : ℤ) = (q : ℤ) - 1 := by omega
      have hdeg' : ((m + (2 * m - 1) * l + (2 * q) * j : ℕ) : ℤ) = (N : ℤ) := by
        exact_mod_cast (hr_eq ▸ hdeg)
      zify [h2m] at hdeg' ⊢
      rw [hsub1, hsub2]
      linarith
    refine ⟨mem_box ?_ ?_ ?_ ?_, by omega, hEq⟩
    · have h1 : 1 * l ≤ (2 * m - 1) * l := Nat.mul_le_mul_right _ (by omega)
      omega
    · have h1 : 1 * l ≤ (2 * m - 1) * l := Nat.mul_le_mul_right _ (by omega)
      have h2 : 1 * j ≤ r * j := Nat.mul_le_mul_right _ (by omega)
      omega
    · omega
    · have h1 : r * 1 ≤ r * j := Nat.mul_le_mul_left _ hj
      omega
  · intro ⟨i, j, u, v⟩ hr
    simp only [setB, Finset.mem_filter] at hr
    ext <;> dsimp only <;> try omega
  · intro ⟨m, l, r, j⟩ hr
    simp only [setZeven, Finset.mem_filter] at hr
    ext <;> dsimp only <;> try omega
  · intro ⟨i, j, u, v⟩ _
    dsimp only [sgn34, sgn13]
    apply sgn_eq_of_mod
    omega

-- Split BB1 = B ⊔ B1
private lemma sum_setBB1_eq (N : ℕ) :
    ∑ r ∈ setBB1 N, sgn34 r = (∑ r ∈ setB N, sgn34 r) + (∑ r ∈ setB1 N, sgn34 r) := by
  have hunion : setBB1 N = setB N ∪ setB1 N := by
    ext ⟨i, j, u, v⟩
    simp only [setBB1, setB, setB1, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro ⟨hb, hdeg⟩
      by_cases hlt : i < j
      · exact Or.inl ⟨hb, hlt, hdeg⟩
      · exact Or.inr ⟨hb, by omega, hdeg⟩
    · rintro (⟨hb, _, hdeg⟩ | ⟨hb, _, hdeg⟩)
      · exact ⟨hb, hdeg⟩
      · exact ⟨hb, hdeg⟩
  have hdisj : Disjoint (setB N) (setB1 N) := by
    rw [Finset.disjoint_left]
    intro ⟨i, j, u, v⟩ h1 h2
    simp only [setB, setB1, Finset.mem_filter] at h1 h2
    omega
  rw [hunion, Finset.sum_union hdisj]

-- Bijection 3: B1 <-> A (for even N, signs agree!)
private lemma sum_setB1_eq_sum_setA_even (k : ℕ) :
    ∑ r ∈ setB1 (2 * k), sgn34 r = ∑ r ∈ setA (2 * k), sgn34 r := by
  refine Finset.sum_nbij'
    (fun r => (r.2.2.1, r.2.2.1 + r.2.2.2 + 1, r.1 - r.2.1, r.2.1))
    (fun r => (r.2.2.1 + r.2.2.2, r.2.2.2, r.1, r.2.1 - r.1 - 1))
    ?_ ?_ ?_ ?_ ?_
  · intro ⟨i, j, u, v⟩ hr
    simp only [setB1, setA, Finset.mem_filter] at hr ⊢
    rcases hr with ⟨_, hji, hdeg⟩
    have hEq :
        (u + v + 1) + 1 + (2 * u + 1) * (i - j) + (2 * (u + v + 1) + 1) * j = 2 * k := by
      zify [hji] at hdeg ⊢
      linarith
    refine ⟨mem_box ?_ ?_ ?_ ?_, by omega, hEq⟩
    · have h1 : 1 * u ≤ (2 * i + 1) * u := Nat.mul_le_mul_right _ (by omega)
      omega
    · have h1 : 1 * u ≤ (2 * i + 1) * u := Nat.mul_le_mul_right _ (by omega)
      have h2 : 1 * v ≤ (2 * j + 1) * v := Nat.mul_le_mul_right _ (by omega)
      omega
    · omega
    · omega
  · intro ⟨i, j, u, v⟩ hr
    simp only [setB1, setA, Finset.mem_filter] at hr ⊢
    rcases hr with ⟨_, hij, hdeg⟩
    have hEq :
        (u + v) + 2 * v + 2 + (2 * (u + v) + 1) * i + (2 * v + 1) * (j - i - 1) = 2 * k := by
      have h1 : i + 1 ≤ j := by omega
      zify [h1] at hdeg ⊢
      have hsub : ((j - i - 1 : ℕ) : ℤ) = (j : ℤ) - (i : ℤ) - 1 := by omega
      rw [hsub]
      linarith
    refine ⟨mem_box ?_ ?_ ?_ ?_, by omega, hEq⟩
    · have h1 : 1 * u ≤ (2 * i + 1) * u := Nat.mul_le_mul_right _ (by omega)
      have h2 : 1 * v ≤ (2 * j + 1) * v := Nat.mul_le_mul_right _ (by omega)
      omega
    · have h2 : 1 * v ≤ (2 * j + 1) * v := Nat.mul_le_mul_right _ (by omega)
      omega
    · omega
    · omega
  · intro ⟨i, j, u, v⟩ hr
    simp only [setB1, Finset.mem_filter] at hr
    ext <;> dsimp only <;> try omega
  · intro ⟨i, j, u, v⟩ hr
    simp only [setA, Finset.mem_filter] at hr
    ext <;> dsimp only <;> try omega
  · intro ⟨i, j, u, v⟩ hr
    simp only [setB1, Finset.mem_filter] at hr
    rcases hr with ⟨_, hji, hdeg⟩
    dsimp only [sgn34]
    apply sgn_eq_of_mod
    have hpar : (i + 2 * j + 2 + (2 * i + 1) * u + (2 * j + 1) * v) % 2 = 0 := by omega
    have hmod1 : ((2 * i + 1) * u) % 2 = u % 2 := by
      have : (2 * i + 1) * u = 2 * (i * u) + u := by ring
      omega
    have hmod2 : ((2 * j + 1) * v) % 2 = v % 2 := by
      have : (2 * j + 1) * v = 2 * (j * v) + v := by ring
      omega
    omega

-- Bijection 4: BB1 <-> D2
private lemma sum_setBB1_eq_sum_setD2 (N : ℕ) :
    ∑ r ∈ setBB1 N, sgn34 r = ∑ r ∈ setD2 N, sgn13 r := by
  refine Finset.sum_nbij'
    (fun r => (r.2.2.1 + 1, r.1, r.2.2.2 + 1, 2 * r.2.1 + 1))
    (fun r => (r.2.1, r.2.2.2 / 2, r.1 - 1, r.2.2.1 - 1))
    ?_ ?_ ?_ ?_ ?_
  · intro ⟨i, j, u, v⟩ hr
    simp only [setBB1, setD2, Finset.mem_filter] at hr ⊢
    rcases hr with ⟨_, hdeg⟩
    have hEq :
        (u + 1) + (2 * (u + 1) - 1) * i + (v + 1) * (2 * j + 1) = N := by
      have hsub : 1 ≤ 2 * (u + 1) := by omega
      zify [hsub] at hdeg ⊢
      linarith
    refine ⟨mem_box ?_ ?_ ?_ ?_, by omega, by omega, by omega, by omega, hEq⟩
    · have h1 : 1 * u ≤ (2 * i + 1) * u := Nat.mul_le_mul_right _ (by omega)
      omega
    · omega
    · have h1 : (v + 1) * 1 ≤ (v + 1) * (2 * j + 1) := Nat.mul_le_mul_left _ (by omega)
      omega
    · omega
  · intro ⟨m, l, r, j⟩ hr
    simp only [setBB1, setD2, Finset.mem_filter] at hr ⊢
    rcases hr with ⟨_, hm, hrg, hj, hodd, hdeg⟩
    set q := j / 2
    have hj_eq : j = 2 * q + 1 := by omega
    have h2m : 1 ≤ 2 * m := by omega
    have hEq :
        l + 2 * q + 2 + (2 * l + 1) * (m - 1) + (2 * q + 1) * (r - 1) = N := by
      have hdeg' : ((m + (2 * m - 1) * l + r * (2 * q + 1) : ℕ) : ℤ) = (N : ℤ) := by
        exact_mod_cast (hj_eq ▸ hdeg)
      zify [hm, hrg, h2m] at hdeg' ⊢
      linarith
    refine ⟨mem_box ?_ ?_ ?_ ?_, hEq⟩
    · have h1 : 1 * l ≤ (2 * m - 1) * l := Nat.mul_le_mul_right _ (by omega)
      omega
    · have h1 : 1 * j ≤ r * j := Nat.mul_le_mul_right _ hrg
      omega
    · omega
    · have h1 : r * 1 ≤ r * j := Nat.mul_le_mul_left _ hj
      omega
  · intro ⟨i, j, u, v⟩ _
    ext <;> dsimp only <;> try omega
  · intro ⟨m, l, r, j⟩ hr
    simp only [setD2, Finset.mem_filter] at hr
    ext <;> dsimp only <;> try omega
  · intro ⟨i, j, u, v⟩ _
    dsimp only [sgn34, sgn13]
    apply sgn_eq_of_mod
    omega

-- Split D1 = D2 ⊔ Ddiff
private lemma sum_setD1_eq_D2_add_Ddiff (N : ℕ) :
    ∑ r ∈ setD1 N, sgn13 r = (∑ r ∈ setD2 N, sgn13 r) + (∑ r ∈ setDdiff N, sgn13 r) := by
  have hunion : setD1 N = setD2 N ∪ setDdiff N := by
    ext ⟨m, l, r, j⟩
    simp only [setD1, setD2, setDdiff, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro ⟨hb, hm, hr, hj, hdeg⟩
      rcases Nat.mod_two_eq_zero_or_one j with h0 | h1
      · exact Or.inr ⟨hb, hm, hr, hj, h0, hdeg⟩
      · exact Or.inl ⟨hb, hm, hr, hj, h1, hdeg⟩
    · rintro (⟨hb, hm, hr, hj, _, hdeg⟩ | ⟨hb, hm, hr, hj, _, hdeg⟩)
      · exact ⟨hb, hm, hr, hj, hdeg⟩
      · exact ⟨hb, hm, hr, hj, hdeg⟩
  have hdisj : Disjoint (setD2 N) (setDdiff N) := by
    rw [Finset.disjoint_left]
    intro ⟨m, l, r, j⟩ h1 h2
    simp only [setD2, setDdiff, Finset.mem_filter] at h1 h2
    omega
  rw [hunion, Finset.sum_union hdisj]

-- Step 5: Sign-reversing involution on Ddiff(2*k): (m, l, r, j) |-> (l + 1, m - 1, r, j)
private lemma sum_setDdiff_even_eq_zero (k : ℕ) :
    ∑ r ∈ setDdiff (2 * k), sgn13 r = 0 := by
  refine sum_eq_zero_of_involution (setDdiff (2 * k)) sgn13
    (fun r => (r.2.1 + 1, r.1 - 1, r.2.2.1, r.2.2.2)) ?_ ?_ ?_
  · intro ⟨m, l, r, j⟩ hr
    simp only [setDdiff, Finset.mem_filter] at hr ⊢
    rcases hr with ⟨_, hm, hrg, hj, heven, hdeg⟩
    have hEq : (l + 1) + (2 * (l + 1) - 1) * (m - 1) + r * j = 2 * k := by
      have h1 : 1 ≤ 2 * (l + 1) := by omega
      have h2m : 1 ≤ 2 * m := by omega
      zify [hm, h1, h2m] at hdeg ⊢
      linarith
    refine ⟨mem_box ?_ ?_ ?_ ?_, by omega, hrg, hj, heven, hEq⟩
    · have h1 : 1 * l ≤ (2 * m - 1) * l := Nat.mul_le_mul_right _ (by omega)
      omega
    · omega
    · have h1 : r * 1 ≤ r * j := Nat.mul_le_mul_left _ hj
      omega
    · have h1 : 1 * j ≤ r * j := Nat.mul_le_mul_right _ hrg
      omega
  · intro ⟨m, l, r, j⟩ hr
    simp only [setDdiff, Finset.mem_filter] at hr
    ext <;> dsimp only <;> try omega
  · intro ⟨m, l, r, j⟩ hr
    simp only [setDdiff, Finset.mem_filter] at hr
    rcases hr with ⟨_, hm, _, _, heven, hdeg⟩
    dsimp only [sgn13]
    apply sgn_neg_of_mod
    have hrj_even : (r * j) % 2 = 0 := by
      set q := j / 2
      have hjeq : j = 2 * q := by omega
      have hmul : r * j = 2 * (r * q) := by rw [hjeq]; ring
      omega
    have hml_even : (m + (2 * m - 1) * l) % 2 = 0 := by omega
    have hmod_ml : ((2 * m - 1) * l) % 2 = l % 2 := by
      have hsub : 2 * m - 1 = 2 * (m - 1) + 1 := by omega
      have hmul : (2 * m - 1) * l = 2 * ((m - 1) * l) + l := by rw [hsub]; ring
      omega
    omega

end OMA.P_oeis_a350583

open OMA.P_oeis_a350583 in
theorem OMA.solution : type_of% @OMA.S_oeis_a350583.main := by
  intro k
  rw [geometricCoefficient_eq_sum_setY, sum_setY_eq_sum_setY2]
  have hD1 := sum_setD1_eq (2 * k)
  have hZ := sum_setZ_eq (2 * k)
  have hA := sum_setA_eq_sum_setZodd (2 * k)
  have hB := sum_setB_eq_sum_setZeven (2 * k)
  have hBB1 := sum_setBB1_eq (2 * k)
  have hB1 := sum_setB1_eq_sum_setA_even k
  have hD2 := sum_setBB1_eq_sum_setD2 (2 * k)
  have hDdiff_split := sum_setD1_eq_D2_add_Ddiff (2 * k)
  have hDdiff_zero := sum_setDdiff_even_eq_zero k
  linarith
