import OMAStatements.S_oeis_a195279

namespace OMA.S_oeis_a195279

open PowerSeries




theorem good_iff (n : ℕ) (x : Fin 3 → Fin 3 → ℤ) : good n x ↔
    (x 0 1 = 0 ∧ x 0 2 = 0 ∧ x 1 2 = 0) ∧
    |x 0 0 - x 1 0| ≤ n ∧ |x 1 0 - x 2 0| ≤ n ∧ |x 1 1 - x 2 1| ≤ n ∧
    |x 1 0 - x 1 1| ≤ n ∧ |x 2 0 - x 2 1| ≤ n ∧ |x 2 1 - x 2 2| ≤ n := by
  unfold good nbr
  constructor
  · rintro ⟨hu, hn⟩
    exact ⟨⟨hu 0 1 (by decide), hu 0 2 (by decide), hu 1 2 (by decide)⟩, hn 0 0 1 0 (by decide),
      hn 1 0 2 0 (by decide), hn 1 1 2 1 (by decide), hn 1 0 1 1 (by decide), hn 2 0 2 1 (by decide),
      hn 2 1 2 2 (by decide)⟩
  · rintro ⟨⟨h01, h02, h12⟩, e1, e2, e3, e4, e5, e6⟩
    refine ⟨fun i j hij => ?_, fun i j i' j' h => ?_⟩
    · fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | assumption
    · fin_cases i <;> fin_cases j <;> fin_cases i' <;> fin_cases j' <;>
        first | exact absurd h (by decide) | assumption | (rw [abs_sub_comm]; assumption)

/-- The triangle with top 0 and steps k - n along the tree edges: k1 from (0,0) to (1,0), k2 from
(1,0) to (2,0), k3 from (1,0) to (1,1), k4 from (2,0) to (2,1), k5 from (2,1) to (2,2). The tuple
is (k1, k5, k2, k3, k4). -/
def φ (n : ℕ) (k : ℕ × ℕ × ℕ × ℕ × ℕ) : Fin 3 → Fin 3 → ℤ :=
  ![![0, 0, 0],
    ![(k.1 : ℤ) - n, ((k.1 : ℤ) - n) + ((k.2.2.2.1 : ℤ) - n), 0],
    ![((k.1 : ℤ) - n) + ((k.2.2.1 : ℤ) - n),
      ((k.1 : ℤ) - n) + ((k.2.2.1 : ℤ) - n) + ((k.2.2.2.2 : ℤ) - n),
      ((k.1 : ℤ) - n) + ((k.2.2.1 : ℤ) - n) + ((k.2.2.2.2 : ℤ) - n) + ((k.2.1 : ℤ) - n)]]

/-- The triples (p, q, r) in [0, m]^3 with q ≤ p + r ≤ q + m. -/
def Tri (m : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.range (m + 1) ×ˢ Finset.range (m + 1) ×ˢ Finset.range (m + 1)).filter
    fun t => t.2.1 ≤ t.1 + t.2.2 ∧ t.1 + t.2.2 ≤ t.2.1 + m

/-- The step tuples of the triangles. -/
def Steps (n : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ × ℕ) :=
  Finset.range (2 * n + 1) ×ˢ Finset.range (2 * n + 1) ×ˢ Tri (2 * n)

theorem φ_inj (n : ℕ) : Function.Injective (φ n) := by
  rintro ⟨k1, k5, k2, k3, k4⟩ ⟨l1, l5, l2, l3, l4⟩ h
  have e10 := congrFun (congrFun h 1) 0
  have e11 := congrFun (congrFun h 1) 1
  have e20 := congrFun (congrFun h 2) 0
  have e21 := congrFun (congrFun h 2) 1
  have e22 := congrFun (congrFun h 2) 2
  simp only [φ, Matrix.cons_val] at e10 e11 e20 e21 e22
  simp only [Prod.mk.injEq]
  omega

theorem ext9 {x y : Fin 3 → Fin 3 → ℤ} (h00 : x 0 0 = y 0 0) (h01 : x 0 1 = y 0 1)
    (h02 : x 0 2 = y 0 2) (h10 : x 1 0 = y 1 0) (h11 : x 1 1 = y 1 1) (h12 : x 1 2 = y 1 2)
    (h20 : x 2 0 = y 2 0) (h21 : x 2 1 = y 2 1) (h22 : x 2 2 = y 2 2) : x = y := by
  funext i j
  fin_cases i <;> fin_cases j <;> assumption

theorem set_eq (n : ℕ) :
    {x : Fin 3 → Fin 3 → ℤ | good n x ∧ x 0 0 = 0} = φ n '' (Steps n : Set _) := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_image, Finset.mem_coe, Steps, Tri, Finset.mem_product,
    Finset.mem_filter, Finset.mem_range, Prod.exists]
  rw [good_iff]
  constructor
  · rintro ⟨⟨⟨h01, h02, h12⟩, e1, e2, e3, e4, e5, e6⟩, h00⟩
    rw [abs_le] at e1 e2 e3 e4 e5 e6
    obtain ⟨k1, hk1⟩ : ∃ k : ℕ, (k : ℤ) = x 1 0 - x 0 0 + n := ⟨_, Int.toNat_of_nonneg (by omega)⟩
    obtain ⟨k5, hk5⟩ : ∃ k : ℕ, (k : ℤ) = x 2 2 - x 2 1 + n := ⟨_, Int.toNat_of_nonneg (by omega)⟩
    obtain ⟨k2, hk2⟩ : ∃ k : ℕ, (k : ℤ) = x 2 0 - x 1 0 + n := ⟨_, Int.toNat_of_nonneg (by omega)⟩
    obtain ⟨k3, hk3⟩ : ∃ k : ℕ, (k : ℤ) = x 1 1 - x 1 0 + n := ⟨_, Int.toNat_of_nonneg (by omega)⟩
    obtain ⟨k4, hk4⟩ : ∃ k : ℕ, (k : ℤ) = x 2 1 - x 2 0 + n := ⟨_, Int.toNat_of_nonneg (by omega)⟩
    refine ⟨k1, k5, k2, k3, k4, ⟨by omega, by omega, ⟨by omega, by omega, by omega⟩, by omega,
      by omega⟩, ?_⟩
    refine ext9 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp only [φ, Matrix.cons_val] <;> omega
  · rintro ⟨k1, k5, k2, k3, k4, ⟨hk1, hk5, ⟨hk2, hk3, hk4⟩, c1, c2⟩, rfl⟩
    refine ⟨⟨⟨rfl, rfl, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl⟩ <;> simp only [φ, Matrix.cons_val] <;>
      rw [abs_le] <;> constructor <;> omega

theorem a_eq (n : ℕ) : a n = (Steps n).card := by
  unfold a
  rw [set_eq, Set.ncard_image_of_injective _ (φ_inj n), Set.ncard_coe_finset]

theorem card_steps (n : ℕ) : (Steps n).card = (2 * n + 1) ^ 2 * (Tri (2 * n)).card := by
  unfold Steps
  rw [Finset.card_product, Finset.card_product, Finset.card_range]
  ring

/-- Gauss's sum, reflected. -/
theorem L1 (q : ℕ) : (∑ p ∈ Finset.range (q + 1), (q - p)) * 2 = q * (q + 1) := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Finset.sum_range_succ, Nat.sub_self, add_zero]
    have : ∑ p ∈ Finset.range (q + 1), (q + 1 - p) = ∑ p ∈ Finset.range (q + 1), ((q - p) + 1) := by
      refine Finset.sum_congr rfl (fun p hp => ?_)
      rw [Finset.mem_range] at hp
      omega
    rw [this, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one,
      add_mul, ih]
    ring

theorem L2 (m : ℕ) : (∑ q ∈ Finset.range (m + 1), q * (q + 1)) * 3 = m * (m + 1) * (m + 2) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, add_mul, ih]
    ring

/-- The triples with p + r < q. -/
def B1 (m : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.range (m + 1) ×ˢ Finset.range (m + 1) ×ˢ Finset.range (m + 1)).filter
    fun t => t.1 + t.2.2 < t.2.1

/-- The triples with p + r > q + m. -/
def B2 (m : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.range (m + 1) ×ˢ Finset.range (m + 1) ×ˢ Finset.range (m + 1)).filter
    fun t => t.2.1 + m < t.1 + t.2.2

theorem card_split (m : ℕ) : (Tri m).card + (B1 m).card + (B2 m).card = (m + 1) ^ 3 := by
  have hc : (Finset.range (m + 1) ×ˢ Finset.range (m + 1) ×ˢ Finset.range (m + 1)).card =
      (m + 1) ^ 3 := by
    rw [Finset.card_product, Finset.card_product, Finset.card_range]
    ring
  rw [← hc]
  unfold Tri B1 B2
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, Finset.card_eq_sum_ones]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  split_ifs <;> omega

theorem card_B2 (m : ℕ) : (B2 m).card = (B1 m).card := by
  unfold B1 B2
  apply Finset.card_nbij' (fun t => (m - t.1, m - t.2.1, m - t.2.2))
    (fun t => (m - t.1, m - t.2.1, m - t.2.2))
  · rintro ⟨p, q, r⟩ ht
    simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_range, Set.mem_setOf_eq] at ht ⊢
    omega
  · rintro ⟨p, q, r⟩ ht
    simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_range, Set.mem_setOf_eq] at ht ⊢
    omega
  · rintro ⟨p, q, r⟩ ht
    simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_range, Set.mem_setOf_eq] at ht
    simp only [Prod.mk.injEq]
    omega
  · rintro ⟨p, q, r⟩ ht
    simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_range, Set.mem_setOf_eq] at ht
    simp only [Prod.mk.injEq]
    omega

theorem card_B1 (m : ℕ) : (B1 m).card * 6 = m * (m + 1) * (m + 2) := by
  have inner : ∀ q ∈ Finset.range (m + 1), ∀ p ∈ Finset.range (m + 1),
      (∑ r ∈ Finset.range (m + 1), if p + r < q then 1 else 0) = q - p := by
    intro q hq p _
    rw [Finset.mem_range] at hq
    rw [← Finset.card_filter]
    have : (Finset.range (m + 1)).filter (fun r => p + r < q) = Finset.range (q - p) := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    rw [this, Finset.card_range]
  have mid : ∀ q ∈ Finset.range (m + 1),
      (∑ p ∈ Finset.range (m + 1), ∑ r ∈ Finset.range (m + 1), if p + r < q then 1 else 0) * 2 =
        q * (q + 1) := by
    intro q hq
    rw [Finset.sum_congr rfl (inner q hq)]
    rw [Finset.mem_range] at hq
    have hs : ∑ p ∈ Finset.range (m + 1), (q - p) = ∑ p ∈ Finset.range (q + 1), (q - p) := by
      symm
      apply Finset.sum_subset
      · exact Finset.range_subset_range.2 (by omega)
      · intro p _ hp
        rw [Finset.mem_range] at hp
        omega
    rw [hs]
    exact L1 q
  have hB : (B1 m).card = ∑ p ∈ Finset.range (m + 1), ∑ q ∈ Finset.range (m + 1),
      ∑ r ∈ Finset.range (m + 1), if p + r < q then 1 else 0 := by
    unfold B1
    rw [Finset.card_filter]
    simp only [Finset.sum_product]
  rw [hB, Finset.sum_comm, ← L2 m, ← Finset.sum_congr rfl mid, ← Finset.sum_mul]
  ring

theorem card_tri (m : ℕ) : (Tri m).card * 3 + m * (m + 1) * (m + 2) = 3 * (m + 1) ^ 3 := by
  have h1 := card_split m
  have h2 := card_B2 m
  have h3 := card_B1 m
  omega

/-- The closed form 3 a(n) = (2n+1)^3 (8n^2 + 8n + 3). -/
theorem a_closed (n : ℕ) : 3 * (a n : ℤ) = (2 * n + 1) ^ 3 * (8 * n ^ 2 + 8 * n + 3) := by
  have h1 : (a n : ℤ) = (2 * n + 1) ^ 2 * (Tri (2 * n)).card := by
    rw [a_eq, card_steps]
    push_cast
    ring
  have h2 : ((Tri (2 * n)).card : ℤ) * 3 + (2 * n) * (2 * n + 1) * (2 * n + 2) =
      3 * (2 * n + 1) ^ 3 := by
    exact_mod_cast card_tri (2 * n)
  linear_combination 3 * h1 + (2 * (n : ℤ) + 1) ^ 2 * h2

/-- Barker's recurrence, for n > 6. -/
theorem recurrence (n : ℕ) (hn : 6 < n) :
    (a n : ℤ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) - 15 * a (n - 4) +
      6 * a (n - 5) - a (n - 6) := by
  obtain ⟨q, rfl⟩ : ∃ q, n = q + 6 := ⟨n - 6, by omega⟩
  simp only [show q + 6 - 1 = q + 5 by omega, show q + 6 - 2 = q + 4 by omega,
    show q + 6 - 3 = q + 3 by omega, show q + 6 - 4 = q + 2 by omega, show q + 6 - 5 = q + 1 by omega,
    show q + 6 - 6 = q by omega]
  have h0 := a_closed q
  have h1 := a_closed (q + 1)
  have h2 := a_closed (q + 2)
  have h3 := a_closed (q + 3)
  have h4 := a_closed (q + 4)
  have h5 := a_closed (q + 5)
  have h6 := a_closed (q + 6)
  push_cast at h0 h1 h2 h3 h4 h5 h6
  have key : 3 * ((a (q + 6) : ℤ) - (6 * a (q + 5) - 15 * a (q + 4) + 20 * a (q + 3) -
      15 * a (q + 2) + 6 * a (q + 1) - a q)) = 0 := by
    linear_combination h6 - 6 * h5 + 15 * h4 - 20 * h3 + 15 * h2 - 6 * h1 + h0
  omega

theorem val (n v : ℕ) (h : (2 * n + 1) ^ 3 * (8 * n ^ 2 + 8 * n + 3) = 3 * v) : a n = v := by
  have h1 := a_closed n
  have h2 : ((2 * n + 1) ^ 3 * (8 * n ^ 2 + 8 * n + 3) : ℤ) = 3 * v := by exact_mod_cast h
  omega

/-- Barker's g.f., as A(x) (1 - x)^6 = x (171 + 1099x + 1134x^2 + 150x^3 + 7x^4 - x^5) in Z[[x]],
with A(x) = Sum_{n >= 1} a(n) x^n. -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 6 =
    X * (171 + 1099 * X + 1134 * X ^ 2 + 150 * X ^ 3 + 7 * X ^ 4 - X ^ 5) := by
  set A : ℤ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) with hA
  have e1 : A * (1 - X) ^ 6 = A - C 6 * (A * X ^ 1) + C 15 * (A * X ^ 2) - C 20 * (A * X ^ 3) +
      C 15 * (A * X ^ 4) - C 6 * (A * X ^ 5) + A * X ^ 6 := by
    simp only [map_ofNat]; ring
  have e2 : (X * (171 + 1099 * X + 1134 * X ^ 2 + 150 * X ^ 3 + 7 * X ^ 4 - X ^ 5) : ℤ⟦X⟧) =
      X ^ 1 * C 171 + X ^ 2 * C 1099 + X ^ 3 * C 1134 + X ^ 4 * C 150 + X ^ 5 * C 7 - X ^ 6 := by
    simp only [map_ofNat]; ring
  rw [e1, e2]
  ext n
  have hc : ∀ k, coeff k A = if k = 0 then (0 : ℤ) else a k := fun k => by rw [hA, coeff_mk]
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_C, coeff_X_pow, coeff_mul_X_pow', hc]
  have v1 : a 1 = 171 := val 1 171 (by norm_num)
  have v2 : a 2 = 2125 := val 2 2125 (by norm_num)
  have v3 : a 3 = 11319 := val 3 11319 (by norm_num)
  have v4 : a 4 = 39609 := val 4 39609 (by norm_num)
  have v5 : a 5 = 107811 := val 5 107811 (by norm_num)
  have v6 : a 6 = 248261 := val 6 248261 (by norm_num)
  rcases Nat.lt_or_ge n 7 with hn | hn
  · interval_cases n <;> simp [v1, v2, v3, v4, v5, v6]
  · obtain ⟨q, rfl⟩ : ∃ q, n = q + 7 := ⟨n - 7, by omega⟩
    have h := recurrence (q + 7) (by omega)
    simp only [show q + 7 - 1 = q + 6 by omega, show q + 7 - 2 = q + 5 by omega,
      show q + 7 - 3 = q + 4 by omega, show q + 7 - 4 = q + 3 by omega,
      show q + 7 - 5 = q + 2 by omega, show q + 7 - 6 = q + 1 by omega] at h ⊢
    simp only [show ¬ q + 7 = 0 by omega, show ¬ q + 6 = 0 by omega, show ¬ q + 5 = 0 by omega,
      show ¬ q + 4 = 0 by omega, show ¬ q + 3 = 0 by omega, show ¬ q + 2 = 0 by omega,
      show ¬ q + 1 = 0 by omega, show 1 ≤ q + 7 by omega, show 2 ≤ q + 7 by omega,
      show 3 ≤ q + 7 by omega, show 4 ≤ q + 7 by omega, show 5 ≤ q + 7 by omega,
      show 6 ≤ q + 7 by omega, show ¬ q + 7 = 1 by omega, show ¬ q + 7 = 2 by omega,
      show ¬ q + 7 = 3 by omega, show ¬ q + 7 = 4 by omega, show ¬ q + 7 = 5 by omega,
      show ¬ q + 7 = 6 by omega, if_true, if_false]
    rw [h]
    ring

/-- Controls: the entry's data a(1..25). -/
theorem controls : a 1 = 171 ∧ a 2 = 2125 ∧ a 3 = 11319 ∧ a 4 = 39609 ∧ a 5 = 107811 ∧
    a 6 = 248261 ∧ a 7 = 507375 ∧ a 8 = 948209 ∧ a 9 = 1653019 ∧ a 10 = 2725821 ∧
    a 11 = 4294951 ∧ a 12 = 6515625 ∧ a 13 = 9572499 ∧ a 14 = 13682229 ∧ a 15 = 19096031 ∧
    a 16 = 26102241 ∧ a 17 = 35028875 ∧ a 18 = 46246189 ∧ a 19 = 60169239 ∧ a 20 = 77260441 ∧
    a 21 = 98032131 ∧ a 22 = 123049125 ∧ a 23 = 152931279 ∧ a 24 = 188356049 ∧
    a 25 = 230061051 :=
  ⟨val 1 _ (by norm_num), val 2 _ (by norm_num), val 3 _ (by norm_num), val 4 _ (by norm_num),
    val 5 _ (by norm_num), val 6 _ (by norm_num), val 7 _ (by norm_num), val 8 _ (by norm_num),
    val 9 _ (by norm_num), val 10 _ (by norm_num), val 11 _ (by norm_num), val 12 _ (by norm_num),
    val 13 _ (by norm_num), val 14 _ (by norm_num), val 15 _ (by norm_num), val 16 _ (by norm_num),
    val 17 _ (by norm_num), val 18 _ (by norm_num), val 19 _ (by norm_num), val 20 _ (by norm_num),
    val 21 _ (by norm_num), val 22 _ (by norm_num), val 23 _ (by norm_num), val 24 _ (by norm_num),
    val 25 _ (by norm_num)⟩

/-- Both of Barker's conjectures. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 6 =
      X * (171 + 1099 * X + 1134 * X ^ 2 + 150 * X ^ 3 + 7 * X ^ 4 - X ^ 5) ∧
    ∀ n : ℕ, 6 < n → (a n : ℤ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) -
      15 * a (n - 4) + 6 * a (n - 5) - a (n - 6) :=
  ⟨gf, recurrence⟩

end OMA.S_oeis_a195279

theorem OMA.solution : type_of% @OMA.S_oeis_a195279.main :=
  OMA.S_oeis_a195279.conjecture
