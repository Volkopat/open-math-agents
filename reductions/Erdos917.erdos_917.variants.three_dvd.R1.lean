import FormalConjectures.ErdosProblems.«917»

/-!
Reduction R1 of the remaining case of Erdős Problem 917: for `k = 3t ≥ 6`,
`f_k(n) ~ (1/2)(1 - 1/t) n^2`.
Credit: @sntntHb

The lower half holds for EVERY large `n` (not only for the special `n` of Erdős' remark):
* if `n - t x` is even, join `t` odd cycles of lengths `x, ..., x, x + d`;
* if it is odd, take the Hajós sum of the `6`-critical graph `C_x ∨ C_(x+d-5)` with `K_6`
  (this adds `5` vertices and `14` edges and flips the parity), then join `t - 2` cycles `C_x`.
Here `x` is odd and about `n / t`, and `d = n - t x` is bounded by `3t`. Counting only the edges
between blocks gives `2t f_k(n) ≥ (t - 1) n^2 - 10 n - 9 t^3`.

So the asymptotic reduces to four statements:
* `H1`: odd cycles are `3`-critical (the same statement as `lower_construction.R1.H1`);
* `H2`: Dirac's join of a `k₁`-critical and a `k₂`-critical graph is `(k₁ + k₂)`-critical
  (the same statement as `lower_construction.R1.H2`);
* `H3`: the Hajós sum of a `6`-critical graph with `K_6` is `6`-critical;
* `H4`: the upper bound `f_k(n) ≤ (1 + ε) (1/2)(1 - 1/t) n^2` for large `n`: the genuinely open part
  (for `k = 6` this is the upper half of `erdos_917.parts.ii`).
-/

namespace OMA.R_Erdos917_erdos_917_variants_three_dvd_R1

open Filter Asymptotics

/-- Odd cycles are `3`-critical: `C_b` has `b` vertices and `b` edges. -/
def H1 : Prop := ∀ b : ℕ, Odd b → 3 ≤ b → (∃ G : SimpleGraph (Fin (b)), Erdos917.IsKCritical G (3) ∧ G.edgeSet.ncard = (b))

/-- Dirac's join: the join of a `k₁`-critical and a `k₂`-critical graph is `(k₁ + k₂)`-critical. -/
def H2 : Prop := ∀ k₁ k₂ n₁ n₂ e₁ e₂ : ℕ, 3 ≤ k₁ → 3 ≤ k₂ → (∃ G : SimpleGraph (Fin (n₁)), Erdos917.IsKCritical G (k₁) ∧ G.edgeSet.ncard = (e₁)) → (∃ G : SimpleGraph (Fin (n₂)), Erdos917.IsKCritical G (k₂) ∧ G.edgeSet.ncard = (e₂)) →
  (∃ G : SimpleGraph (Fin (n₁ + n₂)), Erdos917.IsKCritical G (k₁ + k₂) ∧ G.edgeSet.ncard = (e₁ + e₂ + n₁ * n₂))

/-- Hajós sum with `K_6`: delete an edge `xy` of a `6`-critical graph `G` and an edge `uv` of `K_6`,
identify `x` with `u` and add the edge `yv`. The result is `6`-critical, with `5` more vertices and
`14` more edges. -/
def H3 : Prop := ∀ n e : ℕ, (∃ G : SimpleGraph (Fin n), Erdos917.IsKCritical G 6 ∧ G.edgeSet.ncard = e) →
  (∃ G : SimpleGraph (Fin (n + 5)), Erdos917.IsKCritical G 6 ∧ G.edgeSet.ncard = e + 14)

/-- The open part: the conjectured value is asymptotically an upper bound when `3 ∣ k`. -/
def H4 : Prop := ∀ k : ℕ, 6 ≤ k → 3 ∣ k → ∀ ε : ℝ, 0 < ε →
  ∀ᶠ n : ℕ in atTop, (Erdos917.f k n : ℝ) ≤ (1 + ε) * Erdos917.conjecturedValue k n

/-- Joining `r` further odd cycles `C_b` to a `k₀`-critical graph. -/
lemma iter (h1 : H1) (h2 : H2) {b : ℕ} (hb : Odd b) (hb3 : 3 ≤ b) {k₀ a e : ℕ} (hk₀ : 3 ≤ k₀)
    (h : (∃ G : SimpleGraph (Fin (a)), Erdos917.IsKCritical G (k₀) ∧ G.edgeSet.ncard = (e))) :
    ∀ r : ℕ, ∃ E : ℕ,
      (∃ G : SimpleGraph (Fin (a + r * b)), Erdos917.IsKCritical G (k₀ + 3 * r) ∧
        G.edgeSet.ncard = (E)) ∧
      2 * E + r * b ^ 2 = 2 * e + 2 * r * b + 2 * a * r * b + r ^ 2 * b ^ 2 := by
  intro r
  induction r with
  | zero =>
    refine ⟨e, ?_, by ring⟩
    have h' : a + 0 * b = a := by simp
    have h2 : k₀ + 3 * 0 = k₀ := by simp
    rw [h', h2]
    exact h
  | succ r ih =>
    obtain ⟨E, hE, hE2⟩ := ih
    have hj := h2 (k₀ + 3 * r) 3 (a + r * b) b E b (by omega) le_rfl hE (h1 b hb hb3)
    refine ⟨E + b + (a + r * b) * b, ?_, ?_⟩
    · have e1 : k₀ + 3 * (r + 1) = k₀ + 3 * r + 3 := by ring
      have e2 : a + (r + 1) * b = a + r * b + b := by ring
      rw [e1, e2]
      exact hj
    · nlinarith [hE2]

/-- The `6`-critical core on `2x + d` vertices with at least `x (x + d - 5)` edges. -/
lemma core (h1 : H1) (h2 : H2) (h3 : H3) {x d : ℕ} (hx : Odd x) (hx8 : 8 ≤ x) :
    ∃ e : ℕ, (∃ G : SimpleGraph (Fin (2 * x + d)), Erdos917.IsKCritical G 6 ∧
      G.edgeSet.ncard = e) ∧ x * (x + d) ≤ e + 5 * x := by
  have hx3 : 3 ≤ x := by omega
  rcases Nat.even_or_odd d with hd | hd
  · have hc : Odd (x + d) := hx.add_even hd
    have hj := h2 3 3 x (x + d) x (x + d) le_rfl le_rfl (h1 x hx hx3) (h1 (x + d) hc (by omega))
    refine ⟨x + (x + d) + x * (x + d), ?_, by nlinarith⟩
    have e1 : 2 * x + d = x + (x + d) := by ring
    rw [e1]
    exact hj
  · obtain ⟨m, hm⟩ := hd
    -- `c = x + d - 5` is odd
    have hc : Odd (x + 2 * m + 1 - 5) := by
      obtain ⟨y, hy⟩ := hx
      exact ⟨y + m - 2, by omega⟩
    have hj := h2 3 3 x (x + 2 * m + 1 - 5) x (x + 2 * m + 1 - 5) le_rfl le_rfl (h1 x hx hx3)
      (h1 _ hc (by omega))
    have hh := h3 _ _ hj
    refine ⟨x + (x + 2 * m + 1 - 5) + x * (x + 2 * m + 1 - 5) + 14, ?_, ?_⟩
    · have e1 : 2 * x + d = x + (x + 2 * m + 1 - 5) + 5 := by omega
      rw [e1]
      exact hh
    · have e2 : x + 2 * m + 1 - 5 + 5 = x + d := by omega
      have e3 : x * (x + d) = x * (x + 2 * m + 1 - 5) + 5 * x := by
        rw [← e2]; ring
      rw [e3]
      omega

/-- The lower bound `2 t f_k(n) ≥ (t - 1) n^2 - 10 n - 9 t^3` for every large `n`. -/
lemma lower (h1 : H1) (h2 : H2) (h3 : H3) (t : ℕ) (ht : 2 ≤ t) (n : ℕ) (hn : 20 * t ≤ n) :
    ((t : ℝ) - 1) * (n : ℝ) ^ 2 - 10 * n - 9 * (t : ℝ) ^ 3 ≤
      2 * t * (Erdos917.f (3 * t) n : ℝ) := by
  -- `n = 2 t q + s` with `s < 2 t`; take `x = 2 q - 1` and `d = n - t x = s + t`
  set q := n / (2 * t) with hq
  set s := n % (2 * t) with hs
  have hdiv : 2 * t * q + s = n := Nat.div_add_mod n (2 * t)
  have hs2 : s < 2 * t := Nat.mod_lt _ (by omega)
  have hq5 : 5 ≤ q := by
    by_contra hcon
    push Not at hcon
    have : 2 * t * q ≤ 2 * t * 4 := Nat.mul_le_mul_left _ (by omega)
    omega
  set x := 2 * q - 1 with hxdef
  set d := s + t with hddef
  have hx : Odd x := ⟨q - 1, by omega⟩
  have hx8 : 8 ≤ x := by omega
  have hntx : t * x + d = n := by
    have : t * x = 2 * t * q - t := by
      rw [hxdef, Nat.mul_sub, mul_one]; ring_nf
    have h2tq : t ≤ 2 * t * q := by nlinarith
    omega
  obtain ⟨e, hP, he⟩ := core h1 h2 h3 hx hx8 (d := d)
  obtain ⟨r, hr⟩ : ∃ r : ℕ, t = r + 2 := ⟨t - 2, by omega⟩
  obtain ⟨E, hE, hE2⟩ := iter h1 h2 hx (by omega) (by norm_num : 3 ≤ 6) hP r
  have hsize : 2 * x + d + r * x = n := by rw [← hntx, hr]; ring
  have hk : 6 + 3 * r = 3 * t := by omega
  rw [hsize, hk] at hE
  obtain ⟨G, hG, hGE⟩ := hE
  have hfE : (E : ℝ) ≤ (Erdos917.f (3 * t) n : ℝ) := by
    have := Erdos917.edgeSet_ncard_le_f hG
    rw [hGE] at this
    exact_mod_cast this
  -- real arithmetic
  have hE2R : (2 : ℝ) * E + r * x ^ 2 =
      2 * e + 2 * r * x + 2 * (2 * x + d) * r * x + r ^ 2 * x ^ 2 := by exact_mod_cast hE2
  have heR : (x : ℝ) * (x + d) ≤ e + 5 * x := by exact_mod_cast he
  have hnR : (n : ℝ) = t * x + d := by exact_mod_cast hntx.symm
  have htR : (t : ℝ) = r + 2 := by exact_mod_cast hr
  have hdR : (d : ℝ) ≤ 3 * t := by
    have : d ≤ 3 * t := by omega
    exact_mod_cast this
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg x
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  -- `t * 2E - (t - 1) n^2 ≥ -10 t x - (t - 1) d^2`
  have key : ((t : ℝ) - 1) * (n : ℝ) ^ 2 - 10 * t * x - ((t : ℝ) - 1) * d ^ 2 ≤ t * (2 * E) := by
    have h2E : (2 : ℝ) * E ≥ 2 * (x * (x + d) - 5 * x) + 2 * (2 * x + d) * r * x +
        r * (r - 1) * x ^ 2 := by nlinarith [hE2R, heR]
    rw [hnR, htR]
    rw [htR] at ht0
    have hmul := mul_le_mul_of_nonneg_left h2E ht0
    nlinarith [hmul]
  have htx : (t : ℝ) * x ≤ n := by rw [hnR]; linarith
  have hd2 : ((t : ℝ) - 1) * d ^ 2 ≤ 9 * (t : ℝ) ^ 3 := by
    have h1t : (0 : ℝ) ≤ (t : ℝ) - 1 := by
      have : (2 : ℝ) ≤ t := by exact_mod_cast ht
      linarith
    have hdd : (d : ℝ) ^ 2 ≤ 9 * (t : ℝ) ^ 2 := by nlinarith
    nlinarith
  have h10 : 10 * (t : ℝ) * x ≤ 10 * n := by nlinarith
  nlinarith [hfE]

theorem main : H1 → H2 → H3 → H4 → type_of% @Erdos917.erdos_917.variants.three_dvd := by
  intro h1 h2 h3 h4 k hk hk3
  obtain ⟨t, rfl⟩ := hk3
  have ht : 2 ≤ t := by omega
  have htR : (2 : ℝ) ≤ t := by exact_mod_cast ht
  have hcv : ∀ n : ℕ, Erdos917.conjecturedValue (3 * t) n =
      ((t : ℝ) - 1) * (n : ℝ) ^ 2 / (2 * t) := by
    intro n
    have h3t : (3 * t) / 3 = t := by omega
    rw [Erdos917.conjecturedValue, h3t]
    field_simp
  unfold Asymptotics.IsEquivalent
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  -- `n ≥ N` makes the linear error small
  obtain ⟨N, hN⟩ := exists_nat_gt ((20 + 18 * (t : ℝ) ^ 3) / c)
  filter_upwards [h4 (3 * t) hk (dvd_mul_right 3 t) c hc,
    eventually_ge_atTop (max (20 * t) (N + 1))] with n hup hn
  have hn1 : 20 * t ≤ n := le_of_max_le_left hn
  have hn2 : N + 1 ≤ n := le_of_max_le_right hn
  have hlow := lower h1 h2 h3 t ht n hn1
  simp only [Pi.sub_apply]
  rw [hcv n] at hup ⊢
  set F : ℝ := (Erdos917.f (3 * t) n : ℝ) with hF
  set nn : ℝ := (n : ℝ) with hnn
  have ht0 : (0 : ℝ) < t := by linarith
  have hnpos : (1 : ℝ) ≤ nn := by
    have : 1 ≤ n := by omega
    rw [hnn]
    exact_mod_cast this
  have hcv0 : 0 ≤ ((t : ℝ) - 1) * nn ^ 2 / (2 * t) := by
    apply div_nonneg _ (by positivity)
    apply mul_nonneg (by linarith) (by positivity)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hcv0, abs_le]
  have hNn : ((N : ℝ) + 1) ≤ nn := by
    have : N + 1 ≤ n := hn2
    rw [hnn]
    exact_mod_cast this
  have hcn : 20 + 18 * (t : ℝ) ^ 3 < c * nn := by
    have h1 : (20 + 18 * (t : ℝ) ^ 3) / c < nn := by linarith
    rw [div_lt_iff₀ hc] at h1
    linarith [mul_comm nn c]
  have hsmall : 10 * nn + 9 * (t : ℝ) ^ 3 ≤ c * ((t : ℝ) - 1) * nn ^ 2 := by
    have ht3 : (0 : ℝ) ≤ (t : ℝ) ^ 3 := by positivity
    have hcn2 : (20 + 18 * (t : ℝ) ^ 3) * nn ≤ c * nn * nn :=
      mul_le_mul_of_nonneg_right hcn.le (by linarith)
    have hct : c * nn ^ 2 ≤ c * ((t : ℝ) - 1) * nn ^ 2 := by
      have : (1 : ℝ) ≤ (t : ℝ) - 1 := by linarith
      have hc0 : 0 ≤ c * nn ^ 2 := by positivity
      nlinarith
    nlinarith
  constructor
  · -- lower half
    have key : ((t : ℝ) - 1) * nn ^ 2 / (2 * t) - F ≤ c * (((t : ℝ) - 1) * nn ^ 2 / (2 * t)) := by
      rw [show c * (((t : ℝ) - 1) * nn ^ 2 / (2 * t)) = c * ((t : ℝ) - 1) * nn ^ 2 / (2 * t) by ring]
      rw [div_sub' (by positivity), div_le_div_iff_of_pos_right (by positivity)]
      nlinarith [hlow, hsmall]
    linarith
  · -- upper half
    nlinarith [hup]

end OMA.R_Erdos917_erdos_917_variants_three_dvd_R1
