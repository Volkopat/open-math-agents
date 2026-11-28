import FormalConjectures.ErdosProblems.«78»

/-! Li's rectangle property gives an ordinary Ramsey graph after
ordering each adjacency query. An ordered split of a homogeneous set
loses a factor of two, absorbed by increasing the logarithmic exponent. -/

namespace OMA.R_Erdos78_erdos_78_variants_li_strongly_explicit_R1

open Erdos78 SimpleGraph Finset Filter Real ComplexityTheory

private theorem ordered_halves {n r : ℕ} (S : Finset (Fin n)) (hs : S.card = r + r) :
    ∃ A B : Finset (Fin n), A.card = r ∧ B.card = r ∧ A ⊆ S ∧ B ⊆ S ∧
      ∀ x ∈ A, ∀ y ∈ B, x < y := by
  let f := S.orderEmbOfFin hs
  let a : Fin r ↪ Fin n := (Fin.castLEEmb (Nat.le_add_right r r)).trans f.toEmbedding
  let b : Fin r ↪ Fin n := (Fin.natAddEmb r).trans f.toEmbedding
  refine ⟨univ.map a, univ.map b, by simp, by simp, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, _, rfl⟩ := mem_map.mp hx
    exact S.orderEmbOfFin_mem hs _
  · intro x hx
    obtain ⟨i, _, rfl⟩ := mem_map.mp hx
    exact S.orderEmbOfFin_mem hs _
  · intro x hx y hy
    obtain ⟨i, _, rfl⟩ := mem_map.mp hx
    obtain ⟨j, _, rfl⟩ := mem_map.mp hy
    apply f.strictMono
    change i.val < r + j.val
    omega

private theorem ceiling_bound {t : ℝ} (ht : 4 ≤ t) (C : ℕ) :
    ⌈t ^ C⌉₊ + ⌈t ^ C⌉₊ ≤ ⌈t ^ (C + 1)⌉₊ := by
  have hpow : 1 ≤ t ^ C := one_le_pow₀ (show 1 ≤ t by linarith)
  have hc := Nat.ceil_lt_add_one (show 0 ≤ t ^ C by linarith)
  have hscale : 4 * t ^ C ≤ t ^ (C + 1) := by
    rw [pow_succ, mul_comm 4]
    exact mul_le_mul_of_nonneg_left ht (by linarith)
  have hle : ((⌈t ^ C⌉₊ : ℕ) : ℝ) + ((⌈t ^ C⌉₊ : ℕ) : ℝ) ≤ t ^ (C + 1) := by
    linarith
  exact_mod_cast hle.trans (Nat.le_ceil (t ^ (C + 1)))

/-- The uniform two-source property on ordered rectangles of polylogarithmic size. -/
def H1 : Prop :=
  ∃ C : ℕ, ∃ f : ℕ × ℕ × ℕ → Bool, IsPolyTime f ∧
    ∀ᶠ n : ℕ in atTop, ∀ A B : Finset (Fin n),
      A.card = ⌈(log n) ^ C⌉₊ → B.card = ⌈(log n) ^ C⌉₊ →
      (∀ x ∈ A, ∀ y ∈ B, x < y) →
        ∀ v : Bool, ∃ x ∈ A, ∃ y ∈ B, f (n, x.val, y.val) = v

/-- In the binary-input complexity model, discarding a query in the wrong
order preserves the polynomial time bound. -/
def H2 : Prop :=
  ∀ f : ℕ × ℕ × ℕ → Bool, IsPolyTime f →
    IsPolyTime (fun x : ℕ × ℕ × ℕ ↦ if x.2.1 < x.2.2 then f x else false)

theorem main : H1 → H2 → type_of% @Erdos78.erdos_78.variants.li_strongly_explicit := by
  intro hsource htime
  obtain ⟨C, f, hf, hsource⟩ := hsource
  let query (x : ℕ × ℕ × ℕ) : Bool := if x.2.1 < x.2.2 then f x else false
  refine ⟨((C + 1 : ℕ) : ℝ), by positivity, query, htime f hf, ?_⟩
  have hLog : Tendsto (fun n : ℕ ↦ log (n : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hsource, hLog.eventually_ge_atTop 4] with n hrect hn
  let r := ⌈(log (n : ℝ)) ^ C⌉₊
  let G := stronglyExplicitGraph query n
  have adj (x y : Fin n) (hxy : x < y) : G.Adj x y ↔ f (n, x.val, y.val) = true := by
    simp [G, stronglyExplicitGraph, query, fromRel_adj, hxy, not_lt_of_ge hxy.le, hxy.ne]
  have hf₁ : G.CliqueFree (r + r) := by
    intro S hs
    obtain ⟨A, B, hAc, hBc, hA, hB, ho⟩ := ordered_halves S hs.card_eq
    obtain ⟨x, hx, y, hy, hfalse⟩ := hrect A B hAc hBc ho false
    have hxy := ho x hx y hy
    have htrue := (adj x y hxy).mp (hs.isClique (hA hx) (hB hy) hxy.ne)
    exact Bool.noConfusion (htrue.symm.trans hfalse)
  have hf₂ : Gᶜ.CliqueFree (r + r) := by
    intro S hs
    obtain ⟨A, B, hAc, hBc, hA, hB, ho⟩ := ordered_halves S hs.card_eq
    obtain ⟨x, hx, y, hy, htrue⟩ := hrect A B hAc hBc ho true
    have hxy := ho x hx y hy
    have hnot := ((compl_adj G x y).mp (hs.isClique (hA hx) (hB hy) hxy.ne)).2
    exact hnot ((adj x y hxy).mpr htrue)
  have hbound : r + r ≤ ⌈(log (n : ℝ)) ^ ((C + 1 : ℕ) : ℝ)⌉₊ := by
    simpa only [Real.rpow_natCast] using ceiling_bound hn C
  exact ⟨hf₁.mono hbound, hf₂.mono hbound⟩

end OMA.R_Erdos78_erdos_78_variants_li_strongly_explicit_R1
