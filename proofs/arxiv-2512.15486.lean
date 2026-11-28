import OMAStatements.S_arxiv_2512_15486

/-!
Disproof of Conjecture 1 of Lalou, Mbarek, Skender and Togni (arXiv:2512.15486).

The conjecture was disproved by the same authors (arXiv:2610.08042, Section 3, with three-hyperedge
sunflowers); the smallest counterexample, the sunflower `S_3`, is from Novaković and Jojić
(arXiv:2610.27133, Theorem 3.1): six vertices `s₁, s₂, s₃, p₁, p₂, p₃` (here `0, …, 5`) and the
three hyperedges `{s₁, s₂, s₃, pᵢ}`. Then `χ_p = 4`, `α = 3` and `χ²_p = 3`, while the conjecture
predicts `χ²_p = 4 - ⌈3 / 2⌉ = 2`.
* A panchromatic colouring has at most 4 colours, since a hyperedge has 4 vertices; colouring the
  `sᵢ` with three colours and all the `pᵢ` with a fourth one gives 4 colours and 3 unique colours.
* Every panchromatic 4-colouring gives the three `sᵢ` distinct colours and all the `pᵢ` the fourth
  colour, so it has at least 3 unique colours (a finite check on the six colours).
* Colouring `sᵢ` and `pᵢ` with colour `i` is bipanchromatic with 3 colours; a bipanchromatic
  colouring has no unique colour, hence not 4 colours, and at most 4 colours as it is panchromatic.
-/

open OMA.S_arxiv_2512_15486

namespace OMADisproofAux

/-- The hyperedges `{s₁, s₂, s₃, pᵢ}` of the sunflower `S_3`. -/
def E : Finset (Finset (Fin 6)) := {{0, 1, 2, 3}, {0, 1, 2, 4}, {0, 1, 2, 5}}

theorem mem_E (e : Finset (Fin 6)) (he : e ∈ E) :
    e = {0, 1, 2, 3} ∨ e = {0, 1, 2, 4} ∨ e = {0, 1, 2, 5} := by
  simpa [E] using he

theorem e1_mem : ({0, 1, 2, 3} : Finset (Fin 6)) ∈ E := by simp [E]
theorem e2_mem : ({0, 1, 2, 4} : Finset (Fin 6)) ∈ E := by simp [E]
theorem e3_mem : ({0, 1, 2, 5} : Finset (Fin 6)) ∈ E := by simp [E]

/-- A panchromatic colouring has at most 4 colours. -/
theorem le_four {k : ℕ} (φ : Fin 6 → Fin k) (hφ : IsPanchromatic E φ) : k ≤ 4 := by
  have hsub : (Finset.univ : Finset (Fin k)) ⊆ ({0, 1, 2, 3} : Finset (Fin 6)).image φ := by
    intro c _
    obtain ⟨v, hv, rfl⟩ := hφ _ e1_mem c
    exact Finset.mem_image_of_mem φ hv
  calc k = (Finset.univ : Finset (Fin k)).card := by simp
    _ ≤ (({0, 1, 2, 3} : Finset (Fin 6)).image φ).card := Finset.card_le_card hsub
    _ ≤ ({0, 1, 2, 3} : Finset (Fin 6)).card := Finset.card_image_le
    _ = 4 := by decide

/-- The six-colour check: a panchromatic 4-colouring has at least 3 unique colours. -/
theorem key : ∀ a b c d e f : Fin 4, (∀ x : Fin 4, a = x ∨ b = x ∨ c = x ∨ d = x) →
    (∀ x : Fin 4, a = x ∨ b = x ∨ c = x ∨ e = x) → (∀ x : Fin 4, a = x ∨ b = x ∨ c = x ∨ f = x) →
    3 ≤ numUnique ![a, b, c, d, e, f] := by
  decide

theorem edge_cover (φ : Fin 6 → Fin 4) (hφ : IsPanchromatic E φ) (j : Fin 6)
    (he : ({0, 1, 2, j} : Finset (Fin 6)) ∈ E) (x : Fin 4) :
    φ 0 = x ∨ φ 1 = x ∨ φ 2 = x ∨ φ j = x := by
  obtain ⟨v, hv, hvx⟩ := hφ _ he x
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl | rfl <;> simp [hvx]

theorem three_le_unique (φ : Fin 6 → Fin 4) (hφ : IsPanchromatic E φ) : 3 ≤ numUnique φ := by
  have e : φ = ![φ 0, φ 1, φ 2, φ 3, φ 4, φ 5] := by
    funext i; fin_cases i <;> rfl
  rw [e]
  exact key _ _ _ _ _ _ (edge_cover φ hφ 3 e1_mem) (edge_cover φ hφ 4 e2_mem)
    (edge_cover φ hφ 5 e3_mem)

/-- `s₁, s₂, s₃` get the colours 0, 1, 2 and all the `pᵢ` the colour 3. -/
def φ₀ : Fin 6 → Fin 4 := ![0, 1, 2, 3, 3, 3]

/-- `sᵢ` and `pᵢ` get the colour `i`. -/
def φ₁ : Fin 6 → Fin 3 := ![0, 1, 2, 0, 1, 2]

theorem φ₀_pan : IsPanchromatic E φ₀ := by
  intro e he
  rcases mem_E e he with rfl | rfl | rfl <;> decide

theorem φ₁_pan : IsPanchromatic E φ₁ := by
  intro e he
  rcases mem_E e he with rfl | rfl | rfl <;> decide

theorem hP : IsGreatest {k : ℕ | ∃ φ : Fin 6 → Fin k, IsPanchromatic E φ} 4 :=
  ⟨⟨φ₀, φ₀_pan⟩, fun _ ⟨φ, hφ⟩ => le_four φ hφ⟩

theorem hA : IsLeast {u : ℕ | ∃ φ : Fin 6 → Fin 4, IsPanchromatic E φ ∧ numUnique φ = u} 3 :=
  ⟨⟨φ₀, φ₀_pan, by decide⟩, fun _ ⟨φ, hφ, hu⟩ => hu ▸ three_le_unique φ hφ⟩

theorem hB : IsGreatest {k : ℕ | ∃ φ : Fin 6 → Fin k, IsBipanchromatic E φ} 3 := by
  refine ⟨⟨φ₁, φ₁_pan, by decide⟩, ?_⟩
  rintro k ⟨φ, hφ, h2⟩
  have h4 := le_four φ hφ
  by_contra hk
  obtain rfl : k = 4 := by omega
  have h3 := three_le_unique φ hφ
  have h0 : numUnique φ = 0 := by
    rw [numUnique, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro c _ hc
    have := h2 c
    omega
  omega

end OMADisproofAux

open OMADisproofAux in
theorem OMA.disproof : ¬ (type_of% @OMA.S_arxiv_2512_15486.main) := by
  intro h
  have e := h (Fin 6) E 4 3 3 hP hA hB
  have hc : ⌈((3 : ℕ) : ℚ) / 2⌉ = 2 := by
    rw [Int.ceil_eq_iff]
    norm_num
  rw [hc] at e
  norm_num at e
