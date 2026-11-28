import OMAStatements.S_opg_seymours_r_graph_conjecture

-- Reduction opg-seymours-r-graph-conjecture.R1 of Seymour's r-graph conjecture
-- Credit: @lzvxck
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
-- The literature route: Goldberg's conjecture (now a theorem, Chen-Jing-Zang) implies Seymour's
-- r-graph conjecture. Split by r: r <= 3 from Shannon's bound, r >= 4 from Goldberg with k = r + 1.

namespace OMA.R_opg_seymours_r_graph_conjecture_R1

private theorem count_ends {V : Type} [Fintype V] [DecidableEq V] (S : Finset V) (z : Sym2 V)
    (hz : ¬ z.IsDiag) :
    (S.filter (fun v => v ∈ z)).card =
      2 * (if ∀ v : V, v ∈ z → v ∈ S then 1 else 0) +
      (if (∃ v : V, v ∈ z ∧ v ∈ S) ∧ ∃ v : V, v ∈ z ∧ v ∉ S then 1 else 0) := by
  induction z using Sym2.ind with
  | h a b =>
    have hab : a ≠ b := by simpa using hz
    have h1 : (∀ v : V, v ∈ s(a, b) → v ∈ S) ↔ (a ∈ S ∧ b ∈ S) := by simp [Sym2.mem_iff]
    have h2 : ((∃ v : V, v ∈ s(a, b) ∧ v ∈ S) ∧ ∃ v : V, v ∈ s(a, b) ∧ v ∉ S) ↔
        ((a ∈ S ∨ b ∈ S) ∧ (a ∉ S ∨ b ∉ S)) := by simp [Sym2.mem_iff]
    simp only [h1, h2]
    by_cases ha : a ∈ S <;> by_cases hb : b ∈ S
    · have : S.filter (fun v => v ∈ s(a, b)) = {a, b} := by
        ext v; simp only [Finset.mem_filter, Sym2.mem_iff, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · exact fun h => h.2
        · rintro (rfl | rfl) <;> simp_all
      rw [this, Finset.card_pair hab]; simp [ha, hb]
    · have : S.filter (fun v => v ∈ s(a, b)) = {a} := by
        ext v; simp only [Finset.mem_filter, Sym2.mem_iff, Finset.mem_singleton]
        constructor
        · rintro ⟨h1, rfl | rfl⟩ <;> simp_all
        · rintro rfl; simp_all
      rw [this]; simp [ha, hb]
    · have : S.filter (fun v => v ∈ s(a, b)) = {b} := by
        ext v; simp only [Finset.mem_filter, Sym2.mem_iff, Finset.mem_singleton]
        constructor
        · rintro ⟨h1, rfl | rfl⟩ <;> simp_all
        · rintro rfl; simp_all
      rw [this]; simp [ha, hb]
    · have : S.filter (fun v => v ∈ s(a, b)) = ∅ := by
        ext v; simp only [Finset.mem_filter, Sym2.mem_iff, Finset.notMem_empty, iff_false]
        rintro ⟨h1, rfl | rfl⟩ <;> simp_all
      rw [this]; simp [ha, hb]

private theorem double_count {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] (ends : E → Sym2 V)
    (hloop : ∀ e, ¬ (ends e).IsDiag) (S : Finset V) :
    ∑ v ∈ S, (Finset.univ.filter fun e => v ∈ ends e).card =
      2 * (Finset.univ.filter fun e => ∀ v : V, v ∈ ends e → v ∈ S).card +
      (Finset.univ.filter fun e =>
          (∃ v : V, v ∈ ends e ∧ v ∈ S) ∧ ∃ v : V, v ∈ ends e ∧ v ∉ S).card := by
  simp only [Finset.card_filter]
  rw [Finset.sum_comm, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [← Finset.card_filter, count_ends S (ends e) (hloop e)]

/-- Shannon's theorem (1949) for maximum degree at most 3: a loopless multigraph in which every
vertex lies on at most `d ≤ 3` edges has a proper edge colouring with `⌊3d/2⌋` colours. It covers
the `r`-graphs with `r ≤ 3` (there `⌊3r/2⌋ ≤ r + 1`). -/
def H1 : Prop :=
  ∀ (V E : Type) [Fintype V] [DecidableEq V] [Fintype E] (ends : E → Sym2 V),
    (∀ e, ¬ (ends e).IsDiag) → ∀ d : ℕ, d ≤ 3 →
      (∀ v : V, (Finset.univ.filter fun e => v ∈ ends e).card ≤ d) →
      ∃ c : E → Fin (3 * d / 2), ∀ e f, e ≠ f → (∃ v, v ∈ ends e ∧ v ∈ ends f) → c e ≠ c f

/-- Goldberg's conjecture for `k ≥ 5`, in the encoding of the statement
opg-goldbergs-conjecture: a loopless multigraph with `Δ + 1 ≤ k` and
`e(S) ≤ k ⌊|S|/2⌋` for every vertex set `S` with `|S| ≥ 2` is `k`-edge-colourable. Proved by
Chen, Jing and Zang, J. Combin. Optim. 50 (2025), arXiv:1901.10316. -/
def H2 : Prop :=
  ∀ (V E : Type) [Fintype V] [DecidableEq V] [Fintype E] (ends : E → Sym2 V),
    (∀ e, ¬ (ends e).IsDiag) → ∀ k : ℕ, 5 ≤ k →
      (∀ v : V, (Finset.univ.filter fun e => v ∈ ends e).card + 1 ≤ k) →
      (∀ S : Finset V, 2 ≤ S.card →
        (Finset.univ.filter fun e => ∀ v : V, v ∈ ends e → v ∈ S).card ≤ k * (S.card / 2)) →
      ∃ c : E → Fin k, ∀ e f, e ≠ f → (∃ v, v ∈ ends e ∧ v ∈ ends f) → c e ≠ c f

/-- The reduction, with the target written out. For `r ≥ 4`, Goldberg with `k = r + 1`: double
counting gives `r |S| = 2 e(S) + |δ(S)|`, and `|δ(S)| ≥ r` for odd `S`, so `e(S) ≤ r ⌊|S|/2⌋`. -/
theorem of_H1_H2 : H1 → H2 → ∀ (V E : Type) [Fintype V] [DecidableEq V] [Fintype E] (ends : E → Sym2 V),
    (∀ e, ¬ (ends e).IsDiag) → ∀ r : ℕ,
      (∀ v : V, (Finset.univ.filter fun e => v ∈ ends e).card = r) →
      (∀ X : Finset V, Odd X.card →
        r ≤ (Finset.univ.filter fun e =>
          (∃ v : V, v ∈ ends e ∧ v ∈ X) ∧ ∃ v : V, v ∈ ends e ∧ v ∉ X).card) →
      ∃ c : E → Fin (r + 1), ∀ e f, e ≠ f → (∃ v, v ∈ ends e ∧ v ∈ ends f) → c e ≠ c f := by
  intro h1 h2 V E _ _ _ ends hloop r hreg hodd
  by_cases hr : r ≤ 3
  · obtain ⟨c, hc⟩ := h1 V E ends hloop r hr (fun v => (hreg v).le)
    have hle : 3 * r / 2 ≤ r + 1 := by omega
    exact ⟨fun e => Fin.castLE hle (c e),
      fun e f hef hv h => hc e f hef hv (Fin.castLE_injective hle h)⟩
  · refine h2 V E ends hloop (r + 1) (by omega) (fun v => by rw [hreg v]) fun S _ => ?_
    have hdc := double_count ends hloop S
    simp only [hreg, Finset.sum_const, smul_eq_mul] at hdc
    set I := (Finset.univ.filter fun e => ∀ v : V, v ∈ ends e → v ∈ S).card
    set C := (Finset.univ.filter fun e =>
          (∃ v : V, v ∈ ends e ∧ v ∈ S) ∧ ∃ v : V, v ∈ ends e ∧ v ∉ S).card with hC
    obtain ⟨m, hm | hm⟩ := Nat.even_or_odd' S.card
    · rw [hm] at hdc ⊢
      have : 2 * m / 2 = m := by omega
      rw [this]; nlinarith
    · have hcut : r ≤ C := hodd S ⟨m, hm⟩
      rw [hm] at hdc ⊢
      have : (2 * m + 1) / 2 = m := by omega
      rw [this]; nlinarith

theorem main : H1 → H2 → type_of% @OMA.S_opg_seymours_r_graph_conjecture.main :=
  of_H1_H2

end OMA.R_opg_seymours_r_graph_conjecture_R1
