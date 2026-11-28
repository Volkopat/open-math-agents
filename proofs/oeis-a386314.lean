import OMAStatements.S_oeis_a386314


open OMA.S_oeis_a386314

namespace OMA.A386314Proof

lemma reduced_induction (hC : Collatz) (P : ℕ → Prop) (h1 : P 1)
    (hb : ∀ k y, good k → good y → reduced k y → P y → P k) :
    ∀ k, good k → P k := by
  have main (n : ℕ) (hr : ReachesOne n) :
      ∀ x e : ℕ, n = 2 ^ e * x → good x → P x := by
    induction hr with
    | one =>
      intro x e he hx
      have hp : 0 < (2 : ℕ) ^ e := pow_pos (by decide) e
      have hle : x ≤ 2 ^ e * x := by nlinarith
      have hx1 : x = 1 := by have := hx.1; omega
      simpa [hx1] using h1
    | @back n hn ih =>
      intro x e he hx
      by_cases heven : n % 2 = 0
      · cases e with
        | zero =>
          simp only [pow_zero, one_mul] at he
          have hxodd := hx.2.1
          subst n
          omega
        | succ e =>
          apply ih x e
          · simp only [step, heven, ↓reduceIte]
            rw [he, pow_succ]
            rw [show 2 ^ e * 2 * x = 2 * (2 ^ e * x) by ring]
            omega
          · exact hx
      · have e0 : e = 0 := by
          by_contra hnz
          obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hnz
          rw [pow_succ] at he
          have hnmod : n % 2 = 0 := by simp [he, Nat.mul_mod]
          exact heven hnmod
        subst e
        simp only [pow_zero, one_mul] at he
        subst n
        obtain ⟨f, y, hyodd, hy⟩ := Nat.exists_eq_two_pow_mul_odd (show 3 * x + 1 ≠ 0 by omega)
        have hymod : y % 2 = 1 := by
          obtain ⟨c, hc⟩ := hyodd
          omega
        have hyg : good y := by
          refine ⟨?_, hymod, ?_⟩
          · by_contra! hyzero
            have hyz : y = 0 := by omega
            simp [hyz] at hy
          · intro hy3
            have hydiv : 3 ∣ y := Nat.dvd_of_mod_eq_zero hy3
            have hn3 : 3 ∣ 3 * x + 1 := by
              rw [hy]
              exact dvd_mul_of_dvd_right hydiv (2 ^ f)
            omega
        apply hb x y hx hyg ⟨hymod, f, hy⟩
        apply ih y f
        · simp only [step, heven, ↓reduceIte]
          exact hy
        · exact hyg
  intro k hk
  exact main k (hC k hk.1) k 0 (by simp) hk

end OMA.A386314Proof



namespace OMA.A386314Proof

open OMA.S_oeis_a386314

lemma eligible_exists_of_induction
    (hRI : ∀ (P : ℕ → Prop), P 1 →
      (∀ k y, good k → good y → reduced k y → P y → P k) →
      ∀ k, good k → P k) (s : Finset ℕ) : ∃ k, eligible s k := by
  classical
  by_contra h
  have hn : ∀ k, ¬ eligible s k := not_exists.mp h
  have h1 : 1 ∈ s := by
    by_contra h1
    exact hn 1 ⟨by norm_num [good], h1, Or.inl rfl⟩
  have hall : ∀ k, good k → k ∈ s := hRI (fun k => k ∈ s) h1 (by
    intro k y hk hy hr hys
    by_contra hks
    exact hn k ⟨hk, hks, Or.inr ⟨y, hys, hr⟩⟩)
  let k := 6 * (s.sup id + 1) + 1
  have hg : good k := by
    dsimp [good, k]
    omega
  have hb : k ≤ s.sup id := Finset.le_sup (f := id) (hall k hg)
  dsimp [k] at hb
  omega

end OMA.A386314Proof


namespace OMA.S_oeis_a386314

lemma greedy_pick_spec {s : Finset ℕ} (h : ∃ k, eligible s k) :
    eligible s (pick s) := by
  classical
  simp only [pick, dif_pos h]
  exact Nat.find_spec h

lemma greedy_pick_le {s : Finset ℕ} {k : ℕ} (h : eligible s k) : pick s ≤ k := by
  classical
  have hex : ∃ k, eligible s k := ⟨k, h⟩
  simp only [pick, dif_pos hex]
  exact Nat.find_min' hex h

lemma greedy_seen_image (n : ℕ) : seen n = (Finset.range n).image term := by
  classical
  induction n with
  | zero => simp [seen]
  | succ n ih =>
    rw [seen, Finset.range_add_one, Finset.image_insert, ← ih]
    rfl

lemma greedy_term_mem_seen {i n : ℕ} (h : i < n) : term i ∈ seen n := by
  classical
  rw [greedy_seen_image]
  exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr h, rfl⟩

lemma greedy_seen_mono {m n : ℕ} (h : m ≤ n) : seen m ⊆ seen n := by
  classical
  rw [greedy_seen_image, greedy_seen_image]
  exact Finset.image_subset_image (Finset.range_mono h)

lemma greedy_injective (hex : ∀ n, ∃ k, eligible (seen n) k) :
    Function.Injective term := by
  intro i j hij
  have hn (n : ℕ) : term n ∉ seen n := (greedy_pick_spec (hex n)).2.1
  by_contra h
  rcases lt_or_gt_of_ne h with hlt | hlt
  · exact hn j (hij ▸ greedy_term_mem_seen hlt)
  · exact hn i (hij.symm ▸ greedy_term_mem_seen hlt)

lemma greedy_selected (hex : ∀ n, ∃ k, eligible (seen n) k)
    {k N : ℕ} (hk : good k) (ready : k = 1 ∨ ∃ y ∈ seen N, reduced k y) :
    ∃ n, term n = k := by
  classical
  by_contra h
  have hne (n : ℕ) : term n ≠ k := fun e => h ⟨n, e⟩
  have hnot (n : ℕ) : k ∉ seen n := by
    rw [greedy_seen_image]
    intro hm
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hm
    exact hne i hi
  have hle (i : ℕ) : term (N + i) ≤ k := by
    apply greedy_pick_le
    refine ⟨hk, hnot _, ?_⟩
    rcases ready with rfl | ⟨y, hy, hred⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨y, greedy_seen_mono (Nat.le_add_right N i) hy, hred⟩
  let f : Fin (k + 1) → Fin k := fun i =>
    ⟨term (N + i), by have hh := hle i; have hhne := hne (N + i); omega⟩
  have hf : Function.Injective f := by
    intro i j hij
    have ht : term (N + i.val) = term (N + j.val) := congrArg Fin.val hij
    exact Fin.ext (Nat.add_left_cancel (greedy_injective hex ht))
  have hc := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_fin] at hc
  omega

lemma greedy_complete
    (hex : ∀ n, ∃ k, eligible (seen n) k)
    (hind : ∀ P : ℕ → Prop, P 1 →
      (∀ k y, good k → good y → reduced k y → P y → P k) → ∀ k, good k → P k) :
    Function.Injective term ∧ (∀ n, good (term n)) ∧
      (∀ k, good k → ∃ n, term n = k) := by
  refine ⟨greedy_injective hex, fun n => (greedy_pick_spec (hex n)).1, ?_⟩
  apply hind (fun k => ∃ n, term n = k)
  · exact greedy_selected hex (N := 0) (by norm_num [good]) (Or.inl rfl)
  · intro k y hk _ hred ⟨n, hn⟩
    apply greedy_selected hex (N := n + 1) hk
    exact Or.inr ⟨y, hn ▸ greedy_term_mem_seen (Nat.lt_succ_self n), hred⟩

end OMA.S_oeis_a386314


theorem OMA.solution : type_of% @OMA.S_oeis_a386314.main := by
  intro hC
  exact OMA.S_oeis_a386314.greedy_complete
    (fun n => OMA.A386314Proof.eligible_exists_of_induction
      (OMA.A386314Proof.reduced_induction hC) (OMA.S_oeis_a386314.seen n))
    (OMA.A386314Proof.reduced_induction hC)
