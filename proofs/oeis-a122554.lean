import OMAStatements.S_oeis_a122554
open OMA.S_oeis_a122554 Finset

lemma T {n x} : x ∈ S (n+2) ↔ x ∈ S (n+1) ∨ (∃ y ∈ S (n+1), y+2 = x) ∨ ∃ y ∈ S (n+1), 2*y = x := by simp [S]

lemma M {n x} (h : x ∈ S (n+1)) : x ∈ S (n+2) ∧ x+2 ∈ S (n+2) ∧ 2*x ∈ S (n+2) := by simp [S, h]

lemma B {m x} (h : x ∈ S (m+1)) : 0 < x ∧ (x % 2 = 0 ∨ x ≤ 2*m+1) := by
  induction m generalizing x with
  | zero => simp [S] at h; omega
  | succ m ih => rcases T.1 h with g|⟨y,g,rfl⟩|⟨y,g,rfl⟩ <;> have := ih g <;> omega

lemma I (j x) (h : 0 < x) (h' : x ≤ 2*j+6) : x ∈ S (j+3) := by
  induction j generalizing x with
  | zero => simp [S]; omega
  | succ j ih =>
    by_cases g : x ≤ 2*j+6
    · exact (M (ih x h g)).1
    · obtain ⟨z, rfl⟩ : ∃ z, x = z + 2 := ⟨x - 2, by omega⟩
      exact (M (ih z (by omega) (by omega))).2.1

lemma F (k y) : 2*y ∈ S (k+3) ↔ y ∈ S (k+2) ∨ ∃ a ∈ S (k+1), a+1 = y := by
  induction k generalizing y with
  | zero => simp [S]; omega
  | succ k ih =>
    constructor
    · intro h
      rcases T.1 h with g|⟨b,g,e⟩|⟨b,g,e⟩
      · rcases (ih y).1 g with f|⟨c,f,rfl⟩
        exacts [.inl (M f).1, .inr ⟨c, (M f).1, rfl⟩]
      · obtain ⟨z, rfl⟩ : ∃ z, y = z + 1 := ⟨y - 1, by omega⟩
        obtain rfl : b = 2*z := by omega
        rcases (ih z).1 g with f|⟨c,f,rfl⟩
        exacts [.inr ⟨z, f, rfl⟩, .inl (M (M f).2.1).1]
      · obtain rfl : b = y := by omega
        exact .inl g
    · rintro (h|⟨c,h,rfl⟩)
      exacts [(M h).2.2, (M (M h).2.2).2.1]

lemma D (k) : (S (k+3)).map Equiv.natSumNatEquivNat.symm.toEmbedding = (S (k+2) ∪ (S (k+1)).image (·+1)).disjSum (range (k+3)) := by
  ext (y|y) <;> simp [F]
  constructor
  · intro h; have := B h; omega
  · intro h; exact I k _ (by omega) (by omega)

lemma N (j) : S (j+4) ∩ (S (j+3)).image (·+1) = Icc 2 (2*j+7) := by
  ext x; simp; constructor
  · rintro ⟨hx, y, hy, rfl⟩; have := B hx; have := B hy; omega
  · intro h; exact ⟨I (j+1) x (by omega) (by omega), x-1, I j _ (by omega) (by omega), by omega⟩

lemma R (j) : a (j+5) + j + 1 = a (j+4) + a (j+3) := by
  have := congrArg card (D (j+2))
  have := card_union_add_card_inter (S (j+4)) ((S (j+3)).image (·+1))
  rw [N, card_image_of_injective _ (add_left_injective 1)] at this
  simp [a, add_assoc] at *
  omega

theorem OMA.solution : type_of% @OMA.S_oeis_a122554.main := by
  have H : ∀ m, a (m+3) = LucasNat (m+3) + m + 2 ∧ a (m+4) = LucasNat (m+4) + m + 3 := fun m => by
    induction m with
    | zero => decide
    | succ m ih => have := R m; simp [LucasNat, add_assoc] at *; omega
  refine ⟨fun n h => ?_, fun n h => ?_⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
    have := R m; have := R (m+1); have := R (m+2); simp [add_assoc] at *; omega
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    have := (H m).1; omega
