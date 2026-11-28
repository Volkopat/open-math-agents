import OMAStatements.S_mo_315341
import Mathlib

namespace OMA.PrimeSquareMatching

private def edges {n : ℕ} (i j : Fin n) : Prop :=
  Nat.Prime ((i.val + 1)^2 + (j.val + 1)^2)

private def evens (n : ℕ) : Set (Fin n) := {i | (i.val + 1) % 2 = 0}

private abbrev Good (n : ℕ) := {σ : Equiv.Perm (Fin n) // ∀ i, edges i (σ i)}

private theorem symmEdge {n : ℕ} {i j : Fin n} (h : edges i j) : edges j i := by
  simpa only [edges, add_comm] using h

private theorem sameSide {n : ℕ} {i j : Fin n} (h : edges i j)
    (hp : i ∈ evens n ↔ j ∈ evens n) : i.val = 0 ∧ j.val = 0 := by
  change (i.val + 1) % 2 = 0 ↔ (j.val + 1) % 2 = 0 at hp
  have he : (i.val + 1) % 2 = (j.val + 1) % 2 := by omega
  unfold edges at h
  rcases h.eq_two_or_odd with h₂ | ho
  · constructor <;> nlinarith [Nat.zero_le i.val, Nat.zero_le j.val]
  · rw [Nat.add_mod ((i.val + 1)^2), Nat.pow_mod (i.val + 1),
      Nat.pow_mod (j.val + 1), he] at ho
    have hm : (j.val + 1) % 2 = 0 ∨ (j.val + 1) % 2 = 1 := by omega
    rcases hm with hm | hm <;> simp [hm] at ho

private theorem image_odd {n : ℕ} (σ : Good n) {j : Fin n}
    (hj : j ∈ σ.val '' evens n) : j ∉ evens n := by
  obtain ⟨i, hi, rfl⟩ := hj
  intro hj
  have h := (sameSide (σ.prop i) ⟨fun _ => hj, fun _ => hi⟩).1
  simp [evens, h] at hi

private theorem outside_fixed {n : ℕ} (σ : Good n) {j : Fin n}
    (he : j ∉ evens n) (ho : j ∉ σ.val '' evens n) : σ.val j = j ∧ j.val = 0 := by
  obtain ⟨i, h⟩ := σ.val.surjective j
  have hi : i ∉ evens n := fun hi => ho ⟨i, hi, h⟩
  have hed : edges i j := by rw [← h]; exact σ.prop i
  obtain ⟨h₁, h₂⟩ := sameSide hed ⟨fun q => (hi q).elim, fun q => (he q).elim⟩
  have eq : i = j := Fin.ext (h₁.trans h₂.symm)
  exact ⟨eq ▸ h, h₂⟩

private theorem sameImage {n : ℕ} (σ τ : Good n) :
    σ.val '' evens n = τ.val '' evens n := by
  have incl (s t : Good n) : s.val '' evens n ⊆ t.val '' evens n := by
    intro j hj
    by_contra h
    have h0 := (outside_fixed t (image_odd s hj) h).2
    have sub : t.val '' evens n ⊆ s.val '' evens n := by
      intro k hk
      by_contra h'
      have h0' := (outside_fixed s (image_odd t hk) h').2
      have he : k = j := Fin.ext (h0'.trans h0.symm)
      exact h (he ▸ hk)
    have proper : t.val '' evens n ⊂ s.val '' evens n :=
      ⟨sub, fun converse => h (converse hj)⟩
    have hc := Set.ncard_lt_ncard proper
    rw [Set.ncard_image_of_injective _ t.val.injective,
      Set.ncard_image_of_injective _ s.val.injective] at hc
    exact (lt_irrefl _) hc
  exact Set.Subset.antisymm (incl σ τ) (incl τ σ)

private def inverse {n : ℕ} (σ : Good n) : Good n :=
  ⟨σ.val.symm, fun i => symmEdge (by simpa using σ.prop (σ.val.symm i))⟩

private abbrev OddPart {n : ℕ} (σ₀ : Good n) := σ₀.val '' evens n

private abbrev Match {n : ℕ} (σ₀ : Good n) :=
  {f : (evens n) ≃ (OddPart σ₀) // ∀ i : evens n, edges i.val (f i).val}

private noncomputable def restrict {n : ℕ} (σ₀ σ : Good n) : Match σ₀ := by
  have himage := sameImage σ σ₀
  let f (i : evens n) : OddPart σ₀ := ⟨σ.val i, by
    change σ.val i.val ∈ σ₀.val '' evens n
    rw [← himage]
    exact ⟨i, i.prop, rfl⟩⟩
  have hinj : Function.Injective f := fun i j he =>
    Subtype.ext (σ.val.injective (congrArg Subtype.val he))
  have hsurj : Function.Surjective f := by
    intro j
    have hj : j.val ∈ σ.val '' evens n := by rw [himage]; exact j.prop
    rcases hj with ⟨i, hi, he⟩
    exact ⟨⟨i, hi⟩, Subtype.ext he⟩
  exact ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, fun i => σ.prop i⟩

private noncomputable def joinFun {n : ℕ} {σ₀ : Good n} (p q : Match σ₀)
    (i : Fin n) : Fin n := by
  classical
  exact if he : i ∈ evens n then p.val ⟨i, he⟩
    else if ho : i ∈ OddPart σ₀ then q.val.symm ⟨i, ho⟩ else i

private theorem join_even {n : ℕ} {σ₀ : Good n} (p q : Match σ₀)
    (i : evens n) : joinFun p q i = p.val i := by
  simp only [joinFun, dif_pos i.prop]

private theorem join_odd {n : ℕ} {σ₀ : Good n} (p q : Match σ₀)
    (i : OddPart σ₀) : joinFun p q i = q.val.symm i := by
  simp only [joinFun, dif_neg (image_odd σ₀ i.prop), dif_pos i.prop]

private theorem join_out {n : ℕ} {σ₀ : Good n} (p q : Match σ₀)
    {i : Fin n} (he : i ∉ evens n) (ho : i ∉ OddPart σ₀) : joinFun p q i = i := by
  simp only [joinFun, dif_neg he, dif_neg ho]

private theorem join_inverse {n : ℕ} {σ₀ : Good n} (p q : Match σ₀)
    (i : Fin n) : joinFun q p (joinFun p q i) = i := by
  by_cases he : i ∈ evens n
  · let x : evens n := ⟨i, he⟩
    change joinFun q p (joinFun p q x) = x.val
    rw [join_even p q x, join_odd q p (p.val x)]
    simp
  · by_cases ho : i ∈ OddPart σ₀
    · let x : OddPart σ₀ := ⟨i, ho⟩
      change joinFun q p (joinFun p q x) = x.val
      rw [join_odd p q x, join_even q p (q.val.symm x)]
      simp
    · rw [join_out p q he ho, join_out q p he ho]

private noncomputable def join {n : ℕ} {σ₀ : Good n} (p q : Match σ₀) : Good n := by
  refine ⟨⟨joinFun p q, joinFun q p, join_inverse p q, join_inverse q p⟩, ?_⟩
  intro i
  change edges i (joinFun p q i)
  by_cases he : i ∈ evens n
  · let x : evens n := ⟨i, he⟩
    change edges x.val (joinFun p q x)
    rw [join_even p q x]
    exact p.prop x
  · by_cases ho : i ∈ OddPart σ₀
    · let x : OddPart σ₀ := ⟨i, ho⟩
      change edges x.val (joinFun p q x)
      rw [join_odd p q x]
      exact symmEdge (by simpa using q.prop (q.val.symm x))
    · rw [join_out p q he ho]
      simpa only [(outside_fixed σ₀ he ho).1] using σ₀.prop i

private noncomputable def splitEquiv {n : ℕ} (σ₀ : Good n) :
    Good n ≃ (Match σ₀ × Match σ₀) where
  toFun σ := (restrict σ₀ σ, restrict σ₀ (inverse σ))
  invFun pq := join pq.1 pq.2
  left_inv σ := by
    apply Subtype.ext
    apply Equiv.ext
    intro i
    change joinFun (restrict σ₀ σ) (restrict σ₀ (inverse σ)) i = σ.val i
    by_cases he : i ∈ evens n
    · exact join_even _ _ ⟨i, he⟩
    · by_cases ho : i ∈ OddPart σ₀
      · let x : OddPart σ₀ := ⟨i, ho⟩
        rw [join_odd _ _ x]
        have eq := congrArg (fun t : OddPart σ₀ => t.val)
          ((restrict σ₀ (inverse σ)).val.apply_symm_apply x)
        change σ.val.symm ((restrict σ₀ (inverse σ)).val.symm x).val = i at eq
        simpa using congrArg σ.val eq
      · rw [join_out _ _ he ho]
        have hn : i ∉ σ.val '' evens n := by rw [sameImage σ σ₀]; exact ho
        exact (outside_fixed σ he hn).1.symm
  right_inv := by
    rintro ⟨p, q⟩
    apply Prod.ext
    · change restrict σ₀ (join p q) = p
      apply Subtype.ext
      apply Equiv.ext
      intro i
      apply Subtype.ext
      exact join_even p q i
    · change restrict σ₀ (inverse (join p q)) = q
      apply Subtype.ext
      apply Equiv.ext
      intro i
      apply Subtype.ext
      exact join_even q p i

end OMA.PrimeSquareMatching

open OMA.PrimeSquareMatching in
theorem OMA.solution : type_of% @OMA.S_mo_315341.main := by
  classical
  intro n
  change IsSquare (Nat.card (Good n))
  by_cases h : Nonempty (Good n)
  · let σ₀ := Classical.choice h
    refine ⟨Nat.card (Match σ₀), ?_⟩
    rw [Nat.card_congr (splitEquiv σ₀), Nat.card_prod]
  · have : IsEmpty (Good n) := not_nonempty_iff.mp h
    exact ⟨0, by simp⟩