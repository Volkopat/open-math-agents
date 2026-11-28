import OMAStatements.S_oeis_a108411

/-!
Chu's subset interpretation, proved by Andrew Howroyd, as formalized by
@ivillar (statement #11092, prior proof #15116). Each pair {i,n-i} below
the midpoint has three choices: neither endpoint, the lower, or the upper.
-/

namespace A108411Direct
open Finset Pointwise OMA.S_oeis_a108411

private def decode {n : ℕ} (f : Fin ((n+1)/2) → Fin 3) : Finset ℕ :=
  univ.biUnion fun i => if f i = 1 then {i.val} else if f i = 2 then {n-i.val} else ∅

private lemma mem_decode {n x : ℕ} {f : Fin ((n+1)/2) → Fin 3} :
    x ∈ decode f ↔ ∃ i, (f i = 1 ∧ x = i.val) ∨ (f i = 2 ∧ x = n-i.val) := by
  simp only [decode, mem_biUnion, mem_univ, true_and]
  apply exists_congr
  intro i
  split_ifs <;> simp_all

private lemma lower {n : ℕ} (f : Fin ((n+1)/2) → Fin 3) (i : Fin ((n+1)/2)) :
    i.val ∈ decode f ↔ f i = 1 := by
  rw [mem_decode]
  constructor
  · rintro ⟨j, ⟨hj, hij⟩ | ⟨hj, hij⟩⟩
    · exact (Fin.ext hij : i = j) ▸ hj
    · have := i.isLt; have := j.isLt; omega
  · intro hi; exact ⟨i, Or.inl ⟨hi, rfl⟩⟩

private lemma upper {n : ℕ} (f : Fin ((n+1)/2) → Fin 3) (i : Fin ((n+1)/2)) :
    n-i.val ∈ decode f ↔ f i = 2 := by
  rw [mem_decode]
  constructor
  · rintro ⟨j, ⟨hj, hij⟩ | ⟨hj, hij⟩⟩ <;> have hi := i.isLt <;> have h := j.isLt
    · omega
    · exact (Fin.ext (show i.val = j.val by omega) : i = j) ▸ hj
  · intro hi; exact ⟨i, Or.inr ⟨hi, rfl⟩⟩

private lemma mem_good {n : ℕ} {S : Finset ℕ} :
    S ∈ good n ↔ (∀ x ∈ S, x ≤ n) ∧ ∀ x ∈ S, ∀ y ∈ S, x+y ≠ n := by
  simp only [good, mem_filter, mem_powerset, subset_iff, mem_range, mem_add,
    not_exists, not_and]
  simp only [Nat.lt_succ_iff]

theorem count (n : ℕ) : (good n).card = 3 ^ ((n+1)/2) := by
  classical
  have hc : (univ : Finset (Fin ((n+1)/2) → Fin 3)).card = 3 ^ ((n+1)/2) := by simp
  rw [← hc]
  symm
  apply card_bij (fun f _ => decode (n := n) f)
  · intro f _
    rw [mem_good]
    constructor
    · intro x hx
      obtain ⟨i, h⟩ := mem_decode.mp hx
      have := i.isLt
      rcases h with ⟨_, h⟩ | ⟨_, h⟩ <;> omega
    · intro x hx y hy he
      obtain ⟨i, hix⟩ := mem_decode.mp hx
      obtain ⟨j, hjy⟩ := mem_decode.mp hy
      have hi := i.isLt; have hj := j.isLt
      rcases hix with ⟨hif, hx⟩ | ⟨hif, hx⟩ <;>
        rcases hjy with ⟨hjf, hy⟩ | ⟨hjf, hy⟩
      · omega
      · have h : i = j := Fin.ext (by omega)
        simp_all
      · have h : i = j := Fin.ext (by omega)
        simp_all
      · omega
  · intro f _ g _ h
    funext i
    have h1 := congrArg (fun S => i.val ∈ S) h
    have h2 := congrArg (fun S => n-i.val ∈ S) h
    simp only [lower, upper] at h1 h2
    generalize f i = a at *
    generalize g i = b at *
    fin_cases a <;> fin_cases b <;> simp_all
  · intro S hS
    obtain ⟨hb, hp⟩ := mem_good.mp hS
    let f : Fin ((n+1)/2) → Fin 3 := fun i =>
      if i.val ∈ S then 1 else if n-i.val ∈ S then 2 else 0
    refine ⟨f, mem_univ _, ?_⟩
    ext x
    constructor
    · intro hx
      obtain ⟨i, h⟩ := mem_decode.mp hx
      rcases h with ⟨hf, rfl⟩ | ⟨hf, rfl⟩ <;> dsimp [f] at hf <;>
        split_ifs at hf <;> simp_all
    · intro hx
      have hxn := hb x hx
      by_cases hl : x < (n+1)/2
      · rw [lower f ⟨x, hl⟩]
        simp [f, hx]
      · have hu : n-x < (n+1)/2 := by have := hp x hx x hx; omega
        have hnot : n-x ∉ S := by intro hy; exact hp x hx (n-x) hy (by omega)
        have heq : n-(n-x) = x := by omega
        rw [← heq, upper f ⟨n-x, hu⟩]
        simp [f, hnot, heq, hx]

end A108411Direct

theorem OMA.solution : type_of% @OMA.S_oeis_a108411.main := by
  intro n
  exact (A108411Direct.count n).symm

