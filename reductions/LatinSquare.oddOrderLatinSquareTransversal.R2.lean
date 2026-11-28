import FormalConjectures.Paper.LatinSquare

-- Reduction LatinSquare.oddOrderLatinSquareTransversal.R2 of Conjectures about Latin Squares — oddOrderLatinSquareTransversal
-- Credit: @Pixelstorm44
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_LatinSquare_oddOrderLatinSquareTransversal_R2

/-- On a square with no proper quotient into equal Latin blocks, find a
partial transversal of size one less than the order. -/
def H1 : Prop :=
  ∀ (n : ℕ), Odd n → ∀ L : LatinSquare n,
    ¬ (∃ a b : ℕ, a < n ∧ b < n ∧ n = a * b ∧
      ∃ (R C S : (Fin a × Fin b) ≃ Fin n) (Q : LatinSquare a)
        (B : Fin a → Fin a → LatinSquare b),
        ∀ i j u v, L.mat (R (i,u)) (C (j,v)) = S (Q.mat i j, (B i j).mat u v)) →
    ∃ ρ σ, IsNearTransversal L ρ σ

/-- Repair the normalized one-defect case. The first k diagonal cells
carry their row labels, and the final diagonal cell repeats a label. -/
def H2 : Prop :=
  ∀ (k : ℕ), Odd (k + 1) → ∀ L : LatinSquare (k + 1),
    ¬ (∃ a b : ℕ, a < (k + 1) ∧ b < (k + 1) ∧ (k + 1) = a * b ∧
      ∃ (R C S : (Fin a × Fin b) ≃ Fin (k + 1)) (Q : LatinSquare a)
        (B : Fin a → Fin a → LatinSquare b),
        ∀ i j u v, L.mat (R (i,u)) (C (j,v)) = S (Q.mat i j, (B i j).mat u v)) →
    (∀ i : Fin k, L.mat i.castSucc i.castSucc = i.castSucc) →
    L.mat (Fin.last k) (Fin.last k) ≠ Fin.last k →
    ∃ σ, IsTransversal L σ

/-- An injective map on the first coordinates and injective maps on
the individual fibers give an injective map on the product. -/
lemma fiber_injective {a b : ℕ} {f : Fin a → Fin a}
    {g : Fin a → Fin b → Fin b} (hf : Function.Injective f)
    (hg : ∀ i, Function.Injective (g i)) :
    Function.Injective (fun p : Fin a × Fin b => (f p.1, g p.1 p.2)) := by
  rintro ⟨i, u⟩ ⟨j, v⟩ h
  have hij : i = j := hf (congrArg Prod.fst h)
  subst j
  exact Prod.ext rfl (hg i (congrArg Prod.snd h))

/-- Lift a transversal of the quotient using just the blocks it meets. -/
lemma lift_blocks {n a b : ℕ} (L : LatinSquare n)
    (R C S : (Fin a × Fin b) ≃ Fin n) (Q : LatinSquare a)
    (B : Fin a → Fin a → LatinSquare b)
    (hc : ∀ i j u v, L.mat (R (i,u)) (C (j,v)) =
      S (Q.mat i j, (B i j).mat u v))
    (q : Fin a → Fin a) (hq : IsTransversal Q q)
    (t : Fin a → Fin b → Fin b) (ht : ∀ i, IsTransversal (B i (q i)) (t i)) :
    ∃ σ, IsTransversal L σ := by
  let cols := fun p : Fin a × Fin b => (q p.1, t p.1 p.2)
  let vals := fun p : Fin a × Fin b =>
    (Q.mat p.1 (q p.1), (B p.1 (q p.1)).mat p.2 (t p.1 p.2))
  have hcols : Function.Injective cols := fiber_injective hq.1 (fun i => (ht i).1)
  have hvals : Function.Injective vals := fiber_injective hq.2 (fun i => (ht i).2)
  refine ⟨fun i => C (cols (R.symm i)), C.injective.comp (hcols.comp R.symm.injective), ?_⟩
  have hcell (i : Fin n) : L.mat i (C (cols (R.symm i))) = S (vals (R.symm i)) := by
    obtain ⟨⟨j,u⟩, rfl⟩ := R.surjective i
    simpa [cols, vals] using hc j (q j) u (t j u)
  intro i j h
  change L.mat i (C (cols (R.symm i))) = L.mat j (C (cols (R.symm j))) at h
  rw [hcell, hcell] at h
  exact R.symm.injective (hvals (S.injective h))

lemma normalize_near (repair : H2) (k : ℕ) (hodd : Odd (k+1))
    (L : LatinSquare (k+1)) (hprim : ¬ (∃ a b : ℕ, a < (k + 1) ∧ b < (k + 1) ∧ (k + 1) = a * b ∧
      ∃ (R C S : (Fin a × Fin b) ≃ Fin (k + 1)) (Q : LatinSquare a)
        (B : Fin a → Fin a → LatinSquare b),
        ∀ i j u v, L.mat (R (i,u)) (C (j,v)) = S (Q.mat i j, (B i j).mat u v)))
    (near : ∃ ρ σ, IsNearTransversal L ρ σ) :
    ∃ σ, IsTransversal L σ := by
  obtain ⟨ρ, σ, hr, hc, hs⟩ := near
  obtain ⟨R, hR⟩ := Equiv.Perm.exists_extending_pair Fin.castSucc ρ (Fin.castSucc_injective k) hr
  obtain ⟨C, hC⟩ := Equiv.Perm.exists_extending_pair Fin.castSucc σ (Fin.castSucc_injective k) hc
  obtain ⟨S, hS⟩ := Equiv.Perm.exists_extending_pair Fin.castSucc
    (fun i => L.mat (ρ i) (σ i)) (Fin.castSucc_injective k) hs
  let M : LatinSquare (k+1) := {
    mat := fun i j => S.symm (L.mat (R i) (C j))
    row_injective := fun i => S.symm.injective.comp ((L.row_injective (R i)).comp C.injective)
    col_injective := fun j => S.symm.injective.comp ((L.col_injective (C j)).comp R.injective) }
  have hdiag (i : Fin k) : M.mat i.castSucc i.castSucc = i.castSucc := by
    change S.symm (L.mat (R i.castSucc) (C i.castSucc)) = i.castSucc
    rw [hR, hC, ← hS i, S.symm_apply_apply]
  have hM : ∃ τ, IsTransversal M τ := by
    by_cases hlast : M.mat (Fin.last k) (Fin.last k) = Fin.last k
    · have hfull (i : Fin (k+1)) : M.mat i i = i := Fin.lastCases hlast hdiag i
      exact ⟨id, Function.injective_id, fun {i j} h => (hfull i).symm.trans (h.trans (hfull j))⟩
    · apply repair k hodd M _ hdiag hlast
      rintro ⟨a,b,ha,hb,hn,r,c,s,Q,B,hcells⟩
      apply hprim
      refine ⟨a,b,ha,hb,hn,r.trans R,c.trans C,s.trans S,Q,B,?_⟩
      intro i j u v
      exact (S.symm_apply_eq.mp (hcells i j u v))
  obtain ⟨τ, hτ, hval⟩ := hM
  refine ⟨fun i => C (τ (R.symm i)), C.injective.comp (hτ.comp R.symm.injective), ?_⟩
  intro i j h
  apply R.symm.injective
  apply hval
  simpa [M] using congrArg S.symm h

theorem main : H1 → H2 → type_of% @LatinSquare.oddOrderLatinSquareTransversal := by
  intro near repair n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hodd L
    by_cases split : ∃ a b : ℕ, a < n ∧ b < n ∧ n = a * b ∧
      ∃ (R C S : (Fin a × Fin b) ≃ Fin n) (Q : LatinSquare a)
        (B : Fin a → Fin a → LatinSquare b),
        ∀ i j u v, L.mat (R (i,u)) (C (j,v)) = S (Q.mat i j, (B i j).mat u v)
    · obtain ⟨a,b,ha,hb,hn,R,C,S,Q,B,hcells⟩ := split
      have hab : Odd (a*b) := hn ▸ hodd
      obtain ⟨q,hq⟩ := ih a ha (Nat.odd_mul.mp hab).1 Q
      choose t ht using fun i => ih b hb (Nat.odd_mul.mp hab).2 (B i (q i))
      exact lift_blocks L R C S Q B hcells q hq t ht
    · have hnear := near n hodd L split
      cases n with
      | zero => simp at hodd
      | succ k => exact normalize_near repair k hodd L split hnear

end OMA.R_LatinSquare_oddOrderLatinSquareTransversal_R2
