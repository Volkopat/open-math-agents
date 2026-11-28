import OMAReductions.R_Arxiv_2001_02665_kotzig_conjecture_large_R1

/-!
# Bare paths of admissible length in the Kotzig tree-embedding problem

The parent supplies bare paths of dyadic length. Montgomery, Pokrovskiy and
Sudakov require a multiple of 695 congruent to 7 modulo 12 in Lemma 2.7.
The first step chooses such a length near the square root of the original
length and bounds the number of disjoint blocks. The second step is the
rainbow embedding problem with that family of bare paths available.

Reference: https://arxiv.org/abs/2001.02665
Credit: @VestigeClub
-/

namespace OMA.R_Arxiv_2001_02665_kotzig_conjecture_large_R1_H2_R1

open SimpleGraph

private theorem split_bare {V : Type*} (T : SimpleGraph V) [Fintype V] [DecidableRel T.Adj]
    {m L k q : ℕ} (room : q * (k+1) ≤ L+1)
    (P : Fin m → Fin (L+1) → V)
    (inj : ∀ a i b j, P a i = P b j → a = b ∧ i = j)
    (adj : ∀ a (j : Fin L), T.Adj (P a j.castSucc) (P a j.succ))
    (bare : ∀ a (j : Fin (L+1)), 0 < j.val → j.val < L → T.degree (P a j) = 2) :
    ∃ Q : (Fin m × Fin q) → Fin (k+1) → V,
      (∀ a i b j, Q a i = Q b j → a = b ∧ i = j) ∧
      (∀ a (j : Fin k), T.Adj (Q a j.castSucc) (Q a j.succ)) ∧
      (∀ a (j : Fin (k+1)), 0 < j.val → j.val < k → T.degree (Q a j) = 2) := by
  let pos (b : Fin q) (j : Fin (k+1)) : Fin (L+1) :=
    ⟨b.val*(k+1) + j.val, by
      have hb := Nat.mul_le_mul_right (k+1) b.isLt
      rw [Nat.succ_mul] at hb
      omega⟩
  let Q (a : Fin m × Fin q) (j : Fin (k+1)) := P a.1 (pos a.2 j)
  refine ⟨Q, ?_, ?_, ?_⟩
  · intro a i b j he
    obtain ⟨hab, hij⟩ := inj _ _ _ _ he
    have eq : a.2.val*(k+1)+i.val = b.2.val*(k+1)+j.val := congrArg Fin.val hij
    have off := congrArg (fun t => t % (k+1)) eq
    simp [Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] at off
    have ix : i = j := Fin.ext off
    have prod : a.2.val*(k+1) = b.2.val*(k+1) := by rw [ix] at eq; omega
    have block : a.2 = b.2 := Fin.ext (Nat.eq_of_mul_eq_mul_right (by omega) prod)
    exact ⟨Prod.ext hab block, ix⟩
  · intro a j
    let u := pos a.2 j.castSucc
    let v := pos a.2 j.succ
    have next : v.val = u.val + 1 := rfl
    let i : Fin L := ⟨u.val, by have := v.isLt; omega⟩
    exact adj a.1 i
  · intro a j low high
    apply bare
    · change 0 < a.2.val * (k+1) + j.val
      omega
    · have bound := Nat.mul_le_mul_right (k+1) a.2.isLt
      rw [Nat.succ_mul] at bound
      change a.2.val * (k+1) + j.val < L
      omega

def H1 : Prop :=
  ∀ᶠ (n : ℕ) in Filter.atTop,
      let L := 2 ^ Nat.sqrt (Nat.log 2 n)
      ∃ k, 0 < k ∧ k ≤ Nat.sqrt L ∧ Nat.sqrt L < k+8340 ∧
        k%12=7 ∧ 695∣k ∧ n/(6400*k) ≤ (n/(800*L))*((L+1)/(k+1))

def H2 : Prop :=
  ∀ᶠ (n : ℕ) in Filter.atTop,
    let L := 2 ^ Nat.sqrt (Nat.log 2 n)
    ∀ (T : SimpleGraph (Fin (n+1))) [DecidableRel T.Adj],
      T.IsTree →
      n/100 < (Finset.univ.filter (fun w : Fin (n+1) =>
        ¬ (T.degree w = 1 ∧ ∃ v, T.Adj v w ∧ L^4 ≤
          (Finset.univ.filter (fun u => T.Adj v u ∧ T.degree u = 1)).card))).card →
      ∀ k : ℕ, 0 < k → k ≤ Nat.sqrt L → Nat.sqrt L < k+8340 → k%12 = 7 → 695 ∣ k →
        (∃ Q : Fin (n/(6400*k)) → Fin (k+1) → Fin (n+1),
          (∀ a i b j, Q a i = Q b j → a = b ∧ i = j) ∧
          (∀ a (j : Fin k), T.Adj (Q a j.castSucc) (Q a j.succ)) ∧
          (∀ a (j : Fin (k+1)), 0 < j.val → j.val < k → T.degree (Q a j) = 2)) →
        ∃ g : Fin (n+1) ↪ Fin (2*n+1),
          ∀ u v w z, T.Adj u v → T.Adj w z →
            (g u - g v = g w - g z ∨ g u - g v = g z - g w) → s(u,v) = s(w,z)

theorem main : H1 → H2 → OMA.R_Arxiv_2001_02665_kotzig_conjecture_large_R1.H2 := by
  intro h1 h2
  filter_upwards [h1,h2] with n hparam hshort
  intro T _ tree core paths
  obtain ⟨k,pos,upper,close,res,dvd,cap⟩ := hparam
  apply hshort T tree core k pos upper close res dvd
  obtain ⟨P,hi,ha,hb⟩ := paths
  let L := 2 ^ Nat.sqrt (Nat.log 2 n)
  let m := n/(800*L)
  let q := (L+1)/(k+1)
  have room : q*(k+1) ≤ L+1 := Nat.div_mul_le_self _ _
  obtain ⟨Q,inj,adj,bare⟩ := split_bare T room P hi ha hb
  let e : Fin (n/(6400*k)) ↪ Fin m × Fin q :=
    (Fin.castLEEmb cap).trans finProdFinEquiv.symm.toEmbedding
  refine ⟨fun a => Q (e a), ?_, fun a j => adj (e a) j, fun a j => bare (e a) j⟩
  intro x i y j he
  obtain ⟨eq,ij⟩ := inj _ _ _ _ he
  exact ⟨e.injective eq,ij⟩

end OMA.R_Arxiv_2001_02665_kotzig_conjecture_large_R1_H2_R1
