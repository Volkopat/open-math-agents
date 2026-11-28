import OMAStatements.S_oeis_a188553

namespace OMA.S_oeis_a188553
open Finset

private def column {n : ℕ} (h : Fin (n+1)) (i : Fin n) : Fin 2 :=
  if i.val < h.val then 1 else 0

private def height {n : ℕ} (c : Fin n → Fin 2) : Fin (n+1) :=
  ⟨(univ.filter (fun i => c i = 1)).card,by
    have h := card_le_card (filter_subset (fun i => c i = 1) univ)
    simpa using Nat.lt_succ_of_le h⟩

private theorem column_height {n : ℕ} (c : Fin n → Fin 2) (hc : Antitone c) (i : Fin n) :
    column (height c) i = c i := by
  let S := univ.filter (fun i => c i=1)
  by_cases hi : c i=1
  · have hsub : Iic i ⊆ S := by
      intro r hr
      have hle := hc (mem_Iic.mp hr)
      simp only [S,mem_filter,mem_univ,true_and]
      rw [hi] at hle
      omega
    have hcard := card_le_card hsub
    rw [Fin.card_Iic] at hcard
    have hlt : i.val < (height c).val := by change i.val < S.card; omega
    simp [column,hlt,hi]
  · have hsub : S ⊆ Iio i := by
      intro r hr
      obtain ⟨_,hr⟩ := mem_filter.mp hr
      apply mem_Iio.mpr
      by_contra! h
      have hle := hc h
      rw [hr] at hle
      omega
    have hcard := card_le_card hsub
    rw [Fin.card_Iio] at hcard
    have hlt : ¬i.val < (height c).val := by change ¬i.val < S.card; omega
    simp [column,hlt]
    omega

private theorem column_injective (n : ℕ) : Function.Injective (@column n) := by
  intro a b h
  apply Fin.ext
  by_contra! he
  rcases lt_or_gt_of_ne he with hab|hba
  · let i : Fin n := ⟨a.val,by omega⟩
    have hh := congrFun h i
    simp [column,i,hab] at hh
  · let i : Fin n := ⟨b.val,by omega⟩
    have hh := congrFun h i
    simp [column,i,hba] at hh

private theorem column_antitone {n : ℕ} (h : Fin (n+1)) : Antitone (column h) := by
  intro i r hir
  have : i.val ≤ r.val := hir
  unfold column
  split_ifs <;> omega

private theorem threshold_steps {n : ℕ} {a b : Fin (n+1)}
    (hh : ∀ i, column b i ≤ column a i)
    (hd : ∀ i i' : Fin n, i.val+1=i'.val → column a i' ≤ column b i) :
    b.val=a.val ∨ b.val+1=a.val := by
  have hba : b.val ≤ a.val := by
    by_contra! h
    let i : Fin n := ⟨a.val,by omega⟩
    have := hh i
    simp [column,i,h] at this
  have hdiff : a.val ≤ b.val+1 := by
    by_contra! h
    let i : Fin n := ⟨b.val,by omega⟩
    let i' : Fin n := ⟨b.val+1,by omega⟩
    have := hd i i' rfl
    simp [column,i,i',h] at this
  omega

private def encode {n k : ℕ} (w : Fin k → Fin (n+1)) := fun i j => column (w j) i

private theorem encode_avoids {n k : ℕ} (w : Fin k → Fin (n+1)) (hw : Steps w) : Avoids (encode w) := by
  refine ⟨fun j => column_antitone (w j), ?_⟩
  intro j j' hj
  have h := hw j j' hj
  constructor
  · intro i
    unfold encode column
    split_ifs <;> omega
  · intro i i' hi
    unfold encode column
    split_ifs <;> constructor <;> omega

private def decode {n k : ℕ} (A : Fin n → Fin k → Fin 2) := fun j => height (fun i => A i j)

private theorem encode_decode {n k : ℕ} (A : Fin n → Fin k → Fin 2) (hA : Avoids A) :
    encode (decode A)=A := by
  funext i j
  exact column_height _ (hA.1 j) i

private theorem decode_steps {n k : ℕ} (A : Fin n → Fin k → Fin 2) (hA : Avoids A) : Steps (decode A) := by
  intro j j' hj
  obtain ⟨hh,hd⟩ := hA.2 j j' hj
  have e (i j) : column (decode A j) i = A i j := congrFun (congrFun (encode_decode A hA) i) j
  exact threshold_steps (by simpa only [e] using hh) (by
    intro i i' hi
    simpa only [e] using (hd i i' hi).2)

private def arrayEquiv (n k : ℕ) :
    { A : Fin n → Fin k → Fin 2 // Avoids A } ≃ { w : Fin k → Fin (n+1) // Steps w } where
  toFun A := ⟨decode A.val,decode_steps _ A.property⟩
  invFun w := ⟨encode w.val,encode_avoids _ w.property⟩
  left_inv A := Subtype.ext (encode_decode _ A.property)
  right_inv w := by
    apply Subtype.ext
    funext j
    apply column_injective n
    funext i
    exact column_height _ (column_antitone (w.val j)) i

end OMA.S_oeis_a188553

theorem OMA.solution : type_of% @OMA.S_oeis_a188553.main := by
  intro n k _ _
  exact Nat.card_congr (OMA.S_oeis_a188553.arrayEquiv n k)
