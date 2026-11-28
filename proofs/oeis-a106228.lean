import OMAStatements.S_oeis_a106228

open OMA.S_oeis_a106228 PowerSeries

private def G (n : ℕ) (b : ℕ → ℕ) : Type :=
  {e : (i : Fin n) → Fin (b i) //
    ∀ i j k : Fin n, i < j → j < k → ¬ ((e j : ℕ) < e i ∧ (e i : ℕ) ≤ e k)}

private noncomputable instance instFintypeG (n : ℕ) (b : ℕ → ℕ) : Fintype (G n b) := by
  unfold G
  infer_instance

private lemma card_G_zero (b : ℕ → ℕ) : Fintype.card (G 0 b) = 1 := by
  rw [Fintype.card_eq_one_iff]
  refine ⟨⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩, fun e => ?_⟩
  exact Subtype.ext (funext fun i => Fin.elim0 i)

private lemma card_G_congr (n : ℕ) {b1 b2 : ℕ → ℕ} (h : ∀ j < n, b1 j = b2 j) :
    Fintype.card (G n b1) = Fintype.card (G n b2) := by
  refine Fintype.card_congr
    { toFun := fun e =>
        ⟨fun i => ⟨(e.1 i : ℕ), by rw [← h i i.2]; exact (e.1 i).2⟩, fun i j k hij hjk => e.2 i j k hij hjk⟩
      invFun := fun e =>
        ⟨fun i => ⟨(e.1 i : ℕ), by rw [h i i.2]; exact (e.1 i).2⟩, fun i j k hij hjk => e.2 i j k hij hjk⟩
      left_inv := fun e => Subtype.ext (funext fun i => Fin.ext rfl)
      right_inv := fun e => Subtype.ext (funext fun i => Fin.ext rfl) }

private noncomputable def splitIdx {n : ℕ} {b : ℕ → ℕ} (e : G (n + 1) b) : Fin (n + 1) :=
  let S : Finset (Fin n) := Finset.univ.filter fun t : Fin n => (e.1 t.succ : ℕ) < (e.1 0 : ℕ)
  if h : S.Nonempty then (S.min' h).castSucc else Fin.last n

private lemma splitIdx_left {n : ℕ} {b : ℕ → ℕ} (e : G (n + 1) b)
    (t : Fin (splitIdx e)) :
    (e.1 0 : ℕ) ≤ (e.1 ⟨(t : ℕ) + 1, by omega⟩ : ℕ) := by
  let S : Finset (Fin n) := Finset.univ.filter fun u : Fin n => (e.1 u.succ : ℕ) < (e.1 0 : ℕ)
  have ht_lt_n : (t : ℕ) < n := by
    have h1 : (t : ℕ) < (splitIdx e : ℕ) := t.2
    have h2 : (splitIdx e : ℕ) ≤ n := Nat.lt_succ_iff.mp (splitIdx e).2
    omega
  let t' : Fin n := ⟨(t : ℕ), ht_lt_n⟩
  have hnot : t' ∉ S := by
    intro hmem
    have hne : S.Nonempty := ⟨t', hmem⟩
    have hmin : S.min' hne ≤ t' := Finset.min'_le S t' hmem
    have hsp : (splitIdx e : ℕ) = (S.min' hne : ℕ) := by
      simp [splitIdx, S, hne]
    have htlt : (t : ℕ) < (splitIdx e : ℕ) := t.2
    have hle : (S.min' hne : ℕ) ≤ (t : ℕ) := hmin
    omega
  have hnotlt : ¬ ((e.1 t'.succ : ℕ) < (e.1 0 : ℕ)) := by
    intro hlt
    exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ t', hlt⟩)
  have heq : t'.succ = ⟨(t : ℕ) + 1, by omega⟩ := Fin.ext rfl
  rw [heq] at hnotlt
  omega

private lemma splitIdx_drop {n : ℕ} {b : ℕ → ℕ} (e : G (n + 1) b)
    (hi : (splitIdx e : ℕ) < n) :
    (e.1 ⟨(splitIdx e : ℕ) + 1, by omega⟩ : ℕ) < (e.1 0 : ℕ) := by
  let S : Finset (Fin n) := Finset.univ.filter fun u : Fin n => (e.1 u.succ : ℕ) < (e.1 0 : ℕ)
  by_cases hne : S.Nonempty
  · have hmem : S.min' hne ∈ S := Finset.min'_mem S hne
    have hlt : (e.1 (S.min' hne).succ : ℕ) < (e.1 0 : ℕ) := (Finset.mem_filter.mp hmem).2
    have hsp : (splitIdx e : ℕ) = (S.min' hne : ℕ) := by
      simp [splitIdx, S, hne]
    have heq : (S.min' hne).succ = ⟨(splitIdx e : ℕ) + 1, by omega⟩ := Fin.ext (by simp [hsp])
    rw [heq] at hlt
    exact hlt
  · have hsp : (splitIdx e : ℕ) = n := by
      simp [splitIdx, S, hne]
    omega

private lemma splitIdx_right {n : ℕ} {b : ℕ → ℕ} (e : G (n + 1) b)
    (s : Fin (n - (splitIdx e : ℕ))) :
    (e.1 ⟨(splitIdx e : ℕ) + 1 + (s : ℕ), by omega⟩ : ℕ) < (e.1 0 : ℕ) := by
  have hs2 : (s : ℕ) < n - (splitIdx e : ℕ) := s.2
  have hi : (splitIdx e : ℕ) < n := by omega
  have hdrop := splitIdx_drop e hi
  by_cases hs : (s : ℕ) = 0
  · have heq : (⟨(splitIdx e : ℕ) + 1 + (s : ℕ), by omega⟩ : Fin (n + 1)) =
        ⟨(splitIdx e : ℕ) + 1, by omega⟩ := Fin.ext (by simp [hs])
    rw [heq]
    exact hdrop
  · have hlt1 : (0 : Fin (n + 1)) < ⟨(splitIdx e : ℕ) + 1, by omega⟩ := by
      change 0 < (splitIdx e : ℕ) + 1
      omega
    have hlt2 : (⟨(splitIdx e : ℕ) + 1, by omega⟩ : Fin (n + 1)) <
        ⟨(splitIdx e : ℕ) + 1 + (s : ℕ), by omega⟩ := by
      change (splitIdx e : ℕ) + 1 < (splitIdx e : ℕ) + 1 + (s : ℕ)
      omega
    have havoid := e.2 0 ⟨(splitIdx e : ℕ) + 1, by omega⟩
      ⟨(splitIdx e : ℕ) + 1 + (s : ℕ), by omega⟩ hlt1 hlt2
    by_contra hge
    exact havoid ⟨hdrop, by omega⟩

private noncomputable def decompToFun {n : ℕ} {b : ℕ → ℕ} (e : G (n + 1) b) :
    Σ (c : Fin (b 0)) (i : Fin (n + 1)),
      G i (fun t => b (t + 1) - c) × G (n - i) (fun _ => c) :=
  let c : Fin (b 0) := e.1 0
  let i : Fin (n + 1) := splitIdx e
  let eL : G i (fun t => b (t + 1) - c) :=
    ⟨fun t => ⟨(e.1 ⟨(t : ℕ) + 1, by omega⟩ : ℕ) - (c : ℕ), by
      have hlt : (e.1 ⟨(t : ℕ) + 1, by omega⟩ : ℕ) < b ((t : ℕ) + 1) :=
        (e.1 ⟨(t : ℕ) + 1, by omega⟩).2
      have hge := splitIdx_left e t
      change (e.1 ⟨(t : ℕ) + 1, by omega⟩ : ℕ) - (c : ℕ) < b ((t : ℕ) + 1) - (c : ℕ)
      omega⟩,
    fun u v w huv hvw hbad => by
      have hgeu := splitIdx_left e u
      have hgev := splitIdx_left e v
      have hgew := splitIdx_left e w
      have h1 : (⟨(u : ℕ) + 1, by omega⟩ : Fin (n + 1)) < ⟨(v : ℕ) + 1, by omega⟩ := by
        change (u : ℕ) + 1 < (v : ℕ) + 1
        exact Nat.add_lt_add_right huv 1
      have h2 : (⟨(v : ℕ) + 1, by omega⟩ : Fin (n + 1)) < ⟨(w : ℕ) + 1, by omega⟩ := by
        change (v : ℕ) + 1 < (w : ℕ) + 1
        exact Nat.add_lt_add_right hvw 1
      dsimp only at hbad
      exact e.2 ⟨(u : ℕ) + 1, by omega⟩ ⟨(v : ℕ) + 1, by omega⟩ ⟨(w : ℕ) + 1, by omega⟩
        h1 h2 ⟨by omega, by omega⟩⟩
  let eR : G (n - i) (fun _ => c) :=
    ⟨fun s => ⟨(e.1 ⟨(i : ℕ) + 1 + (s : ℕ), by omega⟩ : ℕ), splitIdx_right e s⟩,
    fun u v w huv hvw hbad => by
      have h1 : (⟨(i : ℕ) + 1 + (u : ℕ), by omega⟩ : Fin (n + 1)) <
          ⟨(i : ℕ) + 1 + (v : ℕ), by omega⟩ := by
        change (i : ℕ) + 1 + (u : ℕ) < (i : ℕ) + 1 + (v : ℕ)
        omega
      have h2 : (⟨(i : ℕ) + 1 + (v : ℕ), by omega⟩ : Fin (n + 1)) <
          ⟨(i : ℕ) + 1 + (w : ℕ), by omega⟩ := by
        change (i : ℕ) + 1 + (v : ℕ) < (i : ℕ) + 1 + (w : ℕ)
        omega
      exact e.2 ⟨(i : ℕ) + 1 + (u : ℕ), by omega⟩ ⟨(i : ℕ) + 1 + (v : ℕ), by omega⟩
        ⟨(i : ℕ) + 1 + (w : ℕ), by omega⟩ h1 h2 hbad⟩
  ⟨c, i, eL, eR⟩

private def invFunVal {n : ℕ} {b : ℕ → ℕ} (hb : Monotone b)
    (c : Fin (b 0)) (i : Fin (n + 1))
    (eL : G i (fun t => b (t + 1) - c)) (eR : G (n - i) (fun _ => c))
    (j : Fin (n + 1)) : Fin (b j) :=
  if hj0 : (j : ℕ) = 0 then
    ⟨(c : ℕ), by rw [hj0]; exact c.2⟩
  else if hji : (j : ℕ) ≤ (i : ℕ) then
    ⟨(eL.1 ⟨(j : ℕ) - 1, by omega⟩ : ℕ) + (c : ℕ), by
      have hlt : (eL.1 ⟨(j : ℕ) - 1, by omega⟩ : ℕ) < b ((j : ℕ) - 1 + 1) - (c : ℕ) :=
        (eL.1 ⟨(j : ℕ) - 1, by omega⟩).2
      have hsub : (j : ℕ) - 1 + 1 = (j : ℕ) := by omega
      rw [hsub] at hlt
      have hcb : (c : ℕ) < b j := lt_of_lt_of_le c.2 (hb (Nat.zero_le j))
      omega⟩
  else
    ⟨(eR.1 ⟨(j : ℕ) - (i : ℕ) - 1, by omega⟩ : ℕ), by
      have hlt : (eR.1 ⟨(j : ℕ) - (i : ℕ) - 1, by omega⟩ : ℕ) < (c : ℕ) :=
        (eR.1 ⟨(j : ℕ) - (i : ℕ) - 1, by omega⟩).2
      have hcb : (c : ℕ) < b j := lt_of_lt_of_le c.2 (hb (Nat.zero_le j))
      omega⟩

private lemma invFunVal_zero {n : ℕ} {b : ℕ → ℕ} (hb : Monotone b)
    (c : Fin (b 0)) (i : Fin (n + 1))
    (eL : G i (fun t => b (t + 1) - c)) (eR : G (n - i) (fun _ => c))
    (j : Fin (n + 1)) (hj0 : (j : ℕ) = 0) :
    (invFunVal hb c i eL eR j : ℕ) = (c : ℕ) := by
  simp [invFunVal, hj0]

private lemma invFunVal_left {n : ℕ} {b : ℕ → ℕ} (hb : Monotone b)
    (c : Fin (b 0)) (i : Fin (n + 1))
    (eL : G i (fun t => b (t + 1) - c)) (eR : G (n - i) (fun _ => c))
    (j : Fin (n + 1)) (hj0 : (j : ℕ) ≠ 0) (hji : (j : ℕ) ≤ (i : ℕ)) :
    (invFunVal hb c i eL eR j : ℕ) = (eL.1 ⟨(j : ℕ) - 1, by omega⟩ : ℕ) + (c : ℕ) := by
  simp [invFunVal, hj0, hji]

private lemma invFunVal_right {n : ℕ} {b : ℕ → ℕ} (hb : Monotone b)
    (c : Fin (b 0)) (i : Fin (n + 1))
    (eL : G i (fun t => b (t + 1) - c)) (eR : G (n - i) (fun _ => c))
    (j : Fin (n + 1)) (hji : (i : ℕ) < (j : ℕ)) :
    (invFunVal hb c i eL eR j : ℕ) = (eR.1 ⟨(j : ℕ) - (i : ℕ) - 1, by omega⟩ : ℕ) := by
  have hj0 : (j : ℕ) ≠ 0 := by omega
  have hnot : ¬ (j : ℕ) ≤ (i : ℕ) := by omega
  simp [invFunVal, hj0, hnot]

private def decompInvFun {n : ℕ} {b : ℕ → ℕ} (hb : Monotone b) :
    (Σ (c : Fin (b 0)) (i : Fin (n + 1)),
      G i (fun t => b (t + 1) - c) × G (n - i) (fun _ => c)) → G (n + 1) b
  | ⟨c, i, eL, eR⟩ =>
    ⟨invFunVal hb c i eL eR, fun u v w huv hvw hbad => by
      have huvn : (u : ℕ) < (v : ℕ) := huv
      have hvwn : (v : ℕ) < (w : ℕ) := hvw
      by_cases hwi : (w : ℕ) ≤ (i : ℕ)
      · have hvi : (v : ℕ) ≤ (i : ℕ) := by omega
        have hv0 : (v : ℕ) ≠ 0 := by omega
        have hw0 : (w : ℕ) ≠ 0 := by omega
        have hvv := invFunVal_left hb c i eL eR v hv0 hvi
        have hww := invFunVal_left hb c i eL eR w hw0 hwi
        by_cases hu0 : (u : ℕ) = 0
        · have huu := invFunVal_zero hb c i eL eR u hu0
          omega
        · have hui : (u : ℕ) ≤ (i : ℕ) := by omega
          have huu := invFunVal_left hb c i eL eR u hu0 hui
          have h1 : (⟨(u : ℕ) - 1, by omega⟩ : Fin i) < ⟨(v : ℕ) - 1, by omega⟩ := by
            change (u : ℕ) - 1 < (v : ℕ) - 1
            omega
          have h2 : (⟨(v : ℕ) - 1, by omega⟩ : Fin i) < ⟨(w : ℕ) - 1, by omega⟩ := by
            change (v : ℕ) - 1 < (w : ℕ) - 1
            omega
          exact eL.2 ⟨(u : ℕ) - 1, by omega⟩ ⟨(v : ℕ) - 1, by omega⟩ ⟨(w : ℕ) - 1, by omega⟩
            h1 h2 ⟨by omega, by omega⟩
      · have hwi' : (i : ℕ) < (w : ℕ) := by omega
        have hww := invFunVal_right hb c i eL eR w hwi'
        have hwlt : (invFunVal hb c i eL eR w : ℕ) < (c : ℕ) := by
          rw [hww]
          exact (eR.1 ⟨(w : ℕ) - (i : ℕ) - 1, by omega⟩).2
        have hui' : (i : ℕ) < (u : ℕ) := by
          by_contra hle
          have hle' : (u : ℕ) ≤ (i : ℕ) := by omega
          by_cases hu0 : (u : ℕ) = 0
          · have huu := invFunVal_zero hb c i eL eR u hu0
            omega
          · have huu := invFunVal_left hb c i eL eR u hu0 hle'
            omega
        have hvi' : (i : ℕ) < (v : ℕ) := by omega
        have huu := invFunVal_right hb c i eL eR u hui'
        have hvv := invFunVal_right hb c i eL eR v hvi'
        have h1 : (⟨(u : ℕ) - (i : ℕ) - 1, by omega⟩ : Fin (n - i)) <
            ⟨(v : ℕ) - (i : ℕ) - 1, by omega⟩ := by
          change (u : ℕ) - (i : ℕ) - 1 < (v : ℕ) - (i : ℕ) - 1
          omega
        have h2 : (⟨(v : ℕ) - (i : ℕ) - 1, by omega⟩ : Fin (n - i)) <
            ⟨(w : ℕ) - (i : ℕ) - 1, by omega⟩ := by
          change (v : ℕ) - (i : ℕ) - 1 < (w : ℕ) - (i : ℕ) - 1
          omega
        exact eR.2 ⟨(u : ℕ) - (i : ℕ) - 1, by omega⟩ ⟨(v : ℕ) - (i : ℕ) - 1, by omega⟩
          ⟨(w : ℕ) - (i : ℕ) - 1, by omega⟩ h1 h2 ⟨by omega, by omega⟩⟩

private lemma splitIdx_decompInvFun {n : ℕ} {b : ℕ → ℕ} (hb : Monotone b)
    (c : Fin (b 0)) (i : Fin (n + 1))
    (eL : G i (fun t => b (t + 1) - c)) (eR : G (n - i) (fun _ => c)) :
    splitIdx (decompInvFun hb ⟨c, i, eL, eR⟩) = i := by
  let e := decompInvFun hb ⟨c, i, eL, eR⟩
  let S : Finset (Fin n) := Finset.univ.filter fun t : Fin n => (e.1 t.succ : ℕ) < (e.1 0 : ℕ)
  have he0 : (e.1 0 : ℕ) = (c : ℕ) := invFunVal_zero hb c i eL eR 0 rfl
  have hmem_iff : ∀ t : Fin n, t ∈ S ↔ (i : ℕ) ≤ (t : ℕ) := by
    intro t
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, he0]
    constructor
    · intro hlt
      by_contra hlti
      have hts : (t.succ : ℕ) ≠ 0 := by simp
      have hti : (t.succ : ℕ) ≤ (i : ℕ) := by simp; omega
      have hv := invFunVal_left hb c i eL eR t.succ hts hti
      change (invFunVal hb c i eL eR t.succ : ℕ) < (c : ℕ) at hlt
      omega
    · intro hle
      have hti : (i : ℕ) < (t.succ : ℕ) := by simp; omega
      have hv := invFunVal_right hb c i eL eR t.succ hti
      change (invFunVal hb c i eL eR t.succ : ℕ) < (c : ℕ)
      rw [hv]
      exact (eR.1 ⟨(t.succ : ℕ) - (i : ℕ) - 1, by omega⟩).2
  apply Fin.ext
  by_cases hin : (i : ℕ) < n
  · let i' : Fin n := ⟨(i : ℕ), hin⟩
    have hi'mem : i' ∈ S := (hmem_iff i').mpr (le_refl _)
    have hne : S.Nonempty := ⟨i', hi'mem⟩
    have hmin_eq : S.min' hne = i' := by
      apply le_antisymm
      · exact Finset.min'_le S i' hi'mem
      · exact (hmem_iff (S.min' hne)).mp (Finset.min'_mem S hne)
    change (splitIdx e : ℕ) = (i : ℕ)
    simp [splitIdx, S, hne, hmin_eq, i']
  · have hnot : ¬ S.Nonempty := by
      rintro ⟨t, ht⟩
      have hle := (hmem_iff t).mp ht
      omega
    change (splitIdx e : ℕ) = (i : ℕ)
    have hieq : (i : ℕ) = n := by omega
    simp [splitIdx, S, hnot, hieq]

private lemma sigma_decomp_ext {n : ℕ} {b : ℕ → ℕ}
    {c1 c2 : Fin (b 0)} {i1 i2 : Fin (n + 1)}
    {p1 : G i1 (fun t => b (t + 1) - c1) × G (n - i1) (fun _ => c1)}
    {p2 : G i2 (fun t => b (t + 1) - c2) × G (n - i2) (fun _ => c2)}
    (hc : c1 = c2) (hi : i1 = i2)
    (hL : ∀ (t : ℕ) (ht1 : t < (i1 : ℕ)) (ht2 : t < (i2 : ℕ)),
      (p1.1.1 ⟨t, ht1⟩ : ℕ) = (p2.1.1 ⟨t, ht2⟩ : ℕ))
    (hR : ∀ (s : ℕ) (hs1 : s < n - (i1 : ℕ)) (hs2 : s < n - (i2 : ℕ)),
      (p1.2.1 ⟨s, hs1⟩ : ℕ) = (p2.2.1 ⟨s, hs2⟩ : ℕ)) :
    (⟨c1, i1, p1⟩ : Σ (c : Fin (b 0)) (i : Fin (n + 1)),
      G i (fun t => b (t + 1) - c) × G (n - i) (fun _ => c)) = ⟨c2, i2, p2⟩ := by
  subst hc
  subst hi
  congr 1
  congr 1
  ext1
  · exact Subtype.ext (funext fun t => Fin.ext (hL t t.2 t.2))
  · exact Subtype.ext (funext fun s => Fin.ext (hR s s.2 s.2))

private lemma card_G_succ (n : ℕ) (b : ℕ → ℕ) (hb : Monotone b) :
    Fintype.card (G (n + 1) b) =
    ∑ c ∈ Finset.range (b 0), ∑ i ∈ Finset.range (n + 1),
      Fintype.card (G i (fun t => b (t + 1) - c)) *
        Fintype.card (G (n - i) (fun _ => c)) := by
  have heq : Fintype.card (G (n + 1) b) =
      Fintype.card (Σ (c : Fin (b 0)) (i : Fin (n + 1)),
        G i (fun t => b (t + 1) - c) × G (n - i) (fun _ => c)) := by
    refine Fintype.card_congr
      { toFun := decompToFun
        invFun := decompInvFun hb
        left_inv := fun e => by
          apply Subtype.ext
          funext j
          apply Fin.ext
          by_cases hj0 : (j : ℕ) = 0
          · have hv := invFunVal_zero hb (e.1 0) (splitIdx e)
              (decompToFun e).2.2.1 (decompToFun e).2.2.2 j hj0
            have hj : j = 0 := Fin.ext hj0
            change (invFunVal hb (e.1 0) (splitIdx e)
              (decompToFun e).2.2.1 (decompToFun e).2.2.2 j : ℕ) = (e.1 j : ℕ)
            rw [hv, hj]
          · by_cases hji : (j : ℕ) ≤ (splitIdx e : ℕ)
            · have hv := invFunVal_left hb (e.1 0) (splitIdx e)
                (decompToFun e).2.2.1 (decompToFun e).2.2.2 j hj0 hji
              change (invFunVal hb (e.1 0) (splitIdx e)
                (decompToFun e).2.2.1 (decompToFun e).2.2.2 j : ℕ) = (e.1 j : ℕ)
              rw [hv]
              have hge := splitIdx_left e ⟨(j : ℕ) - 1, by omega⟩
              have hidx : (⟨(j : ℕ) - 1 + 1, by omega⟩ : Fin (n + 1)) = j :=
                Fin.ext (by dsimp only; omega)
              change (e.1 ⟨(j : ℕ) - 1 + 1, by omega⟩ : ℕ) - (e.1 0 : ℕ) + (e.1 0 : ℕ) = (e.1 j : ℕ)
              rw [hidx] at hge ⊢
              omega
            · have hji' : (splitIdx e : ℕ) < (j : ℕ) := by omega
              have hv := invFunVal_right hb (e.1 0) (splitIdx e)
                (decompToFun e).2.2.1 (decompToFun e).2.2.2 j hji'
              change (invFunVal hb (e.1 0) (splitIdx e)
                (decompToFun e).2.2.1 (decompToFun e).2.2.2 j : ℕ) = (e.1 j : ℕ)
              rw [hv]
              have hidx : (⟨(splitIdx e : ℕ) + 1 + ((j : ℕ) - (splitIdx e : ℕ) - 1), by omega⟩ :
                  Fin (n + 1)) = j := Fin.ext (by dsimp only; omega)
              change (e.1 ⟨(splitIdx e : ℕ) + 1 + ((j : ℕ) - (splitIdx e : ℕ) - 1), by omega⟩ : ℕ) =
                (e.1 j : ℕ)
              rw [hidx]
        right_inv := fun ⟨c, i, eL, eR⟩ => by
          have hc : (decompInvFun hb ⟨c, i, eL, eR⟩).1 0 = c :=
            Fin.ext (invFunVal_zero hb c i eL eR 0 rfl)
          have hi : splitIdx (decompInvFun hb ⟨c, i, eL, eR⟩) = i :=
            splitIdx_decompInvFun hb c i eL eR
          refine sigma_decomp_ext hc hi ?_ ?_
          · intro t ht1 ht2
            have h0 : (⟨t + 1, by omega⟩ : Fin (n + 1)).val ≠ 0 := by simp
            have hle : (⟨t + 1, by omega⟩ : Fin (n + 1)).val ≤ (i : ℕ) := by simp; omega
            have hv := invFunVal_left hb c i eL eR ⟨t + 1, by omega⟩ h0 hle
            have hv0 := invFunVal_zero hb c i eL eR 0 rfl
            change (invFunVal hb c i eL eR ⟨t + 1, by omega⟩ : ℕ) -
                (invFunVal hb c i eL eR 0 : ℕ) = (eL.1 ⟨t, ht2⟩ : ℕ)
            rw [hv, hv0]
            have hsub : (⟨t + 1 - 1, by omega⟩ : Fin i) = ⟨t, ht2⟩ := Fin.ext (by simp)
            rw [hsub]
            omega
          · intro s hs1 hs2
            have hi_val : (splitIdx (decompInvFun hb ⟨c, i, eL, eR⟩) : ℕ) = (i : ℕ) :=
              congrArg Fin.val hi
            have hlt : (i : ℕ) < (⟨(splitIdx (decompInvFun hb ⟨c, i, eL, eR⟩) : ℕ) + 1 + s,
                by omega⟩ : Fin (n + 1)).val := by
              dsimp only
              omega
            have hv := invFunVal_right hb c i eL eR
              ⟨(splitIdx (decompInvFun hb ⟨c, i, eL, eR⟩) : ℕ) + 1 + s, by omega⟩ hlt
            change (invFunVal hb c i eL eR
              ⟨(splitIdx (decompInvFun hb ⟨c, i, eL, eR⟩) : ℕ) + 1 + s, by omega⟩ : ℕ) =
              (eR.1 ⟨s, hs2⟩ : ℕ)
            rw [hv]
            have hsub : (⟨(splitIdx (decompInvFun hb ⟨c, i, eL, eR⟩) : ℕ) + 1 + s - (i : ℕ) - 1,
                by omega⟩ : Fin (n - i)) = ⟨s, hs2⟩ := Fin.ext (by dsimp only; omega)
            rw [hsub] }
  rw [heq, Fintype.card_sigma]
  simp only [Fintype.card_sigma, Fintype.card_prod]
  rw [Fin.sum_univ_eq_sum_range (fun c => ∑ i : Fin (n + 1),
    Fintype.card (G i (fun t => b (t + 1) - c)) * Fintype.card (G (n - i) (fun _ => c)))]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Fin.sum_univ_eq_sum_range (fun i =>
    Fintype.card (G i (fun t => b (t + 1) - c)) * Fintype.card (G (n - i) (fun _ => c)))]

private noncomputable def countU (n r : ℕ) : ℕ :=
  Fintype.card (G n (fun _ => r))

private noncomputable def countS (n k : ℕ) : ℕ :=
  Fintype.card (G n (fun j => j + k + 1))

private lemma countS_zero_eq_count (n : ℕ) : countS n 0 = count n := by
  unfold countS G count
  exact Fintype.card_of_subtype _ (fun _ => by simp)

private lemma countU_zero (r : ℕ) : countU 0 r = 1 :=
  card_G_zero (fun _ => r)

private lemma countS_zero (k : ℕ) : countS 0 k = 1 :=
  card_G_zero (fun j => j + k + 1)

private lemma countU_succ (n r : ℕ) :
    countU (n + 1) r =
    ∑ c ∈ Finset.range r, ∑ i ∈ Finset.range (n + 1), countU i (r - c) * countU (n - i) c := by
  exact card_G_succ n (fun _ => r) monotone_const

private lemma countS_succ (n k : ℕ) :
    countS (n + 1) k =
    ∑ c ∈ Finset.range (k + 1), ∑ i ∈ Finset.range (n + 1),
      countS i (k + 1 - c) * countU (n - i) c := by
  have hmono : Monotone (fun j : ℕ => j + k + 1) := fun a b hab => by
    dsimp only
    omega
  have h := card_G_succ n (fun j => j + k + 1) hmono
  change countS (n + 1) k = _ at h
  rw [Nat.zero_add] at h
  rw [h]
  refine Finset.sum_congr rfl fun c hc => ?_
  have hck : c ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hc)
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  exact card_G_congr i fun t _ => by omega

private noncomputable def U (r : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun n => (countU n r : ℤ)

private noncomputable def S (k : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun n => (countS n k : ℤ)

private lemma coeff_mul_eq_sum_range (φ ψ : PowerSeries ℤ) (n : ℕ) :
    coeff n (φ * ψ) = ∑ k ∈ Finset.range (n + 1), coeff k φ * coeff (n - k) ψ := by
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i φ * coeff j ψ) n]

private lemma U_zero : U 0 = 1 := by
  ext n
  cases n with
  | zero =>
    rw [U, PowerSeries.coeff_mk, PowerSeries.coeff_one, countU_zero]
    simp
  | succ n =>
    rw [U, PowerSeries.coeff_mk, PowerSeries.coeff_one, countU_succ]
    simp

private lemma U_eq (r : ℕ) :
    U r = 1 + PowerSeries.X * ∑ c ∈ Finset.range r, U (r - c) * U c := by
  ext n
  cases n with
  | zero =>
    rw [U, PowerSeries.coeff_mk, map_add, PowerSeries.coeff_one, coeff_zero_X_mul, countU_zero]
    simp
  | succ n =>
    rw [U, PowerSeries.coeff_mk, map_add, PowerSeries.coeff_one, coeff_succ_X_mul, map_sum]
    have h1 : (if n + 1 = 0 then (1 : ℤ) else 0) = 0 := by simp
    rw [h1, zero_add]
    have hnat : countU (n + 1) r =
        ∑ c ∈ Finset.range r, ∑ i ∈ Finset.range (n + 1), countU i (r - c) * countU (n - i) c :=
      countU_succ n r
    have hint : (countU (n + 1) r : ℤ) =
        ∑ c ∈ Finset.range r, ∑ i ∈ Finset.range (n + 1),
          (countU i (r - c) : ℤ) * (countU (n - i) c : ℤ) := by
      exact_mod_cast hnat
    rw [hint]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [coeff_mul_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [U]

private lemma S_eq (k : ℕ) :
    S k = 1 + PowerSeries.X * ∑ r ∈ Finset.range (k + 1), S (k + 1 - r) * U r := by
  ext n
  cases n with
  | zero =>
    rw [S, PowerSeries.coeff_mk, map_add, PowerSeries.coeff_one, coeff_zero_X_mul, countS_zero]
    simp
  | succ n =>
    rw [S, PowerSeries.coeff_mk, map_add, PowerSeries.coeff_one, coeff_succ_X_mul, map_sum]
    have h1 : (if n + 1 = 0 then (1 : ℤ) else 0) = 0 := by simp
    rw [h1, zero_add]
    have hnat : countS (n + 1) k =
        ∑ r ∈ Finset.range (k + 1), ∑ i ∈ Finset.range (n + 1),
          countS i (k + 1 - r) * countU (n - i) r :=
      countS_succ n k
    have hint : (countS (n + 1) k : ℤ) =
        ∑ r ∈ Finset.range (k + 1), ∑ i ∈ Finset.range (n + 1),
          (countS i (k + 1 - r) : ℤ) * (countU (n - i) r : ℤ) := by
      exact_mod_cast hnat
    rw [hint]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [coeff_mul_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [S, U]

private lemma coeff_mul_congr {P1 P2 Q1 Q2 : PowerSeries ℤ} {n : ℕ}
    (hP : ∀ m ≤ n, coeff m P1 = coeff m P2)
    (hQ : ∀ m ≤ n, coeff m Q1 = coeff m Q2) :
    coeff n (P1 * Q1) = coeff n (P2 * Q2) := by
  rw [coeff_mul_eq_sum_range, coeff_mul_eq_sum_range]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [hP k hkn, hQ (n - k) (by omega)]

private lemma coeff_pow_eq_zero {Y : PowerSeries ℤ} (hY0 : constantCoeff Y = 0) :
    ∀ r n : ℕ, n < r → coeff n (Y ^ r) = 0 := by
  intro r
  induction r with
  | zero =>
    intro n hn
    omega
  | succ r ih =>
    intro n hn
    rw [pow_succ, coeff_mul_eq_sum_range]
    refine Finset.sum_eq_zero fun k hk => ?_
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    by_cases hkeq : k = n
    · subst hkeq
      rw [Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff, hY0, mul_zero]
    · rw [ih k (by omega), zero_mul]

private lemma coeff_mul_pow_eq_zero {Y : PowerSeries ℤ} (hY0 : constantCoeff Y = 0)
    (f : PowerSeries ℤ) (r n : ℕ) (hr : n < r) :
    coeff n (f * Y ^ r) = 0 := by
  rw [coeff_mul_eq_sum_range]
  refine Finset.sum_eq_zero fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [coeff_pow_eq_zero hY0 r (n - k) (by omega), mul_zero]

private noncomputable def evalY (Y : PowerSeries ℤ) (F : ℕ → PowerSeries ℤ) : PowerSeries ℤ :=
  PowerSeries.mk fun n => ∑ r ∈ Finset.range (n + 1), coeff n (F r * Y ^ r)

private lemma coeff_evalY_eq_sum {Y : PowerSeries ℤ} (hY0 : constantCoeff Y = 0)
    (F : ℕ → PowerSeries ℤ) (n N : ℕ) (hN : n < N) :
    coeff n (evalY Y F) = ∑ r ∈ Finset.range N, coeff n (F r * Y ^ r) := by
  rw [evalY, PowerSeries.coeff_mk]
  refine Finset.sum_subset (Finset.range_mono (by omega)) ?_
  intro r hr hnot
  have hlt : n < r := by
    simp only [Finset.mem_range] at hnot
    omega
  exact coeff_mul_pow_eq_zero hY0 (F r) r n hlt

private lemma evalY_congr {Y : PowerSeries ℤ} {F G : ℕ → PowerSeries ℤ}
    (h : ∀ r, F r = G r) : evalY Y F = evalY Y G := by
  ext n
  simp only [evalY, PowerSeries.coeff_mk]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [h r]

private lemma evalY_add {Y : PowerSeries ℤ} (F G : ℕ → PowerSeries ℤ) :
    evalY Y (fun r => F r + G r) = evalY Y F + evalY Y G := by
  ext n
  simp only [evalY, map_add, PowerSeries.coeff_mk, add_mul, Finset.sum_add_distrib]

private lemma evalY_mul_left {Y : PowerSeries ℤ} (hY0 : constantCoeff Y = 0)
    (P : PowerSeries ℤ) (F : ℕ → PowerSeries ℤ) :
    evalY Y (fun r => P * F r) = P * evalY Y F := by
  ext n
  have hagree : ∀ m ≤ n, coeff m (evalY Y F) =
      coeff m (∑ r ∈ Finset.range (n + 1), F r * Y ^ r) := by
    intro m hm
    rw [coeff_evalY_eq_sum hY0 F m (n + 1) (by omega), map_sum]
  rw [coeff_mul_congr (fun _ _ => rfl) hagree, Finset.mul_sum, map_sum,
    evalY, PowerSeries.coeff_mk]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [mul_assoc]

private lemma one_sub_mul_geom_sum (Y : PowerSeries ℤ) : ∀ N : ℕ,
    (1 - Y) * ∑ r ∈ Finset.range N, Y ^ r = 1 - Y ^ N := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, mul_add, ih, pow_succ]
    ring

private lemma one_sub_Y_mul_evalY_one {Y : PowerSeries ℤ} (hY0 : constantCoeff Y = 0) :
    (1 - Y) * evalY Y (fun _ => 1) = 1 := by
  ext n
  have hagree : ∀ m ≤ n, coeff m (evalY Y (fun _ => 1)) =
      coeff m (∑ r ∈ Finset.range (n + 1), Y ^ r) := by
    intro m hm
    rw [coeff_evalY_eq_sum hY0 (fun _ => 1) m (n + 1) (by omega), map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [one_mul]
  rw [coeff_mul_congr (fun _ _ => rfl) hagree, one_sub_mul_geom_sum, map_sub,
    coeff_pow_eq_zero hY0 (n + 1) n (Nat.lt_succ_self n), sub_zero]

private lemma evalY_conv {Y : PowerSeries ℤ} (hY0 : constantCoeff Y = 0)
    (F G : ℕ → PowerSeries ℤ) :
    evalY Y (fun r => ∑ c ∈ Finset.range r, F (r - c) * G c) =
    (evalY Y F - F 0) * evalY Y G := by
  ext n
  have hF : ∀ m ≤ n, coeff m (evalY Y F - F 0) =
      coeff m (∑ a ∈ Finset.Ico 1 (n + 1), F a * Y ^ a) := by
    intro m hm
    rw [map_sub, coeff_evalY_eq_sum hY0 F m (n + 1) (by omega), map_sum]
    have hsplit : Finset.range (n + 1) = insert 0 (Finset.Ico 1 (n + 1)) := by
      ext r
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]
      omega
    have hnot : (0 : ℕ) ∉ Finset.Ico 1 (n + 1) := by simp
    rw [hsplit, Finset.sum_insert hnot, pow_zero, mul_one, add_sub_cancel_left]
  have hG : ∀ m ≤ n, coeff m (evalY Y G) =
      coeff m (∑ c ∈ Finset.range (n + 1), G c * Y ^ c) := by
    intro m hm
    rw [coeff_evalY_eq_sum hY0 G m (n + 1) (by omega), map_sum]
  rw [coeff_mul_congr hF hG, Finset.sum_mul, map_sum]
  have hRHS :
      ∑ a ∈ Finset.Ico 1 (n + 1),
        coeff n (F a * Y ^ a * ∑ c ∈ Finset.range (n + 1), G c * Y ^ c) =
      ∑ p ∈ (Finset.Ico 1 (n + 1) ×ˢ Finset.range (n + 1)).filter (fun p => p.1 + p.2 ≤ n),
        coeff n (F p.1 * G p.2 * Y ^ (p.1 + p.2)) := by
    calc
      ∑ a ∈ Finset.Ico 1 (n + 1),
          coeff n (F a * Y ^ a * ∑ c ∈ Finset.range (n + 1), G c * Y ^ c)
        = ∑ a ∈ Finset.Ico 1 (n + 1), ∑ c ∈ Finset.range (n + 1),
            coeff n (F a * G c * Y ^ (a + c)) := by
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [Finset.mul_sum, map_sum]
            refine Finset.sum_congr rfl fun c _ => ?_
            rw [pow_add]
            congr 1
            ring
      _ = ∑ p ∈ Finset.Ico 1 (n + 1) ×ˢ Finset.range (n + 1),
            coeff n (F p.1 * G p.2 * Y ^ (p.1 + p.2)) := by
            rw [Finset.sum_product]
      _ = ∑ p ∈ (Finset.Ico 1 (n + 1) ×ˢ Finset.range (n + 1)).filter (fun p => p.1 + p.2 ≤ n),
            coeff n (F p.1 * G p.2 * Y ^ (p.1 + p.2)) := by
            symm
            refine Finset.sum_subset (Finset.filter_subset _ _) ?_
            intro p hp hnot
            simp only [Finset.mem_filter] at hnot
            have hlt : n < p.1 + p.2 := by
              have : ¬ p.1 + p.2 ≤ n := fun hle => hnot ⟨hp, hle⟩
              omega
            exact coeff_mul_pow_eq_zero hY0 (F p.1 * G p.2) (p.1 + p.2) n hlt
  rw [hRHS, evalY, PowerSeries.coeff_mk]
  have hLHS :
      ∑ r ∈ Finset.range (n + 1),
        coeff n ((∑ c ∈ Finset.range r, F (r - c) * G c) * Y ^ r) =
      ∑ p ∈ (Finset.range (n + 1)).sigma (fun r => Finset.range r),
        coeff n (F (p.1 - p.2) * G p.2 * Y ^ p.1) := by
    calc
      ∑ r ∈ Finset.range (n + 1),
          coeff n ((∑ c ∈ Finset.range r, F (r - c) * G c) * Y ^ r)
        = ∑ r ∈ Finset.range (n + 1), ∑ c ∈ Finset.range r,
            coeff n (F (r - c) * G c * Y ^ r) := by
            refine Finset.sum_congr rfl fun r _ => ?_
            rw [Finset.sum_mul, map_sum]
      _ = ∑ p ∈ (Finset.range (n + 1)).sigma (fun r => Finset.range r),
            coeff n (F (p.1 - p.2) * G p.2 * Y ^ p.1) := by
            rw [Finset.sum_sigma']
  rw [hLHS]
  refine Finset.sum_bij (fun p _ => (p.1 - p.2, p.2)) ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_filter, Finset.mem_product,
      Finset.mem_Ico] at hp ⊢
    omega
  · rintro ⟨r1, c1⟩ hp1 ⟨r2, c2⟩ hp2 heq
    simp only [Finset.mem_sigma, Finset.mem_range] at hp1 hp2
    have hfst : r1 - c1 = r2 - c2 := congrArg Prod.fst heq
    have hsnd : c1 = c2 := congrArg Prod.snd heq
    have hr : r1 = r2 := by omega
    subst hr
    subst hsnd
    rfl
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Ico, Finset.mem_range] at hq
    refine ⟨⟨q.1 + q.2, q.2⟩, ?_, ?_⟩
    · simp only [Finset.mem_sigma, Finset.mem_range]
      omega
    · ext <;> simp
  · intro p hp
    simp only [Finset.mem_sigma, Finset.mem_range] at hp
    have hadd : p.1 - p.2 + p.2 = p.1 := by omega
    rw [hadd]

private lemma Y_mul_evalY_shift {Y : PowerSeries ℤ} (hY0 : constantCoeff Y = 0)
    (H : ℕ → PowerSeries ℤ) (hH0 : H 0 = 0) :
    Y * evalY Y (fun k => H (k + 1)) = evalY Y H := by
  ext n
  have hagree : ∀ m ≤ n, coeff m (evalY Y (fun k => H (k + 1))) =
      coeff m (∑ k ∈ Finset.range (n + 1), H (k + 1) * Y ^ k) := by
    intro m hm
    rw [coeff_evalY_eq_sum hY0 (fun k => H (k + 1)) m (n + 1) (by omega), map_sum]
  rw [coeff_mul_congr (fun _ _ => rfl) hagree, Finset.mul_sum, map_sum,
    coeff_evalY_eq_sum hY0 H n (n + 2) (by omega)]
  rw [Finset.sum_range_succ' (fun m => coeff n (H m * Y ^ m)) (n + 1), hH0, zero_mul, map_zero,
    add_zero]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [pow_succ]
  congr 1
  ring

private lemma Y_mul_evalY_conv {Y : PowerSeries ℤ} (hY0 : constantCoeff Y = 0)
    (F G : ℕ → PowerSeries ℤ) :
    Y * evalY Y (fun k => ∑ r ∈ Finset.range (k + 1), F (k + 1 - r) * G r) =
    (evalY Y F - F 0) * evalY Y G := by
  let H : ℕ → PowerSeries ℤ := fun m => ∑ r ∈ Finset.range m, F (m - r) * G r
  have hH0 : H 0 = 0 := by simp [H]
  calc
    Y * evalY Y (fun k => ∑ r ∈ Finset.range (k + 1), F (k + 1 - r) * G r)
      = Y * evalY Y (fun k => H (k + 1)) := rfl
    _ = evalY Y H := Y_mul_evalY_shift hY0 H hH0
    _ = (evalY Y F - F 0) * evalY Y G := evalY_conv hY0 F G

theorem OMA.solution : type_of% @OMA.S_oeis_a106228.main := by
  intro A hA0 hAeq
  have hconst : PowerSeries.constantCoeff (1 - PowerSeries.X * A ^ 2) = ((1 : ℤˣ) : ℤ) := by
    simp [map_sub, map_one, map_mul, PowerSeries.constantCoeff_X]
  let W : PowerSeries ℤ := PowerSeries.invOfUnit (1 - PowerSeries.X * A ^ 2) 1
  let Y : PowerSeries ℤ := PowerSeries.X * W
  have hW_inv : W * (1 - PowerSeries.X * A ^ 2) = 1 :=
    PowerSeries.invOfUnit_mul (1 - PowerSeries.X * A ^ 2) 1 hconst
  have hY0 : PowerSeries.constantCoeff Y = 0 := by
    simp [Y, map_mul, PowerSeries.constantCoeff_X]
  have hW_sub : W - 1 = PowerSeries.X * A ^ 2 * W := by
    linear_combination hW_inv
  have hA_sub : A - 1 = PowerSeries.X * A * W := by
    have hmul := congrArg (fun z => W * z) hAeq
    linear_combination hmul - A * hW_inv + hW_inv
  have hA_one_sub_Y : A * (1 - Y) = 1 := by
    have hY : Y = PowerSeries.X * W := rfl
    linear_combination hA_sub + A * hY
  have hW_quad : W = A + PowerSeries.X * (W - 1) * W := by
    linear_combination hW_sub - hA_sub + PowerSeries.X * A * W * hA_sub -
      PowerSeries.X * W * hW_sub
  have heval1 : evalY Y (fun _ => 1) = A := by
    calc
      evalY Y (fun _ => 1)
        = (A * (1 - Y)) * evalY Y (fun _ => 1) := by rw [hA_one_sub_Y, one_mul]
      _ = A * ((1 - Y) * evalY Y (fun _ => 1)) := by rw [mul_assoc]
      _ = A * 1 := by rw [one_sub_Y_mul_evalY_one hY0]
      _ = A := by rw [mul_one]
  have hEU_quad : evalY Y U = A + PowerSeries.X * (evalY Y U - 1) * evalY Y U := by
    calc
      evalY Y U
        = evalY Y (fun r => 1 + PowerSeries.X * ∑ c ∈ Finset.range r, U (r - c) * U c) :=
            evalY_congr U_eq
      _ = evalY Y (fun _ => 1) +
            evalY Y (fun r => PowerSeries.X * ∑ c ∈ Finset.range r, U (r - c) * U c) :=
            evalY_add _ _
      _ = A + PowerSeries.X * evalY Y (fun r => ∑ c ∈ Finset.range r, U (r - c) * U c) := by
            rw [heval1, evalY_mul_left hY0]
      _ = A + PowerSeries.X * ((evalY Y U - U 0) * evalY Y U) := by
            rw [evalY_conv hY0 U U]
      _ = A + PowerSeries.X * (evalY Y U - 1) * evalY Y U := by
            rw [U_zero, mul_assoc]
  have hEU_eq_W : evalY Y U = W := by
    ext n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      rw [hEU_quad, hW_quad, map_add, map_add]
      congr 1
      cases n with
      | zero =>
        rw [mul_assoc PowerSeries.X, mul_assoc PowerSeries.X, coeff_zero_X_mul, coeff_zero_X_mul]
      | succ k =>
        rw [mul_assoc PowerSeries.X, mul_assoc PowerSeries.X, coeff_succ_X_mul, coeff_succ_X_mul]
        refine coeff_mul_congr ?_ ?_
        · intro m hm
          rw [map_sub, map_sub, ih m (by omega)]
        · intro m hm
          exact ih m (by omega)
  have hXEU : PowerSeries.X * evalY Y U = Y := by
    rw [hEU_eq_W]
  have hYS : Y * evalY Y S = Y * A + Y * (evalY Y S - S 0) := by
    calc
      Y * evalY Y S
        = Y * evalY Y (fun k => 1 + PowerSeries.X *
            ∑ r ∈ Finset.range (k + 1), S (k + 1 - r) * U r) := by
            rw [evalY_congr S_eq]
      _ = Y * (evalY Y (fun _ => 1) +
            PowerSeries.X * evalY Y (fun k =>
              ∑ r ∈ Finset.range (k + 1), S (k + 1 - r) * U r)) := by
            rw [evalY_add, evalY_mul_left hY0]
      _ = Y * A + PowerSeries.X * (Y * evalY Y (fun k =>
            ∑ r ∈ Finset.range (k + 1), S (k + 1 - r) * U r)) := by
            rw [heval1]
            ring
      _ = Y * A + PowerSeries.X * ((evalY Y S - S 0) * evalY Y U) := by
            rw [Y_mul_evalY_conv hY0 S U]
      _ = Y * A + (PowerSeries.X * evalY Y U) * (evalY Y S - S 0) := by
            ring
      _ = Y * A + Y * (evalY Y S - S 0) := by
            rw [hXEU]
  have hY_zero : Y * (A - S 0) = 0 := by
    linear_combination -hYS
  have hX_zero : PowerSeries.X * (A - S 0) = 0 := by
    have hY : Y = PowerSeries.X * W := rfl
    linear_combination (1 - PowerSeries.X * A ^ 2) * hY_zero -
      PowerSeries.X * (A - S 0) * hW_inv - (1 - PowerSeries.X * A ^ 2) * (A - S 0) * hY
  intro n
  have hcoeff : coeff n (A - S 0) = 0 := by
    have h := congrArg (PowerSeries.coeff (n + 1)) hX_zero
    rw [coeff_succ_X_mul, map_zero] at h
    exact h
  rw [map_sub, sub_eq_zero] at hcoeff
  rw [hcoeff, S, PowerSeries.coeff_mk, countS_zero_eq_count]
