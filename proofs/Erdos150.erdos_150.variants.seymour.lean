import FormalConjectures.ErdosProblems.«150»

/-! Seymour's lower bound $c(3m+2) \ge 3^m$ via $m$ paths of length 4. -/

-- This shortens the proof originally submitted by Genbox in PR #217.

open SimpleGraph

theorem OMA.solution : type_of% @Erdos150.erdos_150.variants.seymour := by
  intro m
  classical
  let L : Fin (3 * m + 2) := ⟨3 * m, by omega⟩
  let R : Fin (3 * m + 2) := ⟨3 * m + 1, by omega⟩
  let p (i : Fin m) (k : ℕ) : Fin (3 * m + 2) :=
    if h : 1 ≤ k ∧ k ≤ 3 then ⟨3 * i + k - 1, by omega⟩ else if k = 0 then L else R
  let G : SimpleGraph (Fin (3 * m + 2)) :=
    fromRel fun a b => ∃ (i : Fin m) (k : ℕ), k < 4 ∧ a = p i k ∧ b = p i (k + 1)
  let T (f : Fin m → Fin 3) : Set (Fin (3 * m + 2)) :=
    Set.range fun i => p i ((f i).1 + 1)
  have hp_eq {i i' : Fin m} {k k' : ℕ} (hk' : 1 ≤ k' ∧ k' ≤ 3) (h : p i k = p i' k') :
      i = i' ∧ k = k' := by
    have h := congrArg Fin.val h
    dsimp [p, L, R] at h; split_ifs at h <;> dsimp at h <;>
      first | omega | exact ⟨Fin.ext (by omega), by omega⟩
  have hmem (f : Fin m → Fin 3) (i : Fin m) (k : ℕ) : p i k ∈ T f ↔ k = (f i).1 + 1 :=
    ⟨fun ⟨i', hi'⟩ => by obtain ⟨rfl, rfl⟩ := hp_eq (by omega) hi'.symm; rfl,
     fun h => ⟨i, h ▸ rfl⟩⟩
  have hT_lt {f : Fin m → Fin 3} {v : Fin (3 * m + 2)} (hv : v ∈ T f) : v.1 < 3 * m := by
    rcases hv with ⟨i, rfl⟩; dsimp [p, L, R]; split_ifs <;> dsimp <;> omega
  have hadj (i : Fin m) (k : ℕ) (hk : k < 4) : G.Adj (p i k) (p i (k + 1)) :=
    ⟨fun h => by
      have := congrArg Fin.val h
      dsimp [p, L, R] at this; split_ifs at this <;> dsimp at this <;> omega,
     Or.inl ⟨i, k, hk, rfl, rfl⟩⟩
  have hcut (f : Fin m → Fin 3) : Erdos150.IsMinimalCut G (T f) := by
    refine ⟨?_, ?_⟩
    · intro hcon
      let left (v : Fin (3 * m + 2)) : Prop :=
        v.1 = 3 * m ∨ ∃ (i : Fin m) (k : ℕ), k ≤ (f i).1 ∧ v = p i k
      have hleft (i : Fin m) (k : ℕ) : left (p i k) ↔ k ≤ (f i).1 := by
        refine ⟨?_, fun hk => Or.inr ⟨i, k, hk, rfl⟩⟩
        rintro (h | ⟨i', k', hk', h⟩)
        · dsimp [p, L, R] at h; split_ifs at h <;> dsimp at h <;> omega
        · by_cases hk0 : k' = 0
          · subst hk0; have h := congrArg Fin.val h
            dsimp [p, L, R] at h; split_ifs at h <;> dsimp at h <;> omega
          · obtain ⟨rfl, rfl⟩ := hp_eq (by omega) h; exact hk'
      have hstep {u v : Fin (3 * m + 2)} (hu : u ∉ T f) (hv : v ∉ T f)
          (h : G.Adj u v) : left u ↔ left v := by
        have h1 {a b} (hb : b ∉ T f)
            (h : ∃ (i : Fin m) (k : ℕ), k < 4 ∧ a = p i k ∧ b = p i (k + 1)) :
            left a ↔ left b := by
          rcases h with ⟨i, k, hk, rfl, rfl⟩
          rw [hleft, hleft]
          have : k + 1 ≠ (f i).1 + 1 := fun he => hb ((hmem f i (k + 1)).mpr he)
          omega
        rcases h.2 with h | h
        · exact h1 hv h
        · exact (h1 hu h).symm
      have hwalk {u v : ↥(T f)ᶜ} (w : (G.induce (T f)ᶜ).Walk u v) : left u.1 → left v.1 := by
        induction w with
        | nil => exact id
        | @cons a b _ hadj _ ih => exact fun ha => ih ((hstep a.2 b.2 hadj).mp ha)
      have hL : L ∉ T f := fun h => by have := hT_lt h; dsimp [L] at this; omega
      have hR : R ∉ T f := fun h => by have := hT_lt h; dsimp [R] at this; omega
      obtain ⟨w⟩ := hcon ⟨L, hL⟩ ⟨R, hR⟩
      rcases hwalk w (Or.inl rfl) with h | ⟨i, k, hk, h⟩
      · dsimp [R] at h; omega
      · have h := congrArg Fin.val h
        dsimp [p, L, R] at h; split_ifs at h <;> dsimp at h <;> omega
    · intro S hS
      have hL : L ∉ S := fun h => by have := hT_lt (hS.1 h); dsimp [L] at this; omega
      have hR : R ∉ S := fun h => by have := hT_lt (hS.1 h); dsimp [R] at this; omega
      have hfree (i : Fin m) (k : ℕ) (hk : k ≠ (f i).1 + 1) : p i k ∉ S :=
        fun h => hk ((hmem f i k).mp (hS.1 h))
      have hseg (i : Fin m) (a b : ℕ) (hab : a ≤ b) (hb : b ≤ 4)
          (h : ∀ k, a ≤ k → k ≤ b → p i k ∉ S) :
          (G.induce Sᶜ).Reachable ⟨p i a, h a le_rfl hab⟩ ⟨p i b, h b hab le_rfl⟩ := by
        induction b, hab using Nat.le_induction with
        | base => exact .rfl
        | succ k hak ih =>
          exact (ih (by omega) fun t ht1 ht2 => h t ht1 (by omega)).trans
            (show (G.induce Sᶜ).Adj ⟨p i k, _⟩ ⟨p i (k + 1), _⟩ from hadj i k (by omega)).reachable
      obtain ⟨_, ⟨i₀, rfl⟩, hi₀⟩ := Set.exists_of_ssubset hS
      have hi₀_all (k : ℕ) : p i₀ k ∉ S := by
        by_cases hk : k = (f i₀).1 + 1
        · exact hk ▸ hi₀
        · exact hfree i₀ k hk
      have hLR : (G.induce Sᶜ).Reachable ⟨L, hL⟩ ⟨R, hR⟩ := by
        simpa [p] using hseg i₀ 0 4 (by omega) le_rfl fun k _ _ => hi₀_all k
      have hfromL (v : ↥Sᶜ) : (G.induce Sᶜ).Reachable ⟨L, hL⟩ v := by
        rcases v with ⟨v, hv⟩
        by_cases hv1 : v.1 < 3 * m
        · let i : Fin m := ⟨v.1 / 3, by omega⟩
          let k : ℕ := v.1 % 3 + 1
          have hk_range : 1 ≤ k ∧ k ≤ 3 := by dsimp [k]; omega
          have hpv : p i k = v := by
            apply Fin.ext
            simp only [p, dif_pos hk_range]
            change 3 * (v.val / 3) + (v.val % 3 + 1) - 1 = v.val
            omega
          by_cases hk : k ≤ (f i).1 + 1
          · have h0 : p i 0 = L := by simp [p]
            simpa only [h0, hpv] using hseg i 0 k (by omega) (by omega) fun t _ htk =>
              if ht : t = k then ht ▸ hpv.symm ▸ hv else hfree i t (by omega)
          · exact hLR.trans (by
              have h4 : p i 4 = R := by simp [p]
              simpa only [h4, hpv] using
                (hseg i k 4 (by omega) le_rfl fun t _ _ => hfree i t (by omega)).symm)
        · by_cases hv2 : v.1 = 3 * m
          · rw [show (⟨v, hv⟩ : ↥Sᶜ) = ⟨L, hL⟩ from Subtype.ext (Fin.ext hv2)]
          · rw [show (⟨v, hv⟩ : ↥Sᶜ) = ⟨R, hR⟩ from Subtype.ext (Fin.ext (by dsimp [R]; omega))]
            exact hLR
      intro a b
      exact (hfromL a).symm.trans (hfromL b)
  have hinj : Function.Injective T := fun f g h => funext fun i =>
    Fin.ext (Nat.succ.inj ((hmem g i _).mp (h ▸ ⟨i, rfl⟩)))
  have hcard : 3 ^ m ≤ {S : Set (Fin (3 * m + 2)) | Erdos150.IsMinimalCut G S}.ncard := by
    have h := Nat.card_le_card_of_injective
      (fun f : Fin m → Fin 3 => (⟨T f, hcut f⟩ : {S | Erdos150.IsMinimalCut G S}))
      (fun f g h => hinj (congrArg Subtype.val h))
    rwa [Nat.card_fun, Nat.card_fin, Nat.card_fin] at h
  exact le_csSup_of_le
    ⟨Nat.card (Set (Fin (3 * m + 2))), by rintro _ ⟨G', rfl⟩; exact Set.ncard_le_card _⟩
    ⟨G, rfl⟩ hcard
