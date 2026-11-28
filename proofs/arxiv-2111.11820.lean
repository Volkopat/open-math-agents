import OMAStatements.S_arxiv_2111_11820

namespace OMA.P_arxiv_2111_11820

open OMA.S_arxiv_2111_11820 SimpleGraph

/-! ### Part 1: Counterexample graph `H_k = K_1 ∨ (P_{6k^2} + (3k^2 - 1) K_1)` on `9k^2` vertices -/

private def counterGraph (k : ℕ) : SimpleGraph (Fin (9 * k ^ 2)) where
  Adj u v :=
    (u.val = 0 ∧ v.val ≠ 0) ∨
    (v.val = 0 ∧ u.val ≠ 0) ∨
    (1 ≤ u.val ∧ u.val ≤ 6 * k ^ 2 ∧ 1 ≤ v.val ∧ v.val ≤ 6 * k ^ 2 ∧
      (u.val + 1 = v.val ∨ v.val + 1 = u.val))
  symm := ⟨fun _ _ h => by rcases h with h | h | ⟨h1, h2, h3, h4, h5⟩ <;> tauto⟩
  loopless := ⟨fun u h => by rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨_, _, _, _, h1 | h1⟩ <;> omega⟩

private instance (k : ℕ) : DecidableRel (counterGraph k).Adj :=
  fun u v => by unfold counterGraph; dsimp; infer_instance

/-! ### Part 2: Outerplanarity of `counterGraph k` (no `K_4` or `K_{2,3}` minor) -/

private lemma walk_intermediate {k : ℕ} {S : Set (Fin (9 * k ^ 2))}
    (h0 : ∀ u ∈ S, u.val ≠ 0)
    {u v : S} (p : ((counterGraph k).induce S).Walk u v) :
    ∀ m : ℕ, u.val.val ≤ m → m ≤ v.val.val → ∃ w ∈ S, w.val = m := by
  induction p with
  | @nil a =>
    intro m h1 h2
    exact ⟨a.val, a.property, by omega⟩
  | @cons a b c hadj q ih =>
    intro m h1 h2
    by_cases hma : m = a.val.val
    · exact ⟨a.val, a.property, hma.symm⟩
    · have ha0 : a.val.val ≠ 0 := h0 a.val a.property
      have hb0 : b.val.val ≠ 0 := h0 b.val b.property
      have hstep : a.val.val + 1 = b.val.val ∨ b.val.val + 1 = a.val.val := by
        rcases hadj with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, _, _, _, h⟩
        · exact absurd h ha0
        · exact absurd h hb0
        · exact h
      exact ih m (by omega) h2

private lemma connected_is_interval {k : ℕ} {S : Set (Fin (9 * k ^ 2))}
    (hne : S.Nonempty) (h0 : ∀ u ∈ S, u.val ≠ 0)
    (hconn : ((counterGraph k).induce S).Connected) :
    ∃ L R : ℕ, L ≤ R ∧ (∀ u ∈ S, L ≤ u.val ∧ u.val ≤ R) ∧
      (∀ u : Fin (9 * k ^ 2), L ≤ u.val → u.val ≤ R → u ∈ S) := by
  classical
  let Sf : Finset (Fin (9 * k ^ 2)) := S.toFinset
  have hSf_ne : Sf.Nonempty := Set.toFinset_nonempty.mpr hne
  let uMin : Fin (9 * k ^ 2) := Sf.min' hSf_ne
  let uMax : Fin (9 * k ^ 2) := Sf.max' hSf_ne
  have huMin : uMin ∈ S := (Set.mem_toFinset).mp (Finset.min'_mem Sf hSf_ne)
  have huMax : uMax ∈ S := (Set.mem_toFinset).mp (Finset.max'_mem Sf hSf_ne)
  have hle_min : ∀ u ∈ S, uMin.val ≤ u.val := fun u hu =>
    Finset.min'_le Sf u ((Set.mem_toFinset).mpr hu)
  have hle_max : ∀ u ∈ S, u.val ≤ uMax.val := fun u hu =>
    Finset.le_max' Sf u ((Set.mem_toFinset).mpr hu)
  refine ⟨uMin.val, uMax.val, hle_min uMax huMax, fun u hu => ⟨hle_min u hu, hle_max u hu⟩, ?_⟩
  intro x hxL hxR
  have hreach : ((counterGraph k).induce S).Reachable ⟨uMin, huMin⟩ ⟨uMax, huMax⟩ :=
    hconn ⟨uMin, huMin⟩ ⟨uMax, huMax⟩
  obtain ⟨p⟩ := hreach
  obtain ⟨w, hwS, hwx⟩ := walk_intermediate h0 p x.val hxL hxR
  have : w = x := Fin.ext hwx
  exact this ▸ hwS

private lemma interval_adj_endpoints {k : ℕ} {S₁ S₂ : Set (Fin (9 * k ^ 2))}
    {L₁ R₁ L₂ R₂ : ℕ}
    (hdisj : Disjoint S₁ S₂)
    (h0₁ : ∀ u ∈ S₁, u.val ≠ 0) (h0₂ : ∀ u ∈ S₂, u.val ≠ 0)
    (hI₁ : (∀ u ∈ S₁, L₁ ≤ u.val ∧ u.val ≤ R₁) ∧ (∀ u : Fin (9 * k ^ 2), L₁ ≤ u.val → u.val ≤ R₁ → u ∈ S₁))
    (hI₂ : (∀ u ∈ S₂, L₂ ≤ u.val ∧ u.val ≤ R₂) ∧ (∀ u : Fin (9 * k ^ 2), L₂ ≤ u.val → u.val ≤ R₂ → u ∈ S₂))
    (hne₁ : S₁.Nonempty) (hne₂ : S₂.Nonempty)
    (hadj : ∃ u ∈ S₁, ∃ v ∈ S₂, (counterGraph k).Adj u v) :
    (L₁ < L₂ ∧ R₁ + 1 = L₂) ∨ (L₂ < L₁ ∧ R₂ + 1 = L₁) := by
  obtain ⟨u, hu, v, hv, huv⟩ := hadj
  have hstep : u.val + 1 = v.val ∨ v.val + 1 = u.val := by
    rcases huv with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, _, _, _, h⟩
    · exact absurd h (h0₁ u hu)
    · exact absurd h (h0₂ v hv)
    · exact h
  have huI := hI₁.1 u hu
  have hvI := hI₂.1 v hv
  obtain ⟨a₁, ha₁⟩ := hne₁
  obtain ⟨a₂, ha₂⟩ := hne₂
  have hL₁_le : L₁ ≤ R₁ := le_trans (hI₁.1 a₁ ha₁).1 (hI₁.1 a₁ ha₁).2
  have hL₂_le : L₂ ≤ R₂ := le_trans (hI₂.1 a₂ ha₂).1 (hI₂.1 a₂ ha₂).2
  have hL₁_lt : L₁ < 9 * k ^ 2 := lt_of_le_of_lt (hI₁.1 a₁ ha₁).1 a₁.isLt
  have hL₂_lt : L₂ < 9 * k ^ 2 := lt_of_le_of_lt (hI₂.1 a₂ ha₂).1 a₂.isLt
  have hL_ne : L₁ ≠ L₂ := by
    intro heq
    have hm1 : (⟨L₁, hL₁_lt⟩ : Fin (9 * k ^ 2)) ∈ S₁ := hI₁.2 ⟨L₁, hL₁_lt⟩ le_rfl hL₁_le
    have hm2 : (⟨L₁, hL₁_lt⟩ : Fin (9 * k ^ 2)) ∈ S₂ := hI₂.2 ⟨L₁, hL₁_lt⟩ (by dsimp; omega) (by dsimp; omega)
    exact Set.disjoint_left.mp hdisj hm1 hm2
  by_cases hlt : L₁ < L₂
  · left
    have hR1_lt : R₁ < L₂ := by
      by_contra hge
      have hm1 : (⟨L₂, hL₂_lt⟩ : Fin (9 * k ^ 2)) ∈ S₁ := hI₁.2 ⟨L₂, hL₂_lt⟩ (by dsimp; omega) (by dsimp; omega)
      have hm2 : (⟨L₂, hL₂_lt⟩ : Fin (9 * k ^ 2)) ∈ S₂ := hI₂.2 ⟨L₂, hL₂_lt⟩ le_rfl hL₂_le
      exact Set.disjoint_left.mp hdisj hm1 hm2
    exact ⟨hlt, by omega⟩
  · right
    have hlt' : L₂ < L₁ := by omega
    have hR2_lt : R₂ < L₁ := by
      by_contra hge
      have hm1 : (⟨L₁, hL₁_lt⟩ : Fin (9 * k ^ 2)) ∈ S₁ := hI₁.2 ⟨L₁, hL₁_lt⟩ le_rfl hL₁_le
      have hm2 : (⟨L₁, hL₁_lt⟩ : Fin (9 * k ^ 2)) ∈ S₂ := hI₂.2 ⟨L₁, hL₁_lt⟩ (by dsimp; omega) (by dsimp; omega)
      exact Set.disjoint_left.mp hdisj hm1 hm2
    exact ⟨hlt', by omega⟩

private lemma no_deg2_in_family {k : ℕ} {W : Type*} [DecidableEq W]
    (B : W → Set (Fin (9 * k ^ 2)))
    (hne : ∀ w, (B w).Nonempty)
    (hdisj : ∀ w₁ w₂, w₁ ≠ w₂ → Disjoint (B w₁) (B w₂))
    (hconn : ∀ w, ((counterGraph k).induce (B w)).Connected)
    (T : Finset W) (hTne : T.Nonempty)
    (hT0 : ∀ w ∈ T, ∀ u ∈ B w, u.val ≠ 0)
    (hdeg2 : ∀ w ∈ T, ∃ w₁ ∈ T, ∃ w₂ ∈ T, w₁ ≠ w ∧ w₂ ≠ w ∧ w₁ ≠ w₂ ∧
      (∃ u ∈ B w, ∃ v ∈ B w₁, (counterGraph k).Adj u v) ∧
      (∃ u ∈ B w, ∃ v ∈ B w₂, (counterGraph k).Adj u v)) : False := by
  classical
  have hI : ∀ w ∈ T, ∃ L R : ℕ, L ≤ R ∧ (∀ u ∈ B w, L ≤ u.val ∧ u.val ≤ R) ∧
      (∀ u : Fin (9 * k ^ 2), L ≤ u.val → u.val ≤ R → u ∈ B w) :=
    fun w hw => connected_is_interval (hne w) (hT0 w hw) (hconn w)
  let Lfn : W → ℕ := fun w => if hw : w ∈ T then Classical.choose (hI w hw) else 0
  obtain ⟨wStar, hwStar, hmin⟩ := Finset.exists_min_image T Lfn hTne
  obtain ⟨w₁, hw₁, w₂, hw₂, h1ne, h2ne, h12, hadj₁, hadj₂⟩ := hdeg2 wStar hwStar
  have hS := Classical.choose_spec (hI wStar hwStar)
  obtain ⟨RStar, hLRS, hIS₁, hIS₂⟩ := hS
  have h1 := Classical.choose_spec (hI w₁ hw₁)
  obtain ⟨R₁, hLR₁, hI1₁, hI1₂⟩ := h1
  have h2 := Classical.choose_spec (hI w₂ hw₂)
  obtain ⟨R₂, hLR₂, hI2₁, hI2₂⟩ := h2
  have hLmin₁ : Classical.choose (hI wStar hwStar) ≤ Classical.choose (hI w₁ hw₁) := by
    have := hmin w₁ hw₁
    simpa only [Lfn, hwStar, hw₁, ↓reduceDIte] using this
  have hLmin₂ : Classical.choose (hI wStar hwStar) ≤ Classical.choose (hI w₂ hw₂) := by
    have := hmin w₂ hw₂
    simpa only [Lfn, hwStar, hw₂, ↓reduceDIte] using this
  have he1 := interval_adj_endpoints (hdisj wStar w₁ h1ne.symm) (hT0 wStar hwStar) (hT0 w₁ hw₁)
    ⟨hIS₁, hIS₂⟩ ⟨hI1₁, hI1₂⟩ (hne wStar) (hne w₁) hadj₁
  have he2 := interval_adj_endpoints (hdisj wStar w₂ h2ne.symm) (hT0 wStar hwStar) (hT0 w₂ hw₂)
    ⟨hIS₁, hIS₂⟩ ⟨hI2₁, hI2₂⟩ (hne wStar) (hne w₂) hadj₂
  have hL1_eq : Classical.choose (hI w₁ hw₁) = RStar + 1 := by omega
  have hL2_eq : Classical.choose (hI w₂ hw₂) = RStar + 1 := by omega
  obtain ⟨a₁, ha₁⟩ := hne w₁
  have hlt : RStar + 1 < 9 * k ^ 2 := by
    have := (hI1₁ a₁ ha₁).1
    omega
  have hm1 : (⟨RStar + 1, hlt⟩ : Fin (9 * k ^ 2)) ∈ B w₁ := hI1₂ ⟨RStar + 1, hlt⟩ (by dsimp; omega) (by dsimp; omega)
  have hm2 : (⟨RStar + 1, hlt⟩ : Fin (9 * k ^ 2)) ∈ B w₂ := hI2₂ ⟨RStar + 1, hlt⟩ (by dsimp; omega) (by dsimp; omega)
  exact Set.disjoint_left.mp (hdisj w₁ w₂ h12) hm1 hm2

private lemma no_deg3_star {k : ℕ} {W : Type*}
    (B : W → Set (Fin (9 * k ^ 2)))
    (hne : ∀ w, (B w).Nonempty)
    (hdisj : ∀ w₁ w₂, w₁ ≠ w₂ → Disjoint (B w₁) (B w₂))
    (hconn : ∀ w, ((counterGraph k).induce (B w)).Connected)
    (w₀ w₁ w₂ w₃ : W)
    (h01 : w₀ ≠ w₁) (h02 : w₀ ≠ w₂) (h03 : w₀ ≠ w₃)
    (h12 : w₁ ≠ w₂) (h13 : w₁ ≠ w₃) (h23 : w₂ ≠ w₃)
    (h0 : ∀ u ∈ B w₀, u.val ≠ 0) (h1 : ∀ u ∈ B w₁, u.val ≠ 0)
    (h2 : ∀ u ∈ B w₂, u.val ≠ 0) (h3 : ∀ u ∈ B w₃, u.val ≠ 0)
    (hadj₁ : ∃ u ∈ B w₀, ∃ v ∈ B w₁, (counterGraph k).Adj u v)
    (hadj₂ : ∃ u ∈ B w₀, ∃ v ∈ B w₂, (counterGraph k).Adj u v)
    (hadj₃ : ∃ u ∈ B w₀, ∃ v ∈ B w₃, (counterGraph k).Adj u v) : False := by
  obtain ⟨L₀, R₀, hLR₀, hI0₁, hI0₂⟩ := connected_is_interval (hne w₀) h0 (hconn w₀)
  obtain ⟨L₁, R₁, hLR₁, hI1₁, hI1₂⟩ := connected_is_interval (hne w₁) h1 (hconn w₁)
  obtain ⟨L₂, R₂, hLR₂, hI2₁, hI2₂⟩ := connected_is_interval (hne w₂) h2 (hconn w₂)
  obtain ⟨L₃, R₃, hLR₃, hI3₁, hI3₂⟩ := connected_is_interval (hne w₃) h3 (hconn w₃)
  have he1 := interval_adj_endpoints (hdisj w₀ w₁ h01) h0 h1 ⟨hI0₁, hI0₂⟩ ⟨hI1₁, hI1₂⟩ (hne w₀) (hne w₁) hadj₁
  have he2 := interval_adj_endpoints (hdisj w₀ w₂ h02) h0 h2 ⟨hI0₁, hI0₂⟩ ⟨hI2₁, hI2₂⟩ (hne w₀) (hne w₂) hadj₂
  have he3 := interval_adj_endpoints (hdisj w₀ w₃ h03) h0 h3 ⟨hI0₁, hI0₂⟩ ⟨hI3₁, hI3₂⟩ (hne w₀) (hne w₃) hadj₃
  -- Two of the three must share either the right endpoint R₀ + 1 or the left endpoint L₀ - 1!
  have hRight : ∀ {a b : W} {La Ra Lb Rb : ℕ},
      a ≠ b → La ≤ Ra → Lb ≤ Rb →
      (∀ u ∈ B a, La ≤ u.val ∧ u.val ≤ Ra) → (∀ u : Fin (9 * k ^ 2), La ≤ u.val → u.val ≤ Ra → u ∈ B a) →
      (∀ u : Fin (9 * k ^ 2), Lb ≤ u.val → u.val ≤ Rb → u ∈ B b) →
      R₀ + 1 = La → R₀ + 1 = Lb → False := by
    intro a b La Ra Lb Rb hab hLa hLb hIa1 hIa2 hIb2 ha hb
    obtain ⟨x, hx⟩ := hne a
    have hlt : R₀ + 1 < 9 * k ^ 2 := by have := (hIa1 x hx).1; omega
    exact Set.disjoint_left.mp (hdisj a b hab) (hIa2 ⟨R₀ + 1, hlt⟩ (by dsimp; omega) (by dsimp; omega))
      (hIb2 ⟨R₀ + 1, hlt⟩ (by dsimp; omega) (by dsimp; omega))
  have hLeft : ∀ {a b : W} {La Ra Lb Rb : ℕ},
      a ≠ b → La ≤ Ra → Lb ≤ Rb →
      (∀ u ∈ B a, La ≤ u.val ∧ u.val ≤ Ra) → (∀ u : Fin (9 * k ^ 2), La ≤ u.val → u.val ≤ Ra → u ∈ B a) →
      (∀ u : Fin (9 * k ^ 2), Lb ≤ u.val → u.val ≤ Rb → u ∈ B b) →
      Ra + 1 = L₀ → Rb + 1 = L₀ → False := by
    intro a b La Ra Lb Rb hab hLa hLb _hIa1 hIa2 hIb2 ha hb
    obtain ⟨y, hy⟩ := hne w₀
    have hlt : Ra < 9 * k ^ 2 := by have := (hI0₁ y hy).1; have := y.isLt; omega
    exact Set.disjoint_left.mp (hdisj a b hab) (hIa2 ⟨Ra, hlt⟩ (by dsimp; omega) (by dsimp; omega))
      (hIb2 ⟨Ra, hlt⟩ (by dsimp; omega) (by dsimp; omega))
  rcases he1 with ⟨_, h1R⟩ | ⟨_, h1L⟩ <;>
  rcases he2 with ⟨_, h2R⟩ | ⟨_, h2L⟩ <;>
  rcases he3 with ⟨_, h3R⟩ | ⟨_, h3L⟩
  · exact hRight h12 hLR₁ hLR₂ hI1₁ hI1₂ hI2₂ h1R h2R
  · exact hRight h12 hLR₁ hLR₂ hI1₁ hI1₂ hI2₂ h1R h2R
  · exact hRight h13 hLR₁ hLR₃ hI1₁ hI1₂ hI3₂ h1R h3R
  · exact hLeft h23 hLR₂ hLR₃ hI2₁ hI2₂ hI3₂ h2L h3L
  · exact hRight h23 hLR₂ hLR₃ hI2₁ hI2₂ hI3₂ h2R h3R
  · exact hLeft h13 hLR₁ hLR₃ hI1₁ hI1₂ hI3₂ h1L h3L
  · exact hLeft h12 hLR₁ hLR₂ hI1₁ hI1₂ hI2₂ h1L h2L
  · exact hLeft h12 hLR₁ hLR₂ hI1₁ hI1₂ hI2₂ h1L h2L

private lemma counterGraph_outerplanar (k : ℕ) (hk : 10 ≤ k) :
    IsOuterplanar (counterGraph k) := by
  have hn_pos : 0 < 9 * k ^ 2 := by nlinarith
  let z0 : Fin (9 * k ^ 2) := ⟨0, hn_pos⟩
  have hu_eq : ∀ u : Fin (9 * k ^ 2), u.val = 0 → u = z0 := fun u hu0 => Fin.ext hu0
  constructor
  · -- No K_4 minor
    rintro ⟨B, hne, hdisj, hconn, hadj⟩
    have hex_bad : ∃ wBad : Fin 4, ∀ w : Fin 4, w ≠ wBad → ∀ u ∈ B w, u.val ≠ 0 := by
      by_cases h0 : ∃ w : Fin 4, z0 ∈ B w
      · obtain ⟨wBad, hwBad⟩ := h0
        refine ⟨wBad, fun w hne' u hu hu0 => ?_⟩
        exact Set.disjoint_left.mp (hdisj w wBad hne') (hu_eq u hu0 ▸ hu) hwBad
      · push Not at h0
        exact ⟨0, fun w _ u hu hu0 => h0 w (hu_eq u hu0 ▸ hu)⟩
    obtain ⟨wBad, hT0⟩ := hex_bad
    let T : Finset (Fin 4) := Finset.univ.erase wBad
    have hTne : T.Nonempty := by
      have hc : T.card = 3 := by simp [T]
      exact Finset.card_pos.mp (by omega)
    refine no_deg2_in_family B hne hdisj hconn T hTne
      (fun w hw => hT0 w (Finset.mem_erase.mp hw).1) ?_
    intro w hw
    have hT2 : (T.erase w).card = 2 := by
      rw [Finset.card_erase_of_mem hw]
      have : T.card = 3 := by simp [T]
      omega
    obtain ⟨w₁, w₂, h12, heq⟩ := Finset.card_eq_two.mp hT2
    have hw1_mem : w₁ ∈ T.erase w := by rw [heq]; simp
    have hw2_mem : w₂ ∈ T.erase w := by rw [heq]; simp
    have ⟨h1ne, hw1T⟩ := Finset.mem_erase.mp hw1_mem
    have ⟨h2ne, hw2T⟩ := Finset.mem_erase.mp hw2_mem
    exact ⟨w₁, hw1T, w₂, hw2T, h1ne, h2ne, h12, hadj w w₁ h1ne.symm, hadj w w₂ h2ne.symm⟩
  · -- No K_{2,3} minor
    rintro ⟨B, hne, hdisj, hconn, hadj⟩
    by_cases hR : ∃ y : Fin 3, z0 ∈ B (Sum.inr y)
    · -- Vertex 0 lies in B(inr y): remaining 2 left + 2 right vertices form C_4!
      obtain ⟨y0, hy0⟩ := hR
      have hT0_fn : ∀ w : Fin 2 ⊕ Fin 3, w ≠ Sum.inr y0 → ∀ u ∈ B w, u.val ≠ 0 := by
        intro w hne' u hu hu0
        exact Set.disjoint_left.mp (hdisj w (Sum.inr y0) hne') (hu_eq u hu0 ▸ hu) hy0
      have hcard : (Finset.univ.erase y0 : Finset (Fin 3)).card = 2 := by simp
      obtain ⟨y₁, y₂, hy12, hy_eq⟩ := Finset.card_eq_two.mp hcard
      have hy1_ne : y₁ ≠ y0 := (Finset.mem_erase.mp (by rw [hy_eq]; simp)).1
      have hy2_ne : y₂ ≠ y0 := (Finset.mem_erase.mp (by rw [hy_eq]; simp)).1
      let T : Finset (Fin 2 ⊕ Fin 3) := {Sum.inl 0, Sum.inl 1, Sum.inr y₁, Sum.inr y₂}
      have hTne : T.Nonempty := ⟨Sum.inl 0, by simp [T]⟩
      refine no_deg2_in_family B hne hdisj hconn T hTne ?_ ?_
      · intro w hw
        simp only [T, Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl | rfl | rfl
        · exact hT0_fn _ (by simp)
        · exact hT0_fn _ (by simp)
        · exact hT0_fn _ (by simp [hy1_ne])
        · exact hT0_fn _ (by simp [hy2_ne])
      · intro w hw
        simp only [T, Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl | rfl | rfl
        · exact ⟨Sum.inr y₁, by simp [T], Sum.inr y₂, by simp [T], by simp, by simp,
            by simp [hy12], hadj _ _ (by simp [K23Graph]), hadj _ _ (by simp [K23Graph])⟩
        · exact ⟨Sum.inr y₁, by simp [T], Sum.inr y₂, by simp [T], by simp, by simp,
            by simp [hy12], hadj _ _ (by simp [K23Graph]), hadj _ _ (by simp [K23Graph])⟩
        · exact ⟨Sum.inl 0, by simp [T], Sum.inl 1, by simp [T], by simp, by simp,
            by decide, hadj _ _ (by simp [K23Graph]), hadj _ _ (by simp [K23Graph])⟩
        · exact ⟨Sum.inl 0, by simp [T], Sum.inl 1, by simp [T], by simp, by simp,
            by decide, hadj _ _ (by simp [K23Graph]), hadj _ _ (by simp [K23Graph])⟩
    · -- No right vertex contains 0; at least one left vertex x0 also avoids 0 -> K_{1,3} star!
      push Not at hR
      have hR0 : ∀ y : Fin 3, ∀ u ∈ B (Sum.inr y), u.val ≠ 0 :=
        fun y u hu hu0 => hR y (hu_eq u hu0 ▸ hu)
      have hex_left : ∃ x0 : Fin 2, ∀ u ∈ B (Sum.inl x0), u.val ≠ 0 := by
        by_cases h0 : z0 ∈ B (Sum.inl 0)
        · refine ⟨1, fun u hu hu0 => ?_⟩
          exact Set.disjoint_left.mp (hdisj (Sum.inl 1) (Sum.inl 0) (by decide)) (hu_eq u hu0 ▸ hu) h0
        · exact ⟨0, fun u hu hu0 => h0 (hu_eq u hu0 ▸ hu)⟩
      obtain ⟨x0, hx0⟩ := hex_left
      exact no_deg3_star B hne hdisj hconn
        (Sum.inl x0) (Sum.inr 0) (Sum.inr 1) (Sum.inr 2)
        (by simp) (by simp) (by simp) (by decide) (by decide) (by decide)
        hx0 (hR0 0) (hR0 1) (hR0 2)
        (hadj _ _ (by simp [K23Graph])) (hadj _ _ (by simp [K23Graph])) (hadj _ _ (by simp [K23Graph]))

/-! ### Part 3: General Rayleigh boundedness and exact quadratic form formulas -/

private lemma rayleigh_bdd {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    BddAbove { r : ℝ | ∃ x : Fin n → ℝ, (∑ i : Fin n, x i ^ 2) ≠ 0 ∧ r = rayleighQuot G x } ∧
    BddBelow { r : ℝ | ∃ x : Fin n → ℝ, (∑ i : Fin n, x i ^ 2) ≠ 0 ∧ r = rayleighQuot G x } := by
  have habs : ∀ x : Fin n → ℝ, |quadForm G x| ≤ (n : ℝ) * ∑ i : Fin n, x i ^ 2 := by
    intro x
    unfold quadForm
    calc |∑ i : Fin n, ∑ j : Fin n, if G.Adj i j then x i * x j else 0|
        ≤ ∑ i : Fin n, |∑ j : Fin n, if G.Adj i j then x i * x j else 0| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin n, ∑ j : Fin n, |if G.Adj i j then x i * x j else 0| :=
          Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin n, ∑ j : Fin n, ((1 / 2 : ℝ) * (x i ^ 2 + x j ^ 2)) := by
          apply Finset.sum_le_sum; intro i _
          apply Finset.sum_le_sum; intro j _
          split_ifs
          · rw [abs_mul]; nlinarith [sq_nonneg (|x i| - |x j|), sq_abs (x i), sq_abs (x j)]
          · rw [abs_zero]; nlinarith [sq_nonneg (x i), sq_nonneg (x j)]
      _ = (n : ℝ) * ∑ i : Fin n, x i ^ 2 := by
          have h1 : ∀ i : Fin n, ∑ j : Fin n, (1 / 2 : ℝ) * (x i ^ 2 + x j ^ 2) =
              (1 / 2 : ℝ) * ((n : ℝ) * x i ^ 2 + ∑ j : Fin n, x j ^ 2) := by
            intro i
            rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
                Fintype.card_fin, nsmul_eq_mul]
          simp_rw [h1, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum,
              Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  constructor
  · refine ⟨(n : ℝ), ?_⟩
    rintro r ⟨x, hx, rfl⟩
    have hpos : 0 < ∑ i : Fin n, x i ^ 2 :=
      lt_of_le_of_ne (Finset.sum_nonneg fun i _ => sq_nonneg (x i)) (Ne.symm hx)
    unfold rayleighQuot
    rw [div_le_iff₀ hpos]
    exact le_trans (le_abs_self _) (habs x)
  · refine ⟨-(n : ℝ), ?_⟩
    rintro r ⟨x, hx, rfl⟩
    have hpos : 0 < ∑ i : Fin n, x i ^ 2 :=
      lt_of_le_of_ne (Finset.sum_nonneg fun i _ => sq_nonneg (x i)) (Ne.symm hx)
    unfold rayleighQuot
    rw [le_div_iff₀ hpos]
    have := neg_le_of_abs_le (habs x)
    linarith

private lemma rayleigh_nonempty {n : ℕ} (hn : 1 ≤ n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    { r : ℝ | ∃ x : Fin n → ℝ, (∑ i : Fin n, x i ^ 2) ≠ 0 ∧ r = rayleighQuot G x }.Nonempty := by
  refine ⟨rayleighQuot G (fun _ => 1), fun _ => 1, ?_, rfl⟩
  simp only [one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  exact Nat.cast_ne_zero.mpr (by omega)

/-! ### Part 4: Upper bound on `graphSpread (fanGraph (9 * k ^ 2))` -/

private lemma quadForm_fanGraph {m : ℕ} (x : Fin (m + 2) → ℝ) :
    quadForm (fanGraph (m + 2)) x =
      2 * x 0 * (∑ i : Fin (m + 1), x i.succ) +
      2 * ∑ i : Fin m, x i.castSucc.succ * x i.succ.succ := by
  unfold quadForm
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ (fun j : Fin (m + 2) => if (fanGraph (m + 2)).Adj 0 j then x 0 * x j else 0)]
  have hinner : ∀ i : Fin (m + 1),
      (∑ j : Fin (m + 2), if (fanGraph (m + 2)).Adj i.succ j then x i.succ * x j else 0) =
      (if (fanGraph (m + 2)).Adj i.succ 0 then x i.succ * x 0 else 0) +
      ∑ j : Fin (m + 1), if (fanGraph (m + 2)).Adj i.succ j.succ then x i.succ * x j.succ else 0 :=
    fun i => Fin.sum_univ_succ _
  simp_rw [hinner]
  -- (0, 0) term is 0:
  have h00 : ¬ (fanGraph (m + 2)).Adj 0 0 := (fanGraph (m + 2)).loopless.irrefl 0
  have h0s : ∀ j : Fin (m + 1), (fanGraph (m + 2)).Adj 0 j.succ :=
    fun j => Or.inl ⟨rfl, Fin.succ_ne_zero j |> fun h => by simp⟩
  have hs0 : ∀ i : Fin (m + 1), (fanGraph (m + 2)).Adj i.succ 0 :=
    fun i => Or.inr (Or.inl ⟨rfl, by simp⟩)
  simp only [h00, h0s, hs0, ↓reduceIte, zero_add]
  rw [Finset.sum_add_distrib]
  have hstar : (∑ j : Fin (m + 1), x 0 * x j.succ) + (∑ i : Fin (m + 1), x i.succ * x 0) =
      2 * x 0 * (∑ i : Fin (m + 1), x i.succ) := by
    rw [← Finset.mul_sum, ← Finset.sum_mul]; ring
  have hpath : (∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
      if (fanGraph (m + 2)).Adj i.succ j.succ then x i.succ * x j.succ else 0) =
      2 * ∑ i : Fin m, x i.castSucc.succ * x i.succ.succ := by
    have hiff : ∀ i j : Fin (m + 1),
        (fanGraph (m + 2)).Adj i.succ j.succ ↔ i.val + 1 = j.val ∨ j.val + 1 = i.val := by
      intro i j
      simp only [fanGraph, Fin.val_succ]
      constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩ | ⟨_, _, h⟩) <;> omega
      · intro h; right; right; exact ⟨by omega, by omega, by omega⟩
    have hsplit : ∀ i j : Fin (m + 1),
        (if (fanGraph (m + 2)).Adj i.succ j.succ then x i.succ * x j.succ else 0) =
        (if i.val + 1 = j.val then x i.succ * x j.succ else 0) +
        (if j.val + 1 = i.val then x i.succ * x j.succ else 0) := by
      intro i j
      by_cases h1 : i.val + 1 = j.val
      · have h2 : ¬ j.val + 1 = i.val := by omega
        simp [(hiff i j).mpr (Or.inl h1), h1, h2]
      · by_cases h2 : j.val + 1 = i.val
        · simp [(hiff i j).mpr (Or.inr h2), h1, h2]
        · have h3 : ¬ (fanGraph (m + 2)).Adj i.succ j.succ := by rw [hiff]; tauto
          simp [h1, h2, h3]
    simp_rw [hsplit, Finset.sum_add_distrib]
    have hsym : (∑ i : Fin (m + 1), ∑ j : Fin (m + 1), if j.val + 1 = i.val then x i.succ * x j.succ else 0) =
        ∑ i : Fin (m + 1), ∑ j : Fin (m + 1), if i.val + 1 = j.val then x i.succ * x j.succ else 0 := by
      rw [Finset.sum_comm]
      congr 1; ext i; congr 1; ext j
      split_ifs <;> ring
    rw [hsym, ← two_mul]
    congr 1
    rw [Fin.sum_univ_castSucc]
    have hlast : (∑ j : Fin (m + 1), if (Fin.last m).val + 1 = j.val then x (Fin.last m).succ * x j.succ else 0) = 0 := by
      apply Finset.sum_eq_zero; intro j _
      have : ¬ (Fin.last m).val + 1 = j.val := by simp; omega
      rw [if_neg this]
    rw [hlast, add_zero]
    congr 1; ext i
    have huniq : ∀ j : Fin (m + 1), (i.castSucc.val + 1 = j.val) ↔ j = i.succ := by
      intro j; simp [Fin.ext_iff, eq_comm]
    simp_rw [huniq]
    simp
  linarith

private lemma path_quad_bound {m : ℕ} (z : Fin (m + 1) → ℝ) :
    (∑ i : Fin m, 2 * z i.castSucc * z i.succ) ≤ 2 * ∑ j : Fin (m + 1), z j ^ 2 ∧
    -(2 * ∑ j : Fin (m + 1), z j ^ 2) ≤ ∑ i : Fin m, 2 * z i.castSucc * z i.succ := by
  have h1 : ∑ i : Fin m, z i.castSucc ^ 2 ≤ ∑ j : Fin (m + 1), z j ^ 2 := by
    rw [Fin.sum_univ_castSucc]; linarith [sq_nonneg (z (Fin.last m))]
  have h2 : ∑ i : Fin m, z i.succ ^ 2 ≤ ∑ j : Fin (m + 1), z j ^ 2 := by
    rw [Fin.sum_univ_succ]; linarith [sq_nonneg (z 0)]
  constructor
  · calc ∑ i : Fin m, 2 * z i.castSucc * z i.succ
        ≤ ∑ i : Fin m, (z i.castSucc ^ 2 + z i.succ ^ 2) :=
          Finset.sum_le_sum fun i _ => by nlinarith [sq_nonneg (z i.castSucc - z i.succ)]
      _ = (∑ i : Fin m, z i.castSucc ^ 2) + ∑ i : Fin m, z i.succ ^ 2 := Finset.sum_add_distrib
      _ ≤ 2 * ∑ j : Fin (m + 1), z j ^ 2 := by linarith
  · calc -(2 * ∑ j : Fin (m + 1), z j ^ 2)
        ≤ -((∑ i : Fin m, z i.castSucc ^ 2) + ∑ i : Fin m, z i.succ ^ 2) := by linarith
      _ = ∑ i : Fin m, -(z i.castSucc ^ 2 + z i.succ ^ 2) := by
          rw [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
      _ ≤ ∑ i : Fin m, 2 * z i.castSucc * z i.succ :=
          Finset.sum_le_sum fun i _ => by nlinarith [sq_nonneg (z i.castSucc + z i.succ)]

private lemma path_shift_id {m : ℕ} (c : ℝ) (z : Fin (m + 1) → ℝ) (hz : ∑ j : Fin (m + 1), z j = 0) :
    2 * ∑ i : Fin m, (c + z i.castSucc) * (c + z i.succ) =
      2 * (m : ℝ) * c ^ 2 - 2 * c * (z 0 + z (Fin.last m)) +
      ∑ i : Fin m, 2 * z i.castSucc * z i.succ := by
  have hexp : ∀ i : Fin m, 2 * ((c + z i.castSucc) * (c + z i.succ)) =
      2 * c ^ 2 + 2 * c * z i.castSucc + 2 * c * z i.succ + 2 * z i.castSucc * z i.succ :=
    fun i => by ring
  rw [Finset.mul_sum]
  simp_rw [hexp, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hcast : ∑ i : Fin m, z i.castSucc = -z (Fin.last m) := by
    have := hz; rw [Fin.sum_univ_castSucc] at this; linarith
  have hsucc : ∑ i : Fin m, z i.succ = -z 0 := by
    have := hz; rw [Fin.sum_univ_succ] at this; linarith
  rw [hcast, hsucc, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

private lemma fanGraph_maxEig_le (k : ℕ) (hk : 10 ≤ k) :
    maxEig (fanGraph (9 * k ^ 2)) ≤ 3 * (k : ℝ) + 1 := by
  have hn_ge2 : 2 ≤ 9 * k ^ 2 := by nlinarith
  obtain ⟨m, hm⟩ : ∃ m : ℕ, 9 * k ^ 2 = m + 2 := ⟨9 * k ^ 2 - 2, by omega⟩
  have hm_cast : (m : ℝ) + 1 = 9 * (k : ℝ) ^ 2 - 1 := by
    have : (m + 2 : ℝ) = 9 * (k : ℝ) ^ 2 := by exact_mod_cast hm.symm
    linarith
  unfold maxEig
  apply csSup_le (rayleigh_nonempty (by omega) (fanGraph (9 * k ^ 2)))
  rintro r ⟨x, hx, rfl⟩
  have hpos : 0 < ∑ i : Fin (9 * k ^ 2), x i ^ 2 :=
    lt_of_le_of_ne (Finset.sum_nonneg fun i _ => sq_nonneg (x i)) (Ne.symm hx)
  unfold rayleighQuot
  rw [div_le_iff₀ hpos]
  -- Transfer to Fin (m + 2) via hm:
  let e : Fin (m + 2) ≃ Fin (9 * k ^ 2) := finCongr hm.symm
  let x' : Fin (m + 2) → ℝ := fun i => x (e i)
  have hq_eq : quadForm (fanGraph (9 * k ^ 2)) x = quadForm (fanGraph (m + 2)) x' := by
    unfold quadForm
    rw [← Equiv.sum_comp e]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Equiv.sum_comp e]
    rfl
  have hnorm_eq : ∑ i : Fin (9 * k ^ 2), x i ^ 2 = ∑ i : Fin (m + 2), x' i ^ 2 :=
    (Equiv.sum_comp e (fun i => x i ^ 2)).symm
  rw [hq_eq, hnorm_eq]
  -- Replace x' by |x'|:
  let ax : Fin (m + 2) → ℝ := fun i => |x' i|
  have hq_abs : quadForm (fanGraph (m + 2)) x' ≤ quadForm (fanGraph (m + 2)) ax := by
    unfold quadForm
    apply Finset.sum_le_sum; intro i _
    apply Finset.sum_le_sum; intro j _
    split_ifs
    · calc x' i * x' j ≤ |x' i * x' j| := le_abs_self _
        _ = ax i * ax j := abs_mul (x' i) (x' j)
    · exact le_rfl
  have hnorm_abs : ∑ i : Fin (m + 2), ax i ^ 2 = ∑ i : Fin (m + 2), x' i ^ 2 := by
    congr 1; ext i; exact sq_abs (x' i)
  rw [← hnorm_abs]
  refine le_trans hq_abs ?_
  rw [quadForm_fanGraph ax, Fin.sum_univ_succ (fun i : Fin (m + 2) => ax i ^ 2)]
  -- Decompose y_i = ax (i.succ) = c + z_i with ∑ z_i = 0:
  have hm1_pos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  let c : ℝ := (∑ i : Fin (m + 1), ax i.succ) / ((m : ℝ) + 1)
  let z : Fin (m + 1) → ℝ := fun i => ax i.succ - c
  have hz_sum : ∑ i : Fin (m + 1), z i = 0 := by
    simp only [z, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_add, Nat.cast_one, c]
    have hne : (m : ℝ) + 1 ≠ 0 := ne_of_gt hm1_pos
    field_simp; ring
  have hsum_y : ∑ i : Fin (m + 1), ax i.succ = ((m : ℝ) + 1) * c := by
    simp only [c]; field_simp
  have hnorm_y : ∑ i : Fin (m + 1), ax i.succ ^ 2 = ((m : ℝ) + 1) * c ^ 2 + ∑ i : Fin (m + 1), z i ^ 2 := by
    have h1 : ∀ i : Fin (m + 1), ax i.succ ^ 2 = c ^ 2 + 2 * c * z i + z i ^ 2 := fun i => by
      simp only [z]; ring
    simp_rw [h1, Finset.sum_add_distrib, ← Finset.mul_sum, hz_sum, mul_zero, add_zero,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  -- Close the path to a cycle using 2 * ax 1 * ax (m+1) ≥ 0!
  have hclose : 2 * ∑ i : Fin m, ax i.castSucc.succ * ax i.succ.succ ≤
      2 * ((m : ℝ) + 1) * c ^ 2 + 2 * ∑ i : Fin (m + 1), z i ^ 2 := by
    have hrew : ∀ i : Fin m, ax i.castSucc.succ * ax i.succ.succ = (c + z i.castSucc) * (c + z i.succ) :=
      fun i => by simp only [z]; ring
    simp_rw [hrew]
    rw [path_shift_id c z hz_sum]
    have hclos_nn : 0 ≤ 2 * (c + z 0) * (c + z (Fin.last m)) := by
      have h0 : c + z 0 = ax (0 : Fin (m + 1)).succ := by simp only [z]; ring
      have hL : c + z (Fin.last m) = ax (Fin.last m).succ := by simp only [z]; ring
      rw [h0, hL]
      exact mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg _)) (abs_nonneg _)
    have hpb : ∑ i : Fin m, 2 * z i.castSucc * z i.succ + 2 * z 0 * z (Fin.last m) ≤
        2 * ∑ j : Fin (m + 1), z j ^ 2 := by
      have h1 : ∑ i : Fin m, 2 * z i.castSucc * z i.succ ≤
          (∑ i : Fin m, z i.castSucc ^ 2) + ∑ i : Fin m, z i.succ ^ 2 := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_le_sum fun i _ => by nlinarith [sq_nonneg (z i.castSucc - z i.succ)]
      have h2 : (∑ i : Fin m, z i.castSucc ^ 2) + z (Fin.last m) ^ 2 = ∑ j : Fin (m + 1), z j ^ 2 :=
        (Fin.sum_univ_castSucc (fun j => z j ^ 2)).symm
      have h3 : z 0 ^ 2 + ∑ i : Fin m, z i.succ ^ 2 = ∑ j : Fin (m + 1), z j ^ 2 :=
        (Fin.sum_univ_succ (fun j => z j ^ 2)).symm
      nlinarith [sq_nonneg (z 0 - z (Fin.last m))]
    linarith
  rw [hm_cast] at hclose
  rw [hsum_y, hnorm_y, hm_cast]
  have hk_ge : (10 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hz_nn : 0 ≤ ∑ i : Fin (m + 1), z i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg (z i)
  nlinarith [sq_nonneg (ax 0 - (3 * (k : ℝ) - 1) * c)]

private lemma fanGraph_minEig_disc (k : ℕ) (hk : 10 ≤ k) :
    let t : ℝ := 3 * (k : ℝ) - 3
    let A : ℝ := 3 * (k : ℝ) - 1 + 1 / (2 * (k : ℝ) ^ 2)
    let B : ℝ := 9 * (k : ℝ) ^ 2 - 1
    let C : ℝ := (3 * (k : ℝ) + 1 + 1 / (2 * (k : ℝ) ^ 2)) * (9 * (k : ℝ) ^ 2 - 1) - 2 - 2 / t
    0 ≤ A * C - B ^ 2 := by
  intro t A B C
  have hk_ge : (10 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have ht_pos : 0 < t := by simp only [t]; linarith
  have hk_ne : (k : ℝ) ≠ 0 := by linarith
  have hk1_ne : (k : ℝ) - 1 ≠ 0 := by linarith
  have hpoly : (A * C - B ^ 2) * (t * (4 * (k : ℝ) ^ 4)) =
      252 * (k : ℝ) ^ 6 - 252 * (k : ℝ) ^ 5 - 52 * (k : ℝ) ^ 4 + 51 * (k : ℝ) ^ 3 -
      19 * (k : ℝ) ^ 2 - 3 * (k : ℝ) + 3 := by
    simp only [A, B, C, t]
    have : 3 * (k : ℝ) - 3 = 3 * ((k : ℝ) - 1) := by ring
    rw [this]
    field_simp
    ring
  have hpos_rhs : 0 ≤ 252 * (k : ℝ) ^ 6 - 252 * (k : ℝ) ^ 5 - 52 * (k : ℝ) ^ 4 + 51 * (k : ℝ) ^ 3 -
      19 * (k : ℝ) ^ 2 - 3 * (k : ℝ) + 3 := by
    have hid : 252 * (k : ℝ) ^ 6 - 252 * (k : ℝ) ^ 5 - 52 * (k : ℝ) ^ 4 + 51 * (k : ℝ) ^ 3 -
        19 * (k : ℝ) ^ 2 - 3 * (k : ℝ) + 3 =
        ((k : ℝ) ^ 2) ^ 2 * (252 * (k : ℝ) ^ 2 - 252 * (k : ℝ) - 52) +
        (k : ℝ) * (51 * (k : ℝ) ^ 2 - 19 * (k : ℝ) - 3) + 3 := by ring
    rw [hid]
    have h1 : 0 ≤ 252 * (k : ℝ) ^ 2 - 252 * (k : ℝ) - 52 := by nlinarith
    have h2 : 0 ≤ 51 * (k : ℝ) ^ 2 - 19 * (k : ℝ) - 3 := by nlinarith
    positivity
  have hmul_pos : 0 < t * (4 * (k : ℝ) ^ 4) := by positivity
  nlinarith

private lemma fanGraph_minEig_ge (k : ℕ) (hk : 10 ≤ k) :
    1 - 3 * (k : ℝ) - 1 / (2 * (k : ℝ) ^ 2) ≤ minEig (fanGraph (9 * k ^ 2)) := by
  have hn_ge2 : 2 ≤ 9 * k ^ 2 := by nlinarith
  obtain ⟨m, hm⟩ : ∃ m : ℕ, 9 * k ^ 2 = m + 2 := ⟨9 * k ^ 2 - 2, by omega⟩
  have hm_cast : (m : ℝ) + 1 = 9 * (k : ℝ) ^ 2 - 1 := by
    have : (m + 2 : ℝ) = 9 * (k : ℝ) ^ 2 := by exact_mod_cast hm.symm
    linarith
  have hm_ge1 : 1 ≤ m := by nlinarith
  unfold minEig
  apply le_csInf (rayleigh_nonempty (by omega) (fanGraph (9 * k ^ 2)))
  rintro r ⟨x, hx, rfl⟩
  have hpos : 0 < ∑ i : Fin (9 * k ^ 2), x i ^ 2 :=
    lt_of_le_of_ne (Finset.sum_nonneg fun i _ => sq_nonneg (x i)) (Ne.symm hx)
  unfold rayleighQuot
  rw [le_div_iff₀ hpos]
  let e : Fin (m + 2) ≃ Fin (9 * k ^ 2) := finCongr hm.symm
  let x' : Fin (m + 2) → ℝ := fun i => x (e i)
  have hq_eq : quadForm (fanGraph (9 * k ^ 2)) x = quadForm (fanGraph (m + 2)) x' := by
    unfold quadForm
    rw [← Equiv.sum_comp e]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Equiv.sum_comp e]
    rfl
  have hnorm_eq : ∑ i : Fin (9 * k ^ 2), x i ^ 2 = ∑ i : Fin (m + 2), x' i ^ 2 :=
    (Equiv.sum_comp e (fun i => x i ^ 2)).symm
  rw [hq_eq, hnorm_eq, quadForm_fanGraph x', Fin.sum_univ_succ (fun i : Fin (m + 2) => x' i ^ 2)]
  have hm1_pos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  let c : ℝ := (∑ i : Fin (m + 1), x' i.succ) / ((m : ℝ) + 1)
  let z : Fin (m + 1) → ℝ := fun i => x' i.succ - c
  have hz_sum : ∑ i : Fin (m + 1), z i = 0 := by
    simp only [z, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_add, Nat.cast_one, c]
    have hne : (m : ℝ) + 1 ≠ 0 := ne_of_gt hm1_pos
    field_simp; ring
  have hsum_y : ∑ i : Fin (m + 1), x' i.succ = ((m : ℝ) + 1) * c := by
    simp only [c]; field_simp
  have hnorm_y : ∑ i : Fin (m + 1), x' i.succ ^ 2 = ((m : ℝ) + 1) * c ^ 2 + ∑ i : Fin (m + 1), z i ^ 2 := by
    have h1 : ∀ i : Fin (m + 1), x' i.succ ^ 2 = c ^ 2 + 2 * c * z i + z i ^ 2 := fun i => by
      simp only [z]; ring
    simp_rw [h1, Finset.sum_add_distrib, ← Finset.mul_sum, hz_sum, mul_zero, add_zero,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  have hrew : ∀ i : Fin m, x' i.castSucc.succ * x' i.succ.succ = (c + z i.castSucc) * (c + z i.succ) :=
    fun i => by simp only [z]; ring
  simp_rw [hrew]
  rw [path_shift_id c z hz_sum, hsum_y, hnorm_y]
  have hpath_lb : -(2 * ∑ j : Fin (m + 1), z j ^ 2) ≤ ∑ i : Fin m, 2 * z i.castSucc * z i.succ :=
    (path_quad_bound z).2
  -- Bound -2 * c * (z 0 + z (last m)) using AM-GM with t = 3*k - 3 > 0:
  have hk_ge : (10 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  let t : ℝ := 3 * (k : ℝ) - 3
  have ht_pos : 0 < t := by linarith
  have hz0_ne : (0 : Fin (m + 1)) ≠ Fin.last m := by
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  have hz_ends : z 0 ^ 2 + z (Fin.last m) ^ 2 ≤ ∑ j : Fin (m + 1), z j ^ 2 := by
    have hsub : ({(0 : Fin (m + 1)), Fin.last m} : Finset (Fin (m + 1))) ⊆ Finset.univ := Finset.subset_univ _
    have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => sq_nonneg (z j))
    rwa [Finset.sum_pair hz0_ne] at hle
  have hcross_lb : -(2 / t) * c ^ 2 - t * (∑ j : Fin (m + 1), z j ^ 2) ≤
      -2 * c * (z 0 + z (Fin.last m)) := by
    have h1 : 0 ≤ (c - t * z 0) ^ 2 := sq_nonneg _
    have h2 : 0 ≤ (c - t * z (Fin.last m)) ^ 2 := sq_nonneg _
    have hsum : 0 ≤ 2 * c ^ 2 - 2 * t * c * (z 0 + z (Fin.last m)) + t ^ 2 * (z 0 ^ 2 + z (Fin.last m) ^ 2) := by
      nlinarith
    have hdiv : 0 ≤ (2 / t) * c ^ 2 - 2 * c * (z 0 + z (Fin.last m)) + t * (z 0 ^ 2 + z (Fin.last m) ^ 2) := by
      have hne : t ≠ 0 := ne_of_gt ht_pos
      have : ((2 / t) * c ^ 2 - 2 * c * (z 0 + z (Fin.last m)) + t * (z 0 ^ 2 + z (Fin.last m) ^ 2)) * t =
          2 * c ^ 2 - 2 * t * c * (z 0 + z (Fin.last m)) + t ^ 2 * (z 0 ^ 2 + z (Fin.last m) ^ 2) := by
        field_simp
      nlinarith
    have ht_ends : t * (z 0 ^ 2 + z (Fin.last m) ^ 2) ≤ t * (∑ j : Fin (m + 1), z j ^ 2) :=
      mul_le_mul_of_nonneg_left hz_ends (le_of_lt ht_pos)
    have hneg : -(2 / t) * c ^ 2 = -(2 / t * c ^ 2) := by ring
    have hneg2 : -2 * c * (z 0 + z (Fin.last m)) = -(2 * c * (z 0 + z (Fin.last m))) := by ring
    linarith
  -- Now reduce to quadratic form A * x0^2 + 2 * B * x0 * c + C * c^2 ≥ 0!
  let A : ℝ := 3 * (k : ℝ) - 1 + 1 / (2 * (k : ℝ) ^ 2)
  let B : ℝ := 9 * (k : ℝ) ^ 2 - 1
  let C : ℝ := (3 * (k : ℝ) + 1 + 1 / (2 * (k : ℝ) ^ 2)) * (9 * (k : ℝ) ^ 2 - 1) - 2 - 2 / t
  have hA_pos : 0 < A := by
    have : 0 < 1 / (2 * (k : ℝ) ^ 2) := by positivity
    linarith
  have hdisc : 0 ≤ A * C - B ^ 2 := fanGraph_minEig_disc k hk
  have hquad_nn : 0 ≤ A * x' 0 ^ 2 + 2 * B * x' 0 * c + C * c ^ 2 := by
    have h1 : A * (A * x' 0 ^ 2 + 2 * B * x' 0 * c + C * c ^ 2) =
        (A * x' 0 + B * c) ^ 2 + (A * C - B ^ 2) * c ^ 2 := by ring
    have h2 : 0 ≤ (A * x' 0 + B * c) ^ 2 + (A * C - B ^ 2) * c ^ 2 :=
      add_nonneg (sq_nonneg _) (mul_nonneg hdisc (sq_nonneg c))
    nlinarith
  have hz_nn : 0 ≤ ∑ j : Fin (m + 1), z j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg (z j)
  have hcoeff_z : 0 ≤ (1 / (2 * (k : ℝ) ^ 2)) * ∑ j : Fin (m + 1), z j ^ 2 :=
    mul_nonneg (by positivity) hz_nn
  have hm_eq : (m : ℝ) = 9 * (k : ℝ) ^ 2 - 2 := by linarith
  have hcombine :
      (2 * x' 0 * ((9 * (k : ℝ) ^ 2 - 1) * c) +
        (2 * (9 * (k : ℝ) ^ 2 - 2) * c ^ 2 - 2 * c * (z 0 + z (Fin.last m)) +
          ∑ i : Fin m, 2 * z i.castSucc * z i.succ)) -
      (1 - 3 * (k : ℝ) - 1 / (2 * (k : ℝ) ^ 2)) *
        (x' 0 ^ 2 + ((9 * (k : ℝ) ^ 2 - 1) * c ^ 2 + ∑ j : Fin (m + 1), z j ^ 2)) ≥
      (A * x' 0 ^ 2 + 2 * B * x' 0 * c + C * c ^ 2) +
        (1 / (2 * (k : ℝ) ^ 2)) * ∑ j : Fin (m + 1), z j ^ 2 := by
    have halg :
        (2 * x' 0 * ((9 * (k : ℝ) ^ 2 - 1) * c) +
          (2 * (9 * (k : ℝ) ^ 2 - 2) * c ^ 2 + (-(2 / t) * c ^ 2 - t * ∑ j : Fin (m + 1), z j ^ 2) +
            -(2 * ∑ j : Fin (m + 1), z j ^ 2))) -
        (1 - 3 * (k : ℝ) - 1 / (2 * (k : ℝ) ^ 2)) *
          (x' 0 ^ 2 + ((9 * (k : ℝ) ^ 2 - 1) * c ^ 2 + ∑ j : Fin (m + 1), z j ^ 2)) =
        (A * x' 0 ^ 2 + 2 * B * x' 0 * c + C * c ^ 2) +
          (1 / (2 * (k : ℝ) ^ 2)) * ∑ j : Fin (m + 1), z j ^ 2 := by
      simp only [A, B, C, t]; ring
    linarith
  rw [hm_cast, hm_eq]
  linarith

private lemma fanGraph_spread_le (k : ℕ) (hk : 10 ≤ k) :
    graphSpread (fanGraph (9 * k ^ 2)) ≤ 6 * (k : ℝ) + 1 / (2 * (k : ℝ) ^ 2) := by
  unfold graphSpread
  have h1 := fanGraph_maxEig_le k hk
  have h2 := fanGraph_minEig_ge k hk
  linarith

/-! ### Part 5: Explicit 3-value Rayleigh quotient lower bound on `graphSpread (counterGraph k)` -/

private def testVec (k : ℕ) (u0 uP uI : ℝ) : Fin (9 * k ^ 2) → ℝ :=
  fun i => if i.val = 0 then u0 else if i.val ≤ 6 * k ^ 2 then uP else uI

private lemma testVec_norm (k : ℕ) (hk : 10 ≤ k) (u0 uP uI : ℝ) :
    ∑ i : Fin (9 * k ^ 2), testVec k u0 uP uI i ^ 2 =
      u0 ^ 2 + (6 * (k : ℝ) ^ 2) * uP ^ 2 + (3 * (k : ℝ) ^ 2 - 1) * uI ^ 2 := by
  have hsplit : ∀ i : Fin (9 * k ^ 2), testVec k u0 uP uI i ^ 2 =
      (if i.val = 0 then u0 ^ 2 else 0) +
      (if 1 ≤ i.val ∧ i.val ≤ 6 * k ^ 2 then uP ^ 2 else 0) +
      (if 6 * k ^ 2 < i.val then uI ^ 2 else 0) := by
    intro i; unfold testVec
    by_cases h0 : i.val = 0
    · simp [h0]
    · by_cases hP : i.val ≤ 6 * k ^ 2
      · have h1 : 1 ≤ i.val := by omega
        have h2 : ¬ 6 * k ^ 2 < i.val := by omega
        simp [h0, hP, h1, h2]
      · have h2 : 6 * k ^ 2 < i.val := by omega
        simp [h0, hP, h2]
  simp_rw [hsplit, Finset.sum_add_distrib, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hn_pos : 0 < 9 * k ^ 2 := by nlinarith
  have hc0 : (Finset.univ.filter (fun i : Fin (9 * k ^ 2) => i.val = 0)).card = 1 := by
    have : Finset.univ.filter (fun i : Fin (9 * k ^ 2) => i.val = 0) = {⟨0, hn_pos⟩} := by
      ext i; simp [Fin.ext_iff]
    rw [this, Finset.card_singleton]
  have hcP : (Finset.univ.filter (fun i : Fin (9 * k ^ 2) => 1 ≤ i.val ∧ i.val ≤ 6 * k ^ 2)).card = 6 * k ^ 2 := by
    let e : Fin (6 * k ^ 2) ≃ { i : Fin (9 * k ^ 2) // 1 ≤ i.val ∧ i.val ≤ 6 * k ^ 2 } :=
      { toFun := fun j => ⟨⟨j.val + 1, by have := j.isLt; nlinarith⟩, by dsimp; omega, by have := j.isLt; dsimp; omega⟩
        invFun := fun i => ⟨i.val.val - 1, by have := i.property; omega⟩
        left_inv := fun j => Fin.ext (by simp)
        right_inv := fun i => Subtype.ext (Fin.ext (by have := i.property.1; dsimp; omega)) }
    rw [← Fintype.card_subtype, ← Fintype.card_congr e, Fintype.card_fin]
  have hcI : (Finset.univ.filter (fun i : Fin (9 * k ^ 2) => 6 * k ^ 2 < i.val)).card = 3 * k ^ 2 - 1 := by
    have hk2 : 1 ≤ 3 * k ^ 2 := by nlinarith
    let e : Fin (3 * k ^ 2 - 1) ≃ { i : Fin (9 * k ^ 2) // 6 * k ^ 2 < i.val } :=
      { toFun := fun j => ⟨⟨j.val + 6 * k ^ 2 + 1, by have := j.isLt; omega⟩, by dsimp; omega⟩
        invFun := fun i => ⟨i.val.val - 6 * k ^ 2 - 1, by have := i.val.isLt; have := i.property; omega⟩
        left_inv := fun j => Fin.ext (by dsimp; omega)
        right_inv := fun i => Subtype.ext (Fin.ext (by have := i.property; dsimp; omega)) }
    rw [← Fintype.card_subtype, ← Fintype.card_congr e, Fintype.card_fin]
  rw [hc0, hcP, hcI]
  have hsub : ((3 * k ^ 2 - 1 : ℕ) : ℝ) = 3 * (k : ℝ) ^ 2 - 1 := by
    rw [Nat.cast_sub (by nlinarith : 1 ≤ 3 * k ^ 2)]; push_cast; ring
  rw [hsub]; push_cast; ring

private lemma testVec_quadForm (k : ℕ) (hk : 10 ≤ k) (u0 uP uI : ℝ) :
    quadForm (counterGraph k) (testVec k u0 uP uI) =
      2 * (6 * (k : ℝ) ^ 2) * u0 * uP +
      2 * (3 * (k : ℝ) ^ 2 - 1) * u0 * uI +
      2 * (6 * (k : ℝ) ^ 2 - 1) * uP ^ 2 := by
  unfold quadForm
  have hn_pos : 0 < 9 * k ^ 2 := by nlinarith
  let z0 : Fin (9 * k ^ 2) := ⟨0, hn_pos⟩
  have hsplit : ∀ i j : Fin (9 * k ^ 2),
      (if (counterGraph k).Adj i j then testVec k u0 uP uI i * testVec k u0 uP uI j else 0) =
      (if i.val = 0 ∧ 1 ≤ j.val ∧ j.val ≤ 6 * k ^ 2 then u0 * uP else 0) +
      (if i.val = 0 ∧ 6 * k ^ 2 < j.val then u0 * uI else 0) +
      (if j.val = 0 ∧ 1 ≤ i.val ∧ i.val ≤ 6 * k ^ 2 then uP * u0 else 0) +
      (if j.val = 0 ∧ 6 * k ^ 2 < i.val then uI * u0 else 0) +
      (if 1 ≤ i.val ∧ i.val < 6 * k ^ 2 ∧ j.val = i.val + 1 then uP * uP else 0) +
      (if 1 ≤ j.val ∧ j.val < 6 * k ^ 2 ∧ i.val = j.val + 1 then uP * uP else 0) := by
    intro i j
    have hAdj : (counterGraph k).Adj i j ↔
        (i.val = 0 ∧ j.val ≠ 0) ∨ (j.val = 0 ∧ i.val ≠ 0) ∨
        (1 ≤ i.val ∧ i.val ≤ 6 * k ^ 2 ∧ 1 ≤ j.val ∧ j.val ≤ 6 * k ^ 2 ∧
          (i.val + 1 = j.val ∨ j.val + 1 = i.val)) := Iff.rfl
    unfold testVec
    by_cases hi0 : i.val = 0 <;> by_cases hj0 : j.val = 0
    · simp [hAdj, hi0, hj0]
    · by_cases hjP : j.val ≤ 6 * k ^ 2
      · have h1 : 1 ≤ j.val := by omega
        have h2 : ¬ 6 * k ^ 2 < j.val := by omega
        simp [hAdj, hi0, hj0, hjP, h1, h2]
      · have h2 : 6 * k ^ 2 < j.val := by omega
        simp [hAdj, hi0, hj0, hjP, h2]
    · by_cases hiP : i.val ≤ 6 * k ^ 2
      · have h1 : 1 ≤ i.val := by omega
        have h2 : ¬ 6 * k ^ 2 < i.val := by omega
        simp [hAdj, hi0, hj0, hiP, h1, h2]
      · have h2 : 6 * k ^ 2 < i.val := by omega
        simp [hAdj, hi0, hj0, hiP, h2]
    · by_cases hup : 1 ≤ i.val ∧ i.val < 6 * k ^ 2 ∧ j.val = i.val + 1
      · have hdn : ¬ (1 ≤ j.val ∧ j.val < 6 * k ^ 2 ∧ i.val = j.val + 1) := by omega
        have hiP : i.val ≤ 6 * k ^ 2 := by omega
        have hjP : j.val ≤ 6 * k ^ 2 := by omega
        have hadj : (counterGraph k).Adj i j := Or.inr (Or.inr (by omega))
        rw [if_pos hadj, if_neg hi0, if_pos hiP, if_neg hj0, if_pos hjP,
            if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
            if_pos hup, if_neg hdn]
        ring
      · by_cases hdn : 1 ≤ j.val ∧ j.val < 6 * k ^ 2 ∧ i.val = j.val + 1
        · have hiP : i.val ≤ 6 * k ^ 2 := by omega
          have hjP : j.val ≤ 6 * k ^ 2 := by omega
          have hadj : (counterGraph k).Adj i j := Or.inr (Or.inr (by omega))
          rw [if_pos hadj, if_neg hi0, if_pos hiP, if_neg hj0, if_pos hjP,
              if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
              if_neg hup, if_pos hdn]
          ring
        · have hnot : ¬ (counterGraph k).Adj i j := by
            rw [hAdj]; omega
          rw [if_neg hnot, if_neg (by omega), if_neg (by omega), if_neg (by omega),
              if_neg (by omega), if_neg hup, if_neg hdn]
          ring
  simp_rw [hsplit, Finset.sum_add_distrib]
  -- Evaluate the 6 double sums:
  have hcP : (Finset.univ.filter (fun j : Fin (9 * k ^ 2) => 1 ≤ j.val ∧ j.val ≤ 6 * k ^ 2)).card = 6 * k ^ 2 := by
    let e : Fin (6 * k ^ 2) ≃ { j : Fin (9 * k ^ 2) // 1 ≤ j.val ∧ j.val ≤ 6 * k ^ 2 } :=
      { toFun := fun t => ⟨⟨t.val + 1, by have := t.isLt; nlinarith⟩, by dsimp; omega, by have := t.isLt; dsimp; omega⟩
        invFun := fun j => ⟨j.val.val - 1, by have := j.property; omega⟩
        left_inv := fun t => Fin.ext (by simp)
        right_inv := fun j => Subtype.ext (Fin.ext (by have := j.property.1; dsimp; omega)) }
    rw [← Fintype.card_subtype, ← Fintype.card_congr e, Fintype.card_fin]
  have hcI : (Finset.univ.filter (fun j : Fin (9 * k ^ 2) => 6 * k ^ 2 < j.val)).card = 3 * k ^ 2 - 1 := by
    have hk2 : 1 ≤ 3 * k ^ 2 := by nlinarith
    let e : Fin (3 * k ^ 2 - 1) ≃ { j : Fin (9 * k ^ 2) // 6 * k ^ 2 < j.val } :=
      { toFun := fun t => ⟨⟨t.val + 6 * k ^ 2 + 1, by have := t.isLt; omega⟩, by dsimp; omega⟩
        invFun := fun j => ⟨j.val.val - 6 * k ^ 2 - 1, by have := j.val.isLt; have := j.property; omega⟩
        left_inv := fun t => Fin.ext (by dsimp; omega)
        right_inv := fun j => Subtype.ext (Fin.ext (by have := j.property; dsimp; omega)) }
    rw [← Fintype.card_subtype, ← Fintype.card_congr e, Fintype.card_fin]
  have hcE : (Finset.univ.filter (fun i : Fin (9 * k ^ 2) => 1 ≤ i.val ∧ i.val < 6 * k ^ 2)).card = 6 * k ^ 2 - 1 := by
    have hk6 : 1 ≤ 6 * k ^ 2 := by nlinarith
    let e : Fin (6 * k ^ 2 - 1) ≃ { i : Fin (9 * k ^ 2) // 1 ≤ i.val ∧ i.val < 6 * k ^ 2 } :=
      { toFun := fun t => ⟨⟨t.val + 1, by have := t.isLt; omega⟩, by dsimp; omega, by have := t.isLt; dsimp; omega⟩
        invFun := fun i => ⟨i.val.val - 1, by have := i.property; omega⟩
        left_inv := fun t => Fin.ext (by simp)
        right_inv := fun i => Subtype.ext (Fin.ext (by have := i.property.1; dsimp; omega)) }
    rw [← Fintype.card_subtype, ← Fintype.card_congr e, Fintype.card_fin]
  have hs1 : (∑ i : Fin (9 * k ^ 2), ∑ j : Fin (9 * k ^ 2),
      if i.val = 0 ∧ 1 ≤ j.val ∧ j.val ≤ 6 * k ^ 2 then u0 * uP else 0) = (6 * (k : ℝ) ^ 2) * (u0 * uP) := by
    have : ∀ i : Fin (9 * k ^ 2), (∑ j : Fin (9 * k ^ 2),
        if i.val = 0 ∧ 1 ≤ j.val ∧ j.val ≤ 6 * k ^ 2 then u0 * uP else 0) =
        if i = z0 then (6 * (k : ℝ) ^ 2) * (u0 * uP) else 0 := by
      intro i
      by_cases hi : i = z0
      · subst hi; simp only [z0, ↓reduceIte, true_and, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hcP]
        push_cast; ring
      · have hne : i.val ≠ 0 := fun h => hi (Fin.ext h)
        simp [hi, hne]
    simp_rw [this]; simp
  have hs2 : (∑ i : Fin (9 * k ^ 2), ∑ j : Fin (9 * k ^ 2),
      if i.val = 0 ∧ 6 * k ^ 2 < j.val then u0 * uI else 0) = (3 * (k : ℝ) ^ 2 - 1) * (u0 * uI) := by
    have : ∀ i : Fin (9 * k ^ 2), (∑ j : Fin (9 * k ^ 2),
        if i.val = 0 ∧ 6 * k ^ 2 < j.val then u0 * uI else 0) =
        if i = z0 then (3 * (k : ℝ) ^ 2 - 1) * (u0 * uI) else 0 := by
      intro i
      by_cases hi : i = z0
      · subst hi; simp only [z0, ↓reduceIte, true_and, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hcI]
        rw [Nat.cast_sub (by nlinarith : 1 ≤ 3 * k ^ 2)]; push_cast; ring
      · have hne : i.val ≠ 0 := fun h => hi (Fin.ext h)
        simp [hi, hne]
    simp_rw [this]; simp
  have hs3 : (∑ i : Fin (9 * k ^ 2), ∑ j : Fin (9 * k ^ 2),
      if j.val = 0 ∧ 1 ≤ i.val ∧ i.val ≤ 6 * k ^ 2 then uP * u0 else 0) = (6 * (k : ℝ) ^ 2) * (uP * u0) := by
    rw [Finset.sum_comm]
    have : ∀ j : Fin (9 * k ^ 2), (∑ i : Fin (9 * k ^ 2),
        if j.val = 0 ∧ 1 ≤ i.val ∧ i.val ≤ 6 * k ^ 2 then uP * u0 else 0) =
        if j = z0 then (6 * (k : ℝ) ^ 2) * (uP * u0) else 0 := by
      intro j
      by_cases hj : j = z0
      · subst hj; simp only [z0, ↓reduceIte, true_and, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hcP]
        push_cast; ring
      · have hne : j.val ≠ 0 := fun h => hj (Fin.ext h)
        simp [hj, hne]
    simp_rw [this]; simp
  have hs4 : (∑ i : Fin (9 * k ^ 2), ∑ j : Fin (9 * k ^ 2),
      if j.val = 0 ∧ 6 * k ^ 2 < i.val then uI * u0 else 0) = (3 * (k : ℝ) ^ 2 - 1) * (uI * u0) := by
    rw [Finset.sum_comm]
    have : ∀ j : Fin (9 * k ^ 2), (∑ i : Fin (9 * k ^ 2),
        if j.val = 0 ∧ 6 * k ^ 2 < i.val then uI * u0 else 0) =
        if j = z0 then (3 * (k : ℝ) ^ 2 - 1) * (uI * u0) else 0 := by
      intro j
      by_cases hj : j = z0
      · subst hj; simp only [z0, ↓reduceIte, true_and, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hcI]
        rw [Nat.cast_sub (by nlinarith : 1 ≤ 3 * k ^ 2)]; push_cast; ring
      · have hne : j.val ≠ 0 := fun h => hj (Fin.ext h)
        simp [hj, hne]
    simp_rw [this]; simp
  have hs5 : (∑ i : Fin (9 * k ^ 2), ∑ j : Fin (9 * k ^ 2),
      if 1 ≤ i.val ∧ i.val < 6 * k ^ 2 ∧ j.val = i.val + 1 then uP * uP else 0) =
      (6 * (k : ℝ) ^ 2 - 1) * (uP * uP) := by
    have hinner : ∀ i : Fin (9 * k ^ 2), (∑ j : Fin (9 * k ^ 2),
        if 1 ≤ i.val ∧ i.val < 6 * k ^ 2 ∧ j.val = i.val + 1 then uP * uP else 0) =
        if 1 ≤ i.val ∧ i.val < 6 * k ^ 2 then uP * uP else 0 := by
      intro i
      by_cases hi : 1 ≤ i.val ∧ i.val < 6 * k ^ 2
      · simp only [hi, true_and, ↓reduceIte]
        have hlt : i.val + 1 < 9 * k ^ 2 := by nlinarith
        have huniq : ∀ j : Fin (9 * k ^ 2), j.val = i.val + 1 ↔ j = ⟨i.val + 1, hlt⟩ :=
          fun j => by simp [Fin.ext_iff]
        simp_rw [huniq]; simp
      · have hnot : ∀ j : Fin (9 * k ^ 2), ¬ (1 ≤ i.val ∧ i.val < 6 * k ^ 2 ∧ j.val = i.val + 1) :=
          fun j h => hi ⟨h.1, h.2.1⟩
        simp [hi, hnot]
    simp_rw [hinner, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hcE]
    rw [Nat.cast_sub (by nlinarith : 1 ≤ 6 * k ^ 2)]; push_cast; ring
  have hs6 : (∑ i : Fin (9 * k ^ 2), ∑ j : Fin (9 * k ^ 2),
      if 1 ≤ j.val ∧ j.val < 6 * k ^ 2 ∧ i.val = j.val + 1 then uP * uP else 0) =
      (6 * (k : ℝ) ^ 2 - 1) * (uP * uP) := by
    rw [Finset.sum_comm]; exact hs5
  rw [hs1, hs2, hs3, hs4, hs5, hs6]; ring

private lemma counterGraph_spread_ge (k : ℕ) (hk : 10 ≤ k) :
    6 * (k : ℝ) + 1 / (12 * (k : ℝ)) ≤ graphSpread (counterGraph k) := by
  have hk_ge : (10 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk_pos : (0 : ℝ) < (k : ℝ) := by linarith
  have hbdd := rayleigh_bdd (counterGraph k)
  -- Lower bound on maxEig via v_+ = testVec k (9k^2 + 2k) (3k + 2) (3k):
  have hmax : 3 * (k : ℝ) + 2 / 3 + 1 / (24 * (k : ℝ)) ≤ maxEig (counterGraph k) := by
    let vp := testVec k (9 * (k : ℝ) ^ 2 + 2 * (k : ℝ)) (3 * (k : ℝ) + 2) (3 * (k : ℝ))
    have hden : ∑ i : Fin (9 * k ^ 2), vp i ^ 2 =
        162 * (k : ℝ) ^ 4 + 108 * (k : ℝ) ^ 3 + 19 * (k : ℝ) ^ 2 := by
      simp only [vp]; rw [testVec_norm k hk]; ring
    have hnum : quadForm (counterGraph k) vp =
        486 * (k : ℝ) ^ 5 + 432 * (k : ℝ) ^ 4 + 138 * (k : ℝ) ^ 3 + 18 * (k : ℝ) ^ 2 - 24 * (k : ℝ) - 8 := by
      simp only [vp]; rw [testVec_quadForm k hk]; ring
    have hden_pos : 0 < ∑ i : Fin (9 * k ^ 2), vp i ^ 2 := by rw [hden]; positivity
    have hmem : rayleighQuot (counterGraph k) vp ∈
        { r : ℝ | ∃ x : Fin (9 * k ^ 2) → ℝ, (∑ i : Fin (9 * k ^ 2), x i ^ 2) ≠ 0 ∧
          r = rayleighQuot (counterGraph k) x } := ⟨vp, ne_of_gt hden_pos, rfl⟩
    refine le_trans ?_ (le_csSup hbdd.1 hmem)
    unfold rayleighQuot
    rw [le_div_iff₀ hden_pos, hden, hnum]
    have hpoly : 0 ≤ 54 * (k : ℝ) ^ 4 + 20 * (k : ℝ) ^ 3 - 595 * (k : ℝ) ^ 2 - 192 * (k : ℝ) := by
      have hf : 54 * (k : ℝ) ^ 4 + 20 * (k : ℝ) ^ 3 - 595 * (k : ℝ) ^ 2 - 192 * (k : ℝ) =
          (k : ℝ) ^ 2 * (54 * (k : ℝ) ^ 2 - 595) + (k : ℝ) * (20 * (k : ℝ) ^ 2 - 192) := by ring
      rw [hf]
      have h1 : 0 ≤ 54 * (k : ℝ) ^ 2 - 595 := by nlinarith
      have h2 : 0 ≤ 20 * (k : ℝ) ^ 2 - 192 := by nlinarith
      positivity
    have hne : (k : ℝ) ≠ 0 := ne_of_gt hk_pos
    have hid : ((486 * (k : ℝ) ^ 5 + 432 * (k : ℝ) ^ 4 + 138 * (k : ℝ) ^ 3 + 18 * (k : ℝ) ^ 2 - 24 * (k : ℝ) - 8) -
        (3 * (k : ℝ) + 2 / 3 + 1 / (24 * (k : ℝ))) *
          (162 * (k : ℝ) ^ 4 + 108 * (k : ℝ) ^ 3 + 19 * (k : ℝ) ^ 2)) * (24 * (k : ℝ)) =
        54 * (k : ℝ) ^ 4 + 20 * (k : ℝ) ^ 3 - 595 * (k : ℝ) ^ 2 - 192 * (k : ℝ) := by
      field_simp; ring
    nlinarith
  -- Upper bound on minEig via v_- = testVec k (-(9k^2 - 2k)) (3k - 2) (3k):
  have hmin : minEig (counterGraph k) ≤ -3 * (k : ℝ) + 2 / 3 - 1 / (24 * (k : ℝ)) := by
    let vm := testVec k (-(9 * (k : ℝ) ^ 2 - 2 * (k : ℝ))) (3 * (k : ℝ) - 2) (3 * (k : ℝ))
    have hden : ∑ i : Fin (9 * k ^ 2), vm i ^ 2 =
        162 * (k : ℝ) ^ 4 - 108 * (k : ℝ) ^ 3 + 19 * (k : ℝ) ^ 2 := by
      simp only [vm]; rw [testVec_norm k hk]; ring
    have hnum : quadForm (counterGraph k) vm =
        -486 * (k : ℝ) ^ 5 + 432 * (k : ℝ) ^ 4 - 138 * (k : ℝ) ^ 3 + 18 * (k : ℝ) ^ 2 + 24 * (k : ℝ) - 8 := by
      simp only [vm]; rw [testVec_quadForm k hk]; ring
    have hden_pos : 0 < ∑ i : Fin (9 * k ^ 2), vm i ^ 2 := by
      rw [hden]
      have hfac : 162 * (k : ℝ) ^ 4 - 108 * (k : ℝ) ^ 3 + 19 * (k : ℝ) ^ 2 =
          (k : ℝ) ^ 2 * (162 * (k : ℝ) ^ 2 - 108 * (k : ℝ) + 19) := by ring
      have hq : 0 < 162 * (k : ℝ) ^ 2 - 108 * (k : ℝ) + 19 := by nlinarith
      rw [hfac]; positivity
    have hmem : rayleighQuot (counterGraph k) vm ∈
        { r : ℝ | ∃ x : Fin (9 * k ^ 2) → ℝ, (∑ i : Fin (9 * k ^ 2), x i ^ 2) ≠ 0 ∧
          r = rayleighQuot (counterGraph k) x } := ⟨vm, ne_of_gt hden_pos, rfl⟩
    refine le_trans (csInf_le hbdd.2 hmem) ?_
    unfold rayleighQuot
    rw [div_le_iff₀ hden_pos, hden, hnum]
    have hpoly : 0 ≤ 54 * (k : ℝ) ^ 4 - 20 * (k : ℝ) ^ 3 - 595 * (k : ℝ) ^ 2 + 192 * (k : ℝ) := by
      have hf : 54 * (k : ℝ) ^ 4 - 20 * (k : ℝ) ^ 3 - 595 * (k : ℝ) ^ 2 + 192 * (k : ℝ) =
          (k : ℝ) ^ 2 * (54 * (k : ℝ) ^ 2 - 20 * (k : ℝ) - 595) + 192 * (k : ℝ) := by ring
      rw [hf]
      have h1 : 0 ≤ 54 * (k : ℝ) ^ 2 - 20 * (k : ℝ) - 595 := by nlinarith
      positivity
    have hne : (k : ℝ) ≠ 0 := ne_of_gt hk_pos
    have hid : ((-3 * (k : ℝ) + 2 / 3 - 1 / (24 * (k : ℝ))) *
          (162 * (k : ℝ) ^ 4 - 108 * (k : ℝ) ^ 3 + 19 * (k : ℝ) ^ 2) -
        (-486 * (k : ℝ) ^ 5 + 432 * (k : ℝ) ^ 4 - 138 * (k : ℝ) ^ 3 + 18 * (k : ℝ) ^ 2 + 24 * (k : ℝ) - 8)) *
          (24 * (k : ℝ)) =
        54 * (k : ℝ) ^ 4 - 20 * (k : ℝ) ^ 3 - 595 * (k : ℝ) ^ 2 + 192 * (k : ℝ) := by
      field_simp; ring
    nlinarith
  unfold graphSpread
  have hfrac : 1 / (24 * (k : ℝ)) + 1 / (24 * (k : ℝ)) = 1 / (12 * (k : ℝ)) := by ring
  linarith

private theorem main_disproof : ¬ (type_of% @OMA.S_arxiv_2111_11820.main) := by
  rintro ⟨N, hN⟩
  let k : ℕ := max N 10
  have hk10 : 10 ≤ k := le_max_right N 10
  have hN_le : N ≤ 9 * k ^ 2 := by
    have hkN : N ≤ k := le_max_left N 10
    nlinarith
  have hle := hN (9 * k ^ 2) hN_le (counterGraph k) (counterGraph_outerplanar k hk10)
  have hF := fanGraph_spread_le k hk10
  have hH := counterGraph_spread_ge k hk10
  have hk_ge : (10 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk10
  have hgap : 1 / (2 * (k : ℝ) ^ 2) < 1 / (12 * (k : ℝ)) := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  linarith

end OMA.P_arxiv_2111_11820

theorem OMA.disproof : ¬ (type_of% @OMA.S_arxiv_2111_11820.main) :=
  OMA.P_arxiv_2111_11820.main_disproof
