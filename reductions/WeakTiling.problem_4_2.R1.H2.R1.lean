import OMAReductions.R_WeakTiling_problem_4_2_R1

/-!
A weak tiling by at most three points is the first step. For a larger tile
of diameter d, the second step asks for a finite binary exact cover of a
single interval of length 2^d. Two matching boundary windows turn this
patch into a periodic tiling of all the integers.
-/

open scoped ENNReal

namespace OMA.R_WeakTiling_problem_4_2_R1_H2_R1

private theorem on_loop (B : Finset ℤ) (s t d : ℤ) (hp : s < t)
    (match_ends : ∀ i : ℤ, 0 ≤ i → i < d → (s+i ∈ B ↔ t+i ∈ B))
    (x : ℤ) (low : s ≤ x) (high : x < t+d) :
    s+(x-s)%(t-s) ∈ B ↔ x ∈ B := by
  by_cases small : x < t
  · rw [Int.emod_eq_of_lt (by omega) (by omega),show s+(x-s)=x by ring]
  · have prev := on_loop B s t d hp match_ends (x-(t-s)) (by omega) (by omega)
    rw [show x-(t-s)-s = x-s-(t-s) by ring,Int.sub_emod_right] at prev
    have edge := match_ends (x-t) (by omega) (by omega)
    rw [show s+(x-t)=x-(t-s) by ring,show t+(x-t)=x by ring] at edge
    exact prev.trans edge
termination_by (x-s).toNat
decreasing_by omega

private theorem anchor {A : Finset ℤ} {U : Set ℤ} (rows : ∀ j : ℤ, ∃! t : ℤ, t ∈ U ∧ j-t ∈ A) :
    ∃ C : Set ℤ, 0 ∈ C ∧ ∀ j : ℤ, ∃! t : ℤ, t ∈ C ∧ j-t ∈ A := by
  obtain ⟨c,⟨hc,_⟩,_⟩ := rows 0
  refine ⟨{t | t+c ∈ U},by simpa using hc,?_⟩
  intro j
  obtain ⟨v,⟨hu,hv⟩,uniq⟩ := rows (j+c)
  refine ⟨v-c,⟨by simpa using hu,by simpa only [show j-(v-c)=j+c-v by ring] using hv⟩,?_⟩
  rintro t ⟨ht,ha⟩
  have := uniq (t+c) ⟨ht,by simpa only [show j+c-(t+c)=j-t by ring] using ha⟩
  omega

/-- Equal windows of length d give a periodic exact cover, including across the join. -/
theorem finite_window (A : Finset ℤ) (l : ℤ) (d : ℕ)
    (support : ∀ a ∈ A, l ≤ a ∧ a ≤ l+d)
    (B : Finset ℤ) (patch : ∀ j : ℤ, l+d ≤ j → j < l+d+(2^d : ℕ) →
      ∃! t : ℤ, t ∈ B ∧ j-t ∈ A) :
    ∃ C : Set ℤ, 0 ∈ C ∧ ∀ j : ℤ, ∃! t : ℤ, t ∈ C ∧ j-t ∈ A := by
  classical
  let state (x : Fin (2^d+1)) (i : Fin d) := decide ((x.val : ℤ)+i.val ∈ B)
  obtain ⟨x,y,hne,hs⟩ := Fintype.exists_ne_map_eq_of_card_lt state (by simp)
  obtain ⟨s,t,hst,heq⟩ : ∃ s t : Fin (2^d+1), s < t ∧ state s = state t := by
    rcases lt_or_gt_of_ne hne with h|h
    · exact ⟨x,y,h,hs⟩
    · exact ⟨y,x,h,hs.symm⟩
  let S : ℤ := s.val
  let T : ℤ := t.val
  have hp : S < T := by dsimp [S,T]; exact_mod_cast (show s.val < t.val from hst)
  have s0 : 0 ≤ S := by dsimp [S]; positivity
  have tmax : T ≤ ((2^d : ℕ) : ℤ) := by dsimp [T]; exact_mod_cast Nat.le_of_lt_succ t.isLt
  have edge (i : ℤ) (hi : 0 ≤ i) (hd : i < d) : S+i ∈ B ↔ T+i ∈ B := by
    let k : Fin d := ⟨i.toNat,by omega⟩
    have h := congrFun heq k
    simpa only [state,k,Int.toNat_of_nonneg hi,decide_eq_decide,S,T] using h
  let U : Set ℤ := {x | S+(x-S)%(T-S) ∈ B}
  apply anchor (U := U)
  intro j
  let base := l+d+S
  let J := base+(j-base)%(T-S)
  have bot : base ≤ J := by dsimp [J]; have := Int.emod_nonneg (j-base) (by omega : T-S≠0); omega
  have top : J < l+d+T := by
    have := Int.emod_lt_of_pos (j-base) (by omega : 0 < T-S)
    dsimp [J,base] at *
    omega
  have equiv (a : ℤ) (ha : a ∈ A) : j-a ∈ U ↔ J-a ∈ B := by
    obtain ⟨lo,hi⟩ := support a ha
    have hmod : (J-a-S)%(T-S) = (j-a-S)%(T-S) := by
      calc
        _ = ((base-a-S)+(j-base)%(T-S))%(T-S) := by congr 1; dsimp [J]; ring
        _ = ((base-a-S)+(j-base))%(T-S) := Int.add_emod_emod ..
        _ = _ := by congr 1; ring
    change S+(j-a-S)%(T-S) ∈ B ↔ _
    rw [← hmod]
    apply on_loop B S T d hp edge
    · dsimp [base] at bot; omega
    · omega
  obtain ⟨v,⟨hv,ha⟩,unique⟩ := patch J (by dsimp [base] at bot; omega) (by omega)
  let c := j-(J-v)
  have hc : c ∈ U := (equiv (J-v) ha).mpr (by simpa using hv)
  refine ⟨c,⟨hc,by simpa [c] using ha⟩,?_⟩
  rintro z ⟨hz,haz⟩
  have hz' := (equiv (j-z) haz).mp (by simpa using hz)
  have e := unique (J-(j-z)) ⟨hz',by simpa using haz⟩
  dsimp [c]
  omega



/-- The small tiles, with unrestricted positions and fractional weights. -/
def H1 : Prop :=
  ∀ A : Finset ℤ, A.Nonempty → A.card ≤ 3 →
    (∃ w : ℤ → ℝ≥0∞, w 0 = 1 ∧ ∀ j, ∑ a ∈ A, w (j-a) = 1) →
    ∃ C : Set ℤ, 0 ∈ C ∧ ∀ j : ℤ, ∃! t : ℤ, t ∈ C ∧ j-t ∈ A

/-- A finite exact-cover problem. Its centers are drawn from a specified finite interval. -/
def H2 : Prop :=
  ∀ (A : Finset ℤ) (h : A.Nonempty), 4 ≤ A.card →
    (∃ w : ℤ → ℝ≥0∞, w 0 = 1 ∧ ∀ j, ∑ a ∈ A, w (j-a) = 1) →
    let d := (A.max' h - A.min' h).toNat
    ∃ B ∈ (Finset.Ico (0 : ℤ) (((2^d+d : ℕ) : ℤ))).powerset,
      ∀ j ∈ Finset.Ico (A.max' h) (A.max' h + ((2^d : ℕ) : ℤ)),
        (B.filter (fun t => j-t ∈ A)).card = 1

theorem main : H1 → H2 → OMA.R_WeakTiling_problem_4_2_R1.H2 := by
  intro small large A h w
  by_cases hc : A.card ≤ 3
  · exact small A h hc w
  classical
  let l := A.min' h
  let d := (A.max' h - l).toNat
  have hle := A.min'_le (A.max' h) (A.max'_mem h)
  have width : l + (d : ℤ) = A.max' h := by dsimp [d,l]; omega
  obtain ⟨B,_,cover⟩ := large A h (by omega) w
  apply finite_window A l d (fun a ha => ⟨A.min'_le a ha, width ▸ A.le_max' a ha⟩) B
  intro j lo hi
  rw [width] at lo hi
  have card := cover j (Finset.mem_Ico.mpr ⟨lo,hi⟩)
  obtain ⟨c,eq⟩ := Finset.card_eq_one.mp card
  have iff_mem (t : ℤ) : t ∈ B ∧ j-t ∈ A ↔ t = c := by
    have mem := Finset.mem_filter (s := B) (p := fun v : ℤ => j-v ∈ A) (a := t)
    rwa [eq,Finset.mem_singleton,iff_comm] at mem
  exact ⟨c,(iff_mem c).mpr rfl,fun t ht => (iff_mem t).mp ht⟩

end OMA.R_WeakTiling_problem_4_2_R1_H2_R1
