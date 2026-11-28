import OMAReductions.R_Erdos562_erdos_562_R1

/-!
Proves `Erdos562.erdos_562.R1.H1`: the Erdős–Rado (1952) upper bound on hypergraph Ramsey numbers,
`(fun n : ℕ ↦ Real.log^[r - 1] (Combinatorics.hypergraphRamsey r n : ℝ)) =O[atTop] (fun n ↦ (n : ℝ))`
for all `r ≥ 3`.

Proof outline:
1. Base case `r = 1`: `hypergraphRamsey 1 n ≤ 2 * n`.
2. Stepping-up lemma for `r = d + 2`: given any 2-coloring of `(d + 2)`-subsets of `Fin N` with
   `N ≥ pool d M M` (where `pool d M 0 = 1` and `pool d M (t + 1) = 1 + 2 ^ (M ^ d) * pool d M t`),
   greedily extract `M` distinct vertices `v 0, ..., v (M - 1)` such that the color of any
   `(d + 2)`-subset depends only on its first `d + 1` vertices. Taking `M = R_{d+1}(n) + 1` gives
   `R_{d+2}(n) ≤ pool d M M ≤ 2 ^ (2 * M ^ (d + 1))`.
3. Iterated logarithm induction for `r ≥ 2`: `Real.log^[r - 1] ((R_r n : ℝ) + 1) ≤ C * n` eventually,
   using `Real.log (x + A) ≤ Real.log x + A` for `x ≥ 1, A ≥ 0`.
-/

namespace OMA.Proof_Erdos562_R1_H1

open Combinatorics Filter Asymptotics

private def HasRamsey (r n m : ℕ) : Prop :=
  ∀ c : Finset (Fin m) → Bool,
    ∃ S : Finset (Fin m), S.card = n ∧
      ∃ color : Bool, ∀ e : Finset (Fin m), e ⊆ S → e.card = r → c e = color

private lemma hypergraphRamsey_le_of_hasRamsey {r n m : ℕ} (h : HasRamsey r n m) :
    hypergraphRamsey r n ≤ m :=
  Nat.sInf_le h

private lemma hasRamsey_one (n : ℕ) : HasRamsey 1 n (2 * n) := by
  intro c
  classical
  let A : Finset (Fin (2 * n)) := Finset.univ.filter fun x => c {x} = false
  let B : Finset (Fin (2 * n)) := Finset.univ.filter fun x => c {x} = true
  have hsum : A.card + B.card = 2 * n := by
    have hdisj : Disjoint A B := by
      rw [Finset.disjoint_filter]
      intro x _ h1 h2
      simp [h1] at h2
    have hunion : A ∪ B = Finset.univ := by
      ext x
      simp only [A, B, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      cases c {x} <;> simp
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, Fintype.card_fin]
  by_cases hA : n ≤ A.card
  · obtain ⟨S, hSA, hScard⟩ := Finset.exists_subset_card_eq hA
    refine ⟨S, hScard, false, fun e heS hecard => ?_⟩
    obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp hecard
    have hxA : x ∈ A := hSA (heS (Finset.mem_singleton_self x))
    exact (Finset.mem_filter.mp hxA).2
  · have hB : n ≤ B.card := by omega
    obtain ⟨S, hSB, hScard⟩ := Finset.exists_subset_card_eq hB
    refine ⟨S, hScard, true, fun e heS hecard => ?_⟩
    obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp hecard
    have hxB : x ∈ B := hSB (heS (Finset.mem_singleton_self x))
    exact (Finset.mem_filter.mp hxB).2

private lemma hypergraphRamsey_one_le (n : ℕ) : hypergraphRamsey 1 n ≤ 2 * n :=
  hypergraphRamsey_le_of_hasRamsey (hasRamsey_one n)

private lemma exists_large_fiber {α β : Type*} [DecidableEq α] [Fintype β] [DecidableEq β]
    (A : Finset α) (f : α → β) (k : ℕ) (hk : Fintype.card β * k < A.card) :
    ∃ b : β, k + 1 ≤ (A.filter fun x => f x = b).card := by
  by_contra h
  push Not at h
  have hsum : A.card = ∑ b : β, (A.filter fun x => f x = b).card := by
    simpa using Finset.card_eq_sum_card_fiberwise (f := f) (s := A) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)
  have hle : ∑ b : β, (A.filter fun x => f x = b).card ≤ ∑ _ : β, k :=
    Finset.sum_le_sum fun b _ => Nat.le_of_lt_succ (h b)
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hle
  omega

private def pool (d M : ℕ) : ℕ → ℕ
  | 0 => 1
  | t + 1 => 1 + 2 ^ (M ^ d) * pool d M t

private lemma pool_pos (d M t : ℕ) : 1 ≤ pool d M t := by
  cases t <;> simp [pool]

private lemma pool_le (d M t : ℕ) : pool d M t ≤ (2 ^ (M ^ d) + 1) ^ t := by
  induction t with
  | zero => simp [pool]
  | succ t ih =>
    have h1 : 1 ≤ (2 ^ (M ^ d) + 1) ^ t := Nat.one_le_pow _ _ (Nat.succ_pos _)
    calc
      pool d M (t + 1) = 1 + 2 ^ (M ^ d) * pool d M t := rfl
      _ ≤ 1 + 2 ^ (M ^ d) * (2 ^ (M ^ d) + 1) ^ t :=
        Nat.add_le_add_left (Nat.mul_le_mul_left _ ih) 1
      _ ≤ (2 ^ (M ^ d) + 1) ^ t + 2 ^ (M ^ d) * (2 ^ (M ^ d) + 1) ^ t :=
        Nat.add_le_add_right h1 _
      _ = (2 ^ (M ^ d) + 1) ^ (t + 1) := by ring

private lemma pool_le_two_pow (d M : ℕ) (hM : 1 ≤ M) :
    pool d M M ≤ 2 ^ (2 * M ^ (d + 1)) := by
  have hbase : 2 ^ (M ^ d) + 1 ≤ 2 ^ (M ^ d + 1) := by
    have : 1 ≤ 2 ^ (M ^ d) := Nat.one_le_pow _ _ (by decide)
    rw [pow_succ]
    omega
  have h1 : (2 ^ (M ^ d) + 1) ^ M ≤ (2 ^ (M ^ d + 1)) ^ M := Nat.pow_le_pow_left hbase M
  have hexp : (M ^ d + 1) * M ≤ 2 * M ^ (d + 1) := by
    have hMd : 1 ≤ M ^ d := Nat.one_le_pow _ _ (by omega)
    calc
      (M ^ d + 1) * M = M ^ (d + 1) + M := by rw [pow_succ]; ring
      _ ≤ M ^ (d + 1) + M ^ d * M := by nlinarith
      _ = 2 * M ^ (d + 1) := by rw [pow_succ]; ring
  calc
    pool d M M ≤ (2 ^ (M ^ d) + 1) ^ M := pool_le d M M
    _ ≤ (2 ^ (M ^ d + 1)) ^ M := h1
    _ = 2 ^ ((M ^ d + 1) * M) := by rw [← pow_mul]
    _ ≤ 2 ^ (2 * M ^ (d + 1)) := Nat.pow_le_pow_right (by decide) hexp

private lemma finset_card_eq_image_fin {α : Type*} [DecidableEq α] {k d : ℕ}
    (v : Fin k → α) (F : Finset α) (hFsub : F ⊆ Finset.univ.image v) (hFcard : F.card = d) :
    ∃ u : Fin d → Fin k, Finset.univ.image (v ∘ u) = F := by
  classical
  let e : Fin d ≃ F := (Fintype.equivFinOfCardEq (by simpa using hFcard)).symm
  have hpre : ∀ i : Fin d, ∃ j : Fin k, v j = (e i).1 := by
    intro i
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp (hFsub (e i).2)
    exact ⟨j, hj⟩
  choose u hu using hpre
  refine ⟨u, ?_⟩
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, Function.comp_apply, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    rw [hu i]
    exact (e i).2
  · intro hx
    refine ⟨e.symm ⟨x, hx⟩, ?_⟩
    rw [hu]
    simp

/-- From the greedy construction at `k = M`, every `(d + 1)`-subset of `{v 0, ..., v (M - 2)}`
gets a well-defined color when extended by any later `v j`, including `v (M - 1)`. -/
private lemma erdos_rado_step_seq {d M N : ℕ} (c : Finset (Fin N) → Bool)
    (hN : pool d M M ≤ N) :
    ∃ v : Fin M → Fin N,
      Function.Injective v ∧
      ∀ (F : Finset (Fin M)) (j₁ j₂ : Fin M),
        F.card = d + 1 →
        (∀ i ∈ F, i < j₁) → (∀ i ∈ F, i < j₂) →
        c (insert (v j₁) (F.image v)) = c (insert (v j₂) (F.image v)) := by
  classical
  suffices h : ∀ k : ℕ, k ≤ M →
      ∃ (v : Fin k → Fin N) (A : Finset (Fin N)),
        Function.Injective v ∧
        (∀ i : Fin k, v i ∉ A) ∧
        pool d M (M - k) ≤ A.card ∧
        (∀ F : Finset (Fin k), F.card = d + 1 →
          ∀ x ∈ A, ∀ y ∈ A, c (insert x (F.image v)) = c (insert y (F.image v))) ∧
        (∀ (F : Finset (Fin k)) (j₁ j₂ : Fin k), F.card = d + 1 →
          (∀ i ∈ F, i < j₁) → (∀ i ∈ F, i < j₂) →
          c (insert (v j₁) (F.image v)) = c (insert (v j₂) (F.image v))) ∧
        (∀ (F : Finset (Fin k)) (j : Fin k) (x : Fin N), F.card = d + 1 →
          (∀ i ∈ F, i < j) → x ∈ A →
          c (insert (v j) (F.image v)) = c (insert x (F.image v))) by
    obtain ⟨v, _, hv_inj, _, _, _, hseq, _⟩ := h M (le_refl M)
    exact ⟨v, hv_inj, hseq⟩
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨Fin.elim0, Finset.univ, fun i => i.elim0, fun i => i.elim0, by simpa using hN,
      ?_, ?_, ?_⟩
    · intro F hF; exfalso; rw [Finset.eq_empty_of_isEmpty F] at hF; simp at hF
    · intro F j₁; exact j₁.elim0
    · intro F j; exact j.elim0
  | succ k ih =>
    intro hkM
    obtain ⟨v, A, hv_inj, hv_disj, hA_card, hInvA, hSeq, hCross⟩ := ih (Nat.le_of_succ_le hkM)
    have hsub : M - k = (M - (k + 1)) + 1 := by omega
    rw [hsub] at hA_card
    have hA_ne : A.Nonempty := Finset.card_pos.mp (lt_of_lt_of_le (pool_pos d M _) hA_card)
    obtain ⟨w, hwA⟩ := hA_ne
    let A0 : Finset (Fin N) := A.erase w
    have hA0_card : 2 ^ (M ^ d) * pool d M (M - (k + 1)) ≤ A0.card := by
      have her : A0.card + 1 = A.card := by simpa [A0] using Finset.card_erase_add_one hwA
      have hdef : pool d M ((M - (k + 1)) + 1) = 1 + 2 ^ (M ^ d) * pool d M (M - (k + 1)) := rfl
      omega
    let f : Fin N → ((Fin d → Fin k) → Bool) :=
      fun x u => c (insert x (insert w (Finset.univ.image (v ∘ u))))
    have hcardβ : Fintype.card ((Fin d → Fin k) → Bool) ≤ 2 ^ (M ^ d) := by
      simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
      exact Nat.pow_le_pow_right (by decide) (Nat.pow_le_pow_left (by omega) d)
    have hp_pos : 1 ≤ pool d M (M - (k + 1)) := pool_pos d M _
    have hstrict : Fintype.card ((Fin d → Fin k) → Bool) * (pool d M (M - (k + 1)) - 1) < A0.card := by
      have hmul : Fintype.card ((Fin d → Fin k) → Bool) * (pool d M (M - (k + 1)) - 1) ≤
          2 ^ (M ^ d) * (pool d M (M - (k + 1)) - 1) :=
        Nat.mul_le_mul_right _ hcardβ
      have hpow_pos : 1 ≤ 2 ^ (M ^ d) := Nat.one_le_pow _ _ (by decide)
      have hlt : 2 ^ (M ^ d) * (pool d M (M - (k + 1)) - 1) < 2 ^ (M ^ d) * pool d M (M - (k + 1)) :=
        Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
      omega
    obtain ⟨g, hg_card⟩ := exists_large_fiber A0 f (pool d M (M - (k + 1)) - 1) hstrict
    let A' : Finset (Fin N) := A0.filter fun x => f x = g
    have hA'_card : pool d M (M - (k + 1)) ≤ A'.card := by
      change pool d M (M - (k + 1)) ≤ (A0.filter fun x => f x = g).card
      omega
    have hA'_sub_A0 : A' ⊆ A0 := Finset.filter_subset _ _
    have hA'_sub_A : A' ⊆ A := hA'_sub_A0.trans (Finset.erase_subset _ _)
    let v' : Fin (k + 1) → Fin N := Fin.snoc v w
    have hv'_inj : Function.Injective v' := by
      intro i j
      refine Fin.lastCases ?_ (fun i' => ?_) i <;> refine Fin.lastCases ?_ (fun j' => ?_) j
      · intro _; rfl
      · intro h
        simp only [v', Fin.snoc_last, Fin.snoc_castSucc] at h
        exact absurd (h ▸ hwA) (hv_disj j')
      · intro h
        simp only [v', Fin.snoc_last, Fin.snoc_castSucc] at h
        exact absurd (h.symm ▸ hwA) (hv_disj i')
      · intro h
        simp only [v', Fin.snoc_castSucc] at h
        exact congrArg Fin.castSucc (hv_inj h)
    have hv'_disj : ∀ i : Fin (k + 1), v' i ∉ A' := by
      intro i hi
      refine Fin.lastCases ?_ (fun i' => ?_) i hi
      · intro h; simp only [v', Fin.snoc_last] at h; exact (Finset.notMem_erase w A) (hA'_sub_A0 h)
      · intro h; simp only [v', Fin.snoc_castSucc] at h; exact hv_disj i' (hA'_sub_A h)
    have hpull : ∀ (F : Finset (Fin (k + 1))), Fin.last k ∉ F →
        ∃ F0 : Finset (Fin k), F = F0.image Fin.castSucc ∧ F0.card = F.card ∧ F.image v' = F0.image v := by
      intro F hlast
      let F0 : Finset (Fin k) := Finset.univ.filter fun i => i.castSucc ∈ F
      have hFeq : F = F0.image Fin.castSucc := by
        ext j
        simp only [F0, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro hj
          refine Fin.lastCases (fun h => absurd h hlast) (fun j' h => ⟨j', h, rfl⟩) j hj
        · rintro ⟨i, hi, rfl⟩; exact hi
      have hcard : F0.card = F.card := by
        rw [hFeq, Finset.card_image_of_injective _ (Fin.castSucc_injective k)]
      have himg : F.image v' = F0.image v := by
        rw [hFeq, Finset.image_image]
        congr 1; ext i; simp [v']
      exact ⟨F0, hFeq, hcard, himg⟩
    have hInvA' : ∀ F : Finset (Fin (k + 1)), F.card = d + 1 →
        ∀ x ∈ A', ∀ y ∈ A', c (insert x (F.image v')) = c (insert y (F.image v')) := by
      intro F hFcard x hx y hy
      by_cases hlast : Fin.last k ∈ F
      · have hnotlast : Fin.last k ∉ F.erase (Fin.last k) := Finset.notMem_erase _ _
        obtain ⟨F0, _, hF0card, hF0img⟩ := hpull (F.erase (Fin.last k)) hnotlast
        have hF0d : F0.card = d := by
          have := Finset.card_erase_add_one hlast
          omega
        obtain ⟨u, hu⟩ := finset_card_eq_image_fin v (F0.image v)
          (Finset.image_subset_image (Finset.subset_univ _))
          (by rw [Finset.card_image_of_injective _ hv_inj, hF0d])
        have hw_eq : w = v' (Fin.last k) := by simp [v']
        have hFimg : F.image v' = insert w (Finset.univ.image (v ∘ u)) := by
          rw [hu, ← hF0img, hw_eq, ← Finset.image_insert, Finset.insert_erase hlast]
        have hfx : f x = g := (Finset.mem_filter.mp hx).2
        have hfy : f y = g := (Finset.mem_filter.mp hy).2
        have hfg : f x u = f y u := by rw [hfx, hfy]
        simpa [f, hFimg] using hfg
      · obtain ⟨F0, _, hF0card, hF0img⟩ := hpull F hlast
        rw [hF0img]
        exact hInvA F0 (by omega) x (hA'_sub_A hx) y (hA'_sub_A hy)
    have hSeq' : ∀ (F : Finset (Fin (k + 1))) (j₁ j₂ : Fin (k + 1)), F.card = d + 1 →
        (∀ i ∈ F, i < j₁) → (∀ i ∈ F, i < j₂) →
        c (insert (v' j₁) (F.image v')) = c (insert (v' j₂) (F.image v')) := by
      intro F j₁ j₂ hFcard hj₁ hj₂
      have hlast : Fin.last k ∉ F := by
        intro hl
        have hlt := hj₁ (Fin.last k) hl
        exact absurd hlt (not_lt.mpr (Fin.le_last j₁))
      obtain ⟨F0, hFeq, hF0card, hF0img⟩ := hpull F hlast
      rw [hF0img]
      refine Fin.lastCases ?_ (fun j₁' => ?_) j₁ hj₁
      · intro _
        refine Fin.lastCases (fun _ => rfl) (fun j₂' hj₂' => ?_) j₂ hj₂
        simp only [v', Fin.snoc_last, Fin.snoc_castSucc]
        have hlt2 : ∀ i ∈ F0, i < j₂' := fun i hi => by
          have := hj₂' i.castSucc (hFeq ▸ Finset.mem_image_of_mem _ hi)
          exact Fin.castSucc_lt_castSucc_iff.mp this
        exact (hCross F0 j₂' w (by omega) hlt2 hwA).symm
      · intro hj₁'
        have hlt1 : ∀ i ∈ F0, i < j₁' := fun i hi => by
          have := hj₁' i.castSucc (hFeq ▸ Finset.mem_image_of_mem _ hi)
          exact Fin.castSucc_lt_castSucc_iff.mp this
        refine Fin.lastCases ?_ (fun j₂' hj₂' => ?_) j₂ hj₂
        · intro _
          simp only [v', Fin.snoc_last, Fin.snoc_castSucc]
          exact hCross F0 j₁' w (by omega) hlt1 hwA
        · simp only [v', Fin.snoc_castSucc]
          have hlt2 : ∀ i ∈ F0, i < j₂' := fun i hi => by
            have := hj₂' i.castSucc (hFeq ▸ Finset.mem_image_of_mem _ hi)
            exact Fin.castSucc_lt_castSucc_iff.mp this
          exact hSeq F0 j₁' j₂' (by omega) hlt1 hlt2
    have hCross' : ∀ (F : Finset (Fin (k + 1))) (j : Fin (k + 1)) (x : Fin N), F.card = d + 1 →
        (∀ i ∈ F, i < j) → x ∈ A' →
        c (insert (v' j) (F.image v')) = c (insert x (F.image v')) := by
      intro F j x hFcard hj hx
      have hlast : Fin.last k ∉ F := by
        intro hl
        exact absurd (hj (Fin.last k) hl) (not_lt.mpr (Fin.le_last j))
      obtain ⟨F0, hFeq, hF0card, hF0img⟩ := hpull F hlast
      rw [hF0img]
      refine Fin.lastCases ?_ (fun j' hj' => ?_) j hj
      · intro _
        simp only [v', Fin.snoc_last]
        exact hInvA F0 (by omega) w hwA x (hA'_sub_A hx)
      · simp only [v', Fin.snoc_castSucc]
        have hlt : ∀ i ∈ F0, i < j' := fun i hi => by
          have := hj' i.castSucc (hFeq ▸ Finset.mem_image_of_mem _ hi)
          exact Fin.castSucc_lt_castSucc_iff.mp this
        exact hCross F0 j' x (by omega) hlt (hA'_sub_A hx)
    exact ⟨v', A', hv'_inj, hv'_disj, hA'_card, hInvA', hSeq', hCross'⟩

private lemma hasRamsey_succ {d n m : ℕ} (hm : HasRamsey (d + 1) n m) :
    HasRamsey (d + 2) (n + 1) (pool d (m + 1) (m + 1)) := by
  classical
  intro c
  obtain ⟨v, hv_inj, hseq⟩ := erdos_rado_step_seq (d := d) (M := m + 1) c (le_refl _)
  let c' : Finset (Fin m) → Bool :=
    fun E => c (insert (v (Fin.last m)) ((E.image Fin.castSucc).image v))
  obtain ⟨S0, hS0card, col, hS0mono⟩ := hm c'
  let S : Finset (Fin (m + 1)) := insert (Fin.last m) (S0.image Fin.castSucc)
  have hlast_notmem : Fin.last m ∉ S0.image Fin.castSucc := by
    simp only [Finset.mem_image, not_exists, not_and]
    intro i _ h
    exact Fin.castSucc_ne_last i h
  have hScard : (S.image v).card = n + 1 := by
    rw [Finset.card_image_of_injective _ hv_inj, Finset.card_insert_of_notMem hlast_notmem,
      Finset.card_image_of_injective _ (Fin.castSucc_injective m), hS0card]
  refine ⟨S.image v, hScard, col, ?_⟩
  intro e heS hecard
  let U : Finset (Fin (m + 1)) := S.filter fun i => v i ∈ e
  have hU_img : U.image v = e := by
    ext z
    simp only [U, Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨i, ⟨_, hzi⟩, rfl⟩; exact hzi
    · intro hz
      obtain ⟨i, hiS, rfl⟩ := Finset.mem_image.mp (heS hz)
      exact ⟨i, ⟨hiS, hz⟩, rfl⟩
  have hU_card : U.card = d + 2 := by
    rw [← Finset.card_image_of_injective U hv_inj, hU_img, hecard]
  have hU_ne : U.Nonempty := Finset.card_pos.mp (by omega)
  let top : Fin (m + 1) := U.max' hU_ne
  have htop_mem : top ∈ U := Finset.max'_mem U hU_ne
  let F : Finset (Fin (m + 1)) := U.erase top
  have hF_card : F.card = d + 1 := by
    have := Finset.card_erase_add_one htop_mem
    dsimp [F]
    omega
  have hF_lt_top : ∀ i ∈ F, i < top := by
    intro i hi
    have hne : i ≠ top := (Finset.mem_erase.mp hi).1
    have hle : i ≤ top := Finset.le_max' U i (Finset.mem_erase.mp hi).2
    exact lt_of_le_of_ne hle hne
  have hF_lt_last : ∀ i ∈ F, i < Fin.last m :=
    fun i hi => lt_of_lt_of_le (hF_lt_top i hi) (Fin.le_last top)
  have hF_sub_S0 : F ⊆ S0.image Fin.castSucc := by
    intro i hi
    have hiU : i ∈ U := (Finset.mem_erase.mp hi).2
    have hiS : i ∈ S := (Finset.mem_filter.mp hiU).1
    rcases Finset.mem_insert.mp hiS with rfl | hmem
    · exact absurd (hF_lt_last _ hi) (lt_irrefl _)
    · exact hmem
  let E : Finset (Fin m) := S0.filter fun i => i.castSucc ∈ F
  have hE_sub : E ⊆ S0 := Finset.filter_subset _ _
  have hE_img : E.image Fin.castSucc = F := by
    ext j
    simp only [E, Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨i, ⟨_, hiF⟩, rfl⟩; exact hiF
    · intro hjF
      obtain ⟨i, hiS0, rfl⟩ := Finset.mem_image.mp (hF_sub_S0 hjF)
      exact ⟨i, ⟨hiS0, hjF⟩, rfl⟩
  have hE_card : E.card = d + 1 := by
    rw [← Finset.card_image_of_injective E (Fin.castSucc_injective m), hE_img, hF_card]
  have he_eq : e = insert (v top) (F.image v) := by
    rw [← hU_img, ← Finset.image_insert, Finset.insert_erase htop_mem]
  rw [he_eq, hseq F top (Fin.last m) hF_card hF_lt_top hF_lt_last, ← hE_img]
  exact hS0mono E hE_sub hE_card

private lemma hasRamsey_mono_n {r n₁ n₂ m : ℕ} (h : HasRamsey r n₂ m) (hle : n₁ ≤ n₂) :
    HasRamsey r n₁ m := by
  intro c
  obtain ⟨S, hScard, col, hmono⟩ := h c
  obtain ⟨S', hS'sub, hS'card⟩ := Finset.exists_subset_card_eq (hScard ▸ hle)
  exact ⟨S', hS'card, col, fun e he => hmono e (he.trans hS'sub)⟩

private lemma exists_hasRamsey : ∀ r n : ℕ, 1 ≤ r → ∃ m : ℕ, HasRamsey r n m := by
  intro r
  induction r with
  | zero => intro _ h; omega
  | succ r ih =>
    cases r with
    | zero => intro n _; exact ⟨2 * n, hasRamsey_one n⟩
    | succ d =>
      intro n _
      obtain ⟨m, hm⟩ := ih n (by omega)
      exact ⟨pool d (m + 1) (m + 1), hasRamsey_mono_n (hasRamsey_succ hm) (Nat.le_succ n)⟩

private lemma hypergraphRamsey_succ_le (d n : ℕ) :
    hypergraphRamsey (d + 2) n ≤ 2 ^ (2 * (hypergraphRamsey (d + 1) n + 1) ^ (d + 1)) := by
  have hne : { m | HasRamsey (d + 1) n m }.Nonempty := exists_hasRamsey (d + 1) n (by omega)
  have hm : HasRamsey (d + 1) n (hypergraphRamsey (d + 1) n) := Nat.sInf_mem hne
  have hstep : HasRamsey (d + 2) n (pool d (hypergraphRamsey (d + 1) n + 1) (hypergraphRamsey (d + 1) n + 1)) :=
    hasRamsey_mono_n (hasRamsey_succ hm) (Nat.le_succ n)
  exact (hypergraphRamsey_le_of_hasRamsey hstep).trans (pool_le_two_pow d _ (by omega))

private lemma le_hypergraphRamsey_of_pos (r n : ℕ) (hr : 1 ≤ r) : n ≤ hypergraphRamsey r n :=
  le_hypergraphRamsey r n (exists_hasRamsey r n hr)

private lemma log_add_le_log_add {x A : ℝ} (hx : 1 ≤ x) (hA : 0 ≤ A) :
    Real.log (x + A) ≤ Real.log x + A := by
  have hxpos : 0 < x := by linarith
  have hxa : x + A ≤ x * Real.exp A := by
    have hexp : A + 1 ≤ Real.exp A := Real.add_one_le_exp A
    nlinarith
  calc
    Real.log (x + A) ≤ Real.log (x * Real.exp A) :=
      Real.log_le_log (by linarith) hxa
    _ = Real.log x + Real.log (Real.exp A) :=
      Real.log_mul hxpos.ne' (Real.exp_pos A).ne'
    _ = Real.log x + A := by rw [Real.log_exp]

private lemma log_iter_mono : ∀ k : ℕ, ∀ {x y : ℝ},
    (∀ j < k, 0 < Real.log^[j] x) → x ≤ y → Real.log^[k] x ≤ Real.log^[k] y := by
  intro k
  induction k with
  | zero => intro _ _ _ h; exact h
  | succ k ih =>
    intro x y hpos hxy
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    have hprev := ih (fun j hj => hpos j (Nat.lt_succ_of_lt hj)) hxy
    exact Real.log_le_log (hpos k (Nat.lt_succ_self k)) hprev

private lemma log_iter_add_le : ∀ k : ℕ, ∀ {x A : ℝ}, 0 ≤ A →
    (∀ j < k, 1 ≤ Real.log^[j] x) →
    Real.log^[k] (x + A) ≤ Real.log^[k] x + A := by
  intro k
  induction k with
  | zero => intro _ _ _ _; exact le_refl _
  | succ k ih =>
    intro x A hA hge
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    have hprev : Real.log^[k] (x + A) ≤ Real.log^[k] x + A :=
      ih hA (fun j hj => hge j (Nat.lt_succ_of_lt hj))
    have hxk : 1 ≤ Real.log^[k] x := hge k (Nat.lt_succ_self k)
    have hpos : 0 < Real.log^[k] (x + A) := by
      have hmono : Real.log^[k] x ≤ Real.log^[k] (x + A) :=
        log_iter_mono k (fun j hj => lt_of_lt_of_le zero_lt_one (hge j (Nat.lt_succ_of_lt hj))) (by linarith)
      linarith
    exact (Real.log_le_log hpos hprev).trans (log_add_le_log_add hxk hA)

private lemma tendsto_log_iter (k : ℕ) :
    Tendsto (fun x : ℝ => Real.log^[k] x) atTop atTop := by
  induction k with
  | zero => exact tendsto_id
  | succ k ih =>
    convert Real.tendsto_log_atTop.comp ih using 1
    ext x
    exact Function.iterate_succ_apply' Real.log k x

private lemma log_iter_bound : ∀ r : ℕ, 2 ≤ r →
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      Real.log^[r - 1] ((hypergraphRamsey r n : ℝ) + 1) ≤ C * (n : ℝ) := by
  intro r
  induction r with
  | zero => intro h; omega
  | succ r ih =>
    intro hr
    by_cases hr2 : r = 1
    · subst hr2
      refine ⟨5, by norm_num, ?_⟩
      filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
      have hR1 : hypergraphRamsey 1 n ≤ 2 * n := hypergraphRamsey_one_le n
      have hR2 : hypergraphRamsey 2 n ≤ 2 ^ (2 * (hypergraphRamsey 1 n + 1) ^ 1) :=
        hypergraphRamsey_succ_le 0 n
      have hexp : 2 * (hypergraphRamsey 1 n + 1) ^ 1 ≤ 4 * n + 2 := by
        rw [pow_one]
        omega
      have hR2' : hypergraphRamsey 2 n + 1 ≤ 2 ^ (4 * n + 3) := by
        have h1 : hypergraphRamsey 2 n ≤ 2 ^ (4 * n + 2) :=
          hR2.trans (Nat.pow_le_pow_right (by decide) hexp)
        have h2 : 1 ≤ 2 ^ (4 * n + 2) := Nat.one_le_pow _ _ (by decide)
        rw [pow_succ]
        omega
      have hR2r : (hypergraphRamsey 2 n : ℝ) + 1 ≤ (2 : ℝ) ^ (4 * n + 3) := by
        exact_mod_cast hR2'
      simp only [Nat.add_sub_cancel, Function.iterate_one]
      have hlog : Real.log ((hypergraphRamsey 2 n : ℝ) + 1) ≤ ((4 * n + 3 : ℕ) : ℝ) * Real.log 2 := by
        calc
          Real.log ((hypergraphRamsey 2 n : ℝ) + 1) ≤ Real.log ((2 : ℝ) ^ (4 * n + 3)) :=
            Real.log_le_log (by positivity) hR2r
          _ = ((4 * n + 3 : ℕ) : ℝ) * Real.log 2 := Real.log_pow 2 (4 * n + 3)
      have hlog2 : Real.log 2 ≤ 7 / 10 := by
        have := Real.log_two_lt_d9
        linarith
      push_cast at hlog
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
    · have hrge2 : 2 ≤ r := by omega
      obtain ⟨C, hC, hIH⟩ := ih hrge2
      let d : ℕ := r - 1
      have hd_eq : r = d + 1 := by omega
      have hR_tendsto : Tendsto (fun n : ℕ => (hypergraphRamsey r n : ℝ) + 1) atTop atTop := by
        apply tendsto_atTop_mono (f := fun n : ℕ => (n : ℝ))
        · intro n
          have : (n : ℝ) ≤ (hypergraphRamsey r n : ℝ) := by
            exact_mod_cast le_hypergraphRamsey_of_pos r n (by omega)
          linarith
        · exact tendsto_natCast_atTop_atTop
      have hR_succ_tendsto : Tendsto (fun n : ℕ => (hypergraphRamsey (r + 1) n : ℝ) + 1) atTop atTop := by
        apply tendsto_atTop_mono (f := fun n : ℕ => (n : ℝ))
        · intro n
          have : (n : ℝ) ≤ (hypergraphRamsey (r + 1) n : ℝ) := by
            exact_mod_cast le_hypergraphRamsey_of_pos (r + 1) n (by omega)
          linarith
        · exact tendsto_natCast_atTop_atTop
      have hall_r : ∀ j < r, ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log^[j] ((hypergraphRamsey r n : ℝ) + 1) :=
        fun j _ => ((tendsto_log_iter j).comp hR_tendsto).eventually_ge_atTop 1
      have hall_r1 : ∀ j < r, ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log^[j] ((hypergraphRamsey (r + 1) n : ℝ) + 1) :=
        fun j _ => ((tendsto_log_iter j).comp hR_succ_tendsto).eventually_ge_atTop 1
      have hbig_log : ∀ᶠ n : ℕ in atTop, Real.log 3 ≤ Real.log ((hypergraphRamsey r n : ℝ) + 1) :=
        ((tendsto_log_iter 1).comp hR_tendsto).eventually_ge_atTop (Real.log 3)
      have hbig_n : ∀ᶠ n : ℕ in atTop, Real.log (3 + (r : ℝ)) ≤ (n : ℝ) :=
        tendsto_natCast_atTop_atTop.eventually_ge_atTop (Real.log (3 + (r : ℝ)))
      have hfin_r : ∀ᶠ n : ℕ in atTop, ∀ j < r, 1 ≤ Real.log^[j] ((hypergraphRamsey r n : ℝ) + 1) := by
        have h := (Finset.eventually_all (I := Finset.range r)).mpr (fun j hj => hall_r j (Finset.mem_range.mp hj))
        filter_upwards [h] with n hn j hj using hn j (Finset.mem_range.mpr hj)
      have hfin_r1 : ∀ᶠ n : ℕ in atTop, ∀ j < r, 1 ≤ Real.log^[j] ((hypergraphRamsey (r + 1) n : ℝ) + 1) := by
        have h := (Finset.eventually_all (I := Finset.range r)).mpr (fun j hj => hall_r1 j (Finset.mem_range.mp hj))
        filter_upwards [h] with n hn j hj using hn j (Finset.mem_range.mpr hj)
      refine ⟨(r + 1) * C + 2, by positivity, ?_⟩
      filter_upwards [hIH, hfin_r, hfin_r1, hbig_log, hbig_n, eventually_ge_atTop (1 : ℕ)] with
        n hIHn hge_r hge_r1 hlog3 hbn hn1
      have hRstep : hypergraphRamsey (r + 1) n ≤ 2 ^ (2 * (hypergraphRamsey r n + 1) ^ r) := by
        have hr1 : r + 1 = d + 2 := by omega
        rw [hr1, hd_eq]
        exact hypergraphRamsey_succ_le d n
      have hRstep1 : hypergraphRamsey (r + 1) n + 1 ≤ 2 ^ (2 * (hypergraphRamsey r n + 1) ^ r + 1) := by
        have : 1 ≤ 2 ^ (2 * (hypergraphRamsey r n + 1) ^ r) := Nat.one_le_pow _ _ (by decide)
        rw [pow_succ]
        omega
      have hRstep1_r : (hypergraphRamsey (r + 1) n : ℝ) + 1 ≤ (2 : ℝ) ^ (2 * (hypergraphRamsey r n + 1) ^ r + 1) := by
        exact_mod_cast hRstep1
      have hlog1 : Real.log ((hypergraphRamsey (r + 1) n : ℝ) + 1) ≤
          3 * ((hypergraphRamsey r n : ℝ) + 1) ^ r := by
        have h1 : Real.log ((hypergraphRamsey (r + 1) n : ℝ) + 1) ≤
            ((2 * (hypergraphRamsey r n + 1) ^ r + 1 : ℕ) : ℝ) * Real.log 2 := by
          calc
            Real.log ((hypergraphRamsey (r + 1) n : ℝ) + 1) ≤
                Real.log ((2 : ℝ) ^ (2 * (hypergraphRamsey r n + 1) ^ r + 1)) :=
              Real.log_le_log (by positivity) hRstep1_r
            _ = ((2 * (hypergraphRamsey r n + 1) ^ r + 1 : ℕ) : ℝ) * Real.log 2 :=
              Real.log_pow 2 _
        have hlog2 : Real.log 2 ≤ 1 := by
          have := Real.log_two_lt_d9
          linarith
        have hpow1 : (1 : ℝ) ≤ ((hypergraphRamsey r n : ℝ) + 1) ^ r :=
          one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) (hypergraphRamsey r n)])
        push_cast at h1
        nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
      have hlog2 : Real.log (Real.log ((hypergraphRamsey (r + 1) n : ℝ) + 1)) ≤
          Real.log 3 + (r : ℝ) * Real.log ((hypergraphRamsey r n : ℝ) + 1) := by
        have hlpos : 0 < Real.log ((hypergraphRamsey (r + 1) n : ℝ) + 1) := by
          have h1 : 1 ≤ Real.log ((hypergraphRamsey (r + 1) n : ℝ) + 1) := by
            simpa using hge_r1 1 (by omega)
          linarith
        have hRrpos : 0 < (hypergraphRamsey r n : ℝ) + 1 := by positivity
        calc
          Real.log (Real.log ((hypergraphRamsey (r + 1) n : ℝ) + 1))
            ≤ Real.log (3 * ((hypergraphRamsey r n : ℝ) + 1) ^ r) :=
              Real.log_le_log hlpos hlog1
          _ = Real.log 3 + Real.log (((hypergraphRamsey r n : ℝ) + 1) ^ r) :=
              Real.log_mul (by norm_num) (pow_ne_zero r hRrpos.ne')
          _ = Real.log 3 + (r : ℝ) * Real.log ((hypergraphRamsey r n : ℝ) + 1) := by
              rw [Real.log_pow]
      by_cases hr_eq2 : r = 2
      · subst hr_eq2
        simp only [Nat.add_sub_cancel, Function.iterate_succ_apply', Function.iterate_zero, id_eq] at hIHn ⊢
        have hn_r : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
        have hlog3_le : Real.log 3 ≤ 2 := by
          have := Real.add_one_le_exp (2 : ℝ)
          have h3 : (3 : ℝ) ≤ Real.exp 2 := by linarith
          calc Real.log 3 ≤ Real.log (Real.exp 2) := Real.log_le_log (by norm_num) h3
            _ = 2 := Real.log_exp 2
        nlinarith
      · have hrge3 : 3 ≤ r := by omega
        have hlog2' : Real.log^[2] ((hypergraphRamsey (r + 1) n : ℝ) + 1) ≤
            (1 + (r : ℝ)) * Real.log ((hypergraphRamsey r n : ℝ) + 1) := by
          simp only [Function.iterate_succ_apply', Function.iterate_zero, id_eq]
          linarith
        have hlog3_step : Real.log^[3] ((hypergraphRamsey (r + 1) n : ℝ) + 1) ≤
            Real.log^[2] ((hypergraphRamsey r n : ℝ) + 1) + Real.log (3 + (r : ℝ)) := by
          have hpos2 : 0 < Real.log^[2] ((hypergraphRamsey (r + 1) n : ℝ) + 1) :=
            lt_of_lt_of_le zero_lt_one (hge_r1 2 (by omega))
          have hpos_r1 : 0 < Real.log ((hypergraphRamsey r n : ℝ) + 1) := by
            have h1 : 1 ≤ Real.log ((hypergraphRamsey r n : ℝ) + 1) := by
              simpa using hge_r 1 (by omega)
            linarith
          have h1 : Real.log (Real.log^[2] ((hypergraphRamsey (r + 1) n : ℝ) + 1)) ≤
              Real.log ((1 + (r : ℝ)) * Real.log ((hypergraphRamsey r n : ℝ) + 1)) :=
            Real.log_le_log hpos2 hlog2'
          rw [Real.log_mul (by positivity) hpos_r1.ne'] at h1
          have hlogr : Real.log (1 + (r : ℝ)) ≤ Real.log (3 + (r : ℝ)) :=
            Real.log_le_log (by positivity) (by linarith)
          change Real.log (Real.log^[2] ((hypergraphRamsey (r + 1) n : ℝ) + 1)) ≤
            Real.log (Real.log ((hypergraphRamsey r n : ℝ) + 1)) + Real.log (3 + (r : ℝ))
          linarith
        have hA_nonneg : 0 ≤ Real.log (3 + (r : ℝ)) :=
          Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) r])
        have hiter_split : ∀ x : ℝ, Real.log^[r] x = Real.log^[r - 3] (Real.log^[3] x) := by
          intro x
          rw [← Function.iterate_add_apply]
          congr 1
          omega
        have hiter_split_r : ∀ x : ℝ, Real.log^[r - 1] x = Real.log^[r - 3] (Real.log^[2] x) := by
          intro x
          rw [← Function.iterate_add_apply]
          congr 1
          omega
        have hstep_mono : Real.log^[r - 3] (Real.log^[3] ((hypergraphRamsey (r + 1) n : ℝ) + 1)) ≤
            Real.log^[r - 3] (Real.log^[2] ((hypergraphRamsey r n : ℝ) + 1) + Real.log (3 + (r : ℝ))) := by
          apply log_iter_mono (r - 3)
          · intro j hj
            rw [← Function.iterate_add_apply]
            exact lt_of_lt_of_le zero_lt_one (hge_r1 (j + 3) (by omega))
          · exact hlog3_step
        have hstep_add : Real.log^[r - 3] (Real.log^[2] ((hypergraphRamsey r n : ℝ) + 1) + Real.log (3 + (r : ℝ))) ≤
            Real.log^[r - 3] (Real.log^[2] ((hypergraphRamsey r n : ℝ) + 1)) + Real.log (3 + (r : ℝ)) := by
          apply log_iter_add_le (r - 3) hA_nonneg
          intro j hj
          rw [← Function.iterate_add_apply]
          exact hge_r (j + 2) (by omega)
        simp only [Nat.add_sub_cancel]
        rw [hiter_split]
        rw [hiter_split_r] at hIHn
        have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        have hr_nonneg : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
        have hCr : C * (n : ℝ) ≤ ((r : ℝ) + 1) * C * (n : ℝ) := by
          have : 0 ≤ (r : ℝ) * C * (n : ℝ) := by positivity
          linarith
        linarith

end OMA.Proof_Erdos562_R1_H1

theorem OMA.solution : OMA.R_Erdos562_erdos_562_R1.H1 := by
  intro r hr
  obtain ⟨C, hC, hbound⟩ := OMA.Proof_Erdos562_R1_H1.log_iter_bound r (by omega)
  have hR_tendsto : Filter.Tendsto (fun n : ℕ => (Combinatorics.hypergraphRamsey r n : ℝ)) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_mono (f := fun n : ℕ => (n : ℝ))
    · intro n
      exact_mod_cast OMA.Proof_Erdos562_R1_H1.le_hypergraphRamsey_of_pos r n (by omega)
    · exact tendsto_natCast_atTop_atTop
  have hpos_all : ∀ᶠ n : ℕ in Filter.atTop,
      ∀ j < r, 1 ≤ Real.log^[j] (Combinatorics.hypergraphRamsey r n : ℝ) := by
    have h := (Finset.eventually_all (I := Finset.range r)).mpr
      (fun j _ => ((OMA.Proof_Erdos562_R1_H1.tendsto_log_iter j).comp hR_tendsto).eventually_ge_atTop 1)
    filter_upwards [h] with n hn j hj using hn j (Finset.mem_range.mpr hj)
  rw [Asymptotics.isBigO_iff]
  refine ⟨C, ?_⟩
  filter_upwards [hbound, hpos_all] with n hbn hposn
  have hnonneg : 0 ≤ Real.log^[r - 1] (Combinatorics.hypergraphRamsey r n : ℝ) :=
    le_trans zero_le_one (hposn (r - 1) (by omega))
  have hle : Real.log^[r - 1] (Combinatorics.hypergraphRamsey r n : ℝ) ≤
      Real.log^[r - 1] ((Combinatorics.hypergraphRamsey r n : ℝ) + 1) :=
    OMA.Proof_Erdos562_R1_H1.log_iter_mono (r - 1)
      (fun j hj => lt_of_lt_of_le zero_lt_one (hposn j (by omega))) (by linarith)
  rw [Real.norm_of_nonneg hnonneg, Real.norm_of_nonneg (Nat.cast_nonneg n)]
  exact hle.trans hbn
