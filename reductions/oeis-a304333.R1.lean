import OMAStatements.S_oeis_a304333

-- Credit: @Pixelstorm44
namespace OMA.R_oeis_a304333_R1

open OMA.S_oeis_a304333

/-- The Lucas pair returns to (2,1) after 24 steps modulo 36. -/
private theorem period36 (k : ℕ) : Nat.ModEq 36 (lucas (k+24)) (lucas k) := by
  induction k using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more k h₀ h₁ =>
    change Nat.ModEq 36 (lucas ((k+1)+24) + lucas (k+24)) (lucas (k+1) + lucas k)
    exact h₁.add h₀

private theorem wheel (k : ℕ) : Nat.ModEq 36 (lucas (k%24)) (lucas k) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases h : k < 24
    · rw [Nat.mod_eq_of_lt h]
    · have e : k = (k-24) + 24 := by omega
      have er : k % 24 = (k-24) % 24 := by omega
      rw [er]
      exact (ih (k-24) (by omega)).trans (by simpa only [← e] using (period36 (k-24)).symm)

/-- Across each complete period at least ten indices avoid both small squares.
The lower bound is attained, for example, by the residue 11 modulo 36. -/
theorem wheel_count : ∀ r : Fin 36, 10 ≤ ((Finset.range 24).filter
    (fun j => lucas j % 4 ≠ r.val % 4 ∧ lucas j % 9 ≠ r.val % 9)).card := by
  decide

private theorem index_le (k : ℕ) : k ≤ lucas k := by
  induction k using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more k h₀ h₁ =>
    change k+2 ≤ lucas (k+1) + lucas k
    cases k with
    | zero => decide
    | succ k => omega

private theorem increasing (k : ℕ) (hk : 1 ≤ k) : lucas k < lucas (k+1) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  change lucas (j+1) < lucas (j+1) + lucas j
  cases j with
  | zero => decide
  | succ j => have := index_le (j+1); omega

private theorem mono_pos {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) : lucas i ≤ lucas j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih => exact ih.trans (increasing j (by omega)).le

/-- Among the first nine offsets there is always one missed by all four
small prime squares. For each of 25 and 49 it suffices to test residues
actually taken by the offsets. -/
private theorem first_nine (z : ℕ) : ∃ k ∈ Finset.Icc 1 9,
    ¬ Nat.ModEq 4 (lucas (k % 24)) z ∧ ¬ Nat.ModEq 9 (lucas (k % 24)) z ∧
    ¬ Nat.ModEq 25 (lucas k) z ∧ ¬ Nat.ModEq 49 (lucas k) z := by
  let x := fun (i : Fin 9) => lucas (i.val+1)
  have repr (q : ℕ) : ∃ j : Fin 9, ∀ i, Nat.ModEq q (x i) z → Nat.ModEq q (x i) (x j) := by
    by_cases h : ∃ j, Nat.ModEq q (x j) z
    · obtain ⟨j,hj⟩ := h
      exact ⟨j, fun _ hi => hi.trans hj.symm⟩
    · exact ⟨0, fun i hi => (h ⟨i,hi⟩).elim⟩
  obtain ⟨b,hb⟩ := repr 25
  obtain ⟨c,hc⟩ := repr 49
  have table : ∀ (r : Fin 36) (b c : Fin 9), ∃ i : Fin 9,
      ¬ Nat.ModEq 4 (x i) r.val ∧ ¬ Nat.ModEq 9 (x i) r.val ∧
      ¬ Nat.ModEq 25 (x i) (x b) ∧ ¬ Nat.ModEq 49 (x i) (x c) := by decide
  obtain ⟨i,hi₄,hi₉,hi₂₅,hi₄₉⟩ := table ⟨z%36, Nat.mod_lt _ (by decide)⟩ b c
  refine ⟨i.val+1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_, ?_,
    fun h => hi₂₅ (hb i h), fun h => hi₄₉ (hc i h)⟩
  · rw [Nat.mod_eq_of_lt (by omega : i.val+1 < 24)]
    exact fun h => hi₄ (h.trans ((Nat.mod_modEq z 36).of_dvd (by decide : 4 ∣ 36)).symm)
  · rw [Nat.mod_eq_of_lt (by omega : i.val+1 < 24)]
    exact fun h => hi₉ (h.trans ((Nat.mod_modEq z 36).of_dvd (by decide : 9 ∣ 36)).symm)

private theorem small_values (n : ℕ) (hn : 1 < n) (h : n ≤ 76) : 0 < a n := by
  have table : ∀ t : Fin 77, 1 < t.val → ∃ i : Fin 9, i.val+1 ≤ t.val ∧
      lucas (i.val+1) < t.val ∧
      ∀ q : Fin 9, 2 ≤ q.val → ¬ q.val*q.val ∣ t.val - lucas (i.val+1) := by decide
  obtain ⟨i,hk,hl,hs⟩ := table ⟨n,by omega⟩ hn
  exact Finset.card_pos.mpr ⟨i.val+1, Finset.mem_filter.mpr
    ⟨Finset.mem_Icc.mpr ⟨by omega,hk⟩,hl,Nat.squarefree_iff_prime_squarefree.mpr
      (fun p hp hd => by
        have hle := Nat.le_of_dvd (Nat.sub_pos_of_lt hl) hd
        have hh : p*p ≤ 76 := hle.trans ((Nat.sub_le _ _).trans h)
        have hlim : p < 9 := by
          by_contra! hb
          have := Nat.mul_le_mul hb hb
          omega
        exact hs ⟨p,hlim⟩ hp.two_le hd)⟩⟩

/-- Any covering residue that lands inside the gap produces a counterexample.
Here z is any representative and n is the integer in the gap. -/
private theorem covered_gap {m n z d : ℕ} (hm : 1 ≤ m) (_hl : lucas m < n)
    (hr : n ≤ lucas (m+1)) (hd : 44100 ∣ d) (he : Nat.ModEq d n z)
    (hc : ∀ k ∈ Finset.Icc 1 m,
      ¬ Nat.ModEq 4 (lucas (k % 24)) z → ¬ Nat.ModEq 9 (lucas (k % 24)) z →
      ¬ Nat.ModEq 25 (lucas k) z → ¬ Nat.ModEq 49 (lucas k) z →
      ∃ p : ℕ, p.Prime ∧ 11 ≤ p ∧ p*p ∣ d ∧ Nat.ModEq (p*p) (lucas k) z) :
    a n = 0 := by
  by_contra! h
  obtain ⟨k,hk⟩ := Finset.card_pos.mp (show 0 < a n by omega)
  obtain ⟨hki,hkn,hs⟩ := Finset.mem_filter.mp hk
  obtain ⟨hk₁,_⟩ := Finset.mem_Icc.mp hki
  have hkm : k ≤ m := by
    by_contra! hb
    have hh := mono_pos (by omega : 1 ≤ m+1) hb
    omega
  have miss (p : ℕ) (hp : p.Prime) (hdp : p*p ∣ d) :
      ¬ Nat.ModEq (p*p) (lucas k) z := by
    intro hh
    exact Nat.squarefree_iff_prime_squarefree.mp hs p hp
      ((Nat.modEq_iff_dvd' hkn.le).mp (hh.trans (he.of_dvd hdp).symm))
  obtain ⟨p,hp,_,hpd,hz⟩ := hc k (Finset.mem_Icc.mpr ⟨hk₁,hkm⟩)
    (fun h => miss 2 (by decide) (dvd_trans (by decide : 4 ∣ 44100) hd)
      (((wheel k).of_dvd (by decide : 4 ∣ 36)).symm.trans h))
    (fun h => miss 3 (by decide) (dvd_trans (by decide : 9 ∣ 44100) hd)
      (((wheel k).of_dvd (by decide : 9 ∣ 36)).symm.trans h))
    (miss 5 (by decide) (dvd_trans (by decide : 25 ∣ 44100) hd))
    (miss 7 (by decide) (dvd_trans (by decide : 49 ∣ 44100) hd))
  exact miss p hp hpd hz

/-- A simultaneous residue class covering the first m offsets must have period
larger than the gap (L_m,L_{m+1}]. The modulus includes the fixed wheel 44100 = 4·9·25·49.
Only the indices surviving that wheel need larger prime squares. -/
def H1 : Prop := ∀ m z d : ℕ, 9 ≤ m → 5336100 ≤ d → 44100 ∣ d →
    (∀ k ∈ Finset.Icc 1 m,
      ¬ Nat.ModEq 4 (lucas (k % 24)) z →
      ¬ Nat.ModEq 9 (lucas (k % 24)) z →
      ¬ Nat.ModEq 25 (lucas k) z → ¬ Nat.ModEq 49 (lucas k) z →
      ∃ p : ℕ, p.Prime ∧ 11 ≤ p ∧ p*p ∣ d ∧ Nat.ModEq (p*p) (lucas k) z) →
    lucas (m+1) - lucas m < d

/-- For a period larger than the gap there is at most one lift of the residue
inside it. In coordinates based at L_m+1, the assertion is that an irredundant
cover's first lift has displacement at least the gap length. -/
def H2 : Prop := ∀ m M r : ℕ, 9 ≤ m → 5336100 ≤ M → 44100 ∣ M → r < M →
    lucas (m+1) - lucas m < M →
    let z := lucas m + 1 + r
    let covers := fun (d : ℕ) => ∀ k ∈ Finset.Icc 1 m,
      ¬ Nat.ModEq 4 (lucas (k % 24)) z →
      ¬ Nat.ModEq 9 (lucas (k % 24)) z →
      ¬ Nat.ModEq 25 (lucas k) z → ¬ Nat.ModEq 49 (lucas k) z →
      ∃ p : ℕ, p.Prime ∧ 11 ≤ p ∧ p*p ∣ d ∧ Nat.ModEq (p*p) (lucas k) z
    covers M → (∀ d, d ∣ M → 44100 ∣ d → 0 < d → covers d → M ≤ d) →
    lucas (m+1) - lucas m ≤ r

/-- Both remaining assertions are necessary as well as jointly sufficient. -/
theorem necessary (sol : ∀ n : ℕ, 1 < n → 0 < a n) : H1 ∧ H2 := by
  constructor
  · intro m z d hm hsize hd hc
    by_contra! h
    let b := lucas m + 1
    let t := z + b*d - b
    have hbd : b ≤ b*d := by simpa using Nat.mul_le_mul_left b (by omega : 1 ≤ d)
    have et : b + t = z + b*d := by dsimp [t]; omega
    have he : Nat.ModEq d (b + t%d) z := calc
      b + t%d ≡ b + t [MOD d] := (Nat.mod_modEq _ _).add_left b
      _ = z + b*d := et
      _ ≡ z [MOD d] := by simp [Nat.ModEq]
    have ht := Nat.mod_lt t (by omega : 0 < d)
    have hbase := index_le m
    have hinc := increasing m (by omega)
    have hzero := covered_gap (n := b + t%d) (by omega : 1 ≤ m)
      (by dsimp [b]; omega) (by dsimp [b]; omega) hd he hc
    have := sol (b + t%d) (by dsimp [b]; omega)
    omega
  · intro m d r hm hsize hd hr hg
    dsimp only
    intro hc _
    by_contra! hin
    have hbase := index_le m
    have hzero := covered_gap (n := lucas m + 1 + r) (by omega : 1 ≤ m)
      (by omega) (by omega) hd (Nat.ModEq.refl _) hc
    have := sol (lucas m + 1 + r) (by omega)
    omega

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a304333.main := by
  classical
  intro h₁ h₂ n hn
  by_cases hsmall : n ≤ 76
  · exact small_values n hn hsmall
  by_contra hnone
  let indices := (Finset.Icc 1 n).filter (fun k => lucas k < n)
  have hne : indices.Nonempty := ⟨1, Finset.mem_filter.mpr
    ⟨Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩, hn⟩⟩
  let m := indices.max' hne
  obtain ⟨hmem, hleft⟩ := Finset.mem_filter.mp (indices.max'_mem hne)
  obtain ⟨hm, hmn⟩ := Finset.mem_Icc.mp hmem
  change 1 ≤ m at hm
  change m ≤ n at hmn
  change lucas m < n at hleft
  have hright : n ≤ lucas (m+1) := by
    by_contra! h
    have hi := index_le (m+1)
    have hk : m+1 ∈ indices := Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, h⟩
    have := Finset.le_max' indices (m+1) hk
    change m+1 ≤ m at this
    omega
  have h9 : 9 ≤ m := by
    apply Finset.le_max' indices 9
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by decide,by omega⟩,
      (by change 76 < n; omega)⟩
  let covers := fun (d : ℕ) => ∀ k ∈ Finset.Icc 1 m,
      ¬ Nat.ModEq 4 (lucas (k % 24)) n →
      ¬ Nat.ModEq 9 (lucas (k % 24)) n →
      ¬ Nat.ModEq 25 (lucas k) n → ¬ Nat.ModEq 49 (lucas k) n →
      ∃ p : ℕ, p.Prime ∧ 11 ≤ p ∧ p*p ∣ d ∧ Nat.ModEq (p*p) (lucas k) n
  have hex : ∃ d, 0 < d ∧ 44100 ∣ d ∧ covers d := by
    refine ⟨44100 * n.factorial, Nat.mul_pos (by decide) (Nat.factorial_pos _),
      dvd_mul_right _ _, ?_⟩
    intro k hk h₄ h₉ h₂₅ h₄₉
    obtain ⟨hk₁,hkm⟩ := Finset.mem_Icc.mp hk
    have hkn := (mono_pos hk₁ hkm).trans_lt hleft
    have hbad : ¬ Squarefree (n - lucas k) := by
      intro hs
      apply hnone
      exact Finset.card_pos.mpr ⟨k, Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨hk₁, hkm.trans hmn⟩, hkn, hs⟩⟩
    rw [Nat.squarefree_iff_prime_squarefree] at hbad
    push Not at hbad
    obtain ⟨p,hp,hd⟩ := hbad
    have he := Nat.modEq_of_dvd' hkn.le hd
    have hp₁₁ : 11 ≤ p := by
      by_contra! h
      interval_cases p
      · exact (by decide : ¬ Nat.Prime 0) hp
      · exact (by decide : ¬ Nat.Prime 1) hp
      · exact h₄ (((wheel k).of_dvd (by decide : 4 ∣ 36)).trans he)
      · exact h₉ (((wheel k).of_dvd (by decide : 9 ∣ 36)).trans he)
      · exact (by decide : ¬ Nat.Prime 4) hp
      · exact h₂₅ he
      · exact (by decide : ¬ Nat.Prime 6) hp
      · exact h₄₉ he
      · exact (by decide : ¬ Nat.Prime 8) hp
      · exact (by decide : ¬ Nat.Prime 9) hp
      · exact (by decide : ¬ Nat.Prime 10) hp
    have hpp := Nat.le_of_dvd (Nat.sub_pos_of_lt hkn) hd
    exact ⟨p,hp,hp₁₁, dvd_trans (Nat.dvd_factorial (by positivity) (by omega))
      (dvd_mul_left _ _),he⟩
  let M := Nat.find hex
  obtain ⟨hM, hwheel, hcover⟩ := Nat.find_spec hex
  obtain ⟨k,hk,h₄,h₉,h₂₅,h₄₉⟩ := first_nine n
  obtain ⟨hk₁,hk₉⟩ := Finset.mem_Icc.mp hk
  obtain ⟨p,hp,hlarge,hpM,_⟩ := hcover k (Finset.mem_Icc.mpr ⟨hk₁,hk₉.trans h9⟩)
    h₄ h₉ h₂₅ h₄₉
  have hcop : Nat.Coprime p 44100 := by
    apply hp.coprime_iff_not_dvd.mpr
    intro hd
    have hnd (j : ℕ) (hj : 0 < j) (hj' : j < 11) : ¬ p ∣ j :=
      fun h => (by have := Nat.le_of_dvd hj h; omega)
    rw [show 44100 = 2*2*3*3*5*5*7*7 by decide] at hd
    simp only [hp.dvd_mul, hnd 2 (by decide) (by decide), hnd 3 (by decide) (by decide),
      hnd 5 (by decide) (by decide), hnd 7 (by decide) (by decide), or_self] at hd
  have hdvd := (hcop.mul_left hcop).symm.mul_dvd_of_dvd_of_dvd hwheel hpM
  have hle := Nat.le_of_dvd hM hdvd
  have hsize : 5336100 ≤ M := (Nat.mul_le_mul_left 44100 (Nat.mul_le_mul hlarge hlarge)).trans hle
  have hgap := h₁ m n M h9 hsize hwheel hcover
  let r := n - (lucas m + 1)
  have er : lucas m + 1 + r = n := by dsimp [r]; omega
  have hr : r < lucas (m+1) - lucas m := by dsimp [r]; omega
  have hbound := h₂ m M r h9 hsize hwheel (hr.trans hgap) hgap
  dsimp only at hbound
  rw [er] at hbound
  have hmin : ∀ d, d ∣ M → 44100 ∣ d → 0 < d → covers d → M ≤ d := by
    intro d _ hd hpos hc
    exact Nat.find_min' hex ⟨hpos,hd,hc⟩
  exact (Nat.not_le_of_lt hr) (hbound hcover hmin)

end OMA.R_oeis_a304333_R1
