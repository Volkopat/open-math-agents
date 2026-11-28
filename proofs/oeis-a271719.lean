import OMAStatements.S_oeis_a271719

/-! Zhi-Wei Sun's two counting assertions for OEIS A271719.
For n at least 133, two primitive representations come from the two
orientations of a scaled 3–4–5 right triangle. A finite enumeration
certifies the small exceptions. -/

namespace Sun271719

/-- On the first period, select a coprime pair whose deviation from slope six divides twelve. -/
private lemma seeds : ∀ r : Fin 72, ∃ v : Fin 40,
    let b := 133 + r.val
    b.Coprime v.val ∧ Nat.dist b (6*v.val) ∣ 12 ∧ b < 7*v.val ∧ 11*v.val < 2*b := by
  decide +kernel

private lemma lift_coprime (b v t : ℕ) (h : b.Coprime v) (hd : Nat.dist b (6*v) ∣ 12) :
    (72*t+b).Coprime (12*t+v) := by
  let g := (72*t+b).gcd (12*t+v)
  have hx : g ∣ 72*t+b := Nat.gcd_dvd_left _ _
  have hy : g ∣ 12*t+v := Nat.gcd_dvd_right _ _
  have h6 : g ∣ 72*t+6*v := by
    rw [show 72*t+6*v = 6*(12*t+v) by ring]
    exact dvd_mul_of_dvd_right hy 6
  have hdist : g ∣ Nat.dist b (6*v) := by
    rw [← Nat.dist_add_add_left (72*t) b (6*v)]
    rcases le_total (72*t+b) (72*t+6*v) with hlo | hhi
    · rw [Nat.dist_eq_sub_of_le hlo]
      exact Nat.dvd_sub h6 hx
    · rw [Nat.dist_eq_sub_of_le_right hhi]
      exact Nat.dvd_sub hx h6
  have h12 := hdist.trans hd
  have h72 : g ∣ 72 := h12.trans (by decide : 12 ∣ 72)
  have hb := (Nat.dvd_add_iff_right (Nat.dvd_mul_right_of_dvd h72 t)).mpr hx
  have hv := (Nat.dvd_add_iff_right (Nat.dvd_mul_right_of_dvd h12 t)).mpr hy
  exact Nat.dvd_one.mp (h.gcd_eq_one ▸ Nat.dvd_gcd hb hv)

theorem nearby (n : ℕ) (hn : 133 ≤ n) :
    ∃ u : ℕ, n.Coprime u ∧ n < 7*u ∧ 11*u < 2*n := by
  let t := (n-133)/72
  let r : Fin 72 := ⟨(n-133)%72, Nat.mod_lt _ (by decide)⟩
  obtain ⟨v,hc,hd,hl,hu⟩ := seeds r
  have he : n = 72*t+(133+r.val) := by dsimp [r,t]; omega
  refine ⟨12*t+v.val, ?_, ?_, ?_⟩
  · rw [he]
    exact lift_coprime _ _ t hc hd
  · omega
  · omega

end Sun271719

namespace Sun271719

def Good (n : ℕ) (t : ℕ × ℕ × ℕ) : Prop :=
  t.1 + t.2.1 + t.2.2 = n ∧ 0 < t.2.1 ∧ t.2.1 ≤ t.1 ∧ 0 < t.2.2 ∧
    Nat.gcd (Nat.gcd t.1 t.2.1) t.2.2 = 1 ∧
    IsSquare (t.1 ^ 2 + (2 * t.2.1 + t.2.2) ^ 2)

theorem large_witnesses {n u : ℕ} (hn : 133 ≤ n) (hcop : n.Coprime u)
    (lo : n < 7*u) (hi : 11*u < 2*n) :
    ∃ t₁ t₂, Good n t₁ ∧ Good n t₂ ∧ t₁ ≠ t₂ := by
  have primitive (x y z : ℕ) (hsum : x+y+z=n)
      (hdiff : 2*y+z-x=u ∨ x-(2*y+z)=u) : Nat.gcd (Nat.gcd x y) z = 1 := by
    let d := Nat.gcd (Nat.gcd x y) z
    have hxy : d ∣ Nat.gcd x y := Nat.gcd_dvd_left _ _
    have hx := hxy.trans (Nat.gcd_dvd_left x y)
    have hy := hxy.trans (Nat.gcd_dvd_right x y)
    have hz : d ∣ z := Nat.gcd_dvd_right _ _
    have hv : d ∣ 2*y+z := dvd_add (dvd_mul_of_dvd_right hy _) hz
    have hd : d ∣ u := by
      rcases hdiff with h | h
      · rw [← h]; exact Nat.dvd_sub hv hx
      · rw [← h]; exact Nat.dvd_sub hx hv
    have hd' : d ∣ n := hsum ▸ dvd_add (dvd_add hx hy) hz
    exact Nat.dvd_one.mp (hcop.gcd_eq_one ▸ Nat.dvd_gcd hd' hd)
  refine ⟨(3*u,7*u-n,2*n-10*u), (4*u,7*u-n,2*n-11*u), ?_, ?_, ?_⟩
  · refine ⟨by dsimp; omega, by dsimp; omega, by dsimp; omega, by dsimp; omega,
      primitive _ _ _ (by dsimp; omega) (Or.inl (by dsimp; omega)), ?_⟩
    refine ⟨5*u, ?_⟩
    dsimp
    rw [show 2*(7*u-n)+(2*n-10*u)=4*u by omega]
    ring
  · refine ⟨by dsimp; omega, by dsimp; omega, by dsimp; omega, by dsimp; omega,
      primitive _ _ _ (by dsimp; omega) (Or.inr (by dsimp; omega)), ?_⟩
    refine ⟨5*u, ?_⟩
    dsimp
    rw [show 2*(7*u-n)+(2*n-11*u)=3*u by omega]
    ring
  · intro h
    have e : 3*u = 4*u := congrArg Prod.fst h
    omega

end Sun271719

namespace Sun271719

def smallOK (n : ℕ) (p : ℕ × ℕ) : Bool :=
  let x := p.1
  let y := p.2
  let z := n-x-y
  let v := x^2 + (2*y+z)^2
  decide (0 < y ∧ y ≤ x ∧ 0 < z ∧ Nat.gcd (Nat.gcd x y) z = 1 ∧ v.sqrt^2 = v)

def countSmall (n : ℕ) : ℕ :=
  (((Finset.range n) ×ˢ (Finset.range n)).filter (fun p => smallOK n p)).card

private abbrev singled : Finset ℕ := {11,12,14,18,24,54}

/-- Two explicit distinct pairs suffice at the nonsingleton indices. -/
private def witnesses : List ((ℕ × ℕ) × (ℕ × ℕ)) := [
  ((0,0),(0,0)), ((0,0),(0,0)), ((0,0),(0,0)), ((0,0),(0,0)),
  ((0,0),(0,0)), ((0,0),(0,0)), ((0,0),(0,0)), ((0,0),(0,0)),
  ((0,0),(0,0)), ((0,0),(0,0)), ((0,0),(0,0)), ((0,0),(0,0)),
  ((0,0),(0,0)), ((5,4),(6,1)), ((0,0),(0,0)), ((5,2),(12,2)),
  ((5,1),(8,7)), ((8,6),(9,4)), ((0,0),(0,0)), ((8,4),(9,2)),
  ((8,3),(9,1)), ((8,2),(12,7)), ((8,1),(15,1)), ((12,5),(16,5)),
  ((0,0),(0,0)), ((7,6),(10,9)), ((7,5),(15,9)), ((7,4),(10,7)),
  ((7,3),(15,7)), ((7,2),(10,5)), ((7,1),(24,1)), ((10,3),(15,4)),
  ((15,3),(20,3)), ((10,1),(15,2)), ((15,1),(20,1)), ((12,12),(16,11)),
  ((12,11),(20,5)), ((12,10),(15,14)), ((12,9),(15,13)), ((12,8),(16,7)),
  ((9,9),(12,7)), ((9,8),(12,6)), ((9,7),(12,5)), ((9,6),(12,4)),
  ((9,5),(12,3)), ((9,4),(12,2)), ((9,3),(12,1)), ((9,2),(15,4)),
  ((9,1),(21,1)), ((14,13),(15,2)), ((15,1),(24,19)), ((14,11),(20,17)),
  ((24,17),(27,11)), ((14,9),(20,15)), ((0,0),(0,0)), ((14,7),(20,13)),
  ((24,13),(27,7)), ((14,5),(20,11)), ((24,11),(27,5)), ((14,3),(20,9)),
  ((11,11),(28,13)), ((11,10),(14,1)), ((11,9),(24,7)), ((11,8),(16,16)),
  ((11,7),(16,15)), ((11,6),(16,14)), ((11,5),(16,13)), ((11,4),(16,12)),
  ((11,3),(16,11)), ((11,2),(16,10)), ((11,1),(16,9)), ((16,8),(24,23)),
  ((16,7),(25,13)), ((16,6),(21,20)), ((16,5),(21,19)), ((16,4),(24,19)),
  ((16,3),(21,17)), ((16,2),(21,16)), ((16,1),(25,7)), ((21,14),(24,15)),
  ((21,13),(33,9)), ((18,17),(24,13)), ((21,11),(25,3)), ((18,15),(21,10)),
  ((13,13),(25,1)), ((13,12),(18,13)), ((13,11),(21,7)), ((13,10),(18,11)),
  ((13,9),(21,5)), ((13,8),(18,9)), ((13,7),(35,29)), ((13,6),(18,7)),
  ((13,5),(21,1)), ((13,4),(18,5)), ((13,3),(35,25)), ((13,2),(18,3)),
  ((13,1),(35,23)), ((18,1),(28,27)), ((36,15),(39,21)), ((20,20),(28,25)),
  ((20,19),(35,19)), ((20,18),(28,23)), ((20,17),(35,17)), ((20,16),(28,21)),
  ((20,15),(35,15)), ((20,14),(28,19)), ((20,13),(35,13)), ((20,12),(28,17)),
  ((20,11),(35,11)), ((20,10),(28,15)), ((20,9),(35,9)), ((20,8),(28,13)),
  ((15,15),(20,7)), ((15,14),(20,6)), ((15,13),(20,5)), ((15,12),(20,4)),
  ((15,11),(20,3)), ((15,10),(20,2)), ((15,9),(20,1)), ((15,8),(28,5)),
  ((15,7),(44,41)), ((15,6),(22,21)), ((15,5),(27,25)), ((15,4),(22,19)),
  ((15,3),(27,23)), ((15,2),(22,17)), ((15,1),(35,29)), ((22,15),(27,20)),
  ((27,19),(35,27)), ((22,13),(32,29)), ((27,17),(36,11)), ((22,11),(27,16)),
  ((35,23),(44,29))]

private def pairValid (n : ℕ) (p : ℕ × ℕ) : Bool :=
  decide (p.1 < n ∧ p.2 < n) && smallOK n p

private theorem twoWitnesses : ∀ i : Fin 133, 10 < i.val → i.val ∉ singled →
    let w := witnesses.getD i.val ((0,0),(0,0))
    pairValid i.val w.1 = true ∧ pairValid i.val w.2 = true ∧ w.1 ≠ w.2 := by
  decide +kernel

private lemma countSmall_two {n : ℕ} {p q : ℕ × ℕ}
    (hp : pairValid n p = true) (hq : pairValid n q = true) (hpq : p ≠ q) :
    2 ≤ countSmall n := by
  let T := ((Finset.range n) ×ˢ (Finset.range n)).filter fun x => smallOK n x
  have mem {x : ℕ × ℕ} (hx : pairValid n x = true) : x ∈ T := by
    simpa [pairValid, T, Finset.mem_product] using hx
  have hsub : {p,q} ⊆ T := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | h
    · exact mem hp
    · exact (Finset.mem_singleton.mp h) ▸ mem hq
  simpa [T, countSmall, Finset.card_pair hpq] using Finset.card_le_card hsub

set_option maxRecDepth 16384 in
private theorem edge_counts :
    (∀ i : Fin 11, countSmall i ≠ 1) ∧
    (countSmall 11 = 1 ∧ countSmall 12 = 1 ∧ countSmall 14 = 1 ∧
      countSmall 18 = 1 ∧ countSmall 24 = 1 ∧ countSmall 54 = 1) := by
  decide +kernel

theorem count_small_spec {n : ℕ} (hn : n < 133) :
    (10 < n → 0 < countSmall n) ∧
    (countSmall n = 1 ↔ n ∈ ({11,12,14,18,24,54} : Finset ℕ)) := by
  by_cases hsmall : n < 11
  · have h := edge_counts.1 ⟨n,hsmall⟩
    have hnot : n ∉ singled := by simp [singled]; omega
    exact ⟨by omega, iff_of_false h hnot⟩
  by_cases hsingle : n ∈ singled
  · have he : countSmall n = 1 := by
      have e := edge_counts.2
      simp only [singled, Finset.mem_insert, Finset.mem_singleton] at hsingle
      rcases hsingle with rfl | rfl | rfl | rfl | rfl | rfl
      · exact e.1
      · exact e.2.1
      · exact e.2.2.1
      · exact e.2.2.2.1
      · exact e.2.2.2.2.1
      · exact e.2.2.2.2.2
    exact ⟨by omega, iff_of_true he hsingle⟩
  obtain ⟨hp, hq, hpq⟩ := twoWitnesses ⟨n,hn⟩ (by simpa using (show 10<n by omega)) hsingle
  have h : 2 ≤ countSmall n := countSmall_two hp hq hpq
  exact ⟨by omega, iff_of_false (by omega) hsingle⟩

end Sun271719

namespace Sun271719

open OMA.S_oeis_a271719

private def attachThird (n : ℕ) : (ℕ × ℕ) ↪ (ℕ × ℕ × ℕ) where
  toFun := fun p => (p.1,p.2,n-p.1-p.2)
  inj' := fun _ _ h => congrArg (fun t : ℕ × ℕ × ℕ => (t.1,t.2.1)) h

private def validTriples (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((((Finset.range n) ×ˢ (Finset.range n)).filter (fun p => smallOK n p)).map (attachThird n))

private theorem square_test (v : ℕ) : IsSquare v ↔ v.sqrt^2 = v := by
  rw [← Nat.exists_mul_self']
  constructor
  · rintro ⟨k,hk⟩
    exact ⟨k,by simpa [pow_two] using hk.symm⟩
  · rintro ⟨k,hk⟩
    exact ⟨k,by simpa [pow_two] using hk.symm⟩

private theorem mem_valid {n : ℕ} {t : ℕ × ℕ × ℕ} :
    t ∈ validTriples n ↔ Good n t := by
  rcases t with ⟨x,y,z⟩
  simp only [validTriples,Finset.mem_map,Finset.mem_filter,Finset.mem_product,Finset.mem_range]
  constructor
  · rintro ⟨⟨a,b⟩,⟨_,hok⟩,he⟩
    change (a,b,n-a-b) = (x,y,z) at he
    cases he
    obtain ⟨h₁,h₂,h₃,h₄,h₅⟩ := of_decide_eq_true hok
    change 0 < n-x-y at h₃
    exact ⟨by change x+y+(n-x-y)=n; omega,h₁,h₂,h₃,h₄,(square_test _).2 h₅⟩
  · rintro ⟨hsum,h₁,h₂,h₃,h₄,h₅⟩
    change x+y+z=n at hsum
    change 0<y at h₁
    change 0<z at h₃
    have hz : n-x-y=z := by omega
    refine ⟨(x,y),⟨⟨by omega,by omega⟩,?_⟩,?_⟩
    · apply decide_eq_true
      simpa only [hz] using And.intro h₁ ⟨h₂,h₃,h₄,(square_test _).1 h₅⟩
    · change (x,y,n-x-y) = (x,y,z)
      rw [hz]

private theorem a_card (n : ℕ) : a n = (validTriples n).card := by
  change {t | Good n t}.ncard = _
  rw [← Set.ncard_coe_finset]
  congr 1
  ext t
  exact mem_valid.symm

theorem a_count (n : ℕ) : a n = countSmall n := by
  rw [a_card,validTriples,Finset.card_map,countSmall]

theorem a_two {n : ℕ} (h : ∃ t₁ t₂, Good n t₁ ∧ Good n t₂ ∧ t₁ ≠ t₂) : 1 < a n := by
  rw [a_card,Finset.one_lt_card_iff]
  obtain ⟨x,y,hx,hy,ne⟩ := h
  exact ⟨x,y,mem_valid.mpr hx,mem_valid.mpr hy,ne⟩

end Sun271719

open Sun271719 OMA.S_oeis_a271719

theorem OMA.solution : type_of% @OMA.S_oeis_a271719.main := by
  have large {n : ℕ} (hn : 133 ≤ n) : 1 < a n := by
    obtain ⟨u,hcop,lo,hi⟩ := nearby n hn
    exact a_two (large_witnesses hn hcop lo hi)
  constructor
  · intro n hn
    by_cases small : n < 133
    · rw [a_count]
      exact (count_small_spec small).1 hn
    · exact Nat.zero_lt_of_lt (large (by omega))
  · intro n
    by_cases small : n < 133
    · rw [a_count]
      exact (count_small_spec small).2
    · have hl := large (n:=n) (by omega)
      have outside : n ∉ ({11,12,14,18,24,54} : Finset ℕ) := by
        simp only [Finset.mem_insert,Finset.mem_singleton]
        omega
      exact ⟨fun h => by omega,fun h => (outside h).elim⟩
