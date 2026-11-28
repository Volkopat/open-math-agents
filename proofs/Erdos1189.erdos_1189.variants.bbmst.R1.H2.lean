import OMAReductions.R_Erdos1189_erdos_1189_variants_bbmst_R1
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Ring

/-!
Credit: @grp06
The finiteness result is recorded in Section 1 of P. Balister, B. Bollobás,
R. Morris, J. Sahasrabudhe and M. Tiba, *The structure and number of Erdős
covering systems*, https://arxiv.org/html/1904.04806#S1.Ex3.
-/

private abbrev ModulusLCM (S : Finset (ℕ × ℤ)) : ℕ :=
  S.lcm Prod.fst

private theorem lcm_pos {S : Finset (ℕ × ℤ)}
    (h : ∀ p ∈ S, 1 < p.1) : 0 < ModulusLCM S := by
  refine Nat.pos_of_ne_zero ?_
  intro hz
  obtain ⟨p, hp, hp0⟩ := Finset.lcm_eq_zero_iff.mp hz
  have hp1 := h p hp
  omega

private theorem shift_preserves_noncoverage {m L i : ℕ} {r a : ℤ}
    (hd : m ∣ L) (hr : ¬ r ≡ a [ZMOD (m : ℤ)]) :
    ¬ r + (i : ℤ) * (L : ℤ) ≡ a [ZMOD (m : ℤ)] := by
  have hdZ : (m : ℤ) ∣ (L : ℤ) := Int.natCast_dvd_natCast.mpr hd
  have hshift : r + (i : ℤ) * (L : ℤ) ≡ r [ZMOD (m : ℤ)] :=
    Int.add_modEq_left_iff.mpr (hdZ.trans (dvd_mul_left (L : ℤ) (i : ℤ)))
  exact fun h => hr (hshift.symm.trans h)

private theorem dvd_gap {m L i j : ℕ} {r a : ℤ} (hij : i ≤ j)
    (hi : r + (i : ℤ) * (L : ℤ) ≡ a [ZMOD (m : ℤ)])
    (hj : r + (j : ℤ) * (L : ℤ) ≡ a [ZMOD (m : ℤ)]) :
    m ∣ (j - i) * L := by
  apply Int.natCast_dvd_natCast.mp
  rw [Int.natCast_mul, Int.natCast_sub hij]
  have h := (hi.trans hj.symm).dvd
  rw [show (r + (j : ℤ) * (L : ℤ)) - (r + (i : ℤ) * (L : ℤ)) =
    ((j : ℤ) - (i : ℤ)) * (L : ℤ) by ring] at h
  exact h

private theorem extend_lcm {A S : Finset (ℕ × ℤ)} {k : ℕ}
    (hmods : ∀ p ∈ A, 1 < p.1)
    (cover : ∀ z : ℤ, ∃ p ∈ A, z ≡ p.2 [ZMOD (p.1 : ℤ)])
    (witness : ∀ p ∈ A, ∃ z : ℤ, z ≡ p.2 [ZMOD (p.1 : ℤ)] ∧
      ∀ q ∈ A, q ≠ p → ¬ z ≡ q.2 [ZMOD (q.1 : ℤ)])
    (hcard : A.card = k) (hS : S ⊆ A) (hproper : S.card < k) :
    ∃ b ∈ A, b ∉ S ∧ 0 < ModulusLCM (insert b S) ∧
      ModulusLCM (insert b S) ≤ k * ModulusLCM S := by
  classical
  have hne : S ≠ A := by
    intro he
    rw [he, hcard] at hproper
    exact (Nat.lt_irrefl k) hproper
  obtain ⟨a, haA, haS⟩ :=
    Finset.exists_of_ssubset (Finset.ssubset_iff_subset_ne.mpr ⟨hS, hne⟩)
  obtain ⟨r, _, hr⟩ := witness a haA
  let L := ModulusLCM S
  have hL : 0 < L := lcm_pos (fun p hp => hmods p (hS hp))
  let z (i : Fin (k + 1)) : ℤ := r + (i.val : ℤ) * (L : ℤ)
  let f (i : Fin (k + 1)) : {p // p ∈ A} :=
    ⟨Classical.choose (cover (z i)), (Classical.choose_spec (cover (z i))).1⟩
  have hf (i : Fin (k + 1)) : z i ≡ (f i).val.2 [ZMOD ((f i).val.1 : ℤ)] :=
    (Classical.choose_spec (cover (z i))).2
  have hfS (i : Fin (k + 1)) : (f i).val ∉ S := by
    intro hi
    have hqa : (f i).val ≠ a := fun eq => haS (eq ▸ hi)
    have hd : (f i).val.1 ∣ L := Finset.dvd_lcm (f := Prod.fst) hi
    exact shift_preserves_noncoverage (i := i.val) hd (hr _ (hS hi) hqa) (hf i)
  have hcollision : ¬ Function.Injective f := by
    intro hinj
    have hc := Fintype.card_le_of_injective f hinj
    rw [Fintype.card_fin, Fintype.card_coe A, hcard] at hc
    omega
  obtain ⟨i, j, heq, hij⟩ := Function.not_injective_iff.mp hcollision
  suffices hordered : ∀ u v : Fin (k + 1), u < v → f u = f v →
      ∃ b ∈ A, b ∉ S ∧ 0 < ModulusLCM (insert b S) ∧
        ModulusLCM (insert b S) ≤ k * ModulusLCM S by
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact hordered i j hlt heq
    · exact hordered j i hgt heq.symm
  intro u v huv hfuv
  change u.val < v.val at huv
  let b := (f u).val
  have hbA : b ∈ A := (f u).property
  have hbS : b ∉ S := hfS u
  have hu : z u ≡ b.2 [ZMOD (b.1 : ℤ)] := hf u
  have hv : z v ≡ b.2 [ZMOD (b.1 : ℤ)] := by
    simpa only [← hfuv] using hf v
  have hd : b.1 ∣ (v.val - u.val) * L := dvd_gap (r := r) huv.le hu hv
  have hinsert : insert b S ⊆ A := Finset.insert_subset hbA hS
  refine ⟨b, hbA, hbS, lcm_pos (fun p hp => hmods p (hinsert hp)), ?_⟩
  have hdiv : ModulusLCM (insert b S) ∣ (v.val - u.val) * L := by
    change (insert b S).lcm Prod.fst ∣ (v.val - u.val) * L
    rw [Finset.lcm_insert]
    exact lcm_dvd hd (dvd_mul_left L (v.val - u.val))
  have hgap : 0 < v.val - u.val := Nat.sub_pos_of_lt huv
  have hvle : v.val ≤ k := Nat.lt_succ_iff.mp v.isLt
  calc
    ModulusLCM (insert b S) ≤ (v.val - u.val) * L :=
      Nat.le_of_dvd (Nat.mul_pos hgap hL) hdiv
    _ ≤ k * L := Nat.mul_le_mul_right L ((Nat.sub_le _ _).trans hvle)

theorem OMA.solution : OMA.R_Erdos1189_erdos_1189_variants_bbmst_R1.H2 := by
  classical
  unfold OMA.R_Erdos1189_erdos_1189_variants_bbmst_R1.H2
  intro k
  let box : Finset (ℕ × ℤ) :=
    Finset.product (Finset.Icc (0 : ℕ) (k ^ k)) (Finset.Icc (0 : ℤ) ((k ^ k : ℕ) : ℤ))
  apply box.powerset.finite_toSet.subset
  intro A hA
  obtain ⟨⟨hnorm, hcover, hminimal⟩, hcard⟩ := hA
  have hmods : ∀ p ∈ A, 1 < p.1 := fun p hp => (hnorm p hp).1
  have hbuild : ∀ t ≤ k, ∃ S ⊆ A, S.card = t ∧
      0 < ModulusLCM S ∧ ModulusLCM S ≤ k ^ t := by
    intro t
    induction t with
    | zero =>
      intro _
      exact ⟨∅, Finset.empty_subset _, by simp, by simp [ModulusLCM],
        by simp [ModulusLCM]⟩
    | succ t ih =>
      intro htk
      have hlt : t < k := Nat.lt_of_succ_le htk
      obtain ⟨S, hS, hSt, _, hSL⟩ := ih hlt.le
      have hScard : S.card < k := by rwa [hSt]
      obtain ⟨b, hbA, hbS, hpos, hbound⟩ :=
        extend_lcm hmods hcover hminimal hcard hS hScard
      refine ⟨insert b S, Finset.insert_subset hbA hS, ?_, hpos, ?_⟩
      · rw [Finset.card_insert_of_notMem hbS, hSt]
      · calc
          ModulusLCM (insert b S) ≤ k * ModulusLCM S := hbound
          _ ≤ k * k ^ t := Nat.mul_le_mul_left k hSL
          _ = k ^ (t + 1) := by rw [pow_succ, Nat.mul_comm]
  obtain ⟨S, hS, hSk, hpos, hbound⟩ := hbuild k le_rfl
  have hSA : S = A := Finset.eq_of_subset_of_card_le hS ((hcard.trans hSk.symm).le)
  subst S
  change A ∈ box.powerset
  apply Finset.mem_powerset.mpr
  intro p hp
  dsimp only [box]
  apply Finset.mem_product.mpr
  have hd : p.1 ∣ ModulusLCM A := Finset.dvd_lcm (f := Prod.fst) hp
  have hm : p.1 ≤ k ^ k := (Nat.le_of_dvd hpos hd).trans hbound
  have hmZ : (p.1 : ℤ) ≤ ((k ^ k : ℕ) : ℤ) := by exact_mod_cast hm
  exact ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _, hm⟩,
    Finset.mem_Icc.mpr ⟨(hnorm p hp).2.1, (hnorm p hp).2.2.le.trans hmZ⟩⟩
