import FormalConjectures.ErdosProblems.«272»
/-! Erdos Problem 272 (Szabo strong variant): maxArithInterCard N = N^2 / 2 + O(N). -/
namespace OMA.E272
open Finset Filter ArithmeticFunction
def distNat (x y : ℕ) : ℕ := max x y - min x y
lemma distNat_comm (x y : ℕ) : distNat x y = distNat y x := by simp [distNat, max_comm, min_comm]
lemma distNat_self (x : ℕ) : distNat x x = 0 := by simp [distNat]
lemma distNat_pos_of_ne {x y : ℕ} (h : x ≠ y) : 0 < distNat x y := by unfold distNat; omega
lemma distNat_eq_sub {x y : ℕ} (h : x <= y) : distNat x y = y - x := by unfold distNat; omega
lemma distNat_eq_sub' {x y : ℕ} (h : y <= x) : distNat x y = x - y := by unfold distNat; omega
def APSet (X : Finset ℕ) : Prop := ∃ a d : ℕ, ∃ I : ℕ -> Prop, (∀ n m, I n -> m <= n -> I m) /\ I 0 /\ ∀ x, x ∈ X ↔ ∃ n, I n /\ x = a + n * d
lemma apSet_of_isAP (X : Finset ℕ) (l : ℕ∞) (hl : 0 < l) (h : (SetLike.coe X).IsAPOfLength l) : APSet X := by
 obtain ⟨a, d, -, hX⟩ := h
 refine ⟨a, d, fun n => (n : ℕ∞) < l, ?_, ?_, ?_⟩
 . intro n m hn hmn
   exact lt_of_le_of_lt (by exact_mod_cast hmn) hn
 . exact_mod_cast hl
 . intro x
   have hx : x ∈ X ↔ x ∈ (SetLike.coe X : Set ℕ) := Iff.rfl;rw [hx, hX]
   constructor
   . rintro ⟨n, hn, rfl⟩; exact ⟨n, hn, by rw [smul_eq_mul]⟩
   . rintro ⟨n, hn, rfl⟩; exact ⟨n, hn, by rw [smul_eq_mul]⟩
lemma isAP_of_card_le_two (X : Finset ℕ) (hne : X.Nonempty) (hc : X.card <= 2) : ∃ l : ℕ∞, 0 < l /\ (SetLike.coe X).IsAPOfLength l := by
 rcases Nat.le_iff_lt_or_eq.mp hc with h1 | h2
 . have hcard1 : X.card = 1 := by
     have := card_pos.mpr hne; omega
   obtain ⟨a, rfl⟩ := card_eq_one.mp hcard1
   refine ⟨1, by norm_num, a, 0, by simp, ?_⟩
   ext x
   simp only [Finset.coe_singleton, Set.mem_singleton_iff, Set.mem_ofPred_eq, Nat.cast_lt_one, smul_eq_mul]
   constructor
   . rintro rfl; exact ⟨0, rfl, by simp⟩
   . rintro ⟨n, rfl, rfl⟩; simp
 . obtain ⟨a, b, hab, rfl⟩ := card_eq_two.mp h2
   have htwo : ∀ u v : ℕ, u < v -> ∃ l : ℕ∞, 0 < l /\ (SetLike.coe ({u, v} : Finset ℕ)).IsAPOfLength l := by
     intro u v huv
     refine ⟨2, by norm_num, u, v - u, by simp [card_pair (ne_of_lt huv)], ?_⟩
     ext x
     simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_ofPred_eq, smul_eq_mul]
     constructor
     . rintro (rfl | rfl)
       . exact ⟨0, by norm_num, by simp⟩
       . exact ⟨1, by norm_num, by omega⟩
     . rintro ⟨n, hn, rfl⟩
       have hn2 : n < 2 := by exact_mod_cast hn
       interval_cases n
       . left; simp
       . right; omega
   rcases lt_or_gt_of_ne hab with hlt | hgt
   . exact htwo a b hlt
   . have heq : ({a, b} : Finset ℕ) = {b, a} := by ext x; simp [or_comm]
     rw [heq]; exact htwo b a hgt
lemma ap_gap (a d : ℕ) (I : ℕ -> Prop) (hI : ∀ n m, I n -> m <= n -> I m) (z u : ℕ) (hz : ∃ n, I n /\ z = a + n * d) (hu : ∃ n, I n /\ u = a + n * d) (hzu : z ≠ u) (hadj : ∀ n, I n -> ¬ (min z u < a + n * d /\ a + n * d < max z u)) : 0 < d /\ distNat z u = d := by
 obtain ⟨i, hIi, hzi⟩ := hz;obtain ⟨j, hIj, huj⟩ := hu
 have hd : 0 < d := by
   rcases Nat.eq_zero_or_pos d with rfl | h0
   . exfalso; apply hzu; simp [hzi, huj]
   . exact h0
 refine ⟨hd, ?_⟩
 unfold distNat
 rcases lt_trichotomy i j with hij | rfl | hij
 . obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_lt hij
   have hu' : u = z + t * d + d := by rw [hzi, huj, ht]; ring
   rcases Nat.eq_zero_or_pos t with rfl | ht0
   . rw [Nat.zero_mul] at hu'; omega
   . exfalso
     have hw : a + (i + 1) * d = z + d := by rw [hzi]; ring
     have htd : d <= t * d := Nat.le_mul_of_pos_left d ht0
     refine hadj (i + 1) (hI j (i + 1) hIj (by omega)) ⟨?_, ?_⟩ <;> (rw [hw]; omega)
 . exfalso; exact hzu (by rw [hzi, huj])
 . obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_lt hij
   have hz' : z = u + t * d + d := by rw [hzi, huj, ht]; ring
   rcases Nat.eq_zero_or_pos t with rfl | ht0
   . rw [Nat.zero_mul] at hz'; omega
   . exfalso
     have hw : a + (j + 1) * d = u + d := by rw [huj]; ring
     have htd : d <= t * d := Nat.le_mul_of_pos_left d ht0
     refine hadj (j + 1) (hI i (j + 1) hIi (by omega)) ⟨?_, ?_⟩ <;> (rw [hw]; omega)
lemma ap_fill (a d : ℕ) (hd : 0 < d) (I : ℕ -> Prop) (hI : ∀ n m, I n -> m <= n -> I m) (z v y : ℕ) (hz : ∃ n, I n /\ z = a + n * d) (hv : ∃ n, I n /\ v = a + n * d) (hy1 : min z v <= y) (hy2 : y <= max z v) (hmod : y % d = z % d) : ∃ n, I n /\ y = a + n * d := by
 obtain ⟨i, hIi, hzi⟩ := hz;obtain ⟨h, hIh, hvh⟩ := hv;have hza : a <= z := by rw [hzi]; exact Nat.le_add_right _ _
 have hva : a <= v := by rw [hvh]; exact Nat.le_add_right _ _
 have hay : a <= y := by omega
 have hmod' : a % d = y % d := by rw [hmod, hzi, Nat.add_mul_mod_self_right]
 obtain ⟨n, hn⟩ := (Nat.modEq_iff_dvd' hay).mp hmod';have hyn : y = a + n * d := by rw [Nat.mul_comm n d]; omega
 refine ⟨n, ?_, hyn⟩
 rcases le_total i h with hih | hih
 . have hzv : z <= v := by
     rw [hzi, hvh]; exact Nat.add_le_add_left (Nat.mul_le_mul_right d hih) a
   have hnd : n * d <= h * d := by omega
   exact hI h n hIh (Nat.le_of_mul_le_mul_right hnd hd)
 . have hvz : v <= z := by
     rw [hzi, hvh]; exact Nat.add_le_add_left (Nat.mul_le_mul_right d hih) a
   have hnd : n * d <= i * d := by omega
   exact hI i n hIi (Nat.le_of_mul_le_mul_right hnd hd)
def runPart (S : Finset ℕ) (z d : ℕ) : Finset ℕ := S.filter (fun x => x % d = z % d /\ ∀ y ∈ Icc (min z x) (max z x), y % d = z % d -> y ∈ S)
lemma mem_runPart (S : Finset ℕ) (z d x : ℕ) : x ∈ runPart S z d ↔ x ∈ S /\ x % d = z % d /\ ∀ y, min z x <= y -> y <= max z x -> y % d = z % d -> y ∈ S := by
 unfold runPart;rw [mem_filter]
 constructor
 . rintro ⟨h1, h2, h3⟩
   exact ⟨h1, h2, fun y hy1 hy2 hy3 => h3 y (mem_Icc.mpr ⟨hy1, hy2⟩) hy3⟩
 . rintro ⟨h1, h2, h3⟩
   exact ⟨h1, h2, fun y hy hy3 => h3 y (mem_Icc.mp hy).1 (mem_Icc.mp hy).2 hy3⟩
lemma runPart_subset (S : Finset ℕ) (z d : ℕ) : runPart S z d ⊆ S := filter_subset _ _
lemma self_mem_runPart {S : Finset ℕ} {z : ℕ} (hz : z ∈ S) (d : ℕ) : z ∈ runPart S z d := by
 rw [mem_runPart]
 refine ⟨hz, rfl, fun y hy1 hy2 _ => ?_⟩
 have hyz : y = z := by omega
 rwa [hyz]
lemma runPart_isAP {S : Finset ℕ} {z d : ℕ} (hz : z ∈ S) (hd : 0 < d) : APSet (runPart S z d) := by
 have hne : (runPart S z d).Nonempty := ⟨z, self_mem_runPart hz d⟩
 set a := (runPart S z d).min' hne
 set b := (runPart S z d).max' hne
 have ha : a ∈ runPart S z d := min'_mem _ hne;have hb : b ∈ runPart S z d := max'_mem _ hne;have ham := (mem_runPart S z d a).mp ha;have hbm := (mem_runPart S z d b).mp hb;have haz : a <= z := min'_le _ _ (self_mem_runPart hz d);have hzb : z <= b := le_max' _ _ (self_mem_runPart hz d);obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' (le_trans haz hzb)).mp (ham.2.1.trans hbm.2.1.symm)
 refine ⟨a, d, fun n => n <= k, fun _ _ hn hmn => le_trans hmn hn, Nat.zero_le k, ?_⟩
 intro x
 constructor
 . intro hx
   have hxm := (mem_runPart S z d x).mp hx;have hax : a <= x := min'_le _ _ hx;have hxb : x <= b := le_max' _ _ hx;obtain ⟨n, hn⟩ := (Nat.modEq_iff_dvd' hax).mp (ham.2.1.trans hxm.2.1.symm)
   refine ⟨n, ?_, by rw [Nat.mul_comm n d]; omega⟩
   have hnd : n * d <= k * d := by rw [Nat.mul_comm n d, Nat.mul_comm k d]; omega
   exact Nat.le_of_mul_le_mul_right hnd hd
 . rintro ⟨n, hn, rfl⟩
   have hax : a <= a + n * d := Nat.le_add_right _ _
   have hxb : a + n * d <= b := by
     have : n * d <= k * d := Nat.mul_le_mul_right d hn;rw [Nat.mul_comm k d] at this; omega
   have hmod : (a + n * d) % d = z % d := by rw [Nat.add_mul_mod_self_right, ham.2.1]
   rw [mem_runPart]
   refine ⟨?_, hmod, ?_⟩
   . rcases le_total (a + n * d) z with hle | hle
     . exact ham.2.2 (a + n * d) (by omega) (by omega) hmod
     . exact hbm.2.2 (a + n * d) (by omega) (by omega) hmod
   . intro y hy1 hy2 hy3
     rcases le_total y z with hle | hle
     . exact ham.2.2 y (by omega) (by omega) hy3
     . exact hbm.2.2 y (by omega) (by omega) hy3
lemma runPart_eq_of_mem {S : Finset ℕ} {z d w : ℕ} (_hd : 0 < d) (hw : w ∈ runPart S z d) : runPart S w d = runPart S z d := by
 have hwm := (mem_runPart S z d w).mp hw
 ext x
 simp only [mem_runPart]
 constructor
 . rintro ⟨hxS, hxm, hxf⟩
   refine ⟨hxS, hxm.trans hwm.2.1, fun y hy1 hy2 hym => ?_⟩
   by_cases h1 : min z w <= y /\ y <= max z w
   . exact hwm.2.2 y h1.1 h1.2 hym
   . exact hxf y (by omega) (by omega) (hym.trans hwm.2.1.symm)
 . rintro ⟨hxS, hxm, hxf⟩
   refine ⟨hxS, hxm.trans hwm.2.1.symm, fun y hy1 hy2 hym => ?_⟩
   have hymz : y % d = z % d := hym.trans hwm.2.1
   by_cases h1 : min z w <= y /\ y <= max z w
   . exact hwm.2.2 y h1.1 h1.2 hymz
   . exact hxf y (by omega) (by omega) hymz
lemma triple_unique (S T : Finset ℕ) (hAP : APSet (S ∩ T)) (z u v : ℕ) (hzu : z ≠ u) (hadj : ∀ w ∈ S, ¬ (min z u < w /\ w < max z u)) (hvS : v ∈ S) (hvR : v ∉ runPart S z (distNat z u)) (hz : z ∈ S ∩ T) (hu : u ∈ S ∩ T) (hv : v ∈ S ∩ T) : False := by
 obtain ⟨a, d, I, hI, -, hX⟩ := hAP;have hz' := (hX z).mp hz;have hu' := (hX u).mp hu;have hv' := (hX v).mp hv
 obtain ⟨hd, hgap⟩ := ap_gap a d I hI z u hz' hu' hzu (fun n hn hbtw =>
   hadj (a + n * d) (mem_of_mem_inter_left ((hX _).mpr ⟨n, hn, rfl⟩)) hbtw)
 rw [hgap] at hvR;apply hvR;rw [mem_runPart]
 refine ⟨hvS, ?_, ?_⟩
 . obtain ⟨i, -, hzi⟩ := hz'
   obtain ⟨h, -, hvh⟩ := hv';rw [hzi, hvh, Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_right]
 . intro y hy1 hy2 hy3
   exact mem_of_mem_inter_left ((hX y).mpr (ap_fill a d hd I hI z v y hz' hv' hy1 hy2 hy3))
lemma exists_adjacent (S : Finset ℕ) (z : ℕ) (hz : z ∈ S) (h2 : 2 <= S.card) : ∃ u, u ∈ S /\ z ≠ u /\ ∀ w ∈ S, ¬ (min z u < w /\ w < max z u) := by
 have hne : (S.erase z).Nonempty := by rw [<- card_pos, card_erase_of_mem hz]; omega
 obtain ⟨u, hu, hmin⟩ := exists_min_image (S.erase z) (fun x => distNat z x) hne;obtain ⟨huz, huS⟩ := Finset.mem_erase.mp hu
 refine ⟨u, huS, fun h => huz h.symm, ?_⟩
 intro w hw hbtw;have hwz : w ≠ z := by intro h; rw [h] at hbtw; omega
 have h3 : distNat z u <= distNat z w := hmin w (Finset.mem_erase.mpr ⟨hwz, hw⟩);unfold distNat at h3; omega
def IsWellInter (N : ℕ) (F : Finset (Finset ℕ)) : Prop := (∀ S ∈ F, S ⊆ Icc 1 N) /\ (∀ S ∈ F, ∀ T ∈ F, S ≠ T -> APSet (S ∩ T))
lemma isWellInter_of_isArithInterSet {N : ℕ} {F : Finset (Finset ℕ)} (hF : Erdos272.IsArithInterSet N F) : IsWellInter N F := by
 obtain ⟨hpow, hpair⟩ := hF
 refine ⟨fun S hS => mem_powerset.mp (hpow hS), fun S hS T hT hST => ?_⟩
 obtain ⟨l, hl, hl'⟩ := hpair (mem_coe.mpr hS) (mem_coe.mpr hT) hST;exact apSet_of_isAP (S ∩ T) l hl hl'
lemma isWellInter_subset {N : ℕ} {F G : Finset (Finset ℕ)} (hF : IsWellInter N F) (hG : G ⊆ F) : IsWellInter N G := ⟨fun S hS => hF.1 S (hG hS), fun S hS T hT hST => hF.2 S (hG hS) T (hG hT) hST⟩
lemma wellInter_meet {N : ℕ} {F : Finset (Finset ℕ)} (hF : IsWellInter N F) {S T : Finset ℕ} (hS : S ∈ F) (hT : T ∈ F) (hST : S ≠ T) : (S ∩ T).Nonempty := by
 obtain ⟨a, d, I, -, hI0, hX⟩ := hF.2 S hS T hT hST;exact ⟨a, (hX a).mpr ⟨0, hI0, by simp⟩⟩
def IsDeltaTriplet (F : Finset (Finset ℕ)) (S : Finset ℕ) (a b c : ℕ) : Prop := a ∈ S /\ b ∈ S /\ c ∈ S /\ a ≠ b /\ a ≠ c /\ b ≠ c /\ ∀ T ∈ F, T ≠ S -> ¬ (a ∈ T /\ b ∈ T /\ c ∈ T)
lemma nu_triplet_fill {N : ℕ} {F : Finset (Finset ℕ)} (hF : IsWellInter N F) {S : Finset ℕ} (hS : S ∈ F) {x y z : ℕ} (hx : x ∈ S) (hy : y ∈ S) (hz : z ∈ S) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (hnu : ¬ IsDeltaTriplet F S x y z) :
   let g := Nat.gcd (distNat x y) (distNat x z)
   0 < g /\ y ∈ runPart S x g /\ z ∈ runPart S x g /\ ∀ w, min x (min y z) <= w -> w <= max x (max y z) -> w % g = x % g -> w ∈ S := by
 have hex : ∃ T ∈ F, T ≠ S /\ x ∈ T /\ y ∈ T /\ z ∈ T := by
   by_contra h;push Not at h;exact hnu ⟨hx, hy, hz, hxy, hxz, hyz, fun T hTF hTS ⟨h1, h2, h3⟩ => h T hTF hTS h1 h2 h3⟩
 obtain ⟨T, hTF, hTS, hxT, hyT, hzT⟩ := hex;obtain ⟨a, d, I, hI, -, hX⟩ := hF.2 S hS T hTF hTS.symm;have hx' := (hX x).mp (mem_inter.mpr ⟨hx, hxT⟩);have hy' := (hX y).mp (mem_inter.mpr ⟨hy, hyT⟩);have hz' := (hX z).mp (mem_inter.mpr ⟨hz, hzT⟩);obtain ⟨ix, hIx, hxe⟩ := hx';obtain ⟨iy, hIy, hye⟩ := hy';obtain ⟨iz, hIz, hze⟩ := hz'
 have hd : 0 < d := by
   rcases Nat.eq_zero_or_pos d with rfl | h0
   . exfalso; exact hxy (by simp [hxe, hye])
   . exact h0
 have hdxy : d ∣ distNat x y := by
   unfold distNat
   rcases le_total ix iy with hle | hle
   . have hle' : x <= y := by rw [hxe, hye]; exact Nat.add_le_add_left (Nat.mul_le_mul_right d hle) a
     have : max x y - min x y = (iy - ix) * d := by
       rw [max_eq_right hle', min_eq_left hle', hxe, hye];have : a + iy * d - (a + ix * d) = iy * d - ix * d := by omega
       rw [this, <- Nat.sub_mul]
     rw [this]; exact dvd_mul_left d _
   . have hle' : y <= x := by rw [hxe, hye]; exact Nat.add_le_add_left (Nat.mul_le_mul_right d hle) a
     have : max x y - min x y = (ix - iy) * d := by
       rw [max_eq_left hle', min_eq_right hle', hxe, hye];have : a + ix * d - (a + iy * d) = ix * d - iy * d := by omega
       rw [this, <- Nat.sub_mul]
     rw [this]; exact dvd_mul_left d _
 have hdxz : d ∣ distNat x z := by
   unfold distNat
   rcases le_total ix iz with hle | hle
   . have hle' : x <= z := by rw [hxe, hze]; exact Nat.add_le_add_left (Nat.mul_le_mul_right d hle) a
     have : max x z - min x z = (iz - ix) * d := by
       rw [max_eq_right hle', min_eq_left hle', hxe, hze];have : a + iz * d - (a + ix * d) = iz * d - ix * d := by omega
       rw [this, <- Nat.sub_mul]
     rw [this]; exact dvd_mul_left d _
   . have hle' : z <= x := by rw [hxe, hze]; exact Nat.add_le_add_left (Nat.mul_le_mul_right d hle) a
     have : max x z - min x z = (ix - iz) * d := by
       rw [max_eq_left hle', min_eq_right hle', hxe, hze];have : a + ix * d - (a + iz * d) = ix * d - iz * d := by omega
       rw [this, <- Nat.sub_mul]
     rw [this]; exact dvd_mul_left d _
 set g := Nat.gcd (distNat x y) (distNat x z)
 have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ (distNat_pos_of_ne hxy);have hdg : d ∣ g := Nat.dvd_gcd hdxy hdxz
 have hfill_pair : ∀ u v, (∃ n, I n /\ u = a + n * d) -> (∃ n, I n /\ v = a + n * d) -> ∀ w, min u v <= w -> w <= max u v -> w % g = x % g -> w ∈ S := by
   intro u v hu hv w hw1 hw2 hwg
   have hwd : w % d = x % d := by
     have h1 : w ≡ x [MOD g] := hwg;exact h1.of_dvd hdg
   have hwu : w % d = u % d := by
     obtain ⟨iu, -, hue⟩ := hu;rw [hwd, hxe, hue, Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_right]
   exact mem_of_mem_inter_left ((hX w).mpr (ap_fill a d hd I hI u v w hu hv hw1 hw2 hwu))
 have hy_mod : y % g = x % g := by
   have hd1 : g ∣ distNat x y := Nat.gcd_dvd_left _ _;unfold distNat at hd1
   rcases le_total x y with hle | hle
   . rw [max_eq_right hle, min_eq_left hle] at hd1
     exact ((Nat.modEq_iff_dvd' hle).mpr hd1).symm
   . rw [max_eq_left hle, min_eq_right hle] at hd1
     exact (Nat.modEq_iff_dvd' hle).mpr hd1
 have hz_mod : z % g = x % g := by
   have hd2 : g ∣ distNat x z := Nat.gcd_dvd_right _ _;unfold distNat at hd2
   rcases le_total x z with hle | hle
   . rw [max_eq_right hle, min_eq_left hle] at hd2
     exact ((Nat.modEq_iff_dvd' hle).mpr hd2).symm
   . rw [max_eq_left hle, min_eq_right hle] at hd2
     exact (Nat.modEq_iff_dvd' hle).mpr hd2
 refine ⟨hgpos, ?_, ?_, ?_⟩
 . rw [mem_runPart]
   exact ⟨hy, hy_mod, fun w hw1 hw2 hwg => hfill_pair x y ⟨ix, hIx, hxe⟩ ⟨iy, hIy, hye⟩ w hw1 hw2 hwg⟩
 . rw [mem_runPart]
   exact ⟨hz, hz_mod, fun w hw1 hw2 hwg => hfill_pair x z ⟨ix, hIx, hxe⟩ ⟨iz, hIz, hze⟩ w hw1 hw2 hwg⟩
 . intro w hw1 hw2 hwg
   rcases le_total w x with hwx | hxw
   . rcases le_total y z with hyz' | hzy'
     . exact hfill_pair x y ⟨ix, hIx, hxe⟩ ⟨iy, hIy, hye⟩ w (by omega) (by omega) hwg
     . exact hfill_pair x z ⟨ix, hIx, hxe⟩ ⟨iz, hIz, hze⟩ w (by omega) (by omega) hwg
   . rcases le_total y z with hyz' | hzy'
     . exact hfill_pair x z ⟨ix, hIx, hxe⟩ ⟨iz, hIz, hze⟩ w (by omega) (by omega) hwg
     . exact hfill_pair x y ⟨ix, hIx, hxe⟩ ⟨iy, hIy, hye⟩ w (by omega) (by omega) hwg
def reflectSet (N : ℕ) (S : Finset ℕ) : Finset ℕ := S.image (fun x => N + 1 - x)
lemma reflectSet_involutive {N : ℕ} {S : Finset ℕ} (hS : S ⊆ Icc 1 N) : reflectSet N (reflectSet N S) = S := by
 ext x
 simp only [reflectSet, mem_image]
 constructor
 . rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
   have hzI := mem_Icc.mp (hS hz);have : N + 1 - (N + 1 - z) = z := by omega
   rwa [this]
 . intro hx
   have hxI := mem_Icc.mp (hS hx);exact ⟨N + 1 - x, ⟨x, hx, rfl⟩, by omega⟩
lemma reflectSet_inter {N : ℕ} {S T : Finset ℕ} (hS : S ⊆ Icc 1 N) (hT : T ⊆ Icc 1 N) : reflectSet N (S ∩ T) = reflectSet N S ∩ reflectSet N T := by
 ext y
 simp only [reflectSet, mem_inter, mem_image]
 constructor
 . rintro ⟨x, ⟨hxS, hxT⟩, rfl⟩
   exact ⟨⟨x, hxS, rfl⟩, ⟨x, hxT, rfl⟩⟩
 . rintro ⟨⟨x1, hx1, h1⟩, ⟨x2, hx2, h2⟩⟩
   have h1I := mem_Icc.mp (hS hx1);have h2I := mem_Icc.mp (hT hx2);have hx : x1 = x2 := by omega
   subst hx;exact ⟨x1, ⟨hx1, hx2⟩, h1⟩
lemma reflectSet_apSet {N : ℕ} {X : Finset ℕ} (hX : X ⊆ Icc 1 N) (hAP : APSet X) : APSet (reflectSet N X) := by
 obtain ⟨a, d, I, hI, hI0, hmem⟩ := hAP;have hne : X.Nonempty := ⟨a, (hmem a).mpr ⟨0, hI0, by simp⟩⟩
 set b := X.max' hne
 have hbX : b ∈ X := max'_mem X hne;obtain ⟨k, hIk, hbk⟩ := (hmem b).mp hbX;have hbI := mem_Icc.mp (hX hbX)
 have hmem_le : ∀ n, I n -> n * d <= k * d := by
   intro n hn;have hxn : a + n * d ∈ X := (hmem _).mpr ⟨n, hn, rfl⟩;have hle : a + n * d <= b := le_max' X _ hxn;omega
 refine ⟨N + 1 - b, d, fun n => n <= k, fun _ _ hn hmn => le_trans hmn hn, Nat.zero_le k, ?_⟩
 intro y;simp only [reflectSet, mem_image]
 constructor
 . rintro ⟨x, hx, rfl⟩
   obtain ⟨n, hIn, rfl⟩ := (hmem x).mp hx;have hnd := hmem_le n hIn
   rcases Nat.eq_zero_or_pos d with rfl | hd
   . refine ⟨0, Nat.zero_le k, ?_⟩
     simp only [Nat.mul_zero, add_zero] at hbk ⊢; rw [hbk]
   . have hnk : n <= k := Nat.le_of_mul_le_mul_right hnd hd
     refine ⟨k - n, Nat.sub_le k n, ?_⟩
     have hxI := mem_Icc.mp (hX ((hmem _).mpr ⟨n, hIn, rfl⟩));have hkn : (k - n) * d = k * d - n * d := Nat.sub_mul k n d;omega
 . rintro ⟨m, hmk, rfl⟩
   refine ⟨a + (k - m) * d, (hmem _).mpr ⟨k - m, hI k (k - m) hIk (Nat.sub_le k m), rfl⟩, ?_⟩
   have hkm : (k - m) * d = k * d - m * d := Nat.sub_mul k m d;have hmd : m * d <= k * d := Nat.mul_le_mul_right d hmk;omega
lemma reflectFamily_wellInter {N : ℕ} {F : Finset (Finset ℕ)} (hF : IsWellInter N F) : IsWellInter N (F.image (reflectSet N)) /\ (F.image (reflectSet N)).card = F.card := by
 have hinj : Set.InjOn (reflectSet N) (F : Set (Finset ℕ)) := by
   intro S hS T hT hST;have h1 := reflectSet_involutive (hF.1 S (mem_coe.mp hS));have h2 := reflectSet_involutive (hF.1 T (mem_coe.mp hT));rw [<- h1, hST, h2]
 refine ⟨⟨?_, ?_⟩, card_image_of_injOn hinj⟩
 . intro R hR
   obtain ⟨S, hS, rfl⟩ := mem_image.mp hR;intro y hy;obtain ⟨x, hx, rfl⟩ := mem_image.mp hy;have hxI := mem_Icc.mp (hF.1 S hS hx);exact mem_Icc.mpr ⟨by omega, by omega⟩
 . intro R1 hR1 R2 hR2 hne
   obtain ⟨S1, hS1, rfl⟩ := mem_image.mp hR1;obtain ⟨S2, hS2, rfl⟩ := mem_image.mp hR2;have hS12 : S1 ≠ S2 := fun h => hne (by rw [h])
   rw [<- reflectSet_inter (hF.1 S1 hS1) (hF.1 S2 hS2)];exact reflectSet_apSet (Finset.inter_subset_left.trans (hF.1 S1 hS1)) (hF.2 S1 hS1 S2 hS2 hS12)
lemma lower_bound_maxArithInterCard (N : ℕ) (hN : 3 <= N) : (N - 1) * (N - 2) / 2 <= Erdos272.maxArithInterCard N := by
 let P2 : Finset (Finset ℕ) := (Icc 2 N).powersetCard 2
 let F : Finset (Finset ℕ) := P2.image (fun p => insert 1 p)
 have h1notin : ∀ p ∈ P2, 1 ∉ p := by
   intro p hp h1;have hsub := (mem_powersetCard.mp hp).1;have := (mem_Icc.mp (hsub h1)).1;omega
 have hinj : Set.InjOn (fun p => insert 1 p) (P2 : Set (Finset ℕ)) := by
   intro p hp q hq heq;have hp1 := h1notin p (mem_coe.mp hp);have hq1 := h1notin q (mem_coe.mp hq)
   ext x
   by_cases hx1 : x = 1
   . subst hx1; simp [hp1, hq1]
   . have := Finset.ext_iff.mp heq x
     simpa [mem_insert, hx1] using this
 have hcardF : F.card = (N - 1) * (N - 2) / 2 := by
   rw [card_image_of_injOn hinj, card_powersetCard, Nat.card_Icc];have hsub : N + 1 - 2 = N - 1 := by omega
   have hsub2 : N - 1 - 1 = N - 2 := by omega
   rw [hsub, Nat.choose_two_right, hsub2]
 have hF : Erdos272.IsArithInterSet N F := by
   refine ⟨?_, ?_⟩
   . intro S hS
     obtain ⟨p, hp, rfl⟩ := mem_image.mp hS;rw [mem_powerset];intro x hx
     rcases mem_insert.mp hx with rfl | hxp
     . exact mem_Icc.mpr ⟨le_rfl, by omega⟩
     . have := mem_Icc.mp ((mem_powersetCard.mp hp).1 hxp)
       exact mem_Icc.mpr ⟨by omega, this.2⟩
   . intro S hS T hT hST
     obtain ⟨p, hp, rfl⟩ := mem_image.mp (mem_coe.mp hS);obtain ⟨q, hq, rfl⟩ := mem_image.mp (mem_coe.mp hT);have hpq : p ≠ q := fun h => hST (by rw [h])
     have hpcard : p.card = 2 := (mem_powersetCard.mp hp).2;have hqcard : q.card = 2 := (mem_powersetCard.mp hq).2;have hne : (insert 1 p ∩ insert 1 q).Nonempty := ⟨1, mem_inter.mpr ⟨Finset.mem_insert_self _ _, Finset.mem_insert_self _ _⟩⟩
     have hint_eq : insert 1 p ∩ insert 1 q = insert 1 (p ∩ q) := by
       ext x; simp only [mem_inter, mem_insert]; tauto
     have hpq_le : (p ∩ q).card <= 1 := by
       by_contra hgt;push Not at hgt;have hle : (p ∩ q).card <= p.card := card_le_card Finset.inter_subset_left;have heq1 : p ∩ q = p := eq_of_subset_of_card_le Finset.inter_subset_left (by omega);have heq2 : p ∩ q = q := eq_of_subset_of_card_le Finset.inter_subset_right (by omega);exact hpq (heq1.symm.trans heq2)
     have hcard2 : (insert 1 p ∩ insert 1 q).card <= 2 := by
       rw [hint_eq];exact le_trans (card_insert_le _ _) (by omega)
     exact isAP_of_card_le_two _ hne hcard2
 unfold Erdos272.maxArithInterCard;rw [<- hcardF]
 refine le_csSup ?_ ⟨F, hF, rfl⟩
 refine ⟨((Icc 1 N).powerset).card, ?_⟩
 rintro b ⟨G, hG, rfl⟩;exact card_le_card hG.1
lemma card_size_le_two {N : ℕ} {F : Finset (Finset ℕ)} (hF : IsWellInter N F) : (F.filter (fun S => S.card <= 2)).card <= N + 3 := by
 let F1 := F.filter (fun S => S.card <= 1)
 let F2 := F.filter (fun S => S.card = 2)
 have hcov : F.filter (fun S => S.card <= 2) ⊆ F1 ∪ F2 := by
   intro S hS;obtain ⟨hSF, hSc⟩ := mem_filter.mp hS
   rcases Nat.le_iff_lt_or_eq.mp hSc with hlt | heq
   . exact mem_union_left _ (mem_filter.mpr ⟨hSF, by omega⟩)
   . exact mem_union_right _ (mem_filter.mpr ⟨hSF, heq⟩)
 have hF1 : F1.card <= 1 := by
   rw [card_le_one];intro S hS T hT;by_contra hne;obtain ⟨hSF, hSc⟩ := mem_filter.mp hS;obtain ⟨hTF, hTc⟩ := mem_filter.mp hT;obtain ⟨x, hx⟩ := wellInter_meet hF hSF hTF hne;have hxS := mem_of_mem_inter_left hx;have hxT := mem_of_mem_inter_right hx
   have hS1 : S = {x} := eq_singleton_iff_unique_mem.mpr ⟨hxS, fun y hy => by
     by_contra hyx;have := one_lt_card.mpr ⟨x, hxS, y, hy, Ne.symm hyx⟩
     omega⟩
   have hT1 : T = {x} := eq_singleton_iff_unique_mem.mpr ⟨hxT, fun y hy => by
     by_contra hyx;have := one_lt_card.mpr ⟨x, hxT, y, hy, Ne.symm hyx⟩
     omega⟩
   exact hne (hS1.trans hT1.symm)
 have hF2 : F2.card <= N + 2 := by
   rcases F2.eq_empty_or_nonempty with hE | ⟨A0, hA0⟩
   . rw [hE]; simp
   obtain ⟨hA0F, hA0c⟩ := mem_filter.mp hA0;obtain ⟨a, b, hab, hA0eq⟩ := card_eq_two.mp hA0c
   by_cases hall_a : ∀ S ∈ F2, a ∈ S
   . have hsub : F2 ⊆ (Icc 1 N).image (fun y => ({a, y} : Finset ℕ)) := by
       intro S hS;obtain ⟨hSF, hSc⟩ := mem_filter.mp hS;have haS := hall_a S hS;have hne' : (S.erase a).Nonempty := by rw [<- card_pos, card_erase_of_mem haS]; omega
       obtain ⟨y, hy⟩ := hne';obtain ⟨hya, hyS⟩ := Finset.mem_erase.mp hy
       have hSeq : S = {a, y} := by
         refine (eq_of_subset_of_card_le ?_ ?_).symm
         . intro z hz
           rcases mem_insert.mp hz with rfl | hz'
           . exact haS
           . rw [mem_singleton.mp hz']; exact hyS
         . rw [card_pair (Ne.symm hya), hSc]
       exact mem_image.mpr ⟨y, hF.1 S hSF hyS, hSeq.symm⟩
     calc F2.card <= ((Icc 1 N).image (fun y => ({a, y} : Finset ℕ))).card :=
           card_le_card hsub
       _ <= (Icc 1 N).card := card_image_le
       _ = N := by rw [Nat.card_Icc]; omega
       _ <= N + 2 := by omega
   . push Not at hall_a
     obtain ⟨A1, hA1, haA1⟩ := hall_a;obtain ⟨hA1F, hA1c⟩ := mem_filter.mp hA1;have hA1ne : A1 ≠ A0 := fun h => haA1 (by rw [h, hA0eq]; simp)
     obtain ⟨u, hu⟩ := wellInter_meet hF hA1F hA0F hA1ne;have huA1 := mem_of_mem_inter_left hu;have huA0 := mem_of_mem_inter_right hu
     have hub : u = b := by
       rw [hA0eq] at huA0
       rcases mem_insert.mp huA0 with rfl | hu'
       . exact absurd huA1 haA1
       . exact mem_singleton.mp hu'
     subst u;have hne1 : (A1.erase b).Nonempty := by rw [<- card_pos, card_erase_of_mem huA1]; omega
     obtain ⟨c, hc⟩ := hne1;obtain ⟨hcb, hcA1⟩ := Finset.mem_erase.mp hc;have hca : c ≠ a := fun h => haA1 (h ▸ hcA1)
     have hA1eq : A1 = {b, c} := by
       refine (eq_of_subset_of_card_le ?_ ?_).symm
       . intro z hz
         rcases mem_insert.mp hz with rfl | hz'
         . exact huA1
         . rw [mem_singleton.mp hz']; exact hcA1
       . rw [card_pair (Ne.symm hcb), hA1c]
     by_cases hall_b : ∀ S ∈ F2, b ∈ S
     . have hsub : F2 ⊆ (Icc 1 N).image (fun y => ({b, y} : Finset ℕ)) := by
         intro S hS;obtain ⟨hSF, hSc⟩ := mem_filter.mp hS;have hbS := hall_b S hS;have hne' : (S.erase b).Nonempty := by rw [<- card_pos, card_erase_of_mem hbS]; omega
         obtain ⟨y, hy⟩ := hne';obtain ⟨hyb, hyS⟩ := Finset.mem_erase.mp hy
         have hSeq : S = {b, y} := by
           refine (eq_of_subset_of_card_le ?_ ?_).symm
           . intro z hz
             rcases mem_insert.mp hz with rfl | hz'
             . exact hbS
             . rw [mem_singleton.mp hz']; exact hyS
           . rw [card_pair (Ne.symm hyb), hSc]
         exact mem_image.mpr ⟨y, hF.1 S hSF hyS, hSeq.symm⟩
       calc F2.card <= ((Icc 1 N).image (fun y => ({b, y} : Finset ℕ))).card :=
             card_le_card hsub
         _ <= (Icc 1 N).card := card_image_le
         _ = N := by rw [Nat.card_Icc]; omega
         _ <= N + 2 := by omega
     . push Not at hall_b
       obtain ⟨A2, hA2, hbA2⟩ := hall_b;obtain ⟨hA2F, hA2c⟩ := mem_filter.mp hA2;have hA2ne0 : A2 ≠ A0 := fun h => hbA2 (by rw [h, hA0eq]; simp)
       have hA2ne1 : A2 ≠ A1 := fun h => hbA2 (by rw [h, hA1eq]; simp)
       obtain ⟨x0, hx0⟩ := wellInter_meet hF hA2F hA0F hA2ne0;obtain ⟨x1, hx1⟩ := wellInter_meet hF hA2F hA1F hA2ne1
       have haA2 : a ∈ A2 := by
         have h0 := mem_of_mem_inter_right hx0;rw [hA0eq] at h0
         rcases mem_insert.mp h0 with rfl | h0'
         . exact mem_of_mem_inter_left hx0
         . rw [mem_singleton.mp h0'] at hx0
           exact absurd (mem_of_mem_inter_left hx0) hbA2
       have hcA2 : c ∈ A2 := by
         have h1 := mem_of_mem_inter_right hx1;rw [hA1eq] at h1
         rcases mem_insert.mp h1 with rfl | h1'
         . exact absurd (mem_of_mem_inter_left hx1) hbA2
         . rw [mem_singleton.mp h1'] at hx1
           exact mem_of_mem_inter_left hx1
       have hA2eq : A2 = {a, c} := by
         refine (eq_of_subset_of_card_le ?_ ?_).symm
         . intro z hz
           rcases mem_insert.mp hz with rfl | hz'
           . exact haA2
           . rw [mem_singleton.mp hz']; exact hcA2
         . rw [card_pair (Ne.symm hca), hA2c]
       have hsub : F2 ⊆ ({A0, A1, A2} : Finset (Finset ℕ)) := by
         intro S hS
         by_cases h0 : S = A0
         . simp [h0]
         by_cases h1 : S = A1
         . simp [h1]
         by_cases h2 : S = A2
         . simp [h2]
         exfalso
         obtain ⟨hSF, hSc⟩ := mem_filter.mp hS;obtain ⟨y0, hy0⟩ := wellInter_meet hF hSF hA0F h0;obtain ⟨y1, hy1⟩ := wellInter_meet hF hSF hA1F h1;obtain ⟨y2, hy2⟩ := wellInter_meet hF hSF hA2F h2;have hy0' : y0 = a \/ y0 = b := by have := mem_of_mem_inter_right hy0; rw [hA0eq] at this; simpa using this
         have hy1' : y1 = b \/ y1 = c := by have := mem_of_mem_inter_right hy1; rw [hA1eq] at this; simpa using this
         have hy2' : y2 = a \/ y2 = c := by have := mem_of_mem_inter_right hy2; rw [hA2eq] at this; simpa using this
         have hm0 := mem_of_mem_inter_left hy0;have hm1 := mem_of_mem_inter_left hy1;have hm2 := mem_of_mem_inter_left hy2
         have hEq : ∀ x y : ℕ, x ∈ S -> y ∈ S -> x ≠ y -> S = {x, y} := by
           intro x y hxS hyS hxy
           refine (eq_of_subset_of_card_le ?_ ?_).symm
           . intro z hz; rcases mem_insert.mp hz with rfl | hz'
             . exact hxS
             . rw [mem_singleton.mp hz']; exact hyS
           . rw [card_pair hxy, hSc]
         rcases hy0' with hy0a | hy0b
         . rcases hy1' with hy1b | hy1c
           . exact h0 ((hEq a b (hy0a ▸ hm0) (hy1b ▸ hm1) hab).trans hA0eq.symm)
           . exact h2 ((hEq a c (hy0a ▸ hm0) (hy1c ▸ hm1) (Ne.symm hca)).trans hA2eq.symm)
         . rcases hy2' with hy2a | hy2c
           . exact h0 ((hEq a b (hy2a ▸ hm2) (hy0b ▸ hm0) hab).trans hA0eq.symm)
           . exact h1 ((hEq b c (hy0b ▸ hm0) (hy2c ▸ hm2) (Ne.symm hcb)).trans hA1eq.symm)
       calc F2.card <= ({A0, A1, A2} : Finset (Finset ℕ)).card := card_le_card hsub
         _ <= 3 := by
           refine le_trans (card_insert_le _ _) ?_
           refine Nat.add_le_add_right (le_trans (card_insert_le _ _) ?_) 1
           simp
         _ <= N + 2 := by
           have h1N : 1 <= N := by
             have haA0 : a ∈ A0 := by rw [hA0eq]; exact Finset.mem_insert_self a {b}
             have := mem_Icc.mp (hF.1 A0 hA0F haA0);omega
           omega
 calc (F.filter (fun S => S.card <= 2)).card
     <= (F1 ∪ F2).card := card_le_card hcov
   _ <= F1.card + F2.card := card_union_le _ _
   _ <= N + 3 := by omega
lemma apSet_canonical {X : Finset ℕ} (hAP : APSet X) (hc : 2 <= X.card) : ∃ d : ℕ, 0 < d /\
     let a := X.min' (card_pos.mp (by omega))
     let b := X.max' (card_pos.mp (by omega))
     a < b /\ d ∣ (b - a) /\
     (∀ x, x ∈ X ↔ a <= x /\ x <= b /\ x % d = a % d) /\
     (X.card - 1) * d = b - a := by
 have hne : X.Nonempty := card_pos.mp (by omega);obtain ⟨a0, d, I, hI, hI0, hX⟩ := hAP
 set a := X.min' hne
 set b := X.max' hne
 have ha : a ∈ X := min'_mem X hne;have hb : b ∈ X := max'_mem X hne
 have hab : a < b := by
   by_contra hle;have heq : a = b := le_antisymm (min'_le X b hb) (by omega)
   have hsub : X ⊆ {a} := fun x hx => mem_singleton.mpr (by
     have h1 := min'_le X x hx;have h2 := le_max' X x hx
     omega)
   have := card_le_card hsub;simp at this; omega
 obtain ⟨ia, hIa, hae⟩ := (hX a).mp ha;obtain ⟨ib, hIb, hbe⟩ := (hX b).mp hb
 have hd : 0 < d := by
   rcases Nat.eq_zero_or_pos d with rfl | h0
   . simp at hae hbe; omega
   . exact h0
 have ha0_eq : a = a0 := by
   have ha0X : a0 ∈ X := (hX a0).mpr ⟨0, hI0, by simp⟩;have h1 : a <= a0 := min'_le X a0 ha0X;omega
 have hiab : ia = 0 := by
   have : ia * d = 0 := by omega
   rcases Nat.mul_eq_zero.mp this with h | h
   . exact h
   . omega
 have hmem_iff : ∀ x, x ∈ X ↔ a <= x /\ x <= b /\ x % d = a % d := by
   intro x
   constructor
   . intro hx
     obtain ⟨ix, -, hxe⟩ := (hX x).mp hx
     refine ⟨min'_le X x hx, le_max' X x hx, ?_⟩
     rw [hxe, ha0_eq, Nat.add_mul_mod_self_right]
   . rintro ⟨h1, h2, h3⟩
     exact (hX x).mpr (ap_fill a0 d hd I hI a b x ⟨ia, hIa, hae⟩ ⟨ib, hIb, hbe⟩ (by omega) (by omega) h3)
 have hba : b - a = ib * d := by omega
 have hcard : X.card = ib + 1 := by
   have hbij : X = (range (ib + 1)).image (fun n => a + n * d) := by
     ext x
     rw [hmem_iff, mem_image]
     constructor
     . rintro ⟨h1, h2, h3⟩
       obtain ⟨n, hn⟩ := (Nat.modEq_iff_dvd' h1).mp h3.symm;have hnd : n * d <= ib * d := by rw [Nat.mul_comm n d]; omega
       have hnle : n <= ib := Nat.le_of_mul_le_mul_right hnd hd;exact ⟨n, mem_range.mpr (by omega), by rw [Nat.mul_comm n d]; omega⟩
     . rintro ⟨n, hn, rfl⟩
       have hnle : n <= ib := Nat.lt_succ_iff.mp (mem_range.mp hn);have hnd : n * d <= ib * d := Nat.mul_le_mul_right d hnle;exact ⟨Nat.le_add_right _ _, by omega, Nat.add_mul_mod_self_right _ _ _⟩
   rw [hbij, card_image_of_injective _ (fun n1 n2 h =>
     Nat.eq_of_mul_eq_mul_right hd (by omega)), card_range]
 refine ⟨d, hd, hab, ⟨ib, by rw [Nat.mul_comm]; exact hba⟩, hmem_iff, ?_⟩
 rw [hcard]; simp [hba]
lemma harmonic_le_one_add_log (M : ℕ) (hM : 1 <= M) : ∑ d ∈ Icc 1 M, (1 : ℝ) / d <= 1 + Real.log M := by
 induction M with
 | zero => omega
 | succ m ih =>
   rcases Nat.eq_zero_or_pos m with rfl | hm
   . simp
   . have hIcc : Icc 1 (m + 1) = insert (m + 1) (Icc 1 m) := by
       ext x; simp only [mem_Icc, mem_insert]; omega
     rw [hIcc, sum_insert (by simp)];have hm1 : 1 <= m := hm;have hih := ih hm1;have hpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
     have hstep : (1 : ℝ) / (m + 1 : ℕ) <= Real.log (m + 1 : ℕ) - Real.log m := by
       have hlog := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < ((m + 1 : ℕ) : ℝ) / m by positivity);have h1 : 1 - (((m + 1 : ℕ) : ℝ) / m)⁻¹ = (1 : ℝ) / (m + 1 : ℕ) := by push_cast; field_simp; ring
       rw [h1, Real.log_div (by positivity) (by positivity)] at hlog;exact hlog
     linarith
lemma sum_inv_sq_from_four (M : ℕ) : ∑ d ∈ Icc 4 M, (1 : ℝ) / (d : ℝ) ^ 2 <= 1 / 3 := by
 have h1 : ∑ d ∈ Icc 4 M, (1 : ℝ) / (d : ℝ) ^ 2
     <= ∑ d ∈ Icc 4 M, ((1 : ℝ) / (d - 1 : ℕ) - 1 / (d : ℝ)) := by
   apply sum_le_sum;intro d hd;have hd4 : 4 <= d := (mem_Icc.mp hd).1;have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
   have hdm : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
   rw [hdm]
   have hdmpos : (0 : ℝ) < (d : ℝ) - 1 := by
     have : (4 : ℝ) <= (d : ℝ) := by exact_mod_cast hd4
     linarith
   rw [div_sub_div _ _ (ne_of_gt hdmpos) (ne_of_gt hdpos)];have hnum : 1 * (d : ℝ) - ((d : ℝ) - 1) * 1 = 1 := by ring
   rw [hnum];apply one_div_le_one_div_of_le (by positivity);nlinarith
 refine le_trans h1 ?_
 induction M with
 | zero => simp
 | succ m ih =>
   by_cases hm : m < 3
   . have : Icc 4 (m + 1) = ∅ := by
       ext x; simp only [mem_Icc, notMem_empty, iff_false]; omega
     rw [this]; norm_num
   . by_cases hm3 : m = 3
     . subst hm3; norm_num
     . have hm4 : 4 <= m := by omega
       have hIcc : Icc 4 (m + 1) = insert (m + 1) (Icc 4 m) := by
         ext x; simp only [mem_Icc, mem_insert]; omega
       have htel : ∀ k : ℕ, ∑ d ∈ Icc 4 (k + 4), ((1 : ℝ) / (d - 1 : ℕ) - 1 / (d : ℝ)) = 1 / 3 - 1 / (k + 4 : ℕ) := by
         intro k
         induction k with
         | zero => norm_num
         | succ j ihj =>
           have hI : Icc 4 (j + 1 + 4) = insert (j + 1 + 4) (Icc 4 (j + 4)) := by
             ext x; simp only [mem_Icc, mem_insert]; omega
           rw [hI, sum_insert (by simp), ihj];have hsub : j + 1 + 4 - 1 = j + 4 := by omega
           rw [hsub]; ring
       have hk : m + 1 = (m - 3) + 4 := by omega
       rw [hk, htel (m - 3)];have hpos : (0 : ℝ) <= 1 / (((m - 3) + 4 : ℕ) : ℝ) := by positivity
       linarith
lemma sum_inv_sq_le_61_36 (M : ℕ) : ∑ d ∈ Icc 1 M, (1 : ℝ) / (d : ℝ) ^ 2 <= 61 / 36 := by
 have hsub : Icc 1 M ⊆ {1, 2, 3} ∪ Icc 4 M := by
   intro d hd;have := mem_Icc.mp hd
   by_cases h4 : d <= 3
   . apply mem_union_left; simp; omega
   . apply mem_union_right; exact mem_Icc.mpr ⟨by omega, this.2⟩
 have hdisj : Disjoint ({1, 2, 3} : Finset ℕ) (Icc 4 M) := by
   rw [Finset.disjoint_left];intro x hx1 hx2;have := (mem_Icc.mp hx2).1;simp at hx1; omega
 calc ∑ d ∈ Icc 1 M, (1 : ℝ) / (d : ℝ) ^ 2
     <= ∑ d ∈ ({1, 2, 3} ∪ Icc 4 M), (1 : ℝ) / (d : ℝ) ^ 2 := sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
   _ = ∑ d ∈ ({1, 2, 3} : Finset ℕ), (1 : ℝ) / (d : ℝ) ^ 2 + ∑ d ∈ Icc 4 M, (1 : ℝ) / (d : ℝ) ^ 2 := sum_union hdisj
   _ <= (1 + 1 / 4 + 1 / 9) + 1 / 3 := by
       have h123 : ∑ d ∈ ({1, 2, 3} : Finset ℕ), (1 : ℝ) / (d : ℝ) ^ 2 = 1 + 1 / 4 + 1 / 9 := by norm_num
       linarith [h123, sum_inv_sq_from_four M]
   _ = 61 / 36 := by norm_num
lemma sum_inv_sq_from_two (M : ℕ) : ∑ d ∈ Icc 2 M, (1 : ℝ) / (d : ℝ) ^ 2 <= 25 / 36 := by
 by_cases hM : M < 2
 . have : Icc 2 M = ∅ := by
     ext x; simp only [mem_Icc, notMem_empty, iff_false]; omega
   rw [this]; norm_num
 . have hI : Icc 1 M = insert 1 (Icc 2 M) := by
     ext x; simp only [mem_Icc, mem_insert]; omega
   have h1 := sum_inv_sq_le_61_36 M;rw [hI, sum_insert (by simp)] at h1;norm_num at h1 ⊢;linarith
lemma sum_inv_sq_tail (K M : ℕ) (hK : 1 <= K) : ∑ d ∈ Icc (K + 1) M, (1 : ℝ) / (d : ℝ) ^ 2 <= 1 / (K : ℝ) := by
 have h1 : ∑ d ∈ Icc (K + 1) M, (1 : ℝ) / (d : ℝ) ^ 2
     <= ∑ d ∈ Icc (K + 1) M, ((1 : ℝ) / (d - 1 : ℕ) - 1 / (d : ℝ)) := by
   apply sum_le_sum;intro d hd;have hdK : K + 1 <= d := (mem_Icc.mp hd).1;have hd2 : 2 <= d := by omega
   have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
   have hdm : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
   rw [hdm]
   have hdmpos : (0 : ℝ) < (d : ℝ) - 1 := by
     have : (2 : ℝ) <= (d : ℝ) := by exact_mod_cast hd2
     linarith
   rw [div_sub_div _ _ (ne_of_gt hdmpos) (ne_of_gt hdpos)];have hnum : 1 * (d : ℝ) - ((d : ℝ) - 1) * 1 = 1 := by ring
   rw [hnum];apply one_div_le_one_div_of_le (by positivity);nlinarith
 refine le_trans h1 ?_
 by_cases hM : M < K + 1
 . have : Icc (K + 1) M = ∅ := by
     ext x; simp only [mem_Icc, notMem_empty, iff_false]; omega
   rw [this]; simp
 . have htel : ∀ j : ℕ, ∑ d ∈ Icc (K + 1) (j + K + 1), ((1 : ℝ) / (d - 1 : ℕ) - 1 / (d : ℝ)) = 1 / (K : ℝ) - 1 / (j + K + 1 : ℕ) := by
     intro j
     induction j with
     | zero =>
       simp only [zero_add, Finset.Icc_self, sum_singleton, add_tsub_cancel_right]
     | succ t iht =>
       have hI : Icc (K + 1) (t + 1 + K + 1) = insert (t + 1 + K + 1) (Icc (K + 1) (t + K + 1)) := by
         ext x; simp only [mem_Icc, mem_insert]; omega
       rw [hI, sum_insert (by simp), iht];have hsub : t + 1 + K + 1 - 1 = t + K + 1 := by omega
       rw [hsub]; ring
   have hMeq : M = (M - (K + 1)) + K + 1 := by omega
   rw [hMeq, htel (M - (K + 1))];have hpos : (0 : ℝ) <= 1 / ((M - (K + 1) + K + 1 : ℕ) : ℝ) := by positivity
   linarith
lemma card_AP_step_endpoints {N d : ℕ} (hd : 1 <= d) {F : Finset (Finset ℕ)} (hF : IsWellInter N F) (hstep : ∀ S ∈ F, 2 <= S.card /\ APSet S /\ ∀ x ∈ S, ∀ y ∈ S, x % d = y % d /\ (∀ z, min x y <= z -> z <= max x y -> z % d = x % d -> z ∈ S)) {a1 a2 b1 b2 : ℕ} (hend : ∀ S ∈ F, (∃ hne : S.Nonempty, S.min' hne ∈ Icc a1 a2 /\ S.max' hne ∈ Icc b1 b2)) : (F.card : ℝ) <= ((a2 + 1 - a1 : ℕ) / (d : ℝ) + 1) * ((b2 + 1 - b1 : ℕ) / (d : ℝ) + 1) := by
 rcases F.eq_empty_or_nonempty with rfl | ⟨S0, hS0⟩
 . simp; positivity
 obtain ⟨hne0, -, -⟩ := hend S0 hS0
 set r := S0.min' hne0 % d
 have hmod : ∀ S ∈ F, ∀ x ∈ S, x % d = r := by
   intro S hS x hx
   by_cases hSS0 : S = S0
   . subst hSS0
     exact (hstep S hS).2.2 x hx (S.min' hne0) (min'_mem S hne0) |>.1
   . obtain ⟨w, hw⟩ := wellInter_meet hF hS hS0 hSS0
     have h1 := ((hstep S hS).2.2 x hx w (mem_of_mem_inter_left hw)).1;have h2 := ((hstep S0 hS0).2.2 w (mem_of_mem_inter_right hw) (S0.min' hne0) (min'_mem S0 hne0)).1;exact h1.trans h2
 let Aset := (Icc a1 a2).filter (fun x => x % d = r)
 let Bset := (Icc b1 b2).filter (fun x => x % d = r)
 have hcard_cls : ∀ u v : ℕ, (((Icc u v).filter (fun x => x % d = r)).card : ℝ) <= (v + 1 - u : ℕ) / (d : ℝ) + 1 := by
   intro u v
   by_cases huv : v < u
   . have : Icc u v = ∅ := by
       ext x; simp only [mem_Icc, notMem_empty, iff_false]; omega
     rw [this]; simp; positivity
   . let K := (v + 1 - u) / d + 1
     have hinj : Set.InjOn (fun x => (x - u) / d) (((Icc u v).filter (fun x => x % d = r)) : Set ℕ) := by
       intro x hx y hy hxy;have hxm := mem_filter.mp (mem_coe.mp hx);have hym := mem_filter.mp (mem_coe.mp hy);have hxI := mem_Icc.mp hxm.1;have hyI := mem_Icc.mp hym.1;have hmx : x % d = y % d := hxm.2.trans hym.2.symm
       have hsub_mod : (x - u) % d = (y - u) % d := by
         have hmeq : x ≡ y [MOD d] := hmx;have h1 : x - u + u = x := Nat.sub_add_cancel hxI.1;have h2 : y - u + u = y := Nat.sub_add_cancel hyI.1;rw [<- h1, <- h2] at hmeq;exact Nat.ModEq.add_right_cancel' u hmeq
       have hdx := Nat.div_add_mod (x - u) d;have hdy := Nat.div_add_mod (y - u) d;have hxy' : (x - u) / d = (y - u) / d := hxy;rw [hxy', hsub_mod] at hdx;omega
     have hmaps : ∀ x ∈ ((Icc u v).filter (fun x => x % d = r)), (x - u) / d ∈ range K := by
       intro x hx;have hxI := mem_Icc.mp (mem_filter.mp hx).1;exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (by omega)))
     have hle := card_le_card_of_injOn (fun x => (x - u) / d) (fun x hx => mem_coe.mpr (hmaps x (mem_coe.mp hx))) hinj;rw [card_range] at hle;have hleR : (((Icc u v).filter (fun x => x % d = r)).card : ℝ) <= (K : ℝ) := by exact_mod_cast hle
     have hdiv : (((v + 1 - u) / d : ℕ) : ℝ) <= (v + 1 - u : ℕ) / (d : ℝ) := by
       have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
       rw [le_div_iff₀ hdpos];exact_mod_cast Nat.div_mul_le_self (v + 1 - u) d
     dsimp only [K] at hleR;push_cast at hleR;linarith
 have hmapsF : ∀ S ∈ F, (if h : S.Nonempty then (S.min' h, S.max' h) else (0, 0)) ∈ Aset ×ˢ Bset := by
   intro S hS;obtain ⟨hne, hmin, hmax⟩ := hend S hS;rw [dif_pos hne, mem_product];exact ⟨mem_filter.mpr ⟨hmin, hmod S hS _ (min'_mem S hne)⟩, mem_filter.mpr ⟨hmax, hmod S hS _ (max'_mem S hne)⟩⟩
 have hinjF : Set.InjOn (fun S => if h : S.Nonempty then (S.min' h, S.max' h) else (0, 0)) (F : Set (Finset ℕ)) := by
   intro S hS T hT heq;have hSF := mem_coe.mp hS;have hTF := mem_coe.mp hT;obtain ⟨hneS, -, -⟩ := hend S hSF;obtain ⟨hneT, -, -⟩ := hend T hTF;dsimp only at heq;rw [dif_pos hneS, dif_pos hneT] at heq;have hlo : S.min' hneS = T.min' hneT := congrArg Prod.fst heq;have hhi : S.max' hneS = T.max' hneT := congrArg Prod.snd heq
   ext x
   constructor
   . intro hx
     have h1 := min'_le S x hx;have h2 := le_max' S x hx;have h3 := (hmod S hSF x hx).trans (hmod T hTF (T.min' hneT) (min'_mem T hneT)).symm;exact (hstep T hTF).2.2 (T.min' hneT) (min'_mem T hneT) (T.max' hneT) (max'_mem T hneT) |>.2 x (by omega) (by omega) h3
   . intro hx
     have h1 := min'_le T x hx;have h2 := le_max' T x hx;have h3 := (hmod T hTF x hx).trans (hmod S hSF (S.min' hneS) (min'_mem S hneS)).symm;exact (hstep S hSF).2.2 (S.min' hneS) (min'_mem S hneS) (S.max' hneS) (max'_mem S hneS) |>.2 x (by omega) (by omega) h3
 have hFcard : F.card <= Aset.card * Bset.card := by
   have := card_le_card_of_injOn _ (fun S hS => mem_coe.mpr (hmapsF S (mem_coe.mp hS))) hinjF;rwa [card_product] at this
 have hFR : (F.card : ℝ) <= (Aset.card : ℝ) * (Bset.card : ℝ) := by exact_mod_cast hFcard
 exact le_trans hFR (mul_le_mul (hcard_cls a1 a2) (hcard_cls b1 b2) (Nat.cast_nonneg _) (by positivity))
lemma card_AP_fixed_step {N d : ℕ} (hd : 1 <= d) {F : Finset (Finset ℕ)} (hF : IsWellInter N F) (hstep : ∀ S ∈ F, 2 <= S.card /\ APSet S /\ ∀ x ∈ S, ∀ y ∈ S, x % d = y % d /\ (∀ z, min x y <= z -> z <= max x y -> z % d = x % d -> z ∈ S)) : (F.card : ℝ) <= ((N : ℝ) / (2 * d) + 1) ^ 2 := by
 rcases F.eq_empty_or_nonempty with rfl | hneF
 . simp; positivity
 have hneS : ∀ S ∈ F, S.Nonempty := fun S hS => card_pos.mp (by have := (hstep S hS).1; omega)
 let mins := F.attach.image (fun S => S.1.min' (hneS S.1 S.2))
 let maxs := F.attach.image (fun S => S.1.max' (hneS S.1 S.2))
 have hne_m : mins.Nonempty := by
   obtain ⟨S0, hS0⟩ := hneF;exact ⟨S0.min' (hneS S0 hS0), mem_image.mpr ⟨⟨S0, hS0⟩, mem_attach _ _, rfl⟩⟩
 set c := mins.max' hne_m
 have hc_mem : c ∈ mins := max'_mem _ hne_m;obtain ⟨⟨Sc, hSc⟩, -, hceq⟩ := mem_image.mp hc_mem
 have hcI : 1 <= c /\ c <= N := by
   rw [<- hceq];exact mem_Icc.mp (hF.1 Sc hSc (min'_mem Sc _))
 have hle_c : ∀ S (hS : S ∈ F), S.min' (hneS S hS) <= c := fun S hS =>
   le_max' mins _ (mem_image.mpr ⟨⟨S, hS⟩, mem_attach _ _, rfl⟩)
 have hc_le : ∀ S (hS : S ∈ F), c <= S.max' (hneS S hS) := by
   intro S hS
   by_cases hSSc : S = Sc
   . subst hSSc; rw [<- hceq]; exact min'_le _ _ (max'_mem _ _)
   . obtain ⟨w, hw⟩ := wellInter_meet hF hS hSc hSSc
     have h1 : c <= w := by rw [<- hceq]; exact min'_le Sc w (mem_of_mem_inter_right hw)
     have h2 : w <= S.max' (hneS S hS) := le_max' S w (mem_of_mem_inter_left hw);omega
 have hmod : ∀ S ∈ F, ∀ x ∈ S, x % d = c % d := by
   intro S hS x hx
   by_cases hSSc : S = Sc
   . subst hSSc; rw [<- hceq]
     exact ((hstep S hS).2.2 x hx (S.min' (hneS S hS)) (min'_mem _ _)).1
   . obtain ⟨w, hw⟩ := wellInter_meet hF hS hSc hSSc
     have h1 := ((hstep S hS).2.2 x hx w (mem_of_mem_inter_left hw)).1;have h2 := ((hstep Sc hSc).2.2 w (mem_of_mem_inter_right hw) (Sc.min' (hneS Sc hSc)) (min'_mem _ _)).1;rw [<- hceq]; exact h1.trans h2
 let Aset := (Icc 1 c).filter (fun x => x % d = c % d)
 let Bset := (Icc c N).filter (fun x => x % d = c % d)
 have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
 have hA : (Aset.card : ℝ) <= (c - 1 : ℕ) / (d : ℝ) + 1 := by
   have hinj : Set.InjOn (fun x => (c - x) / d) (Aset : Set ℕ) := by
     intro x hx y hy hxy;have hxm := mem_filter.mp (mem_coe.mp hx);have hym := mem_filter.mp (mem_coe.mp hy);have hxI := mem_Icc.mp hxm.1;have hyI := mem_Icc.mp hym.1;have hdx : d ∣ c - x := (Nat.modEq_iff_dvd' hxI.2).mp hxm.2;have hdy : d ∣ c - y := (Nat.modEq_iff_dvd' hyI.2).mp hym.2;have h1 : (c - x) / d * d = c - x := Nat.div_mul_cancel hdx;have h2 : (c - y) / d * d = c - y := Nat.div_mul_cancel hdy;have hxy' : (c - x) / d = (c - y) / d := hxy;rw [hxy'] at h1;omega
   have hmaps : ∀ x ∈ Aset, (c - x) / d ∈ range ((c - 1) / d + 1) := by
     intro x hx;have hxI := mem_Icc.mp (mem_filter.mp hx).1;exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (by omega)))
   have hle := card_le_card_of_injOn (fun x => (c - x) / d) (fun x hx => mem_coe.mpr (hmaps x (mem_coe.mp hx))) hinj;rw [card_range] at hle;have hleR : (Aset.card : ℝ) <= ((c - 1) / d : ℕ) + 1 := by exact_mod_cast hle
   have hdiv : (((c - 1) / d : ℕ) : ℝ) <= (c - 1 : ℕ) / (d : ℝ) := by rw [le_div_iff₀ hdpos]; exact_mod_cast Nat.div_mul_le_self (c - 1) d
   linarith
 have hB : (Bset.card : ℝ) <= (N - c : ℕ) / (d : ℝ) + 1 := by
   have hinj : Set.InjOn (fun x => (x - c) / d) (Bset : Set ℕ) := by
     intro x hx y hy hxy;have hxm := mem_filter.mp (mem_coe.mp hx);have hym := mem_filter.mp (mem_coe.mp hy);have hxI := mem_Icc.mp hxm.1;have hyI := mem_Icc.mp hym.1;have hdx : d ∣ x - c := (Nat.modEq_iff_dvd' hxI.1).mp hxm.2.symm;have hdy : d ∣ y - c := (Nat.modEq_iff_dvd' hyI.1).mp hym.2.symm;have h1 : (x - c) / d * d = x - c := Nat.div_mul_cancel hdx;have h2 : (y - c) / d * d = y - c := Nat.div_mul_cancel hdy;have hxy' : (x - c) / d = (y - c) / d := hxy;rw [hxy'] at h1;omega
   have hmaps : ∀ x ∈ Bset, (x - c) / d ∈ range ((N - c) / d + 1) := by
     intro x hx;have hxI := mem_Icc.mp (mem_filter.mp hx).1;exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (by omega)))
   have hle := card_le_card_of_injOn (fun x => (x - c) / d) (fun x hx => mem_coe.mpr (hmaps x (mem_coe.mp hx))) hinj;rw [card_range] at hle;have hleR : (Bset.card : ℝ) <= ((N - c) / d : ℕ) + 1 := by exact_mod_cast hle
   have hdiv : (((N - c) / d : ℕ) : ℝ) <= (N - c : ℕ) / (d : ℝ) := by rw [le_div_iff₀ hdpos]; exact_mod_cast Nat.div_mul_le_self (N - c) d
   linarith
 have hmapsF : ∀ S ∈ F, (if h : S.Nonempty then (S.min' h, S.max' h) else (0, 0)) ∈ Aset ×ˢ Bset := by
   intro S hS;have hne := hneS S hS;rw [dif_pos hne, mem_product];exact ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨(mem_Icc.mp (hF.1 S hS (min'_mem S hne))).1, hle_c S hS⟩, hmod S hS _ (min'_mem S hne)⟩, mem_filter.mpr ⟨mem_Icc.mpr ⟨hc_le S hS, (mem_Icc.mp (hF.1 S hS (max'_mem S hne))).2⟩, hmod S hS _ (max'_mem S hne)⟩⟩
 have hinjF : Set.InjOn (fun S => if h : S.Nonempty then (S.min' h, S.max' h) else (0, 0)) (F : Set (Finset ℕ)) := by
   intro S hS T hT heq;have hSF := mem_coe.mp hS;have hTF := mem_coe.mp hT;have hneS' := hneS S hSF;have hneT' := hneS T hTF;dsimp only at heq;rw [dif_pos hneS', dif_pos hneT'] at heq;have hlo : S.min' hneS' = T.min' hneT' := congrArg Prod.fst heq;have hhi : S.max' hneS' = T.max' hneT' := congrArg Prod.snd heq
   ext x
   constructor
   . intro hx
     have h1 := min'_le S x hx;have h2 := le_max' S x hx;have h3 := (hmod S hSF x hx).trans (hmod T hTF (T.min' hneT') (min'_mem T hneT')).symm;exact (hstep T hTF).2.2 (T.min' hneT') (min'_mem T hneT') (T.max' hneT') (max'_mem T hneT') |>.2 x (by omega) (by omega) h3
   . intro hx
     have h1 := min'_le T x hx;have h2 := le_max' T x hx;have h3 := (hmod T hTF x hx).trans (hmod S hSF (S.min' hneS') (min'_mem S hneS')).symm;exact (hstep S hSF).2.2 (S.min' hneS') (min'_mem S hneS') (S.max' hneS') (max'_mem S hneS') |>.2 x (by omega) (by omega) h3
 have hFcard : F.card <= Aset.card * Bset.card := by
   have := card_le_card_of_injOn _ (fun S hS => mem_coe.mpr (hmapsF S (mem_coe.mp hS))) hinjF;rwa [card_product] at this
 have hFR : (F.card : ℝ) <= ((c - 1 : ℕ) / (d : ℝ) + 1) * ((N - c : ℕ) / (d : ℝ) + 1) := le_trans (by exact_mod_cast hFcard) (mul_le_mul hA hB (Nat.cast_nonneg _) (by positivity))
 have hsum : ((c - 1 : ℕ) : ℝ) + ((N - c : ℕ) : ℝ) <= (N : ℝ) := by
   have : (c - 1) + (N - c) <= N := by omega
   exact_mod_cast this
 have hamgm : (((c - 1 : ℕ) : ℝ) / d + 1) * (((N - c : ℕ) : ℝ) / d + 1) <= (((N : ℝ) / (2 * d) + 1)) ^ 2 := by
   set u := ((c - 1 : ℕ) : ℝ) / d + 1
   set v := ((N - c : ℕ) : ℝ) / d + 1
   have huv : u + v <= (N : ℝ) / d + 2 := by
     dsimp only [u, v];have hdiv := div_le_div_of_nonneg_right hsum (le_of_lt hdpos);rw [add_div] at hdiv; linarith
   have hsq : u * v <= ((u + v) / 2) ^ 2 := by nlinarith [sq_nonneg (u - v)]
   have havg : (u + v) / 2 <= (N : ℝ) / (2 * d) + 1 := by
     have : ((N : ℝ) / d + 2) / 2 = (N : ℝ) / (2 * d) + 1 := by ring
     linarith
   have huv0 : 0 <= (u + v) / 2 := by dsimp only [u, v]; positivity
   nlinarith
 exact le_trans hFR hamgm
lemma card_AP_all {N : ℕ} (hN : 2 <= N) {F FAP : Finset (Finset ℕ)} (hF : IsWellInter N F) (hFAP_sub : FAP ⊆ F) (hFAP : ∀ S ∈ FAP, 3 <= S.card /\ APSet S) : (FAP.card : ℝ) <= (61 / 144 : ℝ) * (N : ℝ) ^ 2 + (N : ℝ) * Real.log N + 2 * N := by
 have hstep_ex : ∀ S : {S // S ∈ FAP}, ∃ d : ℕ, 1 <= d /\ d <= N / 2 /\ ∀ x ∈ S.1, ∀ y ∈ S.1, x % d = y % d /\ (∀ z, min x y <= z -> z <= max x y -> z % d = x % d -> z ∈ S.1) := by
   rintro ⟨S, hS⟩;have hSF : S ∈ F := hFAP_sub hS;obtain ⟨h3, hAP⟩ := hFAP S hS;obtain ⟨d, hd, hab, -, hmem, hcard_d⟩ := apSet_canonical hAP (by omega);have hne : S.Nonempty := card_pos.mp (by omega);have hmin1 := (mem_Icc.mp (hF.1 S hSF (min'_mem S hne))).1;have hmaxN := (mem_Icc.mp (hF.1 S hSF (max'_mem S hne))).2
   have hd_le : d <= N / 2 := by
     have h2d : 2 * d <= (S.card - 1) * d := Nat.mul_le_mul_right d (by omega);have hba : S.max' hne - S.min' hne <= N := by omega
     omega
   refine ⟨d, hd, hd_le, fun x hx y hy => ?_⟩
   have hxm := (hmem x).mp hx;have hym := (hmem y).mp hy
   refine ⟨hxm.2.2.trans hym.2.2.symm, fun z hz1 hz2 hzm => (hmem z).mpr ?_⟩
   exact ⟨by omega, by omega, hzm.trans hxm.2.2⟩
 choose dS' hdS' using hstep_ex
 classical
 let dS : Finset ℕ -> ℕ := fun S => if h : S ∈ FAP then dS' ⟨S, h⟩ else 0
 have hdS : ∀ S (hS : S ∈ FAP), 1 <= dS S /\ dS S <= N / 2 /\ ∀ x ∈ S, ∀ y ∈ S, x % dS S = y % dS S /\ (∀ z, min x y <= z -> z <= max x y -> z % dS S = x % dS S -> z ∈ S) := by
   intro S hS
   simpa [dS, dif_pos hS] using hdS' ⟨S, hS⟩
 have hcov : FAP ⊆ (Icc 1 (N / 2)).biUnion (fun d => FAP.filter (fun S => dS S = d)) := by
   intro S hS;obtain ⟨h1, h2, -⟩ := hdS S hS;exact mem_biUnion.mpr ⟨dS S, mem_Icc.mpr ⟨h1, h2⟩, mem_filter.mpr ⟨hS, rfl⟩⟩
 have hcard_le : (FAP.card : ℝ) <= ∑ d ∈ Icc 1 (N / 2), ((FAP.filter (fun S => dS S = d)).card : ℝ) := by exact_mod_cast le_trans (card_le_card hcov) card_biUnion_le
 have hterm : ∀ d ∈ Icc 1 (N / 2), ((FAP.filter (fun S => dS S = d)).card : ℝ) <= ((N : ℝ) / (2 * d) + 1) ^ 2 := by
   intro d hd;have hd1 : 1 <= d := (mem_Icc.mp hd).1
   refine card_AP_fixed_step hd1 (isWellInter_subset hF (fun S hS =>
     hFAP_sub (mem_filter.mp hS).1)) ?_
   intro S hS;obtain ⟨hSFAP, hdeq⟩ := mem_filter.mp hS;obtain ⟨h3, hAP⟩ := hFAP S hSFAP
   refine ⟨by omega, hAP, ?_⟩
   rw [<- hdeq];exact (hdS S hSFAP).2.2
 have hsum1 : (FAP.card : ℝ) <= ∑ d ∈ Icc 1 (N / 2), ((N : ℝ) / (2 * d) + 1) ^ 2 := le_trans hcard_le (sum_le_sum hterm)
 have hexpand : ∑ d ∈ Icc 1 (N / 2), ((N : ℝ) / (2 * d) + 1) ^ 2 = ((N : ℝ) ^ 2 / 4) * (∑ d ∈ Icc 1 (N / 2), (1 : ℝ) / (d : ℝ) ^ 2) + (N : ℝ) * (∑ d ∈ Icc 1 (N / 2), (1 : ℝ) / (d : ℝ)) + ((Icc 1 (N / 2)).card : ℝ) := by
   rw [mul_sum, mul_sum, <- sum_add_distrib];have hc : ((Icc 1 (N / 2)).card : ℝ) = ∑ _d ∈ Icc 1 (N / 2), (1 : ℝ) := by simp
   rw [hc, <- sum_add_distrib];apply sum_congr rfl;intro d hd;have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (by have := (mem_Icc.mp hd).1; omega : d ≠ 0)
   field_simp; ring
 rw [hexpand] at hsum1;have h1 := sum_inv_sq_le_61_36 (N / 2);have hN2pos : 1 <= N / 2 := by omega
 have h2 := harmonic_le_one_add_log (N / 2) hN2pos
 have hlog : Real.log ((N / 2 : ℕ) : ℝ) <= Real.log (N : ℝ) := by
   apply Real.log_le_log (by exact_mod_cast hN2pos);exact_mod_cast Nat.div_le_self N 2
 have h3 : ((Icc 1 (N / 2)).card : ℝ) <= (N : ℝ) := by rw [Nat.card_Icc]; exact_mod_cast (by omega : N / 2 + 1 - 1 <= N)
 have hN0 : (0 : ℝ) <= (N : ℝ) := Nat.cast_nonneg N
 have h1' : ((N : ℝ) ^ 2 / 4) * (∑ d ∈ Icc 1 (N / 2), (1 : ℝ) / (d : ℝ) ^ 2) <= (61 / 144 : ℝ) * (N : ℝ) ^ 2 := by
   have := mul_le_mul_of_nonneg_left h1 (show (0 : ℝ) <= (N : ℝ) ^ 2 / 4 by positivity);linarith
 have h2' : (N : ℝ) * (∑ d ∈ Icc 1 (N / 2), (1 : ℝ) / (d : ℝ)) <= (N : ℝ) * (1 + Real.log (N : ℝ)) := by exact mul_le_mul_of_nonneg_left (le_trans h2 (by linarith)) hN0
 linarith
lemma card_divisors_pow_four_le {m : ℕ} (hm : 1 <= m) : m.divisors.card ^ 4 <= 19680 * m := by
 have hm0 : m ≠ 0 := by omega
 rw [Nat.card_divisors hm0];have hfac_eq : m = ∏ p ∈ m.primeFactors, p ^ (m.factorization p) := (Nat.prod_factorization_pow_eq_self hm0).symm
 have hge16 : ∀ p e : ℕ, 16 <= p -> (e + 1) ^ 4 <= p ^ e := by
   intro p e hp
   refine le_trans ?_ (Nat.pow_le_pow_left hp e)
   induction e with
   | zero => norm_num
   | succ k ih =>
     have h1 : (k + 1 + 1) <= 2 * (k + 1) := by omega
     have h2 : (k + 1 + 1) ^ 4 <= (2 * (k + 1)) ^ 4 := Nat.pow_le_pow_left h1 4;have h3 : (2 * (k + 1)) ^ 4 = 16 * (k + 1) ^ 4 := by ring
     calc (k + 1 + 1) ^ 4 <= 16 * (k + 1) ^ 4 := by omega
       _ <= 16 * 16 ^ k := Nat.mul_le_mul_left 16 ih
       _ = 16 ^ (k + 1) := by ring
 have h2 : ∀ e : ℕ, (e + 1) ^ 4 <= 41 * 2 ^ e := by
   intro e
   induction e with
   | zero => norm_num
   | succ k ih =>
     by_cases hk : k < 5
     . interval_cases k <;> norm_num
     . have h1 : (k + 2) ^ 4 <= 2 * (k + 1) ^ 4 := by
         have hk5 : (5 : ℤ) <= (k : ℤ) := by exact_mod_cast (by omega : 5 <= k)
         have hZ : ((k : ℤ) + 2) ^ 4 <= 2 * ((k : ℤ) + 1) ^ 4 := by
           have hk0 : (0 : ℤ) <= (k : ℤ) := by omega
           have hsq : 0 <= ((k : ℤ) - 5) * ((k : ℤ) ^ 3 + 5 * (k : ℤ) ^ 2 + 13 * (k : ℤ) + 41) := mul_nonneg (by linarith) (by positivity);linarith
         exact_mod_cast hZ
       calc (k + 1 + 1) ^ 4 <= 2 * (k + 1) ^ 4 := h1
         _ <= 2 * (41 * 2 ^ k) := Nat.mul_le_mul_left 2 ih
         _ = 41 * 2 ^ (k + 1) := by ring
 have h3 : ∀ e : ℕ, (e + 1) ^ 4 <= 10 * 3 ^ e := by
   intro e
   induction e with
   | zero => norm_num
   | succ k ih =>
     by_cases hk : k < 3
     . interval_cases k <;> norm_num
     . have h1 : (k + 2) ^ 4 <= 3 * (k + 1) ^ 4 := by
         have hk3 : (3 : ℤ) <= (k : ℤ) := by exact_mod_cast (by omega : 3 <= k)
         have hZ : ((k : ℤ) + 2) ^ 4 <= 3 * ((k : ℤ) + 1) ^ 4 := by
           have hk0 : (0 : ℤ) <= (k : ℤ) := by omega
           have hsq : 0 <= ((k : ℤ) - 3) * (2 * (k : ℤ) ^ 3 + 10 * (k : ℤ) ^ 2 + 24 * (k : ℤ) + 52) := mul_nonneg (by linarith) (by positivity);linarith
         exact_mod_cast hZ
       calc (k + 1 + 1) ^ 4 <= 3 * (k + 1) ^ 4 := h1
         _ <= 3 * (10 * 3 ^ k) := Nat.mul_le_mul_left 3 ih
         _ = 10 * 3 ^ (k + 1) := by ring
 have h5 : ∀ e : ℕ, (e + 1) ^ 4 <= 4 * 5 ^ e := by
   intro e
   induction e with
   | zero => norm_num
   | succ k ih =>
     by_cases hk : k < 2
     . interval_cases k <;> norm_num
     . have h1 : (k + 2) ^ 4 <= 5 * (k + 1) ^ 4 := by
         have hk2 : 2 <= k := by omega
         nlinarith [sq_nonneg k]
       calc (k + 1 + 1) ^ 4 <= 5 * (k + 1) ^ 4 := h1
         _ <= 5 * (4 * 5 ^ k) := Nat.mul_le_mul_left 5 ih
         _ = 4 * 5 ^ (k + 1) := by ring
 have h7 : ∀ e : ℕ, (e + 1) ^ 4 <= 3 * 7 ^ e := by
   intro e
   induction e with
   | zero => norm_num
   | succ k ih =>
     by_cases hk : k < 1
     . interval_cases k; norm_num
     . have h1 : (k + 2) ^ 4 <= 7 * (k + 1) ^ 4 := by
         have hk1 : 1 <= k := by omega
         nlinarith [sq_nonneg k]
       calc (k + 1 + 1) ^ 4 <= 7 * (k + 1) ^ 4 := h1
         _ <= 7 * (3 * 7 ^ k) := Nat.mul_le_mul_left 7 ih
         _ = 3 * 7 ^ (k + 1) := by ring
 have h11 : ∀ e : ℕ, (e + 1) ^ 4 <= 2 * 11 ^ e := by
   intro e
   induction e with
   | zero => norm_num
   | succ k ih =>
     by_cases hk : k < 1
     . interval_cases k; norm_num
     . have h1 : (k + 2) ^ 4 <= 11 * (k + 1) ^ 4 := by
         have hk1 : 1 <= k := by omega
         nlinarith [sq_nonneg k]
       calc (k + 1 + 1) ^ 4 <= 11 * (k + 1) ^ 4 := h1
         _ <= 11 * (2 * 11 ^ k) := Nat.mul_le_mul_left 11 ih
         _ = 2 * 11 ^ (k + 1) := by ring
 have h13 : ∀ e : ℕ, (e + 1) ^ 4 <= 2 * 13 ^ e := by
   intro e
   induction e with
   | zero => norm_num
   | succ k ih =>
     by_cases hk : k < 1
     . interval_cases k; norm_num
     . have h1 : (k + 2) ^ 4 <= 13 * (k + 1) ^ 4 := by
         have hk1 : 1 <= k := by omega
         nlinarith [sq_nonneg k]
       calc (k + 1 + 1) ^ 4 <= 13 * (k + 1) ^ 4 := h1
         _ <= 13 * (2 * 13 ^ k) := Nat.mul_le_mul_left 13 ih
         _ = 2 * 13 ^ (k + 1) := by ring
 let C : ℕ -> ℕ := fun p =>
   if p = 2 then 41 else if p = 3 then 10 else if p = 5 then 4
   else if p = 7 then 3 else if p = 11 then 2 else if p = 13 then 2 else 1
 have hterm : ∀ p ∈ m.primeFactors, (m.factorization p + 1) ^ 4 <= C p * p ^ (m.factorization p) := by
   intro p hp;have hpr : p.Prime := Nat.prime_of_mem_primeFactors hp
   by_cases hp16 : 16 <= p
   . have hC : C p = 1 := by
       dsimp only [C]; split_ifs <;> omega
     rw [hC, one_mul]; exact hge16 p _ hp16
   . have hlt : p < 16 := by omega
     interval_cases p
     . exact absurd hpr (by decide)
     . exact absurd hpr (by decide)
     . simpa [C] using h2 (m.factorization 2)
     . simpa [C] using h3 (m.factorization 3)
     . exact absurd hpr (by decide)
     . simpa [C] using h5 (m.factorization 5)
     . exact absurd hpr (by decide)
     . simpa [C] using h7 (m.factorization 7)
     . exact absurd hpr (by decide)
     . exact absurd hpr (by decide)
     . exact absurd hpr (by decide)
     . simpa [C] using h11 (m.factorization 11)
     . exact absurd hpr (by decide)
     . simpa [C] using h13 (m.factorization 13)
     . exact absurd hpr (by decide)
     . exact absurd hpr (by decide)
 have hprod : (∏ p ∈ m.primeFactors, (m.factorization p + 1)) ^ 4 <= (∏ p ∈ m.primeFactors, C p) * (∏ p ∈ m.primeFactors, p ^ (m.factorization p)) := by
   rw [<- prod_pow, <- prod_mul_distrib];exact prod_le_prod' hterm
 rw [<- hfac_eq] at hprod
 have hCprod : ∏ p ∈ m.primeFactors, C p <= 19680 := by
   let Ssmall : Finset ℕ := {2, 3, 5, 7, 11, 13}
   have h1 : ∏ p ∈ m.primeFactors, C p = ∏ p ∈ m.primeFactors ∩ Ssmall, C p := by
     symm
     refine prod_subset Finset.inter_subset_left ?_
     intro p hp hnot;have hpS : p ∉ Ssmall := fun h => hnot (mem_inter.mpr ⟨hp, h⟩)
     dsimp only [Ssmall] at hpS;dsimp only [C];simp only [mem_insert, mem_singleton, not_or] at hpS;simp [hpS]
   rw [h1]
   have h2 : ∏ p ∈ m.primeFactors ∩ Ssmall, C p <= ∏ p ∈ Ssmall, C p := prod_le_prod_of_subset_of_one_le' Finset.inter_subset_right (fun p _ _ => by
       dsimp only [C]; split_ifs <;> omega)
   exact le_trans h2 (by decide)
 exact le_trans hprod (Nat.mul_le_mul_right m hCprod)
lemma card_divisors_sq_le_sqrt {m : ℕ} (hm : 1 <= m) : ((m.divisors.card : ℝ) ^ 2) <= 141 * Real.sqrt (m : ℝ) := by
 have h4 : ((m.divisors.card : ℝ) ^ 4) <= 19680 * (m : ℝ) := by exact_mod_cast card_divisors_pow_four_le hm
 have hsq : ((m.divisors.card : ℝ) ^ 2) ^ 2 <= (141 * Real.sqrt (m : ℝ)) ^ 2 := by
   rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg m)];have h1 : ((m.divisors.card : ℝ) ^ 2) ^ 2 = (m.divisors.card : ℝ) ^ 4 := by ring
   rw [h1]; nlinarith [Nat.cast_nonneg (α := ℝ) m]
 have hnn : 0 <= 141 * Real.sqrt (m : ℝ) := by positivity
 nlinarith [sq_nonneg ((m.divisors.card : ℝ) ^ 2 - 141 * Real.sqrt (m : ℝ))]
lemma primorial_le_four_pow : ∀ k : ℕ, ∏ p ∈ (Icc 1 k).filter Nat.Prime, p <= 4 ^ k := by
 intro k
 induction k using Nat.strong_induction_on with
 | _ k ih =>
   by_cases hk2 : k <= 2
   . interval_cases k <;> decide
   . rcases Nat.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
     . have h2m : 2 * m = m + m := by ring
       have hm0 : 1 <= m := by omega
       have hnotp : ¬ Nat.Prime (m + m) := by
         intro hp;have h2dvd : 2 ∣ m + m := ⟨m, by omega⟩
         rcases hp.eq_one_or_self_of_dvd 2 h2dvd with h | h <;> omega
       have heq : (Icc 1 (m + m)).filter Nat.Prime = (Icc 1 (m + m - 1)).filter Nat.Prime := by
         ext p
         simp only [mem_filter, mem_Icc]
         constructor
         . rintro ⟨⟨h1, h2⟩, hp⟩
           have hne : p ≠ m + m := fun h => hnotp (h ▸ hp)
           exact ⟨⟨h1, by omega⟩, hp⟩
         . rintro ⟨⟨h1, h2⟩, hp⟩
           exact ⟨⟨h1, by omega⟩, hp⟩
       rw [heq]
       calc ∏ p ∈ (Icc 1 (m + m - 1)).filter Nat.Prime, p
           <= 4 ^ (m + m - 1) := ih (m + m - 1) (by omega)
         _ <= 4 ^ (m + m) := Nat.pow_le_pow_right (by norm_num) (by omega)
     . have hm1 : 1 <= m := by omega
       let S1 := (Icc 1 (m + 1)).filter Nat.Prime
       let S2 := (Icc (m + 2) (2 * m + 1)).filter Nat.Prime
       have hunion : (Icc 1 (2 * m + 1)).filter Nat.Prime = S1 ∪ S2 := by
         ext p
         simp only [S1, S2, mem_union, mem_filter, mem_Icc]
         constructor
         . rintro ⟨⟨h1, h2⟩, hp⟩
           by_cases hpm : p <= m + 1
           . left; exact ⟨⟨h1, hpm⟩, hp⟩
           . right; exact ⟨⟨by omega, h2⟩, hp⟩
         . rintro (⟨⟨h1, h2⟩, hp⟩ | ⟨⟨h1, h2⟩, hp⟩) <;> exact ⟨⟨by omega, by omega⟩, hp⟩
       have hdisj : Disjoint S1 S2 := by
         rw [Finset.disjoint_left];intro p h1 h2;have := (mem_Icc.mp (mem_filter.mp h1).1).2;have := (mem_Icc.mp (mem_filter.mp h2).1).1;omega
       rw [hunion, prod_union hdisj];have hS1 : ∏ p ∈ S1, p <= 4 ^ (m + 1) := ih (m + 1) (by omega)
       have hS2_dvd : (∏ p ∈ S2, p) ∣ Nat.choose (2 * m + 1) m := by
         refine prod_primes_dvd _ (fun p hp => (mem_filter.mp hp).2.prime) ?_
         intro p hp;obtain ⟨hpI, hpr⟩ := mem_filter.mp hp;obtain ⟨hpm1, hpm2⟩ := mem_Icc.mp hpI;have hfact := Nat.choose_mul_factorial_mul_factorial (show m <= 2 * m + 1 by omega);have hsub : 2 * m + 1 - m = m + 1 := by omega
         rw [hsub] at hfact;have hdvd_top : p ∣ Nat.factorial (2 * m + 1) := hpr.dvd_factorial.mpr hpm2;rw [<- hfact] at hdvd_top
         have hndvd1 : ¬ p ∣ Nat.factorial m := fun h => by
           have := hpr.dvd_factorial.mp h; omega
         have hndvd2 : ¬ p ∣ Nat.factorial (m + 1) := fun h => by
           have := hpr.dvd_factorial.mp h; omega
         rcases hpr.dvd_mul.mp hdvd_top with h1 | h2
         . rcases hpr.dvd_mul.mp h1 with h3 | h4
           . exact h3
           . exact absurd h4 hndvd1
         . exact absurd h2 hndvd2
       have hchoose_pos : 0 < Nat.choose (2 * m + 1) m := Nat.choose_pos (by omega);have hS2_le : ∏ p ∈ S2, p <= Nat.choose (2 * m + 1) m := Nat.le_of_dvd hchoose_pos hS2_dvd
       have hchoose_le : Nat.choose (2 * m + 1) m <= 4 ^ m := by
         have hsym : Nat.choose (2 * m + 1) m = Nat.choose (2 * m + 1) (m + 1) := by
           have := Nat.choose_symm (show m <= 2 * m + 1 by omega);have hsub : 2 * m + 1 - m = m + 1 := by omega
           rw [hsub] at this; exact this.symm
         have hsum := Nat.sum_range_choose (2 * m + 1)
         have hpair : Nat.choose (2 * m + 1) m + Nat.choose (2 * m + 1) (m + 1) <= ∑ i ∈ range (2 * m + 1 + 1), Nat.choose (2 * m + 1) i := by
           have hsub2 : ({m, m + 1} : Finset ℕ) ⊆ range (2 * m + 1 + 1) := by
             intro x hx;simp only [mem_insert, mem_singleton] at hx;rw [mem_range]; omega
           have hle := sum_le_sum_of_subset hsub2 (f := fun i => Nat.choose (2 * m + 1) i);rw [sum_pair (by omega)] at hle;exact hle
         rw [hsum, <- hsym] at hpair;have hpow : 2 ^ (2 * m + 1) = 2 * 4 ^ m := by rw [pow_succ, pow_mul]; ring
         omega
       calc (∏ p ∈ S1, p) * (∏ p ∈ S2, p)
           <= 4 ^ (m + 1) * 4 ^ m := Nat.mul_le_mul hS1 (le_trans hS2_le hchoose_le)
         _ = 4 ^ (2 * m + 1) := by rw [<- pow_add]; congr 1; omega
lemma totient_div_ge_inv_card_primeFactors {Q : ℕ} (hQ : 1 <= Q) : (1 : ℝ) / (Q.primeFactors.card + 1 : ℕ) <= (Q.totient : ℝ) / (Q : ℝ) := by
 have hQ0 : (Q : ℝ) ≠ 0 := by exact_mod_cast (by omega : Q ≠ 0)
 have htot_R : (Q.totient : ℝ) = (Q : ℝ) * ∏ p ∈ Q.primeFactors, (1 - (p : ℝ)⁻¹) := by
   have hq := Nat.totient_eq_mul_prod_factors Q;have hR := congrArg (Rat.cast (K := ℝ)) hq
   simpa [Rat.cast_prod, Rat.cast_sub, Rat.cast_inv] using hR
 rw [htot_R, mul_div_cancel_left₀ _ hQ0]
 let ps := Q.primeFactors.sort (· <= ·)
 have hlen : ps.length = Q.primeFactors.card := length_sort _;have hnodup : ps.Nodup := Q.primeFactors.sort_nodup (· <= ·);have hsorted : ps.Pairwise (· < ·) := ((Q.primeFactors.pairwise_sort (· <= ·)).and hnodup).imp (fun h => lt_of_le_of_ne h.1 h.2)
 have hmem : ∀ p ∈ ps, p.Prime := fun p hp =>
   Nat.prime_of_mem_primeFactors ((mem_sort (· <= ·)).mp hp)
 have hprod_eq : ∏ p ∈ Q.primeFactors, (1 - (p : ℝ)⁻¹) = (ps.map (fun p : ℕ => (1 : ℝ) - (p : ℝ)⁻¹)).prod := by
   have htf : ps.toFinset = Q.primeFactors := by
     ext x; simp [ps]
   rw [<- htf, List.prod_toFinset _ hnodup]
 rw [hprod_eq, <- hlen]
 have hgen : ∀ (l : List ℕ) (a : ℕ), 2 <= a -> l.Pairwise (· < ·) -> (∀ x ∈ l, a <= x) -> ((a - 1 : ℕ) : ℝ) / ((a - 1 + l.length : ℕ) : ℝ) <= (l.map (fun p : ℕ => (1 : ℝ) - (p : ℝ)⁻¹)).prod := by
   intro l
   induction l with
   | nil =>
     intro a ha _ _;simp only [List.length_nil, add_zero, List.map_nil, List.prod_nil];have ha1 : ((a - 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : a - 1 ≠ 0)
     rw [div_self ha1]
   | cons x xs ih =>
     intro a ha hsort hge;have hax : a <= x := hge x List.mem_cons_self;have hxs_sort : xs.Pairwise (· < ·) := (List.pairwise_cons.mp hsort).2
     have hxs_ge : ∀ y ∈ xs, a + 1 <= y := fun y hy => by
       have hxy : x < y := (List.pairwise_cons.mp hsort).1 y hy;omega
     have hih := ih (a + 1) (by omega) hxs_sort hxs_ge;simp only [List.map_cons, List.prod_cons, List.length_cons]
     have h1x : (1 : ℝ) - (a : ℝ)⁻¹ <= 1 - (x : ℝ)⁻¹ := by
       have hapos : (0 : ℝ) < (a : ℝ) := by exact_mod_cast (by omega : 0 < a)
       have hle : (a : ℝ) <= (x : ℝ) := by exact_mod_cast hax
       have := inv_anti₀ hapos hle;linarith
     have h1a_eq : (1 : ℝ) - (a : ℝ)⁻¹ = ((a - 1 : ℕ) : ℝ) / (a : ℝ) := by
       have hapos : (a : ℝ) ≠ 0 := by exact_mod_cast (by omega : a ≠ 0)
       rw [Nat.cast_sub (by omega)]; field_simp; ring
     have hih_nn : 0 <= (xs.map (fun p : ℕ => (1 : ℝ) - (p : ℝ)⁻¹)).prod := by
       apply List.prod_nonneg;intro r hr;obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hr;have hy1 : (1 : ℝ) <= (y : ℝ) := by exact_mod_cast (by have := hxs_ge y hy; omega : 1 <= y)
       have : (y : ℝ)⁻¹ <= 1 := inv_le_one_of_one_le₀ hy1;linarith
     have hsub1 : a + 1 - 1 = a := by omega
     have hsub2 : a + xs.length = a - 1 + (xs.length + 1) := by omega
     rw [hsub1, hsub2] at hih
     have hmul : ((a - 1 : ℕ) : ℝ) / (a : ℝ) * ((a : ℝ) / ((a - 1 + (xs.length + 1) : ℕ) : ℝ)) <= (1 - (x : ℝ)⁻¹) * (xs.map (fun p : ℕ => (1 : ℝ) - (p : ℝ)⁻¹)).prod := by
       refine mul_le_mul (h1a_eq ▸ h1x) hih (by positivity) ?_
       have hx1 : (1 : ℝ) <= (x : ℝ) := by exact_mod_cast (by omega : 1 <= x)
       have : (x : ℝ)⁻¹ <= 1 := inv_le_one_of_one_le₀ hx1;linarith
     have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast (by omega : a ≠ 0)
     have hsimp : ((a - 1 : ℕ) : ℝ) / (a : ℝ) * ((a : ℝ) / ((a - 1 + (xs.length + 1) : ℕ) : ℝ)) = ((a - 1 : ℕ) : ℝ) / ((a - 1 + (xs.length + 1) : ℕ) : ℝ) := by field_simp
     linarith
 have hres := hgen ps 2 le_rfl hsorted (fun p hp => (hmem p hp).two_le);have h21 : (2 - 1 : ℕ) = 1 := rfl;have h22 : 2 - 1 + ps.length = ps.length + 1 := by omega
 simpa [h21, h22] using hres
lemma card_primeFactors_le_log2 {b : ℕ} (hb : 1 <= b) : b.primeFactors.card <= Nat.log 2 b := by
 have hpow : 2 ^ b.primeFactors.card <= b := by
   calc 2 ^ b.primeFactors.card
       = ∏ _p ∈ b.primeFactors, 2 := by simp
     _ <= ∏ p ∈ b.primeFactors, p := prod_le_prod' (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
     _ <= b := Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd b)
 exact (Nat.le_log_iff_pow_le (by norm_num) (by omega)).mpr hpow
lemma card_coprime_block {Q : ℕ} (hQ : 1 <= Q) (u : ℕ) : ((Ioc u (u + Q)).filter (fun q => Nat.Coprime q Q)).card = Q.totient := by
 rw [Nat.totient_eq_card_coprime]
 refine card_bij (fun q _ => q % Q) ?_ ?_ ?_
 . intro q hq
   obtain ⟨-, hcop⟩ := mem_filter.mp hq
   refine mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt q (by omega)), ?_⟩
   rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm, <- Nat.gcd_rec, Nat.gcd_comm];exact hcop.gcd_eq_one
 . intro q1 hq1 q2 hq2 hmod
   have h1 := mem_Ioc.mp (mem_filter.mp hq1).1;have h2 := mem_Ioc.mp (mem_filter.mp hq2).1;have hmod' : q1 % Q = q2 % Q := hmod;have hd1 := Nat.div_add_mod q1 Q;have hd2 := Nat.div_add_mod q2 Q
   have hqeq : q1 / Q = q2 / Q := by
     by_contra hne
     rcases lt_or_gt_of_ne hne with h | h
     . have : Q * (q1 / Q + 1) <= Q * (q2 / Q) := Nat.mul_le_mul_left Q h
       rw [mul_add, mul_one] at this; omega
     . have : Q * (q2 / Q + 1) <= Q * (q1 / Q) := Nat.mul_le_mul_left Q h
       rw [mul_add, mul_one] at this; omega
   rw [hqeq, hmod'] at hd1;omega
 . intro r hr
   obtain ⟨hrR, hcop⟩ := mem_filter.mp hr;have hrlt : r < Q := mem_range.mp hrR
   let q := u + 1 + ((r + Q - (u + 1) % Q) % Q)
   have hqI : q ∈ Ioc u (u + Q) := by
     refine mem_Ioc.mpr ⟨by omega, ?_⟩
     have hlt : (r + Q - (u + 1) % Q) % Q < Q := Nat.mod_lt _ (by omega);omega
   have hqmod : q % Q = r := by
     have h1 : (u + 1) % Q < Q := Nat.mod_lt _ (by omega);have h2 : (u + 1) % Q + (r + Q - (u + 1) % Q) = r + Q := by omega
     dsimp only [q];rw [Nat.add_mod (u + 1), Nat.mod_mod, Nat.add_mod_mod, h2, Nat.add_mod_right, Nat.mod_eq_of_lt hrlt]
   refine ⟨q, mem_filter.mpr ⟨hqI, ?_⟩, hqmod⟩
   rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm, Nat.gcd_rec, hqmod, Nat.gcd_comm];exact hcop.gcd_eq_one
lemma card_coprime_Ioc_bounds {Q : ℕ} (hQ : 1 <= Q) (U V : ℕ) (hUV : U <= V) : ((V - U) / Q) * Q.totient <= ((Ioc U V).filter (fun q => Nat.Coprime q Q)).card /\ ((Ioc U V).filter (fun q => Nat.Coprime q Q)).card <= ((V - U) / Q + 1) * Q.totient := by
 let k := (V - U) / Q
 have hk1 : U + k * Q <= V := by have := Nat.div_mul_le_self (V - U) Q; dsimp only [k]; omega
 have hk2 : V <= U + (k + 1) * Q := by
   have hlt : V - U < (k + 1) * Q := by
     have := Nat.lt_div_mul_add (a := V - U) (b := Q) (by omega);dsimp only [k]; rw [add_mul, one_mul]; exact this
   omega
 have hsum_blocks : ∀ m : ℕ, ((Ioc U (U + m * Q)).filter (fun q => Nat.Coprime q Q)).card = m * Q.totient := by
   intro m
   induction m with
   | zero => simp
   | succ j ih =>
     have hunion : Ioc U (U + (j + 1) * Q) = Ioc U (U + j * Q) ∪ Ioc (U + j * Q) (U + j * Q + Q) := by
       ext x; simp only [mem_Ioc, mem_union]
       have heq : U + (j + 1) * Q = U + j * Q + Q := by ring
       rw [heq]; omega
     have hdisj : Disjoint (Ioc U (U + j * Q)) (Ioc (U + j * Q) (U + j * Q + Q)) := by
       rw [Finset.disjoint_left];intro x h1 h2;have := (mem_Ioc.mp h1).2; have := (mem_Ioc.mp h2).1; omega
     rw [hunion, filter_union, card_union_of_disjoint (disjoint_filter_filter hdisj), ih, card_coprime_block hQ];ring
 constructor
 . rw [<- hsum_blocks k]
   exact card_le_card (filter_subset_filter _ (Finset.Ioc_subset_Ioc_right hk1))
 . rw [<- hsum_blocks (k + 1)]
   exact card_le_card (filter_subset_filter _ (Finset.Ioc_subset_Ioc_right hk2))
lemma card_coprime_div_p_le {Q p U V : ℕ} (hQ : 1 <= Q) (hp : p.Prime) (hUV : U <= V) : ((((Ioc U V).filter (fun q => Nat.Coprime q Q)).filter (fun q => p ∣ q)).card : ℝ) <= (((V - U : ℕ) : ℝ) / ((p : ℝ) * (Q : ℝ)) + 2) * (Q.totient : ℝ) := by
 let Sj := (Ioc U V).filter (fun q => Nat.Coprime q Q)
 have hppos : 0 < p := hp.pos
 have hmaps : ∀ q ∈ Sj.filter (fun q => p ∣ q), q / p ∈ (Ioc (U / p) (V / p)).filter (fun q' => Nat.Coprime q' Q) := by
   intro q hq;obtain ⟨hqSj, hpq⟩ := mem_filter.mp hq;obtain ⟨hqI, hcopQj⟩ := mem_filter.mp hqSj;obtain ⟨hUq, hqV⟩ := mem_Ioc.mp hqI;have hqp : p * (q / p) = q := Nat.mul_div_cancel' hpq
   refine mem_filter.mpr ⟨mem_Ioc.mpr ⟨?_, ?_⟩, ?_⟩
   . exact (Nat.div_lt_iff_lt_mul hppos).mpr (by rw [Nat.mul_comm]; omega)
   . exact Nat.div_le_div_right hqV
   . exact hcopQj.coprime_dvd_left (Nat.div_dvd_of_dvd hpq)
 have hinj : Set.InjOn (fun q => q / p) ((Sj.filter (fun q => p ∣ q)) : Set ℕ) := by
   intro q1 hq1 q2 hq2 heq;have hp1 := (mem_filter.mp (mem_coe.mp hq1)).2;have hp2 := (mem_filter.mp (mem_coe.mp hq2)).2;have h1 := Nat.mul_div_cancel' hp1;have h2 := Nat.mul_div_cancel' hp2;have heq' : q1 / p = q2 / p := heq;rw [<- h1, <- h2, heq']
 have hcard_le := card_le_card_of_injOn (fun q => q / p) (fun q hq => mem_coe.mpr (hmaps q (mem_coe.mp hq))) hinj;have hub := (card_coprime_Ioc_bounds hQ (U / p) (V / p) (Nat.div_le_div_right hUV)).2;have hleR : ((Sj.filter (fun q => p ∣ q)).card : ℝ) <= ((((V / p - U / p) / Q : ℕ) : ℝ) + 1) * (Q.totient : ℝ) := by exact_mod_cast le_trans hcard_le hub
 have hsub_le : V / p - U / p <= (V - U) / p + 1 := by
   have h1 := Nat.div_add_mod U p;have h2 := Nat.div_add_mod V p;have h4 : U % p < p := Nat.mod_lt U hppos;have h5 : V % p < p := Nat.mod_lt V hppos;have h7 : p * (V / p - U / p) <= (V - U) + p := by rw [Nat.mul_sub_left_distrib]; omega
   have h8 : V / p - U / p <= ((V - U) + p) / p := (Nat.le_div_iff_mul_le hppos).mpr (by rw [Nat.mul_comm]; exact h7);rwa [Nat.add_div_right (V - U) hppos] at h8
 have hpposR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hppos
 have hQposR : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast (by omega : 0 < Q)
 have hdiv1 : (((V / p - U / p) / Q : ℕ) : ℝ) <= (((V - U : ℕ) : ℝ) / (p : ℝ) + 1) / (Q : ℝ) := by
   calc (((V / p - U / p) / Q : ℕ) : ℝ)
       <= ((V / p - U / p : ℕ) : ℝ) / (Q : ℝ) := by rw [le_div_iff₀ hQposR]; exact_mod_cast Nat.div_mul_le_self _ _
     _ <= ((((V - U) / p + 1 : ℕ) : ℝ)) / (Q : ℝ) := div_le_div_of_nonneg_right (by exact_mod_cast hsub_le) (le_of_lt hQposR)
     _ <= (((V - U : ℕ) : ℝ) / (p : ℝ) + 1) / (Q : ℝ) := by
         apply div_le_div_of_nonneg_right _ (le_of_lt hQposR);push_cast;have : (((V - U) / p : ℕ) : ℝ) <= ((V - U : ℕ) : ℝ) / (p : ℝ) := by rw [le_div_iff₀ hpposR]; exact_mod_cast Nat.div_mul_le_self (V - U) p
         linarith
 have hQge1 : (1 : ℝ) / (Q : ℝ) <= 1 := by rw [div_le_one hQposR]; exact_mod_cast hQ
 have hcoeff : (((V / p - U / p) / Q : ℕ) : ℝ) + 1 <= ((V - U : ℕ) : ℝ) / ((p : ℝ) * (Q : ℝ)) + 2 := by
   have hrew : (((V - U : ℕ) : ℝ) / (p : ℝ) + 1) / (Q : ℝ) = ((V - U : ℕ) : ℝ) / ((p : ℝ) * (Q : ℝ)) + 1 / (Q : ℝ) := by field_simp
   linarith
 exact le_trans hleR (mul_le_mul_of_nonneg_right hcoeff (Nat.cast_nonneg _))
lemma card_coprime_Ioc_ge_eventually : ∀ᶠ N : ℕ in atTop, ∀ (b U V : ℕ), 1 <= b -> b <= N -> U < V -> N <= (V - U) ^ 6 -> ((V - U : ℕ) : ℝ) / (4 * ((Nat.log 2 N + 1 : ℕ) : ℝ)) <= (((Ioc U V).filter (fun q => Nat.Coprime q b)).card : ℝ) := by
 have hlog_ge : ∀ K : ℕ, ∀ᶠ N : ℕ in atTop, K <= Nat.log 2 N /\ 1 <= N := fun K =>
   Filter.eventually_atTop.mpr ⟨2 ^ K, fun N hN =>
     ⟨(Nat.le_log_iff_pow_le (by norm_num) (Nat.ne_of_gt (lt_of_lt_of_le (Nat.pow_pos (by norm_num)) hN))).mpr hN, le_trans (Nat.one_le_pow K 2 (by norm_num)) hN⟩⟩
 filter_upwards [hlog_ge (2 ^ 68)] with N hN b U V hb1 hbN hUV hW6
 set L := Nat.log 2 N
 have hN_pos : 0 < N := by omega
 have hL_ge68 : 2 ^ 68 <= L := hN.1
 have hL_ge : 4096 <= L := by
   have h4096 : (4096 : ℕ) = 2 ^ 12 := by norm_num
   rw [h4096];exact le_trans (Nat.pow_le_pow_right (by norm_num) (by norm_num : 12 <= 68)) hL_ge68
 have hN_le_pow : N < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by norm_num) N
 set W := V - U
 have hW_pos : 1 <= W := by omega
 have hL_small : 8 * (L + 1) <= 2 ^ (L / 24) := by
   have hlin : ∀ k : ℕ, 170 <= k -> 8 * (24 * k + 24) <= 2 ^ k := by
     intro k hk
     induction k with
     | zero => omega
     | succ j ih =>
       by_cases hj : j < 170
       . have hj169 : j = 169 := by omega
         subst hj169; norm_num
       . have hih := ih (by omega)
         have : 8 * (24 * (j + 1) + 24) <= 2 * (8 * (24 * j + 24)) := by omega
         calc 8 * (24 * (j + 1) + 24) <= 2 * (8 * (24 * j + 24)) := this
           _ <= 2 * 2 ^ j := Nat.mul_le_mul_left 2 hih
           _ = 2 ^ (j + 1) := by ring
   have hdiv : 170 <= L / 24 := by omega
   have h1 := hlin (L / 24) hdiv;have h2 : L + 1 <= 24 * (L / 24) + 24 := by omega
   omega
 have hW_pow : 2 ^ (L / 6) <= W := by
   by_contra hlt;push Not at hlt;have h1 : W ^ 6 < (2 ^ (L / 6)) ^ 6 := Nat.pow_lt_pow_left hlt (by norm_num);have h2 : (2 ^ (L / 6)) ^ 6 = 2 ^ (6 * (L / 6)) := by rw [<- pow_mul, mul_comm]
   have h3 : 2 ^ (6 * (L / 6)) <= 2 ^ L := Nat.pow_le_pow_right (by norm_num) (by omega);have h4 : 2 ^ L <= N := Nat.pow_log_le_self 2 (by omega);omega
 let ps := b.primeFactors.sort (· <= ·)
 let r := ps.length
 have hr_le : r <= L := by
   have h1 : r = b.primeFactors.card := length_sort _;rw [h1];exact le_trans (card_primeFactors_le_log2 hb1) (Nat.log_mono_right hbN)
 have hps_prime : ∀ i : Fin r, (ps.get i).Prime := fun i =>
   Nat.prime_of_mem_primeFactors ((mem_sort (· <= ·)).mp (List.get_mem ps i))
 have hps_nodup : ps.Nodup := b.primeFactors.sort_nodup (· <= ·);have hps_sorted : ps.Pairwise (· < ·) := ((b.primeFactors.pairwise_sort (· <= ·)).and hps_nodup).imp (fun h => lt_of_le_of_ne h.1 h.2)
 let Q : ℕ -> ℕ := fun j => (ps.take j).prod
 have hQ_pos : ∀ j, 1 <= Q j := by
   intro j;dsimp only [Q]
   have hpos : ∀ x ∈ ps.take j, 1 <= x := fun x hx =>
     (Nat.prime_of_mem_primeFactors ((mem_sort (· <= ·)).mp (List.mem_of_mem_take hx))).one_le
   exact Nat.one_le_iff_ne_zero.mpr (List.prod_ne_zero (fun h => by have := hpos 0 h; omega))
 have hQ_dvd : ∀ j, Q j ∣ b := by
   intro j;dsimp only [Q]
   have hsub : (ps.take j).toFinset ⊆ b.primeFactors := by
     intro p hp;exact (mem_sort (· <= ·)).mp (List.mem_of_mem_take (List.mem_toFinset.mp hp))
   have hnd : (ps.take j).Nodup := hps_nodup.take;have hpeq : (ps.take j).prod = ∏ p ∈ (ps.take j).toFinset, p := by simpa using (List.prod_toFinset (id : ℕ -> ℕ) hnd).symm
   rw [hpeq];exact dvd_trans (prod_dvd_prod_of_subset _ _ _ hsub) (Nat.prod_primeFactors_dvd b)
 have hQ_pf : ∀ j, (Q j).primeFactors.card <= L := fun j =>
   le_trans (card_primeFactors_le_log2 (hQ_pos j)) (Nat.log_mono_right (le_trans (Nat.le_of_dvd (by omega) (hQ_dvd j)) hbN))
 let T : ℕ := W / (8 * (L + 1))
 have hT_ge : 1 <= T := by
   have h1 : 8 * (L + 1) <= W := le_trans hL_small (le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) hW_pow);exact (Nat.one_le_div_iff (by omega)).mpr h1
 let goodJ := (range (r + 1)).filter (fun j => Q j <= T)
 have h0good : 0 ∈ goodJ := mem_filter.mpr ⟨mem_range.mpr (by omega), by
   dsimp only [Q]; simp; exact hT_ge⟩
 set j := goodJ.max' ⟨0, h0good⟩
 have hj_mem : j ∈ goodJ := max'_mem _ _;have hj_le_r : j <= r := Nat.lt_succ_iff.mp (mem_range.mp (mem_filter.mp hj_mem).1);have hQj_le : Q j <= T := (mem_filter.mp hj_mem).2;have hQj_mul : Q j * (8 * (L + 1)) <= W := le_trans (Nat.mul_le_mul_right _ hQj_le) (Nat.div_mul_le_self W (8 * (L + 1)))
 have htot_j : (1 : ℝ) / ((L + 1 : ℕ) : ℝ) <= ((Q j).totient : ℝ) / ((Q j : ℕ) : ℝ) := by
   refine le_trans ?_ (totient_div_ge_inv_card_primeFactors (hQ_pos j))
   apply one_div_le_one_div_of_le (by positivity);exact_mod_cast Nat.add_le_add_right (hQ_pf j) 1
 by_cases hjr : j = r
 . have hcop_eq : ∀ q, Nat.Coprime q b ↔ Nat.Coprime q (Q j) := by
     intro q
     constructor
     . intro h; exact h.coprime_dvd_right (hQ_dvd j)
     . intro h
       rw [Nat.coprime_iff_gcd_eq_one];by_contra hne;obtain ⟨p, hpr, hpdvd⟩ := Nat.exists_prime_and_dvd hne;have hpq : p ∣ q := dvd_trans hpdvd (Nat.gcd_dvd_left q b);have hpb : p ∣ b := dvd_trans hpdvd (Nat.gcd_dvd_right q b);have hpmem : p ∈ ps := (mem_sort (· <= ·)).mpr (Nat.mem_primeFactors.mpr ⟨hpr, hpb, by omega⟩)
       have hpQj : p ∣ Q j := by
         dsimp only [Q]; rw [hjr, List.take_length];exact List.dvd_prod hpmem
       exact hpr.not_dvd_one (h ▸ Nat.dvd_gcd hpq hpQj)
   have hfeq : (Ioc U V).filter (fun q => Nat.Coprime q b) = (Ioc U V).filter (fun q => Nat.Coprime q (Q j)) := by
     ext q; simp only [mem_filter, hcop_eq]
   rw [hfeq];have hlb := (card_coprime_Ioc_bounds (hQ_pos j) U V (by omega)).1;have hlbR : (((W / Q j : ℕ) : ℝ) * ((Q j).totient : ℝ)) <= (((Ioc U V).filter (fun q => Nat.Coprime q (Q j))).card : ℝ) := by exact_mod_cast hlb
   have hWQ : (W : ℝ) / (2 * (Q j : ℝ)) <= ((W / Q j : ℕ) : ℝ) := by
     have hQj_posR : (0 : ℝ) < (Q j : ℝ) := by exact_mod_cast hQ_pos j
     have h8 : 2 * Q j <= W := by nlinarith
     have hdiv_ge : (W : ℝ) / (Q j : ℝ) - 1 <= ((W / Q j : ℕ) : ℝ) := by
       have hlt : W < (W / Q j + 1) * Q j := by
         have := Nat.lt_div_mul_add (a := W) (b := Q j) (hQ_pos j);rw [add_mul, one_mul]; exact this
       have hltR : (W : ℝ) < (((W / Q j : ℕ) : ℝ) + 1) * (Q j : ℝ) := by exact_mod_cast hlt
       rw [sub_le_iff_le_add, div_le_iff₀ hQj_posR];linarith
     have hhalf : (1 : ℝ) <= (W : ℝ) / (2 * (Q j : ℝ)) := by
       rw [le_div_iff₀ (by positivity)];have : (2 * (Q j : ℝ)) <= (W : ℝ) := by exact_mod_cast h8
       linarith
     have h2eq : (W : ℝ) / (Q j : ℝ) = 2 * ((W : ℝ) / (2 * (Q j : ℝ))) := by ring
     linarith
   have hQj_posR : (0 : ℝ) < (Q j : ℝ) := by exact_mod_cast hQ_pos j
   have htot_mul : (Q j : ℝ) / ((L + 1 : ℕ) : ℝ) <= ((Q j).totient : ℝ) := by
     have := (le_div_iff₀ hQj_posR).mp htot_j;linarith [show (1 : ℝ) / ((L + 1 : ℕ) : ℝ) * (Q j : ℝ) = (Q j : ℝ) / ((L + 1 : ℕ) : ℝ) by ring]
   calc ((W : ℕ) : ℝ) / (4 * ((L + 1 : ℕ) : ℝ))
       <= ((W : ℕ) : ℝ) / (2 * ((L + 1 : ℕ) : ℝ)) := by
         apply div_le_div_of_nonneg_left (Nat.cast_nonneg W) (by positivity);linarith [show (0 : ℝ) < ((L + 1 : ℕ) : ℝ) by positivity]
     _ = ((W : ℝ) / (2 * (Q j : ℝ))) * ((Q j : ℝ) / ((L + 1 : ℕ) : ℝ)) := by field_simp
     _ <= ((W / Q j : ℕ) : ℝ) * ((Q j).totient : ℝ) := mul_le_mul hWQ htot_mul (by positivity) (by positivity)
     _ <= (((Ioc U V).filter (fun q => Nat.Coprime q (Q j))).card : ℝ) := hlbR
 . have hj_lt : j < r := by omega
   have hQj1_gt : T < Q (j + 1) := by
     by_contra hle;push Not at hle;have hmem : j + 1 ∈ goodJ := mem_filter.mpr ⟨mem_range.mpr (by omega), hle⟩;have := le_max' goodJ (j + 1) hmem;omega
   set P := ps.get ⟨j, hj_lt⟩
   have hP_prime : P.Prime := hps_prime ⟨j, hj_lt⟩
   have hQj1_le_prim : Q (j + 1) <= ∏ p ∈ (Icc 1 P).filter Nat.Prime, p := by
     dsimp only [Q];have hnd : (ps.take (j + 1)).Nodup := hps_nodup.take;have hpeq : (ps.take (j + 1)).prod = ∏ p ∈ (ps.take (j + 1)).toFinset, p := by simpa using (List.prod_toFinset (id : ℕ -> ℕ) hnd).symm
     rw [hpeq]
     refine prod_le_prod_of_subset_of_one_le' ?_ (fun p hp _ => (mem_filter.mp hp).2.one_le)
     intro p hp;have hpmem : p ∈ ps.take (j + 1) := List.mem_toFinset.mp hp;obtain ⟨idx, hidx_eq⟩ := List.mem_iff_get.mp hpmem
     have hidx_j : idx.1 <= j := by
       have hlen_le : (ps.take (j + 1)).length <= j + 1 := List.length_take_le _ _;have h1 := idx.2;omega
     have hp_eq : p = ps.get ⟨idx.1, by omega⟩ := by rw [<- hidx_eq]; simp [List.get_eq_getElem]
     have hp_le_P : p <= P := by
       rw [hp_eq]
       rcases Nat.eq_or_lt_of_le hidx_j with heq | hlt
       . have hfin : (⟨idx.1, by omega⟩ : Fin r) = ⟨j, hj_lt⟩ := Fin.ext heq
         rw [hfin]
       . exact le_of_lt (List.pairwise_iff_get.mp hps_sorted ⟨idx.1, by omega⟩ ⟨j, hj_lt⟩ hlt)
     have hpr := hps_prime ⟨idx.1, by omega⟩;rw [<- hp_eq] at hpr;exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hpr.one_le, hp_le_P⟩, hpr⟩
   have h4P_gt : T < 4 ^ P := lt_of_lt_of_le hQj1_gt (le_trans hQj1_le_prim (primorial_le_four_pow P))
   have hT_pow : 2 ^ (L / 8) <= T := by
     have h1 : 2 ^ (L / 8) * (8 * (L + 1)) <= 2 ^ (L / 8) * 2 ^ (L / 24) := Nat.mul_le_mul_left _ hL_small;have h2 : 2 ^ (L / 8) * 2 ^ (L / 24) = 2 ^ (L / 8 + L / 24) := (pow_add _ _ _).symm;have h3 : 2 ^ (L / 8 + L / 24) <= 2 ^ (L / 6) := Nat.pow_le_pow_right (by norm_num) (by omega);exact (Nat.le_div_iff_mul_le (by omega)).mpr (le_trans h1 (le_trans (h2 ▸ h3) hW_pow))
   have hP_ge : L / 16 <= P := by
     have h1 : 2 ^ (L / 8) < 2 ^ (2 * P) := by
       have h4 : 4 ^ P = 2 ^ (2 * P) := by rw [pow_mul]; norm_num
       omega
     have h2 : L / 8 < 2 * P := (Nat.pow_lt_pow_iff_right (by norm_num)).mp h1;omega
   have hP_ge64 : 2 ^ 64 <= P := by
     have h16 : 16 * 2 ^ 64 = 2 ^ 68 := by
       have : (16 : ℕ) = 2 ^ 4 := by norm_num
       rw [this, <- pow_add]
     omega
   set m := r - j
   have hPm_le : P ^ m <= N := by
     have hdrop_len : (ps.drop j).length = m := by simp [m, r]
     have hgeP : ∀ x ∈ ps.drop j, P <= x := by
       intro x hx;obtain ⟨idx, hidx_eq⟩ := List.mem_iff_get.mp hx;have hxj : x = ps.get ⟨j + idx.1, by have := idx.2; simp at this; omega⟩ := by rw [<- hidx_eq]; simp [List.get_eq_getElem]
       rw [hxj]
       rcases Nat.eq_zero_or_pos idx.1 with h0 | hpos
       . simp [h0]; rfl
       . exact le_of_lt (List.pairwise_iff_get.mp hps_sorted ⟨j, hj_lt⟩ ⟨j + idx.1, by have := idx.2; simp at this; omega⟩ (by simp; omega))
     have h1 : P ^ m <= (ps.drop j).prod := by
       rw [<- hdrop_len]
       have hpow_list : ∀ l : List ℕ, (∀ x ∈ l, P <= x) -> P ^ l.length <= l.prod := by
         intro l
         induction l with
         | nil => intro _; simp
         | cons x xs ih =>
           intro h;simp only [List.length_cons, pow_succ', List.prod_cons];exact Nat.mul_le_mul (h x List.mem_cons_self) (ih (fun y hy => h y (List.mem_cons_of_mem x hy)))
       exact hpow_list (ps.drop j) hgeP
     have hnd : (ps.drop j).Nodup := hps_nodup.drop
     have hsub : (ps.drop j).toFinset ⊆ b.primeFactors := by
       intro p hp;exact (mem_sort (· <= ·)).mp (List.mem_of_mem_drop (List.mem_toFinset.mp hp))
     have h2 : (ps.drop j).prod ∣ b := by
       have hpeq : (ps.drop j).prod = ∏ p ∈ (ps.drop j).toFinset, p := by simpa using (List.prod_toFinset (id : ℕ -> ℕ) hnd).symm
       rw [hpeq];exact dvd_trans (prod_dvd_prod_of_subset _ _ _ hsub) (Nat.prod_primeFactors_dvd b)
     exact le_trans h1 (le_trans (Nat.le_of_dvd (by omega) h2) hbN)
   have h4m_le_P : 4 * m <= P := by
     have hpow1 : 2 ^ (64 * m) <= N := by
       calc 2 ^ (64 * m) = (2 ^ 64) ^ m := by rw [pow_mul]
         _ <= P ^ m := Nat.pow_le_pow_left hP_ge64 m
         _ <= N := hPm_le
     have hlt : 2 ^ (64 * m) < 2 ^ (L + 1) := lt_of_le_of_lt hpow1 hN_le_pow
     have h64m : 64 * m <= L := by
       have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hlt;omega
     omega
   let Sj := (Ioc U V).filter (fun q => Nat.Coprime q (Q j))
   let remPrimes := (ps.drop j).toFinset
   have hrem_card : remPrimes.card = m := by
     rw [List.toFinset_card_of_nodup hps_nodup.drop];simp [m, r]
   have hrem_geP : ∀ p ∈ remPrimes, P <= p /\ p.Prime := by
     intro p hp;have hpm := List.mem_toFinset.mp hp;obtain ⟨idx, hidx_eq⟩ := List.mem_iff_get.mp hpm;have hxj : p = ps.get ⟨j + idx.1, by have := idx.2; simp at this; omega⟩ := by rw [<- hidx_eq]; simp [List.get_eq_getElem]
     refine ⟨?_, hxj ▸ hps_prime ⟨j + idx.1, by have := idx.2; simp at this; omega⟩⟩
     rw [hxj]
     rcases Nat.eq_zero_or_pos idx.1 with h0 | hpos
     . simp [h0]; rfl
     . exact le_of_lt (List.pairwise_iff_get.mp hps_sorted ⟨j, hj_lt⟩ ⟨j + idx.1, by have := idx.2; simp at this; omega⟩ (by simp; omega))
   have hrem_cop_Qj : ∀ p ∈ remPrimes, Nat.Coprime p (Q j) := by
     intro p hp;have ⟨hPlep, hpr⟩ := hrem_geP p hp
     refine hpr.coprime_iff_not_dvd.mpr ?_
     intro hdvd;have hnd : (ps.take j).Nodup := hps_nodup.take
     have hmem_take : p ∈ ps.take j := by
       dsimp only [Q] at hdvd;have hpeq : (ps.take j).prod = ∏ q ∈ (ps.take j).toFinset, q := by simpa using (List.prod_toFinset (id : ℕ -> ℕ) hnd).symm
       have h1 := (hpr.prime.dvd_finsetProd_iff id).mp (hpeq ▸ hdvd);obtain ⟨q, hq, hpq⟩ := h1;have hqm := List.mem_toFinset.mp hq;have hqpr := Nat.prime_of_mem_primeFactors ((mem_sort (· <= ·)).mp (List.mem_of_mem_take hqm));have heq : p = q := (Nat.prime_dvd_prime_iff_eq hpr hqpr).mp hpq;rwa [heq]
     obtain ⟨idx, hidx_eq⟩ := List.mem_iff_get.mp hmem_take
     have hidx_lt : idx.1 < j := by
       have hlen_le : (ps.take j).length <= j := List.length_take_le _ _;have := idx.2;omega
     have hpeq : p = ps.get ⟨idx.1, by omega⟩ := by rw [<- hidx_eq]; simp [List.get_eq_getElem]
     have hplt : p < P := by
       rw [hpeq];exact List.pairwise_iff_get.mp hps_sorted ⟨idx.1, by omega⟩ ⟨j, hj_lt⟩ hidx_lt
     omega
   have hcov_bad : Sj \ ((Ioc U V).filter (fun q => Nat.Coprime q b)) ⊆ remPrimes.biUnion (fun p => Sj.filter (fun q => p ∣ q)) := by
     intro q hq;obtain ⟨hqSj, hqnot⟩ := Finset.mem_sdiff.mp hq;obtain ⟨hqI, hcopQj⟩ := mem_filter.mp hqSj;have hncopb : ¬ Nat.Coprime q b := fun hc => hqnot (mem_filter.mpr ⟨hqI, hc⟩)
     rw [Nat.coprime_iff_gcd_eq_one] at hncopb;obtain ⟨p, hpr, hpdvd⟩ := Nat.exists_prime_and_dvd hncopb;have hpq : p ∣ q := dvd_trans hpdvd (Nat.gcd_dvd_left q b);have hpb : p ∣ b := dvd_trans hpdvd (Nat.gcd_dvd_right q b);have hpm : p ∈ ps := (mem_sort (· <= ·)).mpr (Nat.mem_primeFactors.mpr ⟨hpr, hpb, by omega⟩)
     have hnot_take : p ∉ ps.take j := by
       intro hmem;have hpQj : p ∣ Q j := List.dvd_prod hmem;exact hpr.not_dvd_one (hcopQj ▸ Nat.dvd_gcd hpq hpQj)
     have hmem_drop : p ∈ ps.drop j := by
       have hsp : ps.take j ++ ps.drop j = ps := List.take_append_drop j ps;rw [<- hsp, List.mem_append] at hpm
       rcases hpm with h | h
       . exact absurd h hnot_take
       . exact h
     exact mem_biUnion.mpr ⟨p, List.mem_toFinset.mpr hmem_drop, mem_filter.mpr ⟨hqSj, hpq⟩⟩
   have hbad_p : ∀ p ∈ remPrimes, ((Sj.filter (fun q => p ∣ q)).card : ℝ) <= ((W : ℝ) / ((p : ℝ) * (Q j : ℝ)) + 2) * ((Q j).totient : ℝ) := fun p hp =>
     card_coprime_div_p_le (hQ_pos j) (hrem_geP p hp).2 (by omega)
   have hbad_total : ((Sj \ ((Ioc U V).filter (fun q => Nat.Coprime q b))).card : ℝ) <= ((m : ℝ) / (P : ℝ) * ((W : ℝ) / (Q j : ℝ)) + 2 * (m : ℝ)) * ((Q j).totient : ℝ) := by
     have h1 : ((Sj \ ((Ioc U V).filter (fun q => Nat.Coprime q b))).card : ℝ) <= ∑ p ∈ remPrimes, ((Sj.filter (fun q => p ∣ q)).card : ℝ) := by exact_mod_cast le_trans (card_le_card hcov_bad) card_biUnion_le
     refine le_trans h1 ?_
     have hPposR : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP_prime.pos
     have hQj_posR : (0 : ℝ) < (Q j : ℝ) := by exact_mod_cast hQ_pos j
     have h2 : ∑ p ∈ remPrimes, ((Sj.filter (fun q => p ∣ q)).card : ℝ) <= ∑ _p ∈ remPrimes, ((W : ℝ) / ((P : ℝ) * (Q j : ℝ)) + 2) * ((Q j).totient : ℝ) := by
       apply sum_le_sum;intro p hp
       refine le_trans (hbad_p p hp) ?_
       apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _);have hPlep : (P : ℝ) <= (p : ℝ) := by exact_mod_cast (hrem_geP p hp).1
       have hdiv : (W : ℝ) / ((p : ℝ) * (Q j : ℝ)) <= (W : ℝ) / ((P : ℝ) * (Q j : ℝ)) := div_le_div_of_nonneg_left (Nat.cast_nonneg W) (by positivity) (mul_le_mul_of_nonneg_right hPlep (le_of_lt hQj_posR));linarith
     refine le_trans h2 ?_
     rw [sum_const, nsmul_eq_mul, hrem_card];have heq : (m : ℝ) * (((W : ℝ) / ((P : ℝ) * (Q j : ℝ)) + 2) * ((Q j).totient : ℝ)) = ((m : ℝ) / (P : ℝ) * ((W : ℝ) / (Q j : ℝ)) + 2 * (m : ℝ)) * ((Q j).totient : ℝ) := by field_simp
     rw [heq]
   have hSj_lb : (((W : ℝ) / (Q j : ℝ)) - 1) * ((Q j).totient : ℝ) <= (Sj.card : ℝ) := by
     have hQj_posR : (0 : ℝ) < (Q j : ℝ) := by exact_mod_cast hQ_pos j
     have h1 : (((W / Q j : ℕ) : ℝ) * ((Q j).totient : ℝ)) <= (Sj.card : ℝ) := by exact_mod_cast (card_coprime_Ioc_bounds (hQ_pos j) U V (by omega)).1
     have hlt : W < (W / Q j + 1) * Q j := by
       have := Nat.lt_div_mul_add (a := W) (b := Q j) (hQ_pos j);rw [add_mul, one_mul]; exact this
     have hltR : (W : ℝ) < (((W / Q j : ℕ) : ℝ) + 1) * (Q j : ℝ) := by exact_mod_cast hlt
     have hdiv_ge : (W : ℝ) / (Q j : ℝ) - 1 <= ((W / Q j : ℕ) : ℝ) := by rw [sub_le_iff_le_add, div_le_iff₀ hQj_posR]; linarith
     exact le_trans (mul_le_mul_of_nonneg_right hdiv_ge (Nat.cast_nonneg _)) h1
   have hsub_sdiff : (Sj.card : ℝ) - ((Sj \ ((Ioc U V).filter (fun q => Nat.Coprime q b))).card : ℝ) <= (((Ioc U V).filter (fun q => Nat.Coprime q b)).card : ℝ) := by
     have h1 : Sj.card <= ((Ioc U V).filter (fun q => Nat.Coprime q b)).card + (Sj \ ((Ioc U V).filter (fun q => Nat.Coprime q b))).card := by
       have hsub : Sj ⊆ ((Ioc U V).filter (fun q => Nat.Coprime q b)) ∪ (Sj \ ((Ioc U V).filter (fun q => Nat.Coprime q b))) := by
         intro q hq
         by_cases h : q ∈ (Ioc U V).filter (fun q => Nat.Coprime q b)
         . exact mem_union_left _ h
         . exact mem_union_right _ (Finset.mem_sdiff.mpr ⟨hq, h⟩)
       exact le_trans (card_le_card hsub) (card_union_le _ _)
     have h1R : (Sj.card : ℝ) <= (((Ioc U V).filter (fun q => Nat.Coprime q b)).card : ℝ) + ((Sj \ ((Ioc U V).filter (fun q => Nat.Coprime q b))).card : ℝ) := by exact_mod_cast h1
     linarith
   have hQj_posR : (0 : ℝ) < (Q j : ℝ) := by exact_mod_cast hQ_pos j
   have hPposR : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP_prime.pos
   have hmP : (m : ℝ) / (P : ℝ) <= 1 / 4 := by
     rw [div_le_div_iff₀ hPposR (by norm_num)];have : (4 * (m : ℝ)) <= (P : ℝ) := by exact_mod_cast h4m_le_P
     linarith
   have hWQ_ge : (8 * ((L + 1 : ℕ) : ℝ)) <= (W : ℝ) / (Q j : ℝ) := by
     rw [le_div_iff₀ hQj_posR];have : (8 * ((L + 1 : ℕ) : ℝ)) * (Q j : ℝ) = ((Q j * (8 * (L + 1)) : ℕ) : ℝ) := by push_cast; ring
     rw [this];exact_mod_cast hQj_mul
   have hm_le_L : (m : ℝ) <= (L : ℝ) := by exact_mod_cast (by omega : m <= L)
   have h1_2m : 1 + 2 * (m : ℝ) <= (3 / 8 : ℝ) * ((W : ℝ) / (Q j : ℝ)) := by
     have : ((L + 1 : ℕ) : ℝ) = (L : ℝ) + 1 := by push_cast; ring
     linarith
   have hcoeff_lb : (1 / 4 : ℝ) * ((W : ℝ) / (Q j : ℝ)) <= ((W : ℝ) / (Q j : ℝ) - 1) - ((m : ℝ) / (P : ℝ) * ((W : ℝ) / (Q j : ℝ)) + 2 * (m : ℝ)) := by
     have hWQ0 : 0 <= (W : ℝ) / (Q j : ℝ) := by positivity
     have hprod : (m : ℝ) / (P : ℝ) * ((W : ℝ) / (Q j : ℝ)) <= (1 / 4 : ℝ) * ((W : ℝ) / (Q j : ℝ)) := mul_le_mul_of_nonneg_right hmP hWQ0;linarith
   have htot_mul : (Q j : ℝ) / ((L + 1 : ℕ) : ℝ) <= ((Q j).totient : ℝ) := by
     have := (le_div_iff₀ hQj_posR).mp htot_j;linarith [show (1 : ℝ) / ((L + 1 : ℕ) : ℝ) * (Q j : ℝ) = (Q j : ℝ) / ((L + 1 : ℕ) : ℝ) by ring]
   calc ((W : ℕ) : ℝ) / (4 * ((L + 1 : ℕ) : ℝ))
       = ((1 / 4 : ℝ) * ((W : ℝ) / (Q j : ℝ))) * ((Q j : ℝ) / ((L + 1 : ℕ) : ℝ)) := by field_simp
     _ <= ((1 / 4 : ℝ) * ((W : ℝ) / (Q j : ℝ))) * ((Q j).totient : ℝ) := mul_le_mul_of_nonneg_left htot_mul (by positivity)
     _ <= (((W : ℝ) / (Q j : ℝ) - 1) - ((m : ℝ) / (P : ℝ) * ((W : ℝ) / (Q j : ℝ)) + 2 * (m : ℝ))) * ((Q j).totient : ℝ) := mul_le_mul_of_nonneg_right hcoeff_lb (Nat.cast_nonneg _)
     _ = (((W : ℝ) / (Q j : ℝ) - 1) * ((Q j).totient : ℝ)) - (((m : ℝ) / (P : ℝ) * ((W : ℝ) / (Q j : ℝ)) + 2 * (m : ℝ)) * ((Q j).totient : ℝ)) := by ring
     _ <= (Sj.card : ℝ) - ((Sj \ ((Ioc U V).filter (fun q => Nat.Coprime q b))).card : ℝ) := by linarith
     _ <= (((Ioc U V).filter (fun q => Nat.Coprime q b)).card : ℝ) := hsub_sdiff
noncomputable def zeta2Sum (N : ℕ) : ℝ := ∑ d ∈ Icc 1 N, (1 : ℝ) / (d : ℝ) ^ 2
noncomputable def moebius2Sum (N : ℕ) : ℝ := ∑ d ∈ Icc 1 N, ((moebius d : ℤ) : ℝ) / (d : ℝ) ^ 2
lemma zeta2Sum_bounds {N : ℕ} (hN : 100 <= N) : (159 / 100 : ℝ) <= zeta2Sum N /\ zeta2Sum N <= 165 / 100 := by
 constructor
 . have hsub : Icc 1 20 ⊆ Icc 1 N := Finset.Icc_subset_Icc_right (by omega)
   have h1 : zeta2Sum 20 <= zeta2Sum N := sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
   refine le_trans ?_ h1
   unfold zeta2Sum
   have hdec : (159 / 100 : ℝ) <= ∑ d ∈ Icc (1 : ℕ) 20, (1 : ℝ) / (d : ℝ) ^ 2 := by
     have : Icc (1 : ℕ) 20 = {1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20} := by decide
     rw [this]; norm_num
   exact hdec
 . have hsub : Icc 1 N ⊆ Icc 1 20 ∪ Icc 21 N := by
     intro d hd; have := mem_Icc.mp hd
     by_cases h20 : d <= 20
     . exact mem_union_left _ (mem_Icc.mpr ⟨this.1, h20⟩)
     . exact mem_union_right _ (mem_Icc.mpr ⟨by omega, this.2⟩)
   have hdisj : Disjoint (Icc 1 20) (Icc 21 N) := by
     rw [Finset.disjoint_left]; intro x h1 h2;have := (mem_Icc.mp h1).2; have := (mem_Icc.mp h2).1; omega
   unfold zeta2Sum
   calc ∑ d ∈ Icc 1 N, (1 : ℝ) / (d : ℝ) ^ 2
       <= ∑ d ∈ Icc 1 20 ∪ Icc 21 N, (1 : ℝ) / (d : ℝ) ^ 2 := sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
     _ = ∑ d ∈ Icc (1 : ℕ) 20, (1 : ℝ) / (d : ℝ) ^ 2 + ∑ d ∈ Icc 21 N, (1 : ℝ) / (d : ℝ) ^ 2 := sum_union hdisj
     _ <= (15962 / 10000 : ℝ) + 1 / 20 := by
         have h20 : ∑ d ∈ Icc (1 : ℕ) 20, (1 : ℝ) / (d : ℝ) ^ 2 <= 15962 / 10000 := by
           have : Icc (1 : ℕ) 20 = {1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20} := by decide
           rw [this]; norm_num
         linarith [h20, sum_inv_sq_tail 20 N (by omega)]
     _ <= 165 / 100 := by norm_num
lemma moebius_abs_le_one (d : ℕ) : |((moebius d : ℤ) : ℝ)| <= 1 := by
 have h1 : |moebius d| <= 1 := by
   by_cases h0 : d = 0
   . subst h0; simp
   . by_cases hsf : Squarefree d
     . rw [moebius_apply_of_squarefree hsf]
       rcases Nat.even_or_odd (ArithmeticFunction.cardFactors d) with ⟨k, hk⟩ | ⟨k, hk⟩
       . rw [hk, <- two_mul, pow_mul]; norm_num
       . rw [hk, pow_add, pow_mul]; norm_num
     . rw [moebius_eq_zero_of_not_squarefree hsf]; simp
 exact_mod_cast h1
lemma moebius2Sum_mul_zeta2Sum_approx {N : ℕ} (hN : 1 <= N) : |moebius2Sum N * zeta2Sum N - 1| <= 7 / Real.sqrt (N : ℝ) := by
 unfold moebius2Sum zeta2Sum;rw [sum_mul]
 have h1 : ∑ d ∈ Icc 1 N, ((moebius d : ℤ) : ℝ) / (d : ℝ) ^ 2 * ∑ k ∈ Icc 1 N, (1 : ℝ) / (k : ℝ) ^ 2 = ∑ p ∈ Icc 1 N ×ˢ Icc 1 N, ((moebius p.1 : ℤ) : ℝ) / ((p.1 * p.2 : ℕ) : ℝ) ^ 2 := by
   rw [sum_product]
   refine sum_congr rfl fun d _ => ?_
   rw [mul_sum]
   refine sum_congr rfl fun k _ => ?_
   push_cast; ring
 rw [h1]
 let P1 := (Icc 1 N ×ˢ Icc 1 N).filter (fun p => p.1 * p.2 <= N)
 let P2 := (Icc 1 N ×ˢ Icc 1 N).filter (fun p => N < p.1 * p.2)
 have hsplit : ∑ p ∈ Icc 1 N ×ˢ Icc 1 N, ((moebius p.1 : ℤ) : ℝ) / ((p.1 * p.2 : ℕ) : ℝ) ^ 2 = (∑ p ∈ P1, ((moebius p.1 : ℤ) : ℝ) / ((p.1 * p.2 : ℕ) : ℝ) ^ 2) + (∑ p ∈ P2, ((moebius p.1 : ℤ) : ℝ) / ((p.1 * p.2 : ℕ) : ℝ) ^ 2) := by
   rw [<- sum_filter_add_sum_filter_not _ (fun p : ℕ × ℕ => p.1 * p.2 <= N)]
   congr 1; apply sum_congr ?_ (fun _ _ => rfl)
   ext p; simp only [P2, mem_filter]; constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩
 rw [hsplit]
 have hP1 : ∑ p ∈ P1, ((moebius p.1 : ℤ) : ℝ) / ((p.1 * p.2 : ℕ) : ℝ) ^ 2 = 1 := by
   have hfib : ∑ p ∈ P1, ((moebius p.1 : ℤ) : ℝ) / ((p.1 * p.2 : ℕ) : ℝ) ^ 2 = ∑ m ∈ Icc 1 N, ∑ p ∈ P1.filter (fun p => p.1 * p.2 = m), ((moebius p.1 : ℤ) : ℝ) / (m : ℝ) ^ 2 := by
     rw [<- sum_fiberwise_of_maps_to (g := fun p : ℕ × ℕ => p.1 * p.2) (t := Icc 1 N)]
     . apply sum_congr rfl; intro m _
       apply sum_congr rfl; intro p hp;rw [(mem_filter.mp hp).2]
     . intro p hp
       obtain ⟨hpP, hmul⟩ := mem_filter.mp hp;obtain ⟨h1, h2⟩ := mem_product.mp hpP;have hp1 := (mem_Icc.mp h1).1;have hp2 := (mem_Icc.mp h2).1;exact mem_Icc.mpr ⟨by nlinarith, hmul⟩
   rw [hfib]
   have hterm : ∀ m ∈ Icc 1 N, ∑ p ∈ P1.filter (fun p => p.1 * p.2 = m), ((moebius p.1 : ℤ) : ℝ) / (m : ℝ) ^ 2 = if m = 1 then 1 else 0 := by
     intro m hm;have hm1 := (mem_Icc.mp hm).1;have hmN := (mem_Icc.mp hm).2;rw [<- sum_div]
     have hbij : ∑ p ∈ P1.filter (fun p => p.1 * p.2 = m), ((moebius p.1 : ℤ) : ℝ) = ∑ d ∈ m.divisors, ((moebius d : ℤ) : ℝ) := by
       refine sum_bij (fun p _ => p.1) ?_ ?_ ?_ (fun _ _ => rfl)
       . intro p hp
         obtain ⟨hpP1, hpm⟩ := mem_filter.mp hp;exact Nat.mem_divisors.mpr ⟨⟨p.2, hpm.symm⟩, by omega⟩
       . intro p1 hp1 p2 hp2 heq
         have h1 := (mem_filter.mp hp1).2;have h2 := (mem_filter.mp hp2).2;have hdpos : 0 < p1.1 := (mem_Icc.mp (mem_product.mp (mem_filter.mp (mem_filter.mp hp1).1).1).1).1;have heq' : p1.1 = p2.1 := heq;have h2eq : p1.2 = p2.2 := Nat.eq_of_mul_eq_mul_left hdpos (by rw [h1, <- h2, heq']);exact Prod.ext heq' h2eq
       . intro d hd
         obtain ⟨⟨k, hk⟩, -⟩ := Nat.mem_divisors.mp hd;have hd1 : 1 <= d := Nat.pos_of_dvd_of_pos ⟨k, hk⟩ (by omega)
         have hk1 : 1 <= k := by
           rcases Nat.eq_zero_or_pos k with rfl | h0
           . simp at hk; omega
           . exact h0
         have hdN : d <= N := by nlinarith
         have hkN : k <= N := by nlinarith
         refine ⟨(d, k), mem_filter.mpr ⟨mem_filter.mpr ⟨mem_product.mpr ⟨mem_Icc.mpr ⟨hd1, hdN⟩, mem_Icc.mpr ⟨hk1, hkN⟩⟩, show d * k <= N by omega⟩, hk.symm⟩, rfl⟩
     rw [hbij]
     have hmz : ∑ d ∈ m.divisors, (moebius d : ℤ) = if m = 1 then 1 else 0 := by
       have h := congrFun (congrArg DFunLike.coe moebius_mul_coe_zeta) m;rw [ArithmeticFunction.mul_apply, ArithmeticFunction.one_apply] at h
       rw [Nat.sum_divisorsAntidiagonal (f := fun x y =>
         moebius x * ((ArithmeticFunction.zeta : ArithmeticFunction ℤ) y))] at h
       have hsimp : ∑ d ∈ m.divisors, moebius d * ((ArithmeticFunction.zeta : ArithmeticFunction ℤ) (m / d)) = ∑ d ∈ m.divisors, moebius d := by
         apply sum_congr rfl;intro d hd;have hd0 : m / d ≠ 0 := Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_divisors hd)) (Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hd) (by omega)));simp [ArithmeticFunction.zeta_apply_ne hd0]
       rwa [hsimp] at h
     have hmzR : ∑ d ∈ m.divisors, ((moebius d : ℤ) : ℝ) = if m = 1 then (1 : ℝ) else 0 := by rw [<- Int.cast_sum, hmz]; split_ifs <;> simp
     rw [hmzR]; split_ifs with hm1'
     . subst hm1'; norm_num
     . simp
   rw [sum_congr rfl hterm, sum_ite_eq'];simp [mem_Icc.mpr ⟨le_rfl, hN⟩]
 rw [hP1, add_sub_cancel_left]
 have hP2_le : |∑ p ∈ P2, ((moebius p.1 : ℤ) : ℝ) / ((p.1 * p.2 : ℕ) : ℝ) ^ 2| <= ∑ p ∈ P2, (1 : ℝ) / ((p.1 * p.2 : ℕ) : ℝ) ^ 2 := by
   refine le_trans (abs_sum_le_sum_abs _ _) (sum_le_sum fun p _ => ?_)
   rw [abs_div, abs_of_nonneg (sq_nonneg ((p.1 * p.2 : ℕ) : ℝ))];exact div_le_div_of_nonneg_right (moebius_abs_le_one p.1) (sq_nonneg _)
 refine le_trans hP2_le ?_
 set S := Nat.sqrt N
 have hS1 : 1 <= S := Nat.le_sqrt.mpr (by nlinarith);have hS_sq : S * S <= N := Nat.sqrt_le N;have hN_lt_S1 : N < (S + 1) * (S + 1) := Nat.lt_succ_sqrt N
 have hP2_sub : P2 ⊆ (Icc 1 S ×ˢ Icc (S + 1) N) ∪ (Icc (S + 1) N ×ˢ Icc 1 N) := by
   intro p hp;obtain ⟨hpP, hgt⟩ := mem_filter.mp hp;obtain ⟨h1, h2⟩ := mem_product.mp hpP;obtain ⟨h1a, h1b⟩ := mem_Icc.mp h1;obtain ⟨h2a, h2b⟩ := mem_Icc.mp h2
   by_cases hp1 : p.1 <= S
   . apply mem_union_left
     refine mem_product.mpr ⟨mem_Icc.mpr ⟨h1a, hp1⟩, mem_Icc.mpr ⟨?_, h2b⟩⟩
     by_contra hlt;have : p.1 * p.2 <= S * S := Nat.mul_le_mul hp1 (by omega);omega
   . apply mem_union_right
     exact mem_product.mpr ⟨mem_Icc.mpr ⟨by omega, h1b⟩, h2⟩
 have hsum_P2 : ∑ p ∈ P2, (1 : ℝ) / ((p.1 * p.2 : ℕ) : ℝ) ^ 2 <= (∑ d ∈ Icc 1 S, (1 : ℝ) / (d : ℝ) ^ 2) * (∑ k ∈ Icc (S + 1) N, (1 : ℝ) / (k : ℝ) ^ 2) + (∑ d ∈ Icc (S + 1) N, (1 : ℝ) / (d : ℝ) ^ 2) * (∑ k ∈ Icc 1 N, (1 : ℝ) / (k : ℝ) ^ 2) := by
   have hdisj : Disjoint (Icc 1 S ×ˢ Icc (S + 1) N) (Icc (S + 1) N ×ˢ Icc 1 N) := by
     rw [Finset.disjoint_left]; intro p h1 h2;have := (mem_Icc.mp (mem_product.mp h1).1).2;have := (mem_Icc.mp (mem_product.mp h2).1).1;omega
   have h1 := sum_le_sum_of_subset_of_nonneg hP2_sub (f := fun p : ℕ × ℕ => (1 : ℝ) / ((p.1 * p.2 : ℕ) : ℝ) ^ 2) (fun _ _ _ => div_nonneg zero_le_one (sq_nonneg _));rw [sum_union hdisj] at h1
   have hfac : ∀ A B : Finset ℕ, ∑ p ∈ A ×ˢ B, (1 : ℝ) / ((p.1 * p.2 : ℕ) : ℝ) ^ 2 = (∑ d ∈ A, (1 : ℝ) / (d : ℝ) ^ 2) * (∑ k ∈ B, (1 : ℝ) / (k : ℝ) ^ 2) := by
     intro A B;rw [sum_product, sum_mul]
     refine sum_congr rfl fun d _ => ?_
     rw [mul_sum]
     refine sum_congr rfl fun k _ => ?_
     push_cast; ring
   rw [hfac, hfac] at h1;exact h1
 refine le_trans hsum_P2 ?_
 have htail := sum_inv_sq_tail S N hS1;have hfull1 := sum_inv_sq_le_61_36 S;have hfull2 := sum_inv_sq_le_61_36 N;have hSposR : (0 : ℝ) < (S : ℝ) := by exact_mod_cast hS1
 have hsqrt_le : Real.sqrt (N : ℝ) <= 2 * (S : ℝ) := by
   have h1 : (N : ℝ) <= (2 * (S : ℝ)) ^ 2 := by
     have : N <= 4 * S * S := by nlinarith
     have hR : (N : ℝ) <= (4 * S * S : ℕ) := by exact_mod_cast this
     push_cast at hR; linarith
   have h2 : Real.sqrt (N : ℝ) <= Real.sqrt ((2 * (S : ℝ)) ^ 2) := Real.sqrt_le_sqrt h1;rwa [Real.sqrt_sq (by positivity)] at h2
 have hinv : (1 : ℝ) / (S : ℝ) <= 2 / Real.sqrt (N : ℝ) := by
   have hsqpos : (0 : ℝ) < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hN);rw [div_le_div_iff₀ hSposR hsqpos]; linarith
 have hbd : (61 / 36 : ℝ) * (1 / (S : ℝ)) + (1 / (S : ℝ)) * (61 / 36 : ℝ) <= 7 / Real.sqrt (N : ℝ) := by
   have h1 : (61 / 36 : ℝ) * (1 / (S : ℝ)) + (1 / (S : ℝ)) * (61 / 36 : ℝ) = (61 / 18 : ℝ) * (1 / (S : ℝ)) := by ring
   have h2 : (61 / 18 : ℝ) * (1 / (S : ℝ)) <= (61 / 18 : ℝ) * (2 / Real.sqrt (N : ℝ)) := mul_le_mul_of_nonneg_left hinv (by norm_num);have h3 : (61 / 18 : ℝ) * (2 / Real.sqrt (N : ℝ)) = (61 / 9 : ℝ) / Real.sqrt (N : ℝ) := by ring
   have h4 : (61 / 9 : ℝ) / Real.sqrt (N : ℝ) <= 7 / Real.sqrt (N : ℝ) := div_le_div_of_nonneg_right (by norm_num) (Real.sqrt_nonneg _);linarith
 have hmul1 : (∑ d ∈ Icc 1 S, (1 : ℝ) / (d : ℝ) ^ 2) * (∑ k ∈ Icc (S + 1) N, (1 : ℝ) / (k : ℝ) ^ 2) <= (61 / 36 : ℝ) * (1 / (S : ℝ)) := mul_le_mul hfull1 htail (sum_nonneg fun _ _ => by positivity) (by norm_num);have hmul2 : (∑ d ∈ Icc (S + 1) N, (1 : ℝ) / (d : ℝ) ^ 2) * (∑ k ∈ Icc 1 N, (1 : ℝ) / (k : ℝ) ^ 2) <= (1 / (S : ℝ)) * (61 / 36 : ℝ) := mul_le_mul htail hfull2 (sum_nonneg fun _ _ => by positivity) (by positivity);linarith
lemma card_coprime_rect_le {M a1 a2 b1 b2 : ℕ} (hM : 1 <= M) (ha1 : 1 <= a1) (ha2 : a2 <= M) (hb1 : 1 <= b1) (hb2 : b2 <= M) : (((Icc a1 a2 ×ˢ Icc b1 b2).filter (fun p => Nat.Coprime p.1 p.2)).card : ℝ) <= moebius2Sum M * ((Icc a1 a2).card : ℝ) * ((Icc b1 b2).card : ℝ) + 2 * (M : ℝ) * (1 + Real.log M) + (M : ℝ) := by
 let R := Icc a1 a2 ×ˢ Icc b1 b2
 have hmob : ((R.filter (fun p => Nat.Coprime p.1 p.2)).card : ℝ) = ∑ d ∈ Icc 1 M, ((moebius d : ℤ) : ℝ) * (((Icc a1 a2).filter (fun x => d ∣ x)).card : ℝ) * (((Icc b1 b2).filter (fun y => d ∣ y)).card : ℝ) := by
   have h1 : ∀ p ∈ R, (if Nat.Coprime p.1 p.2 then (1 : ℝ) else 0) = ∑ d ∈ (Nat.gcd p.1 p.2).divisors, ((moebius d : ℤ) : ℝ) := by
     intro p hp;obtain ⟨hpa, hpb⟩ := mem_product.mp hp;have hpos : 0 < Nat.gcd p.1 p.2 := Nat.gcd_pos_of_pos_left _ (by have := (mem_Icc.mp hpa).1; omega)
     have hmz : ∑ d ∈ (Nat.gcd p.1 p.2).divisors, (moebius d : ℤ) = if Nat.gcd p.1 p.2 = 1 then 1 else 0 := by
       have h := congrFun (congrArg DFunLike.coe moebius_mul_coe_zeta) (Nat.gcd p.1 p.2);rw [ArithmeticFunction.mul_apply, ArithmeticFunction.one_apply] at h
       rw [Nat.sum_divisorsAntidiagonal (f := fun x y =>
         moebius x * ((ArithmeticFunction.zeta : ArithmeticFunction ℤ) y))] at h
       have hsimp : ∑ d ∈ (Nat.gcd p.1 p.2).divisors, moebius d * ((ArithmeticFunction.zeta : ArithmeticFunction ℤ) (Nat.gcd p.1 p.2 / d)) = ∑ d ∈ (Nat.gcd p.1 p.2).divisors, moebius d := by
         apply sum_congr rfl;intro d hd;have hd0 : Nat.gcd p.1 p.2 / d ≠ 0 := Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd hpos (Nat.dvd_of_mem_divisors hd)) (Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hd) hpos));simp [ArithmeticFunction.zeta_apply_ne hd0]
       rwa [hsimp] at h
     have hmzR : ∑ d ∈ (Nat.gcd p.1 p.2).divisors, ((moebius d : ℤ) : ℝ) = if Nat.gcd p.1 p.2 = 1 then (1 : ℝ) else 0 := by rw [<- Int.cast_sum, hmz]; split_ifs <;> simp
     simp only [hmzR, Nat.coprime_iff_gcd_eq_one]
   have h2 : ((R.filter (fun p => Nat.Coprime p.1 p.2)).card : ℝ) = ∑ p ∈ R, (if Nat.Coprime p.1 p.2 then (1 : ℝ) else 0) := by rw [sum_boole]
   rw [h2, sum_congr rfl h1]
   have h3 : ∑ p ∈ R, ∑ d ∈ (Nat.gcd p.1 p.2).divisors, ((moebius d : ℤ) : ℝ) = ∑ p ∈ R, ∑ d ∈ Icc 1 M, if d ∣ p.1 /\ d ∣ p.2 then ((moebius d : ℤ) : ℝ) else 0 := by
     apply sum_congr rfl;intro p hp;obtain ⟨hpa, hpb⟩ := mem_product.mp hp;have hp1 := mem_Icc.mp hpa;have hpos : 0 < Nat.gcd p.1 p.2 := Nat.gcd_pos_of_pos_left _ (by omega);rw [<- sum_filter];apply sum_congr ?_ (fun _ _ => rfl)
     ext d
     simp only [Nat.mem_divisors, mem_filter, mem_Icc, Nat.dvd_gcd_iff]
     constructor
     . rintro ⟨⟨hd1, hd2⟩, -⟩
       have hdpos : 1 <= d := Nat.pos_of_dvd_of_pos hd1 (by omega);have hdle : d <= M := le_trans (Nat.le_of_dvd (by omega) hd1) (by omega);exact ⟨⟨hdpos, hdle⟩, hd1, hd2⟩
     . rintro ⟨-, hd1, hd2⟩
       exact ⟨⟨hd1, hd2⟩, by omega⟩
   rw [h3, sum_comm];apply sum_congr rfl;intro d _;rw [<- sum_filter, sum_const, nsmul_eq_mul]
   have hprod_eq : R.filter (fun p => d ∣ p.1 /\ d ∣ p.2) = ((Icc a1 a2).filter (fun x => d ∣ x)) ×ˢ ((Icc b1 b2).filter (fun y => d ∣ y)) := by
     ext p; simp only [R, mem_filter, mem_product]; tauto
   rw [hprod_eq, card_product, Nat.cast_mul];ring
 rw [hmob]
 have hdiv_err : ∀ (u v d : ℕ), 1 <= u -> 1 <= d -> ∃ e : ℝ, |e| <= 1 /\ ((((Icc u v).filter (fun x => d ∣ x)).card : ℝ) = ((Icc u v).card : ℝ) / (d : ℝ) + e) := by
   intro u v d hu1 hd
   set c : ℝ := (((Icc u v).filter (fun x => d ∣ x)).card : ℝ)
   set q : ℝ := ((Icc u v).card : ℝ) / (d : ℝ)
   refine ⟨c - q, ?_, by ring⟩
   rw [abs_le]
   by_cases huv : v < u
   . have : Icc u v = ∅ := by
       ext x; simp only [mem_Icc, notMem_empty, iff_false]; omega
     simp [c, q, this]
   . have hcard : (Icc u v).card = v + 1 - u := Nat.card_Icc u v
     have hcnt : ((Icc u v).filter (fun x => d ∣ x)).card = v / d - (u - 1) / d := by
       have h1 : ∀ n : ℕ, ((Icc 1 n).filter (fun x => d ∣ x)).card = n / d := by
         intro n;have hcardI : (Icc 1 (n / d)).card = n / d := by rw [Nat.card_Icc, Nat.add_sub_cancel]
         rw [<- hcardI]
         refine card_bij (fun x _ => x / d) ?_ ?_ ?_
         . intro x hx
           obtain ⟨hxI, hdx⟩ := mem_filter.mp hx;have hx1 := (mem_Icc.mp hxI).1;have hxn := (mem_Icc.mp hxI).2;exact mem_Icc.mpr ⟨(Nat.one_le_div_iff (by omega)).mpr (Nat.le_of_dvd (by omega) hdx), Nat.div_le_div_right hxn⟩
         . intro x1 hx1 x2 hx2 hq
           have h1 := Nat.mul_div_cancel' (mem_filter.mp hx1).2;have h2 := Nat.mul_div_cancel' (mem_filter.mp hx2).2;have hq' : x1 / d = x2 / d := hq;rw [hq'] at h1;omega
         . intro k hk
           obtain ⟨hk1, hkn⟩ := mem_Icc.mp hk;have hkdv : d * k <= n := le_trans (Nat.mul_le_mul_left d hkn) (Nat.mul_div_le n d)
           refine ⟨d * k, mem_filter.mpr ⟨mem_Icc.mpr ⟨by nlinarith, hkdv⟩, dvd_mul_right d k⟩, Nat.mul_div_cancel_left k (by omega)⟩
       have hunion : Icc 1 v = Icc 1 (u - 1) ∪ Icc u v := by
         ext x; simp only [mem_Icc, mem_union]; omega
       have hdisj : Disjoint (Icc 1 (u - 1)) (Icc u v) := by
         rw [Finset.disjoint_left]; intro x h1 h2;have := (mem_Icc.mp h1).2; have := (mem_Icc.mp h2).1; omega
       have hsum := congrArg Finset.card (by rw [hunion, filter_union] : (Icc 1 v).filter (fun x => d ∣ x) = (Icc 1 (u - 1)).filter (fun x => d ∣ x) ∪ (Icc u v).filter (fun x => d ∣ x));rw [card_union_of_disjoint (disjoint_filter_filter hdisj), h1 v, h1 (u - 1)] at hsum;omega
     have hdposR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
     have hv1 : (v : ℝ) / (d : ℝ) - 1 < ((v / d : ℕ) : ℝ) /\ ((v / d : ℕ) : ℝ) <= (v : ℝ) / (d : ℝ) := by
       constructor
       . rw [sub_lt_iff_lt_add, div_lt_iff₀ hdposR]
         have hlt := Nat.lt_div_mul_add (a := v) (b := d) (by omega);have hltR : (v : ℝ) < ((v / d : ℕ) : ℝ) * (d : ℝ) + (d : ℝ) := by exact_mod_cast hlt
         linarith
       . rw [le_div_iff₀ hdposR]; exact_mod_cast Nat.div_mul_le_self v d
     have hu1' : (((u - 1 : ℕ) : ℝ) / (d : ℝ) - 1 < (((u - 1) / d : ℕ) : ℝ) /\ (((u - 1) / d : ℕ) : ℝ) <= ((u - 1 : ℕ) : ℝ) / (d : ℝ)) := by
       constructor
       . rw [sub_lt_iff_lt_add, div_lt_iff₀ hdposR]
         have hlt := Nat.lt_div_mul_add (a := u - 1) (b := d) (by omega);have hltR : ((u - 1 : ℕ) : ℝ) < (((u - 1) / d : ℕ) : ℝ) * (d : ℝ) + (d : ℝ) := by exact_mod_cast hlt
         linarith
       . rw [le_div_iff₀ hdposR]; exact_mod_cast Nat.div_mul_le_self (u - 1) d
     have hcntR : c = ((v / d : ℕ) : ℝ) - (((u - 1) / d : ℕ) : ℝ) := by dsimp only [c]; rw [hcnt, Nat.cast_sub (Nat.div_le_div_right (by omega))]
     have hqR : q = ((v : ℝ) - ((u - 1 : ℕ) : ℝ)) / (d : ℝ) := by
       dsimp only [q]; rw [hcard];have : v + 1 - u = v - (u - 1) := by omega
       rw [this, Nat.cast_sub (by omega)]
     rw [hcntR, hqR, sub_div]
     constructor <;> linarith
 have hterm : ∀ d ∈ Icc 1 M, ((moebius d : ℤ) : ℝ) * (((Icc a1 a2).filter (fun x => d ∣ x)).card : ℝ) * (((Icc b1 b2).filter (fun y => d ∣ y)).card : ℝ) <= (((moebius d : ℤ) : ℝ) / (d : ℝ) ^ 2) * ((Icc a1 a2).card : ℝ) * ((Icc b1 b2).card : ℝ) + (2 * (M : ℝ) / (d : ℝ) + 1) := by
   intro d hd;have hd1 : 1 <= d := (mem_Icc.mp hd).1;obtain ⟨ea, hea, hae⟩ := hdiv_err a1 a2 d ha1 hd1;obtain ⟨eb, heb, hbe⟩ := hdiv_err b1 b2 d hb1 hd1;rw [hae, hbe]
   set A : ℝ := ((Icc a1 a2).card : ℝ)
   set B : ℝ := ((Icc b1 b2).card : ℝ)
   set mu : ℝ := ((moebius d : ℤ) : ℝ)
   have hA_le : A <= (M : ℝ) := by dsimp only [A]; rw [Nat.card_Icc]; exact_mod_cast (by omega : a2 + 1 - a1 <= M)
   have hB_le : B <= (M : ℝ) := by dsimp only [B]; rw [Nat.card_Icc]; exact_mod_cast (by omega : b2 + 1 - b1 <= M)
   have hA0 : 0 <= A := Nat.cast_nonneg _;have hB0 : 0 <= B := Nat.cast_nonneg _;have hmu : |mu| <= 1 := moebius_abs_le_one d;have hdposR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
   have hexp : mu * (A / (d : ℝ) + ea) * (B / (d : ℝ) + eb) - mu / (d : ℝ) ^ 2 * A * B = mu * (A / (d : ℝ) * eb + B / (d : ℝ) * ea + ea * eb) := by ring
   have herr : |mu * (A / (d : ℝ) * eb + B / (d : ℝ) * ea + ea * eb)| <= 2 * (M : ℝ) / (d : ℝ) + 1 := by
     rw [abs_mul];have h1 : |A / (d : ℝ) * eb + B / (d : ℝ) * ea + ea * eb| <= |A / (d : ℝ) * eb| + |B / (d : ℝ) * ea| + |ea * eb| := by linarith [abs_add_le (A / (d : ℝ) * eb + B / (d : ℝ) * ea) (ea * eb), abs_add_le (A / (d : ℝ) * eb) (B / (d : ℝ) * ea)]
     have h2 : |A / (d : ℝ) * eb| <= (M : ℝ) / (d : ℝ) := by
       rw [abs_mul, abs_of_nonneg (by positivity)];exact le_trans (mul_le_mul_of_nonneg_left heb (by positivity)) (by rw [mul_one]; exact div_le_div_of_nonneg_right hA_le (le_of_lt hdposR))
     have h3 : |B / (d : ℝ) * ea| <= (M : ℝ) / (d : ℝ) := by
       rw [abs_mul, abs_of_nonneg (by positivity)];exact le_trans (mul_le_mul_of_nonneg_left hea (by positivity)) (by rw [mul_one]; exact div_le_div_of_nonneg_right hB_le (le_of_lt hdposR))
     have h4 : |ea * eb| <= 1 := by rw [abs_mul]; nlinarith [abs_nonneg ea, abs_nonneg eb]
     have hsum3 : |A / (d : ℝ) * eb + B / (d : ℝ) * ea + ea * eb| <= 2 * (M : ℝ) / (d : ℝ) + 1 := by
       have : (M : ℝ) / (d : ℝ) + (M : ℝ) / (d : ℝ) = 2 * (M : ℝ) / (d : ℝ) := by ring
       linarith
     calc |mu| * |A / (d : ℝ) * eb + B / (d : ℝ) * ea + ea * eb|
         <= 1 * (2 * (M : ℝ) / (d : ℝ) + 1) := mul_le_mul hmu hsum3 (abs_nonneg _) (by norm_num)
       _ = 2 * (M : ℝ) / (d : ℝ) + 1 := one_mul _
   have hle := (abs_le.mp herr).2;linarith
 have hsum_le := sum_le_sum hterm
 refine le_trans hsum_le ?_
 rw [sum_add_distrib]
 have hmain : ∑ d ∈ Icc 1 M, ((moebius d : ℤ) : ℝ) / (d : ℝ) ^ 2 * ((Icc a1 a2).card : ℝ) * ((Icc b1 b2).card : ℝ) = moebius2Sum M * ((Icc a1 a2).card : ℝ) * ((Icc b1 b2).card : ℝ) := by
   unfold moebius2Sum;rw [sum_mul, sum_mul]
 have herr_sum : ∑ d ∈ Icc 1 M, (2 * (M : ℝ) / (d : ℝ) + 1) <= 2 * (M : ℝ) * (1 + Real.log M) + (M : ℝ) := by
   rw [sum_add_distrib, sum_const, nsmul_eq_mul, mul_one, Nat.card_Icc];have hMsub : ((M + 1 - 1 : ℕ) : ℝ) = (M : ℝ) := by simp
   rw [hMsub];have hmul : ∑ d ∈ Icc 1 M, 2 * (M : ℝ) / (d : ℝ) = 2 * (M : ℝ) * ∑ d ∈ Icc 1 M, (1 : ℝ) / (d : ℝ) := by rw [mul_sum]; apply sum_congr rfl; intro d _; ring
   rw [hmul];linarith [mul_le_mul_of_nonneg_left (harmonic_le_one_add_log M hM) (show (0 : ℝ) <= 2 * (M : ℝ) by positivity)]
 linarith
lemma moebius2Sum_bounds {N : ℕ} (hN : 1 <= N) : 0 <= moebius2Sum N /\ moebius2Sum N <= 2 := by
 constructor
 . unfold moebius2Sum
   have hI : Icc 1 N = insert 1 (Icc 2 N) := by
     ext k; simp only [mem_Icc, mem_insert]; omega
   rw [hI, sum_insert (by simp)];have h1_val : ((moebius 1 : ℤ) : ℝ) / ((1 : ℕ) : ℝ) ^ 2 = 1 := by simp
   rw [h1_val]
   have hle : -(∑ k ∈ Icc 2 N, (1 : ℝ) / (k : ℝ) ^ 2) <= ∑ k ∈ Icc 2 N, ((moebius k : ℤ) : ℝ) / (k : ℝ) ^ 2 := by
     rw [<- sum_neg_distrib];apply sum_le_sum; intro k _;have := (abs_le.mp (moebius_abs_le_one k)).1;have : -(1 / (k : ℝ) ^ 2) = (-1 : ℝ) / (k : ℝ) ^ 2 := by ring
     rw [this];exact div_le_div_of_nonneg_right (by linarith) (sq_nonneg _)
   linarith [sum_inv_sq_from_two N]
 . unfold moebius2Sum
   calc ∑ k ∈ Icc 1 N, ((moebius k : ℤ) : ℝ) / (k : ℝ) ^ 2
       <= ∑ k ∈ Icc 1 N, (1 : ℝ) / (k : ℝ) ^ 2 := by
         apply sum_le_sum; intro k _;exact div_le_div_of_nonneg_right (le_trans (le_abs_self _) (moebius_abs_le_one k)) (sq_nonneg _)
     _ <= 61 / 36 := sum_inv_sq_le_61_36 N
     _ <= 2 := by norm_num
lemma card_gcd_rect_one_side {N d a1 a2 b1 b2 : ℕ} (hd : 1 <= d) (hdN : d <= N) (ha1 : 1 <= a1) (ha2 : a2 <= N) (hb1 : 1 <= b1) (hb2 : b2 <= N) : (((Icc a1 a2 ×ˢ Icc b1 b2).filter (fun p => Nat.gcd p.1 p.2 = d)).card : ℝ) <= (moebius2Sum N / (d : ℝ) ^ 2) * ((Icc a1 a2).card : ℝ) * ((Icc b1 b2).card : ℝ) + 8 * (N : ℝ) * (1 + Real.log N) / (d : ℝ) + 2 := by
 let M := N / d
 have hM1 : 1 <= M := (Nat.one_le_div_iff (by omega)).mpr hdN
 have hmap_le : ((Icc a1 a2 ×ˢ Icc b1 b2).filter (fun p => Nat.gcd p.1 p.2 = d)).card <= ((Icc ((a1 + d - 1) / d) (a2 / d) ×ˢ Icc ((b1 + d - 1) / d) (b2 / d)).filter (fun q => Nat.Coprime q.1 q.2)).card := by
   refine card_le_card_of_injOn (fun p => (p.1 / d, p.2 / d)) ?_ ?_
   . intro p hp
     obtain ⟨hpP, hgcd⟩ := mem_filter.mp (mem_coe.mp hp);obtain ⟨hpa, hpb⟩ := mem_product.mp hpP;have haI := mem_Icc.mp hpa;have hbI := mem_Icc.mp hpb;have hd1 : d ∣ p.1 := hgcd ▸ Nat.gcd_dvd_left p.1 p.2;have hd2 : d ∣ p.2 := hgcd ▸ Nat.gcd_dvd_right p.1 p.2;have hp1eq : d * (p.1 / d) = p.1 := Nat.mul_div_cancel' hd1;have hp2eq : d * (p.2 / d) = p.2 := Nat.mul_div_cancel' hd2
     refine mem_coe.mpr (mem_filter.mpr ⟨mem_product.mpr ⟨?_, ?_⟩, ?_⟩)
     . dsimp only
       refine mem_Icc.mpr ⟨?_, Nat.div_le_div_right haI.2⟩
       exact (Nat.div_le_iff_le_mul_add_pred (by omega)).mpr (by omega)
     . dsimp only
       refine mem_Icc.mpr ⟨?_, Nat.div_le_div_right hbI.2⟩
       exact (Nat.div_le_iff_le_mul_add_pred (by omega)).mpr (by omega)
     . rw [Nat.coprime_iff_gcd_eq_one]
       have hmul : d * Nat.gcd (p.1 / d) (p.2 / d) = d := by rw [<- Nat.gcd_mul_left, hp1eq, hp2eq, hgcd]
       exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < d) (by simpa using hmul)
   . intro p1 hp1 p2 hp2 heq
     have hgcd1 := (mem_filter.mp (mem_coe.mp hp1)).2;have hgcd2 := (mem_filter.mp (mem_coe.mp hp2)).2;have h1a := Nat.mul_div_cancel' (hgcd1 ▸ Nat.gcd_dvd_left p1.1 p1.2);have h1b := Nat.mul_div_cancel' (hgcd1 ▸ Nat.gcd_dvd_right p1.1 p1.2);have h2a := Nat.mul_div_cancel' (hgcd2 ▸ Nat.gcd_dvd_left p2.1 p2.2);have h2b := Nat.mul_div_cancel' (hgcd2 ▸ Nat.gcd_dvd_right p2.1 p2.2);have hfst : p1.1 / d = p2.1 / d := congrArg Prod.fst heq;have hsnd : p1.2 / d = p2.2 / d := congrArg Prod.snd heq;exact Prod.ext (by rw [<- h1a, <- h2a, hfst]) (by rw [<- h1b, <- h2b, hsnd])
 have hA1 : 1 <= (a1 + d - 1) / d := (Nat.one_le_div_iff (by omega)).mpr (by omega);have hB1 : 1 <= (b1 + d - 1) / d := (Nat.one_le_div_iff (by omega)).mpr (by omega);have hrect := card_coprime_rect_le hM1 hA1 (Nat.div_le_div_right ha2) hB1 (Nat.div_le_div_right hb2);have h1 : (((Icc a1 a2 ×ˢ Icc b1 b2).filter (fun p => Nat.gcd p.1 p.2 = d)).card : ℝ) <= moebius2Sum M * ((Icc ((a1 + d - 1) / d) (a2 / d)).card : ℝ) * ((Icc ((b1 + d - 1) / d) (b2 / d)).card : ℝ) + 2 * (M : ℝ) * (1 + Real.log M) + (M : ℝ) := le_trans (by exact_mod_cast hmap_le) hrect
 have hmob_diff : moebius2Sum M <= moebius2Sum N + 1 / (M : ℝ) := by
   unfold moebius2Sum
   have hsub : Icc 1 N = Icc 1 M ∪ Icc (M + 1) N := by
     ext k; simp only [mem_Icc, mem_union]
     have hMN : M <= N := Nat.div_le_self N d;omega
   have hdisj : Disjoint (Icc 1 M) (Icc (M + 1) N) := by
     rw [Finset.disjoint_left]; intro k h1 h2;have := (mem_Icc.mp h1).2; have := (mem_Icc.mp h2).1; omega
   rw [hsub, sum_union hdisj]
   have htail : |∑ k ∈ Icc (M + 1) N, ((moebius k : ℤ) : ℝ) / (k : ℝ) ^ 2| <= 1 / (M : ℝ) := by
     refine le_trans (abs_sum_le_sum_abs _ _) ?_
     refine le_trans (sum_le_sum fun k _ => ?_) (sum_inv_sq_tail M N hM1)
     rw [abs_div, abs_of_nonneg (sq_nonneg (k : ℝ))];exact div_le_div_of_nonneg_right (moebius_abs_le_one k) (sq_nonneg _)
   linarith [(abs_le.mp htail).1]
 have hlen : ∀ u v : ℕ, 1 <= u -> ((Icc ((u + d - 1) / d) (v / d)).card : ℝ) <= ((Icc u v).card : ℝ) / (d : ℝ) + 1 := by
   intro u v hu1
   by_cases huv : v / d < (u + d - 1) / d
   . have : Icc ((u + d - 1) / d) (v / d) = ∅ := by
       ext x; simp only [mem_Icc, notMem_empty, iff_false]; omega
     rw [this]; simp; positivity
   . rw [Nat.card_Icc, Nat.card_Icc]
     have hdposR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
     have hv_ge_u : u <= v := by
       by_contra hlt; push Not at hlt
       have h1 : v / d < (u + d - 1) / d := by
         have : v + 1 <= u := hlt;have h2 : (v / d) * d <= v := Nat.div_mul_le_self v d;have h3 : (v / d + 1) * d <= u + d - 1 := by rw [add_mul, one_mul]; omega
         have h4 : v / d + 1 <= (u + d - 1) / d := (Nat.le_div_iff_mul_le (by omega)).mpr h3;omega
       omega
     have hmul : (v / d - (u + d - 1) / d) * d <= v + 1 - u := by
       have h1 : (v / d) * d <= v := Nat.div_mul_le_self v d
       have h2 : u <= ((u + d - 1) / d) * d := by
         have := Nat.lt_div_mul_add (a := u + d - 1) (b := d) (by omega);omega
       rw [Nat.sub_mul]; omega
     have hdiv : ((v / d - (u + d - 1) / d : ℕ) : ℝ) <= ((v + 1 - u : ℕ) : ℝ) / (d : ℝ) := by rw [le_div_iff₀ hdposR]; exact_mod_cast hmul
     have hsub : v / d + 1 - (u + d - 1) / d = (v / d - (u + d - 1) / d) + 1 := by omega
     rw [hsub, Nat.cast_add, Nat.cast_one];linarith
 have hdposR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
 have hMposR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM1
 have hM_le : (M : ℝ) <= (N : ℝ) / (d : ℝ) := by rw [le_div_iff₀ hdposR]; exact_mod_cast Nat.div_mul_le_self N d
 have hN_ge1 : (1 : ℝ) <= (N : ℝ) := by exact_mod_cast (by omega : 1 <= N)
 have hlogM : Real.log (M : ℝ) <= Real.log (N : ℝ) := Real.log_le_log hMposR (by exact_mod_cast Nat.div_le_self N d);have hlogN_nn : 0 <= Real.log (N : ℝ) := Real.log_nonneg hN_ge1;have hmobN_ge0 : 0 <= moebius2Sum N := (moebius2Sum_bounds (by omega)).1;have hmobN_pos_ub : moebius2Sum N <= 2 := (moebius2Sum_bounds (by omega)).2
 set A : ℝ := ((Icc a1 a2).card : ℝ)
 set B : ℝ := ((Icc b1 b2).card : ℝ)
 have hA_le : A <= (N : ℝ) := by dsimp only [A]; rw [Nat.card_Icc]; exact_mod_cast (by omega : a2 + 1 - a1 <= N)
 have hB_le : B <= (N : ℝ) := by dsimp only [B]; rw [Nat.card_Icc]; exact_mod_cast (by omega : b2 + 1 - b1 <= N)
 have hA0 : 0 <= A := Nat.cast_nonneg _;have hB0 : 0 <= B := Nat.cast_nonneg _
 set A' : ℝ := ((Icc ((a1 + d - 1) / d) (a2 / d)).card : ℝ)
 set B' : ℝ := ((Icc ((b1 + d - 1) / d) (b2 / d)).card : ℝ)
 have hA'le : A' <= (M : ℝ) := by
   dsimp only [A']; rw [Nat.card_Icc]; exact_mod_cast (by
     have := Nat.div_le_div_right (c := d) ha2; omega : a2 / d + 1 - (a1 + d - 1) / d <= M)
 have hB'le : B' <= (M : ℝ) := by
   dsimp only [B']; rw [Nat.card_Icc]; exact_mod_cast (by
     have := Nat.div_le_div_right (c := d) hb2; omega : b2 / d + 1 - (b1 + d - 1) / d <= M)
 have h1' : moebius2Sum M * A' * B' <= moebius2Sum N * A' * B' + (M : ℝ) := by
   have hprod : A' * B' <= (M : ℝ) * (M : ℝ) := mul_le_mul hA'le hB'le (Nat.cast_nonneg _) (by positivity)
   have h1a : (1 / (M : ℝ)) * (A' * B') <= (M : ℝ) := by
     have : (1 / (M : ℝ)) * ((M : ℝ) * (M : ℝ)) = (M : ℝ) := by field_simp
     nlinarith [mul_le_mul_of_nonneg_left hprod (show (0 : ℝ) <= 1 / (M : ℝ) by positivity)]
   have h2a : moebius2Sum M * (A' * B') <= (moebius2Sum N + 1 / (M : ℝ)) * (A' * B') := mul_le_mul_of_nonneg_right hmob_diff (by positivity);nlinarith
 have hA'B' : A' * B' <= (A / (d : ℝ) + 1) * (B / (d : ℝ) + 1) := mul_le_mul (hlen a1 a2 ha1) (hlen b1 b2 hb1) (Nat.cast_nonneg _) (by positivity)
 have h2' : moebius2Sum N * A' * B' <= (moebius2Sum N / (d : ℝ) ^ 2) * A * B + 2 * (N : ℝ) / (d : ℝ) * 2 + 2 := by
   have hmul : moebius2Sum N * (A' * B') <= moebius2Sum N * ((A / (d : ℝ) + 1) * (B / (d : ℝ) + 1)) := mul_le_mul_of_nonneg_left hA'B' hmobN_ge0;have hexp : moebius2Sum N * ((A / (d : ℝ) + 1) * (B / (d : ℝ) + 1)) = (moebius2Sum N / (d : ℝ) ^ 2) * A * B + moebius2Sum N * (A / (d : ℝ) + B / (d : ℝ) + 1) := by ring
   have hAB : A / (d : ℝ) + B / (d : ℝ) + 1 <= 2 * (N : ℝ) / (d : ℝ) + 1 := by
     have h1a := div_le_div_of_nonneg_right hA_le (le_of_lt hdposR);have h1b := div_le_div_of_nonneg_right hB_le (le_of_lt hdposR);have h2eq : 2 * (N : ℝ) / (d : ℝ) = (N : ℝ) / (d : ℝ) + (N : ℝ) / (d : ℝ) := by ring
     linarith
   have h3 : moebius2Sum N * (A / (d : ℝ) + B / (d : ℝ) + 1) <= 2 * (2 * (N : ℝ) / (d : ℝ) + 1) := mul_le_mul hmobN_pos_ub hAB (by positivity) (by norm_num);linarith
 have hMlog : 2 * (M : ℝ) * (1 + Real.log M) + (M : ℝ) + (M : ℝ) <= 4 * (N : ℝ) * (1 + Real.log N) / (d : ℝ) := by
   have h1a : 2 * (M : ℝ) * (1 + Real.log M) <= 2 * ((N : ℝ) / (d : ℝ)) * (1 + Real.log N) := mul_le_mul (mul_le_mul_of_nonneg_left hM_le (by norm_num)) (by linarith) (by linarith [Real.log_nonneg (show (1 : ℝ) <= (M : ℝ) by exact_mod_cast hM1)]) (by positivity);have h2a : (M : ℝ) + (M : ℝ) <= 2 * ((N : ℝ) / (d : ℝ)) * (1 + Real.log N) := by nlinarith [hM_le, hlogN_nn]
   have hrew : 4 * (N : ℝ) * (1 + Real.log N) / (d : ℝ) = 2 * ((N : ℝ) / (d : ℝ)) * (1 + Real.log N) + 2 * ((N : ℝ) / (d : ℝ)) * (1 + Real.log N) := by ring
   linarith
 have h4N : 2 * (N : ℝ) / (d : ℝ) * 2 <= 4 * (N : ℝ) * (1 + Real.log N) / (d : ℝ) := by
   have : 4 * (N : ℝ) * (1 + Real.log N) / (d : ℝ) = 2 * (N : ℝ) / (d : ℝ) * 2 + 4 * (N : ℝ) * Real.log N / (d : ℝ) := by ring
   have hnn : 0 <= 4 * (N : ℝ) * Real.log N / (d : ℝ) := by positivity
   linarith
 have hcomb : 4 * (N : ℝ) * (1 + Real.log N) / (d : ℝ) + 4 * (N : ℝ) * (1 + Real.log N) / (d : ℝ) = 8 * (N : ℝ) * (1 + Real.log N) / (d : ℝ) := by ring
 exact le_trans h1 (by linarith [h1', h2', hMlog, h4N, hcomb])
lemma coprime_density_of_div_bound_aux {M : ℕ} {T : Finset (ℕ × ℕ)} (P : Finset ℕ) (hP_mem : ∀ q < 32, q.Prime -> q ∈ P) (hP_sub : ∀ m ∈ P, 1 <= m /\ m <= 31) (hP_sum : ∑ m ∈ P, (1 : ℝ) / (m : ℝ) ^ 2 <= 447 / 1000) (hbd1 : ∀ p ∈ T, 1 <= p.1 /\ p.1 <= M) (hdiv_bound : ∀ m : ℕ, 1 <= m -> m ^ 2 * (T.filter (fun p => m ∣ p.1 /\ m ∣ p.2)).card <= T.card) : (52 / 100 : ℝ) * (T.card : ℝ) <= ((T.filter (fun p => Nat.Coprime p.1 p.2)).card : ℝ) := by
 let B := P ∪ Icc 32 M
 have hcov : T.filter (fun p => ¬ Nat.Coprime p.1 p.2) ⊆ B.biUnion (fun m => T.filter (fun p => m ∣ p.1 /\ m ∣ p.2)) := by
   intro p hp;have hpT : p ∈ T := (mem_filter.mp hp).1;have hncop : ¬ Nat.Coprime p.1 p.2 := (mem_filter.mp hp).2;rw [Nat.coprime_iff_gcd_eq_one] at hncop;obtain ⟨q, hqpr, hqdvd⟩ := Nat.exists_prime_and_dvd hncop;have hq1 : q ∣ p.1 := dvd_trans hqdvd (Nat.gcd_dvd_left p.1 p.2);have hq2 : q ∣ p.2 := dvd_trans hqdvd (Nat.gcd_dvd_right p.1 p.2);have hp1I := hbd1 p hpT;have hqle : q <= M := le_trans (Nat.le_of_dvd (by omega) hq1) hp1I.2
   refine mem_biUnion.mpr ⟨q, ?_, mem_filter.mpr ⟨hpT, hq1, hq2⟩⟩
   by_cases hq32 : 32 <= q
   . exact mem_union_right _ (mem_Icc.mpr ⟨hq32, hqle⟩)
   . exact mem_union_left _ (hP_mem q (by omega) hqpr)
 have hbad : ((T.filter (fun p => ¬ Nat.Coprime p.1 p.2)).card : ℝ) <= (48 / 100 : ℝ) * (T.card : ℝ) := by
   have h1 : ((T.filter (fun p => ¬ Nat.Coprime p.1 p.2)).card : ℝ) <= ∑ m ∈ B, ((T.filter (fun p => m ∣ p.1 /\ m ∣ p.2)).card : ℝ) := by exact_mod_cast le_trans (card_le_card hcov) card_biUnion_le
   refine le_trans h1 ?_
   have h2 : ∑ m ∈ B, ((T.filter (fun p => m ∣ p.1 /\ m ∣ p.2)).card : ℝ) <= ∑ m ∈ B, (T.card : ℝ) / (m : ℝ) ^ 2 := by
     apply sum_le_sum;intro m hm
     have hm1 : 1 <= m := by
       rcases mem_union.mp hm with h | h
       . exact (hP_sub m h).1
       . have := (mem_Icc.mp h).1; omega
     have hleR : ((m : ℝ) ^ 2) * ((T.filter (fun p => m ∣ p.1 /\ m ∣ p.2)).card : ℝ) <= (T.card : ℝ) := by exact_mod_cast hdiv_bound m hm1
     have hmpos : (0 : ℝ) < (m : ℝ) ^ 2 := by positivity
     rw [le_div_iff₀ hmpos]; linarith
   refine le_trans h2 ?_
   have hdisj : Disjoint P (Icc 32 M) := by
     rw [Finset.disjoint_left]; intro m h1 h2;have := (hP_sub m h1).2;have := (mem_Icc.mp h2).1;omega
   have hsum_eq : ∑ m ∈ B, (T.card : ℝ) / (m : ℝ) ^ 2 = (T.card : ℝ) * ((∑ m ∈ P, (1 : ℝ) / (m : ℝ) ^ 2) + (∑ m ∈ Icc 32 M, (1 : ℝ) / (m : ℝ) ^ 2)) := by
     rw [sum_union hdisj, mul_add, mul_sum, mul_sum]
     congr 1 <;> (apply sum_congr rfl; intro m _; ring)
   rw [hsum_eq];have hTsum := sum_inv_sq_tail 31 M (by norm_num);have htot : (∑ m ∈ P, (1 : ℝ) / (m : ℝ) ^ 2) + (∑ m ∈ Icc 32 M, (1 : ℝ) / (m : ℝ) ^ 2) <= 48 / 100 := by linarith [hP_sum, hTsum]
   have hmul := mul_le_mul_of_nonneg_left htot (Nat.cast_nonneg (α := ℝ) T.card);linarith
 have hpart : (T.filter (fun p => Nat.Coprime p.1 p.2)).card + (T.filter (fun p => ¬ Nat.Coprime p.1 p.2)).card = T.card := by rw [<- card_union_of_disjoint (disjoint_filter_filter_not _ _ _), filter_union_filter_not_eq]
 have hpartR : ((T.filter (fun p => Nat.Coprime p.1 p.2)).card : ℝ) + ((T.filter (fun p => ¬ Nat.Coprime p.1 p.2)).card : ℝ) = (T.card : ℝ) := by exact_mod_cast hpart
 linarith
lemma coprime_density_of_div_bound {M : ℕ} {T : Finset (ℕ × ℕ)} (hbd1 : ∀ p ∈ T, 1 <= p.1 /\ p.1 <= M) (hdiv_bound : ∀ m : ℕ, 1 <= m -> m ^ 2 * (T.filter (fun p => m ∣ p.1 /\ m ∣ p.2)).card <= T.card) : (52 / 100 : ℝ) * (T.card : ℝ) <= ((T.filter (fun p => Nat.Coprime p.1 p.2)).card : ℝ) := coprime_density_of_div_bound_aux {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31} (by decide) (by decide) (by norm_num) hbd1 hdiv_bound
lemma downward_closed_coprime_rect {L R : ℕ} {T : Finset (ℕ × ℕ)} (hsub : T ⊆ Icc 1 L ×ˢ Icc 1 R) (hdown : ∀ i j i' j', (i, j) ∈ T -> 1 <= i' -> i' <= i -> 1 <= j' -> j' <= j -> (i', j') ∈ T) : (52 / 100 : ℝ) * (T.card : ℝ) <= ((T.filter (fun p => Nat.Coprime p.1 p.2)).card : ℝ) := by
 refine coprime_density_of_div_bound (M := L) (fun p hp => mem_Icc.mp (mem_product.mp (hsub hp)).1) ?_
 intro m hm
 let Tm := T.filter (fun p => m ∣ p.1 /\ m ∣ p.2)
 let U := Tm ×ˢ (range m ×ˢ range m)
 have hmaps : ∀ x ∈ U, (x.1.1 - x.2.1, x.1.2 - x.2.2) ∈ T := by
   intro x hx;obtain ⟨hx1, hx2⟩ := mem_product.mp hx;obtain ⟨hxT, hm1, hm2⟩ := mem_filter.mp hx1;obtain ⟨hu, hv⟩ := mem_product.mp hx2;have hult : x.2.1 < m := mem_range.mp hu;have hvlt : x.2.2 < m := mem_range.mp hv;have h1pos : 1 <= x.1.1 := (mem_Icc.mp (mem_product.mp (hsub hxT)).1).1;have h2pos : 1 <= x.1.2 := (mem_Icc.mp (mem_product.mp (hsub hxT)).2).1;have h1ge : m <= x.1.1 := Nat.le_of_dvd (by omega) hm1;have h2ge : m <= x.1.2 := Nat.le_of_dvd (by omega) hm2;exact hdown x.1.1 x.1.2 (x.1.1 - x.2.1) (x.1.2 - x.2.2) hxT (by omega) (Nat.sub_le _ _) (by omega) (Nat.sub_le _ _)
 have hinj : Set.InjOn (fun x : (ℕ × ℕ) × (ℕ × ℕ) => (x.1.1 - x.2.1, x.1.2 - x.2.2)) (U : Set ((ℕ × ℕ) × (ℕ × ℕ))) := by
   intro x hx y hy heq;obtain ⟨hx1, hx2⟩ := mem_product.mp (mem_coe.mp hx);obtain ⟨hy1, hy2⟩ := mem_product.mp (mem_coe.mp hy);obtain ⟨hxT, hxm1, hxm2⟩ := mem_filter.mp hx1;obtain ⟨hyT, hym1, hym2⟩ := mem_filter.mp hy1;obtain ⟨hxu, hxv⟩ := mem_product.mp hx2;obtain ⟨hyu, hyv⟩ := mem_product.mp hy2;have hxult := mem_range.mp hxu;have hxvlt := mem_range.mp hxv;have hyult := mem_range.mp hyu;have hyvlt := mem_range.mp hyv;have hfst : x.1.1 - x.2.1 = y.1.1 - y.2.1 := congrArg Prod.fst heq;have hsnd : x.1.2 - x.2.2 = y.1.2 - y.2.2 := congrArg Prod.snd heq
   have h1pos_x : m <= x.1.1 := Nat.le_of_dvd (by have := (mem_Icc.mp (mem_product.mp (hsub hxT)).1).1; omega) hxm1;have h1pos_y : m <= y.1.1 := Nat.le_of_dvd (by have := (mem_Icc.mp (mem_product.mp (hsub hyT)).1).1; omega) hym1;have h2pos_x : m <= x.1.2 := Nat.le_of_dvd (by have := (mem_Icc.mp (mem_product.mp (hsub hxT)).2).1; omega) hxm2;have h2pos_y : m <= y.1.2 := Nat.le_of_dvd (by have := (mem_Icc.mp (mem_product.mp (hsub hyT)).2).1; omega) hym2
   have huniq : ∀ a b u v : ℕ, m ∣ a -> m ∣ b -> u < m -> v < m -> m <= a -> m <= b -> a - u = b - v -> a = b /\ u = v := by
     intro a b u v hma hmb hu hv ha hb hsub';obtain ⟨ka, rfl⟩ := hma;obtain ⟨kb, rfl⟩ := hmb
     have hkeq : ka = kb := by
       by_contra hne
       rcases lt_or_gt_of_ne hne with h | h
       . have : m * (ka + 1) <= m * kb := Nat.mul_le_mul_left m h
         rw [mul_add, mul_one] at this; omega
       . have : m * (kb + 1) <= m * ka := Nat.mul_le_mul_left m h
         rw [mul_add, mul_one] at this; omega
     subst hkeq; exact ⟨rfl, by omega⟩
   have ⟨h1a, h1u⟩ := huniq x.1.1 y.1.1 x.2.1 y.2.1 hxm1 hym1 hxult hyult h1pos_x h1pos_y hfst;have ⟨h2a, h2v⟩ := huniq x.1.2 y.1.2 x.2.2 y.2.2 hxm2 hym2 hxvlt hyvlt h2pos_x h2pos_y hsnd;exact Prod.ext (Prod.ext h1a h2a) (Prod.ext h1u h2v)
 have hcard := card_le_card_of_injOn _ (fun x hx => mem_coe.mpr (hmaps x (mem_coe.mp hx))) hinj;rw [card_product, card_product, card_range] at hcard;have hmul : Tm.card * (m * m) = m ^ 2 * Tm.card := by ring
 dsimp only [Tm] at hcard hmul;omega
lemma coprime_pairs_triangle_ge (L : ℕ) : (52 / 100 : ℝ) * ((L * (L - 1) / 2 : ℕ) : ℝ) <= ((((Icc 1 L ×ˢ Icc 1 L).filter (fun p => p.1 < p.2 /\ Nat.Coprime p.1 p.2)).card) : ℝ) := by
 have htri_card : ∀ n : ℕ, ((Icc 1 n ×ˢ Icc 1 n).filter (fun p => p.1 < p.2)).card = n * (n - 1) / 2 := by
   intro n
   have hbij : ((Icc 1 n ×ˢ Icc 1 n).filter (fun p => p.1 < p.2)).card = ((Icc 1 n).powersetCard 2).card := by
     refine card_bij (fun p _ => ({p.1, p.2} : Finset ℕ)) ?_ ?_ ?_
     . intro p hp
       obtain ⟨hpP, hlt⟩ := mem_filter.mp hp;obtain ⟨h1, h2⟩ := mem_product.mp hpP
       refine mem_powersetCard.mpr ⟨?_, card_pair (by omega)⟩
       intro x hx; rcases mem_insert.mp hx with rfl | hx'
       . exact h1
       . rw [mem_singleton.mp hx']; exact h2
     . intro p1 hp1 p2 hp2 heq
       have hlt1 := (mem_filter.mp hp1).2;have hlt2 := (mem_filter.mp hp2).2;have h1mem : p1.1 ∈ ({p2.1, p2.2} : Finset ℕ) := by rw [<- heq]; simp
       have h2mem : p1.2 ∈ ({p2.1, p2.2} : Finset ℕ) := by rw [<- heq]; simp
       have h3mem : p2.1 ∈ ({p1.1, p1.2} : Finset ℕ) := by rw [heq]; simp
       have h4mem : p2.2 ∈ ({p1.1, p1.2} : Finset ℕ) := by rw [heq]; simp
       simp only [mem_insert, mem_singleton] at h1mem h2mem h3mem h4mem;exact Prod.ext (by omega) (by omega)
     . intro s hs
       obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp hs;obtain ⟨a, b, hab, rfl⟩ := card_eq_two.mp hcard
       rcases lt_or_gt_of_ne hab with hlt | hgt
       . exact ⟨(a, b), mem_filter.mpr ⟨mem_product.mpr ⟨hsub (by simp), hsub (by simp)⟩, hlt⟩, rfl⟩
       . exact ⟨(b, a), mem_filter.mpr ⟨mem_product.mpr ⟨hsub (by simp), hsub (by simp)⟩, hgt⟩, by ext x; simp [or_comm]⟩
   rw [hbij, card_powersetCard, Nat.card_Icc, Nat.add_sub_cancel, Nat.choose_two_right]
 let Tri := (Icc 1 L ×ˢ Icc 1 L).filter (fun p => p.1 < p.2)
 have hTri_card : Tri.card = L * (L - 1) / 2 := htri_card L
 have hfeq : Tri.filter (fun p => Nat.Coprime p.1 p.2) = (Icc 1 L ×ˢ Icc 1 L).filter (fun p => p.1 < p.2 /\ Nat.Coprime p.1 p.2) := by
   ext p; simp only [Tri, mem_filter]; tauto
 rw [<- hTri_card, <- hfeq]
 refine coprime_density_of_div_bound (M := L) (fun p hp => mem_Icc.mp (mem_product.mp (mem_filter.mp hp).1).1) ?_
 intro m hm
 set q := L / m
 have hTm_le : (Tri.filter (fun p => m ∣ p.1 /\ m ∣ p.2)).card <= q * (q - 1) / 2 := by
   rw [<- htri_card q]
   refine card_le_card_of_injOn (fun p => (p.1 / m, p.2 / m)) ?_ ?_
   . intro p hp
     obtain ⟨hpTri, hm1, hm2⟩ := mem_filter.mp (mem_coe.mp hp);obtain ⟨hpP, hlt⟩ := mem_filter.mp hpTri;obtain ⟨h1, h2⟩ := mem_product.mp hpP;have h1I := mem_Icc.mp h1;have h2I := mem_Icc.mp h2;have hp1 := Nat.mul_div_cancel' hm1;have hp2 := Nat.mul_div_cancel' hm2
     refine mem_coe.mpr (mem_filter.mpr ⟨mem_product.mpr ⟨?_, ?_⟩, ?_⟩)
     . dsimp only
       exact mem_Icc.mpr ⟨(Nat.one_le_div_iff (by omega)).mpr (Nat.le_of_dvd (by omega) hm1), Nat.div_le_div_right h1I.2⟩
     . dsimp only
       exact mem_Icc.mpr ⟨(Nat.one_le_div_iff (by omega)).mpr (Nat.le_of_dvd (by omega) hm2), Nat.div_le_div_right h2I.2⟩
     . dsimp only
       by_contra hge;have : m * (p.2 / m) <= m * (p.1 / m) := Nat.mul_le_mul_left m (by omega);omega
   . intro p1 hp1 p2 hp2 heq
     obtain ⟨-, hm1a, hm1b⟩ := mem_filter.mp (mem_coe.mp hp1);obtain ⟨-, hm2a, hm2b⟩ := mem_filter.mp (mem_coe.mp hp2);have hfst : p1.1 / m = p2.1 / m := congrArg Prod.fst heq;have hsnd : p1.2 / m = p2.2 / m := congrArg Prod.snd heq;exact Prod.ext (by rw [<- Nat.mul_div_cancel' hm1a, <- Nat.mul_div_cancel' hm2a, hfst]) (by rw [<- Nat.mul_div_cancel' hm1b, <- Nat.mul_div_cancel' hm2b, hsnd])
 rw [hTri_card]
 refine le_trans (Nat.mul_le_mul_left (m ^ 2) hTm_le) ?_
 have hmq : m * q <= L := Nat.mul_div_le L m
 have heven_mul : ∀ n : ℕ, 2 ∣ n * (n - 1) := by
   intro n
   rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
   . rw [hk]; exact ⟨k * (k + k - 1), by ring⟩
   . rw [hk]
     have hsub : 2 * k + 1 - 1 = 2 * k := by omega
     rw [hsub]; exact ⟨(2 * k + 1) * k, by ring⟩
 rcases Nat.eq_zero_or_pos q with hq0 | hqpos
 . rw [hq0]; simp
 . have h2dvd := heven_mul q
   have h2L := heven_mul L
   have hineq : m ^ 2 * (q * (q - 1)) <= L * (L - 1) := by
     have h1 : m * (q - 1) <= m * q - 1 := by
       rw [Nat.mul_sub_left_distrib, mul_one];have : 1 <= m * q := Nat.mul_pos (by omega) hqpos;omega
     calc m ^ 2 * (q * (q - 1)) = (m * q) * (m * (q - 1)) := by ring
       _ <= L * (L - 1) := Nat.mul_le_mul hmq (le_trans h1 (Nat.sub_le_sub_right hmq 1))
   have hmul2 : 2 * (m ^ 2 * (q * (q - 1) / 2)) <= 2 * (L * (L - 1) / 2) := by
     rw [Nat.mul_div_cancel' h2L];have : 2 * (m ^ 2 * (q * (q - 1) / 2)) = m ^ 2 * (2 * (q * (q - 1) / 2)) := by ring
     rw [this, Nat.mul_div_cancel' h2dvd];exact hineq
   omega
lemma sum_card_divisors_le {N : ℕ} (hN : 1 <= N) : ∑ m ∈ Icc 1 N, (m.divisors.card : ℝ) <= (N : ℝ) * (1 + Real.log N) := by
 have hswap : (∑ m ∈ Icc 1 N, m.divisors.card) = ∑ d ∈ Icc 1 N, ((Icc 1 N).filter (fun m => d ∣ m)).card := by
   have h1 : ∀ m ∈ Icc 1 N, m.divisors.card = ∑ d ∈ Icc 1 N, if d ∣ m then 1 else 0 := by
     intro m hm;have hm1 := (mem_Icc.mp hm).1;have hmN := (mem_Icc.mp hm).2;rw [<- card_filter]
     congr 1; ext d
     simp only [Nat.mem_divisors, mem_filter, mem_Icc]
     constructor
     . rintro ⟨hd, -⟩
       exact ⟨⟨Nat.pos_of_dvd_of_pos hd (by omega), le_trans (Nat.le_of_dvd (by omega) hd) hmN⟩, hd⟩
     . rintro ⟨-, hd⟩
       exact ⟨hd, by omega⟩
   rw [sum_congr rfl h1, sum_comm]
   refine sum_congr rfl fun d _ => ?_
   rw [sum_boole, Nat.cast_id]
 have hcnt : ∀ d ∈ Icc 1 N, ((Icc 1 N).filter (fun m => d ∣ m)).card = N / d := by
   intro d hd;have hd1 := (mem_Icc.mp hd).1;have hcardI : (Icc 1 (N / d)).card = N / d := by rw [Nat.card_Icc, Nat.add_sub_cancel]
   rw [<- hcardI]
   refine card_bij (fun x _ => x / d) ?_ ?_ ?_
   . intro x hx
     obtain ⟨hxI, hdx⟩ := mem_filter.mp hx;have hx1 := (mem_Icc.mp hxI).1;have hxN := (mem_Icc.mp hxI).2;exact mem_Icc.mpr ⟨(Nat.one_le_div_iff (by omega)).mpr (Nat.le_of_dvd (by omega) hdx), Nat.div_le_div_right hxN⟩
   . intro x1 hx1 x2 hx2 hq
     have h1 := Nat.mul_div_cancel' (mem_filter.mp hx1).2;have h2 := Nat.mul_div_cancel' (mem_filter.mp hx2).2;have hq' : x1 / d = x2 / d := hq;rw [hq'] at h1; omega
   . intro k hk
     obtain ⟨hk1, hkN⟩ := mem_Icc.mp hk;have hkdv : d * k <= N := le_trans (Nat.mul_le_mul_left d hkN) (Nat.mul_div_le N d)
     refine ⟨d * k, mem_filter.mpr ⟨mem_Icc.mpr ⟨by nlinarith, hkdv⟩, dvd_mul_right d k⟩, Nat.mul_div_cancel_left k (by omega)⟩
 have hR : ∑ m ∈ Icc 1 N, (m.divisors.card : ℝ) = ∑ d ∈ Icc 1 N, ((N / d : ℕ) : ℝ) := by
   have hN' : (∑ m ∈ Icc 1 N, m.divisors.card) = ∑ d ∈ Icc 1 N, (N / d) := by rw [hswap]; exact sum_congr rfl hcnt
   exact_mod_cast hN'
 rw [hR]
 have hle : ∑ d ∈ Icc 1 N, ((N / d : ℕ) : ℝ) <= ∑ d ∈ Icc 1 N, (N : ℝ) * ((1 : ℝ) / (d : ℝ)) := by
   apply sum_le_sum; intro d hd;have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by have := (mem_Icc.mp hd).1; omega : 0 < d)
   have hdiv : ((N / d : ℕ) : ℝ) <= (N : ℝ) / (d : ℝ) := by rw [le_div_iff₀ hdpos]; exact_mod_cast Nat.div_mul_le_self N d
   linarith [show (N : ℝ) * ((1 : ℝ) / (d : ℝ)) = (N : ℝ) / (d : ℝ) by ring]
 refine le_trans hle ?_
 rw [<- mul_sum];exact mul_le_mul_of_nonneg_left (harmonic_le_one_add_log N hN) (Nat.cast_nonneg N)
lemma szabo_lemma_3_2 {N c : ℕ} (hN : 1 <= N) (hc : c ∈ Icc 1 N) {H : Finset (Finset ℕ)} (hsub : ∀ S ∈ H, S ⊆ Icc 1 N) (xH yH : Finset ℕ -> ℕ) (hdelta : ∀ S ∈ H, IsDeltaTriplet H S c (xH S) (yH S)) (hfill : ∀ S ∈ H,
     let g := Nat.gcd (distNat c (xH S)) (distNat c (yH S))
     ∀ w, min c (min (xH S) (yH S)) <= w -> w <= max c (max (xH S) (yH S)) -> w % g = c % g -> w ∈ S) :
   (H.card : ℝ) <= (N : ℝ) * (2 + Real.log N) := by
 let gS : Finset ℕ -> ℕ := fun S => Nat.gcd (distNat c (xH S)) (distNat c (yH S))
 let loS : Finset ℕ -> ℕ := fun S => min c (min (xH S) (yH S))
 let hiS : Finset ℕ -> ℕ := fun S => max c (max (xH S) (yH S))
 have hg_bounds : ∀ S ∈ H, 1 <= gS S /\ gS S <= N := by
   intro S hS;have hd := hdelta S hS;have hpos : 0 < distNat c (xH S) := distNat_pos_of_ne hd.2.2.2.1;have hgp : 0 < gS S := Nat.gcd_pos_of_pos_left _ hpos;have hxI := mem_Icc.mp (hsub S hS hd.2.1);have hcI := mem_Icc.mp hc;have hdist : distNat c (xH S) <= N := by unfold distNat; omega
   exact ⟨hgp, le_trans (Nat.le_of_dvd hpos (Nat.gcd_dvd_left _ _)) hdist⟩
 have hcov : H ⊆ (Icc 1 N).biUnion (fun d => H.filter (fun S => gS S = d)) := by
   intro S hS;obtain ⟨h1, h2⟩ := hg_bounds S hS;exact mem_biUnion.mpr ⟨gS S, mem_Icc.mpr ⟨h1, h2⟩, mem_filter.mpr ⟨hS, rfl⟩⟩
 have hcard_le : (H.card : ℝ) <= ∑ d ∈ Icc 1 N, ((H.filter (fun S => gS S = d)).card : ℝ) := by exact_mod_cast le_trans (card_le_card hcov) card_biUnion_le
 have hmod_xy : ∀ S ∈ H, xH S % gS S = c % gS S /\ yH S % gS S = c % gS S := by
   intro S hS;have h1 : gS S ∣ distNat c (xH S) := Nat.gcd_dvd_left _ _;have h2 : gS S ∣ distNat c (yH S) := Nat.gcd_dvd_right _ _
   have hmod_of_dvd : ∀ a b d : ℕ, d ∣ distNat a b -> b % d = a % d := by
     intro a b d hdvd;unfold distNat at hdvd
     rcases le_total a b with hle | hle
     . rw [max_eq_right hle, min_eq_left hle] at hdvd
       exact ((Nat.modEq_iff_dvd' hle).mpr hdvd).symm
     . rw [max_eq_left hle, min_eq_right hle] at hdvd
       exact (Nat.modEq_iff_dvd' hle).mpr hdvd
   exact ⟨hmod_of_dvd c (xH S) (gS S) h1, hmod_of_dvd c (yH S) (gS S) h2⟩
 have hfixed : ∀ d ∈ Icc 1 N, ((H.filter (fun S => gS S = d)).card : ℝ) <= (N : ℝ) / (d : ℝ) + 1 := by
   intro d hd;have hd1 : 1 <= d := (mem_Icc.mp hd).1
   have hmaps : ∀ S ∈ H.filter (fun S => gS S = d), (c - loS S) / d ∈ range (N / d + 1) := by
     intro S hS;have hSH := (mem_filter.mp hS).1;have hcI := mem_Icc.mp hc;have hlo_le : loS S <= c := min_le_left _ _;exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (by omega)))
   have hinj : Set.InjOn (fun S => (c - loS S) / d) ((H.filter (fun S => gS S = d)) : Set (Finset ℕ)) := by
     intro S hS T hT heq;have hSm := mem_filter.mp (mem_coe.mp hS);have hTm := mem_filter.mp (mem_coe.mp hT);have hSH := hSm.1; have hgS := hSm.2;have hTH := hTm.1; have hgT := hTm.2
     have hlo_mod : ∀ U ∈ H, loS U % gS U = c % gS U := by
       intro U hU;have hm := hmod_xy U hU;dsimp only [loS]
       rcases le_total (xH U) (yH U) with h1 | h1
       . rw [min_eq_left h1]
         rcases le_total c (xH U) with h2 | h2
         . rw [min_eq_left h2]
         . rw [min_eq_right h2]; exact hm.1
       . rw [min_eq_right h1]
         rcases le_total c (yH U) with h2 | h2
         . rw [min_eq_left h2]
         . rw [min_eq_right h2]; exact hm.2
     have hmodS : loS S % d = c % d := by rw [<- hgS]; exact hlo_mod S hSH
     have hmodT : loS T % d = c % d := by rw [<- hgT]; exact hlo_mod T hTH
     have hdvdS : d ∣ c - loS S := (Nat.modEq_iff_dvd' (min_le_left _ _)).mp hmodS;have hdvdT : d ∣ c - loS T := (Nat.modEq_iff_dvd' (min_le_left _ _)).mp hmodT;have h1 := Nat.div_mul_cancel hdvdS;have h2 := Nat.div_mul_cancel hdvdT;have heq' : (c - loS S) / d = (c - loS T) / d := heq;rw [heq'] at h1
     have hlo_eq : loS S = loS T := by
       have : loS S <= c := min_le_left _ _;have : loS T <= c := min_le_left _ _;omega
     by_contra hST
     rcases le_total (hiS S) (hiS T) with hhi | hhi
     . exfalso
       have hdt := (hdelta S hSH).2.2.2.2.2.2 T hTH (Ne.symm hST);apply hdt
       refine ⟨(hdelta T hTH).1, ?_, ?_⟩
       . have hxmod : xH S % gS T = c % gS T := by rw [hgT, <- hgS]; exact (hmod_xy S hSH).1
         exact hfill T hTH (xH S) (by dsimp only [loS] at hlo_eq ⊢; omega) (by dsimp only [hiS] at hhi ⊢; omega) hxmod
       . have hymod : yH S % gS T = c % gS T := by rw [hgT, <- hgS]; exact (hmod_xy S hSH).2
         exact hfill T hTH (yH S) (by dsimp only [loS] at hlo_eq ⊢; omega) (by dsimp only [hiS] at hhi ⊢; omega) hymod
     . exfalso
       have hdt := (hdelta T hTH).2.2.2.2.2.2 S hSH hST;apply hdt
       refine ⟨(hdelta S hSH).1, ?_, ?_⟩
       . have hxmod : xH T % gS S = c % gS S := by rw [hgS, <- hgT]; exact (hmod_xy T hTH).1
         exact hfill S hSH (xH T) (by dsimp only [loS] at hlo_eq ⊢; omega) (by dsimp only [hiS] at hhi ⊢; omega) hxmod
       . have hymod : yH T % gS S = c % gS S := by rw [hgS, <- hgT]; exact (hmod_xy T hTH).2
         exact hfill S hSH (yH T) (by dsimp only [loS] at hlo_eq ⊢; omega) (by dsimp only [hiS] at hhi ⊢; omega) hymod
   have hle := card_le_card_of_injOn (fun S => (c - loS S) / d) (fun S hS => mem_coe.mpr (hmaps S (mem_coe.mp hS))) hinj;rw [card_range] at hle;have hleR : ((H.filter (fun S => gS S = d)).card : ℝ) <= ((N / d : ℕ) : ℝ) + 1 := by exact_mod_cast hle
   have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
   have hdiv : ((N / d : ℕ) : ℝ) <= (N : ℝ) / (d : ℝ) := by rw [le_div_iff₀ hdpos]; exact_mod_cast Nat.div_mul_le_self N d
   linarith
 have hsum : (H.card : ℝ) <= ∑ d ∈ Icc 1 N, ((N : ℝ) / (d : ℝ) + 1) := le_trans hcard_le (sum_le_sum hfixed);rw [sum_add_distrib] at hsum;have h1 : ∑ d ∈ Icc 1 N, (N : ℝ) / (d : ℝ) = (N : ℝ) * ∑ d ∈ Icc 1 N, (1 : ℝ) / (d : ℝ) := by rw [mul_sum]; apply sum_congr rfl; intro d _; ring
 have h2 : ∑ _d ∈ Icc 1 N, (1 : ℝ) = (N : ℝ) := by simp [Nat.card_Icc]
 rw [h1, h2] at hsum;have h3 := mul_le_mul_of_nonneg_left (harmonic_le_one_add_log N hN) (Nat.cast_nonneg N);linarith
lemma szabo_lemma_3_1 {N c : ℕ} (hN : 1 <= N) (hc : c ∈ Icc 1 N) {Sfam : Finset (Finset ℕ)} (hF : IsWellInter N Sfam) (hSfam : ∀ S ∈ Sfam, c ∈ S /\ ¬ APSet S) {P : Finset ℕ} (hPsub : P ⊆ Icc 1 N) (hcP : c ∉ P) (hmeetP : ∀ S ∈ Sfam, (S ∩ P).Nonempty) : ∃ H : Finset (Finset ℕ), H ⊆ Sfam /\ (∀ S ∈ H, ∃ p ∈ S ∩ P, ∃ x ∈ S, IsDeltaTriplet Sfam S c p x) /\ (((Sfam \ H).card : ℝ) <= 4 * (N : ℝ) * (1 + Real.log N) + 141 * (P.card : ℝ) * Real.sqrt N) := by
 classical
 let H := Sfam.filter (fun S => ∃ p ∈ S ∩ P, ∃ x ∈ S, IsDeltaTriplet Sfam S c p x)
 refine ⟨H, filter_subset _ _, fun S hS => (mem_filter.mp hS).2, ?_⟩
 let R := Sfam \ H
 have hR_sub : ∀ S ∈ R, S ∈ Sfam := fun S hS => (Finset.mem_sdiff.mp hS).1
 have hR_notH : ∀ S ∈ R, ∀ p ∈ S ∩ P, ∀ x ∈ S, ¬ IsDeltaTriplet Sfam S c p x := by
   intro S hS p hp x hx hdt;exact (Finset.mem_sdiff.mp hS).2 (mem_filter.mpr ⟨hR_sub S hS, p, hp, x, hx, hdt⟩)
 have hp_ex : ∀ S : {S // S ∈ R}, ∃ p, p ∈ S.1 ∩ P := fun ⟨S, hS⟩ => hmeetP S (hR_sub S hS)
 choose pS' hpS' using hp_ex
 let pS : Finset ℕ -> ℕ := fun S => if h : S ∈ R then pS' ⟨S, h⟩ else 0
 have hpS_mem : ∀ S ∈ R, pS S ∈ S /\ pS S ∈ P /\ pS S ≠ c := by
   intro S hS;have hm : pS S ∈ S ∩ P := by simpa [pS, dif_pos hS] using hpS' ⟨S, hS⟩
   have h1 := mem_of_mem_inter_left hm;have h2 := mem_of_mem_inter_right hm;exact ⟨h1, h2, fun h => hcP (h ▸ h2)⟩
 let IS : Finset ℕ -> Finset ℕ := fun S =>
   S.filter (fun w => min c (pS S) <= w /\ w <= max c (pS S))
 let S1 := R.filter (fun S => APSet (IS S))
 let S2 := R.filter (fun S => ¬ APSet (IS S))
 have hR_split : R.card = S1.card + S2.card := by rw [<- card_union_of_disjoint (disjoint_filter_filter_not _ _ _), filter_union_filter_not_eq]
 have hnu_S : ∀ S ∈ R, ∀ z ∈ S, z ≠ c -> z ≠ pS S ->
     let g := Nat.gcd (distNat c (pS S)) (distNat c z)
     0 < g /\ ∀ w, min c (min (pS S) z) <= w -> w <= max c (max (pS S) z) -> w % g = c % g -> w ∈ S := by
   intro S hS z hz hzc hzp;have hSF := hR_sub S hS;have ⟨hpS1, hpS2, hpc⟩ := hpS_mem S hS;have hnotdt := hR_notH S hS (pS S) (mem_inter.mpr ⟨hpS1, hpS2⟩) z hz;have hfill := nu_triplet_fill hF hSF (hSfam S hSF).1 hpS1 hz hpc.symm hzc.symm hzp.symm hnotdt;exact ⟨hfill.1, hfill.2.2.2⟩
 have hS1_card : (S1.card : ℝ) <= 4 * (N : ℝ) * (1 + Real.log N) := by
   have hS1_data : ∀ S : {S // S ∈ S1}, ∃ (z d : ℕ) (dir : Bool), z ∈ Icc 1 N /\ z ≠ c /\ d ∣ distNat c z /\ 1 <= d /\
       let y := if dir then c + d else c - d
       IsDeltaTriplet Sfam S.1 c y z := by
     rintro ⟨S, hS⟩;obtain ⟨hSR, hIS_ap⟩ := mem_filter.mp hS;have hSF := hR_sub S hSR;have hcS := (hSfam S hSF).1;have hnotAP := (hSfam S hSF).2;obtain ⟨hpS1, -, hpc⟩ := hpS_mem S hSR;have hcIS : c ∈ IS S := mem_filter.mpr ⟨hcS, min_le_left _ _, le_max_left _ _⟩;have hpIS : pS S ∈ IS S := mem_filter.mpr ⟨hpS1, min_le_right _ _, le_max_right _ _⟩
     have hIS2 : 2 <= (IS S).card := by
       have hsub2 : ({c, pS S} : Finset ℕ) ⊆ IS S := by
         intro x hx; rcases mem_insert.mp hx with rfl | hx'
         . exact hcIS
         . rw [mem_singleton.mp hx']; exact hpIS
       exact le_trans (by rw [card_pair hpc.symm]) (card_le_card hsub2)
     obtain ⟨d, hd, hminmax, -, hIS_mem, -⟩ := apSet_canonical hIS_ap hIS2
     have hd_dvd_all : ∀ z ∈ S, d ∣ distNat c z := by
       intro z hz
       by_cases hzc : z = c
       . subst hzc; simp [distNat]
       by_cases hzp : z = pS S
       . subst hzp
         have hcm := (hIS_mem c).mp hcIS;have hpm := (hIS_mem (pS S)).mp hpIS;have hmod : pS S % d = c % d := hpm.2.2.trans hcm.2.2.symm;unfold distNat
         rcases le_total c (pS S) with hle | hle
         . rw [max_eq_right hle, min_eq_left hle]; exact (Nat.modEq_iff_dvd' hle).mp hmod.symm
         . rw [max_eq_left hle, min_eq_right hle]; exact (Nat.modEq_iff_dvd' hle).mp hmod
       . obtain ⟨hgpos, hfill⟩ := hnu_S S hSR z hz hzc hzp
         set g := Nat.gcd (distNat c (pS S)) (distNat c z)
         have hgle : g <= distNat c (pS S) := Nat.le_of_dvd (distNat_pos_of_ne hpc.symm) (Nat.gcd_dvd_left _ _);have hcm := (hIS_mem c).mp hcIS
         have hdg : d ∣ g := by
           rcases lt_or_gt_of_ne hpc.symm with hlt | hgt
           . have hcgS : c + g ∈ S := hfill (c + g) (by omega) (by unfold distNat at hgle; omega) (by rw [Nat.add_mod_right])
             have hcgIS : c + g ∈ IS S := mem_filter.mpr ⟨hcgS, by omega, by unfold distNat at hgle; omega⟩;have hcgm := (hIS_mem (c + g)).mp hcgIS;have hmod : (c + g) % d = c % d := hcgm.2.2.trans hcm.2.2.symm;have hdvd := (Nat.modEq_iff_dvd' (Nat.le_add_right c g)).mp hmod.symm;rwa [Nat.add_sub_cancel_left] at hdvd
           . have hle_g : g <= c := by unfold distNat at hgle; omega
             have hcgS : c - g ∈ S := hfill (c - g) (by unfold distNat at hgle; omega) (by omega) (by
                 have h1 : c - g + g = c := Nat.sub_add_cancel hle_g
                 conv_rhs => rw [<- h1]
                 rw [Nat.add_mod_right])
             have hcgIS : c - g ∈ IS S := mem_filter.mpr ⟨hcgS, by unfold distNat at hgle; omega, by omega⟩;have hcgm := (hIS_mem (c - g)).mp hcgIS;have hmod : (c - g) % d = c % d := hcgm.2.2.trans hcm.2.2.symm;have hdvd := (Nat.modEq_iff_dvd' (Nat.sub_le c g)).mp hmod;have hsub_eq : c - (c - g) = g := by omega
             rwa [hsub_eq] at hdvd
         exact dvd_trans hdg (Nat.gcd_dvd_right _ _)
     let dir : Bool := decide (c < pS S)
     let y : ℕ := if dir then c + d else c - d
     have hd_le_dist : d <= distNat c (pS S) := Nat.le_of_dvd (distNat_pos_of_ne hpc.symm) (hd_dvd_all (pS S) hpS1)
     have hyS : y ∈ S := by
       have hcm := (hIS_mem c).mp hcIS;have hpm := (hIS_mem (pS S)).mp hpIS
       have hyIS : y ∈ IS S := (hIS_mem y).mpr (by
         dsimp only [y, dir]
         by_cases hlt : c < pS S
         . rw [if_pos (decide_eq_true hlt)]
           unfold distNat at hd_le_dist
           refine ⟨by omega, by omega, by rw [Nat.add_mod_right]; exact hcm.2.2⟩
         . rw [if_neg (by simp [hlt])]
           unfold distNat at hd_le_dist;have hle_d : d <= c := by omega
           refine ⟨by omega, by omega, ?_⟩
           have h1 : c - d + d = c := Nat.sub_add_cancel hle_d;rw [<- hcm.2.2]
           conv_rhs => rw [<- h1]
           rw [Nat.add_mod_right])
       exact (mem_filter.mp hyIS).1
     have hcy : c ≠ y := by
       by_cases hlt : c < pS S <;>
         simp only [y, dir, hlt, decide_true, decide_false, Bool.false_eq_true, ↓reduceIte] <;>
         (unfold distNat at hd_le_dist; omega)
     have hdist_cy : distNat c y = d := by
       by_cases hlt : c < pS S <;>
         simp only [y, dir, hlt, decide_true, decide_false, Bool.false_eq_true, ↓reduceIte] <;>
         (unfold distNat at hd_le_dist ⊢; omega)
     have hadj : ∀ w ∈ S, ¬ (min c y < w /\ w < max c y) := by
       intro w hw hbtw;have hdvd := hd_dvd_all w hw;have hwne : c ≠ w := by omega
       have hle := Nat.le_of_dvd (distNat_pos_of_ne hwne) hdvd;unfold distNat at hle hdist_cy; omega
     have hex_z : ∃ z ∈ S, z ∉ runPart S c d := by
       by_contra hall;push Not at hall;have heq : S = runPart S c d := Finset.Subset.antisymm (fun x hx => hall x hx) (runPart_subset S c d);exact hnotAP (heq ▸ runPart_isAP hcS (by omega))
     obtain ⟨z, hzS, hznotR⟩ := hex_z;have hcz : c ≠ z := fun h => hznotR (h ▸ self_mem_runPart hcS d)
     have hyz : y ≠ z := by
       intro h; subst h; apply hznotR;rw [mem_runPart]
       refine ⟨hyS, ?_, fun w hw1 hw2 hwm => ?_⟩
       . have hdvd := hd_dvd_all y hyS
         unfold distNat at hdvd
         rcases le_total c y with hle | hle
         . rw [max_eq_right hle, min_eq_left hle] at hdvd; exact ((Nat.modEq_iff_dvd' hle).mpr hdvd).symm
         . rw [max_eq_left hle, min_eq_right hle] at hdvd; exact (Nat.modEq_iff_dvd' hle).mpr hdvd
       . have : w = c \/ w = y := by
           unfold distNat at hdist_cy
           rcases le_total c y with hle | hle
           . by_cases hwc : w = c
             . left; exact hwc
             . have hdvd := (Nat.modEq_iff_dvd' (by omega : c <= w)).mp hwm.symm
               have := Nat.le_of_dvd (by omega) hdvd; right; omega
           . by_cases hwc : w = c
             . left; exact hwc
             . have hdvd := (Nat.modEq_iff_dvd' (by omega : w <= c)).mp hwm
               have := Nat.le_of_dvd (by omega) hdvd; right; omega
         rcases this with rfl | rfl <;> assumption
     refine ⟨z, d, dir, hF.1 S hSF hzS, hcz.symm, hd_dvd_all z hzS, hd, ?_⟩
     refine ⟨hcS, hyS, hzS, hcy, hcz, hyz, fun T hTF hTS ⟨hcT, hyT, hzT⟩ => ?_⟩
     exact triple_unique S T (hF.2 S hSF T hTF hTS.symm) c y z hcy hadj hzS (by rwa [hdist_cy]) (mem_inter.mpr ⟨hcS, hcT⟩) (mem_inter.mpr ⟨hyS, hyT⟩) (mem_inter.mpr ⟨hzS, hzT⟩)
   choose z1 d1 dir1 h1data using hS1_data
   let U1 := ((Icc 1 N).erase c).biUnion (fun z =>
     ((distNat c z).divisors ×ˢ (Finset.univ : Finset Bool)).image (fun p => (z, p.1, p.2)))
   have hS1_le : S1.card <= U1.card := by
     have hcard_att : S1.card = S1.attach.card := (card_attach).symm;rw [hcard_att]
     refine card_le_card_of_injOn (fun S => (z1 S, d1 S, dir1 S)) ?_ ?_
     . intro S _
       obtain ⟨hzI, hzc, hdvd, hd1, -⟩ := h1data S
       refine mem_coe.mpr (mem_biUnion.mpr ⟨z1 S, Finset.mem_erase.mpr ⟨hzc, hzI⟩, mem_image.mpr ⟨(d1 S, dir1 S), mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨hdvd, Nat.ne_of_gt (distNat_pos_of_ne hzc.symm)⟩, Finset.mem_univ _⟩, rfl⟩⟩)
     . intro S _ T _ heq
       have hz_eq : z1 S = z1 T := congrArg Prod.fst heq;have hd_eq : d1 S = d1 T := congrArg (fun p => p.2.1) heq;have hdir_eq : dir1 S = dir1 T := congrArg (fun p => p.2.2) heq;by_contra hne;have hST : S.1 ≠ T.1 := fun h => hne (Subtype.ext h)
       have hdtS := (h1data S).2.2.2.2;have hdtT := (h1data T).2.2.2.2;have hSF := hR_sub S.1 (mem_filter.mp S.2).1;have hTF := hR_sub T.1 (mem_filter.mp T.2).1;apply hdtS.2.2.2.2.2.2 T.1 hTF hST.symm
       refine ⟨hdtT.1, ?_, ?_⟩
       . have hy_eq : (if dir1 S then c + d1 S else c - d1 S) = (if dir1 T then c + d1 T else c - d1 T) := by rw [hd_eq, hdir_eq]
         rw [hy_eq]; exact hdtT.2.1
       . rw [hz_eq]; exact hdtT.2.2.1
   have hU1_le : U1.card <= ∑ z ∈ (Icc 1 N).erase c, 2 * (distNat c z).divisors.card := by
     refine le_trans card_biUnion_le (sum_le_sum fun z _ => ?_)
     refine le_trans card_image_le ?_
     rw [card_product, card_univ, Fintype.card_bool, mul_comm]
   have hsum_dist : ∑ z ∈ (Icc 1 N).erase c, (distNat c z).divisors.card <= 2 * ∑ m ∈ Icc 1 N, m.divisors.card := by
     let Lz := ((Icc 1 N).erase c).filter (fun z => z < c)
     let Rz := ((Icc 1 N).erase c).filter (fun z => c < z)
     have hcov_z : (Icc 1 N).erase c ⊆ Lz ∪ Rz := by
       intro z hz;have hzc := (Finset.mem_erase.mp hz).1
       rcases lt_or_gt_of_ne hzc with hlt | hgt
       . exact mem_union_left _ (mem_filter.mpr ⟨hz, hlt⟩)
       . exact mem_union_right _ (mem_filter.mpr ⟨hz, hgt⟩)
     have hsum_sub : ∑ z ∈ (Icc 1 N).erase c, (distNat c z).divisors.card <= (∑ z ∈ Lz, (distNat c z).divisors.card) + (∑ z ∈ Rz, (distNat c z).divisors.card) := by
       refine le_trans (sum_le_sum_of_subset hcov_z) ?_
       have hdisj : Disjoint Lz Rz := by
         rw [Finset.disjoint_left]; intro z h1 h2;have := (mem_filter.mp h1).2; have := (mem_filter.mp h2).2; omega
       rw [sum_union hdisj]
     have hL : ∑ z ∈ Lz, (distNat c z).divisors.card <= ∑ m ∈ Icc 1 N, m.divisors.card := by
       have h1 : ∑ z ∈ Lz, (distNat c z).divisors.card = ∑ m ∈ Lz.image (fun z => c - z), m.divisors.card := by
         rw [sum_image]
         . apply sum_congr rfl; intro z hz
           have := (mem_filter.mp hz).2;rw [distNat_eq_sub' (le_of_lt this)]
         . intro a ha b hb hab
           have := (mem_filter.mp (mem_coe.mp ha)).2;have := (mem_filter.mp (mem_coe.mp hb)).2;dsimp only at hab; omega
       rw [h1]
       refine sum_le_sum_of_subset ?_
       intro m hm;obtain ⟨z, hz, rfl⟩ := mem_image.mp hm;have hzc := (mem_filter.mp hz).2;have hzI := mem_Icc.mp (Finset.mem_erase.mp (mem_filter.mp hz).1).2;have hcI := mem_Icc.mp hc;exact mem_Icc.mpr ⟨by omega, by omega⟩
     have hR : ∑ z ∈ Rz, (distNat c z).divisors.card <= ∑ m ∈ Icc 1 N, m.divisors.card := by
       have h1 : ∑ z ∈ Rz, (distNat c z).divisors.card = ∑ m ∈ Rz.image (fun z => z - c), m.divisors.card := by
         rw [sum_image]
         . apply sum_congr rfl; intro z hz
           have := (mem_filter.mp hz).2;rw [distNat_eq_sub (le_of_lt this)]
         . intro a ha b hb hab
           have := (mem_filter.mp (mem_coe.mp ha)).2;have := (mem_filter.mp (mem_coe.mp hb)).2;dsimp only at hab; omega
       rw [h1]
       refine sum_le_sum_of_subset ?_
       intro m hm;obtain ⟨z, hz, rfl⟩ := mem_image.mp hm;have hzc := (mem_filter.mp hz).2;have hzI := mem_Icc.mp (Finset.mem_erase.mp (mem_filter.mp hz).1).2;have hcI := mem_Icc.mp hc;exact mem_Icc.mpr ⟨by omega, by omega⟩
     omega
   have hS1_nat : S1.card <= 4 * ∑ m ∈ Icc 1 N, m.divisors.card := by
     have h2 := le_trans hS1_le hU1_le;rw [<- mul_sum] at h2;omega
   have hS1_R : (S1.card : ℝ) <= 4 * ∑ m ∈ Icc 1 N, (m.divisors.card : ℝ) := by exact_mod_cast hS1_nat
   linarith [hS1_R, sum_card_divisors_le hN]
 have hS2_card : (S2.card : ℝ) <= 141 * (P.card : ℝ) * Real.sqrt N := by
   have hS2_data : ∀ S : {S // S ∈ S2}, ∃ (d1 d2 : ℕ), d1 ∣ distNat c (pS S.1) /\ d2 ∣ distNat c (pS S.1) /\
       let w1 := if c < pS S.1 then c + d1 else c - d1
       let w2 := if c < pS S.1 then c + d2 else c - d2
       IsDeltaTriplet Sfam S.1 c w1 w2 := by
     rintro ⟨S, hS⟩;obtain ⟨hSR, hIS_notap⟩ := mem_filter.mp hS;have hSF := hR_sub S hSR;have hcS := (hSfam S hSF).1;obtain ⟨hpS1, -, hpc⟩ := hpS_mem S hSR;have hcIS : c ∈ IS S := mem_filter.mpr ⟨hcS, min_le_left _ _, le_max_left _ _⟩;have hpIS : pS S ∈ IS S := mem_filter.mpr ⟨hpS1, min_le_right _ _, le_max_right _ _⟩;have hne_er : ((IS S).erase c).Nonempty := ⟨pS S, Finset.mem_erase.mpr ⟨hpc, hpIS⟩⟩;obtain ⟨u, hu_mem, hu_min⟩ := exists_min_image ((IS S).erase c) (fun x => distNat c x) hne_er;obtain ⟨huc, huIS⟩ := Finset.mem_erase.mp hu_mem;have huS : u ∈ S := (mem_filter.mp huIS).1
     have huB := (mem_filter.mp huIS).2
     set D := distNat c (pS S)
     set d1 := distNat c u
     have hD_def : D = max c (pS S) - min c (pS S) := rfl;have hd1_def : d1 = max c u - min c u := rfl;have hd1_pos : 0 < d1 := distNat_pos_of_ne huc.symm
     have hd1_dvd : d1 ∣ D := by
       by_cases hup : u = pS S
       . have : d1 = D := by dsimp only [D, d1]; rw [hup]
         rw [this]
       . obtain ⟨hgpos, hfill⟩ := hnu_S S hSR u huS huc hup
         set g := Nat.gcd D d1
         have hgle : g <= d1 := Nat.le_of_dvd hd1_pos (Nat.gcd_dvd_right _ _);have hgleD : g <= D := Nat.le_of_dvd (distNat_pos_of_ne hpc.symm) (Nat.gcd_dvd_left _ _)
         have hge_d1 : d1 <= g := by
           rcases lt_or_gt_of_ne hpc.symm with hlt | hgt
           . have hcgS : c + g ∈ S := hfill (c + g) (by omega) (by omega) (by rw [Nat.add_mod_right])
             have hcgIS : c + g ∈ IS S := mem_filter.mpr ⟨hcgS, by omega, by omega⟩;have hmin : d1 <= distNat c (c + g) := hu_min (c + g) (Finset.mem_erase.mpr ⟨by omega, hcgIS⟩);unfold distNat at hmin; omega
           . have hle_g : g <= c := by omega
             have hcgS : c - g ∈ S := hfill (c - g) (by omega) (by omega) (by
               have h1 : c - g + g = c := Nat.sub_add_cancel hle_g
               conv_rhs => rw [<- h1]
               rw [Nat.add_mod_right])
             have hcgIS : c - g ∈ IS S := mem_filter.mpr ⟨hcgS, by omega, by omega⟩;have hmin : d1 <= distNat c (c - g) := hu_min (c - g) (Finset.mem_erase.mpr ⟨by omega, hcgIS⟩);unfold distNat at hmin; omega
         have hgeq : g = d1 := by omega
         exact hgeq ▸ Nat.gcd_dvd_left D d1
     have hu_eq : u = if c < pS S then c + d1 else c - d1 := by split_ifs with hlt <;> omega
     have hex_v : ∃ v ∈ IS S, ¬ (d1 ∣ distNat c v) := by
       by_contra hall;push Not at hall;apply hIS_notap
       have hIS_eq : IS S = runPart (IS S) c d1 := by
         refine Finset.Subset.antisymm (fun v hv => ?_) (runPart_subset _ _ _)
         rw [mem_runPart];have hdvd_v := hall v hv;have hvB := (mem_filter.mp hv).2
         have hv_mod : v % d1 = c % d1 := by
           unfold distNat at hdvd_v
           rcases le_total c v with hle | hle
           . rw [max_eq_right hle, min_eq_left hle] at hdvd_v
             exact ((Nat.modEq_iff_dvd' hle).mpr hdvd_v).symm
           . rw [max_eq_left hle, min_eq_right hle] at hdvd_v
             exact (Nat.modEq_iff_dvd' hle).mpr hdvd_v
         refine ⟨hv, hv_mod, fun y hy1 hy2 hym => ?_⟩
         by_cases hup : u = pS S
         . have hD_eq : D = d1 := by dsimp only [D, d1]; rw [hup]
           have : y = c \/ y = pS S := by
             rcases lt_or_gt_of_ne hpc.symm with hlt | hgt
             . have hyc : d1 ∣ y - c := (Nat.modEq_iff_dvd' (by omega)).mp hym.symm
               by_cases hyc0 : y = c
               . left; exact hyc0
               . have := Nat.le_of_dvd (by omega) hyc; right; omega
             . have hcy : d1 ∣ c - y := (Nat.modEq_iff_dvd' (by omega)).mp hym
               by_cases hyc0 : y = c
               . left; exact hyc0
               . have := Nat.le_of_dvd (by omega) hcy; right; omega
           rcases this with rfl | rfl
           . exact hcIS
           . exact hpIS
         . obtain ⟨-, hfill⟩ := hnu_S S hSR u huS huc hup
           have hg_eq : Nat.gcd D d1 = d1 := Nat.gcd_eq_right hd1_dvd;have hyS : y ∈ S := hfill y (by omega) (by omega) (by rwa [hg_eq]);exact mem_filter.mpr ⟨hyS, by omega, by omega⟩
       rw [hIS_eq];exact runPart_isAP hcIS hd1_pos
     obtain ⟨v, hvIS, hv_ndvd⟩ := hex_v;have hvS : v ∈ S := (mem_filter.mp hvIS).1;have hvc : v ≠ c := by intro h; subst h; apply hv_ndvd; simp [distNat]
     have hvp : v ≠ pS S := by intro h; subst h; exact hv_ndvd hd1_dvd
     obtain ⟨hd2_pos, hfill_v⟩ := hnu_S S hSR v hvS hvc hvp
     set d2 := Nat.gcd D (distNat c v)
     have hd2_dvd : d2 ∣ D := Nat.gcd_dvd_left _ _;have hd1_ndvd_d2 : ¬ (d1 ∣ d2) := fun h => hv_ndvd (dvd_trans h (Nat.gcd_dvd_right _ _))
     have hd2_le_D : d2 <= D := Nat.le_of_dvd (distNat_pos_of_ne hpc.symm) hd2_dvd
     let w2 := if c < pS S then c + d2 else c - d2
     have hw2S : w2 ∈ S := by
       dsimp only [w2];split_ifs with hlt
       . exact hfill_v (c + d2) (by omega) (by omega) (by rw [Nat.add_mod_right])
       . have hle : d2 <= c := by omega
         exact hfill_v (c - d2) (by omega) (by omega) (by
           have h1 : c - d2 + d2 = c := Nat.sub_add_cancel hle
           conv_rhs => rw [<- h1]
           rw [Nat.add_mod_right])
     have hadj : ∀ w ∈ S, ¬ (min c u < w /\ w < max c u) := by
       intro w hw hbtw;have hwIS : w ∈ IS S := mem_filter.mpr ⟨hw, by omega, by omega⟩;have hwc : w ≠ c := by omega
       have hmin : d1 <= distNat c w := hu_min w (Finset.mem_erase.mpr ⟨hwc, hwIS⟩);unfold distNat at hmin; omega
     have hw2_notR : w2 ∉ runPart S c d1 := by
       intro hmem;have hmod := (mem_runPart S c d1 w2).mp hmem |>.2.1;apply hd1_ndvd_d2;dsimp only [w2] at hmod;split_ifs at hmod with hlt
       . have hdvd := (Nat.modEq_iff_dvd' (Nat.le_add_right c d2)).mp hmod.symm
         rwa [Nat.add_sub_cancel_left] at hdvd
       . have hle : d2 <= c := by omega
         have hdvd := (Nat.modEq_iff_dvd' (Nat.sub_le c d2)).mp hmod;have hsub_eq : c - (c - d2) = d2 := by omega
         rwa [hsub_eq] at hdvd
     have hcw2 : c ≠ w2 := fun h => hw2_notR (h ▸ self_mem_runPart hcS d1)
     have huw2 : u ≠ w2 := fun h => by
       apply hd1_ndvd_d2
       have : d1 = d2 := by
         rw [hu_eq] at h; dsimp only [w2] at h;split_ifs at h with hlt <;> omega
       rw [this]
     refine ⟨d1, d2, hd1_dvd, hd2_dvd, ?_⟩
     rw [<- hu_eq]
     refine ⟨hcS, huS, hw2S, huc.symm, hcw2, huw2, fun T hTF hTS ⟨hcT, huT, hw2T⟩ => ?_⟩
     exact triple_unique S T (hF.2 S hSF T hTF hTS.symm) c u w2 huc.symm hadj hw2S
       hw2_notR (mem_inter.mpr ⟨hcS, hcT⟩) (mem_inter.mpr ⟨huS, huT⟩)
       (mem_inter.mpr ⟨hw2S, hw2T⟩)
   choose d1 d2 h2data using hS2_data
   let U2 := P.biUnion (fun p =>
     ((distNat c p).divisors ×ˢ (distNat c p).divisors).image (fun q => (p, q.1, q.2)))
   have hS2_le : S2.card <= U2.card := by
     rw [<- card_attach]
     refine card_le_card_of_injOn (fun S => (pS S.1, d1 S, d2 S)) ?_ ?_
     . intro S _
       have hSR := (mem_filter.mp S.2).1;obtain ⟨-, hpP, hpc⟩ := hpS_mem S.1 hSR;obtain ⟨hd1, hd2, -⟩ := h2data S;have hD0 : distNat c (pS S.1) ≠ 0 := Nat.ne_of_gt (distNat_pos_of_ne hpc.symm)
       refine mem_coe.mpr (mem_biUnion.mpr ⟨pS S.1, hpP, mem_image.mpr ⟨(d1 S, d2 S), mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨hd1, hD0⟩, Nat.mem_divisors.mpr ⟨hd2, hD0⟩⟩, rfl⟩⟩)
     . intro S _ T _ heq
       have hp_eq : pS S.1 = pS T.1 := congrArg Prod.fst heq;have hd1_eq : d1 S = d1 T := congrArg (fun q => q.2.1) heq;have hd2_eq : d2 S = d2 T := congrArg (fun q => q.2.2) heq;by_contra hne;have hST : S.1 ≠ T.1 := fun h => hne (Subtype.ext h)
       have hdtS := (h2data S).2.2;have hdtT := (h2data T).2.2;have hTF := hR_sub T.1 (mem_filter.mp T.2).1;apply hdtS.2.2.2.2.2.2 T.1 hTF hST.symm
       refine ⟨hdtT.1, ?_, ?_⟩
       . have hw1 : (if c < pS S.1 then c + d1 S else c - d1 S) = (if c < pS T.1 then c + d1 T else c - d1 T) := by rw [hp_eq, hd1_eq]
         rw [hw1]; exact hdtT.2.1
       . have hw2 : (if c < pS S.1 then c + d2 S else c - d2 S) = (if c < pS T.1 then c + d2 T else c - d2 T) := by rw [hp_eq, hd2_eq]
         rw [hw2]; exact hdtT.2.2.1
   have hU2_le : U2.card <= ∑ p ∈ P, (distNat c p).divisors.card ^ 2 := by
     refine le_trans card_biUnion_le (sum_le_sum fun p _ => ?_)
     refine le_trans card_image_le ?_
     rw [card_product, sq]
   have hS2_R : (S2.card : ℝ) <= ∑ p ∈ P, ((distNat c p).divisors.card : ℝ) ^ 2 := by exact_mod_cast le_trans hS2_le hU2_le
   refine le_trans hS2_R ?_
   calc ∑ p ∈ P, ((distNat c p).divisors.card : ℝ) ^ 2
       <= ∑ _p ∈ P, (141 : ℝ) * Real.sqrt (N : ℝ) := by
         apply sum_le_sum; intro p hp;have hpc : p ≠ c := fun h => hcP (h ▸ hp)
         have hDpos : 1 <= distNat c p := distNat_pos_of_ne hpc.symm
         have hDle : distNat c p <= N := by
           have := mem_Icc.mp (hPsub hp);have := mem_Icc.mp hc;unfold distNat; omega
         refine le_trans (card_divisors_sq_le_sqrt hDpos) ?_
         exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by exact_mod_cast hDle)) (by norm_num)
     _ = 141 * (P.card : ℝ) * Real.sqrt (N : ℝ) := by rw [sum_const, nsmul_eq_mul]; ring
 have hR_R : (R.card : ℝ) = (S1.card : ℝ) + (S2.card : ℝ) := by exact_mod_cast hR_split
 linarith
lemma empty_kernel_small_bound {N s : ℕ} (hN : 1 <= N) {Sfam : Finset (Finset ℕ)} (hF : IsWellInter N Sfam) (hSfam : ∀ S ∈ Sfam, 1 <= S.card /\ ¬ APSet S /\ S.card <= s) (hempty : ∀ x ∈ Icc 1 N, ∃ T ∈ Sfam, x ∉ T) : (Sfam.card : ℝ) <= (s : ℝ) ^ 2 * (N : ℝ) + 4 * (s : ℝ) * (N : ℝ) * (1 + Real.log N) + 141 * (s : ℝ) ^ 2 * Real.sqrt N := by
 rcases Sfam.eq_empty_or_nonempty with rfl | ⟨S0, hS0⟩
 . simp; positivity
 have hcov : Sfam ⊆ S0.biUnion (fun z => Sfam.filter (fun S => z ∈ S)) := by
   intro S hS
   by_cases hSS0 : S = S0
   . subst hSS0
     obtain ⟨z, hz⟩ := card_pos.mp (lt_of_lt_of_le Nat.zero_lt_one (hSfam S hS).1);exact mem_biUnion.mpr ⟨z, hz, mem_filter.mpr ⟨hS, hz⟩⟩
   . obtain ⟨z, hz⟩ := wellInter_meet hF hS hS0 hSS0
     exact mem_biUnion.mpr ⟨z, mem_of_mem_inter_right hz, mem_filter.mpr ⟨hS, mem_of_mem_inter_left hz⟩⟩
 have hcard_le : (Sfam.card : ℝ) <= ∑ z ∈ S0, ((Sfam.filter (fun S => z ∈ S)).card : ℝ) := by exact_mod_cast le_trans (card_le_card hcov) card_biUnion_le
 have hterm : ∀ z ∈ S0, ((Sfam.filter (fun S => z ∈ S)).card : ℝ) <= (s : ℝ) * (N : ℝ) + 4 * (N : ℝ) * (1 + Real.log N) + 141 * (s : ℝ) * Real.sqrt N := by
   intro z hz
   let Sz := Sfam.filter (fun S => z ∈ S)
   have hzI : z ∈ Icc 1 N := hF.1 S0 hS0 hz;obtain ⟨Tz, hTzF, hznotT⟩ := hempty z hzI
   have hmeet : ∀ S ∈ Sz, (S ∩ Tz).Nonempty := by
     intro S hS;have hSF := (mem_filter.mp hS).1;have hzS := (mem_filter.mp hS).2;have hSTz : S ≠ Tz := fun h => hznotT (h ▸ hzS)
     exact wellInter_meet hF hSF hTzF hSTz
   obtain ⟨Hz, hHz_sub, hHz_dt, hrem_bd⟩ := szabo_lemma_3_1 hN hzI (isWellInter_subset hF (filter_subset _ _)) (fun S hS => ⟨(mem_filter.mp hS).2, (hSfam S (mem_filter.mp hS).1).2.1⟩) (hF.1 Tz hTzF) hznotT hmeet
   have hHz_le : (Hz.card : ℝ) <= (s : ℝ) * (N : ℝ) := by
     have hch : ∀ S : {S // S ∈ Hz}, ∃ p x, p ∈ Tz /\ x ∈ Icc 1 N /\ IsDeltaTriplet Sz S.1 z p x := by
       rintro ⟨S, hS⟩;obtain ⟨p, hp, x, hx, hdt⟩ := hHz_dt S hS;exact ⟨p, x, mem_of_mem_inter_right hp, hF.1 S (mem_filter.mp (hHz_sub hS)).1 hx, hdt⟩
     choose pH xH hpx using hch
     have hle : Hz.card <= (Tz ×ˢ Icc 1 N).card := by
       rw [<- card_attach]
       refine card_le_card_of_injOn (fun S => (pH S, xH S)) ?_ ?_
       . intro S _
         exact mem_coe.mpr (mem_product.mpr ⟨(hpx S).1, (hpx S).2.1⟩)
       . intro S _ T _ heq
         have hp_eq : pH S = pH T := congrArg Prod.fst heq;have hx_eq : xH S = xH T := congrArg Prod.snd heq;by_contra hne;have hST : S.1 ≠ T.1 := fun h => hne (Subtype.ext h)
         have hdtS := (hpx S).2.2;have hdtT := (hpx T).2.2;exact hdtS.2.2.2.2.2.2 T.1 (hHz_sub T.2) hST.symm ⟨hdtT.1, hp_eq ▸ hdtT.2.1, hx_eq ▸ hdtT.2.2.1⟩
     rw [card_product, Nat.card_Icc, Nat.add_sub_cancel] at hle;have hTz_le : Tz.card <= s := (hSfam Tz hTzF).2.2;have hnat : Hz.card <= s * N := le_trans hle (Nat.mul_le_mul_right N hTz_le);exact_mod_cast hnat
   have hTz_R : (Tz.card : ℝ) <= (s : ℝ) := by exact_mod_cast (hSfam Tz hTzF).2.2
   have hsplit : Sz.card = Hz.card + (Sz \ Hz).card := by rw [add_comm]; exact (card_sdiff_add_card_eq_card hHz_sub).symm
   have hsplitR : (Sz.card : ℝ) = (Hz.card : ℝ) + ((Sz \ Hz).card : ℝ) := by exact_mod_cast hsplit
   have h141 : 141 * (Tz.card : ℝ) * Real.sqrt N <= 141 * (s : ℝ) * Real.sqrt N := by
     have : 0 <= 141 * Real.sqrt N := by positivity
     nlinarith
   linarith
 have hS0_le : (S0.card : ℝ) <= (s : ℝ) := by exact_mod_cast (hSfam S0 hS0).2.2
 have hsum : (Sfam.card : ℝ) <= (S0.card : ℝ) * ((s : ℝ) * (N : ℝ) + 4 * (N : ℝ) * (1 + Real.log N) + 141 * (s : ℝ) * Real.sqrt N) := by
   refine le_trans hcard_le (le_trans (sum_le_sum hterm) ?_)
   rw [sum_const, nsmul_eq_mul]
 have hrhs_nn : 0 <= (s : ℝ) * (N : ℝ) + 4 * (N : ℝ) * (1 + Real.log N) + 141 * (s : ℝ) * Real.sqrt N := by
   have : 0 <= Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN);positivity
 have hmul := mul_le_mul_of_nonneg_right hS0_le hrhs_nn;linarith
lemma dyadic_long_AP_bucket {N L : ℕ} (hN : 1 <= N) (hL : 100 <= L) {B : Finset (Finset ℕ)} (hF : IsWellInter N B) (hB : ∀ S ∈ B, ¬ APSet S /\ L <= S.card /\ S.card < 2 * L /\ ∃ P : Finset ℕ, P ⊆ S /\ APSet P /\ 24 * S.card <= 25 * P.card) : (B.card : ℝ) <= 140 * (N : ℝ) ^ 2 / (L : ℝ) := by
 classical
 set b := L / 4
 have hb_ge : 25 <= b := by omega
 have h5b_ge : L <= 5 * b := by omega
 have hdata : ∀ S : {S // S ∈ B}, ∃ (d r k : ℕ) (M : Finset ℕ), 1 <= d /\ d <= 2 * N / L /\ r < d /\ k <= N / (b * d) /\ M ⊆ S.1 /\ (S.1 \ M).Nonempty /\ 25 * (S.1 \ M).card < 2 * L /\ (∀ x ∈ M, x % d = r /\ k * b <= x / d + 2 * L /\ x / d <= k * b + 2 * L) /\ (∀ x ∈ M, M = runPart S.1 x d) /\ (∀ j < b, r + (k * b + j) * d ∈ M) := by
   rintro ⟨S, hS⟩;obtain ⟨hnotAP, hSL, hS2L, P, hPS, hPap, hPcard⟩ := hB S hS;have hP2 : 2 <= P.card := by omega
   obtain ⟨d, hd1, -, -, hPmem, hPcard_d⟩ := apSet_canonical hPap hP2;have hPne : P.Nonempty := card_pos.mp (by omega)
   set a0 := P.min' hPne
   have ha0P : a0 ∈ P := min'_mem P hPne;have ha0S : a0 ∈ S := hPS ha0P
   set M := runPart S a0 d
   have hMS : M ⊆ S := runPart_subset S a0 d
   have hPM : P ⊆ M := by
     intro x hx;rw [mem_runPart];have hxm := (hPmem x).mp hx;have ha0m := (hPmem a0).mp ha0P
     refine ⟨hPS hx, hxm.2.2.trans ha0m.2.2.symm, fun y hy1 hy2 hym => hPS ((hPmem y).mpr ?_)⟩
     exact ⟨by omega, by omega, hym.trans ha0m.2.2⟩
   have hMcard : P.card <= M.card := card_le_card hPM;have hM_ap : APSet M := runPart_isAP ha0S (by omega);have hM2 : 2 <= M.card := by omega
   have hdiff_ne : (S \ M).Nonempty := by
     by_contra hE;rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hE;exact hnotAP (Finset.Subset.antisymm hE hMS ▸ hM_ap)
   have hdiff_card : 25 * (S \ M).card < 2 * L := by
     have hadd := card_sdiff_add_card_eq_card hMS;omega
   have hMne : M.Nonempty := card_pos.mp (by omega)
   set lo := M.min' hMne
   set hi := M.max' hMne
   have hloM : lo ∈ M := min'_mem M hMne;have hhiM : hi ∈ M := max'_mem M hMne
   set r := a0 % d
   have hM_mod : ∀ x ∈ M, x % d = r := fun x hx => ((mem_runPart S a0 d x).mp hx).2.1
   have hM_eq_rp : ∀ x ∈ M, M = runPart S x d := fun x hx => (runPart_eq_of_mem (by omega) hx).symm
   have hM_fill : ∀ y, lo <= y -> y <= hi -> y % d = r -> y ∈ M := by
     intro y hy1 hy2 hym;have hlo_rp := (mem_runPart S a0 d lo).mp hloM;have hhi_rp := (mem_runPart S a0 d hi).mp hhiM
     have hyS : y ∈ S := by
       rcases le_total y a0 with hle | hle
       . exact hlo_rp.2.2 y (by omega) (by omega) hym
       . exact hhi_rp.2.2 y (by omega) (by omega) hym
     rw [mem_runPart]
     refine ⟨hyS, hym, fun w hw1 hw2 hwm => ?_⟩
     rcases le_total w a0 with hle | hle
     . exact hlo_rp.2.2 w (by omega) (by omega) hwm
     . exact hhi_rp.2.2 w (by omega) (by omega) hwm
   have hM_card_eq : M.card = hi / d - lo / d + 1 := by
     have hbij : M.card = (Icc (lo / d) (hi / d)).card := by
       refine card_bij (fun x _ => x / d) ?_ ?_ ?_
       . intro x hx
         exact mem_Icc.mpr ⟨Nat.div_le_div_right (min'_le M x hx), Nat.div_le_div_right (le_max' M x hx)⟩
       . intro x1 hx1 x2 hx2 hq
         have h1 := Nat.div_add_mod x1 d;have h2 := Nat.div_add_mod x2 d;have hm1 := hM_mod x1 hx1;have hm2 := hM_mod x2 hx2;have hq' : x1 / d = x2 / d := hq;rw [hq', hm1] at h1; rw [hm2] at h2; omega
       . intro t ht
         obtain ⟨ht1, ht2⟩ := mem_Icc.mp ht;have hlo_eq := Nat.div_add_mod lo d;have hhi_eq := Nat.div_add_mod hi d;have hlo_m := hM_mod lo hloM;have hhi_m := hM_mod hi hhiM;have hrm : r < d := Nat.mod_lt a0 (by omega)
         refine ⟨d * t + r, hM_fill (d * t + r) ?_ ?_ ?_, ?_⟩
         . have : d * (lo / d) <= d * t := Nat.mul_le_mul_left d ht1
           omega
         . have : d * t <= d * (hi / d) := Nat.mul_le_mul_left d ht2
           omega
         . rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hrm]
         . rw [Nat.mul_add_div (by omega), Nat.div_eq_of_lt hrm, add_zero]
     have hlo_le_hi' : lo / d <= hi / d := Nat.div_le_div_right (min'_le M hi hhiM);rw [hbij, Nat.card_Icc]; omega
   have hlo_le_hi : lo <= hi := min'_le M hi hhiM;have hhiN : hi <= N := (mem_Icc.mp (hF.1 S hS (hMS hhiM))).2;have hlo1 : 1 <= lo := (mem_Icc.mp (hF.1 S hS (hMS hloM))).1
   have hd_le : d <= 2 * N / L := by
     have hspan : (M.card - 1) * d <= hi - lo := by
       have h1 := Nat.div_add_mod lo d;have h2 := Nat.div_add_mod hi d;rw [hM_mod lo hloM] at h1; rw [hM_mod hi hhiM] at h2;have hsub : hi / d - lo / d = M.card - 1 := by omega
       have hmul_sub : (M.card - 1) * d = d * (hi / d) - d * (lo / d) := by rw [<- hsub, Nat.sub_mul, Nat.mul_comm _ d, Nat.mul_comm _ d]
       omega
     have hL2 : L * d <= 2 * N := by
       have : L <= 2 * (M.card - 1) := by omega
       have h1 := Nat.mul_le_mul_right d this;have h2 : 2 * (M.card - 1) * d = 2 * ((M.card - 1) * d) := by ring
       omega
     exact (Nat.le_div_iff_mul_le (by omega)).mpr (by rw [Nat.mul_comm]; exact hL2)
   set tlo := lo / d
   set thi := hi / d
   set k := (tlo + b - 1) / b
   have hk_ge : tlo <= k * b := by
     have hlt := Nat.lt_div_mul_add (a := tlo + b - 1) (b := b) (by omega);change tlo + b - 1 < k * b + b at hlt;omega
   have hk_le_tlo : k * b <= tlo + b - 1 := Nat.div_mul_le_self (tlo + b - 1) b
   have hk_hi : k * b + (b - 1) <= thi := by
     have hlo_le_hi' : tlo <= thi := Nat.div_le_div_right hlo_le_hi;have hM_ge : 2 * b <= M.card := by have := card_le_card hPM; omega
     have hsub1 : tlo + b - 1 = tlo + (b - 1) := Nat.add_sub_assoc (by omega : 1 <= b) tlo;have h1 : k * b <= tlo + (b - 1) := hsub1 ▸ hk_le_tlo
     have h2 : tlo + (M.card - 1) = thi := by
       have : thi - tlo = M.card - 1 := by omega
       rw [<- this, Nat.add_sub_of_le hlo_le_hi']
     calc k * b + (b - 1) <= (tlo + (b - 1)) + (b - 1) := Nat.add_le_add_right h1 _
       _ <= tlo + (M.card - 1) := by omega
       _ = thi := h2
   have hk_bound : k <= N / (b * d) := by
     have h1 : k * (b * d) <= hi := by
       have h2 : d * (k * b) <= d * thi := Nat.mul_le_mul_left d (by omega);have h3 : d * thi + hi % d = hi := Nat.div_add_mod hi d;have h4 : k * (b * d) = d * (k * b) := by ring
       omega
     exact (Nat.le_div_iff_mul_le (Nat.mul_pos (by omega) (by omega))).mpr (le_trans h1 hhiN)
   refine ⟨d, r, k, M, hd1, hd_le, Nat.mod_lt a0 (by omega), hk_bound, hMS, hdiff_ne, hdiff_card, ?_, hM_eq_rp, ?_⟩
   . intro x hx
     have hxd1 : tlo <= x / d := Nat.div_le_div_right (min'_le M x hx);have hxd2 : x / d <= thi := Nat.div_le_div_right (le_max' M x hx);have hMle2L : M.card < 2 * L := lt_of_le_of_lt (card_le_card hMS) hS2L;change M.card = thi - tlo + 1 at hM_card_eq;exact ⟨hM_mod x hx, by omega, by omega⟩
   . intro j hj
     have hlo_eq : d * tlo + lo % d = lo := Nat.div_add_mod lo d;have hhi_eq : d * thi + hi % d = hi := Nat.div_add_mod hi d;rw [hM_mod lo hloM] at hlo_eq; rw [hM_mod hi hhiM] at hhi_eq;have hrm : r < d := Nat.mod_lt a0 (by omega)
     refine hM_fill (r + (k * b + j) * d) ?_ ?_ ?_
     . have : tlo * d <= (k * b + j) * d := Nat.mul_le_mul_right d (by omega)
       rw [Nat.mul_comm tlo d] at this; omega
     . have : (k * b + j) * d <= thi * d := Nat.mul_le_mul_right d (by omega)
       rw [Nat.mul_comm thi d] at this; omega
     . rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hrm]
 choose dS rS kS MS hSdata using hdata
 have hbucket_disj : ∀ (S T : {S // S ∈ B}), S ≠ T -> dS S = dS T -> rS S = rS T -> kS S = kS T -> Disjoint (S.1 \ MS S) (T.1 \ MS T) := by
   intro S T hST hd_eq hr_eq hk_eq
   set d := dS S; set r := rS S; set k := kS S
   have hST1 : S.1 ≠ T.1 := fun h => hST (Subtype.ext h)
   have hAP_inter := hF.2 S.1 S.2 T.1 T.2 hST1
   have hblk_sub : ∀ j < b, r + (k * b + j) * d ∈ S.1 ∩ T.1 := by
     intro j hj;have h1 := (hSdata S).2.2.2.2.2.2.2.2.2 j hj;have h2 := (hSdata T).2.2.2.2.2.2.2.2.2 j hj;rw [<- hd_eq, <- hr_eq, <- hk_eq] at h2;exact mem_inter.mpr ⟨(hSdata S).2.2.2.2.1 h1, (hSdata T).2.2.2.2.1 h2⟩
   have h0mem : r + k * b * d ∈ S.1 ∩ T.1 := by simpa using hblk_sub 0 (by omega)
   have h1mem : r + (k * b + 1) * d ∈ S.1 ∩ T.1 := hblk_sub 1 (by omega);have hd1 : 1 <= d := (hSdata S).1
   have hinter2 : 2 <= (S.1 ∩ T.1).card := by
     have hne01 : r + k * b * d ≠ r + (k * b + 1) * d := by
       have : (k * b + 1) * d = k * b * d + d := by ring
       omega
     exact one_lt_card.mpr ⟨_, h0mem, _, h1mem, hne01⟩
   obtain ⟨d', hd'1, -, -, hinter_mem, -⟩ := apSet_canonical hAP_inter hinter2;have h0m := (hinter_mem _).mp h0mem;have h1m := (hinter_mem _).mp h1mem
   have hd'_dvd : d' ∣ d := by
     have hmod : (r + (k * b + 1) * d) % d' = (r + k * b * d) % d' := h1m.2.2.trans h0m.2.2.symm
     have hsub : r + (k * b + 1) * d - (r + k * b * d) = d := by
       have : (k * b + 1) * d = k * b * d + d := by ring
       omega
     have hle : r + k * b * d <= r + (k * b + 1) * d := by
       have : (k * b + 1) * d = k * b * d + d := by ring
       omega
     have hdvd := (Nat.modEq_iff_dvd' hle).mp hmod.symm;rwa [hsub] at hdvd
   have hd'_eq : d' = d := by
     by_contra hne;have hd'_lt : d' < d := lt_of_le_of_ne (Nat.le_of_dvd (by omega) hd'_dvd) hne
     have hmaps : ∀ j ∈ range (b - 1), r + (k * b + j) * d + d' ∈ S.1 \ MS S := by
       intro j hj;have hjlt : j < b - 1 := mem_range.mp hj;have hlast := (hinter_mem _).mp (hblk_sub (b - 1) (by omega))
       have hlo_le : r + k * b * d <= r + (k * b + j) * d + d' := by
         have : k * b * d <= (k * b + j) * d := Nat.mul_le_mul_right d (by omega);omega
       have hhi_le : r + (k * b + j) * d + d' <= r + (k * b + (b - 1)) * d := by
         have h1 : (k * b + j + 1) * d <= (k * b + (b - 1)) * d := Nat.mul_le_mul_right d (by omega);have h2 : (k * b + j + 1) * d = (k * b + j) * d + d := by ring
         omega
       have hmod' : (r + (k * b + j) * d + d') % d' = (r + k * b * d) % d' := by
         have hjm := (hinter_mem _).mp (hblk_sub j (by omega));rw [Nat.add_mod_right, hjm.2.2, <- h0m.2.2]
       have hin : r + (k * b + j) * d + d' ∈ S.1 ∩ T.1 := (hinter_mem _).mpr ⟨by omega, by omega, hmod'.trans h0m.2.2⟩
       refine Finset.mem_sdiff.mpr ⟨mem_of_mem_inter_left hin, fun hmemM => ?_⟩
       have hm := ((hSdata S).2.2.2.2.2.2.2.1 _ hmemM).1;have hr_lt : r < d := (hSdata S).2.2.1
       have hmod_d : (r + (k * b + j) * d + d') % d = (r + d') % d := by
         have : r + (k * b + j) * d + d' = (r + d') + (k * b + j) * d := by ring
         rw [this, Nat.add_mul_mod_self_right]
       rw [hmod_d] at hm
       have hd'_mod : d' % d = 0 := by
         have hm' : (r + d') % d = r % d := by rw [Nat.mod_eq_of_lt hr_lt]; exact hm
         have hdvd := (Nat.modEq_iff_dvd' (Nat.le_add_right r d')).mp hm'.symm;rw [Nat.add_sub_cancel_left] at hdvd;exact Nat.mod_eq_zero_of_dvd hdvd
       rw [Nat.mod_eq_of_lt hd'_lt] at hd'_mod;omega
     have hinj : Set.InjOn (fun j => r + (k * b + j) * d + d') (range (b - 1) : Set ℕ) := by
       intro j1 _ j2 _ hjeq;dsimp only at hjeq;have h1 : (k * b + j1) * d = (k * b + j2) * d := by omega
       have h2 := Nat.eq_of_mul_eq_mul_right (by omega : 0 < d) h1;omega
     have hcard := card_le_card_of_injOn _ (fun j hj => mem_coe.mpr (hmaps j (mem_coe.mp hj))) hinj;rw [card_range] at hcard;have hdiff_bd := (hSdata S).2.2.2.2.2.2.1;omega
   rw [Finset.disjoint_left];intro w hwS hwT;have hwInter : w ∈ S.1 ∩ T.1 := mem_inter.mpr ⟨(Finset.mem_sdiff.mp hwS).1, (Finset.mem_sdiff.mp hwT).1⟩;have h0inM : r + k * b * d ∈ MS S := by simpa using (hSdata S).2.2.2.2.2.2.2.2.2 0 (by omega)
   have hMeq := (hSdata S).2.2.2.2.2.2.2.2.1 (r + k * b * d) h0inM;apply (Finset.mem_sdiff.mp hwS).2;rw [hMeq, mem_runPart];have hwm := (hinter_mem w).mp hwInter;rw [hd'_eq] at hwm h0m hinter_mem
   refine ⟨(Finset.mem_sdiff.mp hwS).1, hwm.2.2.trans h0m.2.2.symm, fun y hy1 hy2 hym => ?_⟩
   exact mem_of_mem_inter_left ((hinter_mem y).mpr ⟨by omega, by omega, hym.trans h0m.2.2⟩)
 let Triples := (Icc 1 (2 * N / L)).biUnion (fun d =>
   (range d).biUnion (fun r =>
     (range (N / (b * d) + 1)).image (fun k => (d, r, k))))
 let buck : ℕ × ℕ × ℕ -> Finset {S // S ∈ B} := fun t =>
   B.attach.filter (fun S => (dS S, rS S, kS S) = t)
 have hTriples_card : (Triples.card : ℝ) <= 14 * (N : ℝ) ^ 2 / (L : ℝ) ^ 2 := by
   have h1 : Triples.card <= ∑ d ∈ Icc 1 (2 * N / L), d * (N / (b * d) + 1) := by
     refine le_trans card_biUnion_le (sum_le_sum fun d _ => ?_)
     refine le_trans card_biUnion_le ?_
     have h2 : ∑ r ∈ range d, ((range (N / (b * d) + 1)).image (fun k => (d, r, k))).card <= ∑ _r ∈ range d, (N / (b * d) + 1) := sum_le_sum fun r _ => le_trans card_image_le (by rw [card_range])
     refine le_trans h2 ?_
     rw [sum_const, card_range, smul_eq_mul]
   have h2 : ∑ d ∈ Icc 1 (2 * N / L), d * (N / (b * d) + 1) <= ∑ d ∈ Icc 1 (2 * N / L), (N / b + 2 * N / L) := by
     apply sum_le_sum; intro d hd;have hd1 := (mem_Icc.mp hd).1;have hd2 := (mem_Icc.mp hd).2
     have hmul_le : d * (N / (b * d)) <= N / b := by
       have h3 : (d * (N / (b * d))) * b <= N := by
         have : d * (N / (b * d)) * b = (N / (b * d)) * (b * d) := by ring
         rw [this]; exact Nat.div_mul_le_self N (b * d)
       exact (Nat.le_div_iff_mul_le (by omega)).mpr h3
     rw [mul_add, mul_one]; omega
   have h3 : Triples.card <= (2 * N / L) * (N / b + 2 * N / L) := by
     refine le_trans (le_trans h1 h2) ?_
     rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, smul_eq_mul]
   have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (by omega : 0 < L)
   have hbpos : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (by omega : 0 < b)
   have h3R : (Triples.card : ℝ) <= ((2 * N / L : ℕ) : ℝ) * (((N / b : ℕ) : ℝ) + ((2 * N / L : ℕ) : ℝ)) := by exact_mod_cast h3
   have hdiv1 : ((2 * N / L : ℕ) : ℝ) <= 2 * (N : ℝ) / (L : ℝ) := by rw [le_div_iff₀ hLpos]; exact_mod_cast Nat.div_mul_le_self (2 * N) L
   have hdiv2 : ((N / b : ℕ) : ℝ) <= 5 * (N : ℝ) / (L : ℝ) := by
     have ha : ((N / b : ℕ) : ℝ) <= (N : ℝ) / (b : ℝ) := by rw [le_div_iff₀ hbpos]; exact_mod_cast Nat.div_mul_le_self N b
     have hb : (N : ℝ) / (b : ℝ) <= 5 * (N : ℝ) / (L : ℝ) := by
       rw [div_le_div_iff₀ hbpos hLpos];have h5R : (L : ℝ) <= 5 * (b : ℝ) := by exact_mod_cast h5b_ge
       nlinarith [Nat.cast_nonneg (α := ℝ) N]
     linarith
   have hprod : (2 * (N : ℝ) / (L : ℝ)) * (5 * (N : ℝ) / (L : ℝ) + 2 * (N : ℝ) / (L : ℝ)) = 14 * (N : ℝ) ^ 2 / (L : ℝ) ^ 2 := by ring
   have hsum_bd : ((N / b : ℕ) : ℝ) + ((2 * N / L : ℕ) : ℝ) <= 5 * (N : ℝ) / (L : ℝ) + 2 * (N : ℝ) / (L : ℝ) := by linarith
   have hmul := mul_le_mul hdiv1 hsum_bd (by positivity) (by positivity);linarith
 have hcovB : B.attach ⊆ Triples.biUnion buck := by
   intro S _;obtain ⟨hd1, hd2, hr, hk, -⟩ := hSdata S
   refine mem_biUnion.mpr ⟨(dS S, rS S, kS S), ?_, mem_filter.mpr ⟨mem_attach _ _, rfl⟩⟩
   exact mem_biUnion.mpr ⟨dS S, mem_Icc.mpr ⟨hd1, hd2⟩, mem_biUnion.mpr ⟨rS S, mem_range.mpr hr, mem_image.mpr ⟨kS S, mem_range.mpr (by omega), rfl⟩⟩⟩
 let Heavy := Triples.filter (fun t => 4 * L < (buck t).card)
 let Light := Triples.filter (fun t => (buck t).card <= 4 * L)
 have hB_split : B.card <= (∑ t ∈ Light, (buck t).card) + (∑ t ∈ Heavy, (buck t).card) := by
   rw [<- card_attach]
   refine le_trans (le_trans (card_le_card hcovB) card_biUnion_le) ?_
   have heq : Triples = Light ∪ Heavy := by
     ext t; simp only [Light, Heavy, mem_union, mem_filter]
     constructor
     . intro ht; rcases le_or_gt (buck t).card (4 * L) with h | h
       . left; exact ⟨ht, h⟩
       . right; exact ⟨ht, h⟩
     . rintro (⟨ht, _⟩ | ⟨ht, _⟩) <;> exact ht
   have hdisj : Disjoint Light Heavy := by
     rw [Finset.disjoint_left]; intro t h1 h2;have := (mem_filter.mp h1).2; have := (mem_filter.mp h2).2; omega
   conv_lhs => rw [heq, sum_union hdisj]
 have hLight_bd : ((∑ t ∈ Light, (buck t).card : ℕ) : ℝ) <= 56 * (N : ℝ) ^ 2 / (L : ℝ) := by
   have h1 : ∑ t ∈ Light, (buck t).card <= Triples.card * (4 * L) := by
     calc ∑ t ∈ Light, (buck t).card <= ∑ _t ∈ Light, (4 * L) :=
           sum_le_sum fun t ht => (mem_filter.mp ht).2
       _ = Light.card * (4 * L) := by rw [sum_const, smul_eq_mul]
       _ <= Triples.card * (4 * L) := Nat.mul_le_mul_right _ (card_le_card (filter_subset _ _))
   have h1R : ((∑ t ∈ Light, (buck t).card : ℕ) : ℝ) <= (Triples.card : ℝ) * (4 * (L : ℝ)) := by exact_mod_cast h1
   have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (by omega : 0 < L)
   have h2 := mul_le_mul_of_nonneg_right hTriples_card (show (0 : ℝ) <= 4 * (L : ℝ) by positivity);have h3 : 14 * (N : ℝ) ^ 2 / (L : ℝ) ^ 2 * (4 * (L : ℝ)) = 56 * (N : ℝ) ^ 2 / (L : ℝ) := by field_simp; ring
   linarith
 have hbuck_le_N : ∀ t, (buck t).card <= N := by
   intro t;have hch : ∀ S : {S // S ∈ buck t}, ∃ v, v ∈ S.1.1 \ MS S.1 := fun ⟨S, _⟩ => (hSdata S).2.2.2.2.2.1
   choose vS hvS using hch
   have hle : (buck t).card <= (Icc 1 N).card := by
     rw [<- card_attach]
     refine card_le_card_of_injOn vS ?_ ?_
     . intro S _
       exact mem_coe.mpr (hF.1 S.1.1 S.1.2 (Finset.sdiff_subset (hvS S)))
     . intro S _ T _ heq
       by_contra hne;have hST : S.1 ≠ T.1 := fun h => hne (Subtype.ext h)
       have htS := (mem_filter.mp S.2).2;have htT := (mem_filter.mp T.2).2;have hd_eq : dS S.1 = dS T.1 := congrArg Prod.fst (htS.trans htT.symm);have hr_eq : rS S.1 = rS T.1 := congrArg (fun p => p.2.1) (htS.trans htT.symm);have hk_eq : kS S.1 = kS T.1 := congrArg (fun p => p.2.2) (htS.trans htT.symm);exact Finset.disjoint_left.mp (hbucket_disj S.1 T.1 hST hd_eq hr_eq hk_eq) (hvS S) (heq ▸ hvS T)
   rwa [Nat.card_Icc, Nat.add_sub_cancel] at hle
 have hHeavy_bd : ((∑ t ∈ Heavy, (buck t).card : ℕ) : ℝ) <= 84 * (N : ℝ) ^ 2 / (L : ℝ) := by
   have hU_card_tight : ∀ t ∈ Triples, ((buck t).biUnion (fun S => MS S)).card <= 4 * L := by
     intro t _
     let d := t.1; let r := t.2.1; let k := t.2.2
     have hsub : (buck t).biUnion (fun S => MS S) ⊆ (Icc (k * b + 1 - 2 * L) (k * b + 2 * L - 1)).image (fun q => q * d + r) := by
       intro x hx;obtain ⟨S, hSb, hxM⟩ := mem_biUnion.mp hx;have hteq := (mem_filter.mp hSb).2;have hd_eq : dS S = d := congrArg Prod.fst hteq;have hr_eq : rS S = r := congrArg (fun p => p.2.1) hteq;have hk_eq : kS S = k := congrArg (fun p => p.2.2) hteq;have ⟨hxm, hx1, hx2⟩ := (hSdata S).2.2.2.2.2.2.2.1 x hxM;have hd1 : 1 <= d := hd_eq ▸ (hSdata S).1
       have hx0M : r + k * b * d ∈ MS S := by
         have := (hSdata S).2.2.2.2.2.2.2.2.2 0 (by omega)
         simpa [hd_eq, hr_eq, hk_eq] using this
       have hMlt : (MS S).card < 2 * L := lt_of_le_of_lt (card_le_card (hSdata S).2.2.2.2.1) (hB S.1 S.2).2.2.1
       have hMeq : MS S = runPart S.1 (r + k * b * d) d := by
         have := (hSdata S).2.2.2.2.2.2.2.2.1 _ hx0M;rwa [hd_eq] at this
       have hrp := (mem_runPart S.1 (r + k * b * d) d x).mp (hMeq ▸ hxM);have hrm : r < d := by rw [<- hd_eq, <- hr_eq]; exact (hSdata S).2.2.1
       rw [hd_eq, hr_eq] at hxm
       have hxdiff : (max (x / d) (k * b) - min (x / d) (k * b)) + 1 <= (MS S).card := by
         set loq := min (x / d) (k * b)
         set hiq := max (x / d) (k * b)
         have hsubI : (Icc loq hiq).image (fun q => q * d + r) ⊆ MS S := by
           intro y hy;obtain ⟨q, hq, rfl⟩ := mem_image.mp hy;have hqI := mem_Icc.mp hq;have hx_eq : d * (x / d) + r = x := by have := Nat.div_add_mod x d; rwa [hxm] at this
           have hmin_eq : min (r + k * b * d) x = loq * d + r := by
             dsimp only [loq]
             rcases le_total (x / d) (k * b) with hle | hle
             . have h2 : x <= r + k * b * d := by
                 have := Nat.mul_le_mul_right d hle; rw [Nat.mul_comm d] at hx_eq; omega
               rw [min_eq_right h2, min_eq_left hle]; rw [Nat.mul_comm d] at hx_eq; omega
             . have h2 : r + k * b * d <= x := by
                 have := Nat.mul_le_mul_right d hle; rw [Nat.mul_comm d] at hx_eq; omega
               rw [min_eq_left h2, min_eq_right hle]; omega
           have hmax_eq : max (r + k * b * d) x = hiq * d + r := by
             dsimp only [hiq]
             rcases le_total (x / d) (k * b) with hle | hle
             . have h2 : x <= r + k * b * d := by
                 have := Nat.mul_le_mul_right d hle; rw [Nat.mul_comm d] at hx_eq; omega
               rw [max_eq_left h2, max_eq_right hle]; omega
             . have h2 : r + k * b * d <= x := by
                 have := Nat.mul_le_mul_right d hle; rw [Nat.mul_comm d] at hx_eq; omega
               rw [max_eq_right h2, max_eq_left hle]; rw [Nat.mul_comm d] at hx_eq; omega
           have hq_lo : loq * d <= q * d := Nat.mul_le_mul_right d hqI.1;have hq_hi : q * d <= hiq * d := Nat.mul_le_mul_right d hqI.2;have hyS : q * d + r ∈ S.1 := hrp.2.2 (q * d + r) (by omega) (by omega) (by rw [Nat.mul_add_mod', Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hrm]);rw [hMeq, mem_runPart]
           refine ⟨hyS, by rw [Nat.mul_add_mod', Nat.add_mul_mod_self_right], fun w hw1 hw2 hwm => ?_⟩
           exact hrp.2.2 w (by omega) (by omega) hwm
         have hinjI : Set.InjOn (fun q => q * d + r) (Icc loq hiq : Set ℕ) := by
           intro q1 _ q2 _ heq; dsimp only at heq;exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < d) (by omega)
         have hcardI := card_le_card hsubI;rw [card_image_of_injOn hinjI, Nat.card_Icc] at hcardI;have hle_lh : loq <= hiq := by dsimp only [loq, hiq]; exact min_le_max
         change hiq + 1 - loq <= (MS S).card at hcardI;change (hiq - loq) + 1 <= (MS S).card;omega
       have hxd_lo : k * b + 1 - 2 * L <= x / d := by
         rcases le_total (x / d) (k * b) with h | h
         . rw [max_eq_right h, min_eq_left h] at hxdiff
           exact Nat.sub_le_of_le_add (by omega)
         . exact Nat.sub_le_of_le_add (by omega)
       have hxd_hi : x / d <= k * b + 2 * L - 1 := by
         rcases le_total (x / d) (k * b) with h | h
         . omega
         . rw [max_eq_left h, min_eq_right h] at hxdiff; omega
       refine mem_image.mpr ⟨x / d, mem_Icc.mpr ⟨hxd_lo, hxd_hi⟩, ?_⟩
       have hdm := Nat.div_add_mod x d; rw [hxm] at hdm; rw [Nat.mul_comm]; omega
     refine le_trans (card_le_card hsub) (le_trans card_image_le ?_)
     rw [Nat.card_Icc]; omega
   have hheavy_close : ∀ t1 ∈ Heavy, ∀ t2 ∈ Heavy, t1.1 = t2.1 -> t1.2.1 = t2.2.1 /\ t1.2.2 <= t2.2.2 + 20 /\ t2.2.2 <= t1.2.2 + 20 := by
     intro t1 ht1 t2 ht2 hd_eq;have ht1T := (mem_filter.mp ht1).1;have ht2T := (mem_filter.mp ht2).1;have hcard1 := (mem_filter.mp ht1).2;have hcard2 := (mem_filter.mp ht2).2
     let U2 := (buck t2).biUnion (fun S => MS S)
     have hU2_le : U2.card <= 4 * L := hU_card_tight t2 ht2T
     have hex_S1 : ∃ S1 ∈ buck t1, Disjoint (S1.1 \ MS S1) U2 := by
       by_contra hall;push Not at hall
       have hch : ∀ S : {S // S ∈ buck t1}, ∃ w, w ∈ S.1.1 \ MS S.1 /\ w ∈ U2 := by
         rintro ⟨S, hS⟩;have hnd := hall S hS;rw [Finset.not_disjoint_iff] at hnd;exact hnd
       choose wS hwS using hch
       have hle : (buck t1).card <= U2.card := by
         rw [<- card_attach]
         refine card_le_card_of_injOn wS (fun S _ => mem_coe.mpr (hwS S).2) ?_
         intro S _ T _ heq;by_contra hne;have hST : S.1 ≠ T.1 := fun h => hne (Subtype.ext h)
         have hts := (mem_filter.mp S.2).2.trans (mem_filter.mp T.2).2.symm;exact Finset.disjoint_left.mp (hbucket_disj S.1 T.1 hST (congrArg Prod.fst hts) (congrArg (fun p => p.2.1) hts) (congrArg (fun p => p.2.2) hts)) (hwS S).1 (heq ▸ (hwS T).1)
       omega
     obtain ⟨S1, hS1b, hS1_disj⟩ := hex_S1
     have hex_T1 : ∃ T1 ∈ buck t2, Disjoint (T1.1 \ MS T1) S1.1 := by
       by_contra hall;push Not at hall
       have hch : ∀ T : {T // T ∈ buck t2}, ∃ w, w ∈ T.1.1 \ MS T.1 /\ w ∈ S1.1 := by
         rintro ⟨T, hT⟩;exact Finset.not_disjoint_iff.mp (hall T hT)
       choose wT hwT using hch
       have hle : (buck t2).card <= S1.1.card := by
         rw [<- card_attach]
         refine card_le_card_of_injOn wT (fun T _ => mem_coe.mpr (hwT T).2) ?_
         intro T _ U _ heq;by_contra hne;have hTU : T.1 ≠ U.1 := fun h => hne (Subtype.ext h)
         have hts := (mem_filter.mp T.2).2.trans (mem_filter.mp U.2).2.symm;exact Finset.disjoint_left.mp (hbucket_disj T.1 U.1 hTU (congrArg Prod.fst hts) (congrArg (fun p => p.2.1) hts) (congrArg (fun p => p.2.2) hts)) (hwT T).1 (heq ▸ (hwT U).1)
       have hS1lt := (hB S1.1 S1.2).2.2.1;omega
     obtain ⟨T1, hT1b, hT1_disj⟩ := hex_T1
     have hex_w : ∃ w, w ∈ MS S1 /\ w ∈ MS T1 := by
       by_cases hST1 : S1.1 = T1.1
       . have hw := (hSdata S1).2.2.2.2.2.2.2.2.2 0 (by omega)
         have hS1T1 : S1 = T1 := Subtype.ext hST1;exact ⟨_, hw, hS1T1 ▸ hw⟩
       . obtain ⟨w, hw⟩ := wellInter_meet hF S1.2 T1.2 hST1
         have hwS1 := mem_of_mem_inter_left hw;have hwT1 := mem_of_mem_inter_right hw
         have hwMT1 : w ∈ MS T1 := by
           by_contra hnot;exact Finset.disjoint_left.mp hT1_disj (Finset.mem_sdiff.mpr ⟨hwT1, hnot⟩) hwS1
         have hwU2 : w ∈ U2 := mem_biUnion.mpr ⟨T1, hT1b, hwMT1⟩
         have hwMS1 : w ∈ MS S1 := by
           by_contra hnot;exact Finset.disjoint_left.mp hS1_disj (Finset.mem_sdiff.mpr ⟨hwS1, hnot⟩) hwU2
         exact ⟨w, hwMS1, hwMT1⟩
     obtain ⟨w, hw1, hw2⟩ := hex_w;have ht1eq := (mem_filter.mp hS1b).2;have ht2eq := (mem_filter.mp hT1b).2;have h1 := (hSdata S1).2.2.2.2.2.2.2.1 w hw1;have h2 := (hSdata T1).2.2.2.2.2.2.2.1 w hw2;have hd1eq : dS S1 = t1.1 := congrArg Prod.fst ht1eq;have hr1eq : rS S1 = t1.2.1 := congrArg (fun p => p.2.1) ht1eq;have hk1eq : kS S1 = t1.2.2 := congrArg (fun p => p.2.2) ht1eq;have hd2eq : dS T1 = t2.1 := congrArg Prod.fst ht2eq;have hr2eq : rS T1 = t2.2.1 := congrArg (fun p => p.2.1) ht2eq;have hk2eq : kS T1 = t2.2.2 := congrArg (fun p => p.2.2) ht2eq;rw [hd1eq, hr1eq, hk1eq] at h1
     rw [hd2eq, hr2eq, hk2eq, <- hd_eq] at h2
     refine ⟨h1.1.symm.trans h2.1, ?_, ?_⟩
     . have : t1.2.2 * b <= t2.2.2 * b + 4 * L := by omega
       have : t1.2.2 * b <= (t2.2.2 + 20) * b := by
         have h20 : 4 * L <= 20 * b := by omega
         have : (t2.2.2 + 20) * b = t2.2.2 * b + 20 * b := by ring
         omega
       exact Nat.le_of_mul_le_mul_right this (by omega)
     . have : t2.2.2 * b <= t1.2.2 * b + 4 * L := by omega
       have : t2.2.2 * b <= (t1.2.2 + 20) * b := by
         have h20 : 4 * L <= 20 * b := by omega
         have : (t1.2.2 + 20) * b = t1.2.2 * b + 20 * b := by ring
         omega
       exact Nat.le_of_mul_le_mul_right this (by omega)
   have hHeavy_card : Heavy.card <= (2 * N / L) * 41 := by
     have hcovH : Heavy ⊆ (Icc 1 (2 * N / L)).biUnion (fun d => Heavy.filter (fun t => t.1 = d)) := by
       intro t ht;have htT := (mem_filter.mp ht).1;obtain ⟨d, hd, htd⟩ := mem_biUnion.mp htT;obtain ⟨r, -, htr⟩ := mem_biUnion.mp htd;obtain ⟨k, -, htk⟩ := mem_image.mp htr;have ht1 : t.1 = d := by rw [<- htk]
       exact mem_biUnion.mpr ⟨d, hd, mem_filter.mpr ⟨ht, ht1⟩⟩
     refine le_trans (card_le_card hcovH) (le_trans card_biUnion_le ?_)
     have hper_d : ∀ d ∈ Icc 1 (2 * N / L), (Heavy.filter (fun t => t.1 = d)).card <= 41 := by
       intro d _
       let Hd := Heavy.filter (fun t => t.1 = d)
       rcases Hd.eq_empty_or_nonempty with hE | ⟨t0, ht0⟩
       . change Hd.card <= 41; rw [hE]; simp
       have hsub_d : Hd ⊆ (Icc (t0.2.2 - 20) (t0.2.2 + 20)).image (fun k => (d, t0.2.1, k)) := by
         intro t ht;have htH := (mem_filter.mp ht).1;have ht1 := (mem_filter.mp ht).2;have ht0H := (mem_filter.mp ht0).1;have ht01 := (mem_filter.mp ht0).2;have ⟨hreq, hk1, hk2⟩ := hheavy_close t htH t0 ht0H (ht1.trans ht01.symm)
         refine mem_image.mpr ⟨t.2.2, mem_Icc.mpr ⟨by omega, hk1⟩, ?_⟩
         exact Prod.ext ht1.symm (Prod.ext hreq.symm rfl)
       refine le_trans (card_le_card hsub_d) (le_trans card_image_le ?_)
       rw [Nat.card_Icc]; omega
     refine le_trans (sum_le_sum hper_d) ?_
     rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, smul_eq_mul]
   have hsumH : ∑ t ∈ Heavy, (buck t).card <= (2 * N / L) * 41 * N := by
     calc ∑ t ∈ Heavy, (buck t).card <= ∑ _t ∈ Heavy, N := sum_le_sum fun t _ => hbuck_le_N t
       _ = Heavy.card * N := by rw [sum_const, smul_eq_mul]
       _ <= (2 * N / L) * 41 * N := Nat.mul_le_mul_right N hHeavy_card
   have hsumH_R : ((∑ t ∈ Heavy, (buck t).card : ℕ) : ℝ) <= ((2 * N / L : ℕ) : ℝ) * 41 * (N : ℝ) := by exact_mod_cast hsumH
   have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (by omega : 0 < L)
   have hdiv : ((2 * N / L : ℕ) : ℝ) <= 2 * (N : ℝ) / (L : ℝ) := by rw [le_div_iff₀ hLpos]; exact_mod_cast Nat.div_mul_le_self (2 * N) L
   have hmul : ((2 * N / L : ℕ) : ℝ) * 41 * (N : ℝ) <= (2 * (N : ℝ) / (L : ℝ)) * 41 * (N : ℝ) := by
     have : 0 <= 41 * (N : ℝ) := by positivity
     nlinarith
   have hrew : (2 * (N : ℝ) / (L : ℝ)) * 41 * (N : ℝ) = 82 * (N : ℝ) ^ 2 / (L : ℝ) := by ring
   have hnn : 0 <= 2 * (N : ℝ) ^ 2 / (L : ℝ) := by positivity
   have h84 : 84 * (N : ℝ) ^ 2 / (L : ℝ) = 82 * (N : ℝ) ^ 2 / (L : ℝ) + 2 * (N : ℝ) ^ 2 / (L : ℝ) := by ring
   linarith
 have hB_R : (B.card : ℝ) <= ((∑ t ∈ Light, (buck t).card : ℕ) : ℝ) + ((∑ t ∈ Heavy, (buck t).card : ℕ) : ℝ) := by exact_mod_cast hB_split
 have h140 : 140 * (N : ℝ) ^ 2 / (L : ℝ) = 56 * (N : ℝ) ^ 2 / (L : ℝ) + 84 * (N : ℝ) ^ 2 / (L : ℝ) := by ring
 linarith
lemma long_AP_nonAP_bound {N s : ℕ} (hN : 1 <= N) (hs : 100 <= s) {B : Finset (Finset ℕ)} (hF : IsWellInter N B) (hB : ∀ S ∈ B, ¬ APSet S /\ s <= S.card /\ ∃ P : Finset ℕ, P ⊆ S /\ APSet P /\ 24 * S.card <= 25 * P.card) : (B.card : ℝ) <= 280 * (N : ℝ) ^ 2 / (s : ℝ) := by
 let K := Nat.log 2 N + 1
 have hcov : B ⊆ (range K).biUnion (fun j =>
     B.filter (fun S => s * 2 ^ j <= S.card /\ S.card < 2 * (s * 2 ^ j))) := by
   intro S hS
   have hScard_le : S.card <= N := by
     have := card_le_card (hF.1 S hS);rwa [Nat.card_Icc, Nat.add_sub_cancel] at this
   have hSs := (hB S hS).2.1
   set j := Nat.log 2 (S.card / s)
   have hq_pos : 1 <= S.card / s := (Nat.one_le_div_iff (by omega)).mpr hSs
   have hj_lt : j < K := by
     have h1 : S.card / s <= N := le_trans (Nat.div_le_self _ _) hScard_le;have h2 := Nat.log_mono_right (b := 2) h1;omega
   have hpow1 : 2 ^ j <= S.card / s := Nat.pow_log_le_self 2 (by omega);have hpow2 : S.card / s < 2 ^ (j + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
   have hmul1 : s * 2 ^ j <= S.card := by
     calc s * 2 ^ j <= s * (S.card / s) := Nat.mul_le_mul_left s hpow1
       _ <= S.card := Nat.mul_div_le S.card s
   have hmul2 : S.card < 2 * (s * 2 ^ j) := by
     have hlt := Nat.lt_div_mul_add (a := S.card) (b := s) (by omega);have h1 : (S.card / s + 1) * s <= 2 ^ (j + 1) * s := Nat.mul_le_mul_right s hpow2;have h2 : 2 ^ (j + 1) * s = 2 * (s * 2 ^ j) := by rw [pow_succ]; ring
     rw [add_mul, one_mul] at h1; omega
   exact mem_biUnion.mpr ⟨j, mem_range.mpr hj_lt, mem_filter.mpr ⟨hS, hmul1, hmul2⟩⟩
 have hle : (B.card : ℝ) <= ∑ j ∈ range K, ((B.filter (fun S => s * 2 ^ j <= S.card /\ S.card < 2 * (s * 2 ^ j))).card : ℝ) := by exact_mod_cast le_trans (card_le_card hcov) card_biUnion_le
 have hterm : ∀ j ∈ range K, ((B.filter (fun S => s * 2 ^ j <= S.card /\ S.card < 2 * (s * 2 ^ j))).card : ℝ) <= 140 * (N : ℝ) ^ 2 / ((s * 2 ^ j : ℕ) : ℝ) := by
   intro j _
   have hL100 : 100 <= s * 2 ^ j := by
     have : 1 <= 2 ^ j := Nat.one_le_pow j 2 (by norm_num);nlinarith
   refine dyadic_long_AP_bucket hN hL100 (isWellInter_subset hF (filter_subset _ _)) ?_
   intro S hS;obtain ⟨hSB, h1, h2⟩ := mem_filter.mp hS;obtain ⟨hnotAP, -, hP⟩ := hB S hSB;exact ⟨hnotAP, h1, h2, hP⟩
 refine le_trans hle (le_trans (sum_le_sum hterm) ?_)
 have hgeom : ∑ j ∈ range K, (140 * (N : ℝ) ^ 2 / ((s * 2 ^ j : ℕ) : ℝ)) = (140 * (N : ℝ) ^ 2 / (s : ℝ)) * ∑ j ∈ range K, ((1 / 2 : ℝ) ^ j) := by
   rw [mul_sum];apply sum_congr rfl; intro j _;push_cast; rw [one_div_pow]; ring
 rw [hgeom]
 have hsum2 : ∑ j ∈ range K, ((1 / 2 : ℝ) ^ j) <= 2 := by
   have hgp := geom_sum_eq (by norm_num : (1 / 2 : ℝ) ≠ 1) K;rw [hgp];have hnn : (0 : ℝ) <= (1 / 2 : ℝ) ^ K := by positivity
   have hrew : ((1 / 2 : ℝ) ^ K - 1) / (1 / 2 - 1) = 2 - 2 * (1 / 2 : ℝ) ^ K := by ring
   linarith
 have hfac : 0 <= 140 * (N : ℝ) ^ 2 / (s : ℝ) := by positivity
 have hmul := mul_le_mul_of_nonneg_left hsum2 hfac;have h280 : 140 * (N : ℝ) ^ 2 / (s : ℝ) * 2 = 280 * (N : ℝ) ^ 2 / (s : ℝ) := by ring
 linarith
lemma simonovits_sos_one_side {N m : ℕ} (hN : 1 <= N) (hm : 200 <= m) (hcop_int : ∀ (b U V : ℕ), 1 <= b -> b <= N -> U < V -> N <= (V - U) ^ 6 -> ((V - U : ℕ) : ℝ) / (4 * ((Nat.log 2 N + 1 : ℕ) : ℝ)) <= (((Ioc U V).filter (fun q => Nat.Coprime q b)).card : ℝ)) (hm_large : (N : ℝ) <= (((m : ℝ) / (30 * Real.sqrt (Real.sqrt (N : ℝ))) - 2) ^ 6)) (hm_pos : 4 <= (m : ℝ) / (30 * Real.sqrt (Real.sqrt (N : ℝ)))) {T : Finset ℕ} (hTsub : T ⊆ Icc 1 N) (hTcard : T.card = m) (hnoAP : ∀ P : Finset ℕ, P ⊆ T -> APSet P -> 49 * P.card < 48 * m) :
   (m : ℝ) ^ 2 / (100000 * Real.sqrt (Real.sqrt (N : ℝ)) * ((Nat.log 2 N + 1 : ℕ) : ℝ)) <= (((T ×ˢ T).filter (fun p => p.1 < p.2 /\ ¬ (∀ w, 1 <= w -> w <= p.2 -> w % Nat.gcd p.1 p.2 = 0 -> w ∈ T))).card : ℝ) := by
 classical
 let Bad := (T ×ˢ T).filter (fun p => p.1 < p.2 /\ ¬ (∀ w, 1 <= w -> w <= p.2 -> w % Nat.gcd p.1 p.2 = 0 -> w ∈ T))
 let BadSym := (T ×ˢ T).filter (fun p => p.1 ≠ p.2 /\ ¬ (∀ w, 1 <= w -> w <= max p.1 p.2 -> w % Nat.gcd p.1 p.2 = 0 -> w ∈ T))
 have hBad_sym : BadSym.card = 2 * Bad.card := by
   let B1 := BadSym.filter (fun p => p.1 < p.2)
   let B2 := BadSym.filter (fun p => p.2 < p.1)
   have hdisj : Disjoint B1 B2 := by
     rw [Finset.disjoint_left]; intro p h1 h2;have := (mem_filter.mp h1).2; have := (mem_filter.mp h2).2; omega
   have hunion : BadSym = B1 ∪ B2 := by
     ext p; simp only [B1, B2, BadSym, mem_union, mem_filter]
     constructor
     . rintro ⟨h1, hne, h3⟩
       rcases lt_or_gt_of_ne hne with hlt | hgt
       . left; exact ⟨⟨h1, hne, h3⟩, hlt⟩
       . right; exact ⟨⟨h1, hne, h3⟩, hgt⟩
     . rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
   have hB1_eq : B1 = Bad := by
     ext p; simp only [B1, BadSym, Bad, mem_filter]
     constructor
     . rintro ⟨⟨h1, _, h3⟩, hlt⟩
       rw [max_eq_right (le_of_lt hlt)] at h3; exact ⟨h1, hlt, h3⟩
     . rintro ⟨h1, hlt, h3⟩
       refine ⟨⟨h1, ne_of_lt hlt, ?_⟩, hlt⟩
       rwa [max_eq_right (le_of_lt hlt)]
   have hB2_eq : B2.card = B1.card := by
     refine card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
     . intro p hp
       obtain ⟨hpS, hlt⟩ := mem_filter.mp hp;obtain ⟨hpP, hne, h3⟩ := mem_filter.mp hpS;obtain ⟨h1, h2⟩ := mem_product.mp hpP
       refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_product.mpr ⟨h2, h1⟩, hne.symm, ?_⟩, hlt⟩
       rwa [max_comm, Nat.gcd_comm]
     . intro p1 _ p2 _ heq
       exact Prod.ext (congrArg Prod.snd heq) (congrArg Prod.fst heq)
     . intro p hp
       obtain ⟨hpS, hlt⟩ := mem_filter.mp hp;obtain ⟨hpP, hne, h3⟩ := mem_filter.mp hpS;obtain ⟨h1, h2⟩ := mem_product.mp hpP
       refine ⟨(p.2, p.1), mem_filter.mpr ⟨mem_filter.mpr ⟨mem_product.mpr ⟨h2, h1⟩, hne.symm, ?_⟩, hlt⟩, rfl⟩
       rwa [max_comm, Nat.gcd_comm]
   rw [hunion, card_union_of_disjoint hdisj, hB2_eq, hB1_eq]; ring
 by_cases hbig : (m : ℝ) ^ 2 / 40000 <= (Bad.card : ℝ)
 . refine le_trans ?_ hbig
   apply div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num)
   have hsq1 : (1 : ℝ) <= Real.sqrt (Real.sqrt (N : ℝ)) := by
     have h1 : (1 : ℝ) <= Real.sqrt (N : ℝ) := by rw [<- Real.sqrt_one]; exact Real.sqrt_le_sqrt (by exact_mod_cast hN)
     rw [<- Real.sqrt_one]; exact Real.sqrt_le_sqrt h1
   have hlog1 : (1 : ℝ) <= ((Nat.log 2 N + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 <= Nat.log 2 N + 1)
   nlinarith
 push Not at hbig
 let GoodV := T.filter (fun v => (T.filter (fun u => (u, v) ∈ BadSym)).card * 100 < m)
 have hGoodV_card : 199 * m <= 200 * GoodV.card := by
   let BadV := T.filter (fun v => m <= (T.filter (fun u => (u, v) ∈ BadSym)).card * 100)
   have hpart : GoodV.card + BadV.card = T.card := by
     have h1 : GoodV ∪ BadV = T := by
       ext v; simp only [GoodV, BadV, mem_union, mem_filter]
       constructor
       . rintro (⟨hv, _⟩ | ⟨hv, _⟩) <;> exact hv
       . intro hv; rcases lt_or_ge ((T.filter (fun u => (u, v) ∈ BadSym)).card * 100) m with h | h
         . left; exact ⟨hv, h⟩
         . right; exact ⟨hv, h⟩
     have h2 : Disjoint GoodV BadV := by
       rw [Finset.disjoint_left]; intro v h1 h2;have := (mem_filter.mp h1).2; have := (mem_filter.mp h2).2; omega
     rw [<- card_union_of_disjoint h2, h1]
   have hsum_bad : BadV.card * m <= BadSym.card * 100 := by
     have h1 : BadV.card * m <= ∑ v ∈ BadV, (T.filter (fun u => (u, v) ∈ BadSym)).card * 100 := by
       calc BadV.card * m = ∑ _v ∈ BadV, m := by rw [sum_const, smul_eq_mul]
         _ <= ∑ v ∈ BadV, (T.filter (fun u => (u, v) ∈ BadSym)).card * 100 := sum_le_sum fun v hv => (mem_filter.mp hv).2
     rw [<- sum_mul] at h1
     have h2 : ∑ v ∈ BadV, (T.filter (fun u => (u, v) ∈ BadSym)).card <= BadSym.card := by
       have hsub : BadV.biUnion (fun v => (T.filter (fun u => (u, v) ∈ BadSym)).image (fun u => (u, v))) ⊆ BadSym := by
         intro p hp;obtain ⟨v, -, hpv⟩ := mem_biUnion.mp hp;obtain ⟨u, hu, rfl⟩ := mem_image.mp hpv;exact (mem_filter.mp hu).2
       have hdisj_v : Set.PairwiseDisjoint (BadV : Set ℕ) (fun v => (T.filter (fun u => (u, v) ∈ BadSym)).image (fun u => (u, v))) := by
         intro v1 _ v2 _ hne;change Disjoint _ _;rw [Finset.disjoint_left]; intro p h1 h2;obtain ⟨u1, -, rfl⟩ := mem_image.mp h1;obtain ⟨u2, -, heq⟩ := mem_image.mp h2;exact hne (congrArg Prod.snd heq).symm
       have hcard_u := card_le_card hsub;rw [card_biUnion hdisj_v] at hcard_u
       refine le_trans ?_ hcard_u
       apply sum_le_sum; intro v _;rw [card_image_of_injective _ (fun u1 u2 h => congrArg Prod.fst h)]
     exact le_trans h1 (Nat.mul_le_mul_right 100 h2)
   have hBadV_le : 200 * BadV.card <= m := by
     have hR : (BadSym.card : ℝ) * 100 < (m : ℝ) ^ 2 / 200 := by
       have hsymR : (BadSym.card : ℝ) = 2 * (Bad.card : ℝ) := by exact_mod_cast hBad_sym
       linarith
     have h1R : (BadV.card : ℝ) * (m : ℝ) <= (BadSym.card : ℝ) * 100 := by exact_mod_cast hsum_bad
     have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
     have : (200 : ℝ) * (BadV.card : ℝ) < (m : ℝ) := by nlinarith
     have hnat : 200 * BadV.card < m := by exact_mod_cast this
     omega
   omega
 have hGoodV_ne : GoodV.Nonempty := card_pos.mp (by omega)
 set v0 := GoodV.max' hGoodV_ne
 have hv0_mem : v0 ∈ GoodV := max'_mem GoodV hGoodV_ne;have hv0T : v0 ∈ T := (mem_filter.mp hv0_mem).1;have hv0I := mem_Icc.mp (hTsub hv0T)
 let Tv := (T.filter (fun u => u <= v0)).filter (fun u => (u, v0) ∉ BadSym)
 have hTv_card : 98 * m <= 100 * Tv.card := by
   have hle_v0 : GoodV ⊆ T.filter (fun u => u <= v0) := fun u hu =>
     mem_filter.mpr ⟨(mem_filter.mp hu).1, le_max' GoodV u hu⟩
   have hcard_le_v0 : GoodV.card <= (T.filter (fun u => u <= v0)).card := card_le_card hle_v0
   have hsub_cov : T.filter (fun u => u <= v0) ⊆ Tv ∪ T.filter (fun u => (u, v0) ∈ BadSym) := by
     intro u hu
     by_cases hb : (u, v0) ∈ BadSym
     . exact mem_union_right _ (mem_filter.mpr ⟨(mem_filter.mp hu).1, hb⟩)
     . exact mem_union_left _ (mem_filter.mpr ⟨hu, hb⟩)
   have hcard_u := le_trans (card_le_card hsub_cov) (card_union_le _ _);have hbad_v0 := (mem_filter.mp hv0_mem).2;omega
 let runLenSet : ℕ -> Finset ℕ := fun d =>
   (range (N / d + 1)).filter (fun L => ∀ j ∈ Icc 1 L, j * d ∈ T)
 have hrunLenSet_ne : ∀ d, (runLenSet d).Nonempty := fun d =>
   ⟨0, mem_filter.mpr ⟨mem_range.mpr (Nat.zero_lt_succ _), fun j hj => by
     have := mem_Icc.mp hj; omega⟩⟩
 let runLen : ℕ -> ℕ := fun d =>
   if hd : 1 <= d then (runLenSet d).max' (hrunLenSet_ne d) else 0
 have hrunLen_spec : ∀ d, 1 <= d -> (∀ j ∈ Icc 1 (runLen d), j * d ∈ T) /\ (∀ L, (∀ j ∈ Icc 1 L, j * d ∈ T) -> L <= runLen d) := by
   intro d hd;dsimp only [runLen]; rw [dif_pos hd]
   constructor
   . exact (mem_filter.mp (max'_mem (runLenSet d) (hrunLenSet_ne d))).2
   . intro L hL
     have hLN : L <= N / d := by
       by_cases hL0 : L = 0
       . rw [hL0]; exact Nat.zero_le _
       . have hmem := hL L (mem_Icc.mpr ⟨by omega, le_rfl⟩)
         have hleN := (mem_Icc.mp (hTsub hmem)).2;exact (Nat.le_div_iff_mul_le (by omega)).mpr hleN
     exact le_max' (runLenSet d) L (mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le hLN), hL⟩)
 have hTv_cov : Tv ⊆ v0.divisors.biUnion (fun d => (Icc 1 (runLen d)).image (fun j => j * d)) := by
   intro u hu;obtain ⟨hu1, huNotBad⟩ := mem_filter.mp hu;obtain ⟨huT, huv0⟩ := mem_filter.mp hu1;have huI := mem_Icc.mp (hTsub huT)
   set g := Nat.gcd u v0
   have hg1 : 1 <= g := Nat.gcd_pos_of_pos_left v0 (by omega);have hgv0 : g ∣ v0 := Nat.gcd_dvd_right u v0;have hgu : g ∣ u := Nat.gcd_dvd_left u v0
   have hfill_uv : ∀ w, 1 <= w -> w <= v0 -> w % g = 0 -> w ∈ T := by
     by_cases huv_eq : u = v0
     . intro w hw1 hw2 hwm
       have hg_eq : g = v0 := by dsimp only [g]; rw [huv_eq, Nat.gcd_self]
       rw [hg_eq] at hwm;have hdvd : v0 ∣ w := Nat.dvd_of_mod_eq_zero hwm;have hle := Nat.le_of_dvd (by omega) hdvd;have : w = v0 := by omega
       rwa [this]
     . by_contra hnot
       apply huNotBad
       refine mem_filter.mpr ⟨mem_product.mpr ⟨huT, hv0T⟩, huv_eq, ?_⟩
       rwa [max_eq_right huv0]
   have hv0_div_le : v0 / g <= runLen g := (hrunLen_spec g hg1).2 (v0 / g) (fun j hj => by
     have hjI := mem_Icc.mp hj;have hjg : j * g <= v0 := le_trans (Nat.mul_le_mul_right g hjI.2) (Nat.div_mul_le_self v0 g)
     exact hfill_uv (j * g) (Nat.mul_pos hjI.1 hg1) hjg (Nat.mul_mod_left j g))
   refine mem_biUnion.mpr ⟨g, Nat.mem_divisors.mpr ⟨hgv0, by omega⟩, mem_image.mpr ⟨u / g, mem_Icc.mpr ⟨?_, le_trans (Nat.div_le_div_right huv0) hv0_div_le⟩, Nat.div_mul_cancel hgu⟩⟩
   exact (Nat.one_le_div_iff hg1).mpr (Nat.le_of_dvd (by omega) hgu)
 have hIcc_ne : (Icc 1 N).Nonempty := ⟨1, mem_Icc.mpr ⟨le_rfl, hN⟩⟩;obtain ⟨d0, hd0I, hd0_max⟩ := exists_max_image (Icc 1 N) runLen hIcc_ne
 set L0 := runLen d0
 have hd0_1 : 1 <= d0 := (mem_Icc.mp hd0I).1
 have hL0_lb : (m : ℝ) / (15 * Real.sqrt (Real.sqrt (N : ℝ))) <= (L0 : ℝ) := by
   have hTv_le : Tv.card <= v0.divisors.card * L0 := by
     calc Tv.card <= ∑ d ∈ v0.divisors, ((Icc 1 (runLen d)).image (fun j => j * d)).card :=
           le_trans (card_le_card hTv_cov) card_biUnion_le
       _ <= ∑ d ∈ v0.divisors, L0 := sum_le_sum fun d hd => by
           refine le_trans card_image_le ?_
           rw [Nat.card_Icc, Nat.add_sub_cancel];have hd_pos : 1 <= d := Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hd) (by omega);have hd_leN : d <= N := le_trans (Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_divisors hd)) hv0I.2;exact hd0_max d (mem_Icc.mpr ⟨hd_pos, hd_leN⟩)
       _ = v0.divisors.card * L0 := by rw [sum_const, smul_eq_mul]
   have hdv : (v0.divisors.card : ℝ) <= 12 * Real.sqrt (Real.sqrt (N : ℝ)) := by
     have h4 := card_divisors_pow_four_le hv0I.1
     have h4R : ((v0.divisors.card : ℝ)) ^ 4 <= (12 * Real.sqrt (Real.sqrt (N : ℝ))) ^ 4 := by
       have hsq : (Real.sqrt (Real.sqrt (N : ℝ))) ^ 4 = (N : ℝ) := by
         have h1 : (Real.sqrt (Real.sqrt (N : ℝ))) ^ 2 = Real.sqrt (N : ℝ) := Real.sq_sqrt (Real.sqrt_nonneg _)
         calc (Real.sqrt (Real.sqrt (N : ℝ))) ^ 4 = ((Real.sqrt (Real.sqrt (N : ℝ))) ^ 2) ^ 2 := by ring
           _ = (Real.sqrt (N : ℝ)) ^ 2 := by rw [h1]
           _ = (N : ℝ) := Real.sq_sqrt (Nat.cast_nonneg N)
       have h12 : (12 * Real.sqrt (Real.sqrt (N : ℝ))) ^ 4 = 20736 * (N : ℝ) := by
         calc (12 * Real.sqrt (Real.sqrt (N : ℝ))) ^ 4 = 12 ^ 4 * (Real.sqrt (Real.sqrt (N : ℝ))) ^ 4 := by ring
           _ = 20736 * (N : ℝ) := by rw [hsq]; norm_num
       rw [h12];have h4R' : ((v0.divisors.card : ℝ)) ^ 4 <= 19680 * (v0 : ℝ) := by exact_mod_cast h4
       have hv0N : (v0 : ℝ) <= (N : ℝ) := by exact_mod_cast hv0I.2
       linarith
     by_contra hlt; push Not at hlt;have hpow := pow_lt_pow_left₀ hlt (by positivity) (by norm_num : 4 ≠ 0);linarith
   have hTv_R : (98 / 100 : ℝ) * (m : ℝ) <= (Tv.card : ℝ) := by
     have : (98 : ℝ) * (m : ℝ) <= 100 * (Tv.card : ℝ) := by exact_mod_cast hTv_card
     linarith
   have hTv_leR : (Tv.card : ℝ) <= (v0.divisors.card : ℝ) * (L0 : ℝ) := by exact_mod_cast hTv_le
   have hprod : (v0.divisors.card : ℝ) * (L0 : ℝ) <= (12 * Real.sqrt (Real.sqrt (N : ℝ))) * (L0 : ℝ) := mul_le_mul_of_nonneg_right hdv (Nat.cast_nonneg _)
   have hden_pos : 0 < 15 * Real.sqrt (Real.sqrt (N : ℝ)) := by
     have : (0 : ℝ) < Real.sqrt (Real.sqrt (N : ℝ)) := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (by exact_mod_cast hN));positivity
   rw [div_le_iff₀ hden_pos];nlinarith
 let A0 := (Icc 1 L0).image (fun j => j * d0)
 have hA0_sub : A0 ⊆ T := by
   intro x hx;obtain ⟨j, hj, rfl⟩ := mem_image.mp hx;exact (hrunLen_spec d0 hd0_1).1 j hj
 have hA0_card : A0.card = L0 := by rw [card_image_of_injective _ (fun j1 j2 h => Nat.eq_of_mul_eq_mul_right (by omega : 0 < d0) h), Nat.card_Icc, Nat.add_sub_cancel]
 have hA0_ap : APSet A0 := by
   have hL0_pos : 1 <= L0 := by
     have hpos : (0 : ℝ) < (m : ℝ) / (15 * Real.sqrt (Real.sqrt (N : ℝ))) := by
       have : (0 : ℝ) < Real.sqrt (Real.sqrt (N : ℝ)) := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (by exact_mod_cast hN));positivity
     have h0 : (0 : ℝ) < (L0 : ℝ) := lt_of_lt_of_le hpos hL0_lb;exact_mod_cast h0
   refine ⟨d0, d0, fun n => n < L0, fun _ _ hn hmn => lt_of_le_of_lt hmn hn, hL0_pos, fun x => ?_⟩
   simp only [A0, mem_image, mem_Icc]
   constructor
   . rintro ⟨j, ⟨hj1, hj2⟩, rfl⟩
     refine ⟨j - 1, by omega, ?_⟩
     have : j = 1 + (j - 1) := by omega
     conv_lhs => rw [this]; rw [add_mul, one_mul]
   . rintro ⟨n, hn, rfl⟩
     exact ⟨n + 1, ⟨by omega, by omega⟩, by ring⟩
 have hL0_ub : 49 * L0 < 48 * m := by
   have := hnoAP A0 hA0_sub hA0_ap;rwa [hA0_card] at this
 have hU_V : N <= (L0 - L0 / 2) ^ 6 /\ L0 / 2 < L0 := by
   have hhalf : (m : ℝ) / (30 * Real.sqrt (Real.sqrt (N : ℝ))) - 2 <= ((L0 - L0 / 2 : ℕ) : ℝ) := by
     have h1 : (L0 : ℝ) / 2 - 1 <= ((L0 - L0 / 2 : ℕ) : ℝ) := by
       have hnat : L0 <= 2 * (L0 - L0 / 2) + 1 := by omega
       have hR : (L0 : ℝ) <= 2 * ((L0 - L0 / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast hnat
       linarith
     linarith [hL0_lb, show (m : ℝ) / (30 * Real.sqrt (Real.sqrt (N : ℝ))) = ((m : ℝ) / (15 * Real.sqrt (Real.sqrt (N : ℝ)))) / 2 by ring]
   have hpow : (N : ℝ) <= (((L0 - L0 / 2 : ℕ) : ℝ)) ^ 6 := le_trans hm_large (pow_le_pow_left₀ (by linarith) hhalf 6);have hNle : N <= (L0 - L0 / 2) ^ 6 := by exact_mod_cast hpow
   have hL0_ge4 : 4 <= L0 := by
     have h2x : (m : ℝ) / (15 * Real.sqrt (Real.sqrt (N : ℝ))) = 2 * ((m : ℝ) / (30 * Real.sqrt (Real.sqrt (N : ℝ)))) := by ring
     have : (4 : ℝ) <= (L0 : ℝ) := by linarith
     exact_mod_cast this
   exact ⟨hNle, by omega⟩
 have hpair_bad : ∀ w ∈ T \ A0,
     let bw := if d0 ∣ w then w / d0 else w
     ∀ k ∈ (Ioc (L0 / 2) L0).filter (fun k => Nat.Coprime k bw), (k * d0, w) ∈ BadSym := by
   intro w hw bw k hk;obtain ⟨hwT, hwNotA0⟩ := Finset.mem_sdiff.mp hw;obtain ⟨hkI, hkcop⟩ := mem_filter.mp hk;obtain ⟨hk1, hk2⟩ := mem_Ioc.mp hkI;have hkdT : k * d0 ∈ T := (hrunLen_spec d0 hd0_1).1 k (mem_Icc.mpr ⟨by omega, hk2⟩);have hne : k * d0 ≠ w := fun h => hwNotA0 (h ▸ mem_image.mpr ⟨k, mem_Icc.mpr ⟨by omega, hk2⟩, rfl⟩)
   refine mem_filter.mpr ⟨mem_product.mpr ⟨hkdT, hwT⟩, hne, ?_⟩
   intro hfill
   by_cases hdvd : d0 ∣ w
   ·
     have hbw : bw = w / d0 := if_pos hdvd;rw [hbw] at hkcop
     have hgcd : Nat.gcd (k * d0) w = d0 := by
       have hw_eq : w / d0 * d0 = w := Nat.div_mul_cancel hdvd
       conv_lhs => rw [<- hw_eq]
       rw [Nat.gcd_mul_right, hkcop.gcd_eq_one, one_mul]
     have hw_gt : (L0 + 1) * d0 <= w := by
       by_contra hlt
       have hqle : w / d0 <= L0 := by
         have hw_eq : w / d0 * d0 = w := Nat.div_mul_cancel hdvd;have : (L0 + 1) * d0 = L0 * d0 + d0 := by ring
         by_contra hgt;have : (L0 + 1) * d0 <= w / d0 * d0 := Nat.mul_le_mul_right d0 (by omega);omega
       have hqpos : 1 <= w / d0 := (Nat.one_le_div_iff (by omega)).mpr (Nat.le_of_dvd (mem_Icc.mp (hTsub hwT)).1 hdvd);exact hwNotA0 (mem_image.mpr ⟨w / d0, mem_Icc.mpr ⟨hqpos, hqle⟩, Nat.div_mul_cancel hdvd⟩)
     have hL01_mem : (L0 + 1) * d0 ∈ T := hfill ((L0 + 1) * d0) (by nlinarith) (le_trans hw_gt (le_max_right _ _)) (by rw [hgcd, Nat.mul_mod_left])
     have hL01_le := (hrunLen_spec d0 hd0_1).2 (L0 + 1) (fun j hj => by
       have hjI := mem_Icc.mp hj
       by_cases hjL : j <= L0
       . exact (hrunLen_spec d0 hd0_1).1 j (mem_Icc.mpr ⟨hjI.1, hjL⟩)
       . have : j = L0 + 1 := by omega
         subst this; exact hL01_mem)
     omega
   ·
     have hbw : bw = w := if_neg hdvd;rw [hbw] at hkcop
     set g := Nat.gcd d0 w
     have hgcd : Nat.gcd (k * d0) w = g := by
       dsimp only [g];rw [Nat.mul_comm k d0];exact hkcop.gcd_mul_right_cancel d0
     have hg1 : 1 <= g := Nat.gcd_pos_of_pos_left w (by omega);have hgd0 : g ∣ d0 := Nat.gcd_dvd_left d0 w;have hg_lt : g < d0 := lt_of_le_of_ne (Nat.le_of_dvd (by omega) hgd0) (fun h => hdvd (h ▸ Nat.gcd_dvd_right d0 w))
     have hq_ge2 : 2 <= d0 / g := by
       have hmul := Nat.div_mul_cancel hgd0;by_contra hlt;have hq1 : d0 / g <= 1 := by omega
       have : d0 / g * g <= 1 * g := Nat.mul_le_mul_right g hq1;omega
     have hkd_div : k * (d0 / g) * g = k * d0 := by
       calc k * (d0 / g) * g = k * (d0 / g * g) := by ring
         _ = k * d0 := by rw [Nat.div_mul_cancel hgd0]
     have hrun_g : k * (d0 / g) <= runLen g := (hrunLen_spec g hg1).2 (k * (d0 / g)) (fun j hj => by
       have hjI := mem_Icc.mp hj
       have hjle : j * g <= k * d0 := by
         calc j * g <= k * (d0 / g) * g := Nat.mul_le_mul_right g hjI.2
           _ = k * d0 := hkd_div
       exact hfill (j * g) (Nat.mul_pos hjI.1 hg1) (le_trans hjle (le_max_left _ _)) (by rw [hgcd, Nat.mul_mod_left]))
     have hgN : g <= N := le_trans (le_of_lt hg_lt) (mem_Icc.mp hd0I).2;have hmax_g := hd0_max g (mem_Icc.mpr ⟨hg1, hgN⟩);have h2k : L0 < k * (d0 / g) := lt_of_lt_of_le (by omega : L0 < k * 2) (Nat.mul_le_mul_left k hq_ge2);omega
 have hBadSym_lb : ((T \ A0).card : ℝ) * (((L0 - L0 / 2 : ℕ) : ℝ) / (4 * ((Nat.log 2 N + 1 : ℕ) : ℝ))) <= (BadSym.card : ℝ) := by
   let Img := (T \ A0).biUnion (fun w =>
     ((Ioc (L0 / 2) L0).filter (fun k => Nat.Coprime k (if d0 ∣ w then w / d0 else w))).image (fun k => (k * d0, w)))
   have hImg_sub : Img ⊆ BadSym := by
     intro p hp;obtain ⟨w, hw, hpw⟩ := mem_biUnion.mp hp;obtain ⟨k, hk, rfl⟩ := mem_image.mp hpw;exact hpair_bad w hw k hk
   have hdisj_w : Set.PairwiseDisjoint ((T \ A0 : Finset ℕ) : Set ℕ) (fun w =>
       ((Ioc (L0 / 2) L0).filter (fun k => Nat.Coprime k (if d0 ∣ w then w / d0 else w))).image (fun k => (k * d0, w))) := by
     intro w1 _ w2 _ hne;change Disjoint _ _;rw [Finset.disjoint_left]; intro p h1 h2;obtain ⟨k1, -, rfl⟩ := mem_image.mp h1;obtain ⟨k2, -, heq⟩ := mem_image.mp h2;exact hne (congrArg Prod.snd heq).symm
   have hcard_img : (Img.card : ℝ) = ∑ w ∈ T \ A0, (((Ioc (L0 / 2) L0).filter (fun k => Nat.Coprime k (if d0 ∣ w then w / d0 else w))).card : ℝ) := by
     have hnat : Img.card = ∑ w ∈ T \ A0, ((Ioc (L0 / 2) L0).filter (fun k => Nat.Coprime k (if d0 ∣ w then w / d0 else w))).card := by
       rw [card_biUnion hdisj_w];apply sum_congr rfl; intro w _
       exact card_image_of_injective _ (fun k1 k2 h =>
         Nat.eq_of_mul_eq_mul_right (by omega : 0 < d0) (congrArg Prod.fst h))
     exact_mod_cast hnat
   have hterm_w : ∀ w ∈ T \ A0, ((L0 - L0 / 2 : ℕ) : ℝ) / (4 * ((Nat.log 2 N + 1 : ℕ) : ℝ)) <= (((Ioc (L0 / 2) L0).filter (fun k => Nat.Coprime k (if d0 ∣ w then w / d0 else w))).card : ℝ) := by
     intro w hw;have hwI := mem_Icc.mp (hTsub (Finset.mem_sdiff.mp hw).1)
     set bw := if d0 ∣ w then w / d0 else w
     have hbw1 : 1 <= bw := by
       dsimp only [bw]; split_ifs with hdvd
       . exact (Nat.one_le_div_iff (by omega)).mpr (Nat.le_of_dvd hwI.1 hdvd)
       . exact hwI.1
     have hbwN : bw <= N := by
       dsimp only [bw]; split_ifs
       . exact le_trans (Nat.div_le_self w d0) hwI.2
       . exact hwI.2
     exact hcop_int bw (L0 / 2) L0 hbw1 hbwN hU_V.2 hU_V.1
   have hle : (Img.card : ℝ) <= (BadSym.card : ℝ) := by exact_mod_cast card_le_card hImg_sub
   refine le_trans ?_ hle
   rw [hcard_img]
   refine le_trans ?_ (sum_le_sum hterm_w)
   rw [sum_const, nsmul_eq_mul]
 have hTA0 : (m : ℝ) / 49 <= ((T \ A0).card : ℝ) := by
   have hadd := card_sdiff_add_card_eq_card hA0_sub;rw [hA0_card, hTcard] at hadd;have h1 : m <= 49 * (T \ A0).card := by omega
   have h1R : (m : ℝ) <= 49 * ((T \ A0).card : ℝ) := by exact_mod_cast h1
   linarith
 have hhalf_L0 : (m : ℝ) / (30 * Real.sqrt (Real.sqrt (N : ℝ))) <= ((L0 - L0 / 2 : ℕ) : ℝ) := by
   have hnat : L0 <= 2 * (L0 - L0 / 2) := by omega
   have hR : (L0 : ℝ) <= 2 * ((L0 - L0 / 2 : ℕ) : ℝ) := by exact_mod_cast hnat
   linarith [hL0_lb, show (m : ℝ) / (30 * Real.sqrt (Real.sqrt (N : ℝ))) = ((m : ℝ) / (15 * Real.sqrt (Real.sqrt (N : ℝ)))) / 2 by ring]
 have hlogpos : (0 : ℝ) < 4 * ((Nat.log 2 N + 1 : ℕ) : ℝ) := by positivity
 have hsqpos : (0 : ℝ) < Real.sqrt (Real.sqrt (N : ℝ)) := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (by exact_mod_cast hN))
 have hfrac : (m : ℝ) / (120 * Real.sqrt (Real.sqrt (N : ℝ)) * ((Nat.log 2 N + 1 : ℕ) : ℝ)) <= ((L0 - L0 / 2 : ℕ) : ℝ) / (4 * ((Nat.log 2 N + 1 : ℕ) : ℝ)) := by
   have h1 := div_le_div_of_nonneg_right hhalf_L0 (le_of_lt hlogpos);have h2 : (m : ℝ) / (30 * Real.sqrt (Real.sqrt (N : ℝ))) / (4 * ((Nat.log 2 N + 1 : ℕ) : ℝ)) = (m : ℝ) / (120 * Real.sqrt (Real.sqrt (N : ℝ)) * ((Nat.log 2 N + 1 : ℕ) : ℝ)) := by ring
   linarith
 have hprod := mul_le_mul hTA0 hfrac (by positivity) (Nat.cast_nonneg _);have hprod_eq : (m : ℝ) / 49 * ((m : ℝ) / (120 * Real.sqrt (Real.sqrt (N : ℝ)) * ((Nat.log 2 N + 1 : ℕ) : ℝ))) = (m : ℝ) ^ 2 / (5880 * Real.sqrt (Real.sqrt (N : ℝ)) * ((Nat.log 2 N + 1 : ℕ) : ℝ)) := by ring
 have hsymR : (BadSym.card : ℝ) = 2 * (Bad.card : ℝ) := by exact_mod_cast hBad_sym
 have h2_le : (m : ℝ) ^ 2 / (100000 * Real.sqrt (Real.sqrt (N : ℝ)) * ((Nat.log 2 N + 1 : ℕ) : ℝ)) <= ((m : ℝ) ^ 2 / (5880 * Real.sqrt (Real.sqrt (N : ℝ)) * ((Nat.log 2 N + 1 : ℕ) : ℝ))) / 2 := by
   have h1 : ((m : ℝ) ^ 2 / (5880 * Real.sqrt (Real.sqrt (N : ℝ)) * ((Nat.log 2 N + 1 : ℕ) : ℝ))) / 2 = (m : ℝ) ^ 2 / (11760 * Real.sqrt (Real.sqrt (N : ℝ)) * ((Nat.log 2 N + 1 : ℕ) : ℝ)) := by ring
   rw [h1];apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity);have hlog1 : (0 : ℝ) < ((Nat.log 2 N + 1 : ℕ) : ℝ) := by positivity
   nlinarith [mul_pos hsqpos hlog1]
 linarith
lemma large_nonAP_noap_bound {N s : ℕ} (hN : 1 <= N) (hs : 1000 <= s) (hcop_int : ∀ (b U V : ℕ), 1 <= b -> b <= N -> U < V -> N <= (V - U) ^ 6 -> ((V - U : ℕ) : ℝ) / (4 * ((Nat.log 2 N + 1 : ℕ) : ℝ)) <= (((Ioc U V).filter (fun q => Nat.Coprime q b)).card : ℝ)) (hs_large : (N : ℝ) <= ((((98 / 100 : ℝ) * (s : ℝ)) / (30 * Real.sqrt (Real.sqrt (N : ℝ))) - 2) ^ 6)) (hs_pos : 4 <= ((98 / 100 : ℝ) * (s : ℝ)) / (30 * Real.sqrt (Real.sqrt (N : ℝ)))) {B : Finset (Finset ℕ)} (hF : IsWellInter N B) (hB : ∀ S ∈ B, s <= S.card /\ ∀ P : Finset ℕ, P ⊆ S -> APSet P -> 25 * P.card < 24 * S.card) :
   (B.card : ℝ) <= 20000000 * (N : ℝ) ^ 3 * Real.sqrt (Real.sqrt (N : ℝ)) * ((Nat.log 2 N + 1 : ℕ) : ℝ) / ((s : ℝ) ^ 3) := by
 classical
 let Tri : Finset ℕ -> Finset (ℕ × ℕ × ℕ) := fun S =>
   (S ×ˢ (S ×ˢ S)).filter (fun t => t.1 < t.2.1 /\ t.2.1 < t.2.2 /\ ¬ (∀ w, t.1 <= w -> w <= t.2.2 -> w % Nat.gcd (t.2.1 - t.1) (t.2.2 - t.1) = t.1 % Nat.gcd (t.2.1 - t.1) (t.2.2 - t.1) -> w ∈ S))
 have hTri_disj : Set.PairwiseDisjoint (B : Set (Finset ℕ)) Tri := by
   intro S hS T hT hST;change Disjoint (Tri S) (Tri T);rw [Finset.disjoint_left];intro t htS htT;obtain ⟨htSP, hlt1, hlt2, hnotfill⟩ := mem_filter.mp htS;obtain ⟨hxS, hyzS⟩ := mem_product.mp htSP;obtain ⟨hyS, hzS⟩ := mem_product.mp hyzS;obtain ⟨htTP, -⟩ := mem_filter.mp htT;obtain ⟨hxT, hyzT⟩ := mem_product.mp htTP;obtain ⟨hyT, hzT⟩ := mem_product.mp hyzT
   have hnotdt : ¬ IsDeltaTriplet B S t.1 t.2.1 t.2.2 := fun hdt =>
     hdt.2.2.2.2.2.2 T (mem_coe.mp hT) hST.symm ⟨hxT, hyT, hzT⟩
   have hnu := nu_triplet_fill hF (mem_coe.mp hS) hxS hyS hzS (ne_of_lt hlt1) (ne_of_lt (lt_trans hlt1 hlt2)) (ne_of_lt hlt2) hnotdt;apply hnotfill;intro w hw1 hw2 hwm;have hd1 : distNat t.1 t.2.1 = t.2.1 - t.1 := distNat_eq_sub (le_of_lt hlt1);have hd2 : distNat t.1 t.2.2 = t.2.2 - t.1 := distNat_eq_sub (le_of_lt (lt_trans hlt1 hlt2));rw [hd1, hd2] at hnu;exact hnu.2.2.2 w (by omega) (by omega) hwm
 have hTri_lb : ∀ S ∈ B, (s : ℝ) ^ 3 / (20000000 * Real.sqrt (Real.sqrt (N : ℝ)) * ((Nat.log 2 N + 1 : ℕ) : ℝ)) <= ((Tri S).card : ℝ) := by
   intro S hS;obtain ⟨hSs, hnoAP⟩ := hB S hS
   set h := S.card
   let sl := S.sort (· <= ·)
   have hsl_len : sl.length = h := length_sort _;have hsl_nodup : sl.Nodup := S.sort_nodup (· <= ·);have hsl_sorted : sl.Pairwise (· < ·) := ((S.pairwise_sort (· <= ·)).and hsl_nodup).imp (fun p => lt_of_le_of_ne p.1 p.2)
   set k := h / 50
   let SmallX := (sl.take k).toFinset
   have hSmallX_card : SmallX.card = k := by
     rw [List.toFinset_card_of_nodup hsl_nodup.take, List.length_take, hsl_len];exact min_eq_left (by omega)
   have hSmallX_sub : SmallX ⊆ S := fun x hx =>
     (mem_sort (· <= ·)).mp (List.mem_of_mem_take (List.mem_toFinset.mp hx))
   have hSmallX_gt : ∀ x ∈ SmallX, h - k <= (S.filter (fun a => x < a)).card := by
     intro x hx;obtain ⟨idx, hidx_eq⟩ := List.mem_iff_get.mp (List.mem_toFinset.mp hx);have hidx_lt : idx.1 < k := by have hlen := List.length_take_le k sl; have := idx.2; omega
     have hxeq : x = sl.get ⟨idx.1, by omega⟩ := by rw [<- hidx_eq]; simp [List.get_eq_getElem]
     have hdrop_sub : (sl.drop k).toFinset ⊆ S.filter (fun a => x < a) := by
       intro a ha;have ham := List.mem_toFinset.mp ha;have haS : a ∈ S := (mem_sort (· <= ·)).mp (List.mem_of_mem_drop ham);obtain ⟨jdx, hjdx_eq⟩ := List.mem_iff_get.mp ham;have haeq : a = sl.get ⟨k + jdx.1, by have := jdx.2; simp at this; omega⟩ := by rw [<- hjdx_eq]; simp [List.get_eq_getElem]
       refine mem_filter.mpr ⟨haS, ?_⟩
       rw [hxeq, haeq];exact List.pairwise_iff_get.mp hsl_sorted ⟨idx.1, by omega⟩ ⟨k + jdx.1, by have := jdx.2; simp at this; omega⟩ (by simp; omega)
     have hdrop_card : (sl.drop k).toFinset.card = h - k := by rw [List.toFinset_card_of_nodup hsl_nodup.drop, List.length_drop, hsl_len]
     rw [<- hdrop_card];exact card_le_card hdrop_sub
   have hper_x : ∀ x ∈ SmallX, (s : ℝ) ^ 2 / (200000 * Real.sqrt (Real.sqrt (N : ℝ)) * ((Nat.log 2 N + 1 : ℕ) : ℝ)) <= (((Tri S).filter (fun t => t.1 = x)).card : ℝ) := by
     intro x hx
     let Sx := S.filter (fun a => x < a)
     let Tx := Sx.image (fun a => a - x)
     set m := Tx.card
     have hm_eq : m = Sx.card := card_image_of_injOn (fun a ha b hb hab => by
       have := (mem_filter.mp (mem_coe.mp ha)).2;have := (mem_filter.mp (mem_coe.mp hb)).2
       omega)
     have hm_ge : h - k <= m := by rw [hm_eq]; exact hSmallX_gt x hx
     have hm_ge_98 : 98 * s <= 100 * m := by omega
     have hm200 : 200 <= m := by omega
     have hTx_sub : Tx ⊆ Icc 1 N := by
       intro u hu;obtain ⟨a, ha, rfl⟩ := mem_image.mp hu;have haS := (mem_filter.mp ha).1;have hxa := (mem_filter.mp ha).2;have haI := mem_Icc.mp (hF.1 S hS haS);exact mem_Icc.mpr ⟨by omega, by omega⟩
     have hTx_noAP : ∀ P : Finset ℕ, P ⊆ Tx -> APSet P -> 49 * P.card < 48 * m := by
       intro P hPsub hPap
       let P' := P.image (fun u => x + u)
       have hP'_sub : P' ⊆ S := by
         intro y hy;obtain ⟨u, hu, rfl⟩ := mem_image.mp hy;obtain ⟨a, ha, hax⟩ := mem_image.mp (hPsub hu);have hxa := (mem_filter.mp ha).2;have : x + (a - x) = a := by omega
         rw [<- hax, this]; exact (mem_filter.mp ha).1
       have hP'_card : P'.card = P.card := card_image_of_injective _ (fun u1 u2 h => by omega)
       have hP'_ap : APSet P' := by
         obtain ⟨a, d, I, hI, hI0, hX⟩ := hPap
         refine ⟨x + a, d, I, hI, hI0, fun y => ?_⟩
         simp only [P', mem_image]
         constructor
         . rintro ⟨u, hu, rfl⟩
           obtain ⟨n, hn, rfl⟩ := (hX u).mp hu;exact ⟨n, hn, by omega⟩
         . rintro ⟨n, hn, rfl⟩
           exact ⟨a + n * d, (hX _).mpr ⟨n, hn, rfl⟩, by omega⟩
       have h1 := hnoAP P' hP'_sub hP'_ap;rw [hP'_card] at h1;have : 49 * h <= 50 * m := by omega
       omega
     have hm_R : (98 / 100 : ℝ) * (s : ℝ) <= (m : ℝ) := by
       have : (98 : ℝ) * (s : ℝ) <= 100 * (m : ℝ) := by exact_mod_cast hm_ge_98
       linarith
     have hden_pos : (0 : ℝ) < 30 * Real.sqrt (Real.sqrt (N : ℝ)) := by
       have : (0 : ℝ) < Real.sqrt (Real.sqrt (N : ℝ)) := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (by exact_mod_cast hN));positivity
     have hm_div : ((98 / 100 : ℝ) * (s : ℝ)) / (30 * Real.sqrt (Real.sqrt (N : ℝ))) <= (m : ℝ) / (30 * Real.sqrt (Real.sqrt (N : ℝ))) := div_le_div_of_nonneg_right hm_R (le_of_lt hden_pos);have h1side := simonovits_sos_one_side hN hm200 hcop_int (le_trans hs_large (pow_le_pow_left₀ (by linarith) (by linarith) 6)) (le_trans hs_pos hm_div) hTx_sub rfl hTx_noAP
     have hmap_tri : ((Tx ×ˢ Tx).filter (fun p => p.1 < p.2 /\ ¬ (∀ w, 1 <= w -> w <= p.2 -> w % Nat.gcd p.1 p.2 = 0 -> w ∈ Tx))).card <= ((Tri S).filter (fun t => t.1 = x)).card := by
       refine card_le_card_of_injOn (fun p => (x, x + p.1, x + p.2)) ?_ ?_
       . intro p hp
         obtain ⟨hpP, hlt, hnotfill⟩ := mem_filter.mp (mem_coe.mp hp);obtain ⟨hp1, hp2⟩ := mem_product.mp hpP;obtain ⟨a1, ha1, hax1⟩ := mem_image.mp hp1;obtain ⟨a2, ha2, hax2⟩ := mem_image.mp hp2;have hxa1 := (mem_filter.mp ha1).2;have hxa2 := (mem_filter.mp ha2).2;have hp1pos : 1 <= p.1 := by omega
         have heq1 : x + p.1 = a1 := by omega
         have heq2 : x + p.2 = a2 := by omega
         have hmem1 : x + p.1 ∈ S := by rw [heq1]; exact (mem_filter.mp ha1).1
         have hmem2 : x + p.2 ∈ S := by rw [heq2]; exact (mem_filter.mp ha2).1
         refine mem_coe.mpr (mem_filter.mpr ⟨mem_filter.mpr ⟨mem_product.mpr ⟨hSmallX_sub hx, mem_product.mpr ⟨hmem1, hmem2⟩⟩,
            by dsimp only; omega, by dsimp only; omega, ?_⟩, rfl⟩)
         dsimp only;intro hfillS;apply hnotfill;intro w hw1 hw2 hwm
         have hxwS : x + w ∈ S := hfillS (x + w) (by omega) (by omega) (by
           have hsub1 : x + p.1 - x = p.1 := Nat.add_sub_cancel_left x p.1;have hsub2 : x + p.2 - x = p.2 := Nat.add_sub_cancel_left x p.2
           rw [hsub1, hsub2, Nat.add_mod, hwm, add_zero, Nat.mod_mod])
         exact mem_image.mpr ⟨x + w, mem_filter.mpr ⟨hxwS, by omega⟩, Nat.add_sub_cancel_left x w⟩
       . intro p1 _ p2 _ heq
         have h1 : x + p1.1 = x + p2.1 := congrArg (fun t => t.2.1) heq;have h2 : x + p1.2 = x + p2.2 := congrArg (fun t => t.2.2) heq;exact Prod.ext (by omega) (by omega)
     have hmapR : (((Tx ×ˢ Tx).filter (fun p => p.1 < p.2 /\ ¬ (∀ w, 1 <= w -> w <= p.2 -> w % Nat.gcd p.1 p.2 = 0 -> w ∈ Tx))).card : ℝ) <= (((Tri S).filter (fun t => t.1 = x)).card : ℝ) := by exact_mod_cast hmap_tri
     have hm2 : (s : ℝ) ^ 2 / 2 <= (m : ℝ) ^ 2 := by
       have hs0 : (0 : ℝ) <= (s : ℝ) := Nat.cast_nonneg s;nlinarith [sq_nonneg ((s : ℝ))]
     have hsq_pos : (0 : ℝ) < Real.sqrt (Real.sqrt (N : ℝ)) := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (by exact_mod_cast hN));have hden2 : (0 : ℝ) < 100000 * Real.sqrt (Real.sqrt (N : ℝ)) * ((Nat.log 2 N + 1 : ℕ) : ℝ) := by positivity
     have hcmp : (s : ℝ) ^ 2 / (200000 * Real.sqrt (Real.sqrt (N : ℝ)) * ((Nat.log 2 N + 1 : ℕ) : ℝ)) <= (m : ℝ) ^ 2 / (100000 * Real.sqrt (Real.sqrt (N : ℝ)) * ((Nat.log 2 N + 1 : ℕ) : ℝ)) := by
       have h1 := div_le_div_of_nonneg_right hm2 (le_of_lt hden2);have h2 : (s : ℝ) ^ 2 / 2 / (100000 * Real.sqrt (Real.sqrt (N : ℝ)) * ((Nat.log 2 N + 1 : ℕ) : ℝ)) = (s : ℝ) ^ 2 / (200000 * Real.sqrt (Real.sqrt (N : ℝ)) * ((Nat.log 2 N + 1 : ℕ) : ℝ)) := by ring
       linarith
     linarith
   have hdisj_x : Set.PairwiseDisjoint (SmallX : Set ℕ) (fun x => (Tri S).filter (fun t => t.1 = x)) := by
     intro x1 _ x2 _ hne;change Disjoint _ _;rw [Finset.disjoint_left]; intro t h1 h2;exact hne ((mem_filter.mp h1).2.symm.trans (mem_filter.mp h2).2)
   have hsub_tri : SmallX.biUnion (fun x => (Tri S).filter (fun t => t.1 = x)) ⊆ Tri S := by intro t ht; obtain ⟨_, -, h2⟩ := mem_biUnion.mp ht; exact (mem_filter.mp h2).1
   have hsum_tri : ∑ x ∈ SmallX, (((Tri S).filter (fun t => t.1 = x)).card : ℝ) <= ((Tri S).card : ℝ) := by
     have h1 := card_le_card hsub_tri;rw [card_biUnion hdisj_x] at h1;exact_mod_cast h1
   have hlb_sum : (SmallX.card : ℝ) * ((s : ℝ) ^ 2 / (200000 * Real.sqrt (Real.sqrt (N : ℝ)) * ((Nat.log 2 N + 1 : ℕ) : ℝ))) <= ((Tri S).card : ℝ) := by
     refine le_trans ?_ hsum_tri
     refine le_trans ?_ (sum_le_sum hper_x)
     rw [sum_const, nsmul_eq_mul]
   have hk_ge : (s : ℝ) / 100 <= (SmallX.card : ℝ) := by
     rw [hSmallX_card];have h1 : s <= 100 * k := by omega
     have h1R : (s : ℝ) <= 100 * (k : ℝ) := by exact_mod_cast h1
     linarith
   have hsq_pos : (0 : ℝ) < Real.sqrt (Real.sqrt (N : ℝ)) := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (by exact_mod_cast hN));have hmul := mul_le_mul_of_nonneg_right hk_ge (show (0 : ℝ) <= (s : ℝ) ^ 2 / (200000 * Real.sqrt (Real.sqrt (N : ℝ)) * ((Nat.log 2 N + 1 : ℕ) : ℝ)) by positivity);have hrew : (s : ℝ) / 100 * ((s : ℝ) ^ 2 / (200000 * Real.sqrt (Real.sqrt (N : ℝ)) * ((Nat.log 2 N + 1 : ℕ) : ℝ))) = (s : ℝ) ^ 3 / (20000000 * Real.sqrt (Real.sqrt (N : ℝ)) * ((Nat.log 2 N + 1 : ℕ) : ℝ)) := by ring
   linarith
 have htot_le : (∑ S ∈ B, ((Tri S).card : ℝ)) <= (N : ℝ) ^ 3 := by
   have hsub : B.biUnion Tri ⊆ Icc 1 N ×ˢ (Icc 1 N ×ˢ Icc 1 N) := by
     intro t ht;obtain ⟨S, hSB, htS⟩ := mem_biUnion.mp ht;obtain ⟨htP, -⟩ := mem_filter.mp htS;obtain ⟨h1, h23⟩ := mem_product.mp htP;obtain ⟨h2, h3⟩ := mem_product.mp h23;exact mem_product.mpr ⟨hF.1 S hSB h1, mem_product.mpr ⟨hF.1 S hSB h2, hF.1 S hSB h3⟩⟩
   have hcard := card_le_card hsub;rw [card_biUnion hTri_disj, card_product, card_product, Nat.card_Icc, Nat.add_sub_cancel] at hcard;have hR : (∑ S ∈ B, ((Tri S).card : ℝ)) <= (N : ℝ) * ((N : ℝ) * (N : ℝ)) := by exact_mod_cast hcard
   linarith [show (N : ℝ) * ((N : ℝ) * (N : ℝ)) = (N : ℝ) ^ 3 by ring]
 have hB_mul : (B.card : ℝ) * ((s : ℝ) ^ 3 / (20000000 * Real.sqrt (Real.sqrt (N : ℝ)) * ((Nat.log 2 N + 1 : ℕ) : ℝ))) <= (N : ℝ) ^ 3 := by
   refine le_trans ?_ htot_le
   refine le_trans ?_ (sum_le_sum hTri_lb)
   rw [sum_const, nsmul_eq_mul]
 have hsq_pos : (0 : ℝ) < Real.sqrt (Real.sqrt (N : ℝ)) := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (by exact_mod_cast hN));have hs3_pos : (0 : ℝ) < (s : ℝ) ^ 3 := by positivity
 have hden_pos : (0 : ℝ) < 20000000 * Real.sqrt (Real.sqrt (N : ℝ)) * ((Nat.log 2 N + 1 : ℕ) : ℝ) := by positivity
 rw [le_div_iff₀ hs3_pos];have h1 := mul_le_mul_of_nonneg_right hB_mul (le_of_lt hden_pos);have h2 : (B.card : ℝ) * ((s : ℝ) ^ 3 / (20000000 * Real.sqrt (Real.sqrt (N : ℝ)) * ((Nat.log 2 N + 1 : ℕ) : ℝ))) * (20000000 * Real.sqrt (Real.sqrt (N : ℝ)) * ((Nat.log 2 N + 1 : ℕ) : ℝ)) = (B.card : ℝ) * (s : ℝ) ^ 3 := by field_simp
 linarith
lemma apSet_of_all_fill {W : Finset ℕ} {c : ℕ} (hcW : c ∈ W) (hfill : ∀ x ∈ W, ∀ y ∈ W, x ≠ c -> y ≠ c -> x ≠ y -> ∀ w, min c (min x y) <= w -> w <= max c (max x y) -> w % Nat.gcd (distNat c x) (distNat c y) = c % Nat.gcd (distNat c x) (distNat c y) -> w ∈ W) : APSet W /\ (2 <= W.card -> ∃ d ≥ 1, W = runPart W c d /\ ∀ x ∈ W, d ∣ distNat c x) := by
 by_cases h2 : 2 <= W.card
 . have hne_er : (W.erase c).Nonempty := by
     have : 1 <= (W.erase c).card := by rw [card_erase_of_mem hcW]; omega
     exact card_pos.mp this
   obtain ⟨u, hu_mem, hu_min⟩ := exists_min_image (W.erase c) (fun x => distNat c x) hne_er;obtain ⟨huc, huW⟩ := Finset.mem_erase.mp hu_mem
   set d := distNat c u
   have hd_pos : 1 <= d := distNat_pos_of_ne huc.symm
   have hd_dvd : ∀ x ∈ W, d ∣ distNat c x := by
     intro x hx
     by_cases hxc : x = c
     . subst hxc; simp [distNat]
     by_cases hxu : x = u
     . subst hxu; exact dvd_refl _
     set g := Nat.gcd d (distNat c x)
     have hg_pos : 1 <= g := Nat.gcd_pos_of_pos_left _ hd_pos;have hg_le : g <= d := Nat.le_of_dvd hd_pos (Nat.gcd_dvd_left _ _)
     have hd_le_g : d <= g := by
       rcases lt_or_gt_of_ne huc.symm with hlt | hgt
       . have hu_eq : u = c + d := by dsimp only [d]; unfold distNat; omega
         have hcgW : c + g ∈ W := hfill u huW x hx huc hxc (Ne.symm hxu) (c + g) (by omega) (by omega) (by rw [Nat.add_mod_right])
         have hmin : d <= distNat c (c + g) := hu_min (c + g) (Finset.mem_erase.mpr ⟨by omega, hcgW⟩);unfold distNat at hmin; omega
       . have hle_g : g <= c := by dsimp only [d] at hg_le; unfold distNat at hg_le; omega
         have hu_eq : u + d = c := by dsimp only [d]; unfold distNat; omega
         have hcgW : c - g ∈ W := hfill u huW x hx huc hxc (Ne.symm hxu) (c - g) (by omega) (by omega) (by
             change (c - g) % g = c % g;have h1 : c - g + g = c := Nat.sub_add_cancel hle_g
             conv_rhs => rw [<- h1]
             rw [Nat.add_mod_right])
         have hmin : d <= distNat c (c - g) := hu_min (c - g) (Finset.mem_erase.mpr ⟨by omega, hcgW⟩);unfold distNat at hmin; omega
     have hgeq : g = d := by omega
     exact hgeq ▸ Nat.gcd_dvd_right d (distNat c x)
   have hW_eq : W = runPart W c d := by
     refine Finset.Subset.antisymm (fun x hx => ?_) (runPart_subset W c d)
     rw [mem_runPart];have hdvd := hd_dvd x hx
     have hmod : x % d = c % d := by
       unfold distNat at hdvd
       rcases le_total c x with hle | hle
       . rw [max_eq_right hle, min_eq_left hle] at hdvd; exact ((Nat.modEq_iff_dvd' hle).mpr hdvd).symm
       . rw [max_eq_left hle, min_eq_right hle] at hdvd; exact (Nat.modEq_iff_dvd' hle).mpr hdvd
     refine ⟨hx, hmod, fun w hw1 hw2 hwm => ?_⟩
     by_cases hxc : x = c
     . rw [hxc] at hw1 hw2
       have : w = c := by omega
       rwa [this]
     by_cases hxu : x = u
     . rw [hxu] at hw1 hw2
       rcases le_total c u with hle | hle
       . by_cases hwc : w = c
         . rwa [hwc]
         . have hdw : d ∣ w - c := (Nat.modEq_iff_dvd' (by omega)).mp hwm.symm
           have hle_w := Nat.le_of_dvd (by omega) hdw;have : w = u := by dsimp only [d] at hle_w; unfold distNat at hle_w; omega
           rwa [this]
       . by_cases hwc : w = c
         . rwa [hwc]
         . have hdw : d ∣ c - w := (Nat.modEq_iff_dvd' (by omega)).mp hwm
           have hle_w := Nat.le_of_dvd (by omega) hdw;have : w = u := by dsimp only [d] at hle_w; unfold distNat at hle_w; omega
           rwa [this]
     . have hg_eq : Nat.gcd d (distNat c x) = d := Nat.gcd_eq_left hdvd
       exact hfill u huW x hx huc hxc (Ne.symm hxu) w (by omega) (by omega) (by rwa [hg_eq])
   exact ⟨hW_eq ▸ runPart_isAP hcW hd_pos, fun _ => ⟨d, hd_pos, hW_eq, hd_dvd⟩⟩
 . obtain ⟨l, hl, hAP⟩ := isAP_of_card_le_two W ⟨c, hcW⟩ (by omega)
   exact ⟨apSet_of_isAP W l hl hAP, fun h => absurd h h2⟩
lemma ap_forb_step {N c d : ℕ} (_hN : 1 <= N) (_hc : c ∈ Icc 1 N) (hd1 : 1 <= d) {Ed : Finset (Finset ℕ)} (hEd : ∀ S ∈ Ed, S ⊆ Icc 1 N /\ 3 <= S.card /\ c ∈ S /\ (∀ x ∈ S, x % d = c % d) /\ (∀ x ∈ S, ∀ y ∈ S, ∀ z, min x y <= z -> z <= max x y -> z % d = c % d -> z ∈ S)) : ∃ Fd : Finset (Finset ℕ), Fd ⊆ ((Icc 1 N).erase c).powersetCard 2 /\ (∀ e ∈ Fd, ∀ x ∈ e, ∀ y ∈ e, x ≠ y -> Nat.gcd (distNat c x) (distNat c y) = d) /\ (∀ e ∈ Fd, ∃ E0 ∈ Ed, e ⊆ E0) /\ (Ed.card : ℝ) <= (99 / 100 : ℝ) * (Fd.card : ℝ) + 55 /\ (Ed.card : ℝ) <= (Fd.card : ℝ) + 40 /\
     (∀ X0 : Finset (Finset ℕ), 400 <= N -> 40 * c <= N -> (∀ e ∈ X0, ∃ x y, e = {x, y} /\ c < x /\ 40 * x <= N /\ 39 * N <= 40 * y /\ y <= N) -> (Ed.card : ℝ) <= ((Fd \ X0).card : ℝ) + 42) := by
 classical
 rcases Ed.eq_empty_or_nonempty with rfl | hEd_ne
 . refine ⟨∅, Finset.empty_subset _, fun _ h => absurd h (notMem_empty _), fun _ h => absurd h (notMem_empty _), ?_, ?_, fun _ _ _ _ => ?_⟩ <;> simp
 let leftOff : Finset ℕ -> ℕ := fun S => if h : S.Nonempty then (c - S.min' h) / d else 0
 let rightOff : Finset ℕ -> ℕ := fun S => if h : S.Nonempty then (S.max' h - c) / d else 0
 have hoff_eq : ∀ S ∈ Ed, (∃ hne : S.Nonempty, S.min' hne = c - leftOff S * d /\ S.max' hne = c + rightOff S * d) /\
     leftOff S * d <= c /\ c + rightOff S * d <= N /\
     (∀ x, x ∈ S ↔ c - leftOff S * d <= x /\ x <= c + rightOff S * d /\ x % d = c % d) := by
   intro S hS;obtain ⟨hSsub, hS3, hcS, hmod, hfill⟩ := hEd S hS;have hne : S.Nonempty := ⟨c, hcS⟩;have hl_def : leftOff S = (c - S.min' hne) / d := dif_pos hne;have hr_def : rightOff S = (S.max' hne - c) / d := dif_pos hne;have hmin_mem := min'_mem S hne;have hmax_mem := max'_mem S hne;have hmin_le : S.min' hne <= c := min'_le S c hcS;have hc_le_max : c <= S.max' hne := le_max' S c hcS;have hdl : d ∣ c - S.min' hne := (Nat.modEq_iff_dvd' hmin_le).mp (hmod _ hmin_mem);have hdr : d ∣ S.max' hne - c := (Nat.modEq_iff_dvd' hc_le_max).mp (hmod _ hmax_mem).symm
   have hl_mul : leftOff S * d = c - S.min' hne := hl_def ▸ Nat.div_mul_cancel hdl;have hr_mul : rightOff S * d = S.max' hne - c := hr_def ▸ Nat.div_mul_cancel hdr;have hmax_leN : S.max' hne <= N := (mem_Icc.mp (hSsub hmax_mem)).2
   refine ⟨⟨hne, by omega, by omega⟩, by omega, by omega, fun x => ?_⟩
   constructor
   . intro hx; exact ⟨by have := min'_le S x hx; omega, by have := le_max' S x hx; omega, hmod x hx⟩
   . rintro ⟨hx1, hx2, hxm⟩; exact hfill _ hmin_mem _ hmax_mem x (by omega) (by omega) hxm
 obtain ⟨SL, hSL_mem, hSL_max⟩ := exists_max_image Ed leftOff hEd_ne;obtain ⟨SR, hSR_mem, hSR_max⟩ := exists_max_image Ed rightOff hEd_ne
 let Ld := leftOff SL
 let Rd := rightOff SR
 have hLd_lt : ∀ i, 1 <= i -> i <= Ld -> i * d < c := by
   intro i hi1 hiL;obtain ⟨⟨hneL, hminL, -⟩, -, -, -⟩ := hoff_eq SL hSL_mem;have hmin1 : 1 <= SL.min' hneL := (mem_Icc.mp ((hEd SL hSL_mem).1 (min'_mem SL hneL))).1;have hmul : i * d <= Ld * d := Nat.mul_le_mul_right d hiL;change i * d <= leftOff SL * d at hmul;omega
 have hRd_le : c + Rd * d <= N := (hoff_eq SR hSR_mem).2.2.1
 let Td := (Icc 1 Ld ×ˢ Icc 1 Rd).filter (fun p =>
   ∃ S ∈ Ed, c - p.1 * d ∈ S /\ c + p.2 * d ∈ S)
 have hTd_down : ∀ i j i' j', (i, j) ∈ Td -> 1 <= i' -> i' <= i -> 1 <= j' -> j' <= j -> (i', j') ∈ Td := by
   intro i j i' j' hij hi1 hi2 hj1 hj2;obtain ⟨hijP, S, hSE, hiS, hjS⟩ := mem_filter.mp hij;obtain ⟨hiI, hjI⟩ := mem_product.mp hijP;have hspec := (hoff_eq S hSE).2.2.2;have hid : i * d < c := hLd_lt i (mem_Icc.mp hiI).1 (mem_Icc.mp hiI).2;have hi'd : i' * d <= i * d := Nat.mul_le_mul_right d hi2;have hj'd : j' * d <= j * d := Nat.mul_le_mul_right d hj2;have hi_mem := (hspec (c - i * d)).mp hiS;have hj_mem := (hspec (c + j * d)).mp hjS
   refine mem_filter.mpr ⟨mem_product.mpr ⟨mem_Icc.mpr ⟨hi1, le_trans hi2 (mem_Icc.mp hiI).2⟩, mem_Icc.mpr ⟨hj1, le_trans hj2 (mem_Icc.mp hjI).2⟩⟩, S, hSE, ?_, ?_⟩
   . refine (hspec (c - i' * d)).mpr ⟨by omega, by omega, ?_⟩
     have h1 : c - i' * d + i' * d = c := Nat.sub_add_cancel (by omega)
     conv_rhs => rw [<- h1]
     rw [Nat.add_mul_mod_self_right]
   . exact (hspec (c + j' * d)).mpr ⟨by omega, by omega, by rw [Nat.add_mul_mod_self_right]⟩
 have hEd_le : Ed.card <= Td.card + Ld + Rd := by
   let Eboth := Ed.filter (fun S => 1 <= leftOff S /\ 1 <= rightOff S)
   let Eleft := Ed.filter (fun S => rightOff S = 0)
   let Eright := Ed.filter (fun S => leftOff S = 0)
   have hcov : Ed ⊆ Eboth ∪ (Eleft ∪ Eright) := by
     intro S hS
     by_cases hl0 : leftOff S = 0
     . exact mem_union_right _ (mem_union_right _ (mem_filter.mpr ⟨hS, hl0⟩))
     by_cases hr0 : rightOff S = 0
     . exact mem_union_right _ (mem_union_left _ (mem_filter.mpr ⟨hS, hr0⟩))
     . exact mem_union_left _ (mem_filter.mpr ⟨hS, by omega, by omega⟩)
   have huniq : ∀ S ∈ Ed, ∀ T ∈ Ed, leftOff S = leftOff T -> rightOff S = rightOff T -> S = T := by
     intro S hS T hT hl hr; ext x;rw [(hoff_eq S hS).2.2.2 x, (hoff_eq T hT).2.2.2 x, hl, hr]
   have hboth : Eboth.card <= Td.card := by
     refine card_le_card_of_injOn (fun S => (leftOff S, rightOff S)) ?_ ?_
     . intro S hS
       obtain ⟨hSE, hl1, hr1⟩ := mem_filter.mp (mem_coe.mp hS);obtain ⟨⟨hne, hmin, hmax⟩, -, -, -⟩ := hoff_eq S hSE
       refine mem_coe.mpr (mem_filter.mpr ⟨mem_product.mpr ⟨mem_Icc.mpr ⟨hl1, hSL_max S hSE⟩, mem_Icc.mpr ⟨hr1, hSR_max S hSE⟩⟩, S, hSE, hmin ▸ min'_mem S hne, hmax ▸ max'_mem S hne⟩)
     . intro S hS T hT heq
       exact huniq S (mem_filter.mp (mem_coe.mp hS)).1
         T (mem_filter.mp (mem_coe.mp hT)).1 (congrArg Prod.fst heq) (congrArg Prod.snd heq)
   have hleft : Eleft.card <= Ld := by
     have h1 : Eleft.card <= (Icc 1 Ld).card := by
       refine card_le_card_of_injOn leftOff ?_ ?_
       . intro S hS
         obtain ⟨hSE, hr0⟩ := mem_filter.mp (mem_coe.mp hS)
         have hl1 : 1 <= leftOff S := by
           by_contra h0; have hl0 : leftOff S = 0 := by omega
           have hS1 : S ⊆ {c} := fun x hx => by
             have := ((hoff_eq S hSE).2.2.2 x).mp hx; rw [hl0, hr0] at this; simp at this;exact mem_singleton.mpr (by omega)
           have := card_le_card hS1; have := (hEd S hSE).2.1; simp at *; omega
         exact mem_coe.mpr (mem_Icc.mpr ⟨hl1, hSL_max S hSE⟩)
       . intro S hS T hT heq
         exact huniq S (mem_filter.mp (mem_coe.mp hS)).1
           T (mem_filter.mp (mem_coe.mp hT)).1 heq
           ((mem_filter.mp (mem_coe.mp hS)).2.trans (mem_filter.mp (mem_coe.mp hT)).2.symm)
     rwa [Nat.card_Icc, Nat.add_sub_cancel] at h1
   have hright : Eright.card <= Rd := by
     have h1 : Eright.card <= (Icc 1 Rd).card := by
       refine card_le_card_of_injOn rightOff ?_ ?_
       . intro S hS
         obtain ⟨hSE, hl0⟩ := mem_filter.mp (mem_coe.mp hS)
         have hr1 : 1 <= rightOff S := by
           by_contra h0; have hr0 : rightOff S = 0 := by omega
           have hS1 : S ⊆ {c} := fun x hx => by
             have := ((hoff_eq S hSE).2.2.2 x).mp hx; rw [hl0, hr0] at this; simp at this;exact mem_singleton.mpr (by omega)
           have := card_le_card hS1; have := (hEd S hSE).2.1; simp at *; omega
         exact mem_coe.mpr (mem_Icc.mpr ⟨hr1, hSR_max S hSE⟩)
       . intro S hS T hT heq
         exact huniq S (mem_filter.mp (mem_coe.mp hS)).1
           T (mem_filter.mp (mem_coe.mp hT)).1
           ((mem_filter.mp (mem_coe.mp hS)).2.trans (mem_filter.mp (mem_coe.mp hT)).2.symm) heq
     rwa [Nat.card_Icc, Nat.add_sub_cancel] at h1
   have hc1 := le_trans (card_le_card hcov) (le_trans (card_union_le _ _) (Nat.add_le_add_left (card_union_le _ _) _));omega
 let FLR := (Td.filter (fun p => Nat.Coprime p.1 p.2)).image (fun p => ({c - p.1 * d, c + p.2 * d} : Finset ℕ))
 let FLL := ((Icc 1 Ld ×ˢ Icc 1 Ld).filter (fun p => p.1 < p.2 /\ Nat.Coprime p.1 p.2)).image (fun p => ({c - p.1 * d, c - p.2 * d} : Finset ℕ))
 let FRR := ((Icc 1 Rd ×ˢ Icc 1 Rd).filter (fun p => p.1 < p.2 /\ Nat.Coprime p.1 p.2)).image (fun p => ({c + p.1 * d, c + p.2 * d} : Finset ℕ))
 let Fd := FLR ∪ (FLL ∪ FRR)
 have hFLR_card : (52 / 100 : ℝ) * (Td.card : ℝ) <= (FLR.card : ℝ) := by
   have hinj : Set.InjOn (fun p : ℕ × ℕ => ({c - p.1 * d, c + p.2 * d} : Finset ℕ)) ((Td.filter (fun p => Nat.Coprime p.1 p.2) : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
     intro p hp q hq heq; dsimp only at heq;have hpI := mem_product.mp (mem_filter.mp (mem_filter.mp (mem_coe.mp hp)).1).1;have hqI := mem_product.mp (mem_filter.mp (mem_filter.mp (mem_coe.mp hq)).1).1;have hp1d : p.1 * d < c := hLd_lt p.1 (mem_Icc.mp hpI.1).1 (mem_Icc.mp hpI.1).2;have hq1d : q.1 * d < c := hLd_lt q.1 (mem_Icc.mp hqI.1).1 (mem_Icc.mp hqI.1).2;have hp1pos : 1 <= p.1 * d := Nat.mul_pos (mem_Icc.mp hpI.1).1 hd1;have hp2pos : 1 <= p.2 * d := Nat.mul_pos (mem_Icc.mp hpI.2).1 hd1;have hq1pos : 1 <= q.1 * d := Nat.mul_pos (mem_Icc.mp hqI.1).1 hd1
     have hq2pos : 1 <= q.2 * d := Nat.mul_pos (mem_Icc.mp hqI.2).1 hd1;have h1m : c - p.1 * d ∈ ({c - q.1 * d, c + q.2 * d} : Finset ℕ) := by rw [<- heq]; simp
     have h2m : c + p.2 * d ∈ ({c - q.1 * d, c + q.2 * d} : Finset ℕ) := by rw [<- heq]; simp
     simp only [mem_insert, mem_singleton] at h1m h2m;exact Prod.ext (Nat.eq_of_mul_eq_mul_right (by omega : 0 < d) (by omega)) (Nat.eq_of_mul_eq_mul_right (by omega : 0 < d) (by omega))
   rw [card_image_of_injOn hinj];exact downward_closed_coprime_rect (filter_subset _ _) hTd_down
 have hFLL_card : (52 / 100 : ℝ) * ((Ld * (Ld - 1) / 2 : ℕ) : ℝ) <= (FLL.card : ℝ) := by
   have hinj : Set.InjOn (fun p : ℕ × ℕ => ({c - p.1 * d, c - p.2 * d} : Finset ℕ)) (((Icc 1 Ld ×ˢ Icc 1 Ld).filter (fun p => p.1 < p.2 /\ Nat.Coprime p.1 p.2) : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
     intro p hp q hq heq; dsimp only at heq;obtain ⟨hpP, hplt, -⟩ := mem_filter.mp (mem_coe.mp hp);obtain ⟨hqP, hqlt, -⟩ := mem_filter.mp (mem_coe.mp hq);have hp2d : p.2 * d < c := hLd_lt p.2 (mem_Icc.mp (mem_product.mp hpP).2).1 (mem_Icc.mp (mem_product.mp hpP).2).2;have hq2d : q.2 * d < c := hLd_lt q.2 (mem_Icc.mp (mem_product.mp hqP).2).1 (mem_Icc.mp (mem_product.mp hqP).2).2;have hp12 : p.1 * d < p.2 * d := Nat.mul_lt_mul_of_pos_right hplt (by omega);have hq12 : q.1 * d < q.2 * d := Nat.mul_lt_mul_of_pos_right hqlt (by omega)
     have h1m : c - p.1 * d ∈ ({c - q.1 * d, c - q.2 * d} : Finset ℕ) := by rw [<- heq]; simp
     have h2m : c - p.2 * d ∈ ({c - q.1 * d, c - q.2 * d} : Finset ℕ) := by rw [<- heq]; simp
     have h3m : c - q.1 * d ∈ ({c - p.1 * d, c - p.2 * d} : Finset ℕ) := by rw [heq]; simp
     simp only [mem_insert, mem_singleton] at h1m h2m h3m;exact Prod.ext (Nat.eq_of_mul_eq_mul_right (by omega : 0 < d) (by omega)) (Nat.eq_of_mul_eq_mul_right (by omega : 0 < d) (by omega))
   rw [card_image_of_injOn hinj];exact coprime_pairs_triangle_ge Ld
 have hFRR_card : (52 / 100 : ℝ) * ((Rd * (Rd - 1) / 2 : ℕ) : ℝ) <= (FRR.card : ℝ) := by
   have hinj : Set.InjOn (fun p : ℕ × ℕ => ({c + p.1 * d, c + p.2 * d} : Finset ℕ)) (((Icc 1 Rd ×ˢ Icc 1 Rd).filter (fun p => p.1 < p.2 /\ Nat.Coprime p.1 p.2) : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
     intro p hp q hq heq; dsimp only at heq;obtain ⟨-, hplt, -⟩ := mem_filter.mp (mem_coe.mp hp);obtain ⟨-, hqlt, -⟩ := mem_filter.mp (mem_coe.mp hq);have hp12 : p.1 * d < p.2 * d := Nat.mul_lt_mul_of_pos_right hplt (by omega);have hq12 : q.1 * d < q.2 * d := Nat.mul_lt_mul_of_pos_right hqlt (by omega);have h1m : c + p.1 * d ∈ ({c + q.1 * d, c + q.2 * d} : Finset ℕ) := by rw [<- heq]; simp
     have h2m : c + p.2 * d ∈ ({c + q.1 * d, c + q.2 * d} : Finset ℕ) := by rw [<- heq]; simp
     have h3m : c + q.1 * d ∈ ({c + p.1 * d, c + p.2 * d} : Finset ℕ) := by rw [heq]; simp
     simp only [mem_insert, mem_singleton] at h1m h2m h3m;exact Prod.ext (Nat.eq_of_mul_eq_mul_right (by omega : 0 < d) (by omega)) (Nat.eq_of_mul_eq_mul_right (by omega : 0 < d) (by omega))
   rw [card_image_of_injOn hinj];exact coprime_pairs_triangle_ge Rd
 have hdisj_LR_LL : Disjoint FLR FLL := by
   rw [Finset.disjoint_left]; intro e h1 h2;obtain ⟨p, hp, rfl⟩ := mem_image.mp h1;obtain ⟨q, hq, heq⟩ := mem_image.mp h2;have hp2pos : 1 <= p.2 * d := Nat.mul_pos (mem_Icc.mp (mem_product.mp (mem_filter.mp (mem_filter.mp hp).1).1).2).1 hd1;have hmem : c + p.2 * d ∈ ({c - q.1 * d, c - q.2 * d} : Finset ℕ) := by rw [heq]; simp
   simp only [mem_insert, mem_singleton] at hmem
   rcases hmem with h | h <;> omega
 have hdisj_LR_RR : Disjoint FLR FRR := by
   rw [Finset.disjoint_left]; intro e h1 h2;obtain ⟨p, hp, rfl⟩ := mem_image.mp h1;obtain ⟨q, hq, heq⟩ := mem_image.mp h2;have hp1I := mem_Icc.mp (mem_product.mp (mem_filter.mp (mem_filter.mp hp).1).1).1;have hp1pos : 1 <= p.1 * d := Nat.mul_pos hp1I.1 hd1;have hp1d : p.1 * d < c := hLd_lt p.1 hp1I.1 hp1I.2;have hmem : c - p.1 * d ∈ ({c + q.1 * d, c + q.2 * d} : Finset ℕ) := by rw [heq]; simp
   simp only [mem_insert, mem_singleton] at hmem
   rcases hmem with h | h <;> omega
 have hdisj_LL_RR : Disjoint FLL FRR := by
   rw [Finset.disjoint_left]; intro e h1 h2;obtain ⟨p, hp, rfl⟩ := mem_image.mp h1;obtain ⟨q, hq, heq⟩ := mem_image.mp h2;have hp1I := mem_Icc.mp (mem_product.mp (mem_filter.mp hp).1).1;have hp1pos : 1 <= p.1 * d := Nat.mul_pos hp1I.1 hd1;have hp1d : p.1 * d < c := hLd_lt p.1 hp1I.1 hp1I.2;have hmem : c - p.1 * d ∈ ({c + q.1 * d, c + q.2 * d} : Finset ℕ) := by rw [heq]; simp
   simp only [mem_insert, mem_singleton] at hmem
   rcases hmem with h | h <;> omega
 have hFd_card : Fd.card = FLR.card + FLL.card + FRR.card := by
   dsimp only [Fd];rw [card_union_of_disjoint (Finset.disjoint_union_right.mpr ⟨hdisj_LR_LL, hdisj_LR_RR⟩), card_union_of_disjoint hdisj_LL_RR]; omega
 have hgcd_pair : ∀ (a b : ℕ), a ≠ b -> Nat.gcd (distNat c a) (distNat c b) = d -> ∀ x ∈ ({a, b} : Finset ℕ), ∀ y ∈ ({a, b} : Finset ℕ), x ≠ y -> Nat.gcd (distNat c x) (distNat c y) = d := by
   intro a b hab hg x hx y hy hxy;simp only [mem_insert, mem_singleton] at hx hy
   rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
   . exact absurd rfl hxy
   . exact hg
   . rw [Nat.gcd_comm]; exact hg
   . exact absurd rfl hxy
 have hsub_each : ∀ e ∈ Fd, e ∈ ((Icc 1 N).erase c).powersetCard 2 /\ (∀ x ∈ e, ∀ y ∈ e, x ≠ y -> Nat.gcd (distNat c x) (distNat c y) = d) /\ (∃ E0 ∈ Ed, e ⊆ E0) := by
   intro e he
   rcases mem_union.mp he with h1 | h23
   . obtain ⟨p, hp, rfl⟩ := mem_image.mp h1
     obtain ⟨hpT, hcop⟩ := mem_filter.mp hp;obtain ⟨hpP, S, hSE, hiS, hjS⟩ := mem_filter.mp hpT;have hp1I := mem_Icc.mp (mem_product.mp hpP).1;have hp2I := mem_Icc.mp (mem_product.mp hpP).2;have hp1d : p.1 * d < c := hLd_lt p.1 hp1I.1 hp1I.2;have hp1pos : 1 <= p.1 * d := Nat.mul_pos hp1I.1 hd1;have hp2pos : 1 <= p.2 * d := Nat.mul_pos hp2I.1 hd1;have hne : c - p.1 * d ≠ c + p.2 * d := by omega
     have hgd : Nat.gcd (distNat c (c - p.1 * d)) (distNat c (c + p.2 * d)) = d := by
       rw [distNat_eq_sub' (by omega), distNat_eq_sub (by omega)];have h1 : c - (c - p.1 * d) = p.1 * d := by omega
       rw [h1, Nat.add_sub_cancel_left, Nat.gcd_mul_right, hcop.gcd_eq_one, one_mul]
     refine ⟨mem_powersetCard.mpr ⟨fun z hz => ?_, card_pair hne⟩, hgcd_pair _ _ hne hgd, ⟨S, hSE, fun z hz => by
         simp only [mem_insert, mem_singleton] at hz
         rcases hz with rfl | rfl <;> assumption⟩⟩
     simp only [mem_insert, mem_singleton] at hz
     rcases hz with rfl | rfl
     . exact Finset.mem_erase.mpr ⟨by omega, (hEd S hSE).1 hiS⟩
     . exact Finset.mem_erase.mpr ⟨by omega, (hEd S hSE).1 hjS⟩
   . rcases mem_union.mp h23 with h2 | h3
     . obtain ⟨p, hp, rfl⟩ := mem_image.mp h2
       obtain ⟨hpP, hplt, hcop⟩ := mem_filter.mp hp;have hp1I := mem_Icc.mp (mem_product.mp hpP).1;have hp2I := mem_Icc.mp (mem_product.mp hpP).2;have hp2d : p.2 * d < c := hLd_lt p.2 hp2I.1 hp2I.2;have hp1pos : 1 <= p.1 * d := Nat.mul_pos hp1I.1 hd1;have hp2pos : 1 <= p.2 * d := Nat.mul_pos hp2I.1 hd1;have hp12 : p.1 * d < p.2 * d := Nat.mul_lt_mul_of_pos_right hplt (by omega);have hne : c - p.1 * d ≠ c - p.2 * d := by omega
       have hSL_spec := (hoff_eq SL hSL_mem).2.2.2
       have hiSL : c - p.1 * d ∈ SL := (hSL_spec _).mpr ⟨by
         have : p.1 * d <= leftOff SL * d := Nat.mul_le_mul_right d hp1I.2; omega, by omega, by
         have h1 : c - p.1 * d + p.1 * d = c := Nat.sub_add_cancel (by omega)
         conv_rhs => rw [<- h1]; rw [Nat.add_mul_mod_self_right]⟩
       have hjSL : c - p.2 * d ∈ SL := (hSL_spec _).mpr ⟨by
         have : p.2 * d <= leftOff SL * d := Nat.mul_le_mul_right d hp2I.2; omega, by omega, by
         have h1 : c - p.2 * d + p.2 * d = c := Nat.sub_add_cancel (by omega)
         conv_rhs => rw [<- h1]; rw [Nat.add_mul_mod_self_right]⟩
       have hgd : Nat.gcd (distNat c (c - p.1 * d)) (distNat c (c - p.2 * d)) = d := by
         rw [distNat_eq_sub' (by omega), distNat_eq_sub' (by omega)];have h1 : c - (c - p.1 * d) = p.1 * d := by omega
         have h2 : c - (c - p.2 * d) = p.2 * d := by omega
         rw [h1, h2, Nat.gcd_mul_right, hcop.gcd_eq_one, one_mul]
       refine ⟨mem_powersetCard.mpr ⟨fun z hz => ?_, card_pair hne⟩, hgcd_pair _ _ hne hgd, ⟨SL, hSL_mem, fun z hz => by
           simp only [mem_insert, mem_singleton] at hz
           rcases hz with rfl | rfl <;> assumption⟩⟩
       simp only [mem_insert, mem_singleton] at hz
       rcases hz with rfl | rfl
       . exact Finset.mem_erase.mpr ⟨by omega, (hEd SL hSL_mem).1 hiSL⟩
       . exact Finset.mem_erase.mpr ⟨by omega, (hEd SL hSL_mem).1 hjSL⟩
     . obtain ⟨p, hp, rfl⟩ := mem_image.mp h3
       obtain ⟨hpP, hplt, hcop⟩ := mem_filter.mp hp;have hp1I := mem_Icc.mp (mem_product.mp hpP).1;have hp2I := mem_Icc.mp (mem_product.mp hpP).2;have hp1pos : 1 <= p.1 * d := Nat.mul_pos hp1I.1 hd1;have hp2pos : 1 <= p.2 * d := Nat.mul_pos hp2I.1 hd1;have hp12 : p.1 * d < p.2 * d := Nat.mul_lt_mul_of_pos_right hplt (by omega);have hne : c + p.1 * d ≠ c + p.2 * d := by omega
       have hSR_spec := (hoff_eq SR hSR_mem).2.2.2
       have hiSR : c + p.1 * d ∈ SR := (hSR_spec _).mpr ⟨by omega, by
         have : p.1 * d <= rightOff SR * d := Nat.mul_le_mul_right d hp1I.2; omega,
         by rw [Nat.add_mul_mod_self_right]⟩
       have hjSR : c + p.2 * d ∈ SR := (hSR_spec _).mpr ⟨by omega, by
         have : p.2 * d <= rightOff SR * d := Nat.mul_le_mul_right d hp2I.2; omega,
         by rw [Nat.add_mul_mod_self_right]⟩
       have hgd : Nat.gcd (distNat c (c + p.1 * d)) (distNat c (c + p.2 * d)) = d := by rw [distNat_eq_sub (by omega), distNat_eq_sub (by omega), Nat.add_sub_cancel_left, Nat.add_sub_cancel_left, Nat.gcd_mul_right, hcop.gcd_eq_one, one_mul]
       refine ⟨mem_powersetCard.mpr ⟨fun z hz => ?_, card_pair hne⟩, hgcd_pair _ _ hne hgd, ⟨SR, hSR_mem, fun z hz => by
           simp only [mem_insert, mem_singleton] at hz
           rcases hz with rfl | rfl <;> assumption⟩⟩
       simp only [mem_insert, mem_singleton] at hz
       rcases hz with rfl | rfl
       . exact Finset.mem_erase.mpr ⟨by omega, (hEd SR hSR_mem).1 hiSR⟩
       . exact Finset.mem_erase.mpr ⟨by omega, (hEd SR hSR_mem).1 hjSR⟩
 have htri_cast : ∀ n : ℕ, ((n * (n - 1) / 2 : ℕ) : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
   intro n; rcases n with _ | k
   . simp
   . have hdiv : 2 ∣ (k + 1) * k := by
       rcases Nat.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
       . exact ⟨(k + 1) * m, by rw [hm]; ring⟩
       . exact ⟨(m + 1) * k, by rw [hm]; ring⟩
     have h1 : (((k + 1) * k / 2 : ℕ) : ℝ) * 2 = (((k + 1) * k : ℕ) : ℝ) := by exact_mod_cast Nat.div_mul_cancel hdiv
     simp only [Nat.add_sub_cancel] at h1 ⊢; push_cast at h1 ⊢; linarith
 have hTd_le_LR : (Td.card : ℝ) <= (Ld : ℝ) * (Rd : ℝ) := by
   have h1 : Td.card <= (Icc 1 Ld ×ˢ Icc 1 Rd).card := card_le_card (filter_subset _ _);rw [card_product, Nat.card_Icc, Nat.card_Icc, Nat.add_sub_cancel, Nat.add_sub_cancel] at h1;exact_mod_cast h1
 have hFd_lb : (52 / 100 : ℝ) * ((Td.card : ℝ) + ((Ld : ℝ) ^ 2 / 2 - (Ld : ℝ) / 2) + ((Rd : ℝ) ^ 2 / 2 - (Rd : ℝ) / 2)) <= (Fd.card : ℝ) := by
   have hFdR : (Fd.card : ℝ) = (FLR.card : ℝ) + (FLL.card : ℝ) + (FRR.card : ℝ) := by exact_mod_cast hFd_card
   have hexp : ∀ x : ℝ, x * (x - 1) / 2 = x ^ 2 / 2 - x / 2 := fun x => by ring
   rw [htri_cast Ld, hexp] at hFLL_card; rw [htri_cast Rd, hexp] at hFRR_card; linarith
 have hEd_R : (Ed.card : ℝ) <= (Td.card : ℝ) + (Ld : ℝ) + (Rd : ℝ) := by exact_mod_cast hEd_le
 have hLR_amgm : (Td.card : ℝ) <= ((Ld : ℝ) ^ 2 + (Rd : ℝ) ^ 2) / 2 := by
   have hsq : 0 <= ((Ld : ℝ) - (Rd : ℝ)) ^ 2 := sq_nonneg _;linarith [hTd_le_LR, show ((Ld : ℝ) - (Rd : ℝ)) ^ 2 = (Ld : ℝ) ^ 2 - 2 * ((Ld : ℝ) * (Rd : ℝ)) + (Rd : ℝ) ^ 2 by ring]
 refine ⟨Fd, fun e he => (hsub_each e he).1, fun e he => (hsub_each e he).2.1, fun e he => (hsub_each e he).2.2, ?_, ?_, ?_⟩
 . have h1 : 0 <= ((Ld : ℝ) - 43) ^ 2 := sq_nonneg _
   have h2 : 0 <= ((Rd : ℝ) - 43) ^ 2 := sq_nonneg _;linarith [hFd_lb, hEd_R, hLR_amgm, show ((Ld : ℝ) - 43) ^ 2 = (Ld : ℝ) ^ 2 - 86 * (Ld : ℝ) + 1849 by ring, show ((Rd : ℝ) - 43) ^ 2 = (Rd : ℝ) ^ 2 - 86 * (Rd : ℝ) + 1849 by ring]
 . have h1 : 0 <= ((Ld : ℝ) - 63 / 2) ^ 2 := sq_nonneg _
   have h2 : 0 <= ((Rd : ℝ) - 63 / 2) ^ 2 := sq_nonneg _;linarith [hFd_lb, hEd_R, hLR_amgm, show ((Ld : ℝ) - 63 / 2) ^ 2 = (Ld : ℝ) ^ 2 - 63 * (Ld : ℝ) + 3969 / 4 by ring, show ((Rd : ℝ) - 63 / 2) ^ 2 = (Rd : ℝ) ^ 2 - 63 * (Rd : ℝ) + 3969 / 4 by ring]
 . intro X0 hN400 hc40 hX0
   have hX0_sub : Fd ∩ X0 ⊆ ((Icc 1 (Rd / 38)) ×ˢ (Icc (Rd - Rd / 38) Rd)).image (fun p => ({c + p.1 * d, c + p.2 * d} : Finset ℕ)) := by
     intro e he;obtain ⟨heF, heX⟩ := mem_inter.mp he;obtain ⟨x, y, he_eq, hcx, hx40, hy39, hyN⟩ := hX0 e heX;have hxy : x < y := by omega
     have heRR : e ∈ FRR := by
       rcases mem_union.mp heF with h1 | h23
       . exfalso; obtain ⟨p, hp, hpeq⟩ := mem_image.mp h1
         have hmem : c - p.1 * d ∈ ({x, y} : Finset ℕ) := by rw [<- he_eq, <- hpeq]; simp
         simp only [mem_insert, mem_singleton] at hmem; rcases hmem with h | h <;> omega
       . rcases mem_union.mp h23 with h2 | h3
         . exfalso; obtain ⟨p, hp, hpeq⟩ := mem_image.mp h2
           have hmem : c - p.1 * d ∈ ({x, y} : Finset ℕ) := by rw [<- he_eq, <- hpeq]; simp
           simp only [mem_insert, mem_singleton] at hmem; rcases hmem with h | h <;> omega
         . exact h3
     obtain ⟨p, hp, hpeq⟩ := mem_image.mp heRR;obtain ⟨hpP, hplt, -⟩ := mem_filter.mp hp;have hp1 := mem_Icc.mp (mem_product.mp hpP).1;have hp2 := mem_Icc.mp (mem_product.mp hpP).2;have hp12 : p.1 * d < p.2 * d := Nat.mul_lt_mul_of_pos_right hplt (by omega);have h1m : c + p.1 * d ∈ ({x, y} : Finset ℕ) := by rw [<- he_eq, <- hpeq]; simp
     have h2m : c + p.2 * d ∈ ({x, y} : Finset ℕ) := by rw [<- he_eq, <- hpeq]; simp
     have h3m : x ∈ ({c + p.1 * d, c + p.2 * d} : Finset ℕ) := by rw [hpeq, he_eq]; simp
     simp only [mem_insert, mem_singleton] at h1m h2m h3m;have hx_eq : x = c + p.1 * d := by omega
     have hy_eq : y = c + p.2 * d := by omega
     have hRd_lb : 38 * N <= 40 * (Rd * d) := by have : p.2 * d <= Rd * d := Nat.mul_le_mul_right d hp2.2; omega
     have hi_le : p.1 <= Rd / 38 := by
       have h1 : 38 * (p.1 * d) <= Rd * d := by omega
       have h2 : (38 * p.1) * d <= Rd * d := by rw [mul_assoc]; exact h1
       have h3 : 38 * p.1 <= Rd := Nat.le_of_mul_le_mul_right h2 (by omega);exact (Nat.le_div_iff_mul_le (by norm_num)).mpr (by omega)
     have hj_ge : Rd - Rd / 38 <= p.2 := by
       have hsub : (Rd - p.2) * d = Rd * d - p.2 * d := Nat.sub_mul Rd p.2 d;have h1 : 40 * ((Rd - p.2) * d) <= N := by have : p.2 * d <= Rd * d := Nat.mul_le_mul_right d hp2.2; omega
       have h2 : (38 * (Rd - p.2)) * d <= Rd * d := by rw [mul_assoc]; omega
       have h3 : 38 * (Rd - p.2) <= Rd := Nat.le_of_mul_le_mul_right h2 (by omega);have h4 : Rd - p.2 <= Rd / 38 := (Nat.le_div_iff_mul_le (by norm_num)).mpr (by omega);omega
     exact mem_image.mpr ⟨p, mem_product.mpr ⟨mem_Icc.mpr ⟨hp1.1, hi_le⟩, mem_Icc.mpr ⟨hj_ge, hp2.2⟩⟩, hpeq⟩
   have hX0_card : ((Fd ∩ X0).card : ℝ) <= (Rd : ℝ) ^ 2 / 1444 + (Rd : ℝ) / 38 := by
     have h1 := le_trans (card_le_card hX0_sub) card_image_le;rw [card_product, Nat.card_Icc, Nat.card_Icc, Nat.add_sub_cancel] at h1;have h2 : Rd + 1 - (Rd - Rd / 38) <= Rd / 38 + 1 := by omega
     have h3 : (Fd ∩ X0).card <= (Rd / 38) * (Rd / 38 + 1) := le_trans h1 (Nat.mul_le_mul_left _ h2);have h3R : ((Fd ∩ X0).card : ℝ) <= ((Rd / 38 : ℕ) : ℝ) * (((Rd / 38 : ℕ) : ℝ) + 1) := by exact_mod_cast h3
     have hdiv : ((Rd / 38 : ℕ) : ℝ) <= (Rd : ℝ) / 38 := by rw [le_div_iff₀ (by norm_num)]; exact_mod_cast Nat.div_mul_le_self Rd 38
     have hnn : (0 : ℝ) <= ((Rd / 38 : ℕ) : ℝ) := Nat.cast_nonneg _;have hmul : ((Rd / 38 : ℕ) : ℝ) * (((Rd / 38 : ℕ) : ℝ) + 1) <= ((Rd : ℝ) / 38) * ((Rd : ℝ) / 38 + 1) := mul_le_mul hdiv (by linarith) (by positivity) (by positivity);linarith [h3R, hmul, show ((Rd : ℝ) / 38) * ((Rd : ℝ) / 38 + 1) = (Rd : ℝ) ^ 2 / 1444 + (Rd : ℝ) / 38 by ring]
   have hsdiffR : ((Fd \ X0).card : ℝ) + ((Fd ∩ X0).card : ℝ) = (Fd.card : ℝ) := by exact_mod_cast card_sdiff_add_card_inter Fd X0
   have h1 : 0 <= ((Ld : ℝ) - 63 / 2) ^ 2 := sq_nonneg _;have h2 : 0 <= ((Rd : ℝ) - 3332 / 100) ^ 2 := sq_nonneg _;have hR0 : (0 : ℝ) <= (Rd : ℝ) := Nat.cast_nonneg Rd;linarith [hFd_lb, hEd_R, hLR_amgm, hX0_card, hsdiffR, hR0, show ((Ld : ℝ) - 63 / 2) ^ 2 = (Ld : ℝ) ^ 2 - 63 * (Ld : ℝ) + 3969 / 4 by ring, show ((Rd : ℝ) - 3332 / 100) ^ 2 = (Rd : ℝ) ^ 2 - 6664 / 100 * (Rd : ℝ) + (3332 / 100) ^ 2 by ring]
lemma ap_forb_surplus {N c : ℕ} (hN : 1 <= N) (hc : c ∈ Icc 1 N) {F E : Finset (Finset ℕ)} (hF : IsWellInter N F) (hE_sub : E ⊆ F) (hE : ∀ S ∈ E, 3 <= S.card /\ c ∈ S /\ APSet S) : ∃ Forb : Finset (Finset ℕ), Forb ⊆ ((Icc 1 N).erase c).powersetCard 2 /\ (∀ e ∈ Forb, ∃ E0 ∈ E, e ⊆ E0 /\ ∀ x ∈ e, ∀ y ∈ e, x ≠ y -> (∀ a ∈ E0, a % 2 = c % 2) \/ (x % 2 ≠ c % 2 \/ y % 2 ≠ c % 2)) /\ (E.card : ℝ) <= (99 / 100 : ℝ) * (Forb.card : ℝ) + 55 * (N : ℝ) /\ (E.card : ℝ) <= (Forb.card : ℝ) + 40 * (N : ℝ) /\ (∀ X0 : Finset (Finset ℕ), 400 <= N -> 40 * c <= N ->
       (∀ e ∈ X0, ∃ x y, e = {x, y} /\ c < x /\ 40 * x <= N /\ 39 * N <= 40 * y /\ y <= N) ->
       (E.card : ℝ) <= ((Forb \ X0).card : ℝ) + 42 * (N : ℝ)) := by
 classical
 have hstep_ex : ∀ S : {S // S ∈ E}, ∃ d, 1 <= d /\ d <= N /\ (∀ x ∈ S.1, x % d = c % d) /\ (∀ x ∈ S.1, ∀ y ∈ S.1, ∀ z, min x y <= z -> z <= max x y -> z % d = c % d -> z ∈ S.1) := by
   rintro ⟨S, hS⟩;obtain ⟨hS3, hcS, hAP⟩ := hE S hS;obtain ⟨d, hd1, -, -, hmem, -⟩ := apSet_canonical hAP (by omega);have hcm := (hmem c).mp hcS;have hne_er : (S.erase c).Nonempty := card_pos.mp (by rw [card_erase_of_mem hcS]; omega);obtain ⟨w, hw⟩ := hne_er;obtain ⟨hwc, hwS⟩ := Finset.mem_erase.mp hw;have hwm := (hmem w).mp hwS
   have hdvd : d ∣ distNat c w := by
     unfold distNat
     rcases le_total c w with hle | hle
     . rw [max_eq_right hle, min_eq_left hle]; exact (Nat.modEq_iff_dvd' hle).mp (hwm.2.2.trans hcm.2.2.symm).symm
     . rw [max_eq_left hle, min_eq_right hle]; exact (Nat.modEq_iff_dvd' hle).mp (hwm.2.2.trans hcm.2.2.symm)
   have hdN : d <= N := by
     have hle := Nat.le_of_dvd (distNat_pos_of_ne hwc.symm) hdvd;have hcI := mem_Icc.mp hc;have hwI := mem_Icc.mp (hF.1 S (hE_sub hS) hwS);unfold distNat at hle; omega
   refine ⟨d, hd1, hdN, fun x hx => ((hmem x).mp hx).2.2.trans hcm.2.2.symm, fun x hx y hy z hz1 hz2 hzm => ?_⟩
   have hxm := (hmem x).mp hx; have hym := (hmem y).mp hy;exact (hmem z).mpr ⟨by omega, by omega, hzm.trans hcm.2.2⟩
 choose step hstep using hstep_ex
 let Ed : ℕ -> Finset (Finset ℕ) := fun d => (E.attach.filter (fun S => step S = d)).image Subtype.val
 have hEd_card_att : ∀ d, (Ed d).card = (E.attach.filter (fun S => step S = d)).card := fun d =>
   card_image_of_injective _ Subtype.val_injective
 have hper_d : ∀ d ∈ Icc 1 N, ∃ Fd : Finset (Finset ℕ), Fd ⊆ ((Icc 1 N).erase c).powersetCard 2 /\ (∀ e ∈ Fd, ∀ x ∈ e, ∀ y ∈ e, x ≠ y -> Nat.gcd (distNat c x) (distNat c y) = d) /\ (∀ e ∈ Fd, ∃ E0 ∈ Ed d, e ⊆ E0) /\ ((Ed d).card : ℝ) <= (99 / 100 : ℝ) * (Fd.card : ℝ) + 55 /\ ((Ed d).card : ℝ) <= (Fd.card : ℝ) + 40 /\ (∀ X0 : Finset (Finset ℕ), 400 <= N -> 40 * c <= N -> (∀ e ∈ X0, ∃ x y, e = {x, y} /\ c < x /\ 40 * x <= N /\ 39 * N <= 40 * y /\ y <= N) -> ((Ed d).card : ℝ) <= ((Fd \ X0).card : ℝ) + 42) := by
   intro d hdI
   refine ap_forb_step hN hc (mem_Icc.mp hdI).1 (fun S hS => ?_)
   obtain ⟨S', hS'f, rfl⟩ := mem_image.mp hS;have hsd := (mem_filter.mp hS'f).2;have hsp := hstep S'; rw [hsd] at hsp;exact ⟨hF.1 S'.1 (hE_sub S'.2), (hE S'.1 S'.2).1, (hE S'.1 S'.2).2.1, hsp.2.2.1, hsp.2.2.2⟩
 choose Forbd hForbd using hper_d
 let Forb := (Icc 1 N).attach.biUnion (fun d => Forbd d.1 d.2)
 have hForb_disj : Set.PairwiseDisjoint ((Icc 1 N).attach : Set {d // d ∈ Icc 1 N}) (fun d => Forbd d.1 d.2) := by
   intro d1 _ d2 _ hne;change Disjoint (Forbd d1.1 d1.2) (Forbd d2.1 d2.2);rw [Finset.disjoint_left]; intro e h1 h2;have hcard2 := (mem_powersetCard.mp ((hForbd d1.1 d1.2).1 h1)).2;obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.mp hcard2;have hg1 := (hForbd d1.1 d1.2).2.1 {x, y} h1 x (by simp) y (by simp) hxy;have hg2 := (hForbd d2.1 d2.2).2.1 {x, y} h2 x (by simp) y (by simp) hxy;exact hne (Subtype.ext (hg1.symm.trans hg2))
 have hE_part : E.card = ∑ d ∈ (Icc 1 N).attach, (Ed d.1).card := by
   have hcov : E.attach = (Icc 1 N).attach.biUnion (fun d => E.attach.filter (fun S => step S = d.1)) := by
     ext S; simp only [mem_attach, true_iff, mem_biUnion, mem_filter, true_and]
     exact ⟨⟨step S, mem_Icc.mpr ⟨(hstep S).1, (hstep S).2.1⟩⟩, rfl⟩
   have hdisjE : Set.PairwiseDisjoint ((Icc 1 N).attach : Set {d // d ∈ Icc 1 N}) (fun d => E.attach.filter (fun S => step S = d.1)) := by
     intro d1 _ d2 _ hne;change Disjoint _ _;rw [Finset.disjoint_left]; intro S h1 h2;exact hne (Subtype.ext ((mem_filter.mp h1).2.symm.trans (mem_filter.mp h2).2))
   rw [<- card_attach, hcov, card_biUnion hdisjE];exact sum_congr rfl fun d _ => (hEd_card_att d.1).symm
 have hForb_card : Forb.card = ∑ d ∈ (Icc 1 N).attach, (Forbd d.1 d.2).card := card_biUnion hForb_disj;have hatt_card : (Icc 1 N).attach.card = N := by rw [card_attach, Nat.card_Icc, Nat.add_sub_cancel]
 refine ⟨Forb, ?_, ?_, ?_, ?_, ?_⟩
 . intro e he; obtain ⟨d, -, hed⟩ := mem_biUnion.mp he; exact (hForbd d.1 d.2).1 hed
 . intro e he
   obtain ⟨d, -, hed⟩ := mem_biUnion.mp he;obtain ⟨E0, hE0d, heE0⟩ := (hForbd d.1 d.2).2.2.1 e hed;obtain ⟨E0', hE0'f, rfl⟩ := mem_image.mp hE0d
   refine ⟨E0'.1, E0'.2, heE0, fun x hx y hy hxy => ?_⟩
   by_cases hpar : x % 2 = c % 2 /\ y % 2 = c % 2
   . left
     have hg_eq := (hForbd d.1 d.2).2.1 e hed x hx y hy hxy
     have h2x : 2 ∣ distNat c x := by
       unfold distNat
       rcases le_total c x with hle | hle
       . rw [max_eq_right hle, min_eq_left hle]; exact (Nat.modEq_iff_dvd' hle).mp hpar.1.symm
       . rw [max_eq_left hle, min_eq_right hle]; exact (Nat.modEq_iff_dvd' hle).mp hpar.1
     have h2y : 2 ∣ distNat c y := by
       unfold distNat
       rcases le_total c y with hle | hle
       . rw [max_eq_right hle, min_eq_left hle]; exact (Nat.modEq_iff_dvd' hle).mp hpar.2.symm
       . rw [max_eq_left hle, min_eq_right hle]; exact (Nat.modEq_iff_dvd' hle).mp hpar.2
     have h2d : 2 ∣ d.1 := hg_eq ▸ Nat.dvd_gcd h2x h2y;intro a ha;have ha_mod := (hstep E0').2.2.1 a ha;rw [(mem_filter.mp hE0'f).2] at ha_mod;obtain ⟨k, hk⟩ := h2d;rw [hk] at ha_mod;have h1 := congrArg (· % 2) ha_mod;rwa [Nat.mod_mul_right_mod, Nat.mod_mul_right_mod] at h1
   . right; push Not at hpar; by_cases hx2 : x % 2 = c % 2
     . right; exact hpar hx2
     . left; exact hx2
 . have hsum : (E.card : ℝ) <= ∑ d ∈ (Icc 1 N).attach, ((99 / 100 : ℝ) * ((Forbd d.1 d.2).card : ℝ) + 55) := by
     have hER : (E.card : ℝ) = ∑ d ∈ (Icc 1 N).attach, ((Ed d.1).card : ℝ) := by exact_mod_cast hE_part
     rw [hER]; exact sum_le_sum fun d _ => (hForbd d.1 d.2).2.2.2.1
   rw [sum_add_distrib, <- mul_sum, sum_const, nsmul_eq_mul, hatt_card] at hsum;have hFR : (Forb.card : ℝ) = ∑ d ∈ (Icc 1 N).attach, ((Forbd d.1 d.2).card : ℝ) := by exact_mod_cast hForb_card
   linarith
 . have hsum : (E.card : ℝ) <= ∑ d ∈ (Icc 1 N).attach, (((Forbd d.1 d.2).card : ℝ) + 40) := by
     have hER : (E.card : ℝ) = ∑ d ∈ (Icc 1 N).attach, ((Ed d.1).card : ℝ) := by exact_mod_cast hE_part
     rw [hER]; exact sum_le_sum fun d _ => (hForbd d.1 d.2).2.2.2.2.1
   rw [sum_add_distrib, sum_const, nsmul_eq_mul, hatt_card] at hsum;have hFR : (Forb.card : ℝ) = ∑ d ∈ (Icc 1 N).attach, ((Forbd d.1 d.2).card : ℝ) := by exact_mod_cast hForb_card
   linarith
 . intro X0 hN400 hc40 hX0
   have hsdiff_eq : Forb \ X0 = (Icc 1 N).attach.biUnion (fun d => Forbd d.1 d.2 \ X0) := by
     ext e; simp [Forb, Finset.mem_sdiff, mem_biUnion]
   have hdisj_sd : Set.PairwiseDisjoint ((Icc 1 N).attach : Set {d // d ∈ Icc 1 N}) (fun d => Forbd d.1 d.2 \ X0) := fun d1 h1 d2 h2 hne =>
     (hForb_disj h1 h2 hne).mono Finset.sdiff_subset Finset.sdiff_subset
   have hcard_sd : (Forb \ X0).card = ∑ d ∈ (Icc 1 N).attach, (Forbd d.1 d.2 \ X0).card := by rw [hsdiff_eq, card_biUnion hdisj_sd]
   have hsum : (E.card : ℝ) <= ∑ d ∈ (Icc 1 N).attach, (((Forbd d.1 d.2 \ X0).card : ℝ) + 42) := by
     have hER : (E.card : ℝ) = ∑ d ∈ (Icc 1 N).attach, ((Ed d.1).card : ℝ) := by exact_mod_cast hE_part
     rw [hER]; exact sum_le_sum fun d _ => (hForbd d.1 d.2).2.2.2.2.2 X0 hN400 hc40 hX0
   rw [sum_add_distrib, sum_const, nsmul_eq_mul, hatt_card] at hsum;have hFR : ((Forb \ X0).card : ℝ) = ∑ d ∈ (Icc 1 N).attach, ((Forbd d.1 d.2 \ X0).card : ℝ) := by exact_mod_cast hcard_sd
   linarith
lemma near_kernel_pair_avoidance {N c : ℕ} (hN : 400 <= N) (hc1 : 1 <= c) (hc40 : 40 * c <= N) {S : Finset ℕ} (hSsub : S ⊆ Icc 1 N) (hcS : c ∈ S) (hnotAP : ¬ APSet S) {X0 : Finset (Finset ℕ)} (hX0 : ∀ e ∈ X0, ∃ x y, e = {x, y} /\ c < x /\ 40 * x <= N /\ 39 * N <= 40 * y /\ y <= N /\ (S ∩ Icc (x + 1) (y - 1)).Nonempty) : ∃ x ∈ S, ∃ y ∈ S, x ≠ c /\ y ≠ c /\ x ≠ y /\ ({x, y} : Finset ℕ) ∉ X0 /\ ¬ (∀ w, min c (min x y) <= w -> w <= max c (max x y) -> w % Nat.gcd (distNat c x) (distNat c y) = c % Nat.gcd (distNat c x) (distNat c y) -> w ∈ S) := by
 by_contra hno;push Not at hno
 have hnot_in_X0 : ∀ x y, ¬ (c < min x y /\ 40 * min x y <= N /\ 39 * N <= 40 * max x y) -> ({x, y} : Finset ℕ) ∉ X0 := by
   intro x y hcond hmem;obtain ⟨a, b, heq, hca, ha40, hb39, -, -⟩ := hX0 _ hmem;have hab : a < b := by omega
   have h1 : a ∈ ({x, y} : Finset ℕ) := by rw [heq]; simp
   have h2 : b ∈ ({x, y} : Finset ℕ) := by rw [heq]; simp
   have h3 : x ∈ ({a, b} : Finset ℕ) := by rw [<- heq]; simp
   simp only [mem_insert, mem_singleton] at h1 h2 h3;apply hcond
   rcases le_total x y with hle | hle
   . rw [min_eq_left hle, max_eq_right hle]; omega
   . rw [min_eq_right hle, max_eq_left hle]; omega
 set Ahi := N / 40
 set Clo := (39 * N + 39) / 40
 have hAhi_spec : ∀ x, x <= Ahi ↔ 40 * x <= N := fun x =>
   ⟨fun h => le_trans (Nat.mul_le_mul_left 40 h) (Nat.mul_div_le N 40), fun h => (Nat.le_div_iff_mul_le (by norm_num)).mpr (by omega)⟩
 have hClo_spec : ∀ y, Clo <= y ↔ 39 * N <= 40 * y := fun y =>
   ⟨fun h => by have := Nat.lt_div_mul_add (a := 39 * N + 39) (b := 40) (by norm_num); omega, fun h => (Nat.div_le_iff_le_mul_add_pred (by norm_num)).mpr (by omega)⟩
 let SL := S.filter (fun w => w ≠ c /\ w <= Ahi)
 let SM := S.filter (fun w => Ahi < w /\ w < Clo)
 let SR := S.filter (fun w => Clo <= w)
 have hmid_hit : ∀ g, 1 <= g -> 40 * g <= N -> ∀ z, Clo <= z -> (∀ w, c <= w -> w <= z -> w % g = c % g -> w ∈ S) -> SM.Nonempty := by
   intro g hg1 hg40 z hz hfill
   set q := (Ahi - c) / g + 1
   set w := c + q * g
   have hw_gt : Ahi < w := by
     have h1 := Nat.lt_div_mul_add (a := Ahi - c) (b := g) (by omega);have h2 : q * g = ((Ahi - c) / g) * g + g := by dsimp only [q]; ring
     omega
   have hw_lt : w < Clo := by
     have h1 : ((Ahi - c) / g) * g <= Ahi - c := Nat.div_mul_le_self (Ahi - c) g;have h2 : q * g = ((Ahi - c) / g) * g + g := by dsimp only [q]; ring
     have hcA : c <= Ahi := (hAhi_spec c).mpr hc40;have hClo_ge : 39 * N <= 40 * Clo := (hClo_spec Clo).mp le_rfl;have hAhi_le : 40 * Ahi <= N := (hAhi_spec Ahi).mp le_rfl;omega
   have hwS : w ∈ S := hfill w (by omega) (by omega) (by dsimp only [w]; rw [Nat.add_mul_mod_self_right]);exact ⟨w, mem_filter.mpr ⟨hwS, hw_gt, hw_lt⟩⟩
 rcases SM.eq_empty_or_nonempty with hSM_empty | hSM_ne
 ·
   have hSR_card : SR.card <= 1 := by
     by_contra hgt;obtain ⟨z1, hz1, z2, hz2, hne⟩ := one_lt_card.mp (by omega : 1 < SR.card);obtain ⟨hz1S, hz1C⟩ := mem_filter.mp hz1;obtain ⟨hz2S, hz2C⟩ := mem_filter.mp hz2;have hz1N := (mem_Icc.mp (hSsub hz1S)).2;have hz2N := (mem_Icc.mp (hSsub hz2S)).2
     have hnotX : ({z1, z2} : Finset ℕ) ∉ X0 := hnot_in_X0 z1 z2 (by
       have h1 : 39 * N <= 40 * z1 := (hClo_spec z1).mp hz1C;have h2 : 39 * N <= 40 * z2 := (hClo_spec z2).mp hz2C
       omega)
     have hfill := hno z1 hz1S z2 hz2S (by have := (hClo_spec z1).mp hz1C; omega) (by have := (hClo_spec z2).mp hz2C; omega) hne hnotX
     set g := Nat.gcd (distNat c z1) (distNat c z2)
     have hg1 : 1 <= g := Nat.gcd_pos_of_pos_left _ (distNat_pos_of_ne (by have := (hClo_spec z1).mp hz1C; omega))
     have hgdvd : g ∣ distNat z1 z2 := by
       have h1 : g ∣ z1 - c := by
         rw [<- distNat_eq_sub (by have := (hClo_spec z1).mp hz1C; omega)];exact Nat.gcd_dvd_left _ _
       have h2 : g ∣ z2 - c := by
         rw [<- distNat_eq_sub (by have := (hClo_spec z2).mp hz2C; omega)];exact Nat.gcd_dvd_right _ _
       rcases le_total z1 z2 with hle | hle
       . rw [distNat_eq_sub hle]
         have : z2 - z1 = (z2 - c) - (z1 - c) := by have := (hClo_spec z1).mp hz1C; omega
         rw [this]; exact Nat.dvd_sub h2 h1
       . rw [distNat_eq_sub' hle]
         have : z1 - z2 = (z1 - c) - (z2 - c) := by have := (hClo_spec z2).mp hz2C; omega
         rw [this]; exact Nat.dvd_sub h1 h2
     have hg40 : 40 * g <= N := by
       have hle := Nat.le_of_dvd (distNat_pos_of_ne hne) hgdvd;have h1 := (hClo_spec z1).mp hz1C; have h2 := (hClo_spec z2).mp hz2C;unfold distNat at hle; omega
     have hne_SM := hmid_hit g hg1 hg40 (max z1 z2) (le_trans hz1C (le_max_left _ _)) (fun w hw1 hw2 hwm =>
       hfill w (by have := (hClo_spec z1).mp hz1C; have := (hClo_spec z2).mp hz2C; omega) (by omega) hwm)
     rw [hSM_empty] at hne_SM; exact Finset.not_nonempty_empty hne_SM
   rcases SR.eq_empty_or_nonempty with hSR_empty | hSR_ne
   ·
     apply hnotAP
     refine (apSet_of_all_fill hcS (fun x hx y hy hxc hyc hxy => ?_)).1
     have hnotX : ({x, y} : Finset ℕ) ∉ X0 := hnot_in_X0 x y (by
       have hxlt : x < Clo := by
         by_contra hge; push Not at hge;have : x ∈ SR := mem_filter.mpr ⟨hx, hge⟩;rw [hSR_empty] at this; exact notMem_empty _ this
       have hylt : y < Clo := by
         by_contra hge; push Not at hge;have : y ∈ SR := mem_filter.mpr ⟨hy, hge⟩;rw [hSR_empty] at this; exact notMem_empty _ this
       have h1 : ¬ 39 * N <= 40 * x := by rw [<- hClo_spec]; omega
       have h2 : ¬ 39 * N <= 40 * y := by rw [<- hClo_spec]; omega
       omega)
     exact hno x hx y hy hxc hyc hxy hnotX
   . obtain ⟨z, hz_eq⟩ := card_eq_one.mp (le_antisymm hSR_card (card_pos.mpr hSR_ne))
     have hzR : z ∈ SR := by rw [hz_eq]; simp
     obtain ⟨hzS, hzC⟩ := mem_filter.mp hzR
     rcases SL.eq_empty_or_nonempty with hSL_empty | hSL_ne
     . apply hnotAP
       have hS2 : S.card <= 2 := by
         have hsub : S ⊆ {c, z} := by
           intro w hw
           by_cases hwc : w = c
           . simp [hwc]
           by_cases hwA : w <= Ahi
           . exfalso; have : w ∈ SL := mem_filter.mpr ⟨hw, hwc, hwA⟩
             rw [hSL_empty] at this; exact notMem_empty _ this
           by_cases hwC : Clo <= w
           . have : w ∈ SR := mem_filter.mpr ⟨hw, hwC⟩
             rw [hz_eq, mem_singleton] at this; simp [this]
           . exfalso; have : w ∈ SM := mem_filter.mpr ⟨hw, by omega, by omega⟩
             rw [hSM_empty] at this; exact notMem_empty _ this
         exact le_trans (card_le_card hsub) (card_le_two)
       obtain ⟨l, hl, hAP⟩ := isAP_of_card_le_two S ⟨c, hcS⟩ hS2;exact apSet_of_isAP S l hl hAP
     . set x := SL.max' hSL_ne
       have hxL : x ∈ SL := max'_mem SL hSL_ne;obtain ⟨hxS, hxc, hxA⟩ := mem_filter.mp hxL;have hcz : c < z := by have := (hClo_spec z).mp hzC; omega
       have hxz : x ≠ z := by have := (hAhi_spec x).mp hxA; have := (hClo_spec z).mp hzC; omega
       by_cases hcx : c < x
       ·
         by_cases hxzX : ({x, z} : Finset ℕ) ∈ X0
         . obtain ⟨a, b, heq, hca, ha40, hb39, -, ⟨w, hw⟩⟩ := hX0 _ hxzX
           have hab : a < b := by omega
           have h1 : a ∈ ({x, z} : Finset ℕ) := by rw [heq]; simp
           have h2 : b ∈ ({x, z} : Finset ℕ) := by rw [heq]; simp
           have h3 : x ∈ ({a, b} : Finset ℕ) := by rw [<- heq]; simp
           simp only [mem_insert, mem_singleton] at h1 h2 h3;have hax : a = x := by omega
           have hbz : b = z := by omega
           rw [hax, hbz] at hw;obtain ⟨hwS, hwI⟩ := mem_inter.mp hw;obtain ⟨hw1, hw2⟩ := mem_Icc.mp hwI
           have hwSM : w ∈ SM := by
             refine mem_filter.mpr ⟨hwS, ?_, ?_⟩
             . by_contra hle; push Not at hle
               have hwL : w ∈ SL := mem_filter.mpr ⟨hwS, by omega, hle⟩;have := le_max' SL w hwL; omega
             . by_contra hge; push Not at hge
               have hwR : w ∈ SR := mem_filter.mpr ⟨hwS, hge⟩;rw [hz_eq, mem_singleton] at hwR; omega
           rw [hSM_empty] at hwSM; exact notMem_empty _ hwSM
         . have hfill := hno x hxS z hzS hxc (by omega) hxz hxzX
           set g := Nat.gcd (distNat c x) (distNat c z)
           have hg1 : 1 <= g := Nat.gcd_pos_of_pos_left _ (distNat_pos_of_ne hxc.symm)
           have hg40 : 40 * g <= N := by
             have hle : g <= distNat c x := Nat.le_of_dvd (distNat_pos_of_ne hxc.symm) (Nat.gcd_dvd_left _ _);have := (hAhi_spec x).mp hxA; unfold distNat at hle; omega
           have hne_SM := hmid_hit g hg1 hg40 z hzC (fun w hw1 hw2 hwm =>
             hfill w (by omega) (by omega) hwm)
           rw [hSM_empty] at hne_SM; exact Finset.not_nonempty_empty hne_SM
       ·
         have hnotX : ({x, z} : Finset ℕ) ∉ X0 := hnot_in_X0 x z (by omega);have hfill := hno x hxS z hzS hxc (by omega) hxz hnotX
         set g := Nat.gcd (distNat c x) (distNat c z)
         have hg1 : 1 <= g := Nat.gcd_pos_of_pos_left _ (distNat_pos_of_ne hxc.symm)
         have hg40 : 40 * g <= N := by
           have hle : g <= distNat c x := Nat.le_of_dvd (distNat_pos_of_ne hxc.symm) (Nat.gcd_dvd_left _ _);unfold distNat at hle; omega
         have hne_SM := hmid_hit g hg1 hg40 z hzC (fun w hw1 hw2 hwm =>
           hfill w (by omega) (by omega) hwm)
         rw [hSM_empty] at hne_SM; exact Finset.not_nonempty_empty hne_SM
 ·
   let W := S.filter (fun w => w < Clo)
   have hcW : c ∈ W := mem_filter.mpr ⟨hcS, by
     by_contra hge; push Not at hge; have := (hClo_spec c).mp hge; omega⟩
   have hW_fill : ∀ x ∈ W, ∀ y ∈ W, x ≠ c -> y ≠ c -> x ≠ y -> ∀ w, min c (min x y) <= w -> w <= max c (max x y) -> w % Nat.gcd (distNat c x) (distNat c y) = c % Nat.gcd (distNat c x) (distNat c y) -> w ∈ W := by
     intro x hx y hy hxc hyc hxy w hw1 hw2 hwm;obtain ⟨hxS, hxC⟩ := mem_filter.mp hx;obtain ⟨hyS, hyC⟩ := mem_filter.mp hy
     have hnotX : ({x, y} : Finset ℕ) ∉ X0 := hnot_in_X0 x y (by
       have h1 : ¬ 39 * N <= 40 * x := by rw [<- hClo_spec]; omega
       have h2 : ¬ 39 * N <= 40 * y := by rw [<- hClo_spec]; omega
       omega)
     have hwS := hno x hxS y hyS hxc hyc hxy hnotX w hw1 hw2 hwm;have hcC : c < Clo := (mem_filter.mp hcW).2;exact mem_filter.mpr ⟨hwS, by omega⟩
   obtain ⟨m0, hm0⟩ := hSM_ne;have hm0W : m0 ∈ W := mem_filter.mpr ⟨(mem_filter.mp hm0).1, (mem_filter.mp hm0).2.2⟩;have hm0c : m0 ≠ c := by have := (mem_filter.mp hm0).2.1; have := (hAhi_spec c).mpr hc40; omega
   have hW2 : 2 <= W.card := one_lt_card.mpr ⟨c, hcW, m0, hm0W, hm0c.symm⟩;obtain ⟨-, hW_ap⟩ := apSet_of_all_fill hcW hW_fill;obtain ⟨d, hd1, hW_eq, hd_dvdW⟩ := hW_ap hW2
   set wmax := W.max' ⟨c, hcW⟩
   have hwmaxW : wmax ∈ W := max'_mem W ⟨c, hcW⟩;obtain ⟨hwmaxS, hwmaxC⟩ := mem_filter.mp hwmaxW;have hwmax_gtA : Ahi < wmax := lt_of_lt_of_le (mem_filter.mp hm0).2.1 (le_max' W m0 hm0W);have hc_lt_wmax : c < wmax := by have := (hAhi_spec c).mpr hc40; omega
   have hd_wmax : d ∣ wmax - c := by have := hd_dvdW wmax hwmaxW; rwa [distNat_eq_sub (le_of_lt hc_lt_wmax)] at this
   set M := (wmax - c) / d
   have hMd : M * d = wmax - c := Nat.div_mul_cancel hd_wmax;have hM1 : 1 <= M := Nat.pos_of_ne_zero (fun h0 => by rw [h0, zero_mul] at hMd; omega)
   have hrunW : ∀ k ≤ M, c + k * d ∈ W := by
     intro k hk;have hrp := (mem_runPart W c d wmax).mp (hW_eq ▸ hwmaxW);have hkd : k * d <= M * d := Nat.mul_le_mul_right d hk;exact hrp.2.2 (c + k * d) (by omega) (by omega) (by rw [Nat.add_mul_mod_self_right])
   have hSR_props : ∀ z ∈ SR, d ∣ z - c /\ 19 * N <= 40 * (M * d) := by
     intro z hz;obtain ⟨hzS, hzC⟩ := mem_filter.mp hz;have hwmax_lt_z : wmax < z := by omega
     have hnotX : ({wmax, z} : Finset ℕ) ∉ X0 := hnot_in_X0 wmax z (by
       have h1 : ¬ 40 * wmax <= N := by rw [<- hAhi_spec]; omega
       omega)
     have hfill := hno wmax hwmaxS z hzS (by omega) (by omega) (by omega) hnotX
     set g := Nat.gcd (wmax - c) (z - c)
     have hg_eq : Nat.gcd (distNat c wmax) (distNat c z) = g := by rw [distNat_eq_sub (by omega), distNat_eq_sub (by omega)]
     have hg1 : 1 <= g := Nat.gcd_pos_of_pos_left _ (by omega)
     have hgd : d ∣ g := by
       by_contra hndvd;have hg_lt : g < wmax - c := lt_of_le_of_ne (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left _ _)) (fun h => hndvd (h ▸ hd_wmax));have hcgS : c + g ∈ S := hfill (c + g) (by omega) (by omega) (by rw [hg_eq, Nat.add_mod_right]);have hcgW : c + g ∈ W := mem_filter.mpr ⟨hcgS, by omega⟩;have hdg' := hd_dvdW (c + g) hcgW;rw [distNat_eq_sub (by omega), Nat.add_sub_cancel_left] at hdg';exact hndvd hdg'
     have hdz : d ∣ z - c := dvd_trans hgd (Nat.gcd_dvd_right _ _)
     have hwg_ge : Clo <= wmax + g := by
       by_contra hlt; push Not at hlt
       have hg_dvd_diff : g ∣ z - wmax := by
         have : z - wmax = (z - c) - (wmax - c) := by omega
         rw [this]; exact Nat.dvd_sub (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_left _ _)
       have hwg_le_z : wmax + g <= z := by have := Nat.le_of_dvd (by omega) hg_dvd_diff; omega
       have hwg_mod : (wmax + g) % g = c % g := by
         have h1 : wmax + g = c + ((wmax - c) + g) := by omega
         have h2 : g ∣ (wmax - c) + g := dvd_add (Nat.gcd_dvd_left _ _) (dvd_refl g);obtain ⟨t, ht⟩ := h2;rw [h1, ht, Nat.add_mul_mod_self_left]
       have hwgS : wmax + g ∈ S := hfill (wmax + g) (by omega) (by omega) (by rw [hg_eq]; exact hwg_mod);have hwgW : wmax + g ∈ W := mem_filter.mpr ⟨hwgS, hlt⟩;have := le_max' W (wmax + g) hwgW; omega
     have hg_le : g <= M * d := hMd ▸ Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left _ _);have hClo39 := (hClo_spec Clo).mp le_rfl;exact ⟨hdz, by omega⟩
   have hex_z : ∃ z ∈ SR, z ∉ runPart S c d := by
     by_contra hall; push Not at hall;apply hnotAP
     have hS_eq : S = runPart S c d := by
       refine Finset.Subset.antisymm (fun w hw => ?_) (runPart_subset S c d)
       by_cases hwC : w < Clo
       . have hwW : w ∈ W := mem_filter.mpr ⟨hw, hwC⟩
         have hrp := (mem_runPart W c d w).mp (hW_eq ▸ hwW)
         exact (mem_runPart S c d w).mpr ⟨hw, hrp.2.1, fun y hy1 hy2 hym =>
           (mem_filter.mp (hrp.2.2 y hy1 hy2 hym)).1⟩
       . exact hall w (mem_filter.mpr ⟨hw, by omega⟩)
     exact hS_eq ▸ runPart_isAP hcS hd1
   obtain ⟨z, hzR, hz_notR⟩ := hex_z;obtain ⟨hzS, hzC⟩ := mem_filter.mp hzR;obtain ⟨hdz, hMd19⟩ := hSR_props z hzR
   set K := (z - c) / d
   have hKd : K * d = z - c := Nat.div_mul_cancel hdz;have hzN : z <= N := (mem_Icc.mp (hSsub hzS)).2;have hK_pos : 1 <= K := Nat.pos_of_ne_zero (fun h0 => by rw [h0, zero_mul] at hKd; omega)
   have hK_ub : 19 * K <= 40 * M := by
     have h1 : 19 * (K * d) <= 40 * (M * d) := by omega
     have h2 : (19 * K) * d <= (40 * M) * d := by nlinarith
     exact Nat.le_of_mul_le_mul_right h2 (by omega)
   set K0 := (Ahi - c) / d
   have hK0_le : 19 * K0 <= M := by
     have h1 : K0 * d <= Ahi := le_trans (Nat.div_mul_le_self (Ahi - c) d) (Nat.sub_le _ _);have hAhi40 := (hAhi_spec Ahi).mp le_rfl
     have h2 : (19 * K0) * d <= M * d := by
       have h3 : 40 * ((19 * K0) * d) = 19 * (40 * (K0 * d)) := by ring
       have h4 : 40 * (K0 * d) <= N := by omega
       have h5 : 19 * (40 * (K0 * d)) <= 19 * N := Nat.mul_le_mul_left 19 h4;omega
     exact Nat.le_of_mul_le_mul_right h2 (by omega)
   have hno_cop : ∀ k, K0 < k -> k <= M -> ¬ Nat.Coprime k K := by
     intro k hk1 hk2 hcop;have hckW : c + k * d ∈ W := hrunW k hk2;have hckS : c + k * d ∈ S := (mem_filter.mp hckW).1
     have hck_gtA : Ahi < c + k * d := by
       have h1 : Ahi - c < K0 * d + d := Nat.lt_div_mul_add (a := Ahi - c) (b := d) (by omega);have h2 : (K0 + 1) * d <= k * d := Nat.mul_le_mul_right d hk1;have h3 : (K0 + 1) * d = K0 * d + d := by ring
       have hcA : c <= Ahi := (hAhi_spec c).mpr hc40;omega
     have hck_ltC : c + k * d < Clo := (mem_filter.mp hckW).2
     have hnotX : ({c + k * d, z} : Finset ℕ) ∉ X0 := hnot_in_X0 (c + k * d) z (by
       have h1 : ¬ 40 * (c + k * d) <= N := by rw [<- hAhi_spec]; omega
       omega)
     have hfill := hno (c + k * d) hckS z hzS (by nlinarith) (by omega) (by omega) hnotX;have hgcd_d : Nat.gcd (distNat c (c + k * d)) (distNat c z) = d := by rw [distNat_eq_sub (by omega), distNat_eq_sub (by omega), Nat.add_sub_cancel_left, <- hKd, Nat.gcd_mul_right, hcop.gcd_eq_one, one_mul]
     apply hz_notR;rw [mem_runPart]
     refine ⟨hzS, ?_, fun w hw1 hw2 hwm => hfill w (by omega) (by omega) (by rwa [hgcd_d])⟩
     have : z = c + K * d := by omega
     rw [this, Nat.add_mul_mod_self_right]
   rcases Nat.eq_zero_or_pos K0 with hK0_0 | hK0_pos
   . exact hno_cop 1 (by omega) hM1 (Nat.coprime_one_left K)
   . have hM19 : 19 <= M := by omega
     by_cases hM24 : M < 24
     . have hK0_1 : K0 = 1 := by omega
       have h11 : 11 ∣ K := by
         have hnc := hno_cop 11 (by omega) (by omega);exact (Nat.Prime.coprime_iff_not_dvd (by norm_num)).not_left.mp hnc
       have h13 : 13 ∣ K := by
         have hnc := hno_cop 13 (by omega) (by omega);exact (Nat.Prime.coprime_iff_not_dvd (by norm_num)).not_left.mp hnc
       have h143 : 11 * 13 ∣ K := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h11 h13;have := Nat.le_of_dvd hK_pos h143;omega
     . push Not at hM24
       obtain ⟨p1, hp1_pr, hp1_lo, hp1_hi⟩ := Nat.exists_prime_lt_and_le_two_mul (M / 2) (by omega);obtain ⟨p2, hp2_pr, hp2_lo, hp2_hi⟩ := Nat.exists_prime_lt_and_le_two_mul (M / 4) (by omega);have hp1_leM : p1 <= M := by omega
       have hp2_lt_p1 : p2 < p1 := by omega
       have hK0_lt_p2 : K0 < p2 := by omega
       have hp1_dvd : p1 ∣ K := (hp1_pr.coprime_iff_not_dvd).not_left.mp (hno_cop p1 (by omega) hp1_leM);have hp2_dvd : p2 ∣ K := (hp2_pr.coprime_iff_not_dvd).not_left.mp (hno_cop p2 hK0_lt_p2 (by omega));have hcop_p : Nat.Coprime p1 p2 := (Nat.coprime_primes hp1_pr hp2_pr).mpr (ne_of_gt hp2_lt_p1);have hmul_dvd : p1 * p2 ∣ K := hcop_p.mul_dvd_of_dvd_of_dvd hp1_dvd hp2_dvd;have hmul_le : p1 * p2 <= K := Nat.le_of_dvd hK_pos hmul_dvd;have h2p1 : M + 1 <= 2 * p1 := by omega
       have h4p2 : M + 1 <= 4 * p2 := by omega
       nlinarith
lemma near_kernel_linear_bound_left {N c : ℕ} (hN : 400 <= N) (hc : c ∈ Icc 1 N) {F : Finset (Finset ℕ)} (hF : IsWellInter N F) (hnear : ∀ B ∈ F, c ∉ B -> 39 * N <= 40 * B.card) (hc40 : (∃ B ∈ F, c ∉ B /\ ∃ l r, B = Icc l r) -> 40 * c <= N) : (F.card : ℝ) <= (((N - 1) * (N - 2) / 2 : ℕ) : ℝ) + 46 * (N : ℝ) + 3 := by
 classical
 let F0 := F.filter (fun S => S.card <= 2)
 let Fcbar := F.filter (fun S => 3 <= S.card /\ c ∉ S)
 let E := F.filter (fun S => 3 <= S.card /\ c ∈ S /\ APSet S)
 let H := F.filter (fun S => 3 <= S.card /\ c ∈ S /\ ¬ APSet S)
 have hF_cov : F ⊆ F0 ∪ (Fcbar ∪ (E ∪ H)) := by
   intro S hS
   by_cases h2 : S.card <= 2
   . exact mem_union_left _ (mem_filter.mpr ⟨hS, h2⟩)
   by_cases hcS : c ∈ S
   . by_cases hap : APSet S
     . exact mem_union_right _ (mem_union_right _ (mem_union_left _ (mem_filter.mpr ⟨hS, by omega, hcS, hap⟩)))
     . exact mem_union_right _ (mem_union_right _ (mem_union_right _ (mem_filter.mpr ⟨hS, by omega, hcS, hap⟩)))
   . exact mem_union_right _ (mem_union_left _ (mem_filter.mpr ⟨hS, by omega, hcS⟩))
 have hF_card : F.card <= F0.card + Fcbar.card + E.card + H.card := by
   have h1 := le_trans (card_le_card hF_cov) (card_union_le _ _);have h2 := card_union_le Fcbar (E ∪ H);have h3 := card_union_le E H;omega
 have hF0_card : F0.card <= N + 3 := card_size_le_two hF
 let Ifam := Fcbar.filter (fun B => ∃ l r, B = Icc l r)
 let Fcbar_nonI := Fcbar.filter (fun B => ¬ ∃ l r, B = Icc l r)
 have hFcbar_split : Fcbar.card <= Ifam.card + Fcbar_nonI.card := by
   refine le_trans (card_le_card ?_) (card_union_le _ _)
   intro B hB
   by_cases hI : ∃ l r, B = Icc l r
   . exact mem_union_left _ (mem_filter.mpr ⟨hB, hI⟩)
   . exact mem_union_right _ (mem_filter.mpr ⟨hB, hI⟩)
 have hnonI_le : Fcbar_nonI.card <= N := by
   by_cases h1 : Fcbar_nonI.card <= 1
   . omega
   set mid := N / 2
   have hinter_int : ∀ B1 ∈ Fcbar, ∀ B2 ∈ Fcbar, B1 ≠ B2 -> mid ∈ B1 ∩ B2 /\ ∃ l r, B1 ∩ B2 = Icc l r := by
     intro B1 hB1 B2 hB2 hne;have hB1F := (mem_filter.mp hB1).1;have hB2F := (mem_filter.mp hB2).1;have hc1 := hnear B1 hB1F (mem_filter.mp hB1).2.2;have hc2 := hnear B2 hB2F (mem_filter.mp hB2).2.2
     have hu_le : (B1 ∪ B2).card <= N := by
       have := card_le_card (Finset.union_subset (hF.1 B1 hB1F) (hF.1 B2 hB2F));rwa [Nat.card_Icc, Nat.add_sub_cancel] at this
     have hiu := card_union_add_card_inter B1 B2;have hinter_sz : 38 * N <= 40 * (B1 ∩ B2).card := by omega
     have hAP := hF.2 B1 hB1F B2 hB2F hne;obtain ⟨d, hd1, hab, -, hmem, hcard_eq⟩ := apSet_canonical hAP (by omega)
     set a := (B1 ∩ B2).min' (card_pos.mp (by omega))
     set b := (B1 ∩ B2).max' (card_pos.mp (by omega))
     have ha1 : 1 <= a := (mem_Icc.mp (hF.1 B1 hB1F (mem_of_mem_inter_left (min'_mem _ _)))).1;have hbN : b <= N := (mem_Icc.mp (hF.1 B1 hB1F (mem_of_mem_inter_left (max'_mem _ _)))).2
     have hd_eq1 : d = 1 := by
       by_contra hne1;have hd2 : 2 <= d := by omega
       have hmul : ((B1 ∩ B2).card - 1) * 2 <= ((B1 ∩ B2).card - 1) * d := Nat.mul_le_mul_left _ hd2;omega
     rw [hd_eq1] at hmem hcard_eq
     have hIcc : B1 ∩ B2 = Icc a b := by
       ext x; rw [hmem x, mem_Icc]; simp only [Nat.mod_one, and_true]
     have hmid_mem : mid ∈ B1 ∩ B2 := by rw [hIcc, mem_Icc]; omega
     exact ⟨hmid_mem, a, b, hIcc⟩
   have hmid_in : ∀ B ∈ Fcbar_nonI, mid ∈ B := by
     intro B hB;obtain ⟨A1, hA1, A2, hA2, hA12⟩ := one_lt_card.mp (by omega : 1 < Fcbar_nonI.card)
     by_cases hBA1 : B = A1
     . exact mem_of_mem_inter_left (hinter_int B (mem_filter.mp hB).1
         A2 (mem_filter.mp hA2).1 (hBA1 ▸ hA12)).1
     . exact mem_of_mem_inter_left (hinter_int B (mem_filter.mp hB).1
         A1 (mem_filter.mp hA1).1 hBA1).1
   have hdiff_ne : ∀ B : {B // B ∈ Fcbar_nonI}, (B.1 \ runPart B.1 mid 1).Nonempty := by
     rintro ⟨B, hB⟩;by_contra hE;rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hE;have hBeq : B = runPart B mid 1 := Finset.Subset.antisymm hE (runPart_subset B mid 1);have hmidB := hmid_in B hB;have hneB : B.Nonempty := ⟨mid, hmidB⟩;apply (mem_filter.mp hB).2
     refine ⟨B.min' hneB, B.max' hneB, ?_⟩
     ext x; rw [mem_Icc]
     constructor
     . intro hx; exact ⟨min'_le B x hx, le_max' B x hx⟩
     . rintro ⟨hx1, hx2⟩
       have hmin_rp := (mem_runPart B mid 1 (B.min' hneB)).mp (hBeq ▸ min'_mem B hneB);have hmax_rp := (mem_runPart B mid 1 (B.max' hneB)).mp (hBeq ▸ max'_mem B hneB);have hmin_le : B.min' hneB <= mid := min'_le B mid hmidB;have hmid_le : mid <= B.max' hneB := le_max' B mid hmidB
       rcases le_total x mid with hle | hle
       . exact hmin_rp.2.2 x (by omega) (by omega) (by simp [Nat.mod_one])
       . exact hmax_rp.2.2 x (by omega) (by omega) (by simp [Nat.mod_one])
   choose wB hwB using hdiff_ne
   have hcard_le : Fcbar_nonI.card <= (Icc 1 N).card := by
     rw [<- card_attach]
     refine card_le_card_of_injOn wB ?_ ?_
     . intro B _
       exact mem_coe.mpr (hF.1 B.1 (mem_filter.mp (mem_filter.mp B.2).1).1 (Finset.sdiff_subset (hwB B)))
     . intro B1 _ B2 _ heq
       by_contra hne;have hB12 : B1.1 ≠ B2.1 := fun h => hne (Subtype.ext h)
       obtain ⟨hmid_in12, l, r, hIcc⟩ := hinter_int B1.1 (mem_filter.mp B1.2).1
         B2.1 (mem_filter.mp B2.2).1 hB12
       have hw1 := Finset.mem_sdiff.mp (hwB B1);have hw2 := Finset.mem_sdiff.mp (heq ▸ hwB B2);have hw12 : wB B1 ∈ B1.1 ∩ B2.1 := mem_inter.mpr ⟨hw1.1, hw2.1⟩;apply hw1.2;rw [mem_runPart]
       refine ⟨hw1.1, by simp [Nat.mod_one], fun y hy1 hy2 _ => ?_⟩
       rw [hIcc, mem_Icc] at hmid_in12 hw12;have hy12 : y ∈ B1.1 ∩ B2.1 := by rw [hIcc, mem_Icc]; omega
       exact mem_of_mem_inter_left hy12
   rwa [Nat.card_Icc, Nat.add_sub_cancel] at hcard_le
 let U := ((Icc 1 N).erase c).powersetCard 2
 have hU_card : U.card = (N - 1) * (N - 2) / 2 := by
   dsimp only [U];rw [card_powersetCard, card_erase_of_mem hc, Nat.card_Icc, Nat.add_sub_cancel, Nat.choose_two_right];have : N - 1 - 1 = N - 2 := by omega
   rw [this]
 obtain ⟨Forb, hForb_sub, hForb_inE, -, hE_forb, hE_forb_X0⟩ := ap_forb_surplus (by omega) hc hF (fun S hS => (mem_filter.mp hS).1) (fun S hS => (mem_filter.mp hS).2)
 have hpair_to_U : ∀ S ∈ H, ∀ x y, x ∈ S -> y ∈ S -> x ≠ c -> y ≠ c -> x ≠ y -> ¬ (∀ w, min c (min x y) <= w -> w <= max c (max x y) -> w % Nat.gcd (distNat c x) (distNat c y) = c % Nat.gcd (distNat c x) (distNat c y) -> w ∈ S) -> ({x, y} : Finset ℕ) ∈ U \ Forb /\ IsDeltaTriplet F S c x y := by
   intro S hS x y hxS hyS hxc hyc hxy hnofill;have hSF := (mem_filter.mp hS).1;have hcS := (mem_filter.mp hS).2.2.1;have hnotAP := (mem_filter.mp hS).2.2.2
   have hdt : IsDeltaTriplet F S c x y := by
     by_contra hnot;have hnu := nu_triplet_fill hF hSF hcS hxS hyS hxc.symm hyc.symm hxy hnot;exact hnofill hnu.2.2.2
   have hmemU : ({x, y} : Finset ℕ) ∈ U := mem_powersetCard.mpr ⟨fun z hz => by
     simp only [mem_insert, mem_singleton] at hz
     rcases hz with rfl | rfl
     . exact Finset.mem_erase.mpr ⟨hxc, hF.1 S hSF hxS⟩
     . exact Finset.mem_erase.mpr ⟨hyc, hF.1 S hSF hyS⟩, card_pair hxy⟩
   have hnotForb : ({x, y} : Finset ℕ) ∉ Forb := by
     intro hmemF;obtain ⟨E0, hE0, heE0, -⟩ := hForb_inE _ hmemF;have hE0F := (mem_filter.mp hE0).1;have hE0AP := (mem_filter.mp hE0).2.2.2;have hE0c := (mem_filter.mp hE0).2.2.1;have hSE0 : E0 ≠ S := fun h => hnotAP (h ▸ hE0AP)
     exact hdt.2.2.2.2.2.2 E0 hE0F hSE0 ⟨hE0c, heE0 (by simp), heE0 (by simp)⟩
   exact ⟨Finset.mem_sdiff.mpr ⟨hmemU, hnotForb⟩, hdt⟩
 rcases Ifam.eq_empty_or_nonempty with hIfam_empty | hIfam_ne
 ·
   have hH_pair : ∀ S : {S // S ∈ H}, ∃ e : Finset ℕ, e ∈ U \ Forb /\ ∃ x y, e = {x, y} /\ IsDeltaTriplet F S.1 c x y := by
     rintro ⟨S, hS⟩;have hcS := (mem_filter.mp hS).2.2.1;have hnotAP := (mem_filter.mp hS).2.2.2
     have hex : ∃ x ∈ S, ∃ y ∈ S, x ≠ c /\ y ≠ c /\ x ≠ y /\ ¬ (∀ w, min c (min x y) <= w -> w <= max c (max x y) -> w % Nat.gcd (distNat c x) (distNat c y) = c % Nat.gcd (distNat c x) (distNat c y) -> w ∈ S) := by
       by_contra hall; push Not at hall;exact hnotAP (apSet_of_all_fill hcS hall).1
     obtain ⟨x, hxS, y, hyS, hxc, hyc, hxy, hnofill⟩ := hex;obtain ⟨he, hdt⟩ := hpair_to_U S hS x y hxS hyS hxc hyc hxy hnofill;exact ⟨{x, y}, he, x, y, rfl, hdt⟩
   choose eH heH using hH_pair
   have hH_le : H.card <= (U \ Forb).card := by
     rw [<- card_attach]
     refine card_le_card_of_injOn eH (fun S _ => mem_coe.mpr (heH S).1) ?_
     intro S _ T _ heq;by_contra hne;have hST : S.1 ≠ T.1 := fun h => hne (Subtype.ext h)
     obtain ⟨x, y, hSe, hdtS⟩ := (heH S).2;obtain ⟨a, b, hTe, hdtT⟩ := (heH T).2
     have hxy_sub : ({x, y} : Finset ℕ) ⊆ T.1 := by
       rw [<- hSe, heq, hTe];intro z hz; simp only [mem_insert, mem_singleton] at hz
       rcases hz with rfl | rfl; exact hdtT.2.1; exact hdtT.2.2.1
     exact hdtS.2.2.2.2.2.2 T.1 (mem_filter.mp T.2).1 hST.symm ⟨hdtT.1, hxy_sub (by simp), hxy_sub (by simp)⟩
   have hUF : (U \ Forb).card + Forb.card = U.card := card_sdiff_add_card_eq_card hForb_sub;have hFcbar_le : Fcbar.card <= N := by rw [hIfam_empty, card_empty] at hFcbar_split; omega
   have hF_R : (F.card : ℝ) <= (F0.card : ℝ) + (Fcbar.card : ℝ) + (E.card : ℝ) + (H.card : ℝ) := by exact_mod_cast hF_card
   have hF0_R : (F0.card : ℝ) <= (N : ℝ) + 3 := by exact_mod_cast hF0_card
   have hFc_R : (Fcbar.card : ℝ) <= (N : ℝ) := by exact_mod_cast hFcbar_le
   have hH_R : (H.card : ℝ) + (Forb.card : ℝ) <= (((N - 1) * (N - 2) / 2 : ℕ) : ℝ) := by
     have : H.card + Forb.card <= (N - 1) * (N - 2) / 2 := by rw [<- hU_card, <- hUF]; omega
     exact_mod_cast this
   linarith
 ·
   have hc40_val : 40 * c <= N := by
     obtain ⟨B0, hB0⟩ := hIfam_ne;obtain ⟨hB0c, l, r, hB0eq⟩ := mem_filter.mp hB0;exact hc40 ⟨B0, (mem_filter.mp hB0c).1, (mem_filter.mp hB0c).2.2, l, r, hB0eq⟩
   have hIfam_lr : ∀ B ∈ Ifam, ∃ l r, B = Icc l r /\ c < l /\ l <= r /\ r <= N /\ 40 * (l - 1) <= N /\ 39 * N <= 40 * r := by
     intro B hB;obtain ⟨hBc, l, r, hBeq⟩ := mem_filter.mp hB;have hBF := (mem_filter.mp hBc).1;have hcnotB := (mem_filter.mp hBc).2.2;have hBsz := hnear B hBF hcnotB;have hBne : B.Nonempty := card_pos.mp (by omega)
     have hlr : l <= r := by
       rw [hBeq] at hBne; obtain ⟨w, hw⟩ := hBne;have := mem_Icc.mp hw; omega
     have hl1 : 1 <= l := (mem_Icc.mp (hF.1 B hBF (hBeq.symm ▸ mem_Icc.mpr ⟨le_rfl, hlr⟩))).1;have hrN : r <= N := (mem_Icc.mp (hF.1 B hBF (hBeq.symm ▸ mem_Icc.mpr ⟨hlr, le_rfl⟩))).2;have hBcard : B.card = r + 1 - l := by rw [hBeq, Nat.card_Icc]
     have hcl : c < l := by
       by_contra hle; push Not at hle
       have hrc : r < c := by
         by_contra hge; push Not at hge;exact hcnotB (hBeq.symm ▸ mem_Icc.mpr ⟨hle, hge⟩)
       omega
     exact ⟨l, r, hBeq, hcl, hlr, hrN, by omega, by omega⟩
   let Ifam_l := Ifam.filter (fun B => c + 1 ∈ B)
   let Ifam_r := Ifam.filter (fun B => N ∈ B)
   let Ifam_int := Ifam.filter (fun B => c + 1 ∉ B /\ N ∉ B)
   have hIfam_cov : Ifam ⊆ Ifam_l ∪ (Ifam_r ∪ Ifam_int) := by
     intro B hB
     by_cases h1 : c + 1 ∈ B
     . exact mem_union_left _ (mem_filter.mpr ⟨hB, h1⟩)
     by_cases h2 : N ∈ B
     . exact mem_union_right _ (mem_union_left _ (mem_filter.mpr ⟨hB, h2⟩))
     . exact mem_union_right _ (mem_union_right _ (mem_filter.mpr ⟨hB, h1, h2⟩))
   have hIl_le : Ifam_l.card <= N := by
     have h1 : Ifam_l.card <= (Icc 1 N).card := by
       refine card_le_card_of_injOn (fun B => B.card) ?_ ?_
       . intro B hB
         have hBF := (mem_filter.mp (mem_filter.mp (mem_filter.mp (mem_coe.mp hB)).1).1).1;have hB3 := (mem_filter.mp (mem_filter.mp (mem_filter.mp (mem_coe.mp hB)).1).1).2.1;have hleN := card_le_card (hF.1 B hBF); rw [Nat.card_Icc, Nat.add_sub_cancel] at hleN;exact mem_coe.mpr (mem_Icc.mpr ⟨by dsimp only; omega, hleN⟩)
       . intro B1 hB1 B2 hB2 heq
         dsimp only at heq;obtain ⟨hB1I, hc1_1⟩ := mem_filter.mp (mem_coe.mp hB1);obtain ⟨hB2I, hc1_2⟩ := mem_filter.mp (mem_coe.mp hB2);obtain ⟨l1, r1, h1eq, hcl1, hlr1, -, -, -⟩ := hIfam_lr B1 hB1I;obtain ⟨l2, r2, h2eq, hcl2, hlr2, -, -, -⟩ := hIfam_lr B2 hB2I;rw [h1eq, mem_Icc] at hc1_1;rw [h2eq, mem_Icc] at hc1_2;have hl1 : l1 = c + 1 := by omega
         have hl2 : l2 = c + 1 := by omega
         rw [h1eq, h2eq, Nat.card_Icc, Nat.card_Icc] at heq;have hr : r1 = r2 := by omega
         rw [h1eq, h2eq, hl1, hl2, hr]
     rwa [Nat.card_Icc, Nat.add_sub_cancel] at h1
   have hIr_le : Ifam_r.card <= N := by
     have h1 : Ifam_r.card <= (Icc 1 N).card := by
       refine card_le_card_of_injOn (fun B => B.card) ?_ ?_
       . intro B hB
         have hBF := (mem_filter.mp (mem_filter.mp (mem_filter.mp (mem_coe.mp hB)).1).1).1;have hB3 := (mem_filter.mp (mem_filter.mp (mem_filter.mp (mem_coe.mp hB)).1).1).2.1;have hleN := card_le_card (hF.1 B hBF); rw [Nat.card_Icc, Nat.add_sub_cancel] at hleN;exact mem_coe.mpr (mem_Icc.mpr ⟨by dsimp only; omega, hleN⟩)
       . intro B1 hB1 B2 hB2 heq
         dsimp only at heq;obtain ⟨hB1I, hN1⟩ := mem_filter.mp (mem_coe.mp hB1);obtain ⟨hB2I, hN2⟩ := mem_filter.mp (mem_coe.mp hB2);obtain ⟨l1, r1, h1eq, -, hlr1, hrN1, -, -⟩ := hIfam_lr B1 hB1I;obtain ⟨l2, r2, h2eq, -, hlr2, hrN2, -, -⟩ := hIfam_lr B2 hB2I;rw [h1eq, mem_Icc] at hN1;rw [h2eq, mem_Icc] at hN2;have hr1 : r1 = N := by omega
         have hr2 : r2 = N := by omega
         rw [h1eq, h2eq, Nat.card_Icc, Nat.card_Icc] at heq;have hl : l1 = l2 := by omega
         rw [h1eq, h2eq, hl, hr1, hr2]
     rwa [Nat.card_Icc, Nat.add_sub_cancel] at h1
   let pairOf : Finset ℕ -> Finset ℕ := fun B =>
     if hne : B.Nonempty then ({B.min' hne - 1, B.max' hne + 1} : Finset ℕ) else ∅
   let X0 := Ifam_int.image pairOf
   have hX0_props : X0.card = Ifam_int.card /\ X0 ⊆ U /\ ∀ e ∈ X0, ∃ x y, e = {x, y} /\ c < x /\ 40 * x <= N /\ 39 * N <= 40 * y /\ y <= N /\ Icc (x + 1) (y - 1) ∈ F /\ c ∉ Icc (x + 1) (y - 1) := by
     have hpair_eq : ∀ B ∈ Ifam_int, ∃ l r, B = Icc l r /\ pairOf B = {l - 1, r + 1} /\ c < l - 1 /\ 40 * (l - 1) <= N /\ 39 * N <= 40 * (r + 1) /\ r + 1 <= N := by
       intro B hB;obtain ⟨hBI, hc1not, hNnot⟩ := mem_filter.mp hB;obtain ⟨l, r, hBeq, hcl, hlr, hrN, hl40, hr39⟩ := hIfam_lr B hBI;have hBne : B.Nonempty := ⟨l, hBeq.symm ▸ mem_Icc.mpr ⟨le_rfl, hlr⟩⟩
       have hmin_eq : B.min' hBne = l := by
         apply le_antisymm
         . exact min'_le B l (hBeq.symm ▸ mem_Icc.mpr ⟨le_rfl, hlr⟩)
         . have hm : B.min' hBne ∈ Icc l r := hBeq ▸ min'_mem B hBne
           exact (mem_Icc.mp hm).1
       have hmax_eq : B.max' hBne = r := by
         apply le_antisymm
         . have hm : B.max' hBne ∈ Icc l r := hBeq ▸ max'_mem B hBne
           exact (mem_Icc.mp hm).2
         . exact le_max' B r (hBeq.symm ▸ mem_Icc.mpr ⟨hlr, le_rfl⟩)
       have hpeq : pairOf B = {l - 1, r + 1} := by dsimp only [pairOf]; rw [dif_pos hBne, hmin_eq, hmax_eq]
       have hl_gt : c + 1 < l := by
         by_contra hle; push Not at hle;exact hc1not (hBeq.symm ▸ mem_Icc.mpr ⟨by omega, by omega⟩)
       have hr_lt : r < N := by
         by_contra hge; push Not at hge;exact hNnot (hBeq.symm ▸ mem_Icc.mpr ⟨by omega, by omega⟩)
       exact ⟨l, r, hBeq, hpeq, by omega, hl40, by omega, by omega⟩
     have hinj : Set.InjOn pairOf (Ifam_int : Set (Finset ℕ)) := by
       intro B1 hB1 B2 hB2 heq;obtain ⟨l1, r1, h1eq, hp1, hc1, hl1, hr1, hrN1⟩ := hpair_eq B1 (mem_coe.mp hB1);obtain ⟨l2, r2, h2eq, hp2, hc2, hl2, hr2, hrN2⟩ := hpair_eq B2 (mem_coe.mp hB2);rw [hp1, hp2] at heq;have h1m : l1 - 1 ∈ ({l2 - 1, r2 + 1} : Finset ℕ) := by rw [<- heq]; simp
       have h2m : r1 + 1 ∈ ({l2 - 1, r2 + 1} : Finset ℕ) := by rw [<- heq]; simp
       simp only [mem_insert, mem_singleton] at h1m h2m;have hl_eq : l1 = l2 := by omega
       have hr_eq : r1 = r2 := by omega
       rw [h1eq, h2eq, hl_eq, hr_eq]
     refine ⟨card_image_of_injOn hinj, ?_, ?_⟩
     . intro e he
       obtain ⟨B, hB, rfl⟩ := mem_image.mp he;obtain ⟨l, r, -, hpeq, hcl, hl40, hr39, hrN⟩ := hpair_eq B hB;rw [hpeq]
       refine mem_powersetCard.mpr ⟨fun z hz => ?_, card_pair (by omega)⟩
       simp only [mem_insert, mem_singleton] at hz;have hcI := mem_Icc.mp hc
       rcases hz with rfl | rfl
       . exact Finset.mem_erase.mpr ⟨by omega, mem_Icc.mpr ⟨by omega, by omega⟩⟩
       . exact Finset.mem_erase.mpr ⟨by omega, mem_Icc.mpr ⟨by omega, by omega⟩⟩
     . intro e he
       obtain ⟨B, hB, rfl⟩ := mem_image.mp he;obtain ⟨l, r, hBeq, hpeq, hcl, hl40, hr39, hrN⟩ := hpair_eq B hB;have hBF := (mem_filter.mp (mem_filter.mp (mem_filter.mp hB).1).1).1;have hcnotB := (mem_filter.mp (mem_filter.mp (mem_filter.mp hB).1).1).2.2;have hIcc_eq : Icc (l - 1 + 1) (r + 1 - 1) = B := by rw [hBeq]; congr 1; omega
       exact ⟨l - 1, r + 1, hpeq, hcl, hl40, hr39, hrN, hIcc_eq ▸ hBF, hIcc_eq ▸ hcnotB⟩
   have hH_pair : ∀ S : {S // S ∈ H}, ∃ e : Finset ℕ, e ∈ U \ (Forb ∪ X0) /\ ∃ x y, e = {x, y} /\ IsDeltaTriplet F S.1 c x y := by
     rintro ⟨S, hS⟩;have hSF := (mem_filter.mp hS).1;have hcS := (mem_filter.mp hS).2.2.1;have hnotAP := (mem_filter.mp hS).2.2.2
     obtain ⟨x, hxS, y, hyS, hxc, hyc, hxy, hnotX0, hnofill⟩ := near_kernel_pair_avoidance hN (mem_Icc.mp hc).1 hc40_val (hF.1 S hSF) hcS hnotAP (fun e he => by
           obtain ⟨a, b, heq, hca, ha40, hb39, hbN, hBF, hcnotB⟩ := hX0_props.2.2 e he
           exact ⟨a, b, heq, hca, ha40, hb39, hbN, wellInter_meet hF hSF hBF (fun h => hcnotB (h ▸ hcS))⟩)
     obtain ⟨heUF, hdt⟩ := hpair_to_U S hS x y hxS hyS hxc hyc hxy hnofill;obtain ⟨heU, heNotF⟩ := Finset.mem_sdiff.mp heUF
     exact ⟨{x, y}, Finset.mem_sdiff.mpr ⟨heU, fun h => by
       rcases mem_union.mp h with h1 | h2
       . exact heNotF h1
       . exact hnotX0 h2⟩, x, y, rfl, hdt⟩
   choose eH heH using hH_pair
   have hH_le : H.card <= (U \ (Forb ∪ X0)).card := by
     rw [<- card_attach]
     refine card_le_card_of_injOn eH (fun S _ => mem_coe.mpr (heH S).1) ?_
     intro S _ T _ heq;by_contra hne;have hST : S.1 ≠ T.1 := fun h => hne (Subtype.ext h)
     obtain ⟨x, y, hSe, hdtS⟩ := (heH S).2;obtain ⟨a, b, hTe, hdtT⟩ := (heH T).2
     have hxy_sub : ({x, y} : Finset ℕ) ⊆ T.1 := by
       rw [<- hSe, heq, hTe];intro z hz; simp only [mem_insert, mem_singleton] at hz
       rcases hz with rfl | rfl; exact hdtT.2.1; exact hdtT.2.2.1
     exact hdtS.2.2.2.2.2.2 T.1 (mem_filter.mp T.2).1 hST.symm ⟨hdtT.1, hxy_sub (by simp), hxy_sub (by simp)⟩
   have hFX_sub : Forb ∪ X0 ⊆ U := Finset.union_subset hForb_sub hX0_props.2.1;have hUFX : (U \ (Forb ∪ X0)).card + (Forb ∪ X0).card = U.card := card_sdiff_add_card_eq_card hFX_sub;have hFX_eq : (Forb ∪ X0).card = (Forb \ X0).card + X0.card := by rw [<- card_union_of_disjoint Finset.sdiff_disjoint, Finset.sdiff_union_self_eq_union]
   have hE_bd : (E.card : ℝ) <= ((Forb \ X0).card : ℝ) + 42 * (N : ℝ) := hE_forb_X0 X0 hN hc40_val (fun e he => by
       obtain ⟨a, b, h1, h2, h3, h4, h5, -, -⟩ := hX0_props.2.2 e he
       exact ⟨a, b, h1, h2, h3, h4, h5⟩)
   have hIfam_le : Ifam.card <= X0.card + 2 * N := by
     have h1 := le_trans (card_le_card hIfam_cov) (card_union_le _ _);have h2 := card_union_le Ifam_r Ifam_int;omega
   have hFcbar_le : Fcbar.card <= X0.card + 3 * N := by omega
   have hF_R : (F.card : ℝ) <= (F0.card : ℝ) + (Fcbar.card : ℝ) + (E.card : ℝ) + (H.card : ℝ) := by exact_mod_cast hF_card
   have hF0_R : (F0.card : ℝ) <= (N : ℝ) + 3 := by exact_mod_cast hF0_card
   have hFc_R : (Fcbar.card : ℝ) <= (X0.card : ℝ) + 3 * (N : ℝ) := by exact_mod_cast hFcbar_le
   have hH_R : (H.card : ℝ) + ((Forb \ X0).card : ℝ) + (X0.card : ℝ) <= (((N - 1) * (N - 2) / 2 : ℕ) : ℝ) := by
     have : H.card + (Forb \ X0).card + X0.card <= (N - 1) * (N - 2) / 2 := by rw [<- hU_card, <- hUFX, hFX_eq]; omega
     exact_mod_cast this
   linarith
lemma near_kernel_linear_bound {N c : ℕ} (hN : 400 <= N) (hc : c ∈ Icc 1 N) {F : Finset (Finset ℕ)} (hF : IsWellInter N F) (hnear : ∀ B ∈ F, c ∉ B -> 39 * N <= 40 * B.card) : (F.card : ℝ) <= (((N - 1) * (N - 2) / 2 : ℕ) : ℝ) + 46 * (N : ℝ) + 3 := by
 by_cases hI : ∃ B ∈ F, c ∉ B /\ ∃ l r, B = Icc l r
 . obtain ⟨B0, hB0F, hcnotB0, l0, r0, hB0eq⟩ := hI
   have hB0sz := hnear B0 hB0F hcnotB0;have hB0ne : B0.Nonempty := card_pos.mp (by omega);have hl0r0 : l0 <= r0 := by rw [hB0eq] at hB0ne; obtain ⟨w, hw⟩ := hB0ne; exact le_trans (mem_Icc.mp hw).1 (mem_Icc.mp hw).2
   have hl0_1 : 1 <= l0 := (mem_Icc.mp (hF.1 B0 hB0F (hB0eq.symm ▸ mem_Icc.mpr ⟨le_rfl, hl0r0⟩))).1;have hr0_N : r0 <= N := (mem_Icc.mp (hF.1 B0 hB0F (hB0eq.symm ▸ mem_Icc.mpr ⟨hl0r0, le_rfl⟩))).2;have hB0card : B0.card = r0 + 1 - l0 := by rw [hB0eq, Nat.card_Icc]
   have hside : c < l0 \/ r0 < c := by
     by_contra h; push Not at h;exact hcnotB0 (hB0eq.symm ▸ mem_Icc.mpr ⟨h.1, h.2⟩)
   rcases hside with hcl | hrc
   . exact near_kernel_linear_bound_left hN hc hF hnear (fun _ => by omega)
   ·
     obtain ⟨hFr, hcard_eq⟩ := reflectFamily_wellInter hF
     let c' := N + 1 - c
     have hcI := mem_Icc.mp hc;have hc'I : c' ∈ Icc 1 N := mem_Icc.mpr ⟨by omega, by omega⟩
     have hnear' : ∀ B' ∈ F.image (reflectSet N), c' ∉ B' -> 39 * N <= 40 * B'.card := by
       intro B' hB' hc'not;obtain ⟨B, hBF, rfl⟩ := mem_image.mp hB';have hcnotB : c ∉ B := fun hcB => hc'not (mem_image.mpr ⟨c, hcB, rfl⟩)
       have hcardB : (reflectSet N B).card = B.card := card_image_of_injOn (fun x hx y hy hxy => by
           have hxI := mem_Icc.mp (hF.1 B hBF (mem_coe.mp hx));have hyI := mem_Icc.mp (hF.1 B hBF (mem_coe.mp hy))
           omega)
       rw [hcardB]; exact hnear B hBF hcnotB
     have hbd := near_kernel_linear_bound_left hN hc'I hFr hnear' (fun _ => by omega);rwa [hcard_eq] at hbd
 . exact near_kernel_linear_bound_left hN hc hF hnear (fun h => absurd h hI)
lemma szabo_delta_extract {N c : ℕ} (hN : 1 <= N) (hc : c ∈ Icc 1 N) {F Sfam : Finset (Finset ℕ)} (hF : IsWellInter N F) (hSsub : Sfam ⊆ F) (hSfam : ∀ S ∈ Sfam, c ∈ S /\ ¬ APSet S) {P : Finset ℕ} (hPsub : P ⊆ Icc 1 N) (hcP : c ∉ P) (hmeetP : ∀ S ∈ Sfam, (S ∩ P).Nonempty) (score : ℕ × ℕ -> ℕ) : ∃ (H : Finset (Finset ℕ)) (pH xH : Finset ℕ -> ℕ), H ⊆ Sfam /\ (∀ S ∈ H, pH S ∈ S ∩ P /\ xH S ∈ S /\ IsDeltaTriplet F S c (pH S) (xH S) /\ ¬ (∀ w, min c (min (pH S) (xH S)) <= w -> w <= max c (max (pH S) (xH S)) -> w % Nat.gcd (distNat c (pH S)) (distNat c (xH S)) =
           c % Nat.gcd (distNat c (pH S)) (distNat c (xH S)) -> w ∈ S) /\
       ∀ p ∈ S ∩ P, ∀ x ∈ S, score (p, x) < score (pH S, xH S) -> ¬ IsDeltaTriplet Sfam S c p x) /\
     (((Sfam \ H).card : ℝ) <= 5 * (N : ℝ) * (2 + Real.log N) + 141 * (P.card : ℝ) * Real.sqrt N) := by
 classical
 obtain ⟨K, hKsub, hKdt, hSK_bd⟩ := szabo_lemma_3_1 hN hc (isWellInter_subset hF hSsub) hSfam hPsub hcP hmeetP
 have hpick : ∀ S : {S // S ∈ K}, ∃ q : ℕ × ℕ, q.1 ∈ S.1 ∩ P /\ q.2 ∈ S.1 /\ IsDeltaTriplet Sfam S.1 c q.1 q.2 /\ ∀ p ∈ S.1 ∩ P, ∀ x ∈ S.1, score (p, x) < score q -> ¬ IsDeltaTriplet Sfam S.1 c p x := by
   rintro ⟨S, hS⟩
   let Cands := ((S ∩ P) ×ˢ S).filter (fun q => IsDeltaTriplet Sfam S c q.1 q.2)
   have hne : Cands.Nonempty := by
     obtain ⟨p, hp, x, hx, hdt⟩ := hKdt S hS;exact ⟨(p, x), mem_filter.mpr ⟨mem_product.mpr ⟨hp, hx⟩, hdt⟩⟩
   obtain ⟨q, hq, hqmin⟩ := exists_min_image Cands score hne;obtain ⟨hqP, hqdt⟩ := mem_filter.mp hq;obtain ⟨h1, h2⟩ := mem_product.mp hqP
   refine ⟨q, h1, h2, hqdt, fun p hp x hx hlt hdt => ?_⟩
   have := hqmin (p, x) (mem_filter.mpr ⟨mem_product.mpr ⟨hp, hx⟩, hdt⟩);omega
 choose qK hqK using hpick
 let pH : Finset ℕ -> ℕ := fun S => if h : S ∈ K then (qK ⟨S, h⟩).1 else 0
 let xH : Finset ℕ -> ℕ := fun S => if h : S ∈ K then (qK ⟨S, h⟩).2 else 0
 let fillPred : Finset ℕ -> Prop := fun S =>
   ∀ w, min c (min (pH S) (xH S)) <= w -> w <= max c (max (pH S) (xH S)) -> w % Nat.gcd (distNat c (pH S)) (distNat c (xH S)) = c % Nat.gcd (distNat c (pH S)) (distNat c (xH S)) -> w ∈ S
 let Kstar := K.filter fillPred
 let H := K.filter (fun S => ¬ fillPred S)
 have hHsub : H ⊆ Sfam := (filter_subset _ _).trans hKsub
 have hKstar_bd : (Kstar.card : ℝ) <= (N : ℝ) * (2 + Real.log N) := by
   refine szabo_lemma_3_2 hN hc (fun S hS => hF.1 S (hSsub (hKsub (mem_filter.mp hS).1))) pH xH ?_ ?_
   . intro S hS
     have hSK := (mem_filter.mp hS).1;have hdt := (hqK ⟨S, hSK⟩).2.2.1;have hp : pH S = (qK ⟨S, hSK⟩).1 := dif_pos hSK;have hx : xH S = (qK ⟨S, hSK⟩).2 := dif_pos hSK;rw [hp, hx]
     refine ⟨hdt.1, hdt.2.1, hdt.2.2.1, hdt.2.2.2.1, hdt.2.2.2.2.1, hdt.2.2.2.2.2.1, fun T hT hTS => ?_⟩
     exact hdt.2.2.2.2.2.2 T (hKsub (mem_filter.mp hT).1) hTS
   . intro S hS; exact (mem_filter.mp hS).2
 refine ⟨H, pH, xH, hHsub, ?_, ?_⟩
 . intro S hS
   obtain ⟨hSK, hnofill⟩ := mem_filter.mp hS;have hp : pH S = (qK ⟨S, hSK⟩).1 := dif_pos hSK;have hx : xH S = (qK ⟨S, hSK⟩).2 := dif_pos hSK;obtain ⟨h1, h2, hdtS, hmin⟩ := hqK ⟨S, hSK⟩
   have hdtF : IsDeltaTriplet F S c (pH S) (xH S) := by
     by_contra hnot;have hnu := nu_triplet_fill hF (hSsub (hKsub hSK)) hdtS.1 (hp ▸ hdtS.2.1) (hx ▸ hdtS.2.2.1) (hp ▸ hdtS.2.2.2.1) (hx ▸ hdtS.2.2.2.2.1) (hp ▸ hx ▸ hdtS.2.2.2.2.2.1) hnot;exact hnofill hnu.2.2.2
   refine ⟨hp ▸ h1, hx ▸ h2, hdtF, hnofill, fun p hp' x hx' hlt => hmin p hp' x hx' ?_⟩
   have hqeq : (pH S, xH S) = qK ⟨S, hSK⟩ := Prod.ext hp hx;rwa [<- hqeq]
 . have hcov : Sfam \ H ⊆ (Sfam \ K) ∪ Kstar := by
     intro S hS;obtain ⟨hSF, hnotH⟩ := Finset.mem_sdiff.mp hS
     by_cases hSK : S ∈ K
     . refine mem_union_right _ (mem_filter.mpr ⟨hSK, ?_⟩)
       by_contra hnf; exact hnotH (mem_filter.mpr ⟨hSK, hnf⟩)
     . exact mem_union_left _ (Finset.mem_sdiff.mpr ⟨hSF, hSK⟩)
   have hcard := le_trans (card_le_card hcov) (card_union_le _ _);have hcardR : ((Sfam \ H).card : ℝ) <= ((Sfam \ K).card : ℝ) + (Kstar.card : ℝ) := by exact_mod_cast hcard
   have hN0 : (0 : ℝ) <= (N : ℝ) := Nat.cast_nonneg N;linarith
lemma szabo_cor_3_3 {_N c d a1 a2 b1 b2 : ℕ} (hd1 : 1 <= d) {E H : Finset (Finset ℕ)} (hE : ∀ S ∈ E, c ∈ S /\ (∀ x ∈ S, x % d = c % d) /\ (∀ x ∈ S, ∀ y ∈ S, ∀ z, min x y <= z -> z <= max x y -> z % d = c % d -> z ∈ S) /\ (∃ hne : S.Nonempty, S.min' hne ∈ Icc a1 a2 /\ S.max' hne ∈ Icc b1 b2)) (pH xH : Finset ℕ -> ℕ) (hH : ∀ S ∈ H, xH S ∈ Icc a1 a2 /\ pH S ∈ Icc b1 b2 /\ xH S % d = c % d /\ pH S % d = c % d /\ (∀ T ∈ E, ¬ (xH S ∈ T /\ pH S ∈ T)) /\ (∀ T ∈ H, T ≠ S -> ¬ (xH S ∈ T /\ pH S ∈ T)) /\ xH S ∈ S /\ pH S ∈ S) : (E.card : ℝ) + (H.card : ℝ) <=
     (((Icc a1 a2).card : ℝ) / (d : ℝ) + 1) * (((Icc b1 b2).card : ℝ) / (d : ℝ) + 1) := by
 classical
 let A := (Icc a1 a2).filter (fun x => x % d = c % d)
 let B := (Icc b1 b2).filter (fun x => x % d = c % d)
 let fE : Finset ℕ -> ℕ × ℕ := fun S => if h : S.Nonempty then (S.min' h, S.max' h) else (0, 0)
 let fH : Finset ℕ -> ℕ × ℕ := fun S => (xH S, pH S)
 let ImE := E.image fE
 let ImH := H.image fH
 have hImE_sub : ImE ⊆ A ×ˢ B := by
   intro q hq;obtain ⟨S, hSE, rfl⟩ := mem_image.mp hq;obtain ⟨hcS, hmod, -, hne, hmin, hmax⟩ := hE S hSE;dsimp only [fE]; rw [dif_pos hne];exact mem_product.mpr ⟨mem_filter.mpr ⟨hmin, hmod _ (min'_mem S hne)⟩, mem_filter.mpr ⟨hmax, hmod _ (max'_mem S hne)⟩⟩
 have hImH_sub : ImH ⊆ A ×ˢ B := by
   intro q hq;obtain ⟨S, hSH, rfl⟩ := mem_image.mp hq;obtain ⟨hxI, hpI, hxm, hpm, -⟩ := hH S hSH;exact mem_product.mpr ⟨mem_filter.mpr ⟨hxI, hxm⟩, mem_filter.mpr ⟨hpI, hpm⟩⟩
 have hdisj : Disjoint ImE ImH := by
   rw [Finset.disjoint_left]; intro q h1 h2;obtain ⟨E0, hE0, rfl⟩ := mem_image.mp h1;obtain ⟨S, hSH, heq⟩ := mem_image.mp h2;obtain ⟨-, -, -, hne, -, -⟩ := hE E0 hE0;dsimp only [fE, fH] at heq; rw [dif_pos hne] at heq;have hx_eq : xH S = E0.min' hne := congrArg Prod.fst heq;have hp_eq : pH S = E0.max' hne := congrArg Prod.snd heq;exact (hH S hSH).2.2.2.2.1 E0 hE0 ⟨hx_eq ▸ min'_mem E0 hne, hp_eq ▸ max'_mem E0 hne⟩
 have hE_inj : Set.InjOn fE (E : Set (Finset ℕ)) := by
   intro S1 hS1 S2 hS2 heq;have h1 := hE S1 (mem_coe.mp hS1);have h2 := hE S2 (mem_coe.mp hS2);obtain ⟨hne1, -, -⟩ := h1.2.2.2;obtain ⟨hne2, -, -⟩ := h2.2.2.2;dsimp only [fE] at heq; rw [dif_pos hne1, dif_pos hne2] at heq;have hmin_eq : S1.min' hne1 = S2.min' hne2 := congrArg Prod.fst heq;have hmax_eq : S1.max' hne1 = S2.max' hne2 := congrArg Prod.snd heq
   ext x; constructor <;> intro hx
   . have hlo := min'_le S1 x hx; have hhi := le_max' S1 x hx
     rw [hmin_eq] at hlo; rw [hmax_eq] at hhi;exact h2.2.2.1 _ (min'_mem S2 hne2) _ (max'_mem S2 hne2) x (by omega) (by omega) (h1.2.1 x hx)
   . have hlo := min'_le S2 x hx; have hhi := le_max' S2 x hx
     rw [<- hmin_eq] at hlo; rw [<- hmax_eq] at hhi;exact h1.2.2.1 _ (min'_mem S1 hne1) _ (max'_mem S1 hne1) x (by omega) (by omega) (h2.2.1 x hx)
 have hH_inj : Set.InjOn fH (H : Set (Finset ℕ)) := by
   intro S1 hS1 S2 hS2 heq;by_contra hne;have h1 := hH S1 (mem_coe.mp hS1);have h2 := hH S2 (mem_coe.mp hS2);have hx_eq : xH S1 = xH S2 := congrArg Prod.fst heq;have hp_eq : pH S1 = pH S2 := congrArg Prod.snd heq;exact h1.2.2.2.2.2.1 S2 (mem_coe.mp hS2) (Ne.symm hne) ⟨hx_eq ▸ h2.2.2.2.2.2.2.1, hp_eq ▸ h2.2.2.2.2.2.2.2⟩
 have htot : E.card + H.card <= A.card * B.card := by
   have h1 := card_le_card (Finset.union_subset hImE_sub hImH_sub);rw [card_union_of_disjoint hdisj, card_image_of_injOn hE_inj, card_image_of_injOn hH_inj, card_product] at h1;exact h1
 have hcls : ∀ u v : ℕ, (((Icc u v).filter (fun x => x % d = c % d)).card : ℝ) <= ((Icc u v).card : ℝ) / (d : ℝ) + 1 := by
   intro u v
   by_cases huv : v < u
   . have hE : Icc u v = ∅ := Finset.Icc_eq_empty (by omega)
     rw [hE]; simp
   . push Not at huv
     have hle : ((Icc u v).filter (fun x => x % d = c % d)).card <= (v - u) / d + 1 := by
       rw [<- card_range ((v - u) / d + 1)]
       refine card_le_card_of_injOn (fun x => (x - u) / d) ?_ ?_
       . intro x hx
         have hxI := mem_Icc.mp (mem_filter.mp (mem_coe.mp hx)).1;exact mem_coe.mpr (mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (by omega))))
       . intro x1 hx1 x2 hx2 heq; dsimp only at heq
         have h1 := mem_filter.mp (mem_coe.mp hx1);have h2 := mem_filter.mp (mem_coe.mp hx2);have hx1I := mem_Icc.mp h1.1; have hx2I := mem_Icc.mp h2.1;have hmod12 : x1 % d = x2 % d := h1.2.trans h2.2.symm;have h1q := Nat.div_add_mod (x1 - u) d;have h2q := Nat.div_add_mod (x2 - u) d
         have hmr : (x1 - u) % d = (x2 - u) % d := by
           rcases le_total x1 x2 with hle | hle
           . have hdvd : d ∣ x2 - x1 := (Nat.modEq_iff_dvd' hle).mp hmod12
             have hsub : x2 - u = (x1 - u) + (x2 - x1) := by omega
             obtain ⟨t, ht⟩ := hdvd; rw [hsub, ht, Nat.add_mul_mod_self_left]
           . have hdvd : d ∣ x1 - x2 := (Nat.modEq_iff_dvd' hle).mp hmod12.symm
             have hsub : x1 - u = (x2 - u) + (x1 - x2) := by omega
             obtain ⟨t, ht⟩ := hdvd; rw [hsub, ht, Nat.add_mul_mod_self_left]
         rw [heq] at h1q; omega
     have hleR : (((Icc u v).filter (fun x => x % d = c % d)).card : ℝ) <= (((v - u) / d : ℕ) : ℝ) + 1 := by exact_mod_cast hle
     have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
     have hdiv : (((v - u) / d : ℕ) : ℝ) <= ((Icc u v).card : ℝ) / (d : ℝ) := by
       rw [le_div_iff₀ hdpos, Nat.card_Icc];exact_mod_cast le_trans (Nat.div_mul_le_self (v - u) d) (by omega)
     linarith
 have htotR : (E.card : ℝ) + (H.card : ℝ) <= (A.card : ℝ) * (B.card : ℝ) := by exact_mod_cast htot
 refine le_trans htotR (mul_le_mul (hcls a1 a2) (hcls b1 b2) (Nat.cast_nonneg _) (by positivity))
lemma card_AP_step_ge_two {N : ℕ} (hN : 2 <= N) {F FAP : Finset (Finset ℕ)} (hF : IsWellInter N F) (hFAP_sub : FAP ⊆ F) (hFAP : ∀ S ∈ FAP, 3 <= S.card /\ APSet S /\ ¬ (∃ l r, S = Icc l r)) : (FAP.card : ℝ) <= (25 / 144 : ℝ) * (N : ℝ) ^ 2 + (N : ℝ) * (1 + Real.log N) + (N : ℝ) := by
 classical
 have hstep_ex : ∀ S : {S // S ∈ FAP}, ∃ d, 2 <= d /\ d <= N /\ (∀ x ∈ S.1, ∀ y ∈ S.1, x % d = y % d /\ (∀ z, min x y <= z -> z <= max x y -> z % d = x % d -> z ∈ S.1)) := by
   rintro ⟨S, hS⟩;obtain ⟨hS3, hAP, hnotI⟩ := hFAP S hS;obtain ⟨d, hd1, hab, -, hmem, hcard_eq⟩ := apSet_canonical hAP (by omega)
   set a := S.min' (card_pos.mp (by omega))
   set b := S.max' (card_pos.mp (by omega))
   have hd2 : 2 <= d := by
     by_contra hlt; have hd_eq : d = 1 := by omega
     apply hnotI; refine ⟨a, b, ?_⟩
     ext x; rw [hmem x, mem_Icc, hd_eq]; simp only [Nat.mod_one, and_true]
   have ha1 : 1 <= a := (mem_Icc.mp (hF.1 S (hFAP_sub hS) (min'_mem _ _))).1;have hbN : b <= N := (mem_Icc.mp (hF.1 S (hFAP_sub hS) (max'_mem _ _))).2;have hdN : d <= N := by have : 1 * d <= (S.card - 1) * d := Nat.mul_le_mul_right d (by omega); omega
   refine ⟨d, hd2, hdN, fun x hx y hy => ?_⟩
   have hxm := (hmem x).mp hx; have hym := (hmem y).mp hy;exact ⟨hxm.2.2.trans hym.2.2.symm, fun z hz1 hz2 hzm => (hmem z).mpr ⟨by omega, by omega, hzm.trans hxm.2.2⟩⟩
 choose step hstep using hstep_ex
 let Bd : ℕ -> Finset (Finset ℕ) := fun d => (FAP.attach.filter (fun S => step S = d)).image Subtype.val
 have hcov : FAP ⊆ (Icc 2 N).biUnion Bd := by
   intro S hS;exact mem_biUnion.mpr ⟨step ⟨S, hS⟩, mem_Icc.mpr ⟨(hstep ⟨S, hS⟩).1, (hstep ⟨S, hS⟩).2.1⟩, mem_image.mpr ⟨⟨S, hS⟩, mem_filter.mpr ⟨mem_attach _ _, rfl⟩, rfl⟩⟩
 have hle : (FAP.card : ℝ) <= ∑ d ∈ Icc 2 N, ((Bd d).card : ℝ) := by exact_mod_cast le_trans (card_le_card hcov) card_biUnion_le
 have hterm : ∀ d ∈ Icc 2 N, ((Bd d).card : ℝ) <= ((N : ℝ) / (2 * (d : ℝ)) + 1) ^ 2 := by
   intro d hd;have hd1 : 1 <= d := by have := (mem_Icc.mp hd).1; omega
   refine card_AP_fixed_step hd1 (isWellInter_subset hF (fun S hS => by
     obtain ⟨S', -, rfl⟩ := mem_image.mp hS; exact hFAP_sub S'.2)) (fun S hS => ?_)
   obtain ⟨S', hS'f, rfl⟩ := mem_image.mp hS;have hsd := (mem_filter.mp hS'f).2;have hsp := (hstep S').2.2; rw [hsd] at hsp;exact ⟨by have := (hFAP S'.1 S'.2).1; omega, (hFAP S'.1 S'.2).2.1, hsp⟩
 refine le_trans hle (le_trans (sum_le_sum hterm) ?_)
 have hexp : ∑ d ∈ Icc 2 N, ((N : ℝ) / (2 * (d : ℝ)) + 1) ^ 2 = ((N : ℝ) ^ 2 / 4) * (∑ d ∈ Icc 2 N, 1 / (d : ℝ) ^ 2) + (N : ℝ) * (∑ d ∈ Icc 2 N, 1 / (d : ℝ)) + (∑ _d ∈ Icc 2 N, (1 : ℝ)) := by
   rw [mul_sum, mul_sum, <- sum_add_distrib, <- sum_add_distrib];apply sum_congr rfl; intro d _; ring
 rw [hexp];have h1 : ∑ d ∈ Icc 2 N, (1 : ℝ) / (d : ℝ) ^ 2 <= 25 / 36 := sum_inv_sq_from_two N;have h2 : ∑ d ∈ Icc 2 N, (1 : ℝ) / (d : ℝ) <= 1 + Real.log N := le_trans (sum_le_sum_of_subset_of_nonneg (fun d hd => mem_Icc.mpr ⟨by have := (mem_Icc.mp hd).1; omega, (mem_Icc.mp hd).2⟩) (fun _ _ _ => by positivity)) (harmonic_le_one_add_log N (by omega));have h3 : ∑ _d ∈ Icc 2 N, (1 : ℝ) <= (N : ℝ) := by rw [sum_const, nsmul_eq_mul, mul_one, Nat.card_Icc]; exact_mod_cast (by omega : N + 1 - 2 <= N)
 have hN2 : 0 <= (N : ℝ) ^ 2 / 4 := by positivity
 have hN0 : 0 <= (N : ℝ) := Nat.cast_nonneg N;nlinarith
lemma missing_pair_surplus_bound {N c : ℕ} (hN : 1000 <= N) (hc : c ∈ Icc 1 N) {F E Sfam : Finset (Finset ℕ)} (hF : IsWellInter N F) (hE_sub : E ⊆ F) (hS_sub : Sfam ⊆ F) (hE : ∀ S ∈ E, 3 <= S.card /\ c ∈ S /\ APSet S) (hSfam : ∀ S ∈ Sfam, c ∈ S /\ ¬ APSet S) {B0 : Finset ℕ} (hB0 : B0 ∈ F) (hcB0 : c ∉ B0) (hB0_sz : 40 * B0.card < 39 * N) : (E.card : ℝ) + (Sfam.card : ℝ) <= (N : ℝ) ^ 2 / 2 - (N : ℝ) ^ 2 / 400000 + 141 * (N : ℝ) * Real.sqrt N + 60 * (N : ℝ) * (2 + Real.log N) := by
 classical
 let U := ((Icc 1 N).erase c).powersetCard 2
 have hU_le : (U.card : ℝ) <= (N : ℝ) ^ 2 / 2 := by
   have h1 : U.card = (N - 1) * (N - 2) / 2 := by
     dsimp only [U];rw [card_powersetCard, card_erase_of_mem hc, Nat.card_Icc, Nat.add_sub_cancel, Nat.choose_two_right];have : N - 1 - 1 = N - 2 := by omega
     rw [this]
   have h2 : 2 * U.card <= N * N := by rw [h1]; exact le_trans (Nat.mul_div_le _ 2) (Nat.mul_le_mul (Nat.sub_le N 1) (Nat.sub_le N 2))
   have h2R : 2 * (U.card : ℝ) <= (N : ℝ) * (N : ℝ) := by exact_mod_cast h2
   linarith [show (N : ℝ) * (N : ℝ) = (N : ℝ) ^ 2 by ring]
 let M0 := ((Icc 1 N).erase c) \ B0
 let U0 := M0.powersetCard 2
 have hU0_sub : U0 ⊆ U := powersetCard_mono Finset.sdiff_subset
 have hU0_lb : (N : ℝ) ^ 2 / 4000 <= (U0.card : ℝ) := by
   have hM0_card : N <= 40 * M0.card + 80 := by
     have h1 : ((Icc 1 N).erase c).card <= M0.card + B0.card := by
       have := card_le_card (show (Icc 1 N).erase c ⊆ M0 ∪ B0 from
         fun x hx => by by_cases h : x ∈ B0; · exact mem_union_right _ h
                        . exact mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx, h⟩))
       exact le_trans this (card_union_le _ _)
     rw [card_erase_of_mem hc, Nat.card_Icc, Nat.add_sub_cancel] at h1;omega
   have hU0_eq : U0.card = M0.card * (M0.card - 1) / 2 := by dsimp only [U0]; rw [card_powersetCard, Nat.choose_two_right]
   have hM0_ge20 : 20 <= M0.card := by omega
   have hdiv2 : 2 ∣ M0.card * (M0.card - 1) := by
     rcases Nat.even_or_odd M0.card with ⟨k, hk⟩ | ⟨k, hk⟩
     . exact ⟨k * (M0.card - 1), by rw [hk]; ring⟩
     . refine ⟨M0.card * k, ?_⟩
       have h1 : M0.card - 1 = 2 * k := by omega
       rw [h1]; ring
   have hU0_2 : 2 * U0.card = M0.card * (M0.card - 1) := by rw [hU0_eq, Nat.mul_div_cancel' hdiv2]
   have hU0_2R : 2 * (U0.card : ℝ) = (M0.card : ℝ) * ((M0.card : ℝ) - 1) := by
     have h2 : ((2 * U0.card : ℕ) : ℝ) = ((M0.card * (M0.card - 1) : ℕ) : ℝ) := by exact_mod_cast hU0_2
     rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (by omega : 1 <= M0.card)] at h2; push_cast at h2; exact h2
   have hM0R : (N : ℝ) <= 40 * (M0.card : ℝ) + 80 := by exact_mod_cast hM0_card
   have hNR : (1000 : ℝ) <= (N : ℝ) := by exact_mod_cast hN
   nlinarith
 obtain ⟨H, pH, xH, hHsub, hHdt, hSH_bd⟩ := szabo_delta_extract (by omega) hc hF hS_sub hSfam (hF.1 B0 hB0) hcB0 (fun S hS => wellInter_meet hF (hS_sub hS) hB0 (fun h => hcB0 (h ▸ (hSfam S hS).1))) (fun _ => 0);obtain ⟨Forb, hForb_sub, hForb_inE, hE_99, -, -⟩ := ap_forb_surplus (by omega) hc hF hE_sub hE
 have hH_le : H.card <= (U \ (Forb ∪ U0)).card := by
   refine card_le_card_of_injOn (fun S => ({pH S, xH S} : Finset ℕ)) ?_ ?_
   . intro S hS
     have hSH := mem_coe.mp hS;obtain ⟨hpP, hxS, hdt, -, -⟩ := hHdt S hSH;have hSF := hS_sub (hHsub hSH)
     have hmemU : ({pH S, xH S} : Finset ℕ) ∈ U := mem_powersetCard.mpr ⟨fun z hz => by
       simp only [mem_insert, mem_singleton] at hz
       rcases hz with rfl | rfl
       . exact Finset.mem_erase.mpr ⟨hdt.2.2.2.1.symm, hF.1 S hSF hdt.2.1⟩
       . exact Finset.mem_erase.mpr ⟨hdt.2.2.2.2.1.symm, hF.1 S hSF hdt.2.2.1⟩,
       card_pair hdt.2.2.2.2.2.1⟩
     refine mem_coe.mpr (Finset.mem_sdiff.mpr ⟨hmemU, fun hmem => ?_⟩)
     rcases mem_union.mp hmem with hF0 | hU0m
     . obtain ⟨E0, hE0, heE0, -⟩ := hForb_inE _ hF0
       have hE0ne : E0 ≠ S := fun h => (hSfam S (hHsub hSH)).2 (h ▸ (hE E0 hE0).2.2)
       exact hdt.2.2.2.2.2.2 E0 (hE_sub hE0) hE0ne ⟨(hE E0 hE0).2.1, heE0 (by simp), heE0 (by simp)⟩
     . have hpM0 : pH S ∈ M0 := (mem_powersetCard.mp hU0m).1 (Finset.mem_insert_self _ _)
       exact (Finset.mem_sdiff.mp hpM0).2 (mem_of_mem_inter_right hpP)
   . intro S hS T hT heq; dsimp only at heq
     by_contra hne;have hdtS := (hHdt S (mem_coe.mp hS)).2.2.1;have hdtT := (hHdt T (mem_coe.mp hT)).2.2.1
     have hsub : ({pH S, xH S} : Finset ℕ) ⊆ T := by
       rw [heq]; intro z hz; simp only [mem_insert, mem_singleton] at hz
       rcases hz with rfl | rfl; exact hdtT.2.1; exact hdtT.2.2.1
     exact hdtS.2.2.2.2.2.2 T (hS_sub (hHsub (mem_coe.mp hT))) (Ne.symm hne) ⟨hdtT.1, hsub (by simp), hsub (by simp)⟩
 have hUFU : (U \ (Forb ∪ U0)).card + (Forb \ U0).card + U0.card = U.card := by
   have h1 : (U \ (Forb ∪ U0)).card + (Forb ∪ U0).card = U.card := card_sdiff_add_card_eq_card (Finset.union_subset hForb_sub hU0_sub);have h2 : (Forb ∪ U0).card = (Forb \ U0).card + U0.card := by rw [<- card_union_of_disjoint Finset.sdiff_disjoint, Finset.sdiff_union_self_eq_union]
   omega
 have hForb_split : Forb.card <= (Forb \ U0).card + U0.card := by
   have h1 := card_sdiff_add_card_inter Forb U0;have h2 : (Forb ∩ U0).card <= U0.card := card_le_card Finset.inter_subset_right;omega
 have hH_R : (H.card : ℝ) + ((Forb \ U0).card : ℝ) + (U0.card : ℝ) <= (U.card : ℝ) := by exact_mod_cast (by omega : H.card + (Forb \ U0).card + U0.card <= U.card)
 have hForb_R : (Forb.card : ℝ) <= ((Forb \ U0).card : ℝ) + (U0.card : ℝ) := by exact_mod_cast hForb_split
 have hS_split : (Sfam.card : ℝ) = (H.card : ℝ) + ((Sfam \ H).card : ℝ) := by exact_mod_cast (by rw [add_comm]; exact (card_sdiff_add_card_eq_card hHsub).symm)
 have hB0_leN : (B0.card : ℝ) <= (N : ℝ) := by
   have := card_le_card (hF.1 B0 hB0); rw [Nat.card_Icc, Nat.add_sub_cancel] at this;exact_mod_cast this
 have hsq_nn : 0 <= Real.sqrt (N : ℝ) := Real.sqrt_nonneg _;have hlog_nn : 0 <= Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 <= N));nlinarith
lemma even_pair_parity_surplus_bound {N c : ℕ} (hN : 1000 <= N) (hc : c ∈ Icc 1 N) {F P E Sfam : Finset (Finset ℕ)} (hF : IsWellInter N F) (hP_sub : P ⊆ F) (hE_sub : E ⊆ F) (hS_sub : Sfam ⊆ F) (hP_ne : P.Nonempty) (hP : ∀ S ∈ P, 3 <= S.card /\ c ∉ S /\ APSet S /\ (∀ x ∈ S, ∀ y ∈ S, x % 2 = y % 2 /\ (∀ z, min x y <= z -> z <= max x y -> z % 2 = x % 2 -> z ∈ S)) /\ (∃ hne : S.Nonempty, S.min' hne < c /\ c < S.max' hne)) (hE : ∀ S ∈ E, 3 <= S.card /\ c ∈ S /\ APSet S) (hSfam : ∀ S ∈ Sfam, c ∈ S /\ ¬ APSet S) : (P.card : ℝ) + (E.card : ℝ) + (Sfam.card : ℝ) <=
     (7 / 16 : ℝ) * (N : ℝ) ^ 2 + 141 * (N : ℝ) * Real.sqrt N + 50 * (N : ℝ) * (2 + Real.log N) + 10 := by
 classical
 obtain ⟨P0, hP0⟩ := hP_ne
 have hP0_par : ∀ p ∈ P0, p % 2 ≠ c % 2 := by
   intro p hp hmod;obtain ⟨-, hcnot, -, hstep2, hne0, hmin_lt, hc_lt_max⟩ := hP P0 hP0;apply hcnot;have hmin_mem := min'_mem P0 hne0;have hmax_mem := max'_mem P0 hne0;have hpm := (hstep2 p hp _ hmin_mem).1;exact (hstep2 _ hmin_mem _ hmax_mem).2 c (by omega) (by omega) (hmod.symm.trans hpm)
 have hP_card : (P.card : ℝ) <= (N : ℝ) ^ 2 / 16 + (N : ℝ) + 1 := by
   have h1 := card_AP_step_endpoints (N := N) (d := 2) (by norm_num) (isWellInter_subset hF hP_sub) (fun S hS => ⟨by have := (hP S hS).1; omega, (hP S hS).2.2.1, (hP S hS).2.2.2.1⟩) (a1 := 1) (a2 := c) (b1 := c) (b2 := N) (fun S hS => by
       obtain ⟨-, -, -, -, hne, h1, h2⟩ := hP S hS;have hmin1 := (mem_Icc.mp (hF.1 S (hP_sub hS) (min'_mem S hne))).1;have hmaxN := (mem_Icc.mp (hF.1 S (hP_sub hS) (max'_mem S hne))).2
       exact ⟨hne, mem_Icc.mpr ⟨hmin1, by omega⟩, mem_Icc.mpr ⟨by omega, hmaxN⟩⟩)
   have hcI := mem_Icc.mp hc;have hc_eq : (c + 1 - 1 : ℕ) = c := by omega
   have hNc_eq : (N + 1 - c : ℕ) = N + 1 - c := rfl;rw [hc_eq] at h1
   have hcast : ((N + 1 - c : ℕ) : ℝ) = (N : ℝ) + 1 - (c : ℝ) := by
     have : c <= N + 1 := by omega
     rw [Nat.cast_sub this]; push_cast; ring
   rw [hcast] at h1;have hsq : 0 <= ((c : ℝ) - ((N : ℝ) + 1) / 2) ^ 2 := sq_nonneg _;have hNR : (1000 : ℝ) <= (N : ℝ) := by exact_mod_cast hN
   nlinarith
 obtain ⟨H, pH, xH, hHsub, hHdt, hSH_bd⟩ := szabo_delta_extract (by omega) hc hF hS_sub hSfam (hF.1 P0 (hP_sub hP0)) (hP P0 hP0).2.1 (fun S hS => wellInter_meet hF (hS_sub hS) (hP_sub hP0) (fun h => (hP P0 hP0).2.1 (h ▸ (hSfam S hS).1))) (fun _ => 0);obtain ⟨Forb, hForb_sub, hForb_inE, -, hE_forb, -⟩ := ap_forb_surplus (by omega) hc hF hE_sub hE
 let U := ((Icc 1 N).erase c).powersetCard 2
 let EvenPts := ((Icc 1 N).erase c).filter (fun x => x % 2 = c % 2)
 let Ueven := EvenPts.powersetCard 2
 have hUeven_sub : Ueven ⊆ U := powersetCard_mono (filter_subset _ _)
 have hForb_disj_even : Disjoint Forb Ueven := by
   rw [Finset.disjoint_left]; intro e heF heE;obtain ⟨E0, hE0, heE0, hpar⟩ := hForb_inE e heF;have hcard2 := (mem_powersetCard.mp heE).2;obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.mp hcard2;have hxE := (mem_filter.mp ((mem_powersetCard.mp heE).1 (Finset.mem_insert_self x {y}))).2;have hyE := (mem_filter.mp ((mem_powersetCard.mp heE).1 (Finset.mem_insert_of_mem (Finset.mem_singleton_self y)))).2
   rcases hpar x (by simp) y (by simp) hxy with hall_even | hnot_even
   ·
     have hE0ne : E0 ≠ P0 := fun h => (hP P0 hP0).2.1 (h ▸ (hE E0 hE0).2.1)
     obtain ⟨w, hw⟩ := wellInter_meet hF (hE_sub hE0) (hP_sub hP0) hE0ne;exact hP0_par w (mem_of_mem_inter_right hw) (hall_even w (mem_of_mem_inter_left hw))
   . rcases hnot_even with h | h; exact h hxE; exact h hyE
 have hH_le : H.card <= (U \ (Forb ∪ Ueven)).card := by
   refine card_le_card_of_injOn (fun S => ({pH S, xH S} : Finset ℕ)) ?_ ?_
   . intro S hS
     have hSH := mem_coe.mp hS;obtain ⟨hpP, -, hdt, -, -⟩ := hHdt S hSH;have hSF := hS_sub (hHsub hSH)
     have hmemU : ({pH S, xH S} : Finset ℕ) ∈ U := mem_powersetCard.mpr ⟨fun z hz => by
       simp only [mem_insert, mem_singleton] at hz
       rcases hz with rfl | rfl
       . exact Finset.mem_erase.mpr ⟨hdt.2.2.2.1.symm, hF.1 S hSF hdt.2.1⟩
       . exact Finset.mem_erase.mpr ⟨hdt.2.2.2.2.1.symm, hF.1 S hSF hdt.2.2.1⟩,
       card_pair hdt.2.2.2.2.2.1⟩
     refine mem_coe.mpr (Finset.mem_sdiff.mpr ⟨hmemU, fun hmem => ?_⟩)
     rcases mem_union.mp hmem with hF0 | hEv
     . obtain ⟨E0, hE0, heE0, -⟩ := hForb_inE _ hF0
       have hE0ne : E0 ≠ S := fun h => (hSfam S (hHsub hSH)).2 (h ▸ (hE E0 hE0).2.2)
       exact hdt.2.2.2.2.2.2 E0 (hE_sub hE0) hE0ne ⟨(hE E0 hE0).2.1, heE0 (by simp), heE0 (by simp)⟩
     . have hpEv := (mem_filter.mp ((mem_powersetCard.mp hEv).1 (Finset.mem_insert_self _ _))).2
       exact hP0_par (pH S) (mem_of_mem_inter_right hpP) hpEv
   . intro S hS T hT heq; dsimp only at heq
     by_contra hne;have hdtS := (hHdt S (mem_coe.mp hS)).2.2.1;have hdtT := (hHdt T (mem_coe.mp hT)).2.2.1
     have hsub : ({pH S, xH S} : Finset ℕ) ⊆ T := by
       rw [heq]; intro z hz; simp only [mem_insert, mem_singleton] at hz
       rcases hz with rfl | rfl; exact hdtT.2.1; exact hdtT.2.2.1
     exact hdtS.2.2.2.2.2.2 T (hS_sub (hHsub (mem_coe.mp hT))) (Ne.symm hne) ⟨hdtT.1, hsub (by simp), hsub (by simp)⟩
 have hUeven_lb : (N : ℝ) ^ 2 / 8 - 2 * (N : ℝ) <= (Ueven.card : ℝ) := by
   have hEv_lb : N <= 2 * EvenPts.card + 4 := by
     have hsub : (range ((N - 1) / 2)).image (fun k => 2 * k + 1 + (1 - c % 2)) ⊆ (Icc 1 N).filter (fun x => x % 2 = c % 2) := by
       intro x hx; obtain ⟨k, hk, rfl⟩ := mem_image.mp hx;have hklt := mem_range.mp hk;exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
     have hinj : Function.Injective (fun k => 2 * k + 1 + (1 - c % 2)) := fun a b h => by dsimp only at h; omega
     have hc1 := card_le_card hsub;rw [card_image_of_injective _ hinj, card_range] at hc1
     have hc2 : ((Icc 1 N).filter (fun x => x % 2 = c % 2)).card <= EvenPts.card + 1 := by
       have hsub2 : (Icc 1 N).filter (fun x => x % 2 = c % 2) ⊆ insert c EvenPts := by
         intro x hx; by_cases hxc : x = c
         . subst hxc; exact Finset.mem_insert_self _ _
         . exact Finset.mem_insert_of_mem (mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hxc, (mem_filter.mp hx).1⟩, (mem_filter.mp hx).2⟩)
       exact le_trans (card_le_card hsub2) (card_insert_le _ _)
     omega
   have hUev_eq : Ueven.card = EvenPts.card * (EvenPts.card - 1) / 2 := by dsimp only [Ueven]; rw [card_powersetCard, Nat.choose_two_right]
   have hdiv2 : 2 ∣ EvenPts.card * (EvenPts.card - 1) := by
     rcases Nat.even_or_odd EvenPts.card with ⟨k, hk⟩ | ⟨k, hk⟩
     . exact ⟨k * (EvenPts.card - 1), by rw [hk]; ring⟩
     . refine ⟨EvenPts.card * k, ?_⟩
       have h1 : EvenPts.card - 1 = 2 * k := by omega
       rw [h1]; ring
   have h2R : 2 * (Ueven.card : ℝ) = (EvenPts.card : ℝ) * ((EvenPts.card : ℝ) - 1) := by
     have h1 : 2 * Ueven.card = EvenPts.card * (EvenPts.card - 1) := by rw [hUev_eq, Nat.mul_div_cancel' hdiv2]
     have h2 : ((2 * Ueven.card : ℕ) : ℝ) = ((EvenPts.card * (EvenPts.card - 1) : ℕ) : ℝ) := by exact_mod_cast h1
     rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (by omega : 1 <= EvenPts.card)] at h2; push_cast at h2; exact h2
   have hEvR : (N : ℝ) <= 2 * (EvenPts.card : ℝ) + 4 := by exact_mod_cast hEv_lb
   have hNR : (1000 : ℝ) <= (N : ℝ) := by exact_mod_cast hN
   nlinarith
 have hU_le : (U.card : ℝ) <= (N : ℝ) ^ 2 / 2 := by
   have h1 : U.card = (N - 1) * (N - 2) / 2 := by
     dsimp only [U];rw [card_powersetCard, card_erase_of_mem hc, Nat.card_Icc, Nat.add_sub_cancel, Nat.choose_two_right];have : N - 1 - 1 = N - 2 := by omega
     rw [this]
   have h2 : 2 * U.card <= N * N := by rw [h1]; exact le_trans (Nat.mul_div_le _ 2) (Nat.mul_le_mul (Nat.sub_le N 1) (Nat.sub_le N 2))
   have h2R : 2 * (U.card : ℝ) <= (N : ℝ) * (N : ℝ) := by exact_mod_cast h2
   linarith [show (N : ℝ) * (N : ℝ) = (N : ℝ) ^ 2 by ring]
 have hsum_nat : H.card + Forb.card + Ueven.card <= U.card := by
   have h1 : (U \ (Forb ∪ Ueven)).card + (Forb ∪ Ueven).card = U.card := card_sdiff_add_card_eq_card (Finset.union_subset hForb_sub hUeven_sub);rw [card_union_of_disjoint hForb_disj_even] at h1; omega
 have hsumR : (H.card : ℝ) + (Forb.card : ℝ) + (Ueven.card : ℝ) <= (U.card : ℝ) := by exact_mod_cast hsum_nat
 have hS_split : (Sfam.card : ℝ) = (H.card : ℝ) + ((Sfam \ H).card : ℝ) := by exact_mod_cast (by rw [add_comm]; exact (card_sdiff_add_card_eq_card hHsub).symm)
 have hP0_leN : (P0.card : ℝ) <= (N : ℝ) := by
   have := card_le_card (hF.1 P0 (hP_sub hP0)); rw [Nat.card_Icc, Nat.add_sub_cancel] at this;exact_mod_cast this
 have hsq_nn : 0 <= Real.sqrt (N : ℝ) := Real.sqrt_nonneg _;have hlog_nn : 0 <= Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 <= N));nlinarith
lemma szabo_theorem_4_2 {N c : ℕ} (hN : 1000 <= N) (hc : c ∈ Icc 1 N) {F P E Sfam : Finset (Finset ℕ)} (hF : IsWellInter N F) (hP_sub : P ⊆ F) (hE_sub : E ⊆ F) (hS_sub : Sfam ⊆ F) (hP : ∀ S ∈ P, 3 <= S.card /\ c ∉ S /\ APSet S /\ ¬ (∃ l r, S = Icc l r)) (hE : ∀ S ∈ E, 3 <= S.card /\ c ∈ S /\ APSet S) (hSfam : ∀ S ∈ Sfam, c ∈ S /\ ¬ APSet S) {P0 : Finset ℕ} {k : ℕ} (hP0 : P0 ∈ P) (hk : 3 <= k) (hP0_step : ∀ x ∈ P0, ∀ y ∈ P0, x % k = y % k /\ (∀ z, min x y <= z -> z <= max x y -> z % k = x % k -> z ∈ P0)) (hP0_jump : ∃ hne : P0.Nonempty, P0.min' hne < c /\ c < P0.max' hne) :
   (P.card : ℝ) + (E.card : ℝ) + (Sfam.card : ℝ) <= (65 / 144 : ℝ) * (N : ℝ) ^ 2 + 141 * (N : ℝ) * Real.sqrt N + 25 * (N : ℝ) * (2 + Real.log N) + 20 := by
 classical
 let E1 := E.filter (fun S => ∃ l r, S = Icc l r)
 let Ege2 := E.filter (fun S => ¬ ∃ l r, S = Icc l r)
 have hE_split : E.card = E1.card + Ege2.card := by
   have hdisj : Disjoint E1 Ege2 := by rw [Finset.disjoint_left]; intro S h1 h2; exact (mem_filter.mp h2).2 (mem_filter.mp h1).2
   have hu : E1 ∪ Ege2 = E := by
     ext S; simp only [E1, Ege2, mem_union, mem_filter]
     constructor
     . rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
     . intro h; by_cases hI : ∃ l r, S = Icc l r; exact Or.inl ⟨h, hI⟩; exact Or.inr ⟨h, hI⟩
   rw [<- card_union_of_disjoint hdisj, hu]
 have hPEge2_bd : (P.card : ℝ) + (Ege2.card : ℝ) <= (25 / 144 : ℝ) * (N : ℝ) ^ 2 + (N : ℝ) * (1 + Real.log N) + (N : ℝ) := by
   have hdisj : Disjoint P Ege2 := by
     rw [Finset.disjoint_left]; intro S h1 h2;exact (hP S h1).2.1 (hE S (mem_filter.mp h2).1).2.1
   have h1 := card_AP_step_ge_two (by omega) hF (Finset.union_subset hP_sub ((filter_subset (fun S => ¬ ∃ l r, S = Icc l r) E).trans hE_sub)) (fun S hS => by
       rcases mem_union.mp hS with h1 | h2
       . exact ⟨(hP S h1).1, (hP S h1).2.2.1, (hP S h1).2.2.2⟩
       . obtain ⟨hSE, hnotI⟩ := mem_filter.mp h2
         exact ⟨(hE S hSE).1, (hE S hSE).2.2, hnotI⟩)
   rw [card_union_of_disjoint hdisj, Nat.cast_add] at h1;exact h1
 obtain ⟨hne0, hmin_lt, hc_lt_max⟩ := hP0_jump
 set r0 := P0.min' hne0 % k
 let Pext := (Icc 1 N).filter (fun x => x % k = r0)
 have hP0_sub_ext : P0 ⊆ Pext := fun x hx =>
   mem_filter.mpr ⟨hF.1 P0 (hP_sub hP0) hx, (hP0_step x hx _ (min'_mem P0 hne0)).1⟩
 have hc_not_ext : c ∉ Pext := by
   intro hcP;have hcm := (mem_filter.mp hcP).2
   have hmem : c ∈ P0 := (hP0_step _ (min'_mem P0 hne0) _ (max'_mem P0 hne0)).2
     c (by omega) (by omega) hcm
   exact (hP P0 hP0).2.1 hmem
 obtain ⟨H, pH, xH, hHsub, hHdt, hSH_bd⟩ := szabo_delta_extract (by omega) hc hF hS_sub hSfam (filter_subset _ _) hc_not_ext (fun S hS => by
     obtain ⟨w, hw⟩ := wellInter_meet hF (hS_sub hS) (hP_sub hP0) (fun h => (hP P0 hP0).2.1 (h ▸ (hSfam S hS).1))
     exact ⟨w, mem_inter.mpr ⟨mem_of_mem_inter_left hw, hP0_sub_ext (mem_of_mem_inter_right hw)⟩⟩)
   (fun _ => 0)
 have hE1_Icc : ∀ E0 ∈ E1, ∃ hne : E0.Nonempty, E0 = Icc (E0.min' hne) (E0.max' hne) /\ E0.min' hne <= c /\ c <= E0.max' hne := by
   intro E0 hE0;obtain ⟨hE0E, l, r, hEq⟩ := mem_filter.mp hE0;have hcE0 := (hE E0 hE0E).2.1;have hne : E0.Nonempty := ⟨c, hcE0⟩;have hlr : l <= r := by rw [hEq, mem_Icc] at hcE0; omega
   have hmin_eq : E0.min' hne = l := le_antisymm (min'_le E0 l (hEq.symm ▸ mem_Icc.mpr ⟨le_rfl, hlr⟩)) (mem_Icc.mp (show E0.min' hne ∈ Icc l r from hEq ▸ min'_mem E0 hne)).1;have hmax_eq : E0.max' hne = r := le_antisymm (mem_Icc.mp (show E0.max' hne ∈ Icc l r from hEq ▸ max'_mem E0 hne)).2 (le_max' E0 r (hEq.symm ▸ mem_Icc.mpr ⟨hlr, le_rfl⟩));exact ⟨hne, by rw [hmin_eq, hmax_eq]; exact hEq, min'_le E0 c hcE0, le_max' E0 c hcE0⟩
 have hloE_ex : ∃ loE hiE, 1 <= loE /\ loE <= c /\ c <= hiE /\ hiE <= N /\ (∀ E0 ∈ E1, E0 ⊆ Icc loE hiE) /\ (loE < c -> ∃ EL ∈ E1, Icc loE c ⊆ EL) /\ (c < hiE -> ∃ ER ∈ E1, Icc c hiE ⊆ ER) := by
   rcases E1.eq_empty_or_nonempty with hE1_e | hE1_ne
   . have hcI := mem_Icc.mp hc
     exact ⟨c, c, hcI.1, le_rfl, le_rfl, hcI.2, fun _ h => absurd h (hE1_e.symm ▸ notMem_empty _), fun h => by omega, fun h => by omega⟩
   . let minOf : Finset ℕ -> ℕ := fun S => if h : S.Nonempty then S.min' h else c
     let maxOf : Finset ℕ -> ℕ := fun S => if h : S.Nonempty then S.max' h else c
     obtain ⟨EL, hEL, hEL_min⟩ := exists_min_image E1 minOf hE1_ne;obtain ⟨ER, hER, hER_max⟩ := exists_max_image E1 maxOf hE1_ne;obtain ⟨hneL, hEL_eq, hL_le, hc_leL⟩ := hE1_Icc EL hEL;obtain ⟨hneR, hER_eq, hR_le, hc_leR⟩ := hE1_Icc ER hER
     refine ⟨EL.min' hneL, ER.max' hneR, (mem_Icc.mp (hF.1 EL (hE_sub (mem_filter.mp hEL).1) (min'_mem EL hneL))).1, hL_le, hc_leR, (mem_Icc.mp (hF.1 ER (hE_sub (mem_filter.mp hER).1) (max'_mem ER hneR))).2, fun E0 hE0 x hx => ?_, fun _ => ⟨EL, hEL, fun x hx => ?_⟩, fun _ => ⟨ER, hER, fun x hx => ?_⟩⟩
     . obtain ⟨hne0, -, -, -⟩ := hE1_Icc E0 hE0
       have h1 : EL.min' hneL <= E0.min' hne0 := by have := hEL_min E0 hE0; dsimp only [minOf] at this; rwa [dif_pos hneL, dif_pos hne0] at this
       have h2 : E0.max' hne0 <= ER.max' hneR := by have := hER_max E0 hE0; dsimp only [maxOf] at this; rwa [dif_pos hne0, dif_pos hneR] at this
       exact mem_Icc.mpr ⟨le_trans h1 (min'_le E0 x hx), le_trans (le_max' E0 x hx) h2⟩
     . rw [hEL_eq, mem_Icc]; have := mem_Icc.mp hx; omega
     . rw [hER_eq, mem_Icc]; have := mem_Icc.mp hx; omega
 obtain ⟨loE, hiE, hlo1, hlo_c, hc_hi, hhiN, hE1_sub, hEL_cov, hER_cov⟩ := hloE_ex
 let X := Icc loE (c - 1)
 let Y := Icc (c + 1) hiE
 let A := X ∪ Y
 let B := ((Icc 1 N).erase c) \ A
 let H_XY := H.filter (fun S => (pH S ∈ X /\ xH S ∈ Y) \/ (pH S ∈ Y /\ xH S ∈ X))
 let H_rem := H.filter (fun S => pH S ∈ B \/ xH S ∈ B)
 have hH_cov : H ⊆ H_XY ∪ H_rem := by
   intro S hS;obtain ⟨-, -, hdt, -, -⟩ := hHdt S hS;have hSF := hS_sub (hHsub hS);have hpU : pH S ∈ (Icc 1 N).erase c := Finset.mem_erase.mpr ⟨hdt.2.2.2.1.symm, hF.1 S hSF hdt.2.1⟩;have hxU : xH S ∈ (Icc 1 N).erase c := Finset.mem_erase.mpr ⟨hdt.2.2.2.2.1.symm, hF.1 S hSF hdt.2.2.1⟩
   by_cases hpB : pH S ∈ B
   . exact mem_union_right _ (mem_filter.mpr ⟨hS, Or.inl hpB⟩)
   by_cases hxB : xH S ∈ B
   . exact mem_union_right _ (mem_filter.mpr ⟨hS, Or.inr hxB⟩)
   have hpA : pH S ∈ A := by by_contra h; exact hpB (Finset.mem_sdiff.mpr ⟨hpU, h⟩)
   have hxA : xH S ∈ A := by by_contra h; exact hxB (Finset.mem_sdiff.mpr ⟨hxU, h⟩)
   rcases mem_union.mp hpA with hpX | hpY <;> rcases mem_union.mp hxA with hxX | hxY
   ·
     exfalso
     have hpI := mem_Icc.mp hpX; have hxI := mem_Icc.mp hxX;obtain ⟨EL, hEL, hELsub⟩ := hEL_cov (by omega);have hELne : EL ≠ S := fun h => (hSfam S (hHsub hS)).2 (h ▸ (hE EL (mem_filter.mp hEL).1).2.2)
     exact hdt.2.2.2.2.2.2 EL (hE_sub (mem_filter.mp hEL).1) hELne ⟨hELsub (mem_Icc.mpr ⟨hlo_c, le_rfl⟩), hELsub (mem_Icc.mpr ⟨hpI.1, by omega⟩), hELsub (mem_Icc.mpr ⟨hxI.1, by omega⟩)⟩
   . exact mem_union_left _ (mem_filter.mpr ⟨hS, Or.inl ⟨hpX, hxY⟩⟩)
   . exact mem_union_left _ (mem_filter.mpr ⟨hS, Or.inr ⟨hpY, hxX⟩⟩)
   ·
     exfalso
     have hpI := mem_Icc.mp hpY; have hxI := mem_Icc.mp hxY;obtain ⟨ER, hER, hERsub⟩ := hER_cov (by omega);have hERne : ER ≠ S := fun h => (hSfam S (hHsub hS)).2 (h ▸ (hE ER (mem_filter.mp hER).1).2.2)
     exact hdt.2.2.2.2.2.2 ER (hE_sub (mem_filter.mp hER).1) hERne ⟨hERsub (mem_Icc.mpr ⟨le_rfl, hc_hi⟩), hERsub (mem_Icc.mpr ⟨by omega, hpI.2⟩), hERsub (mem_Icc.mpr ⟨by omega, hxI.2⟩)⟩
 have hE1_HXY : (E1.card : ℝ) + (H_XY.card : ℝ) <= (A.card : ℝ) ^ 2 / 4 + 2 * (N : ℝ) + 1 := by
   let X' := Icc loE c
   let Y' := Icc c hiE
   let f1 : Finset ℕ -> ℕ × ℕ := fun E0 => if h : E0.Nonempty then (E0.min' h, E0.max' h) else (0, 0)
   let f2 : Finset ℕ -> ℕ × ℕ := fun S => (min (pH S) (xH S), max (pH S) (xH S))
   have hIm1 : E1.image f1 ⊆ X' ×ˢ Y' := by
     intro q hq; obtain ⟨E0, hE0, rfl⟩ := mem_image.mp hq;obtain ⟨hne, -, hmin_c, hc_max⟩ := hE1_Icc E0 hE0;have hmin_lo := (mem_Icc.mp (hE1_sub E0 hE0 (min'_mem E0 hne))).1;have hmax_hi := (mem_Icc.mp (hE1_sub E0 hE0 (max'_mem E0 hne))).2;dsimp only [f1]; rw [dif_pos hne];exact mem_product.mpr ⟨mem_Icc.mpr ⟨hmin_lo, hmin_c⟩, mem_Icc.mpr ⟨hc_max, hmax_hi⟩⟩
   have hIm2 : H_XY.image f2 ⊆ X' ×ˢ Y' := by
     intro q hq; obtain ⟨S, hS, rfl⟩ := mem_image.mp hq;have hxy := (mem_filter.mp hS).2;dsimp only [f2]
     rcases hxy with ⟨hpX, hxY⟩ | ⟨hpY, hxX⟩
     . have hpI := mem_Icc.mp hpX; have hxI := mem_Icc.mp hxY
       rw [min_eq_left (by omega), max_eq_right (by omega)];exact mem_product.mpr ⟨mem_Icc.mpr ⟨hpI.1, by omega⟩, mem_Icc.mpr ⟨by omega, hxI.2⟩⟩
     . have hpI := mem_Icc.mp hpY; have hxI := mem_Icc.mp hxX
       rw [min_eq_right (by omega), max_eq_left (by omega)];exact mem_product.mpr ⟨mem_Icc.mpr ⟨hxI.1, by omega⟩, mem_Icc.mpr ⟨by omega, hpI.2⟩⟩
   have hdisj : Disjoint (E1.image f1) (H_XY.image f2) := by
     rw [Finset.disjoint_left]; intro q h1 h2;obtain ⟨E0, hE0, rfl⟩ := mem_image.mp h1;obtain ⟨S, hSH, heq⟩ := mem_image.mp h2;obtain ⟨hne, -, -, -⟩ := hE1_Icc E0 hE0;dsimp only [f1, f2] at heq; rw [dif_pos hne] at heq;have hmin_eq : min (pH S) (xH S) = E0.min' hne := congrArg Prod.fst heq;have hmax_eq : max (pH S) (xH S) = E0.max' hne := congrArg Prod.snd heq;have hdt := (hHdt S (mem_filter.mp hSH).1).2.2.1;have hE0ne : E0 ≠ S := fun h => (hSfam S (hHsub (mem_filter.mp hSH).1)).2 (h ▸ (hE E0 (mem_filter.mp hE0).1).2.2)
     have hpE0 : pH S ∈ E0 := by
       rcases le_total (pH S) (xH S) with hle | hle
       . rw [min_eq_left hle] at hmin_eq; exact hmin_eq ▸ min'_mem E0 hne
       . rw [max_eq_left hle] at hmax_eq; exact hmax_eq ▸ max'_mem E0 hne
     have hxE0 : xH S ∈ E0 := by
       rcases le_total (pH S) (xH S) with hle | hle
       . rw [max_eq_right hle] at hmax_eq; exact hmax_eq ▸ max'_mem E0 hne
       . rw [min_eq_right hle] at hmin_eq; exact hmin_eq ▸ min'_mem E0 hne
     exact hdt.2.2.2.2.2.2 E0 (hE_sub (mem_filter.mp hE0).1) hE0ne ⟨(hE E0 (mem_filter.mp hE0).1).2.1, hpE0, hxE0⟩
   have hinj1 : Set.InjOn f1 (E1 : Set (Finset ℕ)) := by
     intro E1a h1 E1b h2 heq;obtain ⟨hne1, heq1, -, -⟩ := hE1_Icc E1a (mem_coe.mp h1);obtain ⟨hne2, heq2, -, -⟩ := hE1_Icc E1b (mem_coe.mp h2);dsimp only [f1] at heq; rw [dif_pos hne1, dif_pos hne2] at heq;have hf : E1a.min' hne1 = E1b.min' hne2 := congrArg Prod.fst heq;have hs : E1a.max' hne1 = E1b.max' hne2 := congrArg Prod.snd heq;rw [heq1, heq2, hf, hs]
   have hinj2 : Set.InjOn f2 (H_XY : Set (Finset ℕ)) := by
     intro S1 h1 S2 h2 heq; dsimp only [f2] at heq;by_contra hne;have hdt1 := (hHdt S1 (mem_filter.mp (mem_coe.mp h1)).1).2.2.1;have hdt2 := (hHdt S2 (mem_filter.mp (mem_coe.mp h2)).1).2.2.1;have hmin_eq : min (pH S1) (xH S1) = min (pH S2) (xH S2) := congrArg Prod.fst heq;have hmax_eq : max (pH S1) (xH S1) = max (pH S2) (xH S2) := congrArg Prod.snd heq
     have hmem2 : ∀ w, w = min (pH S2) (xH S2) \/ w = max (pH S2) (xH S2) -> w ∈ S2 := by
       intro w hw; rcases hw with rfl | rfl
       . rcases min_choice (pH S2) (xH S2) with h | h <;> rw [h]; exact hdt2.2.1; exact hdt2.2.2.1
       . rcases max_choice (pH S2) (xH S2) with h | h <;> rw [h]; exact hdt2.2.1; exact hdt2.2.2.1
     have hp1 : pH S1 ∈ S2 := hmem2 (pH S1) (by
       rcases le_total (pH S1) (xH S1) with hle | hle
       . left; rw [<- hmin_eq, min_eq_left hle]
       . right; rw [<- hmax_eq, max_eq_left hle])
     have hx1 : xH S1 ∈ S2 := hmem2 (xH S1) (by
       rcases le_total (pH S1) (xH S1) with hle | hle
       . right; rw [<- hmax_eq, max_eq_right hle]
       . left; rw [<- hmin_eq, min_eq_right hle])
     exact hdt1.2.2.2.2.2.2 S2 (hS_sub (hHsub (mem_filter.mp (mem_coe.mp h2)).1)) (Ne.symm hne) ⟨hdt2.1, hp1, hx1⟩
   have hcard := card_le_card (Finset.union_subset hIm1 hIm2);rw [card_union_of_disjoint hdisj, card_image_of_injOn hinj1, card_image_of_injOn hinj2, card_product] at hcard;have hX'_card : X'.card = X.card + 1 := by dsimp only [X', X]; rw [Nat.card_Icc, Nat.card_Icc]; omega
   have hY'_card : Y'.card = Y.card + 1 := by dsimp only [Y', Y]; rw [Nat.card_Icc, Nat.card_Icc]; omega
   have hA_card : A.card = X.card + Y.card := by
     refine card_union_of_disjoint ?_
     rw [Finset.disjoint_left]; intro z h1 h2;have := mem_Icc.mp h1; have := mem_Icc.mp h2; omega
   have hA_leN : A.card <= N := by
     have hsubA : A ⊆ Icc 1 N := Finset.union_subset (fun z hz => mem_Icc.mpr ⟨by have := mem_Icc.mp hz; omega,
         by have := mem_Icc.mp hz; have := mem_Icc.mp hc; omega⟩)
       (fun z hz => mem_Icc.mpr ⟨by have := mem_Icc.mp hz; omega,
         by have := mem_Icc.mp hz; omega⟩)
     have := card_le_card hsubA; rwa [Nat.card_Icc, Nat.add_sub_cancel] at this
   have hcardR : (E1.card : ℝ) + (H_XY.card : ℝ) <= ((X.card : ℝ) + 1) * ((Y.card : ℝ) + 1) := by rw [hX'_card, hY'_card] at hcard; exact_mod_cast hcard
   have hAR : (A.card : ℝ) = (X.card : ℝ) + (Y.card : ℝ) := by exact_mod_cast hA_card
   have hANR : (A.card : ℝ) <= (N : ℝ) := by exact_mod_cast hA_leN
   nlinarith [sq_nonneg ((X.card : ℝ) - (Y.card : ℝ))]
 let PA := A ∩ Pext
 let PB := B ∩ Pext
 have hHrem_card : (H_rem.card : ℝ) <= (PA.card : ℝ) * ((B.card : ℝ) - (PB.card : ℝ)) + (PB.card : ℝ) * (A.card : ℝ) + (PB.card : ℝ) * (B.card : ℝ) - (PB.card : ℝ) ^ 2 / 2 := by
   let P1 := (PA ×ˢ (B \ PB)).image (fun q => ({q.1, q.2} : Finset ℕ))
   let P2 := (PB ×ˢ A).image (fun q => ({q.1, q.2} : Finset ℕ))
   let P3 := (PB ×ˢ (B \ PB)).image (fun q => ({q.1, q.2} : Finset ℕ))
   let P4 := PB.powersetCard 2
   have hmaps : ∀ S ∈ H_rem, ({pH S, xH S} : Finset ℕ) ∈ P1 ∪ (P2 ∪ (P3 ∪ P4)) := by
     intro S hS;obtain ⟨hSH, hB_or⟩ := mem_filter.mp hS;obtain ⟨hpP, -, hdt, -, -⟩ := hHdt S hSH;have hSF := hS_sub (hHsub hSH);have hpExt : pH S ∈ Pext := mem_of_mem_inter_right hpP;have hpU : pH S ∈ (Icc 1 N).erase c := Finset.mem_erase.mpr ⟨hdt.2.2.2.1.symm, hF.1 S hSF hdt.2.1⟩;have hxU : xH S ∈ (Icc 1 N).erase c := Finset.mem_erase.mpr ⟨hdt.2.2.2.2.1.symm, hF.1 S hSF hdt.2.2.1⟩
     by_cases hpB : pH S ∈ B
     . have hpPB : pH S ∈ PB := mem_inter.mpr ⟨hpB, hpExt⟩
       by_cases hxA : xH S ∈ A
       . exact mem_union_right _ (mem_union_left _ (mem_image.mpr ⟨(pH S, xH S), mem_product.mpr ⟨hpPB, hxA⟩, rfl⟩))
       . have hxB : xH S ∈ B := Finset.mem_sdiff.mpr ⟨hxU, hxA⟩
         by_cases hxPB : xH S ∈ PB
         . exact mem_union_right _ (mem_union_right _ (mem_union_right _ (mem_powersetCard.mpr ⟨fun z hz => by
               simp only [mem_insert, mem_singleton] at hz
               rcases hz with rfl | rfl; exact hpPB; exact hxPB, card_pair hdt.2.2.2.2.2.1⟩)))
         . exact mem_union_right _ (mem_union_right _ (mem_union_left _ (mem_image.mpr ⟨(pH S, xH S), mem_product.mpr ⟨hpPB, Finset.mem_sdiff.mpr ⟨hxB, hxPB⟩⟩, rfl⟩)))
     . have hpA : pH S ∈ A := by by_contra h; exact hpB (Finset.mem_sdiff.mpr ⟨hpU, h⟩)
       have hpPA : pH S ∈ PA := mem_inter.mpr ⟨hpA, hpExt⟩;have hxB : xH S ∈ B := hB_or.resolve_left hpB
       by_cases hxPB : xH S ∈ PB
       . exact mem_union_right _ (mem_union_left _ (mem_image.mpr ⟨(xH S, pH S), mem_product.mpr ⟨hxPB, hpA⟩, pair_comm _ _⟩))
       . exact mem_union_left _ (mem_image.mpr ⟨(pH S, xH S), mem_product.mpr ⟨hpPA, Finset.mem_sdiff.mpr ⟨hxB, hxPB⟩⟩, rfl⟩)
   have hinj : Set.InjOn (fun S => ({pH S, xH S} : Finset ℕ)) (H_rem : Set (Finset ℕ)) := by
     intro S hS T hT heq; dsimp only at heq;by_contra hne;have hdtS := (hHdt S (mem_filter.mp (mem_coe.mp hS)).1).2.2.1;have hdtT := (hHdt T (mem_filter.mp (mem_coe.mp hT)).1).2.2.1
     have hsub : ({pH S, xH S} : Finset ℕ) ⊆ T := by
       rw [heq]; intro z hz; simp only [mem_insert, mem_singleton] at hz
       rcases hz with rfl | rfl; exact hdtT.2.1; exact hdtT.2.2.1
     exact hdtS.2.2.2.2.2.2 T (hS_sub (hHsub (mem_filter.mp (mem_coe.mp hT)).1)) (Ne.symm hne) ⟨hdtT.1, hsub (by simp), hsub (by simp)⟩
   have hcard := card_le_card_of_injOn _ (fun S hS => mem_coe.mpr (hmaps S (mem_coe.mp hS))) hinj;have hu1 := card_union_le P1 (P2 ∪ (P3 ∪ P4));have hu2 := card_union_le P2 (P3 ∪ P4);have hu3 := card_union_le P3 P4;have hc1 : P1.card <= PA.card * (B \ PB).card := le_trans card_image_le (by rw [card_product]);have hc2 : P2.card <= PB.card * A.card := le_trans card_image_le (by rw [card_product]);have hc3 : P3.card <= PB.card * (B \ PB).card := le_trans card_image_le (by rw [card_product])
   have hc4 : (P4.card : ℝ) <= (PB.card : ℝ) ^ 2 / 2 := by
     have h1 : P4.card = PB.card * (PB.card - 1) / 2 := by dsimp only [P4]; rw [card_powersetCard, Nat.choose_two_right]
     have h2 : 2 * P4.card <= PB.card * PB.card := by rw [h1]; exact le_trans (Nat.mul_div_le _ 2) (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
     have h2R : 2 * (P4.card : ℝ) <= (PB.card : ℝ) * (PB.card : ℝ) := by exact_mod_cast h2
     linarith [show (PB.card : ℝ) * (PB.card : ℝ) = (PB.card : ℝ) ^ 2 by ring]
   have hBsdiff : ((B \ PB).card : ℝ) = (B.card : ℝ) - (PB.card : ℝ) := by
     have hsub : PB ⊆ B := Finset.inter_subset_left;have hadd := card_sdiff_add_card_eq_card hsub;have hR : ((B \ PB).card : ℝ) + (PB.card : ℝ) = (B.card : ℝ) := by exact_mod_cast hadd
     linarith
   have htotR : (H_rem.card : ℝ) <= (PA.card : ℝ) * ((B \ PB).card : ℝ) + (PB.card : ℝ) * (A.card : ℝ) + (PB.card : ℝ) * ((B \ PB).card : ℝ) + (P4.card : ℝ) := by
     have hnat : H_rem.card <= PA.card * (B \ PB).card + PB.card * A.card + PB.card * (B \ PB).card + P4.card := by omega
     exact_mod_cast hnat
   rw [hBsdiff] at htotR; nlinarith
 have hint_ext : ∀ u v : ℕ, (((Icc u v) ∩ Pext).card : ℝ) <= ((Icc u v).card : ℝ) / 3 + 1 := by
   intro u v
   by_cases huv : v < u
   . rw [Finset.Icc_eq_empty (by omega)]; simp
   . push Not at huv
     have hle : ((Icc u v) ∩ Pext).card <= (v - u) / k + 1 := by
       rw [<- card_range ((v - u) / k + 1)]
       refine card_le_card_of_injOn (fun x => (x - u) / k) ?_ ?_
       . intro x hx
         have hxI := mem_Icc.mp (mem_inter.mp (mem_coe.mp hx)).1;exact mem_coe.mpr (mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (by omega))))
       . intro x1 hx1 x2 hx2 heq; dsimp only at heq
         have h1 := mem_inter.mp (mem_coe.mp hx1);have h2 := mem_inter.mp (mem_coe.mp hx2);have hx1I := mem_Icc.mp h1.1; have hx2I := mem_Icc.mp h2.1;have hmod12 : x1 % k = x2 % k := (mem_filter.mp h1.2).2.trans (mem_filter.mp h2.2).2.symm;have h1q := Nat.div_add_mod (x1 - u) k; have h2q := Nat.div_add_mod (x2 - u) k
         have hmr : (x1 - u) % k = (x2 - u) % k := by
           rcases le_total x1 x2 with hle | hle
           . have hdvd : k ∣ x2 - x1 := (Nat.modEq_iff_dvd' hle).mp hmod12
             obtain ⟨t, ht⟩ := hdvd;have : x2 - u = (x1 - u) + k * t := by omega
             rw [this, Nat.add_mul_mod_self_left]
           . have hdvd : k ∣ x1 - x2 := (Nat.modEq_iff_dvd' hle).mp hmod12.symm
             obtain ⟨t, ht⟩ := hdvd;have : x1 - u = (x2 - u) + k * t := by omega
             rw [this, Nat.add_mul_mod_self_left]
         rw [heq] at h1q; omega
     have hleR : (((Icc u v) ∩ Pext).card : ℝ) <= (((v - u) / k : ℕ) : ℝ) + 1 := by exact_mod_cast hle
     have hk3 : (3 : ℝ) <= (k : ℝ) := by exact_mod_cast hk
     have hdiv : (((v - u) / k : ℕ) : ℝ) <= ((Icc u v).card : ℝ) / 3 := by
       rw [le_div_iff₀ (by norm_num), Nat.card_Icc];have h1 : ((v - u) / k) * 3 <= ((v - u) / k) * k := Nat.mul_le_mul_left _ hk;have h2 : ((v - u) / k) * k <= v + 1 - u := le_trans (Nat.div_mul_le_self (v - u) k) (by omega);exact_mod_cast le_trans h1 h2
     linarith
 have hPA_ub : (PA.card : ℝ) <= (A.card : ℝ) / 3 + 2 := by
   have hcov : PA ⊆ (X ∩ Pext) ∪ (Y ∩ Pext) := fun z hz => by
     obtain ⟨hzA, hzP⟩ := mem_inter.mp hz
     rcases mem_union.mp hzA with h1 | h2
     . exact mem_union_left _ (mem_inter.mpr ⟨h1, hzP⟩)
     . exact mem_union_right _ (mem_inter.mpr ⟨h2, hzP⟩)
   have hc := le_trans (card_le_card hcov) (card_union_le _ _);have hcR : (PA.card : ℝ) <= ((X ∩ Pext).card : ℝ) + ((Y ∩ Pext).card : ℝ) := by exact_mod_cast hc
   have hA_eq : (A.card : ℝ) = (X.card : ℝ) + (Y.card : ℝ) := by
     have hdisj : Disjoint X Y := by
       rw [Finset.disjoint_left]; intro z h1 h2;have := mem_Icc.mp h1; have := mem_Icc.mp h2; omega
     exact_mod_cast card_union_of_disjoint hdisj
   linarith [hint_ext loE (c - 1), hint_ext (c + 1) hiE]
 have hPB_ub : (PB.card : ℝ) <= (B.card : ℝ) / 3 + 2 := by
   let U1 := Icc 1 (loE - 1)
   let V1 := Icc (hiE + 1) N
   have hB_eq : B = U1 ∪ V1 := by
     ext z; simp only [B, A, X, Y, U1, V1, Finset.mem_sdiff, Finset.mem_erase, mem_union, mem_Icc]
     omega
   have hdisjUV : Disjoint U1 V1 := by
     rw [Finset.disjoint_left]; intro z h1 h2;have := mem_Icc.mp h1; have := mem_Icc.mp h2; omega
   have hcov : PB ⊆ (U1 ∩ Pext) ∪ (V1 ∩ Pext) := fun z hz => by
     obtain ⟨hzB, hzP⟩ := mem_inter.mp hz;rw [hB_eq] at hzB
     rcases mem_union.mp hzB with h1 | h2
     . exact mem_union_left _ (mem_inter.mpr ⟨h1, hzP⟩)
     . exact mem_union_right _ (mem_inter.mpr ⟨h2, hzP⟩)
   have hc := le_trans (card_le_card hcov) (card_union_le _ _);have hcR : (PB.card : ℝ) <= ((U1 ∩ Pext).card : ℝ) + ((V1 ∩ Pext).card : ℝ) := by exact_mod_cast hc
   have hB_card : (B.card : ℝ) = (U1.card : ℝ) + (V1.card : ℝ) := by rw [hB_eq]; exact_mod_cast card_union_of_disjoint hdisjUV
   linarith [hint_ext 1 (loE - 1), hint_ext (hiE + 1) N]
 have hAB_leN : (A.card : ℝ) + (B.card : ℝ) <= (N : ℝ) := by
   have hdisj : Disjoint A B := Finset.disjoint_sdiff
   have hsub : A ∪ B ⊆ Icc 1 N := Finset.union_subset (Finset.union_subset (fun z hz => mem_Icc.mpr ⟨by have := mem_Icc.mp hz; omega,
         by have := mem_Icc.mp hz; have := mem_Icc.mp hc; omega⟩)
       (fun z hz => mem_Icc.mpr ⟨by have := mem_Icc.mp hz; omega,
         by have := mem_Icc.mp hz; omega⟩))
     (Finset.sdiff_subset.trans (erase_subset _ _))
   have hc := card_le_card hsub;rw [card_union_of_disjoint hdisj, Nat.card_Icc, Nat.add_sub_cancel] at hc;exact_mod_cast hc
 have hPA_leA : (PA.card : ℝ) <= (A.card : ℝ) := by exact_mod_cast card_le_card Finset.inter_subset_left
 have hPB_leB : (PB.card : ℝ) <= (B.card : ℝ) := by exact_mod_cast card_le_card Finset.inter_subset_left
 have hHrem_quad : (H_rem.card : ℝ) <= (5 / 9 : ℝ) * (A.card : ℝ) * (B.card : ℝ) + (5 / 18 : ℝ) * (B.card : ℝ) ^ 2 + 6 * (N : ℝ) + 4 := by
   set a := (A.card : ℝ); set b := (B.card : ℝ)
   set pa := (PA.card : ℝ); set pb := (PB.card : ℝ)
   have hstep1 : pa * (b - pb) <= (a / 3 + 2) * (b - pb) := mul_le_mul_of_nonneg_right hPA_ub (by linarith)
   have hquad_pb : pb * (2 * a / 3 + b) - pb ^ 2 / 2 <= (b / 3 + 2) * (2 * a / 3 + b) - (b / 3 + 2) ^ 2 / 2 + 2 * (b / 3 + 2) := by
     have hfac2 : 0 <= 2 * a / 3 + b - (b / 3 + 2 + pb) / 2 + 2 := by
       have ha0 : 0 <= a := Nat.cast_nonneg _; have hb0 : 0 <= b := Nat.cast_nonneg _;linarith
     have hpb0 : 0 <= pb := Nat.cast_nonneg _;have h1 : 0 <= (b / 3 + 2 - pb) * (2 * a / 3 + b - (b / 3 + 2 + pb) / 2 + 2) := mul_nonneg (by linarith) hfac2;linarith [h1, hpb0, show ((b / 3 + 2) * (2 * a / 3 + b) - (b / 3 + 2) ^ 2 / 2 + 2 * (b / 3 + 2)) - (pb * (2 * a / 3 + b) - pb ^ 2 / 2) = (b / 3 + 2 - pb) * (2 * a / 3 + b - (b / 3 + 2 + pb) / 2 + 2) + 2 * pb by ring]
   have ha0 : 0 <= a := Nat.cast_nonneg _; have hb0 : 0 <= b := Nat.cast_nonneg _;have hpb0 : 0 <= pb := Nat.cast_nonneg _;linarith [hHrem_card, hstep1, hquad_pb, hAB_leN, ha0, hb0, hpb0, show (a / 3 + 2) * (b - pb) + pb * a + pb * b - pb ^ 2 / 2 = (a / 3 + 2) * b + (pb * (2 * a / 3 + b) - pb ^ 2 / 2) - 2 * pb by ring, show (a / 3 + 2) * b + ((b / 3 + 2) * (2 * a / 3 + b) - (b / 3 + 2) ^ 2 / 2 + 2 * (b / 3 + 2)) = (5 / 9 : ℝ) * a * b + (5 / 18 : ℝ) * b ^ 2 + (4 / 3 : ℝ) * a + 4 * b + 2 by ring]
 have hH_le : (H.card : ℝ) <= (H_XY.card : ℝ) + (H_rem.card : ℝ) := by exact_mod_cast le_trans (card_le_card hH_cov) (card_union_le _ _)
 have hS_split : (Sfam.card : ℝ) = (H.card : ℝ) + ((Sfam \ H).card : ℝ) := by exact_mod_cast (by rw [add_comm]; exact (card_sdiff_add_card_eq_card hHsub).symm)
 have hE_R : (E.card : ℝ) = (E1.card : ℝ) + (Ege2.card : ℝ) := by exact_mod_cast hE_split
 have hPext_leN : (Pext.card : ℝ) <= (N : ℝ) := by
   have := card_le_card (filter_subset (fun x => x % k = r0) (Icc 1 N));rw [Nat.card_Icc, Nat.add_sub_cancel] at this; exact_mod_cast this
 have hA0 : 0 <= (A.card : ℝ) := Nat.cast_nonneg _;have hB0 : 0 <= (B.card : ℝ) := Nat.cast_nonneg _;have hsq_nn : 0 <= Real.sqrt (N : ℝ) := Real.sqrt_nonneg _;have hlog_nn : 0 <= Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 <= N))
 have hquad_AB : (A.card : ℝ) ^ 2 / 4 + (5 / 9 : ℝ) * (A.card : ℝ) * (B.card : ℝ) + (5 / 18 : ℝ) * (B.card : ℝ) ^ 2 <= (5 / 18 : ℝ) * (N : ℝ) ^ 2 := by
   have hsum_sq : ((A.card : ℝ) + (B.card : ℝ)) ^ 2 <= (N : ℝ) ^ 2 := pow_le_pow_left₀ (by linarith) hAB_leN 2;have hA2 : 0 <= (A.card : ℝ) ^ 2 := sq_nonneg _;linarith [hsum_sq, hA2, show ((A.card : ℝ) + (B.card : ℝ)) ^ 2 = (A.card : ℝ) ^ 2 + 2 * ((A.card : ℝ) * (B.card : ℝ)) + (B.card : ℝ) ^ 2 by ring]
 have hSH_bd' : ((Sfam \ H).card : ℝ) <= 5 * (N : ℝ) * (2 + Real.log N) + 141 * (N : ℝ) * Real.sqrt N := by
   have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hPext_leN (by norm_num : (0 : ℝ) <= 141)) hsq_nn;linarith [hSH_bd, this]
 linarith [hPEge2_bd, hE1_HXY, hHrem_quad, hH_le, hS_split, hE_R, hquad_AB, hSH_bd', hlog_nn, show (0 : ℝ) <= (N : ℝ) * Real.log N by positivity, show (N : ℝ) * (1 + Real.log N) = (N : ℝ) + (N : ℝ) * Real.log N by ring, show (N : ℝ) * (2 + Real.log N) = 2 * (N : ℝ) + (N : ℝ) * Real.log N by ring]
lemma thm41_algebra {N c q r x s Z : ℝ} (hc : 0 <= c) (hq : 0 <= q) (hr : 0 <= r) (hx : 0 <= x) (_hs0 : 0 <= s) (hsr : s <= r) (hsum : c + q + r + x <= N) (hZ1 : 1 <= Z) (hZ2 : Z <= 165 / 100) : Z * x * (q + c) + r * x + Z * c * (r - s) + s * (q + c + r) - s ^ 2 / 2 <= N ^ 2 / 2 - ((c + q) ^ 2 + x ^ 2) / 200 := by
 set z := r - s
 set c' := c + q
 set X := x + z
 have hz0 : 0 <= z := by linarith
 have hc'0 : 0 <= c' := by linarith
 have hX0 : 0 <= X := by linarith
 have hN_ge : c' + X + s <= N := by linarith
 have hN_sq : (c' + X + s) ^ 2 <= N ^ 2 := pow_le_pow_left₀ (by linarith) hN_ge 2
 have h1 : Z * c * z <= Z * c' * z := by
   have : 0 <= Z * q * z := by positivity
   linarith [show Z * c' * z = Z * c * z + Z * q * z by ring]
 have h2 : x * z <= X ^ 2 / 4 := by
   have : 0 <= (x - z) ^ 2 := sq_nonneg _;linarith [show X ^ 2 - 4 * (x * z) = (x - z) ^ 2 by ring]
 have h3 : x ^ 2 <= X ^ 2 := pow_le_pow_left₀ hx (by linarith) 2;have hsq : 0 <= ((49 / 100 : ℝ) * X - (Z - 1) * (50 / 49) * c') ^ 2 := sq_nonneg _;have hZsq : (Z - 1) ^ 2 <= (65 / 100 : ℝ) ^ 2 := by nlinarith
 have hc'2 : 0 <= c' ^ 2 := sq_nonneg c';have hX2 : 0 <= X ^ 2 := sq_nonneg X
 have hcoeff : ((Z - 1) * (50 / 49 : ℝ)) ^ 2 * c' ^ 2 <= (495 / 1000 : ℝ) * c' ^ 2 := by
   have : ((Z - 1) * (50 / 49 : ℝ)) ^ 2 <= 495 / 1000 := by
     have : ((Z - 1) * (50 / 49 : ℝ)) ^ 2 = (Z - 1) ^ 2 * (2500 / 2401) := by ring
     linarith
   exact mul_le_mul_of_nonneg_right this hc'2
 have hexp1 : ((49 / 100 : ℝ) * X - (Z - 1) * (50 / 49) * c') ^ 2 = (2401 / 10000 : ℝ) * X ^ 2 - (Z - 1) * (c' * X) + ((Z - 1) * (50 / 49 : ℝ)) ^ 2 * c' ^ 2 := by ring
 have hexp2 : (c' + X + s) ^ 2 / 2 - (Z * c' * X + s * (c' + X) + s ^ 2 / 2 + X ^ 2 / 4) = X ^ 2 / 4 + c' ^ 2 / 2 - (Z - 1) * (c' * X) := by ring
 have hmain : Z * x * (q + c) + r * x + Z * c * z + s * (q + c + r) - s ^ 2 / 2 <= Z * c' * X + s * (c' + X) + s ^ 2 / 2 + X ^ 2 / 4 := by linarith [h1, h2, show Z * x * (q + c) + r * x + Z * c' * z + s * (q + c + r) - s ^ 2 / 2 = Z * c' * X + s * (c' + X) + s ^ 2 / 2 + x * z by dsimp only [c', X, z]; ring]
 linarith
lemma card_gcd_shifted_intervals {N c d a1 a2 b1 b2 : ℕ} (hN : 1 <= N) (hc : c ∈ Icc 1 N) (hd1 : 1 <= d) (hdN : d <= N) {H : Finset (Finset ℕ)} (f1 f2 : Finset ℕ -> ℕ) (hinj : Set.InjOn (fun S => (f1 S, f2 S)) (H : Set (Finset ℕ))) (h1_side : (∀ S ∈ H, a1 <= f1 S /\ f1 S <= a2 /\ a2 < c) \/ (∀ S ∈ H, c < a1 /\ a1 <= f1 S /\ f1 S <= a2)) (h2_side : ∀ S ∈ H, c < b1 /\ b1 <= f2 S /\ f2 S <= b2 /\ b2 <= N) (ha_sub : 1 <= a1 /\ a2 <= N) (hgcd : ∀ S ∈ H, Nat.gcd (distNat c (f1 S)) (distNat c (f2 S)) = d) : (H.card : ℝ) <=
     (moebius2Sum N / (d : ℝ) ^ 2) * ((Icc a1 a2).card : ℝ) * ((Icc b1 b2).card : ℝ) + 8 * (N : ℝ) * (1 + Real.log N) / (d : ℝ) + 2 := by
 rcases H.eq_empty_or_nonempty with rfl | ⟨S0, hS0⟩
 . simp
   have hM0 : 0 <= moebius2Sum N := by linarith [(moebius2Sum_bounds hN).1]
   have hlog : 0 <= Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN);positivity
 have h20 := h2_side S0 hS0;have hb12 : b1 <= b2 := le_trans h20.2.1 h20.2.2.1;have hcb1 : c < b1 := h20.1;have hb2N : b2 <= N := h20.2.2.2;have hcI := mem_Icc.mp hc
 rcases h1_side with hleft | hright
 . have h10 := hleft S0 hS0
   have ha12 : a1 <= a2 := le_trans h10.1 h10.2.1;have ha2c : a2 < c := h10.2.2
   have hle : H.card <= ((Icc (c - a2) (c - a1) ×ˢ Icc (b1 - c) (b2 - c)).filter (fun p => Nat.gcd p.1 p.2 = d)).card := by
     refine card_le_card_of_injOn (fun S => (c - f1 S, f2 S - c)) ?_ ?_
     . intro S hS
       have hSm := mem_coe.mp hS;have h1 := hleft S hSm; have h2 := h2_side S hSm
       refine mem_coe.mpr (mem_filter.mpr ⟨mem_product.mpr ⟨mem_Icc.mpr ⟨by dsimp only; omega, by dsimp only; omega⟩, mem_Icc.mpr ⟨by dsimp only; omega, by dsimp only; omega⟩⟩, ?_⟩)
       dsimp only;have hg := hgcd S hSm;rw [distNat_eq_sub' (by omega), distNat_eq_sub (by omega)] at hg; exact hg
     . intro S1 hS1 S2 hS2 heq; dsimp only at heq
       have h11 := hleft S1 (mem_coe.mp hS1); have h12 := hleft S2 (mem_coe.mp hS2);have h21 := h2_side S1 (mem_coe.mp hS1); have h22 := h2_side S2 (mem_coe.mp hS2);have hf1 : c - f1 S1 = c - f1 S2 := congrArg Prod.fst heq;have hf2 : f2 S1 - c = f2 S2 - c := congrArg Prod.snd heq;exact hinj hS1 hS2 (by dsimp only; exact Prod.ext (by omega) (by omega))
   have hbd := card_gcd_rect_one_side (N := N) (d := d) hd1 hdN (a1 := c - a2) (a2 := c - a1) (b1 := b1 - c) (b2 := b2 - c) (by omega) (by have := ha_sub.1; omega) (by omega) (by omega);have hca : (Icc (c - a2) (c - a1)).card = (Icc a1 a2).card := by rw [Nat.card_Icc, Nat.card_Icc]; omega
   have hcb : (Icc (b1 - c) (b2 - c)).card = (Icc b1 b2).card := by rw [Nat.card_Icc, Nat.card_Icc]; omega
   rw [hca, hcb] at hbd;exact le_trans (by exact_mod_cast hle) hbd
 . have h10 := hright S0 hS0
   have ha12 : a1 <= a2 := le_trans h10.2.1 h10.2.2;have hca1 : c < a1 := h10.1
   have hle : H.card <= ((Icc (a1 - c) (a2 - c) ×ˢ Icc (b1 - c) (b2 - c)).filter (fun p => Nat.gcd p.1 p.2 = d)).card := by
     refine card_le_card_of_injOn (fun S => (f1 S - c, f2 S - c)) ?_ ?_
     . intro S hS
       have hSm := mem_coe.mp hS;have h1 := hright S hSm; have h2 := h2_side S hSm
       refine mem_coe.mpr (mem_filter.mpr ⟨mem_product.mpr ⟨mem_Icc.mpr ⟨by dsimp only; omega, by dsimp only; omega⟩, mem_Icc.mpr ⟨by dsimp only; omega, by dsimp only; omega⟩⟩, ?_⟩)
       dsimp only;have hg := hgcd S hSm;rw [distNat_eq_sub (by omega), distNat_eq_sub (by omega)] at hg; exact hg
     . intro S1 hS1 S2 hS2 heq; dsimp only at heq
       have h11 := hright S1 (mem_coe.mp hS1); have h12 := hright S2 (mem_coe.mp hS2);have h21 := h2_side S1 (mem_coe.mp hS1); have h22 := h2_side S2 (mem_coe.mp hS2);have hf1 : f1 S1 - c = f1 S2 - c := congrArg Prod.fst heq;have hf2 : f2 S1 - c = f2 S2 - c := congrArg Prod.snd heq;exact hinj hS1 hS2 (by dsimp only; exact Prod.ext (by omega) (by omega))
   have hbd := card_gcd_rect_one_side (N := N) (d := d) hd1 hdN (a1 := a1 - c) (a2 := a2 - c) (b1 := b1 - c) (b2 := b2 - c) (by omega) (by have := ha_sub.2; omega) (by omega) (by omega);have hca : (Icc (a1 - c) (a2 - c)).card = (Icc a1 a2).card := by rw [Nat.card_Icc, Nat.card_Icc]; omega
   have hcb : (Icc (b1 - c) (b2 - c)).card = (Icc b1 b2).card := by rw [Nat.card_Icc, Nat.card_Icc]; omega
   rw [hca, hcb] at hbd;exact le_trans (by exact_mod_cast hle) hbd
lemma card_gcd_self_interval {N c d u v : ℕ} (hN : 1 <= N) (hd1 : 1 <= d) (hdN : d <= N) (hcu : c < u) (hvN : v <= N) {F A : Finset (Finset ℕ)} (hA_sub : A ⊆ F) (pH xH : Finset ℕ -> ℕ) (hA : ∀ S ∈ A, IsDeltaTriplet F S c (pH S) (xH S) /\ Nat.gcd (distNat c (pH S)) (distNat c (xH S)) = d /\ pH S ∈ Icc u v /\ xH S ∈ Icc u v) : (A.card : ℝ) <= (moebius2Sum N / (d : ℝ) ^ 2) * ((Icc u v).card : ℝ) ^ 2 / 2 + 4 * (N : ℝ) * (1 + Real.log N) / (d : ℝ) + 1 := by
 classical
 have hM_nn : 0 <= moebius2Sum N := (moebius2Sum_bounds hN).1;have hlog_nn : 0 <= Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN);have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
 rcases A.eq_empty_or_nonempty with rfl | ⟨S0, hS0⟩
 . simp; positivity
 have huv : u <= v := le_trans (mem_Icc.mp (hA S0 hS0).2.2.1).1 (mem_Icc.mp (hA S0 hS0).2.2.1).2
 have hinj_xp : Set.InjOn (fun S => (xH S, pH S)) (A : Set (Finset ℕ)) := fun S1 h1 S2 h2 heq => by
   dsimp only at heq; by_contra hne;have hdt1 := (hA S1 (mem_coe.mp h1)).1; have hdt2 := (hA S2 (mem_coe.mp h2)).1
   rcases Prod.mk.inj heq with ⟨hx_eq, hp_eq⟩
   exact hdt1.2.2.2.2.2.2 S2 (hA_sub (mem_coe.mp h2)) (Ne.symm hne) ⟨hdt2.1, hp_eq ▸ hdt2.2.1, hx_eq ▸ hdt2.2.2.1⟩
 let Img1 := A.image (fun S => (pH S - c, xH S - c))
 let Img2 := A.image (fun S => (xH S - c, pH S - c))
 have hdisj : Disjoint Img1 Img2 := by
   rw [Finset.disjoint_left]; intro q h1 h2;obtain ⟨S1, hS1, rfl⟩ := mem_image.mp h1;obtain ⟨S2, hS2, heq⟩ := mem_image.mp h2;have h1I := mem_Icc.mp (hA S1 hS1).2.2.1; have h1I' := mem_Icc.mp (hA S1 hS1).2.2.2;have h2I := mem_Icc.mp (hA S2 hS2).2.2.1; have h2I' := mem_Icc.mp (hA S2 hS2).2.2.2;have he1 : xH S2 = pH S1 := by have := congrArg Prod.fst heq; omega
   have he2 : pH S2 = xH S1 := by have := congrArg Prod.snd heq; omega
   by_cases h12 : S1 = S2
   . subst h12; exact (hA S1 hS1).1.2.2.2.2.2.1 he1.symm
   . have hdt1 := (hA S1 hS1).1; have hdt2 := (hA S2 hS2).1
     exact hdt1.2.2.2.2.2.2 S2 (hA_sub hS2) (Ne.symm h12) ⟨hdt2.1, he1 ▸ hdt2.2.2.1, he2 ▸ hdt2.2.1⟩
 have hinj1 : Set.InjOn (fun S => (pH S - c, xH S - c)) (A : Set (Finset ℕ)) := fun S1 h1 S2 h2 heq => by
   dsimp only at heq;have h1I := (hA S1 (mem_coe.mp h1)).2.2; have h2I := (hA S2 (mem_coe.mp h2)).2.2;have hp : pH S1 = pH S2 := by have := congrArg Prod.fst heq; have := (mem_Icc.mp h1I.1).1; have := (mem_Icc.mp h2I.1).1; omega
   have hx : xH S1 = xH S2 := by have := congrArg Prod.snd heq; have := (mem_Icc.mp h1I.2).1; have := (mem_Icc.mp h2I.2).1; omega
   exact hinj_xp h1 h2 (Prod.ext hx hp)
 have hinj2 : Set.InjOn (fun S => (xH S - c, pH S - c)) (A : Set (Finset ℕ)) := fun S1 h1 S2 h2 heq => by
   dsimp only at heq;have h1I := (hA S1 (mem_coe.mp h1)).2.2; have h2I := (hA S2 (mem_coe.mp h2)).2.2;have hx : xH S1 = xH S2 := by have := congrArg Prod.fst heq; have := (mem_Icc.mp h1I.2).1; have := (mem_Icc.mp h2I.2).1; omega
   have hp : pH S1 = pH S2 := by have := congrArg Prod.snd heq; have := (mem_Icc.mp h1I.1).1; have := (mem_Icc.mp h2I.1).1; omega
   exact hinj_xp h1 h2 (Prod.ext hx hp)
 have hsub : Img1 ∪ Img2 ⊆ (Icc (u - c) (v - c) ×ˢ Icc (u - c) (v - c)).filter (fun p => Nat.gcd p.1 p.2 = d) := by
   intro q hq
   rcases mem_union.mp hq with h1 | h2
   . obtain ⟨S, hS, rfl⟩ := mem_image.mp h1
     have h1I := mem_Icc.mp (hA S hS).2.2.1; have h2I := mem_Icc.mp (hA S hS).2.2.2;have hg := (hA S hS).2.1; rw [distNat_eq_sub (by omega), distNat_eq_sub (by omega)] at hg;exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, mem_Icc.mpr ⟨by omega, by omega⟩⟩, hg⟩
   . obtain ⟨S, hS, rfl⟩ := mem_image.mp h2
     have h1I := mem_Icc.mp (hA S hS).2.2.1; have h2I := mem_Icc.mp (hA S hS).2.2.2;have hg := (hA S hS).2.1; rw [distNat_eq_sub (by omega), distNat_eq_sub (by omega), Nat.gcd_comm] at hg;exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, mem_Icc.mpr ⟨by omega, by omega⟩⟩, hg⟩
 have hc2 := card_le_card hsub;rw [card_union_of_disjoint hdisj, card_image_of_injOn hinj1, card_image_of_injOn hinj2] at hc2;have hbd := card_gcd_rect_one_side (N := N) (d := d) hd1 hdN (a1 := u - c) (a2 := v - c) (b1 := u - c) (b2 := v - c) (by omega) (by omega) (by omega) (by omega);have hceq : (Icc (u - c) (v - c)).card = (Icc u v).card := by rw [Nat.card_Icc, Nat.card_Icc]; omega
 rw [hceq] at hbd
 have hc2R : 2 * (A.card : ℝ) <= (((Icc (u - c) (v - c) ×ˢ Icc (u - c) (v - c)).filter (fun p => Nat.gcd p.1 p.2 = d)).card : ℝ) := by
   have : 2 * A.card = A.card + A.card := by omega
   rw [<- this] at hc2; exact_mod_cast hc2
 linarith [hbd, hc2R, show (moebius2Sum N / (d : ℝ) ^ 2) * ((Icc u v).card : ℝ) * ((Icc u v).card : ℝ) = 2 * ((moebius2Sum N / (d : ℝ) ^ 2) * ((Icc u v).card : ℝ) ^ 2 / 2) by ring, show 8 * (N : ℝ) * (1 + Real.log N) / (d : ℝ) = 2 * (4 * (N : ℝ) * (1 + Real.log N) / (d : ℝ)) by ring]
lemma thm41_step_vi_d_empty {N c q r d : ℕ} (hN : 1 <= N) (hc : c ∈ Icc 1 N) (hcqr : c + q + r <= N) (hd1 : 1 <= d) (hdN : d <= N) {F HdR : Finset (Finset ℕ)} (hHdR_sub : HdR ⊆ F) (pH xH : Finset ℕ -> ℕ) (hHdR : ∀ S ∈ HdR, IsDeltaTriplet F S c (pH S) (xH S) /\ Nat.gcd (distNat c (pH S)) (distNat c (xH S)) = d /\ pH S ∈ Icc (c + q + 1) (c + q + r - 1) /\ xH S ∈ (Icc 1 (c + q + r - 1)).erase c) : (HdR.card : ℝ) <= (moebius2Sum N * ((r : ℝ) * ((q : ℝ) + (c : ℝ) + (r : ℝ)) - (r : ℝ) ^ 2 / 2)) / (d : ℝ) ^ 2 + 40 * (N : ℝ) * (1 + Real.log N) / (d : ℝ) + 12 := by
 classical
 have hM_nn : 0 <= moebius2Sum N := (moebius2Sum_bounds hN).1;have hlog_nn : 0 <= Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN);have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
 by_cases hr2 : r <= 1
 . have hHdR_e : HdR = ∅ := eq_empty_iff_forall_notMem.mpr fun S hS => by
     have := mem_Icc.mp (hHdR S hS).2.2.1; omega
   rw [hHdR_e]; simp
   have h1 : 0 <= moebius2Sum N * ((r : ℝ) * ((q : ℝ) + (c : ℝ) + (r : ℝ)) - (r : ℝ) ^ 2 / 2) / (d : ℝ) ^ 2 := by
     have h2 : 0 <= (r : ℝ) * ((q : ℝ) + (c : ℝ) + (r : ℝ)) - (r : ℝ) ^ 2 / 2 := by
       have : (r : ℝ) * ((q : ℝ) + (c : ℝ) + (r : ℝ)) - (r : ℝ) ^ 2 / 2 = (r : ℝ) * ((q : ℝ) + (c : ℝ)) + (r : ℝ) ^ 2 / 2 := by ring
       rw [this]; positivity
     positivity
   have h3 : 0 <= 40 * (N : ℝ) * (1 + Real.log N) / (d : ℝ) := by positivity
   linarith
 push Not at hr2
 have hinj_xp : ∀ A ⊆ HdR, Set.InjOn (fun S => (xH S, pH S)) (A : Set (Finset ℕ)) := by
   intro A hA S1 h1 S2 h2 heq; dsimp only at heq; by_contra hne;have hdt1 := (hHdR S1 (hA (mem_coe.mp h1))).1; have hdt2 := (hHdR S2 (hA (mem_coe.mp h2))).1
   rcases Prod.mk.inj heq with ⟨hx_eq, hp_eq⟩
   exact hdt1.2.2.2.2.2.2 S2 (hHdR_sub (hA (mem_coe.mp h2))) (Ne.symm hne) ⟨hdt2.1, hp_eq ▸ hdt2.2.1, hx_eq ▸ hdt2.2.2.1⟩
 let HC := HdR.filter (fun S => xH S < c)
 let HQ := HdR.filter (fun S => c < xH S /\ xH S <= c + q)
 let HR := HdR.filter (fun S => c + q < xH S)
 have hcov : HdR ⊆ HC ∪ (HQ ∪ HR) := fun S hS => by
   have hxe := Finset.mem_erase.mp (hHdR S hS).2.2.2
   by_cases h1 : xH S < c
   . exact mem_union_left _ (mem_filter.mpr ⟨hS, h1⟩)
   by_cases h2 : xH S <= c + q
   . exact mem_union_right _ (mem_union_left _ (mem_filter.mpr ⟨hS, by omega, h2⟩))
   . exact mem_union_right _ (mem_union_right _ (mem_filter.mpr ⟨hS, by omega⟩))
 have hHC := card_gcd_shifted_intervals hN hc hd1 hdN (a1 := 1) (a2 := c - 1) (b1 := c + q + 1) (b2 := c + q + r - 1) xH pH (hinj_xp HC (filter_subset _ _)) (Or.inl fun S hS => ⟨(mem_Icc.mp (Finset.mem_erase.mp (hHdR S (mem_filter.mp hS).1).2.2.2).2).1,
     by have := (mem_filter.mp hS).2; omega, by have := (mem_filter.mp hS).2; omega⟩)
   (fun S hS => have h := mem_Icc.mp (hHdR S (mem_filter.mp hS).1).2.2.1; ⟨by omega, h.1, h.2, by omega⟩)
   ⟨le_rfl, by have := (mem_Icc.mp hc).2; omega⟩
   (fun S hS => by rw [Nat.gcd_comm]; exact (hHdR S (mem_filter.mp hS).1).2.1)
 have hHQ := card_gcd_shifted_intervals hN hc hd1 hdN (a1 := c + 1) (a2 := c + q) (b1 := c + q + 1) (b2 := c + q + r - 1) xH pH (hinj_xp HQ (filter_subset _ _)) (Or.inr fun S hS => have h := (mem_filter.mp hS).2; ⟨by omega, by omega, h.2⟩) (fun S hS => have h := mem_Icc.mp (hHdR S (mem_filter.mp hS).1).2.2.1; ⟨by omega, h.1, h.2, by omega⟩) ⟨by omega, by omega⟩ (fun S hS => by rw [Nat.gcd_comm]; exact (hHdR S (mem_filter.mp hS).1).2.1)
 have hHR := card_gcd_self_interval (A := HR) hN hd1 hdN (u := c + q + 1) (v := c + q + r - 1) (by omega) (by omega) ((filter_subset _ _).trans hHdR_sub) pH xH (fun S hS => ⟨(hHdR S (mem_filter.mp hS).1).1, (hHdR S (mem_filter.mp hS).1).2.1, (hHdR S (mem_filter.mp hS).1).2.2.1, mem_Icc.mpr ⟨by have := (mem_filter.mp hS).2; omega, (mem_Icc.mp (Finset.mem_erase.mp (hHdR S (mem_filter.mp hS).1).2.2.2).2).2⟩⟩);have hc1 : ((Icc 1 (c - 1)).card : ℝ) <= (c : ℝ) := by rw [Nat.card_Icc]; exact_mod_cast (by omega : c - 1 + 1 - 1 <= c)
 have hc2 : ((Icc (c + 1) (c + q)).card : ℝ) <= (q : ℝ) := by rw [Nat.card_Icc]; exact_mod_cast (by omega : c + q + 1 - (c + 1) <= q)
 have hc3 : ((Icc (c + q + 1) (c + q + r - 1)).card : ℝ) <= (r : ℝ) := by rw [Nat.card_Icc]; exact_mod_cast (by omega : c + q + r - 1 + 1 - (c + q + 1) <= r)
 have hHdR_le : (HdR.card : ℝ) <= (HC.card : ℝ) + (HQ.card : ℝ) + (HR.card : ℝ) := by
   have h1 : HdR.card <= HC.card + HQ.card + HR.card := by
     have := le_trans (card_le_card hcov) (le_trans (card_union_le _ _) (Nat.add_le_add_left (card_union_le _ _) _));omega
   exact_mod_cast h1
 have hm1 := mul_le_mul (mul_le_mul_of_nonneg_left hc1 (show 0 <= moebius2Sum N / (d : ℝ) ^ 2 by positivity)) hc3 (Nat.cast_nonneg _) (by positivity);have hm2 := mul_le_mul (mul_le_mul_of_nonneg_left hc2 (show 0 <= moebius2Sum N / (d : ℝ) ^ 2 by positivity)) hc3 (Nat.cast_nonneg _) (by positivity)
 have hm3 : (moebius2Sum N / (d : ℝ) ^ 2) * ((Icc (c + q + 1) (c + q + r - 1)).card : ℝ) ^ 2 / 2 <= (moebius2Sum N / (d : ℝ) ^ 2) * (r : ℝ) ^ 2 / 2 := by
   have hsq := pow_le_pow_left₀ (Nat.cast_nonneg _) hc3 2;have := mul_le_mul_of_nonneg_left hsq (show 0 <= moebius2Sum N / (d : ℝ) ^ 2 by positivity);linarith
 have hrew : (moebius2Sum N / (d : ℝ) ^ 2) * (c : ℝ) * (r : ℝ) + (moebius2Sum N / (d : ℝ) ^ 2) * (q : ℝ) * (r : ℝ) + (moebius2Sum N / (d : ℝ) ^ 2) * (r : ℝ) ^ 2 / 2 = (moebius2Sum N * ((r : ℝ) * ((q : ℝ) + (c : ℝ) + (r : ℝ)) - (r : ℝ) ^ 2 / 2)) / (d : ℝ) ^ 2 := by ring
 have herr : 0 <= 20 * (N : ℝ) * (1 + Real.log N) / (d : ℝ) := by positivity
 linarith [hHdR_le, hHC, hHQ, hHR, hm1, hm2, hm3, hrew, herr, show 8 * (N : ℝ) * (1 + Real.log N) / (d : ℝ) + 8 * (N : ℝ) * (1 + Real.log N) / (d : ℝ) + 4 * (N : ℝ) * (1 + Real.log N) / (d : ℝ) + 20 * (N : ℝ) * (1 + Real.log N) / (d : ℝ) = 40 * (N : ℝ) * (1 + Real.log N) / (d : ℝ) by ring]
lemma thm41_step_vi_d {N c q r d : ℕ} (hN : 1 <= N) (hN1000 : 1000 <= N) (hc : c ∈ Icc 1 N) (hq1 : 1 <= q) (hcqr : c + q + r <= N) (hd1 : 1 <= d) (hdN : d <= N) {F EdR HdR : Finset (Finset ℕ)} (_hF : IsWellInter N F) (hEdR_sub : EdR ⊆ F) (hHdR_sub : HdR ⊆ F) (hEdR : ∀ E0 ∈ EdR, c ∈ E0 /\ (∀ x ∈ E0, x % d = c % d) /\ (∀ x ∈ E0, ∀ y ∈ E0, ∀ z, min x y <= z -> z <= max x y -> z % d = c % d -> z ∈ E0) /\ (∃ hne : E0.Nonempty, E0.min' hne ∈ Icc 1 c /\ E0.max' hne ∈ Icc (c + q + 1) (c + q + r - 1))) (pH xH : Finset ℕ -> ℕ) (hHdR : ∀ S ∈ HdR, S ∉ EdR /\ IsDeltaTriplet F S c (pH S) (xH S) /\
     Nat.gcd (distNat c (pH S)) (distNat c (xH S)) = d /\
     pH S ∈ Icc (c + q + 1) (c + q + r - 1) /\
     xH S ∈ (Icc 1 (c + q + r - 1)).erase c) :
   ∃ sd : ℕ, sd <= r /\ (EdR.card : ℝ) + (HdR.card : ℝ) <= ((c : ℝ) * ((r : ℝ) - (sd : ℝ)) + moebius2Sum N * ((sd : ℝ) * ((q : ℝ) + (c : ℝ) + (r : ℝ)) - (sd : ℝ) ^ 2 / 2)) / (d : ℝ) ^ 2 + 40 * (N : ℝ) * (1 + Real.log N) / (d : ℝ) + 12 := by
 classical
 have hM_nn : 0 <= moebius2Sum N := (moebius2Sum_bounds hN).1
 have hM_le1 : moebius2Sum N <= 1 := by
   have hZ := (zeta2Sum_bounds (by omega : 100 <= N)).1;have hMZ := (abs_le.mp (moebius2Sum_mul_zeta2Sum_approx hN)).2
   have hsq : (20 : ℝ) <= Real.sqrt N := by
     rw [<- Real.sqrt_sq (by norm_num : (0 : ℝ) <= 20)];exact Real.sqrt_le_sqrt (by exact_mod_cast (by omega : 400 <= N))
   have hdiv : 7 / Real.sqrt N <= 7 / 20 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hsq;nlinarith
 have hlog_nn : 0 <= Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN);have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
 have hinj_xp : ∀ A ⊆ HdR, Set.InjOn (fun S => (xH S, pH S)) (A : Set (Finset ℕ)) := by
   intro A hA S1 h1 S2 h2 heq; dsimp only at heq;by_contra hne;have hdt1 := (hHdR S1 (hA (mem_coe.mp h1))).2.1;have hdt2 := (hHdR S2 (hA (mem_coe.mp h2))).2.1;have hp_eq : pH S1 = pH S2 := congrArg Prod.snd heq;have hx_eq : xH S1 = xH S2 := congrArg Prod.fst heq;exact hdt1.2.2.2.2.2.2 S2 (hHdR_sub (hA (mem_coe.mp h2))) (Ne.symm hne) ⟨hdt2.1, hp_eq ▸ hdt2.2.1, hx_eq ▸ hdt2.2.2.1⟩
 have hmod_d : ∀ S ∈ HdR, pH S % d = c % d /\ xH S % d = c % d := by
   intro S hS;have hg := (hHdR S hS).2.2.1;have h1 : d ∣ distNat c (pH S) := hg ▸ Nat.gcd_dvd_left _ _;have h2 : d ∣ distNat c (xH S) := hg ▸ Nat.gcd_dvd_right _ _
   have hof : ∀ a : ℕ, d ∣ distNat c a -> a % d = c % d := fun a hdvd => by
     unfold distNat at hdvd
     rcases le_total c a with hle | hle
     . rw [max_eq_right hle, min_eq_left hle] at hdvd; exact ((Nat.modEq_iff_dvd' hle).mpr hdvd).symm
     . rw [max_eq_left hle, min_eq_right hle] at hdvd; exact (Nat.modEq_iff_dvd' hle).mpr hdvd
   exact ⟨hof _ h1, hof _ h2⟩
 have hself_half : ∀ (A : Finset (Finset ℕ)) (u v : ℕ), A ⊆ HdR -> c < u -> v <= N -> (∀ S ∈ A, pH S ∈ Icc u v /\ xH S ∈ Icc u v) -> (A.card : ℝ) <= (moebius2Sum N / (d : ℝ) ^ 2) * ((Icc u v).card : ℝ) ^ 2 / 2 + 4 * (N : ℝ) * (1 + Real.log N) / (d : ℝ) + 1 := fun A u v hA hcu hvN hmem =>
   card_gcd_self_interval hN hd1 hdN hcu hvN (hA.trans hHdR_sub) pH xH (fun S hS => ⟨(hHdR S (hA hS)).2.1, (hHdR S (hA hS)).2.2.1, (hmem S hS).1, (hmem S hS).2⟩)
 rcases EdR.eq_empty_or_nonempty with rfl | hEdR_ne
 . refine ⟨r, le_rfl, ?_⟩
   simp only [card_empty, Nat.cast_zero, zero_add, sub_self, mul_zero];exact thm41_step_vi_d_empty hN hc hcqr hd1 hdN hHdR_sub pH xH (fun S hS => (hHdR S hS).2)
 ·
   let minOf : Finset ℕ -> ℕ := fun E0 => if h : E0.Nonempty then E0.min' h else c
   let maxOf : Finset ℕ -> ℕ := fun E0 => if h : E0.Nonempty then E0.max' h else c
   obtain ⟨Emin, hEmin, hEmin_le⟩ := exists_min_image EdR minOf hEdR_ne;obtain ⟨Emax, hEmax, hEmax_ge⟩ := exists_max_image EdR maxOf hEdR_ne;obtain ⟨-, -, -, hne_min, hmin_I, -⟩ := hEdR Emin hEmin
   obtain ⟨-, -, -, hne_max, -, hmax_I⟩ := hEdR Emax hEmax
   set ymin := Emin.min' hne_min
   set rmax := Emax.max' hne_max
   have hymin_I := mem_Icc.mp hmin_I;have hrmax_I := mem_Icc.mp hmax_I;have hr2 : 2 <= r := by omega
   set yd := c - ymin
   set sd := c + q + r - rmax
   have hsd_le : sd <= r := by omega
   refine ⟨sd, hsd_le, ?_⟩
   let H_Y_RS := HdR.filter (fun S => pH S <= rmax /\ ymin <= xH S /\ xH S < c)
   let H_CY_RS := HdR.filter (fun S => pH S <= rmax /\ xH S < ymin)
   let H_C_S := HdR.filter (fun S => rmax < pH S /\ xH S < c)
   let H_QRS_S := HdR.filter (fun S => c < min (pH S) (xH S) /\ min (pH S) (xH S) <= rmax /\ rmax < max (pH S) (xH S))
   let H_S_S := HdR.filter (fun S => rmax < pH S /\ rmax < xH S)
   have hcov : HdR ⊆ H_Y_RS ∪ (H_CY_RS ∪ (H_C_S ∪ (H_QRS_S ∪ H_S_S))) := by
     intro S hS;have hxe := Finset.mem_erase.mp (hHdR S hS).2.2.2.2;have hpI := mem_Icc.mp (hHdR S hS).2.2.2.1
     by_cases hp : pH S <= rmax
     . by_cases hx : xH S < c
       . by_cases hxy : ymin <= xH S
         . exact mem_union_left _ (mem_filter.mpr ⟨hS, hp, hxy, hx⟩)
         . exact mem_union_right _ (mem_union_left _ (mem_filter.mpr ⟨hS, hp, by omega⟩))
       . by_cases hxr : xH S <= rmax
         . exfalso
           obtain ⟨hcE, -, hfillE, -, -, -⟩ := hEdR Emax hEmax;have hdt := (hHdR S hS).2.1; have hmd := hmod_d S hS;have hneE : Emax ≠ S := fun h => (hHdR S hS).1 (h ▸ hEmax)
           have hpE : pH S ∈ Emax := hfillE c hcE rmax (max'_mem Emax hne_max) (pH S) (by omega) (by omega) hmd.1;have hxE : xH S ∈ Emax := hfillE c hcE rmax (max'_mem Emax hne_max) (xH S) (by omega) (by omega) hmd.2;exact hdt.2.2.2.2.2.2 Emax (hEdR_sub hEmax) hneE ⟨hcE, hpE, hxE⟩
         . exact mem_union_right _ (mem_union_right _ (mem_union_right _ (mem_union_left _ (mem_filter.mpr ⟨hS, by omega, by omega, by omega⟩))))
     . by_cases hx : xH S < c
       . exact mem_union_right _ (mem_union_right _ (mem_union_left _ (mem_filter.mpr ⟨hS, by omega, hx⟩)))
       . by_cases hxr : xH S <= rmax
         . exact mem_union_right _ (mem_union_right _ (mem_union_right _ (mem_union_left _ (mem_filter.mpr ⟨hS, by omega, by omega, by omega⟩))))
         . exact mem_union_right _ (mem_union_right _ (mem_union_right _ (mem_union_right _ (mem_filter.mpr ⟨hS, by omega, by omega⟩))))
   have hB1 : (EdR.card : ℝ) + (H_Y_RS.card : ℝ) <= ((yd : ℝ) + 1) * ((r : ℝ) - (sd : ℝ)) / (d : ℝ) ^ 2 + 2 * (N : ℝ) / (d : ℝ) + 1 := by
     have hcor := szabo_cor_3_3 (_N := N) (c := c) (d := d) (a1 := ymin) (a2 := c) (b1 := c + q + 1) (b2 := rmax) (E := EdR) (H := H_Y_RS) hd1 (fun E0 hE0 => by
         obtain ⟨hcE, hmodE, hfillE, hne0, hmin0, hmax0⟩ := hEdR E0 hE0;have h1 : ymin <= E0.min' hne0 := by have := hEmin_le E0 hE0; dsimp only [minOf] at this; rwa [dif_pos hne_min, dif_pos hne0] at this
         have h2 : E0.max' hne0 <= rmax := by have := hEmax_ge E0 hE0; dsimp only [maxOf] at this; rwa [dif_pos hne0, dif_pos hne_max] at this
         exact ⟨hcE, hmodE, hfillE, hne0, mem_Icc.mpr ⟨h1, (mem_Icc.mp hmin0).2⟩, mem_Icc.mpr ⟨(mem_Icc.mp hmax0).1, h2⟩⟩)
       pH xH (fun S hS => by
         obtain ⟨hSH, hp, hxy, hxc⟩ := mem_filter.mp hS;have hmd := hmod_d S hSH; have hdt := (hHdR S hSH).2.1;have hpI := mem_Icc.mp (hHdR S hSH).2.2.2.1
         exact ⟨mem_Icc.mpr ⟨hxy, by omega⟩, mem_Icc.mpr ⟨hpI.1, hp⟩, hmd.2, hmd.1, fun T hTE ⟨hxT, hpT⟩ => hdt.2.2.2.2.2.2 T (hEdR_sub hTE) (fun h => (hHdR S hSH).1 (h ▸ hTE)) ⟨(hEdR T hTE).1, hpT, hxT⟩, fun T hTH hTS ⟨hxT, hpT⟩ => hdt.2.2.2.2.2.2 T (hHdR_sub (mem_filter.mp hTH).1) hTS ⟨(hHdR T (mem_filter.mp hTH).1).2.1.1, hpT, hxT⟩, hdt.2.2.1, hdt.2.1⟩)
     have hcA : ((Icc ymin c).card : ℝ) = (yd : ℝ) + 1 := by
       rw [Nat.card_Icc]; have : c + 1 - ymin = yd + 1 := by omega
       rw [this]; push_cast; ring
     have hcB : ((Icc (c + q + 1) rmax).card : ℝ) <= (r : ℝ) - (sd : ℝ) := by
       rw [Nat.card_Icc];have hnat : rmax + 1 - (c + q + 1) <= r - sd := by omega
       have hR : ((rmax + 1 - (c + q + 1) : ℕ) : ℝ) <= ((r - sd : ℕ) : ℝ) := by exact_mod_cast hnat
       rw [Nat.cast_sub hsd_le] at hR; exact hR
     have hAN : (yd : ℝ) + 1 <= (N : ℝ) := by exact_mod_cast (by omega : yd + 1 <= N)
     have hBN : (r : ℝ) - (sd : ℝ) <= (N : ℝ) := by
       have : ((r - sd : ℕ) : ℝ) <= (N : ℝ) := by exact_mod_cast (by omega : r - sd <= N)
       rwa [Nat.cast_sub hsd_le] at this
     have hprod : (((Icc ymin c).card : ℝ) / (d : ℝ) + 1) * (((Icc (c + q + 1) rmax).card : ℝ) / (d : ℝ) + 1) <= (((yd : ℝ) + 1) / (d : ℝ) + 1) * (((r : ℝ) - (sd : ℝ)) / (d : ℝ) + 1) := mul_le_mul (by rw [hcA]) (by linarith [div_le_div_of_nonneg_right hcB (le_of_lt hdpos)]) (by positivity) (by positivity);have hexp : (((yd : ℝ) + 1) / (d : ℝ) + 1) * (((r : ℝ) - (sd : ℝ)) / (d : ℝ) + 1) = ((yd : ℝ) + 1) * ((r : ℝ) - (sd : ℝ)) / (d : ℝ) ^ 2 + (((yd : ℝ) + 1) + ((r : ℝ) - (sd : ℝ))) / (d : ℝ) + 1 := by field_simp; ring
     have hlin : (((yd : ℝ) + 1) + ((r : ℝ) - (sd : ℝ))) / (d : ℝ) <= 2 * (N : ℝ) / (d : ℝ) := div_le_div_of_nonneg_right (by linarith) (le_of_lt hdpos);linarith [hcor, hprod, hexp, hlin]
   have hB2 : (H_CY_RS.card : ℝ) <= (moebius2Sum N / (d : ℝ) ^ 2) * ((c : ℝ) - (yd : ℝ) - 1) * ((r : ℝ) - (sd : ℝ)) + 8 * (N : ℝ) * (1 + Real.log N) / (d : ℝ) + 2 := by
     by_cases hy1 : ymin <= 1
     . have hE : H_CY_RS = ∅ := eq_empty_iff_forall_notMem.mpr fun S hS => by
         have := (mem_filter.mp hS).2.2;have := (mem_Icc.mp (Finset.mem_erase.mp (hHdR S (mem_filter.mp hS).1).2.2.2.2).2).1;omega
       rw [hE]; simp
       have h1 : (c : ℝ) - (yd : ℝ) - 1 = 0 := by
         have : c = yd + 1 := by omega
         have hR : (c : ℝ) = (yd : ℝ) + 1 := by exact_mod_cast this
         linarith
       rw [h1]; simp; positivity
     push Not at hy1
     have hbd := card_gcd_shifted_intervals hN hc hd1 hdN (a1 := 1) (a2 := ymin - 1) (b1 := c + q + 1) (b2 := rmax) xH pH (hinj_xp H_CY_RS (filter_subset _ _)) (Or.inl fun S hS => ⟨(mem_Icc.mp (Finset.mem_erase.mp (hHdR S (mem_filter.mp hS).1).2.2.2.2).2).1,
         by have := (mem_filter.mp hS).2.2; omega, by omega⟩)
       (fun S hS => ⟨by omega, (mem_Icc.mp (hHdR S (mem_filter.mp hS).1).2.2.2.1).1, (mem_filter.mp hS).2.1, by omega⟩)
       ⟨le_rfl, by omega⟩ (fun S hS => by rw [Nat.gcd_comm]; exact (hHdR S (mem_filter.mp hS).1).2.2.1)
     have hcA : ((Icc 1 (ymin - 1)).card : ℝ) = (c : ℝ) - (yd : ℝ) - 1 := by
       rw [Nat.card_Icc]; have hnat : ymin - 1 + 1 - 1 + yd + 1 = c := by omega
       have hR : ((ymin - 1 + 1 - 1 : ℕ) : ℝ) + (yd : ℝ) + 1 = (c : ℝ) := by exact_mod_cast hnat
       linarith
     have hcB : ((Icc (c + q + 1) rmax).card : ℝ) <= (r : ℝ) - (sd : ℝ) := by
       rw [Nat.card_Icc]; have hnat : rmax + 1 - (c + q + 1) <= r - sd := by omega
       have hR : ((rmax + 1 - (c + q + 1) : ℕ) : ℝ) <= ((r - sd : ℕ) : ℝ) := by exact_mod_cast hnat
       rwa [Nat.cast_sub hsd_le] at hR
     rw [hcA] at hbd;have hnnA : 0 <= (c : ℝ) - (yd : ℝ) - 1 := by rw [<- hcA]; exact Nat.cast_nonneg _
     have hmul := mul_le_mul_of_nonneg_left hcB (show 0 <= (moebius2Sum N / (d : ℝ) ^ 2) * ((c : ℝ) - (yd : ℝ) - 1) by positivity);linarith
   have hB3 : (H_C_S.card : ℝ) <= (moebius2Sum N / (d : ℝ) ^ 2) * (c : ℝ) * (sd : ℝ) + 8 * (N : ℝ) * (1 + Real.log N) / (d : ℝ) + 2 := by
     by_cases hsd2 : sd <= 1
     . have hE : H_C_S = ∅ := eq_empty_iff_forall_notMem.mpr fun S hS => by
         have := (mem_filter.mp hS).2.1;have := (mem_Icc.mp (hHdR S (mem_filter.mp hS).1).2.2.2.1).2; omega
       rw [hE]; simp; positivity
     push Not at hsd2
     have hbd := card_gcd_shifted_intervals hN hc hd1 hdN (a1 := 1) (a2 := c - 1) (b1 := rmax + 1) (b2 := c + q + r - 1) xH pH (hinj_xp H_C_S (filter_subset _ _)) (Or.inl fun S hS => ⟨(mem_Icc.mp (Finset.mem_erase.mp (hHdR S (mem_filter.mp hS).1).2.2.2.2).2).1,
         by have := (mem_filter.mp hS).2.2; omega, by have := (mem_filter.mp hS).2.2; omega⟩)
       (fun S hS => ⟨by omega, by have := (mem_filter.mp hS).2.1; omega, (mem_Icc.mp (hHdR S (mem_filter.mp hS).1).2.2.2.1).2, by omega⟩)
       ⟨le_rfl, by have := (mem_Icc.mp hc).2; omega⟩
       (fun S hS => by rw [Nat.gcd_comm]; exact (hHdR S (mem_filter.mp hS).1).2.2.1)
     have hcA : ((Icc 1 (c - 1)).card : ℝ) <= (c : ℝ) := by rw [Nat.card_Icc]; exact_mod_cast (by omega : c - 1 + 1 - 1 <= c)
     have hcB : ((Icc (rmax + 1) (c + q + r - 1)).card : ℝ) <= (sd : ℝ) := by rw [Nat.card_Icc]; exact_mod_cast (by omega : c + q + r - 1 + 1 - (rmax + 1) <= sd)
     have hmul := mul_le_mul (mul_le_mul_of_nonneg_left hcA (show 0 <= moebius2Sum N / (d : ℝ) ^ 2 by positivity))
       hcB (Nat.cast_nonneg _) (by positivity)
     linarith
   have hB4 : (H_QRS_S.card : ℝ) <= (moebius2Sum N / (d : ℝ) ^ 2) * ((q : ℝ) + (r : ℝ) - (sd : ℝ)) * (sd : ℝ) + 8 * (N : ℝ) * (1 + Real.log N) / (d : ℝ) + 2 := by
     by_cases hsd2 : sd <= 1
     . have hE : H_QRS_S = ∅ := eq_empty_iff_forall_notMem.mpr fun S hS => by
         have := (mem_filter.mp hS).2.2.2;have h1 := (mem_Icc.mp (hHdR S (mem_filter.mp hS).1).2.2.2.1).2;have h2 := (mem_Icc.mp (Finset.mem_erase.mp (hHdR S (mem_filter.mp hS).1).2.2.2.2).2).2;omega
       rw [hE]; simp
       have hqrs : 0 <= (q : ℝ) + (r : ℝ) - (sd : ℝ) := by
         have : (sd : ℝ) <= (r : ℝ) := by exact_mod_cast hsd_le
         have : (0 : ℝ) <= (q : ℝ) := Nat.cast_nonneg _; linarith
       positivity
     push Not at hsd2
     have hinj_mm : Set.InjOn (fun S => (min (pH S) (xH S), max (pH S) (xH S))) (H_QRS_S : Set (Finset ℕ)) := by
       intro S1 h1 S2 h2 heq; dsimp only at heq;by_contra hne;have hdt1 := (hHdR S1 (mem_filter.mp (mem_coe.mp h1)).1).2.1;have hdt2 := (hHdR S2 (mem_filter.mp (mem_coe.mp h2)).1).2.1;have hmin_eq : min (pH S1) (xH S1) = min (pH S2) (xH S2) := congrArg Prod.fst heq;have hmax_eq : max (pH S1) (xH S1) = max (pH S2) (xH S2) := congrArg Prod.snd heq
       have hm2 : ∀ w, w = min (pH S2) (xH S2) \/ w = max (pH S2) (xH S2) -> w ∈ S2 := fun w hw => by
         rcases hw with rfl | rfl
         . rcases min_choice (pH S2) (xH S2) with h | h <;> rw [h]; exact hdt2.2.1; exact hdt2.2.2.1
         . rcases max_choice (pH S2) (xH S2) with h | h <;> rw [h]; exact hdt2.2.1; exact hdt2.2.2.1
       have hp1 : pH S1 ∈ S2 := hm2 _ (by
         rcases le_total (pH S1) (xH S1) with h | h
         . left; rw [<- hmin_eq, min_eq_left h]
         . right; rw [<- hmax_eq, max_eq_left h])
       have hx1 : xH S1 ∈ S2 := hm2 _ (by
         rcases le_total (pH S1) (xH S1) with h | h
         . right; rw [<- hmax_eq, max_eq_right h]
         . left; rw [<- hmin_eq, min_eq_right h])
       exact hdt1.2.2.2.2.2.2 S2 (hHdR_sub (mem_filter.mp (mem_coe.mp h2)).1) (Ne.symm hne) ⟨hdt2.1, hp1, hx1⟩
     have hbd := card_gcd_shifted_intervals hN hc hd1 hdN (a1 := c + 1) (a2 := rmax) (b1 := rmax + 1) (b2 := c + q + r - 1) (fun S => min (pH S) (xH S)) (fun S => max (pH S) (xH S)) hinj_mm (Or.inr fun S hS => ⟨by omega, by have := (mem_filter.mp hS).2.1; omega, (mem_filter.mp hS).2.2.1⟩) (fun S hS => ⟨by omega, by have := (mem_filter.mp hS).2.2.2; omega,
         by have h1 := (mem_Icc.mp (hHdR S (mem_filter.mp hS).1).2.2.2.1).2
            have h2 := (mem_Icc.mp (Finset.mem_erase.mp (hHdR S (mem_filter.mp hS).1).2.2.2.2).2).2
            omega, by omega⟩)
       ⟨by omega, by omega⟩
       (fun S hS => by
         have hg := (hHdR S (mem_filter.mp hS).1).2.2.1
         rcases le_total (pH S) (xH S) with h | h
         . rwa [min_eq_left h, max_eq_right h]
         . rw [min_eq_right h, max_eq_left h, Nat.gcd_comm]; exact hg)
     have hcA : ((Icc (c + 1) rmax).card : ℝ) = (q : ℝ) + (r : ℝ) - (sd : ℝ) := by
       rw [Nat.card_Icc]; have hnat : rmax + 1 - (c + 1) + sd = q + r := by omega
       have hR : ((rmax + 1 - (c + 1) : ℕ) : ℝ) + (sd : ℝ) = (q : ℝ) + (r : ℝ) := by exact_mod_cast hnat
       linarith
     have hcB : ((Icc (rmax + 1) (c + q + r - 1)).card : ℝ) <= (sd : ℝ) := by rw [Nat.card_Icc]; exact_mod_cast (by omega : c + q + r - 1 + 1 - (rmax + 1) <= sd)
     rw [hcA] at hbd;have hqrs : 0 <= (q : ℝ) + (r : ℝ) - (sd : ℝ) := by rw [<- hcA]; exact Nat.cast_nonneg _
     have hmul := mul_le_mul_of_nonneg_left hcB (show 0 <= (moebius2Sum N / (d : ℝ) ^ 2) * ((q : ℝ) + (r : ℝ) - (sd : ℝ)) by positivity);linarith
   have hB5 : (H_S_S.card : ℝ) <= (moebius2Sum N / (d : ℝ) ^ 2) * (sd : ℝ) ^ 2 / 2 + 4 * (N : ℝ) * (1 + Real.log N) / (d : ℝ) + 1 := by
     by_cases hsd2 : sd <= 1
     . have hE : H_S_S = ∅ := eq_empty_iff_forall_notMem.mpr fun S hS => by
         have := (mem_filter.mp hS).2.1;have := (mem_Icc.mp (hHdR S (mem_filter.mp hS).1).2.2.2.1).2; omega
       rw [hE]; simp; positivity
     push Not at hsd2;have hbd := hself_half H_S_S (rmax + 1) (c + q + r - 1) (filter_subset _ _) (by omega) (by omega) (fun S hS => ⟨mem_Icc.mpr ⟨by have := (mem_filter.mp hS).2.1; omega, (mem_Icc.mp (hHdR S (mem_filter.mp hS).1).2.2.2.1).2⟩, mem_Icc.mpr ⟨by have := (mem_filter.mp hS).2.2; omega, (mem_Icc.mp (Finset.mem_erase.mp (hHdR S (mem_filter.mp hS).1).2.2.2.2).2).2⟩⟩);have hcB : ((Icc (rmax + 1) (c + q + r - 1)).card : ℝ) <= (sd : ℝ) := by rw [Nat.card_Icc]; exact_mod_cast (by omega : c + q + r - 1 + 1 - (rmax + 1) <= sd)
     have hsq : ((Icc (rmax + 1) (c + q + r - 1)).card : ℝ) ^ 2 <= (sd : ℝ) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hcB 2;have hmul := mul_le_mul_of_nonneg_left hsq (show 0 <= moebius2Sum N / (d : ℝ) ^ 2 by positivity);linarith
   have hHdR_le : (HdR.card : ℝ) <= (H_Y_RS.card : ℝ) + (H_CY_RS.card : ℝ) + (H_C_S.card : ℝ) + (H_QRS_S.card : ℝ) + (H_S_S.card : ℝ) := by
     have h1 := le_trans (card_le_card hcov) (card_union_le _ _);have h2 := card_union_le H_CY_RS (H_C_S ∪ (H_QRS_S ∪ H_S_S));have h3 := card_union_le H_C_S (H_QRS_S ∪ H_S_S);have h4 := card_union_le H_QRS_S H_S_S;exact_mod_cast (by omega : HdR.card <= H_Y_RS.card + H_CY_RS.card + H_C_S.card + H_QRS_S.card + H_S_S.card)
   have hM_yd : ((yd : ℝ) + 1) + moebius2Sum N * ((c : ℝ) - (yd : ℝ) - 1) <= (c : ℝ) + 1 := by
     have hcy0 : 0 <= (c : ℝ) - (yd : ℝ) - 1 := by
       have h1 : 1 <= ymin := hymin_I.1; have h2 : ymin <= c := hymin_I.2;have h3 : ymin - 1 + yd + 1 = c := by omega
       have h4 : ((ymin - 1 : ℕ) : ℝ) + (yd : ℝ) + 1 = (c : ℝ) := by exact_mod_cast h3
       linarith [Nat.cast_nonneg (α := ℝ) (ymin - 1)]
     have h1 := mul_le_mul_of_nonneg_right hM_le1 hcy0;linarith [h1]
   have hrs0 : 0 <= (r : ℝ) - (sd : ℝ) := by
     have : (sd : ℝ) <= (r : ℝ) := by exact_mod_cast hsd_le
     linarith
   have hrsN : (r : ℝ) - (sd : ℝ) <= (N : ℝ) := by
     have : ((r - sd : ℕ) : ℝ) <= (N : ℝ) := by exact_mod_cast (by omega : r - sd <= N)
     rwa [Nat.cast_sub hsd_le] at this
   have hd2_ge : (d : ℝ) <= (d : ℝ) ^ 2 := by
     have h1 : (1 : ℝ) <= (d : ℝ) := by exact_mod_cast hd1
     have h2 : (1 : ℝ) * (d : ℝ) <= (d : ℝ) * (d : ℝ) := mul_le_mul_of_nonneg_right h1 (by positivity);linarith [h2, show (d : ℝ) ^ 2 = (d : ℝ) * (d : ℝ) by ring]
   have h1_over_d2 : ((r : ℝ) - (sd : ℝ)) / (d : ℝ) ^ 2 <= (N : ℝ) / (d : ℝ) := by
     calc ((r : ℝ) - (sd : ℝ)) / (d : ℝ) ^ 2 <= (N : ℝ) / (d : ℝ) ^ 2 := div_le_div_of_nonneg_right hrsN (by positivity)
       _ <= (N : ℝ) / (d : ℝ) := div_le_div_of_nonneg_left (Nat.cast_nonneg N) hdpos hd2_ge
   have hcomb1 : (((yd : ℝ) + 1) * ((r : ℝ) - (sd : ℝ)) / (d : ℝ) ^ 2) + (moebius2Sum N / (d : ℝ) ^ 2) * ((c : ℝ) - (yd : ℝ) - 1) * ((r : ℝ) - (sd : ℝ)) <= ((c : ℝ) * ((r : ℝ) - (sd : ℝ))) / (d : ℝ) ^ 2 + (N : ℝ) / (d : ℝ) := by
     have h1 : (((yd : ℝ) + 1) + moebius2Sum N * ((c : ℝ) - (yd : ℝ) - 1)) * (((r : ℝ) - (sd : ℝ)) / (d : ℝ) ^ 2) <= ((c : ℝ) + 1) * (((r : ℝ) - (sd : ℝ)) / (d : ℝ) ^ 2) := mul_le_mul_of_nonneg_right hM_yd (by positivity)
     linarith [h1, h1_over_d2, show (((yd : ℝ) + 1) * ((r : ℝ) - (sd : ℝ)) / (d : ℝ) ^ 2) + (moebius2Sum N / (d : ℝ) ^ 2) * ((c : ℝ) - (yd : ℝ) - 1) * ((r : ℝ) - (sd : ℝ)) = (((yd : ℝ) + 1) + moebius2Sum N * ((c : ℝ) - (yd : ℝ) - 1)) * (((r : ℝ) - (sd : ℝ)) / (d : ℝ) ^ 2) by ring, show ((c : ℝ) + 1) * (((r : ℝ) - (sd : ℝ)) / (d : ℝ) ^ 2) = (c : ℝ) * ((r : ℝ) - (sd : ℝ)) / (d : ℝ) ^ 2 + ((r : ℝ) - (sd : ℝ)) / (d : ℝ) ^ 2 by ring]
   have hcomb2 : (moebius2Sum N / (d : ℝ) ^ 2) * (c : ℝ) * (sd : ℝ) + (moebius2Sum N / (d : ℝ) ^ 2) * ((q : ℝ) + (r : ℝ) - (sd : ℝ)) * (sd : ℝ) + (moebius2Sum N / (d : ℝ) ^ 2) * (sd : ℝ) ^ 2 / 2 = (moebius2Sum N * ((sd : ℝ) * ((q : ℝ) + (c : ℝ) + (r : ℝ)) - (sd : ℝ) ^ 2 / 2)) / (d : ℝ) ^ 2 := by ring
   have hcomb3 : ((c : ℝ) * ((r : ℝ) - (sd : ℝ))) / (d : ℝ) ^ 2 + (moebius2Sum N * ((sd : ℝ) * ((q : ℝ) + (c : ℝ) + (r : ℝ)) - (sd : ℝ) ^ 2 / 2)) / (d : ℝ) ^ 2 = ((c : ℝ) * ((r : ℝ) - (sd : ℝ)) + moebius2Sum N * ((sd : ℝ) * ((q : ℝ) + (c : ℝ) + (r : ℝ)) - (sd : ℝ) ^ 2 / 2)) / (d : ℝ) ^ 2 := by ring
   have herr : 3 * (N : ℝ) / (d : ℝ) + 28 * (N : ℝ) * (1 + Real.log N) / (d : ℝ) <= 40 * (N : ℝ) * (1 + Real.log N) / (d : ℝ) := by
     have h1 : 3 * (N : ℝ) / (d : ℝ) <= 12 * (N : ℝ) * (1 + Real.log N) / (d : ℝ) := by
       apply div_le_div_of_nonneg_right _ (le_of_lt hdpos);have h12 := mul_le_mul_of_nonneg_left (show (1 : ℝ) <= 1 + Real.log N by linarith) (show (0 : ℝ) <= 12 * (N : ℝ) by positivity);linarith [h12, Nat.cast_nonneg (α := ℝ) N]
     linarith [h1, show 12 * (N : ℝ) * (1 + Real.log N) / (d : ℝ) + 28 * (N : ℝ) * (1 + Real.log N) / (d : ℝ) = 40 * (N : ℝ) * (1 + Real.log N) / (d : ℝ) by ring]
   linarith only [hB1, hB2, hB3, hB4, hB5, hHdR_le, hcomb1, hcomb2, hcomb3, herr, show 2 * (N : ℝ) / (d : ℝ) + (N : ℝ) / (d : ℝ) = 3 * (N : ℝ) / (d : ℝ) by ring, show 8 * (N : ℝ) * (1 + Real.log N) / (d : ℝ) + 8 * (N : ℝ) * (1 + Real.log N) / (d : ℝ) + 8 * (N : ℝ) * (1 + Real.log N) / (d : ℝ) + 4 * (N : ℝ) * (1 + Real.log N) / (d : ℝ) = 28 * (N : ℝ) * (1 + Real.log N) / (d : ℝ) by ring]
lemma thm41_step_ii {N c q r : ℕ} (hcqr : c + q + r <= N) {F Sfam P1 HXQ : Finset (Finset ℕ)} (hF : IsWellInter N F) (hSfam_sub : Sfam ⊆ F) (hP1_sub : P1 ⊆ F) (hHXQ_sub : HXQ ⊆ Sfam) (hP1 : ∀ I ∈ P1, ∃ i f, i ∈ Icc (c + 1) (c + q - 1) /\ f ∈ Icc (c + q + r + 1) N /\ I = Icc i f) (pH xH : Finset ℕ -> ℕ) (hHXQ : ∀ S ∈ HXQ, xH S ∈ Icc (c + 1) (c + q - 1) /\ pH S ∈ Icc (c + q + r + 1) N /\ IsDeltaTriplet F S c (pH S) (xH S) /\ ¬ (∀ w, min c (min (pH S) (xH S)) <= w -> w <= max c (max (pH S) (xH S)) ->
       w % Nat.gcd (distNat c (pH S)) (distNat c (xH S)) = c % Nat.gcd (distNat c (pH S)) (distNat c (xH S)) -> w ∈ S) /\
     ∀ a ∈ S, ∀ b ∈ S, c + q + r < a -> b <= c + q + r -> distNat a b < distNat (pH S) (xH S) -> ¬ IsDeltaTriplet Sfam S c a b) :
   (P1.card : ℝ) + (HXQ.card : ℝ) <= (q : ℝ) * ((N - (c + q + r) : ℕ) : ℝ) + 4 * (N : ℝ) := by
 classical
 let Q := Icc (c + 1) (c + q - 1)
 let X := Icc (c + q + r + 1) N
 let Jof : Finset ℕ -> Finset ℕ := fun S => S.filter (fun w => xH S <= w /\ w <= pH S)
 let Hhat := HXQ.filter (fun S => (Jof S).card <= 2)
 let Hbar := HXQ.filter (fun S => ¬ APSet (Jof S))
 have hcovH : HXQ ⊆ Hhat ∪ Hbar := by
   intro S hS
   by_cases h2 : (Jof S).card <= 2
   . exact mem_union_left _ (mem_filter.mpr ⟨hS, h2⟩)
   by_cases hnot : ¬ APSet (Jof S)
   . exact mem_union_right _ (mem_filter.mpr ⟨hS, hnot⟩)
   push Not at hnot h2; exfalso;obtain ⟨hxQ, hpX, hdt, hnofill, hopt⟩ := hHXQ S hS;have hxI := mem_Icc.mp hxQ; have hpI := mem_Icc.mp hpX;have hxJ : xH S ∈ Jof S := mem_filter.mpr ⟨hdt.2.2.1, le_rfl, by omega⟩;have hpJ : pH S ∈ Jof S := mem_filter.mpr ⟨hdt.2.1, by omega, le_rfl⟩
   let JX := (Jof S).filter (fun w => c + q + r < w)
   let JQR := (Jof S).filter (fun w => w <= c + q + r)
   have hJX_ne : JX.Nonempty := ⟨pH S, mem_filter.mpr ⟨hpJ, by omega⟩⟩;have hJQR_ne : JQR.Nonempty := ⟨xH S, mem_filter.mpr ⟨hxJ, by omega⟩⟩
   set a := JX.min' hJX_ne; set b := JQR.max' hJQR_ne
   have haJX := min'_mem JX hJX_ne; have hbJQR := max'_mem JQR hJQR_ne;have haJ := (mem_filter.mp haJX).1; have ha_gt := (mem_filter.mp haJX).2;have hbJ := (mem_filter.mp hbJQR).1; have hb_le := (mem_filter.mp hbJQR).2;have haS := (mem_filter.mp haJ).1; have haB := (mem_filter.mp haJ).2;have hbS := (mem_filter.mp hbJ).1; have hbB := (mem_filter.mp hbJ).2
   have hno_btw : ∀ w ∈ S, ¬ (b < w /\ w < a) := by
     intro w hw ⟨h1, h2⟩;have hwJ : w ∈ Jof S := mem_filter.mpr ⟨hw, by omega, by omega⟩
     by_cases hwr : w <= c + q + r
     . have := le_max' JQR w (mem_filter.mpr ⟨hwJ, hwr⟩); omega
     . have := min'_le JX w (mem_filter.mpr ⟨hwJ, by omega⟩); omega
   have hlt_dist : distNat a b < distNat (pH S) (xH S) := by
     rw [distNat_eq_sub' (by omega), distNat_eq_sub' (by omega)];by_contra hge;have ha_eq : a = pH S := by omega
     have hb_eq : b = xH S := by omega
     have hsub2 : Jof S ⊆ {xH S, pH S} := fun w hw => by
       have hwB := (mem_filter.mp hw).2; have hwS := (mem_filter.mp hw).1
       by_cases h1 : w = xH S; · simp [h1]
       by_cases h2 : w = pH S; · simp [h2]
       exact absurd ⟨by omega, by omega⟩ (hno_btw w hwS)
     have := le_trans (card_le_card hsub2) card_le_two; omega
   have hnotdt : ¬ IsDeltaTriplet Sfam S c a b := hopt a haS b hbS ha_gt hb_le hlt_dist;have hnu := nu_triplet_fill (isWellInter_subset hF hSfam_sub) (hHXQ_sub hS) hdt.1 haS hbS (by omega) (by omega) (by omega) hnotdt
   set g := Nat.gcd (distNat c a) (distNat c b)
   have hg_pos : 1 <= g := hnu.1
   have hg_dvd_ab : g ∣ a - b := by
     have h1 : g ∣ a - c := by rw [<- distNat_eq_sub (by omega)]; exact Nat.gcd_dvd_left _ _
     have h2 : g ∣ b - c := by rw [<- distNat_eq_sub (by omega)]; exact Nat.gcd_dvd_right _ _
     have : a - b = (a - c) - (b - c) := by omega
     rw [this]; exact Nat.dvd_sub h1 h2
   have hg_eq : g = a - b := by
     have hle := Nat.le_of_dvd (by omega) hg_dvd_ab;by_contra hne
     have hbg_mod : (b + g) % g = c % g := by
       have h2 : g ∣ b - c := by rw [<- distNat_eq_sub (by omega)]; exact Nat.gcd_dvd_right _ _
       obtain ⟨t, ht⟩ := h2; have : b + g = c + g * (t + 1) := by rw [mul_add, mul_one]; omega
       rw [this, Nat.add_mul_mod_self_left]
     have hbgS : b + g ∈ S := hnu.2.2.2 (b + g) (by omega) (by omega) hbg_mod;exact hno_btw (b + g) hbgS ⟨by omega, by omega⟩
   obtain ⟨dJ, hdJ1, -, -, hJmem, -⟩ := apSet_canonical hnot (by omega);have haJm := (hJmem a).mp haJ; have hbJm := (hJmem b).mp hbJ;have hdJ_dvd : dJ ∣ a - b := (Nat.modEq_iff_dvd' (by omega)).mp (haJm.2.2.trans hbJm.2.2.symm).symm
   have hdJ_eq : dJ = g := by
     have hle := Nat.le_of_dvd (by omega) hdJ_dvd;by_contra hne;have hbdJ : b + dJ ∈ Jof S := (hJmem (b + dJ)).mpr ⟨by omega, by omega, by rw [Nat.add_mod_right]; exact hbJm.2.2⟩;exact hno_btw (b + dJ) (mem_filter.mp hbdJ).1 ⟨by omega, by omega⟩
   rw [hdJ_eq] at hJmem haJm hbJm
   have hcm_a : a % g = c % g := by
     have h1 : g ∣ a - c := by rw [<- distNat_eq_sub (by omega)]; exact Nat.gcd_dvd_left _ _
     exact ((Nat.modEq_iff_dvd' (by omega)).mpr h1).symm
   have hJg : ∀ w, xH S <= w -> w <= pH S -> w % g = c % g -> w ∈ S := fun w hw1 hw2 hwm =>
     (mem_filter.mp ((hJmem w).mpr ⟨le_trans ((hJmem _).mp hxJ).1 hw1, le_trans hw2 ((hJmem _).mp hpJ).2.1, hwm.trans (hcm_a.symm.trans haJm.2.2)⟩)).1
   have hgx : g ∣ distNat c (xH S) := by
     rw [distNat_eq_sub (by omega)];exact (Nat.modEq_iff_dvd' (by omega)).mp ((((hJmem _).mp hxJ).2.2.trans haJm.2.2.symm).trans hcm_a).symm
   have hgp : g ∣ distNat c (pH S) := by
     rw [distNat_eq_sub (by omega)];exact (Nat.modEq_iff_dvd' (by omega)).mp ((((hJmem _).mp hpJ).2.2.trans haJm.2.2.symm).trans hcm_a).symm
   have hg_dvd_gcd : g ∣ Nat.gcd (distNat c (pH S)) (distNat c (xH S)) := Nat.dvd_gcd hgp hgx;apply hnofill; intro w hw1 hw2 hwm
   have hwm_g : w % g = c % g := by
     obtain ⟨t, ht⟩ := hg_dvd_gcd; rw [ht] at hwm;have := congrArg (· % g) hwm; rwa [Nat.mod_mul_right_mod, Nat.mod_mul_right_mod] at this
   by_cases hwa : w <= a
   . exact hnu.2.2.2 w (by omega) (by omega) hwm_g
   . exact hJg w (by omega) (by omega) hwm_g
 let P1i : ℕ -> Finset (Finset ℕ) := fun i => P1.filter (fun I => ∃ f, I = Icc i f)
 let Hhati : ℕ -> Finset (Finset ℕ) := fun i => Hhat.filter (fun S => xH S = i)
 let Hbari : ℕ -> Finset (Finset ℕ) := fun i => Hbar.filter (fun S => xH S = i)
 have hpH_inj : ∀ i, Set.InjOn pH ((Hhati i ∪ Hbari i : Finset (Finset ℕ)) : Set (Finset ℕ)) := by
   intro i S1 h1 S2 h2 heq; by_contra hne;have hS1 : S1 ∈ HXQ /\ xH S1 = i := by rcases mem_union.mp (mem_coe.mp h1) with h | h <;> exact ⟨(mem_filter.mp (mem_filter.mp h).1).1, (mem_filter.mp h).2⟩
   have hS2 : S2 ∈ HXQ /\ xH S2 = i := by rcases mem_union.mp (mem_coe.mp h2) with h | h <;> exact ⟨(mem_filter.mp (mem_filter.mp h).1).1, (mem_filter.mp h).2⟩
   have hdt1 := (hHXQ S1 hS1.1).2.2.1; have hdt2 := (hHXQ S2 hS2.1).2.2.1;exact hdt1.2.2.2.2.2.2 S2 (hSfam_sub (hHXQ_sub hS2.1)) (Ne.symm hne) ⟨hdt2.1, heq ▸ hdt2.2.1, (hS1.2.trans hS2.2.symm) ▸ hdt2.2.2.1⟩
 have hP1i_inj : ∀ i, Set.InjOn (fun I : Finset ℕ => if h : I.Nonempty then I.max' h else 0) (P1i i : Set (Finset ℕ)) := by
   intro i I1 h1 I2 h2 heq; dsimp only at heq;obtain ⟨hI1P, f1, h1eq⟩ := mem_filter.mp (mem_coe.mp h1);obtain ⟨hI2P, f2, h2eq⟩ := mem_filter.mp (mem_coe.mp h2);obtain ⟨i1, f1', hi1, hf1, h1'⟩ := hP1 I1 hI1P;obtain ⟨i2, f2', hi2, hf2, h2'⟩ := hP1 I2 hI2P;have hne1 : I1.Nonempty := ⟨i1, h1'.symm ▸ mem_Icc.mpr ⟨le_rfl, by have := mem_Icc.mp hi1; have := mem_Icc.mp hf1; omega⟩⟩;have hne2 : I2.Nonempty := ⟨i2, h2'.symm ▸ mem_Icc.mpr ⟨le_rfl, by have := mem_Icc.mp hi2; have := mem_Icc.mp hf2; omega⟩⟩
   have hif1 : i <= f1 := by
     have hm : i1 ∈ Icc i f1 := h1eq ▸ h1'.symm ▸ mem_Icc.mpr ⟨le_rfl, by have := mem_Icc.mp hi1; have := mem_Icc.mp hf1; omega⟩;have := mem_Icc.mp hm; omega
   have hif2 : i <= f2 := by
     have hm : i2 ∈ Icc i f2 := h2eq ▸ h2'.symm ▸ mem_Icc.mpr ⟨le_rfl, by have := mem_Icc.mp hi2; have := mem_Icc.mp hf2; omega⟩;have := mem_Icc.mp hm; omega
   have hmax1 : I1.max' hne1 = f1 := le_antisymm (mem_Icc.mp (show I1.max' hne1 ∈ Icc i f1 from h1eq ▸ max'_mem I1 hne1)).2 (le_max' I1 f1 (h1eq.symm ▸ mem_Icc.mpr ⟨hif1, le_rfl⟩));have hmax2 : I2.max' hne2 = f2 := le_antisymm (mem_Icc.mp (show I2.max' hne2 ∈ Icc i f2 from h2eq ▸ max'_mem I2 hne2)).2 (le_max' I2 f2 (h2eq.symm ▸ mem_Icc.mpr ⟨hif2, le_rfl⟩));rw [dif_pos hne1, dif_pos hne2, hmax1, hmax2] at heq; rw [h1eq, h2eq, heq]
 have htriple : ∀ i' i, i' ∈ Q -> i ∈ Q -> i' < i -> (P1i i).Nonempty -> (Hhati i').card + (P1i i).card + (Hbari i).card <= N - (c + q + r) + 1 := by
   intro i' i hi'Q hiQ hlt hPne
   let maxOf : Finset ℕ -> ℕ := fun I => if h : I.Nonempty then I.max' h else 0
   obtain ⟨Imin, hImin, hImin_le⟩ := exists_min_image (P1i i) maxOf hPne;obtain ⟨hIminP, lmin, hImin_eq⟩ := mem_filter.mp hImin
   obtain ⟨i0, f0, hi0, hf0, h0eq⟩ := hP1 Imin hIminP
   have hlmin_eq : lmin = f0 /\ i = i0 := by
     have hi0f0 : i0 <= f0 := by have := mem_Icc.mp hi0; have := mem_Icc.mp hf0; omega
     have h1 : i0 ∈ Icc i lmin := hImin_eq ▸ h0eq.symm ▸ mem_Icc.mpr ⟨le_rfl, hi0f0⟩;have h2 : f0 ∈ Icc i lmin := hImin_eq ▸ h0eq.symm ▸ mem_Icc.mpr ⟨hi0f0, le_rfl⟩;have h3 : i ∈ Icc i0 f0 := h0eq ▸ hImin_eq.symm ▸ mem_Icc.mpr ⟨le_rfl, by have := mem_Icc.mp h1; have := mem_Icc.mp h2; omega⟩;have h4 : lmin ∈ Icc i0 f0 := h0eq ▸ hImin_eq.symm ▸ mem_Icc.mpr ⟨by have := mem_Icc.mp h1; have := mem_Icc.mp h2; omega, le_rfl⟩;have := mem_Icc.mp h1; have := mem_Icc.mp h2; have := mem_Icc.mp h3; have := mem_Icc.mp h4; omega
   have hlminX : lmin ∈ X := hlmin_eq.1 ▸ hf0;have hlminI := mem_Icc.mp hlminX
   have hpK_ex : ∃ pK, lmin < pK /\ pK <= N + 1 /\ (∀ I ∈ P1i i, ∀ f, I = Icc i f -> lmin <= f /\ f < pK) /\ (∀ S ∈ Hbari i, pK <= pH S /\ pH S <= N) := by
     have hmax_I : ∀ I ∈ P1i i, ∀ f, I = Icc i f -> lmin <= f := fun I hI f hIeq => by
       obtain ⟨hIP, -⟩ := mem_filter.mp hI;obtain ⟨ia, fa, hia, hfa, haeq⟩ := hP1 I hIP;have hneI : I.Nonempty := ⟨ia, haeq.symm ▸ mem_Icc.mpr ⟨le_rfl, by have := mem_Icc.mp hia; have := mem_Icc.mp hfa; omega⟩⟩;have hneM : Imin.Nonempty := ⟨i, hImin_eq.symm ▸ mem_Icc.mpr ⟨le_rfl, by have := mem_Icc.mp hiQ; omega⟩⟩;have hif : i <= f := by have hm : ia ∈ Icc i f := hIeq ▸ haeq.symm ▸ mem_Icc.mpr ⟨le_rfl, by have := mem_Icc.mp hia; have := mem_Icc.mp hfa; omega⟩; have := mem_Icc.mp hm; omega
       have hm1 : I.max' hneI = f := le_antisymm (mem_Icc.mp (show I.max' hneI ∈ Icc i f from hIeq ▸ max'_mem I hneI)).2 (le_max' I f (hIeq.symm ▸ mem_Icc.mpr ⟨hif, le_rfl⟩));have hm2 : Imin.max' hneM = lmin := le_antisymm (mem_Icc.mp (show Imin.max' hneM ∈ Icc i lmin from hImin_eq ▸ max'_mem Imin hneM)).2 (le_max' Imin lmin (hImin_eq.symm ▸ mem_Icc.mpr ⟨by have := mem_Icc.mp hiQ; omega, le_rfl⟩));have := hImin_le I hI; dsimp only [maxOf] at this; rwa [dif_pos hneM, dif_pos hneI, hm1, hm2] at this
     have hAP_trunc : ∀ (I K : Finset ℕ) (f : ℕ), I ∈ P1i i -> I = Icc i f -> K ∈ Hbari i -> f < pH K := by
       intro I K f hI hIeq hK; by_contra hge; push Not at hge;obtain ⟨hKbar, hxK⟩ := mem_filter.mp hK; obtain ⟨hKHXQ, hnotAP⟩ := mem_filter.mp hKbar
       have hIK_ne : I ≠ K := fun h => by
         have hcK := (hHXQ K hKHXQ).2.2.1.1; rw [<- h, hIeq, mem_Icc] at hcK; have := mem_Icc.mp hiQ; omega
       have hAP := hF.2 I (hP1_sub (mem_filter.mp hI).1) K (hSfam_sub (hHXQ_sub hKHXQ)) hIK_ne;obtain ⟨a, d, P, hP, hP0, hmem⟩ := hAP;apply hnotAP
       refine ⟨a, d, fun n => P n /\ a + n * d <= pH K, fun n m ⟨hn, hle⟩ hmn =>
         ⟨hP n m hn hmn, by have := Nat.mul_le_mul_right d hmn; omega⟩, ?_, fun w => ?_⟩
       . refine ⟨hP0, ?_⟩
         have ha_mem : a ∈ I ∩ K := (hmem a).mpr ⟨0, hP0, by simp⟩;have haI := mem_Icc.mp (hIeq ▸ mem_of_mem_inter_left ha_mem);have hK_x : xH K ∈ I ∩ K := mem_inter.mpr ⟨hIeq.symm ▸ mem_Icc.mpr ⟨by omega, by have := mem_Icc.mp (hHXQ K hKHXQ).2.1; omega⟩, (hHXQ K hKHXQ).2.2.1.2.2.1⟩;obtain ⟨nx, hnx, hxeq⟩ := (hmem (xH K)).mp hK_x;have : a <= xH K := by omega
         have := mem_Icc.mp (hHXQ K hKHXQ).1; have := mem_Icc.mp (hHXQ K hKHXQ).2.1; omega
       . simp only [Jof, mem_filter]
         constructor
         . rintro ⟨hwK, hw1, hw2⟩
           have hwIK : w ∈ I ∩ K := mem_inter.mpr ⟨hIeq.symm ▸ mem_Icc.mpr ⟨by omega, by omega⟩, hwK⟩;obtain ⟨n, hn, rfl⟩ := (hmem w).mp hwIK; exact ⟨n, ⟨hn, hw2⟩, rfl⟩
         . rintro ⟨n, ⟨hn, hle⟩, rfl⟩
           have hwIK : a + n * d ∈ I ∩ K := (hmem _).mpr ⟨n, hn, rfl⟩;have hwI := mem_Icc.mp (hIeq ▸ mem_of_mem_inter_left hwIK);exact ⟨mem_of_mem_inter_right hwIK, by omega, hle⟩
     rcases (Hbari i).eq_empty_or_nonempty with hE | hHne
     . refine ⟨N + 1, by omega, le_rfl, fun I hI f hIeq => ⟨hmax_I I hI f hIeq, ?_⟩, fun S hS => by rw [hE] at hS; exact absurd hS (notMem_empty _)⟩
       obtain ⟨ia, fa, -, hfa, haeq⟩ := hP1 I (mem_filter.mp hI).1
       have hleN : f <= N := by
         have hm : f ∈ I := hIeq.symm ▸ mem_Icc.mpr ⟨by have := hmax_I I hI f hIeq; have := mem_Icc.mp hiQ; omega, le_rfl⟩;exact (mem_Icc.mp (hF.1 I (hP1_sub (mem_filter.mp hI).1) hm)).2
       omega
     . obtain ⟨K, hK, hKmin⟩ := exists_min_image (Hbari i) pH hHne
       have hpK_I := mem_Icc.mp (hHXQ K (mem_filter.mp (mem_filter.mp hK).1).1).2.1;exact ⟨pH K, hAP_trunc Imin K lmin hImin hImin_eq hK, by omega, fun I hI f hIeq => ⟨hmax_I I hI f hIeq, hAP_trunc I K f hI hIeq hK⟩, fun S hS => ⟨hKmin S hS, (mem_Icc.mp (hHXQ S (mem_filter.mp (mem_filter.mp hS).1).1).2.1).2⟩⟩
   obtain ⟨pK, hlmin_lt, hpK_N, hP1_rng, hHbar_rng⟩ := hpK_ex
   have hc1 : (Hhati i').card <= lmin - (c + q + r) := by
     have hle : (Hhati i').card <= (Icc (c + q + r + 1) lmin).card := by
       refine card_le_card_of_injOn pH (fun S hS => ?_) (fun S1 h1 S2 h2 heq =>
         hpH_inj i' (mem_coe.mpr (mem_union_left _ (mem_coe.mp h1))) (mem_coe.mpr (mem_union_left _ (mem_coe.mp h2))) heq)
       obtain ⟨hShat, hxS⟩ := mem_filter.mp (mem_coe.mp hS);obtain ⟨hSHXQ, hJ2⟩ := mem_filter.mp hShat;have hpI := mem_Icc.mp (hHXQ S hSHXQ).2.1
       refine mem_coe.mpr (mem_Icc.mpr ⟨hpI.1, ?_⟩)
       by_contra hgt; push Not at hgt
       have hSI : S ≠ Imin := fun h => by
         have hcS := (hHXQ S hSHXQ).2.2.1.1; rw [h, hImin_eq, mem_Icc] at hcS; have := mem_Icc.mp hiQ; omega
       obtain ⟨w, hw⟩ := wellInter_meet hF (hSfam_sub (hHXQ_sub hSHXQ)) (hP1_sub hIminP) hSI;have hwI := mem_Icc.mp (hImin_eq ▸ mem_of_mem_inter_right hw);have hwJ : w ∈ Jof S := mem_filter.mpr ⟨mem_of_mem_inter_left hw, by omega, by omega⟩;have hdt := (hHXQ S hSHXQ).2.2.1
       have hsub3 : ({xH S, w, pH S} : Finset ℕ) ⊆ Jof S := fun z hz => by
         simp only [mem_insert, mem_singleton] at hz
         rcases hz with rfl | rfl | rfl
         . exact mem_filter.mpr ⟨hdt.2.2.1, le_rfl, by omega⟩
         . exact hwJ
         . exact mem_filter.mpr ⟨hdt.2.1, by omega, le_rfl⟩
       have hc3 : ({xH S, w, pH S} : Finset ℕ).card = 3 := by rw [card_insert_of_notMem (by simp; omega), card_pair (by omega)]
       have := card_le_card hsub3; omega
     rw [Nat.card_Icc] at hle; omega
   have hc2 : (P1i i).card <= pK - lmin := by
     have hle : (P1i i).card <= (Icc lmin (pK - 1)).card := by
       refine card_le_card_of_injOn (fun I : Finset ℕ => if h : I.Nonempty then I.max' h else 0) (fun I hI => ?_) (hP1i_inj i)
       obtain ⟨hIP, f, hIeq⟩ := mem_filter.mp (mem_coe.mp hI);obtain ⟨hl1, hl2⟩ := hP1_rng I (mem_coe.mp hI) f hIeq;have hneI : I.Nonempty := ⟨i, hIeq.symm ▸ mem_Icc.mpr ⟨le_rfl, by have := mem_Icc.mp hiQ; omega⟩⟩;have hmaxI : I.max' hneI = f := le_antisymm (mem_Icc.mp (show I.max' hneI ∈ Icc i f from hIeq ▸ max'_mem I hneI)).2 (le_max' I f (hIeq.symm ▸ mem_Icc.mpr ⟨by have := mem_Icc.mp hiQ; omega, le_rfl⟩));exact mem_coe.mpr (by dsimp only; rw [dif_pos hneI, hmaxI]; exact mem_Icc.mpr ⟨hl1, by omega⟩)
     rw [Nat.card_Icc] at hle; omega
   have hc3 : (Hbari i).card <= N + 1 - pK := by
     have hle : (Hbari i).card <= (Icc pK N).card := by refine card_le_card_of_injOn pH (fun S hS => mem_coe.mpr (mem_Icc.mpr (hHbar_rng S (mem_coe.mp hS)))) (fun S1 h1 S2 h2 heq => hpH_inj i (mem_coe.mpr (mem_union_right _ (mem_coe.mp h1))) (mem_coe.mpr (mem_union_right _ (mem_coe.mp h2))) heq)
     rw [Nat.card_Icc] at hle; exact hle
   omega
 let Qne := Q.filter (fun i => (P1i i).Nonempty)
 let Qemp := Q.filter (fun i => ¬ (P1i i).Nonempty)
 have hP1_cov : P1 ⊆ Qne.biUnion P1i := fun I hI => by
   obtain ⟨i, f, hiQ, -, hIeq⟩ := hP1 I hI;exact mem_biUnion.mpr ⟨i, mem_filter.mpr ⟨hiQ, ⟨I, mem_filter.mpr ⟨hI, f, hIeq⟩⟩⟩, mem_filter.mpr ⟨hI, f, hIeq⟩⟩
 have hH_cov_i : Hhat ∪ Hbar ⊆ Q.biUnion (fun i => Hhati i ∪ Hbari i) := fun S hS => by
   rcases mem_union.mp hS with h1 | h2
   . exact mem_biUnion.mpr ⟨xH S, (hHXQ S (mem_filter.mp h1).1).1, mem_union_left _ (mem_filter.mpr ⟨h1, rfl⟩)⟩
   . exact mem_biUnion.mpr ⟨xH S, (hHXQ S (mem_filter.mp h2).1).1, mem_union_right _ (mem_filter.mpr ⟨h2, rfl⟩)⟩
 have hQemp_bd : ∀ i ∈ Qemp, (Hhati i ∪ Hbari i).card <= N - (c + q + r) := fun i _ => by
   have hle : (Hhati i ∪ Hbari i).card <= X.card := card_le_card_of_injOn pH (fun S hS => by
     rcases mem_union.mp (mem_coe.mp hS) with h | h <;>
       exact mem_coe.mpr (hHXQ S (mem_filter.mp (mem_filter.mp h).1).1).2.1) (hpH_inj i)
   rwa [Nat.card_Icc, show N + 1 - (c + q + r + 1) = N - (c + q + r) by omega] at hle
 have hQne_bd : ∑ i ∈ Qne, ((P1i i).card + (Hhati i).card + (Hbari i).card) <= Qne.card * (N - (c + q + r) + 1) + 3 * N := by
   let sl := Qne.sort (· <= ·)
   have hsl_len : sl.length = Qne.card := length_sort _;have hsl_nd : sl.Nodup := Qne.sort_nodup (· <= ·);have hsl_lt : sl.Pairwise (· < ·) := ((Qne.pairwise_sort (· <= ·)).and hsl_nd).imp fun p => lt_of_le_of_ne p.1 p.2
   have hsum_eq : ∀ f : ℕ -> ℕ, ∑ i ∈ Qne, f i = ∑ j ∈ range sl.length, f (if h : j < sl.length then sl.get ⟨j, h⟩ else 0) := fun f => by
     have h1 : Qne = (range sl.length).image (fun j => if h : j < sl.length then sl.get ⟨j, h⟩ else 0) := by
       ext x; simp only [mem_image, mem_range]
       constructor
       . intro hx; obtain ⟨⟨j, hj⟩, rfl⟩ := List.mem_iff_get.mp ((mem_sort (· <= ·)).mpr hx)
         exact ⟨j, hj, dif_pos hj⟩
       . rintro ⟨j, hj, rfl⟩; rw [dif_pos hj]; exact (mem_sort (· <= ·)).mp (List.get_mem sl ⟨j, hj⟩)
     have hinj : Set.InjOn (fun j => if h : j < sl.length then sl.get ⟨j, h⟩ else 0) (range sl.length : Set ℕ) := by
       intro j1 h1 j2 h2 heq; dsimp only at heq;have hj1 := mem_range.mp (mem_coe.mp h1); have hj2 := mem_range.mp (mem_coe.mp h2);rw [dif_pos hj1, dif_pos hj2] at heq;exact congrArg Fin.val ((List.nodup_iff_injective_get.mp hsl_nd) heq)
     conv_lhs => rw [h1, sum_image hinj]
   rcases Nat.eq_zero_or_pos Qne.card with h0 | hpos
   . rw [card_eq_zero.mp h0]; simp
   have hleN_each : ∀ i ∈ Qne, (P1i i).card <= N /\ (Hhati i).card <= N /\ (Hbari i).card <= N := fun i _ => by
     have h1 : (P1i i).card <= (Icc 1 N).card := card_le_card_of_injOn (fun I : Finset ℕ => if h : I.Nonempty then I.max' h else 0) (fun I hI => by
         obtain ⟨hIP, -, -⟩ := mem_filter.mp (mem_coe.mp hI);obtain ⟨ia, fa, hia, hfa, haeq⟩ := hP1 I hIP;have hneI : I.Nonempty := ⟨ia, haeq.symm ▸ mem_Icc.mpr ⟨le_rfl, by have := mem_Icc.mp hia; have := mem_Icc.mp hfa; omega⟩⟩
         exact mem_coe.mpr (by dsimp only; rw [dif_pos hneI]; exact hF.1 I (hP1_sub hIP) (max'_mem I hneI))) (hP1i_inj i)
     have h2 : (Hhati i).card <= X.card := card_le_card_of_injOn pH (fun S hS => mem_coe.mpr (hHXQ S (mem_filter.mp (mem_filter.mp (mem_coe.mp hS)).1).1).2.1) (fun S1 h1 S2 h2 heq => hpH_inj i (mem_coe.mpr (mem_union_left _ (mem_coe.mp h1))) (mem_coe.mpr (mem_union_left _ (mem_coe.mp h2))) heq);have h3 : (Hbari i).card <= X.card := card_le_card_of_injOn pH (fun S hS => mem_coe.mpr (hHXQ S (mem_filter.mp (mem_filter.mp (mem_coe.mp hS)).1).1).2.1) (fun S1 h1 S2 h2 heq => hpH_inj i (mem_coe.mpr (mem_union_right _ (mem_coe.mp h1))) (mem_coe.mpr (mem_union_right _ (mem_coe.mp h2))) heq)
     rw [Nat.card_Icc, Nat.add_sub_cancel] at h1; rw [Nat.card_Icc] at h2 h3; omega
   let k := sl.length
   let idx : ℕ -> ℕ := fun j => if h : j < k then sl.get ⟨j, h⟩ else 0
   have hidx_Qne : ∀ j < k, idx j ∈ Qne := fun j hj => by
     dsimp only [idx]; rw [dif_pos hj]; exact (mem_sort (· <= ·)).mp (List.get_mem sl ⟨j, hj⟩)
   have hsum_P : ∑ i ∈ Qne, (P1i i).card = ∑ j ∈ range k, (P1i (idx j)).card := hsum_eq _;have hsum_Hh : ∑ i ∈ Qne, (Hhati i).card = ∑ j ∈ range k, (Hhati (idx j)).card := hsum_eq _;have hsum_Hb : ∑ i ∈ Qne, (Hbari i).card = ∑ j ∈ range k, (Hbari (idx j)).card := hsum_eq _
   have hshift : ∑ j ∈ range k, ((P1i (idx j)).card + (Hhati (idx j)).card + (Hbari (idx j)).card) = (P1i (idx 0)).card + (Hbari (idx 0)).card + (Hhati (idx (k - 1))).card + ∑ j ∈ range (k - 1), ((Hhati (idx j)).card + (P1i (idx (j + 1))).card + (Hbari (idx (j + 1))).card) := by
     have hk1 : k = (k - 1) + 1 := by omega
     have hP_s : ∑ j ∈ range k, (P1i (idx j)).card = (P1i (idx 0)).card + ∑ j ∈ range (k - 1), (P1i (idx (j + 1))).card := by
       conv_lhs => rw [hk1, sum_range_succ']
       omega
     have hHb_s : ∑ j ∈ range k, (Hbari (idx j)).card = (Hbari (idx 0)).card + ∑ j ∈ range (k - 1), (Hbari (idx (j + 1))).card := by
       conv_lhs => rw [hk1, sum_range_succ']
       omega
     have hHh_s : ∑ j ∈ range k, (Hhati (idx j)).card = (∑ j ∈ range (k - 1), (Hhati (idx j)).card) + (Hhati (idx (k - 1))).card := by
       conv_lhs => rw [hk1, sum_range_succ]
     simp only [sum_add_distrib] at hP_s hHb_s hHh_s ⊢; omega
   have hpair_le : ∑ j ∈ range (k - 1), ((Hhati (idx j)).card + (P1i (idx (j + 1))).card + (Hbari (idx (j + 1))).card) <= (k - 1) * (N - (c + q + r) + 1) := by
     calc ∑ j ∈ range (k - 1), ((Hhati (idx j)).card + (P1i (idx (j + 1))).card + (Hbari (idx (j + 1))).card)
         <= ∑ _j ∈ range (k - 1), (N - (c + q + r) + 1) := sum_le_sum fun j hj => by
           have hjlt := mem_range.mp hj;have h1 := mem_filter.mp (hidx_Qne j (by omega));have h2 := mem_filter.mp (hidx_Qne (j + 1) (by omega))
           have hlt' : idx j < idx (j + 1) := by
             dsimp only [idx]; rw [dif_pos (by omega), dif_pos (by omega)];exact List.pairwise_iff_get.mp hsl_lt ⟨j, by omega⟩ ⟨j + 1, by omega⟩ (by simp)
           exact htriple (idx j) (idx (j + 1)) h1.1 h2.1 hlt' h2.2
       _ = (k - 1) * (N - (c + q + r) + 1) := by rw [sum_const, card_range, smul_eq_mul]
   have h0 := hleN_each (idx 0) (hidx_Qne 0 (by omega));have hlast := hleN_each (idx (k - 1)) (hidx_Qne (k - 1) (by omega));rw [sum_add_distrib, sum_add_distrib, hsum_P, hsum_Hh, hsum_Hb, <- sum_add_distrib, <- sum_add_distrib, hshift];have hkl : k = Qne.card := hsl_len;have h1 : (k - 1) * (N - (c + q + r) + 1) <= Qne.card * (N - (c + q + r) + 1) := Nat.mul_le_mul_right _ (by omega);omega
 have hQ_part : Qne.card + Qemp.card = Q.card := by
   have hdisj : Disjoint Qne Qemp := by rw [disjoint_left]; intro i h1 h2; exact (mem_filter.mp h2).2 (mem_filter.mp h1).2
   have hu : Qne ∪ Qemp = Q := by ext i; simp only [Qne, Qemp, mem_union, mem_filter]; tauto
   rw [<- card_union_of_disjoint hdisj, hu]
 have hQ_le : Q.card <= q := by dsimp only [Q]; rw [Nat.card_Icc]; omega
 have htot_nat : P1.card + HXQ.card <= q * (N - (c + q + r)) + 4 * N := by
   have hP1_le : P1.card <= ∑ i ∈ Qne, (P1i i).card := le_trans (card_le_card hP1_cov) card_biUnion_le
   have hHXQ_le : HXQ.card <= (∑ i ∈ Qne, ((Hhati i).card + (Hbari i).card)) + ∑ i ∈ Qemp, (Hhati i ∪ Hbari i).card := by
     have h1 := le_trans (card_le_card hcovH) (le_trans (card_le_card hH_cov_i) card_biUnion_le);have hdisj : Disjoint Qne Qemp := by rw [disjoint_left]; intro i h1 h2; exact (mem_filter.mp h2).2 (mem_filter.mp h1).2
     have hu : Q = Qne ∪ Qemp := by ext i; simp only [Qne, Qemp, mem_union, mem_filter]; tauto
     rw [hu, sum_union hdisj] at h1;exact le_trans h1 (Nat.add_le_add_right (sum_le_sum fun i _ => card_union_le _ _) _)
   have hQemp_sum : ∑ i ∈ Qemp, (Hhati i ∪ Hbari i).card <= Qemp.card * (N - (c + q + r)) := by
     calc ∑ i ∈ Qemp, (Hhati i ∪ Hbari i).card <= ∑ _i ∈ Qemp, (N - (c + q + r)) := sum_le_sum hQemp_bd
       _ = Qemp.card * (N - (c + q + r)) := by rw [sum_const, smul_eq_mul]
   have hadd_sum : (∑ i ∈ Qne, (P1i i).card) + ∑ i ∈ Qne, ((Hhati i).card + (Hbari i).card) = ∑ i ∈ Qne, ((P1i i).card + (Hhati i).card + (Hbari i).card) := by simp only [sum_add_distrib]; omega
   have hmul_eq : Qne.card * (N - (c + q + r) + 1) + Qemp.card * (N - (c + q + r)) = Q.card * (N - (c + q + r)) + Qne.card := by
     have : Qne.card * (N - (c + q + r) + 1) = Qne.card * (N - (c + q + r)) + Qne.card := by ring
     rw [this, <- hQ_part]; ring
   have hqmul : Q.card * (N - (c + q + r)) <= q * (N - (c + q + r)) := Nat.mul_le_mul_right _ hQ_le;have hQneN : Qne.card <= N := by omega
   omega
 exact_mod_cast htot_nat
lemma card_AP_rect_endpoints {N d0 a1 a2 b1 b2 : ℕ} (hN : 1 <= N) {F A : Finset (Finset ℕ)} (hF : IsWellInter N F) (hAsub : A ⊆ F) (hd0 : d0 = 1 \/ d0 = 2) (hA : ∀ S ∈ A, 3 <= S.card /\ APSet S /\ (∃ hne : S.Nonempty, S.min' hne ∈ Icc a1 a2 /\ S.max' hne ∈ Icc b1 b2) /\ (d0 = 2 -> ¬ ∃ l r, S = Icc l r)) : (A.card : ℝ) <= ((∑ d ∈ Icc d0 N, (1 : ℝ) / (d : ℝ) ^ 2) * ((a2 + 1 - a1 : ℕ) : ℝ) * ((b2 + 1 - b1 : ℕ) : ℝ)) + (((a2 + 1 - a1 : ℕ) : ℝ) + ((b2 + 1 - b1 : ℕ) : ℝ)) * (1 + Real.log N) + (N : ℝ) := by
 classical
 have hstep_ex : ∀ S : {S // S ∈ A}, ∃ d, d0 <= d /\ d <= N /\ (∀ x ∈ S.1, ∀ y ∈ S.1, x % d = y % d /\ (∀ z, min x y <= z -> z <= max x y -> z % d = x % d -> z ∈ S.1)) := by
   rintro ⟨S, hS⟩; obtain ⟨hS3, hAP, -, hnoI⟩ := hA S hS;obtain ⟨d, hd1, -, -, hmem, hcard_eq⟩ := apSet_canonical hAP (by omega)
   set lo := S.min' (card_pos.mp (by omega)); set hi := S.max' (card_pos.mp (by omega))
   have hd_ge : d0 <= d := by
     rcases hd0 with rfl | rfl
     . omega
     . by_contra hlt; have hd_eq : d = 1 := by omega
       apply hnoI rfl; refine ⟨lo, hi, ?_⟩
       ext z; rw [hmem z, mem_Icc, hd_eq]; simp only [Nat.mod_one, and_true]
   have hhiN : hi <= N := (mem_Icc.mp (hF.1 S (hAsub hS) (max'_mem _ _))).2;have hdN : d <= N := by have : 1 * d <= (S.card - 1) * d := Nat.mul_le_mul_right d (by omega); omega
   refine ⟨d, hd_ge, hdN, fun x hx y hy => ?_⟩
   have hxm := (hmem x).mp hx; have hym := (hmem y).mp hy;exact ⟨hxm.2.2.trans hym.2.2.symm, fun z hz1 hz2 hzm => (hmem z).mpr ⟨by omega, by omega, hzm.trans hxm.2.2⟩⟩
 choose step hstep using hstep_ex
 let Ad : ℕ -> Finset (Finset ℕ) := fun d => (A.attach.filter (fun S => step S = d)).image Subtype.val
 have hcov : A ⊆ (Icc d0 N).biUnion Ad := fun S hS =>
   mem_biUnion.mpr ⟨step ⟨S, hS⟩, mem_Icc.mpr ⟨(hstep ⟨S, hS⟩).1, (hstep ⟨S, hS⟩).2.1⟩, mem_image.mpr ⟨⟨S, hS⟩, mem_filter.mpr ⟨mem_attach _ _, rfl⟩, rfl⟩⟩
 have hle : (A.card : ℝ) <= ∑ d ∈ Icc d0 N, ((Ad d).card : ℝ) := by exact_mod_cast le_trans (card_le_card hcov) card_biUnion_le
 have hterm : ∀ d ∈ Icc d0 N, ((Ad d).card : ℝ) <= (((a2 + 1 - a1 : ℕ) : ℝ) / (d : ℝ) + 1) * (((b2 + 1 - b1 : ℕ) : ℝ) / (d : ℝ) + 1) := by
   intro d hd
   refine card_AP_step_endpoints (by have := (mem_Icc.mp hd).1; rcases hd0 with rfl | rfl <;> omega) (isWellInter_subset hF (fun S hS => by obtain ⟨S', -, rfl⟩ := mem_image.mp hS; exact hAsub S'.2)) (fun S hS => by
       obtain ⟨S', hS'f, rfl⟩ := mem_image.mp hS;have hsp := (hstep S').2.2; rw [(mem_filter.mp hS'f).2] at hsp
       exact ⟨by have := (hA S'.1 S'.2).1; omega, (hA S'.1 S'.2).2.1, hsp⟩)
     (fun S hS => by obtain ⟨S', -, rfl⟩ := mem_image.mp hS; exact (hA S'.1 S'.2).2.2.1)
 refine le_trans hle (le_trans (sum_le_sum hterm) ?_)
 have hexp : ∑ d ∈ Icc d0 N, (((a2 + 1 - a1 : ℕ) : ℝ) / (d : ℝ) + 1) * (((b2 + 1 - b1 : ℕ) : ℝ) / (d : ℝ) + 1) = ((∑ d ∈ Icc d0 N, (1 : ℝ) / (d : ℝ) ^ 2) * ((a2 + 1 - a1 : ℕ) : ℝ) * ((b2 + 1 - b1 : ℕ) : ℝ)) + (((a2 + 1 - a1 : ℕ) : ℝ) + ((b2 + 1 - b1 : ℕ) : ℝ)) * (∑ d ∈ Icc d0 N, (1 : ℝ) / (d : ℝ)) + (∑ _d ∈ Icc d0 N, (1 : ℝ)) := by
   rw [sum_mul, sum_mul, mul_sum, <- sum_add_distrib, <- sum_add_distrib]
   refine sum_congr rfl fun d _ => ?_; ring
 rw [hexp];have hharm : ∑ d ∈ Icc d0 N, (1 : ℝ) / (d : ℝ) <= 1 + Real.log N := le_trans (sum_le_sum_of_subset_of_nonneg (fun d hd => mem_Icc.mpr ⟨by have := (mem_Icc.mp hd).1; rcases hd0 with rfl | rfl <;> omega, (mem_Icc.mp hd).2⟩) (fun _ _ _ => by positivity)) (harmonic_le_one_add_log N hN)
 have h1s : ∑ _d ∈ Icc d0 N, (1 : ℝ) <= (N : ℝ) := by rw [sum_const, nsmul_eq_mul, mul_one, Nat.card_Icc]; exact_mod_cast (by rcases hd0 with rfl | rfl <;> omega : N + 1 - d0 <= N)
 have hnn : 0 <= ((a2 + 1 - a1 : ℕ) : ℝ) + ((b2 + 1 - b1 : ℕ) : ℝ) := by positivity
 have hmul := mul_le_mul_of_nonneg_left hharm hnn;linarith [hmul, h1s]
lemma thm41_step_vi_sum {N c q r x : ℕ} (hN : 100 <= N) (hsum_N : c + q + r + x = N) {a b : ℕ -> ℝ} (ha : ∀ d ∈ Icc 1 N, ∃ sd : ℕ, sd <= r /\ a d + b d <= ((c : ℝ) * ((r : ℝ) - (sd : ℝ)) + moebius2Sum N * ((sd : ℝ) * ((q : ℝ) + (c : ℝ) + (r : ℝ)) - (sd : ℝ) ^ 2 / 2)) / (d : ℝ) ^ 2 + 40 * (N : ℝ) * (1 + Real.log N) / (d : ℝ) + 12) : (∑ d ∈ Icc 1 N, a d) + (∑ d ∈ Icc 1 N, b d) + zeta2Sum N * (x : ℝ) * ((q : ℝ) + (c : ℝ)) + (r : ℝ) * (x : ℝ) <= (N : ℝ) ^ 2 / 2 - (((c : ℝ) + (q : ℝ)) ^ 2 + (x : ℝ) ^ 2) / 200 + 14 * (N : ℝ) * Real.sqrt N + 40 * (N : ℝ) * (1 + Real.log N) ^ 2 + 12 * (N : ℝ) := by
 set Z := zeta2Sum N
 set M := moebius2Sum N
 have hZ_bds := zeta2Sum_bounds hN;have hMZ := moebius2Sum_mul_zeta2Sum_approx (by omega : 1 <= N);have hlog_nn : 0 <= Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 <= N));have hZpos : 0 < Z := by linarith
 have hM_approx : M <= 1 / Z + 7 / (Z * Real.sqrt N) := by
   have h1 : M * Z - 1 <= 7 / Real.sqrt N := (abs_le.mp hMZ).2;rw [show 1 / Z + 7 / (Z * Real.sqrt N) = (1 + 7 / Real.sqrt N) / Z by field_simp];rw [le_div_iff₀ hZpos]; linarith
 have hterm_comb : ∀ d ∈ Icc 1 N, a d + b d + (1 / (Z * (d : ℝ) ^ 2)) * (Z * (x : ℝ) * ((q : ℝ) + (c : ℝ)) + (r : ℝ) * (x : ℝ)) <= (1 / (Z * (d : ℝ) ^ 2)) * ((N : ℝ) ^ 2 / 2 - (((c : ℝ) + (q : ℝ)) ^ 2 + (x : ℝ) ^ 2) / 200) + (7 / (Z * Real.sqrt N * (d : ℝ) ^ 2)) * (N : ℝ) ^ 2 + 40 * (N : ℝ) * (1 + Real.log N) / (d : ℝ) + 12 := by
   intro d hdI;obtain ⟨sd, hsd_le, hbd⟩ := ha d hdI;have hsdR : (sd : ℝ) <= (r : ℝ) := by exact_mod_cast hsd_le
   have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by have := (mem_Icc.mp hdI).1; omega : 0 < d)
   have hquad_pos : 0 <= (sd : ℝ) * ((q : ℝ) + (c : ℝ) + (r : ℝ)) - (sd : ℝ) ^ 2 / 2 := by
     have : (sd : ℝ) * ((q : ℝ) + (c : ℝ) + (r : ℝ)) - (sd : ℝ) ^ 2 / 2 = (sd : ℝ) * ((q : ℝ) + (c : ℝ)) + (sd : ℝ) * ((r : ℝ) - (sd : ℝ)) + (sd : ℝ) ^ 2 / 2 := by ring
     rw [this]; positivity
   have hquad_leN2 : (sd : ℝ) * ((q : ℝ) + (c : ℝ) + (r : ℝ)) - (sd : ℝ) ^ 2 / 2 <= (N : ℝ) ^ 2 := by
     have hsdN : (sd : ℝ) <= (N : ℝ) := by exact_mod_cast (by omega : sd <= N)
     have hqcrN : (q : ℝ) + (c : ℝ) + (r : ℝ) <= (N : ℝ) := by exact_mod_cast (by omega : q + c + r <= N)
     have hmul := mul_le_mul hsdN hqcrN (by positivity) (Nat.cast_nonneg N);linarith [hmul, sq_nonneg (sd : ℝ), show (N : ℝ) * (N : ℝ) = (N : ℝ) ^ 2 by ring]
   have hM_term : M * ((sd : ℝ) * ((q : ℝ) + (c : ℝ) + (r : ℝ)) - (sd : ℝ) ^ 2 / 2) <= (1 / Z) * ((sd : ℝ) * ((q : ℝ) + (c : ℝ) + (r : ℝ)) - (sd : ℝ) ^ 2 / 2) + (7 / (Z * Real.sqrt N)) * (N : ℝ) ^ 2 := by
     have h1 := mul_le_mul_of_nonneg_right hM_approx hquad_pos;have h2 := mul_le_mul_of_nonneg_left hquad_leN2 (show 0 <= 7 / (Z * Real.sqrt N) by positivity);linarith [h1, h2, show (1 / Z + 7 / (Z * Real.sqrt N)) * ((sd : ℝ) * ((q : ℝ) + (c : ℝ) + (r : ℝ)) - (sd : ℝ) ^ 2 / 2) = (1 / Z) * ((sd : ℝ) * ((q : ℝ) + (c : ℝ) + (r : ℝ)) - (sd : ℝ) ^ 2 / 2) + (7 / (Z * Real.sqrt N)) * ((sd : ℝ) * ((q : ℝ) + (c : ℝ) + (r : ℝ)) - (sd : ℝ) ^ 2 / 2) by ring]
   have halg := thm41_algebra (N := (N : ℝ)) (c := (c : ℝ)) (q := (q : ℝ)) (r := (r : ℝ)) (x := (x : ℝ)) (s := (sd : ℝ)) (Z := Z) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) hsdR (by exact_mod_cast le_of_eq hsum_N) (by linarith) hZ_bds.2;have hdiv_alg := mul_le_mul_of_nonneg_left halg (show 0 <= 1 / (Z * (d : ℝ) ^ 2) by positivity);have hdiv_M := div_le_div_of_nonneg_right (add_le_add (le_refl ((c : ℝ) * ((r : ℝ) - (sd : ℝ)))) hM_term) (sq_nonneg (d : ℝ))
   have hrew1 : ((c : ℝ) * ((r : ℝ) - (sd : ℝ)) + ((1 / Z) * ((sd : ℝ) * ((q : ℝ) + (c : ℝ) + (r : ℝ)) - (sd : ℝ) ^ 2 / 2) + (7 / (Z * Real.sqrt N)) * (N : ℝ) ^ 2)) / (d : ℝ) ^ 2 + (1 / (Z * (d : ℝ) ^ 2)) * (Z * (x : ℝ) * ((q : ℝ) + (c : ℝ)) + (r : ℝ) * (x : ℝ)) = (1 / (Z * (d : ℝ) ^ 2)) * (Z * (x : ℝ) * ((q : ℝ) + (c : ℝ)) + (r : ℝ) * (x : ℝ) + Z * (c : ℝ) * ((r : ℝ) - (sd : ℝ)) + (sd : ℝ) * ((q : ℝ) + (c : ℝ) + (r : ℝ)) - (sd : ℝ) ^ 2 / 2) + (7 / (Z * Real.sqrt N * (d : ℝ) ^ 2)) * (N : ℝ) ^ 2 := by field_simp; ring
   linarith [hbd, hdiv_M, hrew1, hdiv_alg]
 have hsum_all := sum_le_sum hterm_comb
 have hZ_norm : ∑ d ∈ Icc 1 N, (1 : ℝ) / (Z * (d : ℝ) ^ 2) = 1 := by
   have h1 : ∑ d ∈ Icc 1 N, (1 : ℝ) / (Z * (d : ℝ) ^ 2) = (1 / Z) * Z := by dsimp only [Z, zeta2Sum]; rw [mul_sum]; refine sum_congr rfl fun d _ => by ring
   rw [h1, one_div_mul_cancel (by linarith)]
 have hZ_sqrt : ∑ d ∈ Icc 1 N, (7 / (Z * Real.sqrt N * (d : ℝ) ^ 2)) * (N : ℝ) ^ 2 = 7 * (N : ℝ) * Real.sqrt N := by
   have h1 : ∑ d ∈ Icc 1 N, (7 / (Z * Real.sqrt N * (d : ℝ) ^ 2)) * (N : ℝ) ^ 2 = (7 * (N : ℝ) ^ 2 / (Z * Real.sqrt N)) * Z := by dsimp only [Z, zeta2Sum]; rw [mul_sum]; refine sum_congr rfl fun d _ => by ring
   rw [h1];have hZne : Z ≠ 0 := by linarith
   have hsqne : Real.sqrt (N : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < N)));have hsq2 : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = (N : ℝ) := Real.mul_self_sqrt (Nat.cast_nonneg N);field_simp;linarith [show 7 * (N : ℝ) ^ 2 = 7 * (N : ℝ) * (Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ)) by rw [hsq2]; ring]
 have hharm : ∑ d ∈ Icc 1 N, (40 * (N : ℝ) * (1 + Real.log N) / (d : ℝ)) <= 40 * (N : ℝ) * (1 + Real.log N) ^ 2 := by
   have h1 : ∑ d ∈ Icc 1 N, (40 * (N : ℝ) * (1 + Real.log N) / (d : ℝ)) = (40 * (N : ℝ) * (1 + Real.log N)) * ∑ d ∈ Icc 1 N, (1 : ℝ) / (d : ℝ) := by rw [mul_sum]; refine sum_congr rfl fun d _ => by ring
   rw [h1];have := mul_le_mul_of_nonneg_left (harmonic_le_one_add_log N (by omega)) (show 0 <= 40 * (N : ℝ) * (1 + Real.log N) by positivity);linarith [this, show 40 * (N : ℝ) * (1 + Real.log N) * (1 + Real.log N) = 40 * (N : ℝ) * (1 + Real.log N) ^ 2 by ring]
 have h12s : ∑ _d ∈ Icc 1 N, (12 : ℝ) = 12 * (N : ℝ) := by rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]; ring
 simp only [sum_add_distrib] at hsum_all;rw [<- sum_mul, <- sum_mul, hZ_norm, one_mul, one_mul, hZ_sqrt, h12s] at hsum_all;linarith [hsum_all, hharm, show 0 <= 7 * (N : ℝ) * Real.sqrt N by positivity]
lemma thm41_step_i {N c cq cqr p x : ℕ} (hc_lt_cq : c < cq) (hcq_le_cqr : cq <= cqr) {F Sfam : Finset (Finset ℕ)} (hF : IsWellInter N F) (hS_sub : Sfam ⊆ F) {T0 S : Finset ℕ} (hT0F : T0 ∈ F) (hcT0 : c ∉ T0) (hT0_max : ∀ w ∈ T0, w <= cqr) (hS : S ∈ Sfam) (hdt : IsDeltaTriplet F S c p x) (hnofill : ¬ (∀ w, min c (min p x) <= w -> w <= max c (max p x) -> w % Nat.gcd (distNat c p) (distNat c x) = c % Nat.gcd (distNat c p) (distNat c x) -> w ∈ S)) (hopt : ∀ u ∈ S ∩ Icc cq N, ∀ v ∈ S, (if u <= cqr then 0 else if v <= cqr then 1 else 2) * (N + 1) + distNat u v <
       (if p <= cqr then 0 else if x <= cqr then 1 else 2) * (N + 1) + distNat p x ->
     ¬ IsDeltaTriplet Sfam S c u v) :
   ¬ (cqr < p /\ cqr < x) := by
 classical
 rintro ⟨hp_gt, hx_gt⟩;have hST0 : S ≠ T0 := fun h => hcT0 (h ▸ hdt.1)
 obtain ⟨w0, hw0⟩ := wellInter_meet hF (hS_sub hS) hT0F hST0;have hw0S := mem_of_mem_inter_left hw0; have hw0T := mem_of_mem_inter_right hw0;have hw0_le : w0 <= cqr := hT0_max w0 hw0T;have hw0_ne : w0 ≠ c := fun h => hcT0 (h ▸ hw0T)
 let Low := (S.filter (fun w => w <= cqr)).erase c
 have hLow_ne : Low.Nonempty := ⟨w0, mem_erase.mpr ⟨hw0_ne, mem_filter.mpr ⟨hw0S, hw0_le⟩⟩⟩;obtain ⟨z, hzL, hz_min⟩ := exists_min_image Low (fun w => distNat c w) hLow_ne;obtain ⟨hzc, hzF⟩ := mem_erase.mp hzL;obtain ⟨hzS, hz_le⟩ := mem_filter.mp hzF
 set dz := distNat c z
 have hdz_pos : 1 <= dz := distNat_pos_of_ne hzc.symm
 have hfill_u : ∀ u ∈ S, cqr < u -> dz ∣ distNat c u /\ (∀ w, min c u <= w -> w <= max c u -> w % dz = c % dz -> w ∈ S) := by
   intro u huS hu_gt;have huP : u ∈ S ∩ Icc cq N := mem_inter.mpr ⟨huS, mem_Icc.mpr ⟨by omega, (mem_Icc.mp (hF.1 S (hS_sub hS) huS)).2⟩⟩
   have hsc_lt : (if u <= cqr then 0 else if z <= cqr then 1 else 2) * (N + 1) + distNat u z < (if p <= cqr then 0 else if x <= cqr then 1 else 2) * (N + 1) + distNat p x := by
     rw [if_neg (by omega), if_pos hz_le, if_neg (by omega), if_neg (by omega)]
     have : distNat u z <= N := by
       have := mem_Icc.mp (hF.1 S (hS_sub hS) huS);have := mem_Icc.mp (hF.1 S (hS_sub hS) hzS);unfold distNat; omega
     omega
   have hnotdt := hopt u huP z hzS hsc_lt;have hnu := nu_triplet_fill (isWellInter_subset hF hS_sub) hS hdt.1 huS hzS (by omega) hzc.symm (by omega) hnotdt
   set g := Nat.gcd (distNat c u) dz
   have hg_pos : 1 <= g := hnu.1;have hg_le : g <= dz := Nat.le_of_dvd hdz_pos (Nat.gcd_dvd_right _ _)
   have hdz_le_g : dz <= g := by
     rcases lt_or_gt_of_ne hzc.symm with hlt | hgt
     . have hcgS : c + g ∈ S := hnu.2.2.2 (c + g) (by omega) (by dsimp only [dz] at hg_le; unfold distNat at hg_le; omega) (by rw [Nat.add_mod_right])
       have hcgL : c + g ∈ Low := mem_erase.mpr ⟨by omega, mem_filter.mpr ⟨hcgS, by dsimp only [dz] at hg_le; unfold distNat at hg_le; omega⟩⟩;have hm : dz <= distNat c (c + g) := hz_min (c + g) hcgL;unfold distNat at hm; omega
     . have hgle_c : g <= c := by dsimp only [dz] at hg_le; unfold distNat at hg_le; omega
       have hcgS : c - g ∈ S := hnu.2.2.2 (c - g) (by dsimp only [dz] at hg_le; unfold distNat at hg_le; omega) (by omega) (by
         have h1 : c - g + g = c := Nat.sub_add_cancel hgle_c
         conv_rhs => rw [<- h1]
         rw [Nat.add_mod_right])
       have hcgL : c - g ∈ Low := mem_erase.mpr ⟨by omega, mem_filter.mpr ⟨hcgS, by omega⟩⟩;have hm : dz <= distNat c (c - g) := hz_min (c - g) hcgL;unfold distNat at hm; omega
   have hgeq : g = dz := by omega
   exact ⟨hgeq ▸ Nat.gcd_dvd_left _ _, fun w hw1 hw2 hwm => hnu.2.2.2 w (by omega) (by omega) (by rwa [hgeq])⟩
 obtain ⟨hd_p, hfp⟩ := hfill_u p hdt.2.1 hp_gt;obtain ⟨hd_x, hfx⟩ := hfill_u x hdt.2.2.1 hx_gt;have hdz_dvd : dz ∣ Nat.gcd (distNat c p) (distNat c x) := Nat.dvd_gcd hd_p hd_x;apply hnofill; intro w hw1 hw2 hwm
 have hwm_dz : w % dz = c % dz := by
   obtain ⟨t, ht⟩ := hdz_dvd; rw [ht] at hwm;have := congrArg (· % dz) hwm; rwa [Nat.mod_mul_right_mod, Nat.mod_mul_right_mod] at this
 rcases le_total p x with hpx | hpx
 . exact hfx w (by omega) (by omega) hwm_dz
 . exact hfp w (by omega) (by omega) hwm_dz
lemma szabo_theorem_4_1_right {N c : ℕ} (hN : 10000 <= N) (hc : c ∈ Icc 1 N) {F P E Sfam : Finset (Finset ℕ)} (hF : IsWellInter N F) (hP_sub : P ⊆ F) (hE_sub : E ⊆ F) (hS_sub : Sfam ⊆ F) (hP : ∀ S ∈ P, 3 <= S.card /\ c ∉ S /\ APSet S) (hE : ∀ S ∈ E, 3 <= S.card /\ c ∈ S /\ APSet S) (hSfam : ∀ S ∈ Sfam, c ∈ S /\ ¬ APSet S) {B0 : Finset ℕ} (hB0 : B0 ∈ F) (hcB0 : c ∉ B0) (hB0_sz : 40 * B0.card < 39 * N) (hP_right : ∃ P0 ∈ P, ∃ hne : P0.Nonempty, c < P0.min' hne) : (P.card : ℝ) + (E.card : ℝ) + (Sfam.card : ℝ) <= (N : ℝ) ^ 2 / 2 - (N : ℝ) ^ 2 / 1000000000 +
       200 * (N : ℝ) * Real.sqrt N + 200 * (N : ℝ) * (2 + Real.log N) ^ 2 + 100 := by
 classical
 have hP_ne : P.Nonempty := by obtain ⟨P0, hP0, -⟩ := hP_right; exact ⟨P0, hP0⟩
 let minOf : Finset ℕ -> ℕ := fun S => if h : S.Nonempty then S.min' h else 0
 let maxOf : Finset ℕ -> ℕ := fun S => if h : S.Nonempty then S.max' h else N
 obtain ⟨P0, hP0, hP0_max⟩ := exists_max_image P minOf hP_ne;obtain ⟨T0, hT0, hT0_min⟩ := exists_min_image P maxOf hP_ne;have hP0_ne : P0.Nonempty := card_pos.mp (by have := (hP P0 hP0).1; omega);have hT0_ne : T0.Nonempty := card_pos.mp (by have := (hP T0 hT0).1; omega)
 set cq := P0.min' hP0_ne
 set cqr := T0.max' hT0_ne
 have hc_lt_cq : c < cq := by
   obtain ⟨P1, hP1, hne1, hlt1⟩ := hP_right;have := hP0_max P1 hP1; dsimp only [minOf] at this; rw [dif_pos hne1, dif_pos hP0_ne] at this; omega
 have hcq_le_cqr : cq <= cqr := by
   by_cases hPT : P0 = T0
   . subst hPT; exact min'_le P0 (P0.max' hP0_ne) (max'_mem P0 hP0_ne)
   . obtain ⟨w, hw⟩ := wellInter_meet hF (hP_sub hP0) (hP_sub hT0) hPT
     exact le_trans (min'_le P0 w (mem_of_mem_inter_left hw)) (le_max' T0 w (mem_of_mem_inter_right hw))
 have hcqr_leN : cqr <= N := (mem_Icc.mp (hF.1 T0 (hP_sub hT0) (max'_mem T0 hT0_ne))).2
 set q := cq - c
 set r := cqr - cq
 set x := N - cqr
 have hq1 : 1 <= q := by omega
 have hcqr_eq : c + q + r = cqr := by omega
 have hsum_N : c + q + r + x = N := by omega
 have hP_end : ∀ S ∈ P, ∃ hne : S.Nonempty, S.min' hne ∈ Icc 1 cq /\ S.max' hne ∈ Icc cqr N := fun S hS => by
   have hne : S.Nonempty := card_pos.mp (by have := (hP S hS).1; omega);have h1 := hP0_max S hS; dsimp only [minOf] at h1; rw [dif_pos hne, dif_pos hP0_ne] at h1;have h2 := hT0_min S hS; dsimp only [maxOf] at h2; rw [dif_pos hT0_ne, dif_pos hne] at h2;exact ⟨hne, mem_Icc.mpr ⟨(mem_Icc.mp (hF.1 S (hP_sub hS) (min'_mem S hne))).1, h1⟩, mem_Icc.mpr ⟨h2, (mem_Icc.mp (hF.1 S (hP_sub hS) (max'_mem S hne))).2⟩⟩
 have hlog_nn : 0 <= Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 <= N));have hsq_nn : 0 <= Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
 have hAP_rect : ∀ (A : Finset (Finset ℕ)) (d0 a1 a2 b1 b2 : ℕ), A ⊆ F -> (d0 = 1 \/ d0 = 2) -> (∀ S ∈ A, 3 <= S.card /\ APSet S /\ (∃ hne : S.Nonempty, S.min' hne ∈ Icc a1 a2 /\ S.max' hne ∈ Icc b1 b2) /\ (d0 = 2 -> ¬ ∃ l r, S = Icc l r)) -> (A.card : ℝ) <= ((∑ d ∈ Icc d0 N, (1 : ℝ) / (d : ℝ) ^ 2) * ((a2 + 1 - a1 : ℕ) : ℝ) * ((b2 + 1 - b1 : ℕ) : ℝ)) + (((a2 + 1 - a1 : ℕ) : ℝ) + ((b2 + 1 - b1 : ℕ) : ℝ)) * (1 + Real.log N) + (N : ℝ) := fun A d0 a1 a2 b1 b2 hAsub hd0 hA => card_AP_rect_endpoints (by omega) hF hAsub hd0 hA
 by_cases hsmall : 1000 * (c + q + x) < N
 . have hP_bd := hAP_rect P 1 1 cq cqr N hP_sub (Or.inl rfl) (fun S hS =>
     ⟨(hP S hS).1, (hP S hS).2.2, hP_end S hS, fun h => by omega⟩)
   have hZ_ub : ∑ d ∈ Icc 1 N, (1 : ℝ) / (d : ℝ) ^ 2 <= 61 / 36 := sum_inv_sq_le_61_36 N;have hmiss := missing_pair_surplus_bound (by omega) hc hF hE_sub hS_sub hE hSfam hB0 hcB0 hB0_sz
   have hc1 : ((cq + 1 - 1 : ℕ) : ℝ) <= (N : ℝ) / 1000 := by
     have : 1000 * (cq + 1 - 1) <= N := by omega
     have hR : 1000 * ((cq + 1 - 1 : ℕ) : ℝ) <= (N : ℝ) := by exact_mod_cast this
     linarith
   have hc2 : ((N + 1 - cqr : ℕ) : ℝ) <= (N : ℝ) / 1000 + 1 := by
     have : 1000 * (N + 1 - cqr) <= N + 1000 := by omega
     have hR : 1000 * ((N + 1 - cqr : ℕ) : ℝ) <= (N : ℝ) + 1000 := by exact_mod_cast this
     linarith
   have hprod : (∑ d ∈ Icc 1 N, (1 : ℝ) / (d : ℝ) ^ 2) * ((cq + 1 - 1 : ℕ) : ℝ) * ((N + 1 - cqr : ℕ) : ℝ) <= (61 / 36 : ℝ) * ((N : ℝ) / 1000) * ((N : ℝ) / 1000 + 1) := by exact mul_le_mul (mul_le_mul hZ_ub hc1 (Nat.cast_nonneg _) (by positivity)) hc2 (Nat.cast_nonneg _) (by positivity)
   have hNR : (10000 : ℝ) <= (N : ℝ) := by exact_mod_cast hN
   have hlog2 : (2 + Real.log N) <= (2 + Real.log N) ^ 2 := by nlinarith
   nlinarith
 push Not at hsmall
 let badAP : Finset ℕ -> Prop := fun S => ∃ hne : S.Nonempty, S.min' hne = cq \/ S.min' hne = cqr \/ S.max' hne = cq \/ S.max' hne = cqr
 let P' := P.filter (fun S => ¬ badAP S)
 let E' := E.filter (fun S => ¬ badAP S)
 have hbad_AP_card : ((P.filter badAP).card : ℝ) + ((E.filter badAP).card : ℝ) <= 4 * ((N : ℝ) * (4 + Real.log N) + (N : ℝ)) := by
   have hfix : ∀ (u : ℕ) (isMin : Bool), (((P ∪ E).filter (fun S => ∃ hne : S.Nonempty, (if isMin then S.min' hne else S.max' hne) = u)).card : ℝ) <= (N : ℝ) * (4 + Real.log N) + (N : ℝ) := by
     intro u isMin
     let A := (P ∪ E).filter (fun S => ∃ hne : S.Nonempty, (if isMin then S.min' hne else S.max' hne) = u)
     have hAsub : A ⊆ F := (filter_subset _ _).trans (union_subset hP_sub hE_sub)
     cases isMin
     . have h1 := hAP_rect A 1 1 N u u hAsub (Or.inl rfl) (fun S hS => by
         obtain ⟨hSPE, hne, heq⟩ := mem_filter.mp hS;have h3 : 3 <= S.card /\ APSet S := by rcases mem_union.mp hSPE with h | h; exact ⟨(hP S h).1, (hP S h).2.2⟩; exact ⟨(hE S h).1, (hE S h).2.2⟩
         exact ⟨h3.1, h3.2, ⟨hne, hF.1 S (hAsub hS) (min'_mem S hne), by simp at heq; rw [heq]; exact mem_Icc.mpr ⟨le_rfl, le_rfl⟩⟩, fun h => by omega⟩)
       have hZ := sum_inv_sq_le_61_36 N;have hc1 : ((N + 1 - 1 : ℕ) : ℝ) = (N : ℝ) := by exact_mod_cast (by omega : N + 1 - 1 = N)
       have hc2 : ((u + 1 - u : ℕ) : ℝ) = 1 := by exact_mod_cast (by omega : u + 1 - u = 1)
       have hlogN : Real.log (N : ℝ) <= (N : ℝ) - 1 := Real.log_le_sub_one_of_pos (by exact_mod_cast (by omega : 0 < N));have hZN := mul_le_mul_of_nonneg_right hZ (Nat.cast_nonneg N);rw [hc1, hc2] at h1;linarith [h1, hZN, hlogN, show ((N : ℝ) + 1) * (1 + Real.log N) = (N : ℝ) + (N : ℝ) * Real.log N + 1 + Real.log N by ring, show (N : ℝ) * (4 + Real.log N) = 4 * (N : ℝ) + (N : ℝ) * Real.log N by ring]
     . have h1 := hAP_rect A 1 u u 1 N hAsub (Or.inl rfl) (fun S hS => by
         obtain ⟨hSPE, hne, heq⟩ := mem_filter.mp hS;have h3 : 3 <= S.card /\ APSet S := by rcases mem_union.mp hSPE with h | h; exact ⟨(hP S h).1, (hP S h).2.2⟩; exact ⟨(hE S h).1, (hE S h).2.2⟩
         exact ⟨h3.1, h3.2, ⟨hne, by simp at heq; rw [heq]; exact mem_Icc.mpr ⟨le_rfl, le_rfl⟩, hF.1 S (hAsub hS) (max'_mem S hne)⟩, fun h => by omega⟩)
       have hZ := sum_inv_sq_le_61_36 N;have hc1 : ((N + 1 - 1 : ℕ) : ℝ) = (N : ℝ) := by exact_mod_cast (by omega : N + 1 - 1 = N)
       have hc2 : ((u + 1 - u : ℕ) : ℝ) = 1 := by exact_mod_cast (by omega : u + 1 - u = 1)
       have hlogN : Real.log (N : ℝ) <= (N : ℝ) - 1 := Real.log_le_sub_one_of_pos (by exact_mod_cast (by omega : 0 < N));have hZN := mul_le_mul_of_nonneg_right hZ (Nat.cast_nonneg N);rw [hc1, hc2] at h1;linarith [h1, hZN, hlogN, show (1 + (N : ℝ)) * (1 + Real.log N) = (N : ℝ) + (N : ℝ) * Real.log N + 1 + Real.log N by ring, show (N : ℝ) * (4 + Real.log N) = 4 * (N : ℝ) + (N : ℝ) * Real.log N by ring]
   have hdisjPE : Disjoint (P.filter badAP) (E.filter badAP) := by rw [disjoint_left]; intro S h1 h2; exact (hP S (mem_filter.mp h1).1).2.1 (hE S (mem_filter.mp h2).1).2.1
   let B1 := (P ∪ E).filter (fun S => ∃ hne : S.Nonempty, (if true then S.min' hne else S.max' hne) = cq)
   let B2 := (P ∪ E).filter (fun S => ∃ hne : S.Nonempty, (if true then S.min' hne else S.max' hne) = cqr)
   let B3 := (P ∪ E).filter (fun S => ∃ hne : S.Nonempty, (if false then S.min' hne else S.max' hne) = cq)
   let B4 := (P ∪ E).filter (fun S => ∃ hne : S.Nonempty, (if false then S.min' hne else S.max' hne) = cqr)
   have hcovB : (P.filter badAP) ∪ (E.filter badAP) ⊆ B1 ∪ (B2 ∪ (B3 ∪ B4)) := by
     intro S hS
     have ⟨hSPE, hne, hbad⟩ : S ∈ P ∪ E /\ badAP S := by
       rcases mem_union.mp hS with h | h
       . exact ⟨mem_union_left _ (mem_filter.mp h).1, (mem_filter.mp h).2⟩
       . exact ⟨mem_union_right _ (mem_filter.mp h).1, (mem_filter.mp h).2⟩
     rcases hbad with h1 | h2 | h3 | h4
     . exact mem_union_left _ (mem_filter.mpr ⟨hSPE, hne, by simp [h1]⟩)
     . exact mem_union_right _ (mem_union_left _ (mem_filter.mpr ⟨hSPE, hne, by simp [h2]⟩))
     . exact mem_union_right _ (mem_union_right _ (mem_union_left _ (mem_filter.mpr ⟨hSPE, hne, by simp [h3]⟩)))
     . exact mem_union_right _ (mem_union_right _ (mem_union_right _ (mem_filter.mpr ⟨hSPE, hne, by simp [h4]⟩)))
   have hcard := card_le_card hcovB;rw [card_union_of_disjoint hdisjPE] at hcard;have hu1 := card_union_le B1 (B2 ∪ (B3 ∪ B4));have hu2 := card_union_le B2 (B3 ∪ B4);have hu3 := card_union_le B3 B4;have hR : ((P.filter badAP).card : ℝ) + ((E.filter badAP).card : ℝ) <= (B1.card : ℝ) + (B2.card : ℝ) + (B3.card : ℝ) + (B4.card : ℝ) := by exact_mod_cast (by omega : (P.filter badAP).card + (E.filter badAP).card <= B1.card + B2.card + B3.card + B4.card)
   linarith [hR, hfix cq true, hfix cqr true, hfix cq false, hfix cqr false]
 let score : ℕ × ℕ -> ℕ := fun p =>
   (if p.1 <= cqr then 0 else if p.2 <= cqr then 1 else 2) * (N + 1) + distNat p.1 p.2
 obtain ⟨H0, pH, xH, hH0sub, hH0dt, hSH0_bd⟩ := szabo_delta_extract (by omega) hc hF hS_sub hSfam (P := Icc cq N) (fun z hz => mem_Icc.mpr ⟨by have := mem_Icc.mp hz; omega, (mem_Icc.mp hz).2⟩) (fun hcP => by have := (mem_Icc.mp hcP).1; omega) (fun S hS => by
     obtain ⟨w, hw⟩ := wellInter_meet hF (hS_sub hS) (hP_sub hP0) (fun h => (hP P0 hP0).2.1 (h ▸ (hSfam S hS).1));have hwP0 := mem_of_mem_inter_right hw
     exact ⟨w, mem_inter.mpr ⟨mem_of_mem_inter_left hw, mem_Icc.mpr ⟨min'_le P0 w hwP0, (mem_Icc.mp (hF.1 P0 (hP_sub hP0) hwP0)).2⟩⟩⟩)
   score
 let badH : Finset ℕ -> Prop := fun S => pH S = cq \/ pH S = cqr \/ xH S = cq \/ xH S = cqr
 let H := H0.filter (fun S => ¬ badH S)
 have hbadH_card : (H0.filter badH).card <= 4 * N := by
   have hfixH : ∀ (u : ℕ) (isP : Bool), (H0.filter (fun S => (if isP then pH S else xH S) = u)).card <= N := fun u isP => by
     have hle : (H0.filter (fun S => (if isP then pH S else xH S) = u)).card <= (Icc 1 N).card := by
       refine card_le_card_of_injOn (fun S => if isP then xH S else pH S) (fun S hS => by
         have hSH0 := (mem_filter.mp (mem_coe.mp hS)).1;have hdt := (hH0dt S hSH0).2.2.1
         cases isP <;> exact mem_coe.mpr (hF.1 S (hS_sub (hH0sub hSH0)) (by first | exact hdt.2.2.1 | exact hdt.2.1))) ?_
       intro S1 h1 S2 h2 heq; dsimp only at heq; by_contra hne;have hS1 := mem_filter.mp (mem_coe.mp h1); have hS2 := mem_filter.mp (mem_coe.mp h2);have hdt1 := (hH0dt S1 hS1.1).2.2.1; have hdt2 := (hH0dt S2 hS2.1).2.2.1
       cases isP
       . simp at hS1 hS2 heq
         exact hdt1.2.2.2.2.2.2 S2 (hS_sub (hH0sub hS2.1)) (Ne.symm hne) ⟨hdt2.1, heq ▸ hdt2.2.1, (hS1.2.trans hS2.2.symm) ▸ hdt2.2.2.1⟩
       . simp at hS1 hS2 heq
         exact hdt1.2.2.2.2.2.2 S2 (hS_sub (hH0sub hS2.1)) (Ne.symm hne) ⟨hdt2.1, (hS1.2.trans hS2.2.symm) ▸ hdt2.2.1, heq ▸ hdt2.2.2.1⟩
     rwa [Nat.card_Icc, Nat.add_sub_cancel] at hle
   let H1 := H0.filter (fun S => (if true then pH S else xH S) = cq)
   let H2 := H0.filter (fun S => (if true then pH S else xH S) = cqr)
   let H3 := H0.filter (fun S => (if false then pH S else xH S) = cq)
   let H4 := H0.filter (fun S => (if false then pH S else xH S) = cqr)
   have hcov : H0.filter badH ⊆ H1 ∪ (H2 ∪ (H3 ∪ H4)) := fun S hS => by
     obtain ⟨hSH0, h1 | h2 | h3 | h4⟩ := mem_filter.mp hS
     . exact mem_union_left _ (mem_filter.mpr ⟨hSH0, h1⟩)
     . exact mem_union_right _ (mem_union_left _ (mem_filter.mpr ⟨hSH0, h2⟩))
     . exact mem_union_right _ (mem_union_right _ (mem_union_left _ (mem_filter.mpr ⟨hSH0, h3⟩)))
     . exact mem_union_right _ (mem_union_right _ (mem_union_right _ (mem_filter.mpr ⟨hSH0, h4⟩)))
   have := le_trans (card_le_card hcov) (card_union_le H1 (H2 ∪ (H3 ∪ H4)));have := card_union_le H2 (H3 ∪ H4);have := card_union_le H3 H4;have h1 : H1.card <= N := hfixH cq true;have h2 : H2.card <= N := hfixH cqr true;have h3 : H3.card <= N := hfixH cq false;have h4 : H4.card <= N := hfixH cqr false;omega
 have hH_XX_empty : ∀ S ∈ H, ¬ (cqr < pH S /\ cqr < xH S) := fun S hS => by
   obtain ⟨hSH0, -⟩ := mem_filter.mp hS;obtain ⟨-, -, hdt, hnofill, hopt⟩ := hH0dt S hSH0;exact thm41_step_i hc_lt_cq hcq_le_cqr hF hS_sub (hP_sub hT0) (hP T0 hT0).2.1 (fun w hw => le_max' T0 w hw) (hH0sub hSH0) hdt hnofill hopt
 let P1 := P'.filter (fun S => ∃ l r, S = Icc l r)
 let Pge2 := P'.filter (fun S => ¬ ∃ l r, S = Icc l r)
 let E_X := E'.filter (fun S => ∃ hne : S.Nonempty, cqr < S.max' hne)
 let E1_X := E_X.filter (fun S => ∃ l r, S = Icc l r)
 let Ege2_X := E_X.filter (fun S => ¬ ∃ l r, S = Icc l r)
 let E_R := E'.filter (fun S => ¬ ∃ hne : S.Nonempty, cqr < S.max' hne)
 let HXQ := H.filter (fun S => cqr < pH S /\ c < xH S /\ xH S < cq)
 let HXR := H.filter (fun S => (cqr < pH S /\ cq < xH S /\ xH S < cqr) \/ (pH S < cqr /\ cqr < xH S))
 let HXC := H.filter (fun S => cqr < pH S /\ xH S < c)
 let H_R := H.filter (fun S => pH S < cqr /\ xH S < cqr)
 have hStep2 : (P1.card : ℝ) + (HXQ.card : ℝ) <= (q : ℝ) * (x : ℝ) + 4 * (N : ℝ) := by
   have h1 := thm41_step_ii (N := N) (c := c) (q := q) (r := r) (P1 := P1) (HXQ := HXQ) (by omega) hF hS_sub ((filter_subset _ _).trans ((filter_subset _ _).trans hP_sub)) ((filter_subset _ _).trans ((filter_subset _ _).trans hH0sub)) (fun I hI => by
       obtain ⟨hIP', l, r0, hIeq⟩ := mem_filter.mp hI;obtain ⟨hIP, hnotbad⟩ := mem_filter.mp hIP';obtain ⟨hne, hminI, hmaxI⟩ := hP_end I hIP;have hmin_in : I.min' hne ∈ Icc l r0 := hIeq ▸ min'_mem I hne;have hmax_in : I.max' hne ∈ Icc l r0 := hIeq ▸ max'_mem I hne;have hlr : l <= r0 := le_trans (mem_Icc.mp hmin_in).1 (mem_Icc.mp hmin_in).2;have hmin_eq : I.min' hne = l := le_antisymm (min'_le I l (hIeq.symm ▸ mem_Icc.mpr ⟨le_rfl, hlr⟩)) (mem_Icc.mp hmin_in).1;have hmax_eq : I.max' hne = r0 := le_antisymm (mem_Icc.mp hmax_in).2 (le_max' I r0 (hIeq.symm ▸ mem_Icc.mpr ⟨hlr, le_rfl⟩))
       have hne_cq : l ≠ cq := fun h => hnotbad ⟨hne, Or.inl (hmin_eq.trans h)⟩
       have hne_cqr : r0 ≠ cqr := fun h => hnotbad ⟨hne, Or.inr (Or.inr (Or.inr (hmax_eq.trans h)))⟩
       have hcl : c < l := by
         by_contra hle; push Not at hle;exact (hP I hIP).2.1 (hIeq.symm ▸ mem_Icc.mpr ⟨hle, by have := (mem_Icc.mp hmaxI).1; omega⟩)
       exact ⟨l, r0, mem_Icc.mpr ⟨by omega, by have := (mem_Icc.mp hminI).2; omega⟩, mem_Icc.mpr ⟨by have := (mem_Icc.mp hmaxI).1; omega, hmax_eq ▸ (mem_Icc.mp hmaxI).2⟩, hIeq⟩)
     pH xH (fun S hS => by
       obtain ⟨hSH, hp_gt, hx1, hx2⟩ := mem_filter.mp hS;obtain ⟨hSH0, -⟩ := mem_filter.mp hSH;obtain ⟨hpI, -, hdt, hnofill, hopt⟩ := hH0dt S hSH0
       refine ⟨mem_Icc.mpr ⟨by omega, by omega⟩, mem_Icc.mpr ⟨by omega, (mem_Icc.mp (mem_of_mem_inter_right hpI)).2⟩, hdt, hnofill, fun a ha b hb ha_gt hb_le hlt => ?_⟩
       apply hopt a (mem_inter.mpr ⟨ha, mem_Icc.mpr ⟨by omega, (mem_Icc.mp (hF.1 S (hS_sub (hH0sub hSH0)) ha)).2⟩⟩) b hb
       dsimp only [score]; rw [if_neg (by omega), if_pos (by omega), if_neg (by omega), if_pos (by omega)]; omega)
   have hx_eq : N - (c + q + r) = x := by omega
   rwa [hx_eq] at h1
 have hStep3 : (Pge2.card : ℝ) + (Ege2_X.card : ℝ) <= (zeta2Sum N - 1) * ((c : ℝ) + (q : ℝ)) * (x : ℝ) + 2 * (N : ℝ) * (1 + Real.log N) + (N : ℝ) := by
   have hdisj : Disjoint Pge2 Ege2_X := by
     rw [disjoint_left]; intro S h1 h2;exact (hP S (mem_filter.mp (mem_filter.mp h1).1).1).2.1 (hE S (mem_filter.mp (mem_filter.mp (mem_filter.mp h2).1).1).1).2.1
   have h1 := hAP_rect (Pge2 ∪ Ege2_X) 2 1 (cq - 1) (cqr + 1) N (union_subset ((filter_subset _ _).trans ((filter_subset _ _).trans hP_sub)) ((filter_subset _ _).trans ((filter_subset _ _).trans ((filter_subset _ _).trans hE_sub)))) (Or.inr rfl) (fun S hS => by
       rcases mem_union.mp hS with h1 | h2
       . obtain ⟨hSP', hnotI⟩ := mem_filter.mp h1; obtain ⟨hSP, hnotbad⟩ := mem_filter.mp hSP'
         obtain ⟨hne, hminI, hmaxI⟩ := hP_end S hSP;have h1' : S.min' hne ≠ cq := fun h => hnotbad ⟨hne, Or.inl h⟩
         have h2' : S.max' hne ≠ cqr := fun h => hnotbad ⟨hne, Or.inr (Or.inr (Or.inr h))⟩
         exact ⟨(hP S hSP).1, (hP S hSP).2.2, ⟨hne, mem_Icc.mpr ⟨(mem_Icc.mp hminI).1, by have := (mem_Icc.mp hminI).2; omega⟩, mem_Icc.mpr ⟨by have := (mem_Icc.mp hmaxI).1; omega, (mem_Icc.mp hmaxI).2⟩⟩, fun _ => hnotI⟩
       . obtain ⟨hSEX, hnotI⟩ := mem_filter.mp h2
         obtain ⟨hSE', hne, hmax_gt⟩ := mem_filter.mp hSEX;obtain ⟨hSE, -⟩ := mem_filter.mp hSE';have hcS := (hE S hSE).2.1
         exact ⟨(hE S hSE).1, (hE S hSE).2.2, ⟨hne, mem_Icc.mpr ⟨(mem_Icc.mp (hF.1 S (hE_sub hSE) (min'_mem S hne))).1,
           by have := min'_le S c hcS; omega⟩, mem_Icc.mpr ⟨by omega, (mem_Icc.mp (hF.1 S (hE_sub hSE) (max'_mem S hne))).2⟩⟩, fun _ => hnotI⟩)
   rw [card_union_of_disjoint hdisj, Nat.cast_add] at h1
   have hZ_eq : ∑ d ∈ Icc 2 N, (1 : ℝ) / (d : ℝ) ^ 2 = zeta2Sum N - 1 := by
     dsimp only [zeta2Sum];have hsp : Icc 1 N = insert 1 (Icc 2 N) := by ext d; simp only [mem_Icc, mem_insert]; omega
     rw [hsp, sum_insert (by simp)]; ring
   rw [hZ_eq] at h1;have hZ1 : 0 <= zeta2Sum N - 1 := by linarith [(zeta2Sum_bounds (by omega : 100 <= N)).1]
   have hc1 : ((cq - 1 + 1 - 1 : ℕ) : ℝ) <= (c : ℝ) + (q : ℝ) := by exact_mod_cast (by omega : cq - 1 + 1 - 1 <= c + q)
   have hc2 : ((N + 1 - (cqr + 1) : ℕ) : ℝ) <= (x : ℝ) := by exact_mod_cast (by omega : N + 1 - (cqr + 1) <= x)
   have hc1N : ((cq - 1 + 1 - 1 : ℕ) : ℝ) <= (N : ℝ) := by exact_mod_cast (by omega : cq - 1 + 1 - 1 <= N)
   have hc2N : ((N + 1 - (cqr + 1) : ℕ) : ℝ) <= (N : ℝ) := by exact_mod_cast (by omega : N + 1 - (cqr + 1) <= N)
   have hmul := mul_le_mul (mul_le_mul_of_nonneg_left hc1 hZ1) hc2 (Nat.cast_nonneg _) (by positivity);have hmul2 := mul_le_mul_of_nonneg_right (show ((cq - 1 + 1 - 1 : ℕ) : ℝ) + ((N + 1 - (cqr + 1) : ℕ) : ℝ) <= 2 * (N : ℝ) by linarith) (show 0 <= 1 + Real.log N by linarith);linarith [h1, hmul, hmul2]
 have hStep4 : (HXR.card : ℝ) <= (r : ℝ) * (x : ℝ) := by
   let fRX : Finset ℕ -> ℕ × ℕ := fun S => if cqr < pH S then (xH S, pH S) else (pH S, xH S)
   have hle : HXR.card <= (Icc (cq + 1) (cqr - 1) ×ˢ Icc (cqr + 1) N).card := by
     refine card_le_card_of_injOn fRX (fun S hS => by
       obtain ⟨hSH, hcond⟩ := mem_filter.mp (mem_coe.mp hS);have hdt := (hH0dt S (mem_filter.mp hSH).1).2.2.1;have hSF := hS_sub (hH0sub (mem_filter.mp hSH).1)
       rcases hcond with ⟨hp_gt, hx1, hx2⟩ | ⟨hp_lt, hx_gt⟩
       . dsimp only [fRX]; rw [if_pos hp_gt]
         exact mem_coe.mpr (mem_product.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, mem_Icc.mpr ⟨by omega, (mem_Icc.mp (hF.1 S hSF hdt.2.1)).2⟩⟩)
       . dsimp only [fRX]; rw [if_neg (by omega)]
         have hp_ge := (mem_Icc.mp (mem_of_mem_inter_right (hH0dt S (mem_filter.mp hSH).1).1)).1;have hp_ne : pH S ≠ cq := fun h => (mem_filter.mp hSH).2 (Or.inl h)
         exact mem_coe.mpr (mem_product.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, mem_Icc.mpr ⟨by omega, (mem_Icc.mp (hF.1 S hSF hdt.2.2.1)).2⟩⟩)) ?_
     intro S1 h1 S2 h2 heq; by_contra hne;have hS1 := (mem_filter.mp (mem_coe.mp h1)).1; have hS2 := (mem_filter.mp (mem_coe.mp h2)).1;have hdt1 := (hH0dt S1 (mem_filter.mp hS1).1).2.2.1; have hdt2 := (hH0dt S2 (mem_filter.mp hS2).1).2.2.1
     have hpair : ({pH S1, xH S1} : Finset ℕ) = {pH S2, xH S2} := by
       dsimp only [fRX] at heq;split_ifs at heq with h1' h2' h2'
       . rcases Prod.mk.inj heq with ⟨ha, hb⟩; rw [ha, hb]
       . rcases Prod.mk.inj heq with ⟨ha, hb⟩; rw [ha, hb, pair_comm]
       . rcases Prod.mk.inj heq with ⟨ha, hb⟩; rw [ha, hb, pair_comm]
       . rcases Prod.mk.inj heq with ⟨ha, hb⟩; rw [ha, hb]
     have hsub : ({pH S1, xH S1} : Finset ℕ) ⊆ S2 := by
       rw [hpair]; intro z hz; simp only [mem_insert, mem_singleton] at hz
       rcases hz with rfl | rfl; exact hdt2.2.1; exact hdt2.2.2.1
     exact hdt1.2.2.2.2.2.2 S2 (hS_sub (hH0sub (mem_filter.mp hS2).1)) (Ne.symm hne) ⟨hdt2.1, hsub (by simp), hsub (by simp)⟩
   rw [card_product, Nat.card_Icc, Nat.card_Icc] at hle;have h1 : (cqr - 1 + 1 - (cq + 1)) * (N + 1 - (cqr + 1)) <= r * x := Nat.mul_le_mul (by omega) (by omega);exact_mod_cast le_trans hle h1
 have hStep5 : (E1_X.card : ℝ) + (HXC.card : ℝ) <= (c : ℝ) * (x : ℝ) + 2 * (N : ℝ) + 1 := by
   have hcor := szabo_cor_3_3 (_N := N) (c := c) (d := 1) (a1 := 1) (a2 := c) (b1 := cqr + 1) (b2 := N) (E := E1_X) (H := HXC) le_rfl (fun E0 hE0 => by
       obtain ⟨hE0X, l, r0, hEq⟩ := mem_filter.mp hE0;obtain ⟨hE0', hne, hmax_gt⟩ := mem_filter.mp hE0X;obtain ⟨hE0E, -⟩ := mem_filter.mp hE0';have hcE := (hE E0 hE0E).2.1
       refine ⟨hcE, fun x _ => by simp [Nat.mod_one], fun a ha b hb z hz1 hz2 _ => ?_, hne, mem_Icc.mpr ⟨(mem_Icc.mp (hF.1 E0 (hE_sub hE0E) (min'_mem E0 hne))).1, min'_le E0 c hcE⟩, mem_Icc.mpr ⟨by omega, (mem_Icc.mp (hF.1 E0 (hE_sub hE0E) (max'_mem E0 hne))).2⟩⟩
       rw [hEq, mem_Icc] at ha hb ⊢; omega)
     pH xH (fun S hS => by
       obtain ⟨hSH, hp_gt, hx_lt⟩ := mem_filter.mp hS;have hSH0 := (mem_filter.mp hSH).1; have hdt := (hH0dt S hSH0).2.2.1;have hSF := hS_sub (hH0sub hSH0)
       exact ⟨mem_Icc.mpr ⟨(mem_Icc.mp (hF.1 S hSF hdt.2.2.1)).1, by omega⟩, mem_Icc.mpr ⟨by omega, (mem_Icc.mp (hF.1 S hSF hdt.2.1)).2⟩,
         by simp [Nat.mod_one], by simp [Nat.mod_one],
         fun T hTE ⟨hxT, hpT⟩ => hdt.2.2.2.2.2.2 T (hE_sub (mem_filter.mp (mem_filter.mp (mem_filter.mp hTE).1).1).1) (fun h => (hSfam S (hH0sub hSH0)).2 (h ▸ (hE T (mem_filter.mp (mem_filter.mp (mem_filter.mp hTE).1).1).1).2.2)) ⟨(hE T (mem_filter.mp (mem_filter.mp (mem_filter.mp hTE).1).1).1).2.1, hpT, hxT⟩,
         fun T hTH hTS ⟨hxT, hpT⟩ => hdt.2.2.2.2.2.2 T (hS_sub (hH0sub (mem_filter.mp (mem_filter.mp hTH).1).1)) hTS ⟨(hH0dt T (mem_filter.mp (mem_filter.mp hTH).1).1).2.2.1.1, hpT, hxT⟩,
         hdt.2.2.1, hdt.2.1⟩)
   have hcA : ((Icc 1 c).card : ℝ) = (c : ℝ) := by rw [Nat.card_Icc, Nat.add_sub_cancel]
   have hcB : ((Icc (cqr + 1) N).card : ℝ) = (x : ℝ) := by rw [Nat.card_Icc]; exact_mod_cast (by omega : N + 1 - (cqr + 1) = x)
   rw [hcA, hcB, Nat.cast_one, div_one, div_one] at hcor;have hcN : (c : ℝ) <= (N : ℝ) := by exact_mod_cast (mem_Icc.mp hc).2
   have hxN : (x : ℝ) <= (N : ℝ) := by exact_mod_cast (by omega : x <= N)
   linarith [hcor, show ((c : ℝ) + 1) * ((x : ℝ) + 1) = (c : ℝ) * (x : ℝ) + (c : ℝ) + (x : ℝ) + 1 by ring]
 have hE_R_step : ∀ E0 : {E0 // E0 ∈ E_R}, ∃ d, 1 <= d /\ d <= N /\ (∀ z ∈ E0.1, z % d = c % d) /\ (∀ a ∈ E0.1, ∀ b ∈ E0.1, ∀ z, min a b <= z -> z <= max a b -> z % d = c % d -> z ∈ E0.1) := by
   rintro ⟨E0, hE0⟩;have hE0E := (mem_filter.mp (mem_filter.mp hE0).1).1;obtain ⟨h3, hcE, hAP⟩ := hE E0 hE0E;obtain ⟨d, hd1, -, -, hmem, -⟩ := apSet_canonical hAP (by omega);have hcm := (hmem c).mp hcE;obtain ⟨w, hw⟩ := card_pos.mp (by rw [card_erase_of_mem hcE]; omega : 0 < (E0.erase c).card);obtain ⟨hwc, hwE⟩ := mem_erase.mp hw;have hwm := (hmem w).mp hwE
   have hdN : d <= N := by
     have hdvd : d ∣ distNat c w := by
       unfold distNat; rcases le_total c w with h | h
       . rw [max_eq_right h, min_eq_left h]; exact (Nat.modEq_iff_dvd' h).mp (hwm.2.2.trans hcm.2.2.symm).symm
       . rw [max_eq_left h, min_eq_right h]; exact (Nat.modEq_iff_dvd' h).mp (hwm.2.2.trans hcm.2.2.symm)
     have hle := Nat.le_of_dvd (distNat_pos_of_ne hwc.symm) hdvd;have := mem_Icc.mp hc; have := mem_Icc.mp (hF.1 E0 (hE_sub hE0E) hwE); unfold distNat at hle; omega
   refine ⟨d, hd1, hdN, fun z hz => ((hmem z).mp hz).2.2.trans hcm.2.2.symm, fun a ha b hb z hz1 hz2 hzm => ?_⟩
   have ham := (hmem a).mp ha; have hbm := (hmem b).mp hb;exact (hmem z).mpr ⟨by omega, by omega, hzm.trans hcm.2.2⟩
 choose dER hdER using hE_R_step
 let EdR : ℕ -> Finset (Finset ℕ) := fun d => (E_R.attach.filter (fun E0 => dER E0 = d)).image Subtype.val
 let HdR : ℕ -> Finset (Finset ℕ) := fun d => H_R.filter (fun S => Nat.gcd (distNat c (pH S)) (distNat c (xH S)) = d)
 have hStep6_d : ∀ d ∈ Icc 1 N, ∃ sd : ℕ, sd <= r /\ ((EdR d).card : ℝ) + ((HdR d).card : ℝ) <= ((c : ℝ) * ((r : ℝ) - (sd : ℝ)) + moebius2Sum N * ((sd : ℝ) * ((q : ℝ) + (c : ℝ) + (r : ℝ)) - (sd : ℝ) ^ 2 / 2)) / (d : ℝ) ^ 2 + 40 * (N : ℝ) * (1 + Real.log N) / (d : ℝ) + 12 := by
   intro d hdI
   refine thm41_step_vi_d (by omega) (by omega) hc hq1 (by omega) (mem_Icc.mp hdI).1 (mem_Icc.mp hdI).2 hF (fun E0 hE0 => by obtain ⟨E0', -, rfl⟩ := mem_image.mp hE0; exact hE_sub (mem_filter.mp (mem_filter.mp E0'.2).1).1) ((filter_subset _ _).trans ((filter_subset _ _).trans ((filter_subset _ _).trans (hH0sub.trans hS_sub)))) (fun E0 hE0 => by
       obtain ⟨E0', hE0'f, rfl⟩ := mem_image.mp hE0;have hE0'R := E0'.2; have hE0'E' := (mem_filter.mp hE0'R).1; have hnotX := (mem_filter.mp hE0'R).2;have hE0E := (mem_filter.mp hE0'E').1; have hnotbad := (mem_filter.mp hE0'E').2;have hcE := (hE E0'.1 hE0E).2.1; have hne : E0'.1.Nonempty := ⟨c, hcE⟩;have hsp := hdER E0'; rw [(mem_filter.mp hE0'f).2] at hsp;have hneP0 : E0'.1 ≠ P0 := fun h => (hP P0 hP0).2.1 (h ▸ hcE)
       obtain ⟨w, hw⟩ := wellInter_meet hF (hE_sub hE0E) (hP_sub hP0) hneP0;have hmax_ge : cq <= E0'.1.max' hne := le_trans (min'_le P0 w (mem_of_mem_inter_right hw)) (le_max' E0'.1 w (mem_of_mem_inter_left hw));have hmax_le : E0'.1.max' hne <= cqr := by by_contra hgt; exact hnotX ⟨hne, by omega⟩
       have hne_cq : E0'.1.max' hne ≠ cq := fun h => hnotbad ⟨hne, Or.inr (Or.inr (Or.inl h))⟩
       have hne_cqr : E0'.1.max' hne ≠ cqr := fun h => hnotbad ⟨hne, Or.inr (Or.inr (Or.inr h))⟩
       exact ⟨hcE, hsp.2.2.1, hsp.2.2.2, hne, mem_Icc.mpr ⟨(mem_Icc.mp (hF.1 E0'.1 (hE_sub hE0E) (min'_mem E0'.1 hne))).1, min'_le E0'.1 c hcE⟩, mem_Icc.mpr ⟨by omega, by omega⟩⟩)
     pH xH (fun S hS => by
       obtain ⟨hSHR, hgcd⟩ := mem_filter.mp hS;obtain ⟨hSH, hp_lt, hx_lt⟩ := mem_filter.mp hSHR;obtain ⟨hSH0, hnotbad⟩ := mem_filter.mp hSH;obtain ⟨hpI, -, hdt, -, -⟩ := hH0dt S hSH0;have hSF := hS_sub (hH0sub hSH0);have hp_ge := (mem_Icc.mp (mem_of_mem_inter_right hpI)).1;have hp_ne_cq : pH S ≠ cq := fun h => hnotbad (Or.inl h)
       exact ⟨fun hmem => by obtain ⟨E0', -, hEq⟩ := mem_image.mp hmem; exact (hSfam S (hH0sub hSH0)).2 (hEq ▸ (hE E0'.1 (mem_filter.mp (mem_filter.mp E0'.2).1).1).2.2), hdt, hgcd, mem_Icc.mpr ⟨by omega, by omega⟩, mem_erase.mpr ⟨hdt.2.2.2.2.1.symm, mem_Icc.mpr ⟨(mem_Icc.mp (hF.1 S hSF hdt.2.2.1)).1, by omega⟩⟩⟩)
 set Z := zeta2Sum N
 have hStep6_sum : (E_R.card : ℝ) + (H_R.card : ℝ) + Z * (x : ℝ) * ((q : ℝ) + (c : ℝ)) + (r : ℝ) * (x : ℝ) <= (N : ℝ) ^ 2 / 2 - (((c : ℝ) + (q : ℝ)) ^ 2 + (x : ℝ) ^ 2) / 200 + 14 * (N : ℝ) * Real.sqrt N + 40 * (N : ℝ) * (1 + Real.log N) ^ 2 + 12 * (N : ℝ) := by
   have hcovER : E_R ⊆ (Icc 1 N).biUnion EdR := fun E0 hE0 =>
     mem_biUnion.mpr ⟨dER ⟨E0, hE0⟩, mem_Icc.mpr ⟨(hdER ⟨E0, hE0⟩).1, (hdER ⟨E0, hE0⟩).2.1⟩, mem_image.mpr ⟨⟨E0, hE0⟩, mem_filter.mpr ⟨mem_attach _ _, rfl⟩, rfl⟩⟩
   have hcovHR : H_R ⊆ (Icc 1 N).biUnion HdR := fun S hS => by
     have hSH0 := (mem_filter.mp (mem_filter.mp hS).1).1; have hdt := (hH0dt S hSH0).2.2.1
     set g := Nat.gcd (distNat c (pH S)) (distNat c (xH S))
     have hg1 : 1 <= g := Nat.gcd_pos_of_pos_left _ (distNat_pos_of_ne hdt.2.2.2.1)
     have hgN : g <= N := by
       have hle : g <= distNat c (pH S) := Nat.le_of_dvd (distNat_pos_of_ne hdt.2.2.2.1) (Nat.gcd_dvd_left _ _);have := mem_Icc.mp hc; have := mem_Icc.mp (hF.1 S (hS_sub (hH0sub hSH0)) hdt.2.1); unfold distNat at hle; omega
     exact mem_biUnion.mpr ⟨g, mem_Icc.mpr ⟨hg1, hgN⟩, mem_filter.mpr ⟨hS, rfl⟩⟩
   have hsum_ER : (E_R.card : ℝ) <= ∑ d ∈ Icc 1 N, ((EdR d).card : ℝ) := by exact_mod_cast le_trans (card_le_card hcovER) card_biUnion_le
   have hsum_HR : (H_R.card : ℝ) <= ∑ d ∈ Icc 1 N, ((HdR d).card : ℝ) := by exact_mod_cast le_trans (card_le_card hcovHR) card_biUnion_le
   have hsum_bd := thm41_step_vi_sum (N := N) (c := c) (q := q) (r := r) (x := x) (by omega) hsum_N (a := fun d => ((EdR d).card : ℝ)) (b := fun d => ((HdR d).card : ℝ)) hStep6_d;linarith [hsum_ER, hsum_HR, hsum_bd]
 have hP'_card : (P'.card : ℝ) <= (P1.card : ℝ) + (Pge2.card : ℝ) := by
   have hcov : P' ⊆ P1 ∪ Pge2 := fun S hS => by
     by_cases hI : ∃ l r, S = Icc l r; exact mem_union_left _ (mem_filter.mpr ⟨hS, hI⟩)
     exact mem_union_right _ (mem_filter.mpr ⟨hS, hI⟩)
   exact_mod_cast le_trans (card_le_card hcov) (card_union_le _ _)
 have hE'_card : (E'.card : ℝ) <= (E1_X.card : ℝ) + (Ege2_X.card : ℝ) + (E_R.card : ℝ) := by
   have hcov : E' ⊆ E1_X ∪ (Ege2_X ∪ E_R) := fun S hS => by
     by_cases hX : ∃ hne : S.Nonempty, cqr < S.max' hne
     . by_cases hI : ∃ l r, S = Icc l r
       . exact mem_union_left _ (mem_filter.mpr ⟨mem_filter.mpr ⟨hS, hX⟩, hI⟩)
       . exact mem_union_right _ (mem_union_left _ (mem_filter.mpr ⟨mem_filter.mpr ⟨hS, hX⟩, hI⟩))
     . exact mem_union_right _ (mem_union_right _ (mem_filter.mpr ⟨hS, hX⟩))
   have := le_trans (card_le_card hcov) (le_trans (card_union_le _ _) (Nat.add_le_add_left (card_union_le _ _) _));rw [<- add_assoc] at this;exact_mod_cast this
 have hH_card : (H.card : ℝ) <= (HXQ.card : ℝ) + (HXR.card : ℝ) + (HXC.card : ℝ) + (H_R.card : ℝ) := by
   have hcov : H ⊆ HXQ ∪ (HXR ∪ (HXC ∪ H_R)) := fun S hS => by
     obtain ⟨hSH0, hnotbad⟩ := mem_filter.mp hS;obtain ⟨hpI, -, hdt, -, -⟩ := hH0dt S hSH0;have hp_ge := (mem_Icc.mp (mem_of_mem_inter_right hpI)).1;have hp_ne_cq : pH S ≠ cq := fun h => hnotbad (Or.inl h)
     have hp_ne_cqr : pH S ≠ cqr := fun h => hnotbad (Or.inr (Or.inl h))
     have hx_ne_cq : xH S ≠ cq := fun h => hnotbad (Or.inr (Or.inr (Or.inl h)))
     have hx_ne_cqr : xH S ≠ cqr := fun h => hnotbad (Or.inr (Or.inr (Or.inr h)))
     have hx_ne_c : xH S ≠ c := hdt.2.2.2.2.1.symm
     by_cases hp_gt : cqr < pH S
     . by_cases hx_lt_c : xH S < c
       . exact mem_union_right _ (mem_union_right _ (mem_union_left _ (mem_filter.mpr ⟨hS, hp_gt, hx_lt_c⟩)))
       by_cases hx_lt_cq : xH S < cq
       . exact mem_union_left _ (mem_filter.mpr ⟨hS, hp_gt, by omega, hx_lt_cq⟩)
       by_cases hx_lt_cqr : xH S < cqr
       . exact mem_union_right _ (mem_union_left _ (mem_filter.mpr ⟨hS, Or.inl ⟨hp_gt, by omega, hx_lt_cqr⟩⟩))
       . exact absurd ⟨hp_gt, by omega⟩ (hH_XX_empty S hS)
     . by_cases hx_gt : cqr < xH S
       . exact mem_union_right _ (mem_union_left _ (mem_filter.mpr ⟨hS, Or.inr ⟨by omega, hx_gt⟩⟩))
       . exact mem_union_right _ (mem_union_right _ (mem_union_right _ (mem_filter.mpr ⟨hS, by omega, by omega⟩)))
   have h1 := le_trans (card_le_card hcov) (card_union_le _ _);have h2 := card_union_le HXR (HXC ∪ H_R); have h3 := card_union_le HXC H_R;exact_mod_cast (by omega : H.card <= HXQ.card + HXR.card + HXC.card + H_R.card)
 have hslack : (N : ℝ) ^ 2 / 1000000000 <= (((c : ℝ) + (q : ℝ)) ^ 2 + (x : ℝ) ^ 2) / 200 := by
   have h1 : (N : ℝ) <= 1000 * (((c : ℝ) + (q : ℝ)) + (x : ℝ)) := by exact_mod_cast hsmall
   have hsq := sq_nonneg (((c : ℝ) + (q : ℝ)) - (x : ℝ));have h2 : (N : ℝ) ^ 2 <= (1000 * (((c : ℝ) + (q : ℝ)) + (x : ℝ))) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg N) h1 2;linarith [h2, hsq, sq_nonneg (N : ℝ), show (1000 * (((c : ℝ) + (q : ℝ)) + (x : ℝ))) ^ 2 + 1000000 * (((c : ℝ) + (q : ℝ)) - (x : ℝ)) ^ 2 = 2000000 * (((c : ℝ) + (q : ℝ)) ^ 2 + (x : ℝ) ^ 2) by ring]
 have hP_sp : (P.card : ℝ) <= (P'.card : ℝ) + ((P.filter badAP).card : ℝ) := by
   have : P ⊆ P' ∪ P.filter badAP := fun S hS => by
     by_cases h : badAP S; exact mem_union_right _ (mem_filter.mpr ⟨hS, h⟩); exact mem_union_left _ (mem_filter.mpr ⟨hS, h⟩)
   exact_mod_cast le_trans (card_le_card this) (card_union_le _ _)
 have hE_sp : (E.card : ℝ) <= (E'.card : ℝ) + ((E.filter badAP).card : ℝ) := by
   have : E ⊆ E' ∪ E.filter badAP := fun S hS => by
     by_cases h : badAP S; exact mem_union_right _ (mem_filter.mpr ⟨hS, h⟩); exact mem_union_left _ (mem_filter.mpr ⟨hS, h⟩)
   exact_mod_cast le_trans (card_le_card this) (card_union_le _ _)
 have hS_sp : (Sfam.card : ℝ) <= (H.card : ℝ) + ((H0.filter badH).card : ℝ) + ((Sfam \ H0).card : ℝ) := by
   have h1 : Sfam ⊆ H ∪ (H0.filter badH ∪ (Sfam \ H0)) := fun S hS => by
     by_cases h0 : S ∈ H0
     . by_cases hb : badH S
       . exact mem_union_right _ (mem_union_left _ (mem_filter.mpr ⟨h0, hb⟩))
       . exact mem_union_left _ (mem_filter.mpr ⟨h0, hb⟩)
     . exact mem_union_right _ (mem_union_right _ (mem_sdiff.mpr ⟨hS, h0⟩))
   have := le_trans (card_le_card h1) (le_trans (card_union_le _ _) (Nat.add_le_add_left (card_union_le _ _) _));rw [<- add_assoc] at this;exact_mod_cast this
 have hbadH_R : ((H0.filter badH).card : ℝ) <= 4 * (N : ℝ) := by exact_mod_cast hbadH_card
 have hPset_leN : ((Icc cq N).card : ℝ) <= (N : ℝ) := by rw [Nat.card_Icc]; exact_mod_cast (by omega : N + 1 - cq <= N)
 have hSH0_bd' : ((Sfam \ H0).card : ℝ) <= 5 * (N : ℝ) * (2 + Real.log N) + 141 * (N : ℝ) * Real.sqrt N := by
   have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hPset_leN (by norm_num : (0 : ℝ) <= 141)) hsq_nn;linarith [hSH0_bd, this]
 have hcomb_main : (q : ℝ) * (x : ℝ) + (Z - 1) * ((c : ℝ) + (q : ℝ)) * (x : ℝ) + (r : ℝ) * (x : ℝ) + (c : ℝ) * (x : ℝ) = Z * (x : ℝ) * ((q : ℝ) + (c : ℝ)) + (r : ℝ) * (x : ℝ) := by ring
 have hN1 : (1 : ℝ) <= (N : ℝ) := by exact_mod_cast (by omega : 1 <= N)
 have hlog_sq : (1 + Real.log N) ^ 2 <= (2 + Real.log N) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
 have hlog_lin : 2 + Real.log N <= (2 + Real.log N) ^ 2 := by
   have := mul_le_mul_of_nonneg_right (show (1 : ℝ) <= 2 + Real.log N by linarith) (show 0 <= 2 + Real.log N by linarith);linarith [this, show (2 + Real.log N) * (2 + Real.log N) = (2 + Real.log N) ^ 2 by ring]
 have h1_le_log2 : (1 : ℝ) <= (2 + Real.log N) ^ 2 := by linarith [hlog_lin, hlog_nn]
 have hN_le_log2 : (N : ℝ) <= (N : ℝ) * (2 + Real.log N) ^ 2 := by have := mul_le_mul_of_nonneg_left h1_le_log2 (Nat.cast_nonneg N); linarith
 have h4log : (N : ℝ) * (4 + Real.log N) <= 2 * ((N : ℝ) * (2 + Real.log N) ^ 2) := by
   have h1 : 4 + Real.log N <= 2 * (2 + Real.log N) ^ 2 := by linarith [hlog_lin, hlog_nn]
   have := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg N); linarith
 have hNlog1 : (N : ℝ) * (1 + Real.log N) <= (N : ℝ) * (2 + Real.log N) ^ 2 := mul_le_mul_of_nonneg_left (by linarith [hlog_lin]) (Nat.cast_nonneg N);have hNlog2 : (N : ℝ) * (2 + Real.log N) <= (N : ℝ) * (2 + Real.log N) ^ 2 := mul_le_mul_of_nonneg_left hlog_lin (Nat.cast_nonneg N);have hNlogsq : (N : ℝ) * (1 + Real.log N) ^ 2 <= (N : ℝ) * (2 + Real.log N) ^ 2 := mul_le_mul_of_nonneg_left hlog_sq (Nat.cast_nonneg N);have hNsq_nn : 0 <= (N : ℝ) * Real.sqrt N := by positivity
 linarith [hP_sp, hE_sp, hS_sp, hP'_card, hE'_card, hH_card, hStep2, hStep3, hStep4, hStep5, hStep6_sum, hbad_AP_card, hbadH_R, hSH0_bd', hslack, hcomb_main, hNlog1, hNlog2, hNlogsq, hN_le_log2, h4log, hNsq_nn]
lemma non_near_kernel_bound {N c : ℕ} (hN : 10000 <= N) (hc : c ∈ Icc 1 N) {F P E Sfam : Finset (Finset ℕ)} (hF : IsWellInter N F) (hP_sub : P ⊆ F) (hE_sub : E ⊆ F) (hS_sub : Sfam ⊆ F) (hP : ∀ S ∈ P, 3 <= S.card /\ c ∉ S /\ APSet S) (hE : ∀ S ∈ E, 3 <= S.card /\ c ∈ S /\ APSet S) (hSfam : ∀ S ∈ Sfam, c ∈ S /\ ¬ APSet S) {B0 : Finset ℕ} (hB0 : B0 ∈ F) (hcB0 : c ∉ B0) (hB0_sz : 40 * B0.card < 39 * N) : (P.card : ℝ) + (E.card : ℝ) + (Sfam.card : ℝ) <= (N : ℝ) ^ 2 / 2 - (N : ℝ) ^ 2 / 1000000000 + 200 * (N : ℝ) * Real.sqrt N + 200 * (N : ℝ) * (2 + Real.log N) ^ 2 + 100 := by
 have hlog_nn : 0 <= Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 <= N));have hsq_nn : 0 <= Real.sqrt (N : ℝ) := Real.sqrt_nonneg _;have hN0 : (0 : ℝ) <= (N : ℝ) := Nat.cast_nonneg N;have hlog_lin : 2 + Real.log N <= (2 + Real.log N) ^ 2 := by nlinarith
 rcases P.eq_empty_or_nonempty with rfl | hP_ne
 . have h1 := missing_pair_surplus_bound (by omega) hc hF hE_sub hS_sub hE hSfam hB0 hcB0 hB0_sz
   simp only [card_empty, Nat.cast_zero, zero_add];nlinarith [sq_nonneg (N : ℝ)]
 by_cases hright : ∃ P0 ∈ P, ∃ hne : P0.Nonempty, c < P0.min' hne
 . exact szabo_theorem_4_1_right hN hc hF hP_sub hE_sub hS_sub hP hE hSfam hB0 hcB0 hB0_sz hright
 by_cases hleft : ∃ P0 ∈ P, ∃ hne : P0.Nonempty, P0.max' hne < c
 ·
   obtain ⟨hFr, -⟩ := reflectFamily_wellInter hF
   let c' := N + 1 - c
   have hcI := mem_Icc.mp hc;have hc'I : c' ∈ Icc 1 N := mem_Icc.mpr ⟨by omega, by omega⟩
   have hcard_ref : ∀ A ⊆ F, (A.image (reflectSet N)).card = A.card := fun A hA =>
     card_image_of_injOn (fun S hS T hT hST => by
       rw [<- reflectSet_involutive (hF.1 S (hA (mem_coe.mp hS))), hST, reflectSet_involutive (hF.1 T (hA (mem_coe.mp hT)))])
   have hcard_set : ∀ S ∈ F, (reflectSet N S).card = S.card := fun S hSF =>
     card_image_of_injOn (fun a ha b hb h => by
       have := mem_Icc.mp (hF.1 S hSF (mem_coe.mp ha)); have := mem_Icc.mp (hF.1 S hSF (mem_coe.mp hb)); omega)
   have hc'_mem : ∀ S ∈ F, c' ∈ reflectSet N S ↔ c ∈ S := fun S hSF => by
     constructor
     . intro h; obtain ⟨w, hw, hweq⟩ := mem_image.mp h
       have := mem_Icc.mp (hF.1 S hSF hw); have hwc : w = c := by omega
       exact hwc ▸ hw
     . intro h; exact mem_image.mpr ⟨c, h, rfl⟩
   have hAP_ref : ∀ S ∈ F, APSet (reflectSet N S) ↔ APSet S := fun S hSF =>
     ⟨fun h => reflectSet_involutive (hF.1 S hSF) ▸ reflectSet_apSet (fun z hz => by
       obtain ⟨w, hw, rfl⟩ := mem_image.mp hz; have := mem_Icc.mp (hF.1 S hSF hw); exact mem_Icc.mpr ⟨by omega, by omega⟩) h,
      reflectSet_apSet (hF.1 S hSF)⟩
   have hbd := szabo_theorem_4_1_right hN hc'I hFr (image_subset_image hP_sub) (image_subset_image hE_sub) (image_subset_image hS_sub)
     (fun S' hS' => by obtain ⟨S, hS, rfl⟩ := mem_image.mp hS'; exact ⟨(hcard_set S (hP_sub hS)).symm ▸ (hP S hS).1, fun h => (hP S hS).2.1 ((hc'_mem S (hP_sub hS)).mp h), (hAP_ref S (hP_sub hS)).mpr (hP S hS).2.2⟩)
     (fun S' hS' => by obtain ⟨S, hS, rfl⟩ := mem_image.mp hS'; exact ⟨(hcard_set S (hE_sub hS)).symm ▸ (hE S hS).1, (hc'_mem S (hE_sub hS)).mpr (hE S hS).2.1, (hAP_ref S (hE_sub hS)).mpr (hE S hS).2.2⟩)
     (fun S' hS' => by obtain ⟨S, hS, rfl⟩ := mem_image.mp hS'; exact ⟨(hc'_mem S (hS_sub hS)).mpr (hSfam S hS).1, fun h => (hSfam S hS).2 ((hAP_ref S (hS_sub hS)).mp h)⟩)
     (mem_image_of_mem _ hB0) (fun h => hcB0 ((hc'_mem B0 hB0).mp h)) ((hcard_set B0 hB0).symm ▸ hB0_sz)
     (by obtain ⟨P0, hP0, hne0, hmax_lt⟩ := hleft
         refine ⟨reflectSet N P0, mem_image_of_mem _ hP0, hne0.image _, ?_⟩
         have hm := min'_mem (reflectSet N P0) (hne0.image _);obtain ⟨w, hw, hweq⟩ := mem_image.mp hm;have hw_le : w <= P0.max' hne0 := le_max' P0 w hw
         have := mem_Icc.mp (hF.1 P0 (hP_sub hP0) hw); omega)
   rwa [hcard_ref P hP_sub, hcard_ref E hE_sub, hcard_ref Sfam hS_sub] at hbd
 push Not at hright hleft
 have hP_jump : ∀ P0 ∈ P, ∃ hne : P0.Nonempty, P0.min' hne < c /\ c < P0.max' hne := fun P0 hP0 => by
   have hne : P0.Nonempty := card_pos.mp (by have := (hP P0 hP0).1; omega);have h1 := hright P0 hP0 hne; have h2 := hleft P0 hP0 hne;have hne1 : P0.min' hne ≠ c := fun h => (hP P0 hP0).2.1 (h ▸ min'_mem P0 hne)
   have hne2 : P0.max' hne ≠ c := fun h => (hP P0 hP0).2.1 (h ▸ max'_mem P0 hne)
   exact ⟨hne, by omega, by omega⟩
 have hP_noI : ∀ P0 ∈ P, ¬ ∃ l r, P0 = Icc l r := fun P0 hP0 ⟨l, r, hEq⟩ => by
   obtain ⟨hne, h1, h2⟩ := hP_jump P0 hP0;have hl : l <= P0.min' hne := (mem_Icc.mp (show P0.min' hne ∈ Icc l r from hEq ▸ min'_mem P0 hne)).1;have hr : P0.max' hne <= r := (mem_Icc.mp (show P0.max' hne ∈ Icc l r from hEq ▸ max'_mem P0 hne)).2;exact (hP P0 hP0).2.1 (hEq.symm ▸ mem_Icc.mpr ⟨by omega, by omega⟩)
 by_cases hk3 : ∃ P0 ∈ P, ∃ k ≥ 3, ∀ x ∈ P0, ∀ y ∈ P0, x % k = y % k /\ (∀ z, min x y <= z -> z <= max x y -> z % k = x % k -> z ∈ P0)
 . obtain ⟨P0, hP0, k, hk, hstep⟩ := hk3
   have h1 := szabo_theorem_4_2 (by omega) hc hF hP_sub hE_sub hS_sub (fun S hS => ⟨(hP S hS).1, (hP S hS).2.1, (hP S hS).2.2, hP_noI S hS⟩) hE hSfam hP0 hk hstep (hP_jump P0 hP0);nlinarith [sq_nonneg (N : ℝ)]
 . push Not at hk3
   have hP_step2 : ∀ S ∈ P, ∀ x ∈ S, ∀ y ∈ S, x % 2 = y % 2 /\ (∀ z, min x y <= z -> z <= max x y -> z % 2 = x % 2 -> z ∈ S) := by
     intro S hS;obtain ⟨d, hd1, -, -, hmem, -⟩ := apSet_canonical (hP S hS).2.2 (by have := (hP S hS).1; omega)
     have hstep_d : ∀ x ∈ S, ∀ y ∈ S, x % d = y % d /\ (∀ z, min x y <= z -> z <= max x y -> z % d = x % d -> z ∈ S) := by
       intro x hx y hy; have hxm := (hmem x).mp hx; have hym := (hmem y).mp hy;exact ⟨hxm.2.2.trans hym.2.2.symm, fun z hz1 hz2 hzm => (hmem z).mpr ⟨by omega, by omega, hzm.trans hxm.2.2⟩⟩
     have hd_ne1 : d ≠ 1 := fun h1 => hP_noI S hS ⟨S.min' (card_pos.mp (by have := (hP S hS).1; omega)), S.max' (card_pos.mp (by have := (hP S hS).1; omega)), by
       ext z; rw [hmem z, mem_Icc, h1]; simp only [Nat.mod_one, and_true]⟩
     have hd_lt3 : d < 3 := by
       by_contra hge; push Not at hge;obtain ⟨x, hx, y, hy, hbad⟩ := hk3 S hS d hge;obtain ⟨z, hz1, hz2, hzm, hznot⟩ := hbad (hstep_d x hx y hy).1;exact hznot ((hstep_d x hx y hy).2 z hz1 hz2 hzm)
     have hd2 : d = 2 := by omega
     rwa [hd2] at hstep_d
   have h1 := even_pair_parity_surplus_bound (by omega) hc hF hP_sub hE_sub hS_sub hP_ne (fun S hS => ⟨(hP S hS).1, (hP S hS).2.1, (hP S hS).2.2, hP_step2 S hS, hP_jump S hS⟩) hE hSfam;nlinarith [sq_nonneg (N : ℝ)]
lemma upper_bound_eventually : ∀ᶠ N : ℕ in atTop, ∀ F : Finset (Finset ℕ), IsWellInter N F -> (F.card : ℝ) <= (N : ℝ) ^ 2 / 2 + 50 * (N : ℝ) := by
 classical
 have hlog_small : ∀ᶠ N : ℕ in atTop, Real.log (N : ℝ) <= (N : ℝ) ^ (1 / 40 : ℝ) := by
   have h1 := isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 40 by norm_num);have h2 := tendsto_natCast_atTop_atTop.eventually (h1.bound (show (0 : ℝ) < 1 by norm_num))
   filter_upwards [h2, eventually_ge_atTop 2] with N hN hN2
   have hlog0 : 0 <= Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 <= N));have hrp0 : 0 <= (N : ℝ) ^ (1 / 40 : ℝ) := by positivity
   rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul, abs_of_nonneg hlog0, abs_of_nonneg hrp0] at hN;exact hN
 have hrpow_big : ∀ᶠ N : ℕ in atTop, (10 : ℝ) ^ 20 <= (N : ℝ) ^ (1 / 40 : ℝ) := by
   have ht := (tendsto_rpow_atTop (show (0 : ℝ) < 1 / 40 by norm_num)).comp tendsto_natCast_atTop_atTop;exact ht.eventually (eventually_ge_atTop ((10 : ℝ) ^ 20))
 filter_upwards [card_coprime_Ioc_ge_eventually, hlog_small, hrpow_big, eventually_ge_atTop 10000] with
     N hcop_int hlog hbig hN10000
 intro F hF;have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
 have hN1 : (1 : ℝ) <= (N : ℝ) := by exact_mod_cast (by omega : 1 <= N)
 set a := (N : ℝ) ^ (1 / 40 : ℝ)
 have ha_ge : (10 : ℝ) ^ 20 <= a := hbig;have ha_pos : 0 < a := by linarith
 have hpow_mono : ∀ m n : ℕ, m <= n -> a ^ m <= a ^ n := fun m n h => pow_le_pow_right₀ (by linarith) h
 have ha40 : a ^ 40 = (N : ℝ) := by dsimp only [a]; rw [<- Real.rpow_natCast, <- Real.rpow_mul (le_of_lt hNpos)]; norm_num
 have hsqrt_eq : Real.sqrt (N : ℝ) = a ^ 20 := by rw [<- ha40, show a ^ 40 = (a ^ 20) ^ 2 by ring, Real.sqrt_sq (by positivity)]
 have hsqrt4_eq : Real.sqrt (Real.sqrt (N : ℝ)) = a ^ 10 := by rw [hsqrt_eq, show a ^ 20 = (a ^ 10) ^ 2 by ring, Real.sqrt_sq (by positivity)]
 have hlog2_le : ((Nat.log 2 N + 1 : ℕ) : ℝ) <= 3 * a := by
   have hpow : (2 : ℝ) ^ (Nat.log 2 N) <= (N : ℝ) := by exact_mod_cast Nat.pow_log_le_self 2 (by omega)
   have hln : (Nat.log 2 N : ℝ) * Real.log 2 <= Real.log (N : ℝ) := by have := Real.log_le_log (by positivity) hpow; rwa [Real.log_pow] at this
   have hln2 : (1 / 2 : ℝ) <= Real.log 2 := by linarith [Real.log_two_gt_d9]
   push_cast; nlinarith
 set s := Nat.ceil (a ^ 18)
 have hs_lo : a ^ 18 <= (s : ℝ) := Nat.le_ceil _
 have hs_hi : (s : ℝ) <= 2 * a ^ 18 := by
   have hlt := Nat.ceil_lt_add_one (show (0 : ℝ) <= a ^ 18 by positivity);have ha18 : (1 : ℝ) <= a ^ 18 := one_le_pow₀ (by linarith);linarith
 have hs_ge1000 : 1000 <= s := by
   have ha17 : (1 : ℝ) <= a ^ 17 := one_le_pow₀ (by linarith)
   have ha18 : (10 : ℝ) ^ 20 <= a ^ 18 := by
     have := mul_le_mul ha_ge ha17 (by positivity) (by positivity);linarith [this, show a * a ^ 17 = a ^ 18 by ring]
   have hsR : (1000 : ℝ) <= (s : ℝ) := by linarith
   exact_mod_cast hsR
 let F0 := F.filter (fun S => S.card <= 2)
 let FAP := F.filter (fun S => 3 <= S.card /\ APSet S)
 let Bap := F.filter (fun S => 3 <= S.card /\ ¬ APSet S /\ s <= S.card /\ ∃ P : Finset ℕ, P ⊆ S /\ APSet P /\ 24 * S.card <= 25 * P.card)
 let Bnoap := F.filter (fun S => 3 <= S.card /\ ¬ APSet S /\ s <= S.card /\ ∀ P : Finset ℕ, P ⊆ S -> APSet P -> 25 * P.card < 24 * S.card)
 let Sfam := F.filter (fun S => 3 <= S.card /\ ¬ APSet S /\ S.card < s)
 have hF_cov : F ⊆ F0 ∪ (FAP ∪ (Bap ∪ (Bnoap ∪ Sfam))) := fun S hS => by
   by_cases h2 : S.card <= 2; · exact mem_union_left _ (mem_filter.mpr ⟨hS, h2⟩)
   by_cases hap : APSet S; · exact mem_union_right _ (mem_union_left _ (mem_filter.mpr ⟨hS, by omega, hap⟩))
   by_cases hs : s <= S.card
   . by_cases hex : ∃ P : Finset ℕ, P ⊆ S /\ APSet P /\ 24 * S.card <= 25 * P.card
     . exact mem_union_right _ (mem_union_right _ (mem_union_left _ (mem_filter.mpr ⟨hS, by omega, hap, hs, hex⟩)))
     . push Not at hex
       exact mem_union_right _ (mem_union_right _ (mem_union_right _ (mem_union_left _ (mem_filter.mpr ⟨hS, by omega, hap, hs, hex⟩))))
   . exact mem_union_right _ (mem_union_right _ (mem_union_right _ (mem_union_right _ (mem_filter.mpr ⟨hS, by omega, hap, by omega⟩))))
 have hF0_R : (F0.card : ℝ) <= (N : ℝ) + 3 := by exact_mod_cast card_size_le_two hF
 have hBap_R : (Bap.card : ℝ) <= 280 * (N : ℝ) ^ 2 / (s : ℝ) := long_AP_nonAP_bound (by omega) (by omega) (isWellInter_subset hF (filter_subset _ _)) (fun S hS => by obtain ⟨-, -, h1, h2, h3⟩ := mem_filter.mp hS; exact ⟨h1, h2, h3⟩)
 have hBnoap_R : (Bnoap.card : ℝ) <= 20000000 * (N : ℝ) ^ 3 * Real.sqrt (Real.sqrt (N : ℝ)) * ((Nat.log 2 N + 1 : ℕ) : ℝ) / ((s : ℝ) ^ 3) := by
   have hdiv_lb : a ^ 8 / 40 <= ((98 / 100 : ℝ) * (s : ℝ)) / (30 * Real.sqrt (Real.sqrt (N : ℝ))) := by
     rw [hsqrt4_eq, div_le_div_iff₀ (by norm_num) (by positivity)];have : a ^ 8 * (30 * a ^ 10) = 30 * a ^ 18 := by ring
     nlinarith
   have ha8_big : (10 : ℝ) ^ 20 <= a ^ 8 := le_trans ha_ge (by have : (1 : ℝ) <= a ^ 7 := one_le_pow₀ (by linarith); nlinarith);have hbase : a ^ 8 / 80 <= ((98 / 100 : ℝ) * (s : ℝ)) / (30 * Real.sqrt (Real.sqrt (N : ℝ))) - 2 := by linarith
   refine large_nonAP_noap_bound (by omega) hs_ge1000 hcop_int ?_ (by linarith) (isWellInter_subset hF (filter_subset _ _)) (fun S hS => by obtain ⟨-, -, -, h2, h3⟩ := mem_filter.mp hS; exact ⟨h2, h3⟩)
   calc (N : ℝ) = a ^ 40 := ha40.symm
     _ <= (a ^ 8 / 80) ^ 6 := by
       rw [div_pow, le_div_iff₀ (by norm_num), <- pow_mul];have : a ^ 40 * 80 ^ 6 <= a ^ 40 * a ^ 8 := mul_le_mul_of_nonneg_left (by linarith [show (80 : ℝ) ^ 6 <= (10 : ℝ) ^ 20 by norm_num]) (by positivity);linarith [this, show a ^ 40 * a ^ 8 = a ^ (8 * 6) by ring]
     _ <= _ := pow_le_pow_left₀ (by positivity) hbase 6
 have htail_small : (F0.card : ℝ) + (Bap.card : ℝ) + (Bnoap.card : ℝ) <= (N : ℝ) ^ 2 / 10000000000 := by
   have hBap_a : (Bap.card : ℝ) <= 280 * a ^ 62 := by
     refine le_trans hBap_R ?_; rw [div_le_iff₀ (by positivity)]
     have h1 : 280 * (N : ℝ) ^ 2 = 280 * a ^ 62 * a ^ 18 := by rw [<- ha40]; ring
     rw [h1]; exact mul_le_mul_of_nonneg_left hs_lo (by positivity)
   have hBnoap_a : (Bnoap.card : ℝ) <= 60000000 * a ^ 77 := by
     refine le_trans hBnoap_R ?_; rw [div_le_iff₀ (by positivity)]
     rw [hsqrt4_eq];have h1 : 20000000 * (N : ℝ) ^ 3 * a ^ 10 * ((Nat.log 2 N + 1 : ℕ) : ℝ) <= 20000000 * (N : ℝ) ^ 3 * a ^ 10 * (3 * a) := mul_le_mul_of_nonneg_left hlog2_le (by positivity);have h2 : 20000000 * (N : ℝ) ^ 3 * a ^ 10 * (3 * a) = 60000000 * a ^ 77 * (a ^ 18) ^ 3 := by rw [<- ha40]; ring
     have h3 : (a ^ 18) ^ 3 <= (s : ℝ) ^ 3 := pow_le_pow_left₀ (by positivity) hs_lo 3;exact le_trans (h2 ▸ h1) (mul_le_mul_of_nonneg_left h3 (by positivity))
   have hN2_eq : (N : ℝ) ^ 2 = a ^ 80 := by rw [<- ha40]; ring
   have ha3 : (10 : ℝ) ^ 20 <= a ^ 3 := le_trans ha_ge (by simpa using hpow_mono 1 3 (by norm_num))
   have h1 : (F0.card : ℝ) <= a ^ 77 := by
     have h40 : a ^ 40 <= a ^ 76 := hpow_mono 40 76 (by norm_num);have h3le : (3 : ℝ) <= a ^ 76 := le_trans (show (3 : ℝ) <= a by linarith) (by simpa using hpow_mono 1 76 (by norm_num));have hmul := mul_le_mul_of_nonneg_right (show (2 : ℝ) <= a by linarith) (show (0 : ℝ) <= a ^ 76 by positivity);linarith [hF0_R, ha40, h40, h3le, hmul, show a * a ^ 76 = a ^ 77 by ring]
   have h2 : (Bap.card : ℝ) <= 280 * a ^ 77 := by
     have : a ^ 62 <= a ^ 77 := hpow_mono 62 77 (by norm_num);linarith
   have h3 : 60000300 * a ^ 77 <= a ^ 80 / 10000000000 := by
     have : 60000300 * 10000000000 <= a ^ 3 := by linarith [show (60000300 : ℝ) * 10000000000 <= (10 : ℝ) ^ 20 by norm_num]
     have hmul := mul_le_mul_of_nonneg_right this (show (0 : ℝ) <= a ^ 77 by positivity);linarith [hmul, show a ^ 3 * a ^ 77 = a ^ 80 by ring]
   rw [hN2_eq]; linarith
 by_cases hempty : ∀ x ∈ Icc 1 N, ∃ T ∈ Sfam, x ∉ T
 . have hSfam_bd := empty_kernel_small_bound (s := s) (by omega) (isWellInter_subset hF (filter_subset _ _)) (fun S hS => by obtain ⟨-, h3, hnotAP, hlt⟩ := mem_filter.mp hS; exact ⟨by omega, hnotAP, by omega⟩) hempty
   have hFAP_bd := card_AP_all (FAP := FAP) (by omega) hF (filter_subset _ _) (fun S hS => by obtain ⟨-, h3, hAP⟩ := mem_filter.mp hS; exact ⟨h3, hAP⟩)
   have hSfam_a : (Sfam.card : ℝ) <= a ^ 79 := by
     have hs2 : (s : ℝ) ^ 2 <= 4 * a ^ 36 := by have := pow_le_pow_left₀ (Nat.cast_nonneg s) hs_hi 2; linarith [this, show (2 * a ^ 18) ^ 2 = 4 * a ^ 36 by ring]
     have h1 : (s : ℝ) ^ 2 * (N : ℝ) <= 4 * a ^ 76 := by have := mul_le_mul_of_nonneg_right hs2 (le_of_lt hNpos); linarith [this, show 4 * a ^ 36 * (N : ℝ) = 4 * a ^ 76 by rw [<- ha40]; ring]
     have h2 : 4 * (s : ℝ) * (N : ℝ) * (1 + Real.log N) <= 16 * a ^ 59 := by
       have h1log : 1 + Real.log N <= 2 * a := by linarith
       have ha1 : 4 * (s : ℝ) * (N : ℝ) <= 8 * a ^ 58 := by
         have := mul_le_mul_of_nonneg_right hs_hi (le_of_lt hNpos);linarith [this, show 2 * a ^ 18 * (N : ℝ) = 2 * a ^ 58 by rw [<- ha40]; ring]
       have := mul_le_mul ha1 h1log (by positivity) (by positivity);linarith [this, show 8 * a ^ 58 * (2 * a) = 16 * a ^ 59 by ring]
     have h3 : 141 * (s : ℝ) ^ 2 * Real.sqrt N <= 564 * a ^ 56 := by
       rw [hsqrt_eq]; have := mul_le_mul_of_nonneg_right hs2 (show 0 <= a ^ 20 by positivity);linarith [this, show 4 * a ^ 36 * a ^ 20 = 4 * a ^ 56 by ring]
     have h59 : a ^ 59 <= a ^ 76 := hpow_mono 59 76 (by norm_num);have h56 : a ^ 56 <= a ^ 76 := hpow_mono 56 76 (by norm_num)
     have h76 : 600 * a ^ 76 <= a ^ 79 := by
       have h600 : (600 : ℝ) <= a ^ 3 := le_trans (show (600 : ℝ) <= a by linarith) (by simpa using hpow_mono 1 3 (by norm_num));have := mul_le_mul_of_nonneg_right h600 (show 0 <= a ^ 76 by positivity);linarith [this, show a ^ 3 * a ^ 76 = a ^ 79 by ring]
     linarith [hSfam_bd, h1, h2, h3, h59, h56, h76]
   have hF_le : (F.card : ℝ) <= (F0.card : ℝ) + (FAP.card : ℝ) + (Bap.card : ℝ) + (Bnoap.card : ℝ) + (Sfam.card : ℝ) := by
     have h1 := le_trans (card_le_card hF_cov) (card_union_le _ _);have h2 := card_union_le FAP (Bap ∪ (Bnoap ∪ Sfam));have h3 := card_union_le Bap (Bnoap ∪ Sfam); have h4 := card_union_le Bnoap Sfam;exact_mod_cast (by omega : F.card <= F0.card + FAP.card + Bap.card + Bnoap.card + Sfam.card)
   have hN2_eq : (N : ℝ) ^ 2 = a ^ 80 := by rw [<- ha40]; ring
   have ha79 : a ^ 79 <= (N : ℝ) ^ 2 / 100 := by
     rw [hN2_eq]; have := mul_le_mul_of_nonneg_right (show (100 : ℝ) <= a by linarith) (show 0 <= a ^ 79 by positivity);linarith [this, show a * a ^ 79 = a ^ 80 by ring]
   have hNlog : (N : ℝ) * Real.log N + 2 * (N : ℝ) <= (N : ℝ) ^ 2 / 100 := by
     have : (N : ℝ) * Real.log N + 2 * (N : ℝ) <= 3 * a ^ 41 := by
       have := mul_le_mul_of_nonneg_left hlog (le_of_lt hNpos);have hN41 : (N : ℝ) <= a ^ 41 := by rw [<- ha40]; exact hpow_mono 40 41 (by norm_num)
       linarith [this, show (N : ℝ) * a = a ^ 41 by rw [<- ha40]; ring, hN41]
     have h41 : 3 * a ^ 41 <= a ^ 79 := by
       have h3le : (3 : ℝ) <= a ^ 38 := le_trans (show (3 : ℝ) <= a by linarith) (by simpa using hpow_mono 1 38 (by norm_num));have := mul_le_mul_of_nonneg_right h3le (show 0 <= a ^ 41 by positivity);linarith [this, show a ^ 38 * a ^ 41 = a ^ 79 by ring]
     linarith [this, h41, ha79]
   linarith [hF_le, htail_small, hFAP_bd, hSfam_a, ha79, hNlog, show (0 : ℝ) <= (N : ℝ) by positivity]
 push Not at hempty; obtain ⟨c, hcI, hc_all⟩ := hempty
 by_cases hnear : ∀ B ∈ F, c ∉ B -> 39 * N <= 40 * B.card
 . have hlin := near_kernel_linear_bound (by omega) hcI hF hnear
   have hC2 : (((N - 1) * (N - 2) / 2 : ℕ) : ℝ) <= (N : ℝ) ^ 2 / 2 := by
     have h1 : 2 * ((N - 1) * (N - 2) / 2) <= N * N := le_trans (Nat.mul_div_le _ 2) (Nat.mul_le_mul (Nat.sub_le N 1) (Nat.sub_le N 2));have h1R : 2 * (((N - 1) * (N - 2) / 2 : ℕ) : ℝ) <= (N : ℝ) * (N : ℝ) := by exact_mod_cast h1
     linarith [show (N : ℝ) * (N : ℝ) = (N : ℝ) ^ 2 by ring]
   linarith
 push Not at hnear; obtain ⟨B0, hB0, hcB0, hB0_sz⟩ := hnear
 let P := FAP.filter (fun S => c ∉ S)
 let E := FAP.filter (fun S => c ∈ S)
 have hFAP_sp : (FAP.card : ℝ) <= (P.card : ℝ) + (E.card : ℝ) := by
   have : FAP ⊆ P ∪ E := fun S hS => by
     by_cases hcS : c ∈ S; exact mem_union_right _ (mem_filter.mpr ⟨hS, hcS⟩)
     exact mem_union_left _ (mem_filter.mpr ⟨hS, hcS⟩)
   exact_mod_cast le_trans (card_le_card this) (card_union_le _ _)
 have hnnk := non_near_kernel_bound (P := P) (E := E) (Sfam := Sfam) hN10000 hcI hF ((filter_subset _ _).trans (filter_subset _ _)) ((filter_subset _ _).trans (filter_subset _ _)) (filter_subset _ _) (fun S hS => by obtain ⟨hFAPm, hcnot⟩ := mem_filter.mp hS; obtain ⟨-, h3, hAP⟩ := mem_filter.mp hFAPm; exact ⟨h3, hcnot, hAP⟩) (fun S hS => by obtain ⟨hFAPm, hcS⟩ := mem_filter.mp hS; obtain ⟨-, h3, hAP⟩ := mem_filter.mp hFAPm; exact ⟨h3, hcS, hAP⟩) (fun S hS => ⟨hc_all S hS, (mem_filter.mp hS).2.2.1⟩) hB0 hcB0 hB0_sz
 have hF_le : (F.card : ℝ) <= (F0.card : ℝ) + (Bap.card : ℝ) + (Bnoap.card : ℝ) + ((P.card : ℝ) + (E.card : ℝ) + (Sfam.card : ℝ)) := by
   have h1 := le_trans (card_le_card hF_cov) (card_union_le _ _);have h2 := card_union_le FAP (Bap ∪ (Bnoap ∪ Sfam));have h3 := card_union_le Bap (Bnoap ∪ Sfam); have h4 := card_union_le Bnoap Sfam;have hR : (F.card : ℝ) <= (F0.card : ℝ) + (FAP.card : ℝ) + (Bap.card : ℝ) + (Bnoap.card : ℝ) + (Sfam.card : ℝ) := by exact_mod_cast (by omega : F.card <= F0.card + FAP.card + Bap.card + Bnoap.card + Sfam.card)
   linarith
 have herr_small : 200 * (N : ℝ) * Real.sqrt N + 200 * (N : ℝ) * (2 + Real.log N) ^ 2 + 100 <= (N : ℝ) ^ 2 / 2000000000 := by
   have h1 : 200 * (N : ℝ) * Real.sqrt N = 200 * a ^ 60 := by rw [hsqrt_eq, <- ha40]; ring
   have h2 : 200 * (N : ℝ) * (2 + Real.log N) ^ 2 <= 1800 * a ^ 42 := by
     have hlog3 : 2 + Real.log N <= 3 * a := by linarith
     have hsq3 : (2 + Real.log N) ^ 2 <= 9 * a ^ 2 := by
       have := pow_le_pow_left₀ (by linarith [Real.log_nonneg hN1]) hlog3 2;linarith [this, show (3 * a) ^ 2 = 9 * a ^ 2 by ring]
     have := mul_le_mul_of_nonneg_left hsq3 (show 0 <= 200 * (N : ℝ) by positivity);linarith [this, show 200 * (N : ℝ) * (9 * a ^ 2) = 1800 * a ^ 42 by rw [<- ha40]; ring]
   have h42 : a ^ 42 <= a ^ 60 := hpow_mono 42 60 (by norm_num);have h100 : (100 : ℝ) <= a ^ 60 := le_trans (show (100 : ℝ) <= a by linarith) (by simpa using hpow_mono 1 60 (by norm_num))
   have h60 : 2100 * a ^ 60 <= a ^ 80 / 2000000000 := by
     have h20 : (2100 : ℝ) * 2000000000 <= a ^ 20 := le_trans (show (2100 : ℝ) * 2000000000 <= a by linarith [show (2100 : ℝ) * 2000000000 <= (10 : ℝ) ^ 20 by norm_num]) (by simpa using hpow_mono 1 20 (by norm_num));have := mul_le_mul_of_nonneg_right h20 (show 0 <= a ^ 60 by positivity);linarith [this, show a ^ 20 * a ^ 60 = a ^ 80 by ring]
   have hN2_eq : (N : ℝ) ^ 2 = a ^ 80 := by rw [<- ha40]; ring
   rw [hN2_eq]; linarith [h1, h2, h42, h100, h60]
 linarith [hF_le, htail_small, hnnk, herr_small, show (0 : ℝ) <= (N : ℝ) by positivity, sq_nonneg (N : ℝ)]
end OMA.E272
theorem OMA.solution : type_of% @Erdos272.erdos_272.variants.szabo_strong := by
 rw [Asymptotics.isBigO_iff]
 refine ⟨50, ?_⟩
 filter_upwards [OMA.E272.upper_bound_eventually, Filter.eventually_ge_atTop 3] with N hup hN3
 have hlo_nat : (N - 1) * (N - 2) / 2 <= Erdos272.maxArithInterCard N := OMA.E272.lower_bound_maxArithInterCard N hN3
 have hlo : (N : ℝ) ^ 2 / 2 - 2 * (N : ℝ) <= (Erdos272.maxArithInterCard N : ℝ) := by
   have h1 : (N - 1) * (N - 2) <= 2 * ((N - 1) * (N - 2) / 2) + 1 := by omega
   have h1R : ((N - 1 : ℕ) : ℝ) * ((N - 2 : ℕ) : ℝ) <= 2 * (((N - 1) * (N - 2) / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast h1
   rw [Nat.cast_sub (by omega : 1 <= N), Nat.cast_sub (by omega : 2 <= N)] at h1R;push_cast at h1R;have hloR : (((N - 1) * (N - 2) / 2 : ℕ) : ℝ) <= (Erdos272.maxArithInterCard N : ℝ) := by exact_mod_cast hlo_nat
   have hN3R : (3 : ℝ) <= (N : ℝ) := by exact_mod_cast hN3
   linarith [h1R, hloR, show ((N : ℝ) - 1) * ((N : ℝ) - 2) = (N : ℝ) ^ 2 - 3 * (N : ℝ) + 2 by ring]
 have hhi : (Erdos272.maxArithInterCard N : ℝ) <= (N : ℝ) ^ 2 / 2 + 50 * (N : ℝ) := by
   have hne : {n | ∃ A : Finset (Finset ℕ), Erdos272.IsArithInterSet N A /\ A.card = n}.Nonempty := ⟨0, ∅, ⟨Finset.empty_subset _, by simp⟩, rfl⟩
   have hle_fl : Erdos272.maxArithInterCard N <= Nat.floor ((N : ℝ) ^ 2 / 2 + 50 * (N : ℝ)) := by
     unfold Erdos272.maxArithInterCard
     refine csSup_le ?_ ?_
     . exact ⟨0, ∅, ⟨Finset.empty_subset _, by simp⟩, rfl⟩
     . rintro n ⟨A, hA, rfl⟩
       exact Nat.le_floor (hup A (OMA.E272.isWellInter_of_isArithInterSet hA))
   exact le_trans (by exact_mod_cast hle_fl) (Nat.floor_le (by positivity))
 rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_le];have hNabs : |(N : ℝ)| = (N : ℝ) := abs_of_nonneg (Nat.cast_nonneg N);rw [hNabs]
 constructor <;> linarith [Nat.cast_nonneg (α := ℝ) N]
