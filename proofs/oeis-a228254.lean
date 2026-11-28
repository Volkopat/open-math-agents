import OMAStatements.S_oeis_a228254

namespace OMA.S_oeis_a228254

open Finset PowerSeries



/-- Shifting an array by a constant does not change its third differences. -/
lemma D_shift {n : ℕ} (x y : Fin (n + 3) → Fin 3) (c : ℤ)
    (h : ∀ i, ((x i).val : ℤ) = (y i).val + c) : D x = D y := by
  funext i
  simp only [D, h]
  ring

/-- The difference of two arrays, indexed by naturals (0 outside the array). -/
def zf {n : ℕ} (x y : Fin (n + 3) → Fin 3) (k : ℕ) : ℤ :=
  if h : k < n + 3 then ((x ⟨k, h⟩).val : ℤ) - (y ⟨k, h⟩).val else 0

lemma zf_bound {n : ℕ} (x y : Fin (n + 3) → Fin 3) (k : ℕ) : -2 ≤ zf x y k ∧ zf x y k ≤ 2 := by
  unfold zf
  split_ifs with h
  · have hx := (x ⟨k, h⟩).isLt
    have hy := (y ⟨k, h⟩).isLt
    constructor <;> omega
  · omega

lemma zf_rec {n : ℕ} (x y : Fin (n + 3) → Fin 3) (hD : D x = D y) (k : ℕ) (hk : k < n) :
    zf x y (k + 3) - 3 * zf x y (k + 2) + 3 * zf x y (k + 1) - zf x y k = 0 := by
  have h := congrFun hD ⟨k, hk⟩
  simp only [D] at h
  unfold zf
  rw [dif_pos (by omega), dif_pos (by omega), dif_pos (by omega), dif_pos (by omega)]
  linarith

lemma zf_window {n : ℕ} (x y : Fin (n + 3) → Fin 3) (hD : D x = D y) (p : ℕ) (hp : p + 6 < n + 3) :
    zf x y (p + 1) = zf x y p ∧ zf x y (p + 2) = zf x y p ∧ zf x y (p + 3) = zf x y p ∧
      zf x y (p + 4) = zf x y p ∧ zf x y (p + 5) = zf x y p ∧ zf x y (p + 6) = zf x y p := by
  have e0 := zf_rec x y hD p (by omega)
  have e1 := zf_rec x y hD (p + 1) (by omega)
  have e2 := zf_rec x y hD (p + 2) (by omega)
  have e3 := zf_rec x y hD (p + 3) (by omega)
  have b0 := zf_bound x y p
  have b1 := zf_bound x y (p + 1)
  have b2 := zf_bound x y (p + 2)
  have b3 := zf_bound x y (p + 3)
  have b4 := zf_bound x y (p + 4)
  have b5 := zf_bound x y (p + 5)
  have b6 := zf_bound x y (p + 6)
  simp only [show p + 1 + 3 = p + 4 from rfl, show p + 1 + 2 = p + 3 from rfl,
    show p + 1 + 1 = p + 2 from rfl, show p + 2 + 3 = p + 5 from rfl,
    show p + 2 + 2 = p + 4 from rfl, show p + 2 + 1 = p + 3 from rfl,
    show p + 3 + 3 = p + 6 from rfl, show p + 3 + 2 = p + 5 from rfl,
    show p + 3 + 1 = p + 4 from rfl] at e1 e2 e3
  generalize zf x y p = z0 at *
  generalize zf x y (p + 1) = z1 at *
  generalize zf x y (p + 2) = z2 at *
  generalize zf x y (p + 3) = z3 at *
  generalize zf x y (p + 4) = z4 at *
  generalize zf x y (p + 5) = z5 at *
  generalize zf x y (p + 6) = z6 at *
  have hb : z0 - 2 * z3 + z6 = 9 * (z2 - 2 * z1 + z0) := by linarith
  have hb0 : z2 - 2 * z1 + z0 = 0 := by omega
  have h6 : z6 - z0 = 6 * (z1 - z0) := by linarith
  have h10 : z1 = z0 := by omega
  omega

/-- For n >= 4, arrays with the same third differences differ by a constant. -/
lemma rigid {n : ℕ} (hn : 4 ≤ n) (x y : Fin (n + 3) → Fin 3) (hD : D x = D y) :
    ∀ i : Fin (n + 3), ((x i).val : ℤ) - (y i).val = ((x 0).val : ℤ) - (y 0).val := by
  have step : ∀ k, k + 1 < n + 3 → zf x y (k + 1) = zf x y k := by
    intro k hk
    by_cases hkp : k ≤ n - 4
    · exact (zf_window x y hD k (by omega)).1
    · have w := zf_window x y hD (n - 4) (by omega)
      have hk' : k = n - 4 + 1 ∨ k = n - 4 + 2 ∨ k = n - 4 + 3 ∨ k = n - 4 + 4 ∨
          k = n - 4 + 5 := by omega
      obtain ⟨w1, w2, w3, w4, w5, w6⟩ := w
      rcases hk' with rfl | rfl | rfl | rfl | rfl
      · rw [w2, w1]
      · rw [w3, w2]
      · rw [w4, w3]
      · rw [w5, w4]
      · rw [w6, w5]
  have all : ∀ k, k < n + 3 → zf x y k = zf x y 0 := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih => intro hk; rw [step k hk, ih (by omega)]
  intro i
  have := all i.val i.isLt
  unfold zf at this
  rw [dif_pos i.isLt, dif_pos (by omega)] at this
  exact this

/-- The arrays that contain a 0. -/
def Z (N : ℕ) : Finset (Fin N → Fin 3) := (univ : Finset (Fin N → Fin 3)).filter (fun x => ∃ i, x i = 0)

lemma card_Z (N : ℕ) : (Z N).card = 3 ^ N - 2 ^ N := by
  have h := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin N → Fin 3)))
    (fun x => ∃ i, x i = 0)
  have e : (univ : Finset (Fin N → Fin 3)).filter (fun x => ¬ ∃ i, x i = 0) =
      Fintype.piFinset (fun _ : Fin N => (univ : Finset (Fin 3)).erase 0) := by
    ext x
    simp [Fintype.mem_piFinset]
  rw [e, Fintype.card_piFinset_const, Finset.card_erase_of_mem (Finset.mem_univ _)] at h
  simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    show (3 : ℕ) - 1 = 2 from rfl] at h
  unfold Z
  omega

lemma image_eq (n : ℕ) : (univ : Finset (Fin (n + 3) → Fin 3)).image D = (Z (n + 3)).image D := by
  apply Finset.Subset.antisymm _ (Finset.image_subset_image (Finset.subset_univ _))
  intro d hd
  rw [Finset.mem_image] at hd ⊢
  obtain ⟨x, _, rfl⟩ := hd
  by_cases h0 : ∃ i, x i = 0
  · exact ⟨x, Finset.mem_filter.2 ⟨Finset.mem_univ _, h0⟩, rfl⟩
  · push_neg at h0
    by_cases h1 : ∃ i, x i = 1
    · refine ⟨fun i => ⟨(x i).val - 1, by omega⟩, ?_, ?_⟩
      · obtain ⟨i, hi⟩ := h1
        refine Finset.mem_filter.2 ⟨Finset.mem_univ _, i, ?_⟩
        ext
        simp [hi]
      · apply D_shift _ _ (-1)
        intro i
        have hi : (x i).val ≠ 0 := fun h => h0 i (Fin.ext h)
        simp only
        omega
    · push_neg at h1
      refine ⟨fun _ => 0, Finset.mem_filter.2 ⟨Finset.mem_univ _, ⟨0, by omega⟩, rfl⟩, ?_⟩
      apply D_shift _ _ (-2)
      intro i
      have hi0 : (x i).val ≠ 0 := fun h => h0 i (Fin.ext h)
      have hi1 : (x i).val ≠ 1 := fun h => h1 i (Fin.ext h)
      have := (x i).isLt
      simp only [Fin.val_zero]
      omega

lemma injOn_Z {n : ℕ} (hn : 4 ≤ n) : Set.InjOn D (Z (n + 3) : Set (Fin (n + 3) → Fin 3)) := by
  intro x hx y hy hD
  simp only [Z, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hx hy
  have hr := rigid hn x y hD
  obtain ⟨i, hi⟩ := hx
  obtain ⟨j, hj⟩ := hy
  have ci := hr i
  have cj := hr j
  rw [hi] at ci
  rw [hj] at cj
  simp only [Fin.val_zero, Nat.cast_zero] at ci cj
  have hyi := (y i).isLt
  have hxj := (x j).isLt
  funext k
  have ck := hr k
  apply Fin.ext
  have : ((x k).val : ℤ) = (y k).val := by
    have h1 : (0 : ℤ) ≤ (y i).val := by positivity
    have h2 : (0 : ℤ) ≤ (x j).val := by positivity
    linarith
  exact_mod_cast this

/-- Barker's closed form, for n > 3. -/
theorem closed_form : ∀ n : ℕ, 3 < n → a n = 3 ^ (3 + n) - 2 ^ (3 + n) := by
  intro n hn
  unfold a
  rw [image_eq, Finset.card_image_of_injOn (injOn_Z (by omega)), card_Z,
    show n + 3 = 3 + n by omega]

/-- An injective encoding of difference vectors with entries in [-8, 8]. -/
def enc1 (d : Fin 1 → ℤ) : ℤ := d 0

def enc2 (d : Fin 2 → ℤ) : ℤ := d 0 + 17 * d 1

def enc3 (d : Fin 3 → ℤ) : ℤ := d 0 + 17 * d 1 + 289 * d 2

lemma D_bound {n : ℕ} (x : Fin (n + 3) → Fin 3) (i : Fin n) : -8 ≤ D x i ∧ D x i ≤ 8 := by
  unfold D
  have h0 := (x ⟨i.val + 3, by omega⟩).isLt
  have h1 := (x ⟨i.val + 2, by omega⟩).isLt
  have h2 := (x ⟨i.val + 1, by omega⟩).isLt
  have h3 := (x ⟨i.val, by omega⟩).isLt
  constructor <;> omega

lemma card_via_enc {m : ℕ} (enc : (Fin m → ℤ) → ℤ)
    (henc : ∀ d d' : Fin m → ℤ, (∀ i, -8 ≤ d i ∧ d i ≤ 8) → (∀ i, -8 ≤ d' i ∧ d' i ≤ 8) →
      enc d = enc d' → d = d') :
    a m = ((univ : Finset (Fin (m + 3) → Fin 3)).image (fun x => enc (D x))).card := by
  unfold a
  rw [show (fun x => enc (D x)) = enc ∘ D from rfl, ← Finset.image_image,
    Finset.card_image_of_injOn (f := enc)]
  intro d hd d' hd' h
  simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hd hd'
  obtain ⟨x, rfl⟩ := hd
  obtain ⟨y, rfl⟩ := hd'
  exact henc _ _ (D_bound x) (D_bound y) h

lemma enc1_inj : ∀ d d' : Fin 1 → ℤ, (∀ i, -8 ≤ d i ∧ d i ≤ 8) → (∀ i, -8 ≤ d' i ∧ d' i ≤ 8) →
    enc1 d = enc1 d' → d = d' := by
  intro d d' hd hd' h
  funext i
  fin_cases i
  have := hd 0
  have := hd' 0
  simp only [enc1] at h
  simp only [Fin.zero_eta, Fin.isValue]
  omega

lemma enc2_inj : ∀ d d' : Fin 2 → ℤ, (∀ i, -8 ≤ d i ∧ d i ≤ 8) → (∀ i, -8 ≤ d' i ∧ d' i ≤ 8) →
    enc2 d = enc2 d' → d = d' := by
  intro d d' hd hd' h
  have := hd 0
  have := hd 1
  have := hd' 0
  have := hd' 1
  simp only [enc2] at h
  funext i
  fin_cases i <;> simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one] <;> omega

lemma enc3_inj : ∀ d d' : Fin 3 → ℤ, (∀ i, -8 ≤ d i ∧ d i ≤ 8) → (∀ i, -8 ≤ d' i ∧ d' i ≤ 8) →
    enc3 d = enc3 d' → d = d' := by
  intro d d' hd hd' h
  have := hd 0
  have := hd 1
  have := hd 2
  have := hd' 0
  have := hd' 1
  have := hd' 2
  simp only [enc3] at h
  funext i
  fin_cases i <;> simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk] <;> omega

/-- Enumerating the arrays through their base-3 codes, with an integer-valued g shifted to be
nonnegative. -/
lemma card_reindex {m : ℕ} (g : (Fin (m + 3) → Fin 3) → ℤ) (S : ℤ) (hS : ∀ x, 0 ≤ g x + S) :
    ((univ : Finset (Fin (m + 3) → Fin 3)).image g).card =
      ((univ : Finset (Fin (3 ^ (m + 3)))).image
        (fun k => (g (finFunctionFinEquiv.symm k) + S).toNat)).card := by
  have e1 : (univ : Finset (Fin (m + 3) → Fin 3)) =
      (univ : Finset (Fin (3 ^ (m + 3)))).image finFunctionFinEquiv.symm := by
    rw [← Finset.map_univ_equiv finFunctionFinEquiv.symm, Finset.map_eq_image]
    rfl
  have e2 : (univ : Finset (Fin (3 ^ (m + 3)))).image
      (fun k => (g (finFunctionFinEquiv.symm k) + S).toNat) =
      ((univ : Finset (Fin (3 ^ (m + 3)))).image (g ∘ finFunctionFinEquiv.symm)).image
        (fun z => (z + S).toNat) := by
    rw [Finset.image_image]
    rfl
  rw [e1, Finset.image_image, e2, Finset.card_image_of_injOn (f := fun z => (z + S).toNat)]
  intro z hz z' hz' h
  simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range,
    Function.comp_apply] at hz hz'
  obtain ⟨k, rfl⟩ := hz
  obtain ⟨k', rfl⟩ := hz'
  have h1 := hS (finFunctionFinEquiv.symm k)
  have h2 := hS (finFunctionFinEquiv.symm k')
  simp only at h
  omega

lemma testBit_foldl {n : ℕ} (f : Fin n → ℕ) (L : List (Fin n)) (m i : ℕ) :
    (L.foldl (fun m k => m ||| (1 <<< f k)) m).testBit i = true ↔
      m.testBit i = true ∨ ∃ k ∈ L, f k = i := by
  induction L generalizing m with
  | nil => simp
  | cons k L ih =>
    rw [List.foldl_cons, ih]
    simp only [Nat.testBit_or, Bool.or_eq_true, Nat.one_shiftLeft, Nat.testBit_two_pow,
      decide_eq_true_eq, List.mem_cons]
    constructor
    · rintro ((h | h) | ⟨k', hk', h'⟩)
      · exact Or.inl h
      · exact Or.inr ⟨k, Or.inl rfl, h⟩
      · exact Or.inr ⟨k', Or.inr hk', h'⟩
    · rintro (h | ⟨k', hk' | hk', h'⟩)
      · exact Or.inl (Or.inl h)
      · subst hk'
        exact Or.inl (Or.inr h')
      · exact Or.inr ⟨k', hk', h'⟩

/-- The size of an image, read off a bit mask. -/
lemma card_image_bits {n B : ℕ} (f : Fin n → ℕ) (hf : ∀ k, f k < B) :
    ((univ : Finset (Fin n)).image f).card =
      ((range B).filter (fun i =>
        ((List.finRange n).foldl (fun m k => m ||| (1 <<< f k)) 0).testBit i = true)).card := by
  congr 1
  ext i
  rw [Finset.mem_image, Finset.mem_filter, Finset.mem_range, testBit_foldl]
  simp only [Finset.mem_univ, true_and, Nat.zero_testBit, Bool.false_eq_true, false_or,
    List.mem_finRange]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨hf k, k, rfl⟩
  · rintro ⟨_, k, rfl⟩
    exact ⟨k, rfl⟩

lemma hS1 (x : Fin 4 → Fin 3) : 0 ≤ enc1 (D x) + 8 := by
  have := D_bound x 0; simp only [enc1]; omega

lemma hS2 (x : Fin 5 → Fin 3) : 0 ≤ enc2 (D x) + 144 := by
  have := D_bound x 0; have := D_bound x 1; simp only [enc2]; omega

lemma hS3 (x : Fin 6 → Fin 3) : 0 ≤ enc3 (D x) + 2456 := by
  have := D_bound x 0; have := D_bound x 1; have := D_bound x 2; simp only [enc3]; omega

lemma hB1 (k : Fin (3 ^ 4)) : (enc1 (D (finFunctionFinEquiv.symm k)) + 8).toNat < 17 := by
  have := D_bound (finFunctionFinEquiv.symm k) 0; simp only [enc1]; omega

lemma hB2 (k : Fin (3 ^ 5)) : (enc2 (D (finFunctionFinEquiv.symm k)) + 144).toNat < 289 := by
  have := D_bound (finFunctionFinEquiv.symm k) 0; have := D_bound (finFunctionFinEquiv.symm k) 1
  simp only [enc2]; omega

lemma hB3 (k : Fin (3 ^ 6)) : (enc3 (D (finFunctionFinEquiv.symm k)) + 2456).toNat < 4913 := by
  have := D_bound (finFunctionFinEquiv.symm k) 0; have := D_bound (finFunctionFinEquiv.symm k) 1
  have := D_bound (finFunctionFinEquiv.symm k) 2
  simp only [enc3]; omega

lemma mask1 : (List.finRange (3 ^ 4)).foldl
    (fun m k => m ||| (1 <<< (enc1 (D (finFunctionFinEquiv.symm k)) + 8).toNat)) 0 = 131071 := by
  decide +kernel

lemma mask2 : (List.finRange (3 ^ 5)).foldl
    (fun m k => m ||| (1 <<< (enc2 (D (finFunctionFinEquiv.symm k)) + 144).toNat)) 0 =
    53123500198324685978261925482267208774604646993699752015704766839479569192908341248 := by
  decide +kernel

lemma mask3 : (List.finRange (3 ^ 6)).foldl
    (fun m k => m ||| (1 <<< (enc3 (D (finFunctionFinEquiv.symm k)) + 2456).toNat)) 0 =
    28254284650574002730470244298910622587147011419295693926470664794704916622526954971993092562454607922483210653225833898654629742141367325271780328918794169143085582128904003490246343395784767314492029233302045430570531523705818860770924645652247825788844815743960665946918500297725799385653538746884337414678661766640490596897186353978502525720163691586473678028758083957727765900469095437983863915472243499309714777398700968351903522617351869480705369907053287885228982551680863088615723060008623120141088195795923343772928423887056801597873231873865928940697975070561857059155558194189363369275459539273031413491838148564365789051176536394610401946858908241862815262899941912458309980006581300938634760657390553501878159321871146129211037180902343589244063765412413500951672713829697648222598965477907659846011387571783065756255676908632226036581100068329969805730936610307668489515167931209897555114666550507479958179871566760573075175223944341185282478829136538453538871596362095030150440191168092259407066869371481870354260724912168669254271470840549602605633335186262072592743233843862115343162910044004014735834172780541910252389739627308179731047597068489253473853679463107289187430347756461548286223546485535949691272957320607565120765788760798776175092483887542881019397208115754054102269148912473791630690159033758368711283536593921072374092146429746132694535422958219189601214006247668133658624 := by
  decide +kernel

lemma count1 : ((range 17).filter (fun i => (131071 : ℕ).testBit i = true)).card = 17 := by
  decide +kernel

lemma count2 : ((range 289).filter (fun i =>
    (53123500198324685978261925482267208774604646993699752015704766839479569192908341248 :
      ℕ).testBit i = true)).card = 143 := by
  decide +kernel

lemma count3 : ((range 4913).filter (fun i =>
    (28254284650574002730470244298910622587147011419295693926470664794704916622526954971993092562454607922483210653225833898654629742141367325271780328918794169143085582128904003490246343395784767314492029233302045430570531523705818860770924645652247825788844815743960665946918500297725799385653538746884337414678661766640490596897186353978502525720163691586473678028758083957727765900469095437983863915472243499309714777398700968351903522617351869480705369907053287885228982551680863088615723060008623120141088195795923343772928423887056801597873231873865928940697975070561857059155558194189363369275459539273031413491838148564365789051176536394610401946858908241862815262899941912458309980006581300938634760657390553501878159321871146129211037180902343589244063765412413500951672713829697648222598965477907659846011387571783065756255676908632226036581100068329969805730936610307668489515167931209897555114666550507479958179871566760573075175223944341185282478829136538453538871596362095030150440191168092259407066869371481870354260724912168669254271470840549602605633335186262072592743233843862115343162910044004014735834172780541910252389739627308179731047597068489253473853679463107289187430347756461548286223546485535949691272957320607565120765788760798776175092483887542881019397208115754054102269148912473791630690159033758368711283536593921072374092146429746132694535422958219189601214006247668133658624 :
      ℕ).testBit i = true)).card = 621 := by
  decide +kernel

lemma a1 : a 1 = 17 := by
  have h := (card_via_enc enc1 enc1_inj).trans
    ((card_reindex (fun x => enc1 (D x)) 8 hS1).trans (card_image_bits _ hB1))
  rw [mask1] at h
  exact h.trans count1

lemma a2 : a 2 = 143 := by
  have h := (card_via_enc enc2 enc2_inj).trans
    ((card_reindex (fun x => enc2 (D x)) 144 hS2).trans (card_image_bits _ hB2))
  rw [mask2] at h
  exact h.trans count2

lemma a3 : a 3 = 621 := by
  have h := (card_via_enc enc3 enc3_inj).trans
    ((card_reindex (fun x => enc3 (D x)) 2456 hS3).trans (card_image_bits _ hB3))
  rw [mask3] at h
  exact h.trans count3

/-- Controls: the entry's data a(1..11). -/
theorem controls : (List.range 11).map (fun i => a (i + 1)) =
    [17, 143, 621, 2059, 6305, 19171, 58025, 175099, 527345, 1586131, 4766585] := by
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append, List.map_append]
  rw [a1, a2, a3, closed_form 4 (by norm_num), closed_form 5 (by norm_num),
    closed_form 6 (by norm_num), closed_form 7 (by norm_num), closed_form 8 (by norm_num),
    closed_form 9 (by norm_num), closed_form 10 (by norm_num), closed_form 11 (by norm_num)]
  norm_num

lemma a_q (m : ℕ) : (a (m + 4) : ℚ) = 27 * 3 ^ (m + 4) - 8 * 2 ^ (m + 4) := by
  rw [closed_form (m + 4) (by omega), Nat.cast_sub (Nat.pow_le_pow_left (by norm_num) _)]
  push_cast
  ring

/-- Barker's g.f.: Sum_{n >= 1} a(n) x^n = x(17 + 58x + 8x^2 - 188x^3 - 264x^4)/((1-2x)(1-3x)). -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
    ((1 - 2 * X) * (1 - 3 * X)) = X * (17 + 58 * X + 8 * X ^ 2 - 188 * X ^ 3 - 264 * X ^ 4) := by
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * ((1 - 2 * X) * (1 - 3 * X)) = A - C (5 : ℚ) * (A * X ^ 1) + C (6 : ℚ) * (A * X ^ 2) := by
    rw [show (C (5 : ℚ) : ℚ⟦X⟧) = 5 from map_ofNat C 5,
      show (C (6 : ℚ) : ℚ⟦X⟧) = 6 from map_ofNat C 6]
    ring
  have e2 : (X : ℚ⟦X⟧) * (17 + 58 * X + 8 * X ^ 2 - 188 * X ^ 3 - 264 * X ^ 4) =
      C (17 : ℚ) * X ^ 1 + C (58 : ℚ) * X ^ 2 + C (8 : ℚ) * X ^ 3 - C (188 : ℚ) * X ^ 4 -
        C (264 : ℚ) * X ^ 5 := by
    rw [show (C (17 : ℚ) : ℚ⟦X⟧) = 17 from map_ofNat C 17,
      show (C (58 : ℚ) : ℚ⟦X⟧) = 58 from map_ofNat C 58,
      show (C (8 : ℚ) : ℚ⟦X⟧) = 8 from map_ofNat C 8,
      show (C (188 : ℚ) : ℚ⟦X⟧) = 188 from map_ofNat C 188,
      show (C (264 : ℚ) : ℚ⟦X⟧) = 264 from map_ofNat C 264]
    ring
  rw [e1, e2]
  ext n
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_C, hA, coeff_mk]
  have a4 : a 4 = 2059 := by rw [closed_form 4 (by norm_num)]; norm_num
  have a5 : a 5 = 6305 := by rw [closed_form 5 (by norm_num)]; norm_num
  rcases Nat.lt_or_ge n 6 with hn | hn
  · interval_cases n <;> simp [a1, a2, a3, a4, a5] <;> norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
    have h0 := a_q (m + 2)
    have h1 := a_q (m + 1)
    have h2 := a_q m
    simp only [show m + 2 + 4 = m + 6 from rfl, show m + 1 + 4 = m + 5 from rfl] at h0 h1
    simp only [show m + 6 - 1 = m + 5 by omega, show m + 6 - 2 = m + 4 by omega,
      show m + 6 - 3 = m + 3 by omega, show m + 6 - 4 = m + 2 by omega,
      show m + 6 - 5 = m + 1 by omega, show ¬ m + 6 = 0 by omega, show ¬ m + 5 = 0 by omega,
      show ¬ m + 4 = 0 by omega, show ¬ m + 3 = 0 by omega, show ¬ m + 2 = 0 by omega,
      show ¬ m + 1 = 0 by omega, show 1 ≤ m + 6 by omega, show 2 ≤ m + 6 by omega,
      show 3 ≤ m + 6 by omega, show 4 ≤ m + 6 by omega, show 5 ≤ m + 6 by omega, if_true,
      if_false]
    rw [h0, h1, h2]
    ring

/-- Both of Barker's conjectures. -/
theorem conjecture : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
    ((1 - 2 * X) * (1 - 3 * X)) = X * (17 + 58 * X + 8 * X ^ 2 - 188 * X ^ 3 - 264 * X ^ 4) ∧
    ∀ n : ℕ, 3 < n → a n = 3 ^ (3 + n) - 2 ^ (3 + n) :=
  ⟨gf, closed_form⟩

end OMA.S_oeis_a228254

theorem OMA.solution : type_of% @OMA.S_oeis_a228254.main :=
  OMA.S_oeis_a228254.conjecture
