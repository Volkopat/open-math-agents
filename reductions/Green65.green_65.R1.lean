import FormalConjectures.GreensOpenProblems.«65»
/-! Port of openai/math 3344da59991ed94f9ba711217b29c1d760badfa6 (OAI.Combinatorics.SquareDifference, Apache-2.0), adapted to the pinned Mathlib. -/
namespace OMA.R_Green65_green_65_R1
open Filter Finset
open scoped Topology Pointwise
lemma density_root_bound (d N : ℕ) (hd : 0<d) (hN : 0<N) (δ D a : ℝ)
    (hδ : 0≤δ) (hD : 0≤D) (hh : δ^d≤D*(N:ℝ)^(-a)) :
    δ≤D^((d:ℝ)⁻¹)*(N:ℝ)^(-(a*(d:ℝ)⁻¹)) := by
  have hd0 : (0:ℝ)<d := by exact_mod_cast hd
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have he := Real.rpow_le_rpow (pow_nonneg hδ _) hh (inv_nonneg.mpr hd0.le)
  rw [←Real.rpow_natCast_mul hδ,mul_inv_cancel₀ hd0.ne',Real.rpow_one] at he
  rw [Real.mul_rpow hD (Real.rpow_nonneg hn.le _),←Real.rpow_mul hn.le] at he
  simpa only [neg_mul] using he
lemma natTranslate_sub (N : ℕ) (A : Finset ℤ) (hA : A⊆Icc 1 (N:ℤ)) : (A.image (fun z => (z-1).toNat))⊆range N := by
  intro n hn
  obtain ⟨z,hz,rfl⟩ := mem_image.mp hn
  have hz' := mem_Icc.mp (hA hz)
  rw [mem_range]
  omega
lemma natTranslate_card (N : ℕ) (A : Finset ℤ) (hA : A⊆Icc 1 (N:ℤ)) : ((A.image (fun z => (z-1).toNat))).card=A.card := by
  apply card_image_iff.mpr
  intro z hz w hw he
  change (z-1).toNat=(w-1).toNat at he
  have hz' := (mem_Icc.mp (hA hz)).1
  have hw' := (mem_Icc.mp (hA hw)).1
  omega
lemma natTranslate_free (N : ℕ) (A : Finset ℤ) (hA : A⊆Icc 1 (N:ℤ)) (hf : (∀ a ∈ A, ∀ b ∈ A, ∀ m : ℕ, 1 ≤ m → a - b ≠ (m : ℤ) ^ 2)) :
    ∀ x ∈ ((A.image (fun z => (z-1).toNat))), ∀ y ∈ ((A.image (fun z => (z-1).toNat))), ∀ m : ℕ, 1 ≤ m → y ≠ x+m^2 := by
  intro a ha b hb m hm he
  obtain ⟨z,hz,rfl⟩ := mem_image.mp ha
  obtain ⟨w,hw,rfl⟩ := mem_image.mp hb
  apply hf w hw z hz m hm
  have hz' := (mem_Icc.mp (hA hz)).1
  have hw' := (mem_Icc.mp (hA hw)).1
  have he' := congrArg (fun n : ℕ => (n:ℤ)) he
  push_cast at he'
  omega
open Filter
open scoped Pointwise Topology

theorem green65_of_power_saving (H : ∃ c C : ℝ, 0 < c ∧ ∀ N : ℕ, 1 ≤ N → ∀ A : Finset ℤ,
    A ⊆ Finset.Icc 1 (N : ℤ) → (∀ a ∈ A, ∀ b ∈ A, ∀ m : ℕ, 1 ≤ m → a-b ≠ (m : ℤ)^2) →
    (A.card : ℝ) ≤ C * (N : ℝ) ^ (1-c)) : type_of% @Green65.green_65 := by
  obtain ⟨c,C,hc,H⟩ := H
  let d := min (c/2) (1/2 : ℝ)
  have hd : 0 < d := lt_min (by linarith) (by norm_num)
  have hdc : d < c := lt_of_le_of_lt (min_le_left ..) (by linarith)
  refine ⟨d, hd, lt_of_le_of_lt (min_le_right ..) (by norm_num), ?_⟩
  have ht := (tendsto_rpow_atTop (sub_pos.mpr hdc)).comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually_gt_atTop C, eventually_ge_atTop (1:ℕ)] with N hC hN
  intro A hA hcard
  by_contra h
  have hbound := H N hN A hA (by
    intro a ha b hb m hm he
    exact h ⟨a-b, Finset.sub_mem_sub ha hb, m, by omega, he⟩)
  have hn : 0 < (N:ℝ) := by exact_mod_cast (show 0<N by omega)
  have hlt := mul_lt_mul_of_pos_right (show C < (N:ℝ)^(c-d) from hC) (Real.rpow_pos_of_pos hn (1-c))
  rw [← Real.rpow_add hn, show c-d+(1-c) = 1-d by ring] at hlt
  exact (not_lt_of_ge (hcard.trans hbound)) hlt
lemma combine_bounds (F : ℕ → ℕ → Finset ℕ → ℝ)
    (lower : ∀ᶠ P : ℕ in atTop, ∃ d : ℕ, 0 < d ∧ ∀ N : ℕ, 1 ≤ N → ∀ A : Finset ℕ, A ⊆ range N → ((A.card:ℝ)/N)^d ≤ F P N A)
    (upper : ∀ᶠ P : ℕ in atTop, ∃ a D : ℝ, 0 < a ∧ 1 ≤ D ∧ ∀ N : ℕ, 1 ≤ N → ∀ A : Finset ℕ, A ⊆ range N → (∀ x ∈ A, ∀ y ∈ A, ∀ m : ℕ, 1 ≤ m → y ≠ x+m^2) → F P N A ≤ D*(N:ℝ)^(-a)) : type_of% @Green65.green_65 := by
  obtain ⟨P,⟨d,hd,hL⟩,a,D,ha,hD,hU⟩ := (lower.and upper).exists
  have hd0 : (0:ℝ)<d := by exact_mod_cast hd
  apply green65_of_power_saving
  have hnats : ∃ c C : ℝ, 0<c ∧ ∀N : ℕ, 1≤N → ∀A : Finset ℕ, A⊆range N → (∀ x ∈ A, ∀ y ∈ A, ∀ m : ℕ, 1 ≤ m → y ≠ x+m^2) → (A.card:ℝ)≤C*(N:ℝ)^(1-c) := by
    let c := a*(d:ℝ)⁻¹
    let C := D^((d:ℝ)⁻¹)
    refine ⟨c,C,mul_pos ha (inv_pos.mpr hd0),?_⟩
    intro N hN A hA hf
    have hl := hL N hN A hA
    have hh := hU N hN A hA hf
    have hb := density_root_bound d N hd (by omega) ((A.card:ℝ)/(N:ℝ)) D a
      (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (by linarith) (hl.trans hh)
    have hn : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
    have hb' := mul_le_mul_of_nonneg_right hb hn.le
    rw [div_mul_cancel₀ _ hn.ne'] at hb'
    apply hb'.trans_eq
    change C*(N:ℝ)^(-c)*(N:ℝ)=C*(N:ℝ)^(1-c)
    have hr : (N:ℝ)^(-c)*(N:ℝ)=(N:ℝ)^(1-c) := by
      calc
        _ = (N:ℝ)^(-c)*(N:ℝ)^(1:ℝ) := by rw [Real.rpow_one]
        _ = _ := by rw [←Real.rpow_add hn]; congr 1; ring
    rw [mul_assoc,hr]
  obtain ⟨c,C,hc,h⟩ := hnats
  refine ⟨c,C,hc,?_⟩
  intro N hN A hA hf
  have hh := h N hN _ (natTranslate_sub N A hA) (natTranslate_free N A hA hf)
  rwa [natTranslate_card N A hA] at hh

def H1 : Prop :=
  let F := fun (P N : ℕ) (A : Finset ℕ) => open Finset in
    let H := 24; let T := 80
    let V := Fin (2*T+1) → Equiv.Perm (Fin H)
    let J := {q // q ∈ (Icc P N).filter Nat.Prime}
    haveI : ∀ j : J, NeZero j.1 := fun j => ⟨(mem_filter.1 j.2).2.ne_zero⟩
    let g : (∀ j : J, ZMod j.1) → ℝ := fun x => ∑ U ∈ univ.filter (fun U : Finset J => ∏ j ∈ U, j.1 ≤ ⌊(N:ℝ)^(1/100000:ℝ)⌋₊),
      (N:ℝ)⁻¹ * ∑ n ∈ range N, (if n ∈ A then 1 else 0) * ∏ j ∈ U, ((if x j - n = 0 then (j.1:ℝ) else 0) - 1)
    let M : (q : ℕ) → [NeZero q] → ((V → ZMod q) → ℝ) → ℝ := fun q _ G =>
      ∑ S ∈ (univ : Finset (Fin (2*T+1))).powerset, let E := ({b // b ∉ S} → Equiv.Perm (Fin H)) × Fin ((H.factorial/2)^S.card)
      if S.card ≤ T+1 then (q:ℝ)^(-(S.card:ℝ)/16) *
        univ.expect fun Y : E → ZMod q => univ.expect fun i : V → Fin ((H.factorial/2)^S.card) =>
        (∏ e ∈ (by classical exact if S.card ≤ T then univ.filter fun e : E × E =>
            T+1 ≤ (univ.filter fun b => e.2.1 b = e.1.1 b * finRotate H).card else ∅),
          (by classical exact if Y e.2 - Y e.1 ≠ 0 ∧ IsSquare (Y e.2 - Y e.1) then (1:ℝ) else 0)) *
        Real.exp (1/2 * ∑ v, ∑ w, (∑ b ∈ S, ∑ π : {π : Fin H × Fin H // π.1 < π.2},
            if w = Function.update v b (v b * Equiv.swap π.1.1 π.1.2) then (1/(10*(H:ℝ)^2))^(π.1.2.val - π.1.1.val) else 0) *
          if i v = i w then 1 else 0) *
        G fun v => Y (fun b => v b.1, i v)
      else 0
    ∑ z : ∀ j : J, V → ZMod j.1, (∏ j, (M j.1 fun _ => 1)⁻¹ * M j.1 fun y => if y = z j then 1 else 0) * ∏ v, g fun j => z j v
  ∀ᶠ P : ℕ in atTop, ∃ d : ℕ, 0 < d ∧ ∀ N : ℕ, 1 ≤ N → ∀ A : Finset ℕ, A ⊆ range N → ((A.card:ℝ)/N)^d ≤ F P N A

def H2 : Prop :=
  let F := fun (P N : ℕ) (A : Finset ℕ) => open Finset in
    let H := 24; let T := 80
    let V := Fin (2*T+1) → Equiv.Perm (Fin H)
    let J := {q // q ∈ (Icc P N).filter Nat.Prime}
    haveI : ∀ j : J, NeZero j.1 := fun j => ⟨(mem_filter.1 j.2).2.ne_zero⟩
    let g : (∀ j : J, ZMod j.1) → ℝ := fun x => ∑ U ∈ univ.filter (fun U : Finset J => ∏ j ∈ U, j.1 ≤ ⌊(N:ℝ)^(1/100000:ℝ)⌋₊),
      (N:ℝ)⁻¹ * ∑ n ∈ range N, (if n ∈ A then 1 else 0) * ∏ j ∈ U, ((if x j - n = 0 then (j.1:ℝ) else 0) - 1)
    let M : (q : ℕ) → [NeZero q] → ((V → ZMod q) → ℝ) → ℝ := fun q _ G =>
      ∑ S ∈ (univ : Finset (Fin (2*T+1))).powerset, let E := ({b // b ∉ S} → Equiv.Perm (Fin H)) × Fin ((H.factorial/2)^S.card)
      if S.card ≤ T+1 then (q:ℝ)^(-(S.card:ℝ)/16) *
        univ.expect fun Y : E → ZMod q => univ.expect fun i : V → Fin ((H.factorial/2)^S.card) =>
        (∏ e ∈ (by classical exact if S.card ≤ T then univ.filter fun e : E × E =>
            T+1 ≤ (univ.filter fun b => e.2.1 b = e.1.1 b * finRotate H).card else ∅),
          (by classical exact if Y e.2 - Y e.1 ≠ 0 ∧ IsSquare (Y e.2 - Y e.1) then (1:ℝ) else 0)) *
        Real.exp (1/2 * ∑ v, ∑ w, (∑ b ∈ S, ∑ π : {π : Fin H × Fin H // π.1 < π.2},
            if w = Function.update v b (v b * Equiv.swap π.1.1 π.1.2) then (1/(10*(H:ℝ)^2))^(π.1.2.val - π.1.1.val) else 0) *
          if i v = i w then 1 else 0) *
        G fun v => Y (fun b => v b.1, i v)
      else 0
    ∑ z : ∀ j : J, V → ZMod j.1, (∏ j, (M j.1 fun _ => 1)⁻¹ * M j.1 fun y => if y = z j then 1 else 0) * ∏ v, g fun j => z j v
  ∀ᶠ P : ℕ in atTop, ∃ a D : ℝ, 0 < a ∧ 1 ≤ D ∧ ∀ N : ℕ, 1 ≤ N → ∀ A : Finset ℕ, A ⊆ range N → (∀ x ∈ A, ∀ y ∈ A, ∀ m : ℕ, 1 ≤ m → y ≠ x+m^2) → F P N A ≤ D*(N:ℝ)^(-a)

theorem main : H1 → H2 → type_of% @Green65.green_65 := by
  intro h1 h2
  exact combine_bounds _ h1 h2

end OMA.R_Green65_green_65_R1
