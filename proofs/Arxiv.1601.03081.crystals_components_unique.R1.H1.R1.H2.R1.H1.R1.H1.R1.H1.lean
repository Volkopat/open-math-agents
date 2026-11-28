import OMAReductions.R_Arxiv_1601_03081_crystals_components_unique_R1_H1_R1_H2_R1_H1_R1_H1_R1
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.ModEq

namespace OMA.CrystalFinite

def candidate (m D : ℕ) : Bool :=
  let c := (D - 1) / m
  let t := Nat.sqrt ((c + 1) / 2)
  let a := (2 * (t + 1)^2 - 1) / m
  decide (m * c + 1 = D ∧ c + 1 = 2 * t^2 ∧
    m * a + 1 = 2 * (t + 1)^2 ∧ 3 ≤ a ∧ D ∣ (a - 1)^2)

private def value : List (ℕ × ℕ) → ℕ
  | [] => 1
  | (p, e) :: tail => p ^ e * value tail

private def checkD (m acc : ℕ) : List (ℕ × ℕ) → Bool
  | [] => !(candidate m acc)
  | (p, e) :: tail =>
    (List.range (e+1)).all fun i => checkD m (acc * p^i) tail

private theorem checkD_sound {m : ℕ} {fs : List (ℕ × ℕ)}
    (hp : ∀ x ∈ fs, x.1.Prime) {acc d : ℕ}
    (hc : checkD m acc fs = true) (hd : d ∣ value fs) :
    candidate m (acc * d) = false := by
  induction fs generalizing acc d with
  | nil =>
    have he : d = 1 := Nat.eq_one_of_dvd_one hd
    simpa [he, checkD] using hc
  | cons pe tail ih =>
    rcases pe with ⟨p,e⟩
    obtain ⟨u,v,hu,hv,rfl⟩ := Nat.dvd_mul.mp
      (show d ∣ p^e * value tail from hd)
    obtain ⟨i,hi,rfl⟩ := (Nat.dvd_prime_pow (hp (p,e) (by simp))).mp hu
    have hs := List.all_eq_true.mp hc i (List.mem_range.mpr (by omega))
    simpa [Nat.mul_assoc] using
      ih (fun x hx => hp x (by simp [hx])) hs hv

private def certified (m : ℕ) (fs : List (ℕ × ℕ)) : Bool :=
  decide (value fs = ((m^2-1)*(m^2-4*m-1))^2) &&
    fs.all (fun x => decide x.1.Prime) && checkD m 1 fs

private theorem use_certificate {m d : ℕ} (fs : List (ℕ × ℕ))
    (hc : certified m fs = true)
    (hd : d ∣ ((m^2-1)*(m^2-4*m-1))^2) : candidate m d = false := by
  simp only [certified, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
  rw [← hc.1.1] at hd
  simpa using checkD_sound hc.1.2 hc.2 hd

theorem no_root_excludes {m d : ℕ} (hm : 1 < m)
    (h : (List.range m).all (fun z => decide ((2*z^2)%m ≠ 1)) = true) :
    candidate m d = false := by
  cases hy : candidate m d with
  | false => rfl
  | true =>
    let c := (d-1)/m
    let t := Nat.sqrt ((c+1)/2)
    let a := (2*(t+1)^2-1)/m
    change decide (m*c+1=d ∧ c+1=2*t^2 ∧ m*a+1=2*(t+1)^2 ∧ 3≤a ∧ d ∣ (a-1)^2) = true at hy
    have hr := (of_decide_eq_true hy).2.2.1
    let x := (t+1)%m
    have hx : x ∈ List.range m := List.mem_range.mpr (Nat.mod_lt _ (by omega))
    have hn := of_decide_eq_true ((List.all_eq_true.mp h) x hx)
    have hc : 2*x^2 ≡ 2*(t+1)^2 [MOD m] := ((Nat.mod_modEq (t+1) m).pow 2).mul_left 2
    have h1 : (2*x^2)%m = 1 := by
      calc
        _ = (2*(t+1)^2)%m := hc
        _ = (m*a+1)%m := by rw [hr]
        _ = 1 := by simp [Nat.add_mod, Nat.mod_eq_of_lt hm]
    exact (hn h1).elim

private def survivors : List ℕ := [23, 31, 41, 47, 49, 71, 73, 79, 89, 97, 103, 113, 119, 127]

private theorem sieve_table :
    (List.range 129).all (fun m => decide (m < 21) ||
      (List.range m).all (fun z => decide ((2*z^2)%m ≠ 1)) || survivors.contains m) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
private theorem cert_23 : certified 23
    [(2, 12), (3, 2), (11, 2), (109, 2)] = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
private theorem cert_31 : certified 31
    [(2, 16), (3, 2), (5, 2), (11, 2), (19, 2)] = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
private theorem cert_41 : certified 41
    [(2, 12), (3, 2), (5, 2), (7, 2), (379, 2)] = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
private theorem cert_47 : certified 47
    [(2, 14), (3, 2), (5, 2), (23, 2), (101, 2)] = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
private theorem cert_49 : certified 49
    [(2, 14), (3, 2), (5, 4), (19, 2), (29, 2)] = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
private theorem cert_71 : certified 71
    [(2, 12), (3, 4), (5, 2), (7, 2), (29, 2), (41, 2)] = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
private theorem cert_73 : certified 73
    [(2, 12), (3, 4), (37, 2), (1259, 2)] = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
private theorem cert_79 : certified 79
    [(2, 14), (3, 2), (5, 2), (13, 2), (1481, 2)] = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
private theorem cert_89 : certified 89
    [(2, 12), (3, 4), (5, 2), (11, 2), (31, 2), (61, 2)] = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
private theorem cert_97 : certified 97
    [(2, 16), (3, 2), (5, 2), (7, 4), (11, 2), (41, 2)] = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
private theorem cert_103 : certified 103
    [(2, 12), (3, 2), (13, 2), (17, 2), (2549, 2)] = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
private theorem cert_113 : certified 113
    [(2, 14), (3, 2), (7, 2), (19, 2), (3079, 2)] = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
private theorem cert_119 : certified 119
    [(2, 12), (3, 2), (5, 2), (11, 2), (59, 2), (311, 2)] = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
private theorem cert_127 : certified 127
    [(2, 20), (3, 4), (5, 2), (7, 2), (11, 2), (71, 2)] = true := by decide +kernel

theorem exclude (m D : ℕ) (hmin : 21 ≤ m) (hmax : m ≤ 128)
    (hD : D ∣ ((m^2-1)*(m^2-4*m-1))^2) : candidate m D = false := by
  by_cases h : (List.range m).all (fun z => decide ((2*z^2)%m ≠ 1)) = true
  · exact no_root_excludes (by omega) h
  have hm := List.all_eq_true.mp sieve_table m (List.mem_range.mpr (by omega))
  have hs : m ∈ survivors := by
    simp only [Bool.or_eq_true, decide_eq_true_eq, List.contains_iff_mem] at hm
    exact hm.resolve_left (fun hn => hn.elim (Nat.not_lt.mpr hmin) h)
  simp only [survivors, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact use_certificate _ cert_23 hD
  · exact use_certificate _ cert_31 hD
  · exact use_certificate _ cert_41 hD
  · exact use_certificate _ cert_47 hD
  · exact use_certificate _ cert_49 hD
  · exact use_certificate _ cert_71 hD
  · exact use_certificate _ cert_73 hD
  · exact use_certificate _ cert_79 hD
  · exact use_certificate _ cert_89 hD
  · exact use_certificate _ cert_97 hD
  · exact use_certificate _ cert_103 hD
  · exact use_certificate _ cert_113 hD
  · exact use_certificate _ cert_119 hD
  · exact use_certificate _ cert_127 hD

end OMA.CrystalFinite

namespace OMA.CrystalFinite

theorem div_resultant {a c m : ℕ} (hm : 21 ≤ m)
    (components : (c + m*a)^2 = 4*((c+1)*(m*a+1)))
    (factor : ((m*c : ℕ) : ℤ)+1 ∣ ((a : ℤ)-1)^2) :
    m*c+1 ∣ ((m^2-1)*(m^2-4*m-1))^2 := by
  have h1 : 1 ≤ m^2 := by nlinarith
  have h2 : 4*m+1 ≤ m^2 := by nlinarith [Nat.mul_le_mul_right m hm]
  have hres := CrystalMultiplier.resultant (by simpa using factor)
    (show ((c : ℤ) + (m : ℤ)*a)^2 = 4*((c+1)*((m : ℤ)*a+1)) by exact_mod_cast components)
  have hcast : ((m^2-4*m-1 : ℕ) : ℤ) = (m : ℤ)^2-4*m-1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega : 4*m ≤ m^2)]
    push_cast
    rfl
  exact_mod_cast (show ((m*c+1 : ℕ) : ℤ) ∣ ((((m^2-1)*(m^2-4*m-1))^2 : ℕ) : ℤ) by
    simpa only [Nat.cast_pow, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sub h1, hcast]
      using hres)

theorem candidate_necessary {a c m t : ℕ} (hm : 21 ≤ m) (ha : 3 ≤ a)
    (left : c+1 = 2*t^2) (right : m*a+1 = 2*(t+1)^2)
    (factor : ((m*c : ℕ) : ℤ)+1 ∣ ((a : ℤ)-1)^2) :
    candidate m (m*c+1) = true := by
  have hc : (m*c+1-1)/m = c := by simp [Nat.mul_div_cancel_left _ (by omega : 0 < m)]
  have ht : Nat.sqrt ((c+1)/2) = t := by rw [left]; simp
  have hb : 2*(t+1)^2-1 = m*a := by omega
  have hdiv : m*a/m = a := Nat.mul_div_cancel_left _ (by omega)
  have hf : m*c+1 ∣ (a-1)^2 := by
    exact_mod_cast (show ((m*c+1 : ℕ) : ℤ) ∣ (((a-1)^2 : ℕ) : ℤ) by
      simpa only [Nat.cast_pow, Nat.cast_sub (by omega : 1 ≤ a), Nat.cast_one, Nat.cast_add]
        using factor)
  simp only [candidate, hc, ht, hb, hdiv, decide_eq_true_eq]
  exact ⟨trivial, left, right, ha, hf⟩

end OMA.CrystalFinite

theorem OMA.solution : OMA.R_Arxiv_1601_03081_crystals_components_unique_R1_H1_R1_H2_R1_H1_R1_H1_R1.H1 := by
  intro a c m t hm hmax ha comp left right factor
  have divides := OMA.CrystalFinite.div_resultant hm comp factor
  have needed := OMA.CrystalFinite.candidate_necessary hm ha left right factor
  have excluded := OMA.CrystalFinite.exclude m (m*c+1) hm hmax divides
  simp_all
