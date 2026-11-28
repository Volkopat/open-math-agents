import Mathlib

/-!
# Singular values of a cyclic Hankel matrix after sampling at twice the frequency

Source: JoJo, https://mathoverflow.net/questions/408662 (CC BY-SA 4.0).
Credit: @connoranderson. The even/odd split is the classical radix-two Fourier identity
of Danielson and Lanczos, also used by Cooley and Tukey (1965).

Sample index zero denotes the first sample at positive time. At twice the sampling
rate the old data occupy the odd zero-based indices. The characteristic polynomial of
the Gram matrix specifies all squared singular values with multiplicity. The final
clause is realized by polynomial time series, at unit time spacing for the fine grid.
Rescaling the time variable gives any positive length of the observation interval.
-/

namespace OMA.S_mo_408662
open Matrix Polynomial Finset

noncomputable def hankel (n : ℕ) (c : ℕ → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => c (i+j).val

noncomputable def transform (n : ℕ) (c : ℕ → ℂ) (z : ℂ) : ℂ :=
  ∑ j ∈ range n, c j*z^j

theorem main :
    (∀ (n : ℕ), 0<n → ∀ (c : ℕ → ℂ) (ζ : ℂ), IsPrimitiveRoot ζ n →
      ((hankel n c)ᴴ * hankel n c).charpoly =
        ∏ i : Fin n, (X-C ((‖transform n c (ζ^i.val)‖^2 : ℝ) : ℂ))) ∧
    (∀ (n : ℕ) (c : ℕ → ℂ) (z : ℂ),
      let E := transform n (fun i => c (2*i)) (z^2)
      let B := transform n (fun i => c (2*i+1)) (z^2)
      transform (2*n) c z = E+z*B ∧ transform (2*n) c (-z) = E-z*B ∧
      (‖z‖=1 →
        |‖transform (2*n) c z‖-‖transform (2*n) c (-z)‖| ≤ 2*‖B‖ ∧
        2*‖B‖ ≤ ‖transform (2*n) c z‖+‖transform (2*n) c (-z)‖)) ∧
    (∀ (N : ℕ) (d : ℕ → ℝ), ∃ P : ℝ[X], ∀ i<N, P.eval ((i:ℝ)+1)=d i) ∧
    ∀ (n : ℕ), 0<n → ∀ (b : ℕ → ℝ) (R : ℝ), ∃ P : ℝ[X],
      (∀ i<n, P.eval (2*((i:ℝ)+1))=b i) ∧
      ∀ z : ℂ, z^(2*n)=1 → R ≤ ‖transform (2*n) (fun i => ((P.eval ((i:ℝ)+1) : ℝ) : ℂ)) z‖ := by
  sorry

end OMA.S_mo_408662
