/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleContour
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighMassPolynomial
import all PseudoPrime.LLS.PaperStatements.ShiftedPoleKernel

/-! # Absolute value of the middle shifted-pole kernel -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Factor the finite middle kernel into the squared polynomial numerator and
one common pole denominator. The missing three terms have zero coefficients. -/
public theorem middle_pole_kernel_factor (Q : Polynomial ℚ) {N : ℕ} (hQ : 2 * Q.natDegree + 3 ≤ N)
    {a : ℝ} (ha : 1 / 2 < a) (b : ℝ) {s : ℂ} (hs : s + (a : ℂ) ≠ 0) :
    (∑ i ∈ Finset.Ico 3 (N + 1),
        ((Q ^ 2).coeff (N - i) : ℂ) *
          (LLS.PaperStatements.shiftedPoleKernel (max 1 i) a b (le_max_left _ _) ha).function s) =
      Complex.exp ((b : ℂ) * s) * (Q.eval₂ (Rat.castHom ℂ) (s + (a : ℂ))) ^ 2 /
        (s + (a : ℂ)) ^ (N + 1) := by
  let v := s + (a : ℂ)
  let A := Complex.exp ((b : ℂ) * s)
  have hP : (Q ^ 2).natDegree ≤ N :=
    Polynomial.natDegree_pow_le.trans ((Nat.le_add_right _ _).trans hQ)
  have he :
    (Q.eval₂ (Rat.castHom ℂ) v) ^ 2 =
      ∑ j ∈ Finset.range (N + 1), ((Q ^ 2).coeff j : ℂ) * v ^ j := by
    rw [← Polynomial.eval₂_pow,
      Polynomial.eval₂_eq_sum_range' (f := Rat.castHom ℂ) (Nat.lt_succ_of_le hP)]
    rfl
  change _ = A * (Q.eval₂ (Rat.castHom ℂ) v) ^ 2 / v ^ (N + 1)
  rw [he, Finset.mul_sum, Finset.sum_div]
  rw [← Finset.sum_range_reflect (fun j ↦ A * (((Q ^ 2).coeff j : ℂ) * v ^ j) / v ^ (N + 1))]
  simp only [Nat.add_sub_cancel]
  have hsub : Finset.Ico 3 (N + 1) ⊆ Finset.range (N + 1) := fun i hi ↦
    Finset.mem_range.mpr (Finset.mem_Ico.mp hi).2
  rw [← Finset.sum_subset hsub]
  · apply Finset.sum_congr rfl
    intro i hi
    have hi₁ := (by decide : 1 ≤ (3 : ℕ)).trans (Finset.mem_Ico.mp hi).1
    have hi₂ := Nat.le_of_lt_succ (Finset.mem_Ico.mp hi).2
    have hpow : v ^ (N + 1) = v ^ (i + 1) * v ^ (N - i) := by
      rw [← pow_add, Nat.add_right_comm, Nat.add_sub_of_le hi₂]
    rw [hpow, ← mul_assoc, mul_div_mul_right _ _ (pow_ne_zero _ hs)]
    change
      ((Q ^ 2).coeff (N - i) : ℂ) * (A / v ^ (max 1 i + 1)) =
        A * ((Q ^ 2).coeff (N - i) : ℂ) / v ^ (i + 1)
    rw [max_eq_right hi₁, ← mul_div_assoc, mul_comm A]
  · intro i hi hnot
    have hi₃ : i < 3 := lt_of_not_ge (fun h ↦ hnot (Finset.mem_Ico.mpr ⟨h, Finset.mem_range.mp hi⟩))
    have hdeg : (Q ^ 2).natDegree < N - i := by
      have hd := Polynomial.natDegree_pow_le (p := Q) (n := 2)
      exact Nat.lt_sub_iff_add_lt.mpr ((Nat.add_lt_add_of_le_of_lt hd hi₃).trans_le hQ)
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hdeg, Rat.cast_zero, zero_mul, mul_zero, zero_div]

/-- On the critical line, the absolute kernel is the rational norm-square
polynomial divided by a power of the squared pole distance. -/
public theorem middle_pole_kernel_norm (Q : Polynomial ℚ) {m : ℕ}
    (hQ : 2 * Q.natDegree + 3 ≤ 2 * m - 1) {a : ℚ} (ha : 1 / 2 < (a : ℝ)) (b t : ℝ) :
    ‖∑ i ∈ Finset.Ico 3 (2 * m),
          ((Q ^ 2).coeff (2 * m - 1 - i) : ℂ) *
            (LLS.PaperStatements.shiftedPoleKernel (max 1 i) a b (le_max_left _ _) ha).function
              (Complex.I * (t : ℂ))‖ =
      (normSqPolynomial a Q).eval₂ (Rat.castHom ℝ) ((a : ℝ) ^ 2 + t ^ 2) /
        ((a : ℝ) ^ 2 + t ^ 2) ^ m := by
  have hm : 0 < 2 * m :=
    (Nat.zero_lt_succ (2 * Q.natDegree + 2)).trans_le (hQ.trans (Nat.sub_le _ _))
  have hN : 2 * m - 1 + 1 = 2 * m := Nat.sub_add_cancel (Nat.succ_le_of_lt hm)
  have hre : (Complex.I * (t : ℂ) + (a : ℂ)).re = (a : ℝ) := by
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im,
      zero_mul, mul_zero, sub_zero, zero_add, Complex.ratCast_re]
  have hs : Complex.I * (t : ℂ) + (a : ℂ) ≠ 0 := by
    intro hz
    have h := congrArg Complex.re hz
    rw [hre, Complex.zero_re] at h
    linarith only [ha, h]
  have h :=
    middle_pole_kernel_factor Q hQ ha b (s := Complex.I * (t : ℂ))
      (by simpa only [Complex.ofReal_ratCast] using hs)
  rw [hN] at h
  rw [h, norm_div, norm_mul, norm_pow, Complex.norm_exp]
  have hphase : (((b : ℂ) * (Complex.I * (t : ℂ)))).re = 0 := by
    simp only [Complex.mul_re, Complex.I_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      mul_zero, sub_zero]
  have hdist : ‖Complex.I * (t : ℂ) + (a : ℂ)‖ ^ 2 = (a : ℝ) ^ 2 + t ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre]
    simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.ratCast_im, zero_mul, one_mul, zero_add, add_zero, pow_two]
  rw [hphase, Real.exp_zero, one_mul]
  simp only [norm_pow, Complex.ofReal_ratCast, ← norm_sq_polynomial_eval]
  rw [pow_mul, hdist]

/-- The common zero divisor and cutoff phase factor out of the component sum.
The phase has unit norm, so the remaining weight is the rational mass kernel. -/
public theorem middle_zero_term_norm (Q : Polynomial ℚ) {m : ℕ}
    (hQ : 2 * Q.natDegree + 3 ≤ 2 * m - 1) {a : ℚ} (ha : 1 / 2 < (a : ℝ)) (b : ℝ) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {X : ℝ} (hX : 0 < X) (ρ : ℂ) :
    let K := fun i : ℕ ↦ LLS.PaperStatements.shiftedPoleKernel (max 1 i) a b (le_max_left _ _) ha
    let D := MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ
    let u := (a : ℝ) ^ 2 + ρ.im ^ 2
    ‖∑ i ∈ Finset.Ico 3 (2 * m),
          ((Q ^ 2).coeff (2 * m - 1 - i) : ℂ) * (K i).oscillatingZeroTerm χ X ρ‖ =
      ‖(D : ℂ)‖ * ((normSqPolynomial a Q).eval₂ (Rat.castHom ℝ) u / u ^ m) := by
  intro K D u
  let c := fun i : ℕ ↦ ((Q ^ 2).coeff (2 * m - 1 - i) : ℂ)
  let v := Complex.I * ρ.im
  let phase := (X : ℂ) ^ v
  have hphase : ‖phase‖ = 1 := by
    rw [show phase = (X : ℂ) ^ (Complex.I * ρ.im) from rfl, Complex.norm_cpow_eq_rpow_re_of_pos hX]
    simp only [Complex.mul_re, Complex.I_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero,
      Real.rpow_zero]
  have hfactor :
    (∑ i ∈ Finset.Ico 3 (2 * m), c i * (K i).oscillatingZeroTerm χ X ρ) =
      (D : ℂ) * (∑ i ∈ Finset.Ico 3 (2 * m), c i * (K i).function v) * phase := by
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    simp only [LLS.PaperStatements.MellinKernel.oscillatingZeroTerm,
      LLS.PaperStatements.MellinKernel.kernelZeroTerm, D, v, phase]
    ac_rfl
  change ‖∑ i ∈ Finset.Ico 3 (2 * m), c i * (K i).oscillatingZeroTerm χ X ρ‖ = _
  rw [hfactor, norm_mul, norm_mul, hphase, mul_one]
  exact congrArg (‖(D : ℂ)‖ * ·) (middle_pole_kernel_norm Q hQ ha b ρ.im)

/-- The signed contribution of a primitive character is bounded above by the
absolute mass with the exact zero multiplicities. The comparison uses the
norm of the combined kernel at each zero, before summing over zeros. -/
public theorem middle_signed_zero_le_mass (Q : Polynomial ℚ) {m : ℕ}
    (hQ : 2 * Q.natDegree + 3 ≤ 2 * m - 1) {a : ℚ} (ha : 1 / 2 < (a : ℝ)) (b : ℝ) {q : ℕ} [NeZero q]
    (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {X κ : ℝ} (hX : 0 < X) (hκ : 0 ≤ κ) :
    let K := fun i : ℕ ↦ LLS.PaperStatements.shiftedPoleKernel (max 1 i) a b (le_max_left _ _) ha
    let D := MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ
    let u := fun ρ : ℂ ↦ (a : ℝ) ^ 2 + ρ.im ^ 2
    (-((κ : ℂ) *
            (∑' ρ : ℂ,
              ∑ i ∈ Finset.Ico 3 (2 * m),
                ((Q ^ 2).coeff (2 * m - 1 - i) : ℂ) * (K i).oscillatingZeroTerm χ X ρ)).re) ≤
      κ *
        (∑' ρ : ℂ,
          (D ρ : ℝ) * ((normSqPolynomial a Q).eval₂ (Rat.castHom ℝ) (u ρ) / (u ρ) ^ m)) := by
  intro K D u
  let F := fun ρ : ℂ ↦
    ∑ i ∈ Finset.Ico 3 (2 * m),
      ((Q ^ 2).coeff (2 * m - 1 - i) : ℂ) * (K i).oscillatingZeroTerm χ X ρ
  have hF : Summable F :=
    summable_sum fun i _ ↦ ((K i).summable_oscillatingZeroTerm hq hGRH hp hne hinv hX).mul_left _
  have hA : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) Set.univ := fun z _ ↦
    (DirichletCharacter.differentiable_completedLFunction hne).analyticAt z
  have hnorm (ρ : ℂ) :
    ‖F ρ‖ = (D ρ : ℝ) * ((normSqPolynomial a Q).eval₂ (Rat.castHom ℝ) (u ρ) / (u ρ) ^ m) := by
    have h := middle_zero_term_norm Q hQ ha b χ hX ρ
    change ‖F ρ‖ = ‖(D ρ : ℂ)‖ * _ at h
    have hn : (0 : ℝ) ≤ D ρ := by exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hA ρ
    simpa only [Complex.norm_intCast, abs_of_nonneg hn] using h
  change -((κ : ℂ) * (∑' ρ, F ρ)).re ≤ _
  have h := (neg_le_abs (((κ : ℂ) * (∑' ρ, F ρ)).re)).trans (Complex.abs_re_le_norm _)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hκ] at h
  exact
    h.trans
      (mul_le_mul_of_nonneg_left ((norm_tsum_le_tsum_norm hF.norm).trans_eq (tsum_congr hnorm)) hκ)

end PseudoPrime.PrimeTestBounds.MillerRabin
