/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.FiniteSumExhaustion
public import PseudoPrime.LLS.MellinKernelContourLimits
public import PseudoPrime.LLS.MellinKernelZeros

/-!
# Infinite weighted residues for general Mellin kernels

The shifted finite ledger exhausts every contributing singularity along good heights.
Translation preserves zero multiplicities, matching its residues with the global zero series.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements.MellinKernel

open AnalyticNumberTheory.DirichletLFunction in
/-- For primitive nonprincipal GRH data, each shifted residue away from the kernel pole
is minus the corresponding oscillatory zero term. Translation identifies multiplicities;
GRH identifies the shifted coordinate with the imaginary ordinate. Terms with zero divisor
vanish on both sides. This matches finite contour weights with the global zero series. -/
theorem weightedResidue_eq_neg_oscillatingZeroTerm (K : MellinKernel) {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (x : ℝ) {s : ℂ} (hs : s ≠ -1 / 2) :
    weightedResidue K (fun z : ℂ => χ.completedLFunction (z + 1 / 2)) x s =
      -K.oscillatingZeroTerm χ x (s + 1 / 2) := by
  rw [weightedResidue, ite_eq_right hs]
  have hm :
    (analyticOrderNatAt (fun z : ℂ => χ.completedLFunction (z + 1 / 2)) s : ℂ) =
      (MeromorphicOn.divisor χ.completedLFunction Set.univ (s + 1 / 2) : ℂ) := by
    exact_mod_cast shifted_completed_orderNat_eq_divisor hp hne s
  rw [hm, oscillatingZeroTerm, kernelZeroTerm]
  by_cases hD : MeromorphicOn.divisor χ.completedLFunction Set.univ (s + 1 / 2) = 0
  · simp only [hD, Int.cast_zero, neg_zero, zero_mul]
  · have hz := dirichletCompletedLFunction_zero_of_divisor_univ_ne_zero hne hD
    have hr := completedLFunction_zero_re_eq_half hGRH hp hne hinv hz
    have he : s = Complex.I * (s + 1 / 2).im := by
      apply Complex.ext
      · simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re] at hr
        simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
          zero_mul, mul_zero, sub_zero]
        linarith only [hr]
      · simp only [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
          zero_mul, one_mul, add_zero, Complex.add_im, Complex.div_ofNat_im, Complex.one_im,
          zero_div, zero_add]
    rw [← he]
    ring

open AnalyticNumberTheory.DirichletLFunction in
/-- In a fixed rectangle with left edge below minus one half and right edge above one half,
every shifted completed zero and the kernel pole eventually belongs to the good-height
ledger. GRH fixes the real coordinates and heights tending to infinity cover each ordinate.
This supplies exhaustion without requiring the height sequence to be monotone. -/
theorem eventually_mem_completedKernelSingularities {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {a b : ℝ} (ha : a < -1 / 2) (hb : 1 / 2 < b)
    {s : ℂ} (hs : s = -1 / 2 ∨ χ.completedLFunction (s + 1 / 2) = 0) :
    ∀ᶠ n in Filter.atTop,
      s ∈
        completedKernelSingularities hp hne
          ((a : ℂ) - primitiveHorizontalHeightSeq hq hGRH hp hne hinv n * Complex.I)
          ((b : ℂ) + primitiveHorizontalHeightSeq hq hGRH hp hne hinv n * Complex.I) := by
  have hsr : s.re = -1 / 2 ∨ s.re = 0 := by
    rcases hs with he | hz
    · exact
        Or.inl
          (by
            rw [he]; norm_num only [Complex.neg_re, Complex.div_ofNat_re, Complex.one_re])
    · have hr := completedLFunction_zero_re_eq_half hGRH hp hne hinv hz
      simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re] at hr
      exact Or.inr (by linarith only [hr])
  have hT := tendsto_primitiveHorizontalHeightSeq_atTop hq hGRH hp hne hinv
  filter_upwards [hT.eventually_gt_atTop |s.im|] with n hn
  apply mem_completedKernelSingularities.mpr
  refine ⟨?_, hs⟩
  have ht : 0 ≤ primitiveHorizontalHeightSeq hq hGRH hp hne hinv n := (abs_nonneg s.im).trans hn.le
  change s.re ∈ Set.uIcc _ _ ∧ s.im ∈ Set.uIcc _ _
  simp only [Complex.sub_re, Complex.add_re, Complex.sub_im, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero,
    mul_one, add_zero, zero_add, sub_zero, zero_sub]
  rw [Set.uIcc_of_le (by linarith only [ha, hb]), Set.uIcc_of_le (neg_le_self ht)]
  constructor
  · rcases hsr with he | he <;> rw [he] <;> constructor <;> linarith only [ha, hb]
  · exact ⟨by linarith only [neg_abs_le s.im, hn], (le_abs_self s.im).trans hn.le⟩

open AnalyticNumberTheory.DirichletLFunction in
/-- For a primitive nonprincipal character, the zero term at the origin vanishes.
The completed function is nonzero there, hence its divisor is zero. This separates
the kernel pole from the completed-zero contribution. -/
theorem oscillatingZeroTerm_zero (K : MellinKernel) {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (x : ℝ) : K.oscillatingZeroTerm χ x 0 = 0 := by
  have hD : MeromorphicOn.divisor χ.completedLFunction Set.univ 0 = 0 := by
    by_contra hd
    exact
      dirichletCompletedLFunction_zero_ne_zero_of_primitive hp hne
        (dirichletCompletedLFunction_zero_of_divisor_univ_ne_zero hne hd)
  simp only [oscillatingZeroTerm, kernelZeroTerm, hD, Int.cast_zero, zero_mul]

open AnalyticNumberTheory.DirichletLFunction in
/-- Under primitive nonprincipal GRH data and positive scale, the whole-plane weighted
residue family sums to the kernel-pole residue minus the oscillatory zero series.
Translate the absolutely convergent zero family and add the single pole contribution.
This identifies the infinite residue sum used by contour limits. -/
theorem hasSum_completed_weightedResidue (K : MellinKernel) {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) :
    HasSum (weightedResidue K (fun z : ℂ => χ.completedLFunction (z + 1 / 2)) x)
      (weightedResidue K (fun z : ℂ => χ.completedLFunction (z + 1 / 2)) x (-1 / 2) -
        ∑' ρ : ℂ, K.oscillatingZeroTerm χ x ρ) := by
  classical
  have hzero := oscillatingZeroTerm_zero K hp hne x
  let R := weightedResidue K (fun z : ℂ => χ.completedLFunction (z + 1 / 2)) x
  have hZ :
    HasSum (fun s : ℂ => K.oscillatingZeroTerm χ x (s + 1 / 2))
      (∑' ρ : ℂ, K.oscillatingZeroTerm χ x ρ) := by
    exact
      ((Equiv.addRight (1 / 2 : ℂ)).hasSum_iff (f := K.oscillatingZeroTerm χ x)).mpr
        (summable_oscillatingZeroTerm K hq hGRH hp hne hinv hx).hasSum
  have h := (hasSum_ite_eq (-1 / 2 : ℂ) (R (-1 / 2))).sub hZ
  apply h.congr_fun
  intro s
  by_cases hs : s = -1 / 2
  · subst s
    simp only [neg_div, neg_add_cancel, hzero, sub_zero, ite_true]
    rfl
  · rw [ite_eq_right hs, zero_sub]
    exact weightedResidue_eq_neg_oscillatingZeroTerm K hGRH hp hne hinv x hs

open AnalyticNumberTheory.DirichletLFunction in
/-- For primitive nonprincipal GRH data, positive scale and fixed lines enclosing the
shifted zeros and kernel pole, the finite residue sums along good heights tend to the
pole residue minus the oscillatory zero tsum. Absolute convergence and eventual inclusion
of every contributing singularity prove the limit. This removes the finite ledger. -/
theorem tendsto_completed_weightedResidueSum (K : MellinKernel) {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) {a b : ℝ}
    (ha : a < -1 / 2) (hb : 1 / 2 < b) :
    let T := primitiveHorizontalHeightSeq hq hGRH hp hne hinv
    let R := weightedResidue K (fun z : ℂ => χ.completedLFunction (z + 1 / 2)) x
    Filter.Tendsto
      (fun n =>
        ∑
          s ∈
            completedKernelSingularities hp hne ((a : ℂ) - T n * Complex.I)
              ((b : ℂ) + T n * Complex.I),
          R s)
      Filter.atTop (nhds (R (-1 / 2) - ∑' ρ : ℂ, K.oscillatingZeroTerm χ x ρ)) := by
  let R := weightedResidue K (fun z : ℂ => χ.completedLFunction (z + 1 / 2)) x
  have hR := hasSum_completed_weightedResidue K hq hGRH hp hne hinv hx
  dsimp only
  rw [← hR.tsum_eq]
  apply Analysis.tendsto_sum_of_eventually_mem_support R hR.summable.norm
  intro s hs
  apply eventually_mem_completedKernelSingularities hq hGRH hp hne hinv ha hb
  by_cases hpole : s = -1 / 2
  · exact Or.inl hpole
  · right
    apply
      apply_eq_zero_of_analyticOrderNatAt_ne_zero (f := fun z : ℂ =>
        χ.completedLFunction (z + 1 / 2)) (z₀ := s)
    intro ho
    apply hs
    simp only [R, weightedResidue, ite_eq_right hpole, ho, Nat.cast_zero, neg_zero, zero_mul]

open AnalyticNumberTheory.DirichletLFunction in
/-- In the admissible kernel strip, let the left line lie between minus three halves and
minus one half and the right line between one half and three halves, and take scale at
least one. Under primitive nonprincipal GRH data, the vertical integral difference times
`i` equals `2πi` times the pole residue minus the oscillatory zero series. Uniqueness of
the contour and residue limits proves the equality, the completed Mellin formula. -/
theorem completed_contour_zero_identity (K : MellinKernel) {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {a b x : ℝ} (hab : a < b)
    (ha : -1 / 2 - K.delta < a) (hb : b ≤ 1 / 2 + K.delta) (ha' : -3 / 2 ≤ a) (hb' : b ≤ 3 / 2)
    (hx : 1 ≤ x) (haleft : a < -1 / 2) (hbright : 1 / 2 < b) :
    let F := fun s : ℂ => -logDeriv χ.completedLFunction (s + 1 / 2) * (K.function s * (x : ℂ) ^ s)
    Complex.I * ((∫ t : ℝ, F ((b : ℂ) + t * Complex.I)) - (∫ t : ℝ, F ((a : ℂ) + t * Complex.I))) =
      2 * Real.pi * Complex.I *
        (weightedResidue K (fun z : ℂ => χ.completedLFunction (z + 1 / 2)) x (-1 / 2) -
          ∑' ρ : ℂ, K.oscillatingZeroTerm χ x ρ) := by
  have h1 := tendsto_completed_residueSum K hq hGRH hp hne hinv hab ha hb ha' hb' hx haleft hbright
  have h2 :=
    (tendsto_completed_weightedResidueSum K hq hGRH hp hne hinv (zero_lt_one.trans_le hx) haleft
          hbright).const_mul
      (2 * Real.pi * Complex.I)
  apply tendsto_nhds_unique h1
  exact h2.congr (fun n => Finset.mul_sum _ _ _)

open AnalyticNumberTheory.DirichletLFunction in
/-- Under the completed contour identity hypotheses, the difference of the right and left
vertical integrals equals `2π` times the kernel-pole residue minus the oscillatory zero
series. Cancel the nonzero factor `i` in the contour identity. This is the normalization
used when separating the ordinary L-function, gamma factor and conductor terms. -/
theorem completed_vertical_difference_eq_residues (K : MellinKernel) {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {a b x : ℝ} (hab : a < b)
    (ha : -1 / 2 - K.delta < a) (hb : b ≤ 1 / 2 + K.delta) (ha' : -3 / 2 ≤ a) (hb' : b ≤ 3 / 2)
    (hx : 1 ≤ x) (haleft : a < -1 / 2) (hbright : 1 / 2 < b) :
    let F := fun s : ℂ => -logDeriv χ.completedLFunction (s + 1 / 2) * (K.function s * (x : ℂ) ^ s)
    (∫ t : ℝ, F ((b : ℂ) + t * Complex.I)) - (∫ t : ℝ, F ((a : ℂ) + t * Complex.I)) =
      (2 * Real.pi : ℂ) *
        (weightedResidue K (fun z : ℂ => χ.completedLFunction (z + 1 / 2)) x (-1 / 2) -
          ∑' ρ : ℂ, K.oscillatingZeroTerm χ x ρ) := by
  apply mul_left_cancel₀ Complex.I_ne_zero
  have h :=
    completed_contour_zero_identity K hq hGRH hp hne hinv hab ha hb ha' hb' hx haleft hbright
  dsimp only at h ⊢
  exact h.trans (by ring)

end PseudoPrime.LLS.PaperStatements.MellinKernel
