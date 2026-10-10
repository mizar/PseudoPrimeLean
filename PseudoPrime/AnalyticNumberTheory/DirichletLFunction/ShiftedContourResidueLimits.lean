/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.ShiftedContourResidues
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.ShiftedContourAssembly

/-!
# Good-height limits of finite shifted residue sums

Individual character RH supplies horizontal nonvanishing and derivative envelopes on any
fixed strip. Together with vertical nonvanishing, these put each shifted ledger inside its
rectangle and identify its finite residue sum with the normalized boundary integral.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- For a non-principal character away from the real axis, completed nonvanishing implies
ordinary L-function nonvanishing. Divide by the nonzero gamma factor in the continuation
identity; this transfers good-height certificates to the shifted contour boundary. -/
theorem LFunction_ne_zero_of_completed_ne_zero_of_im_ne_zero {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hne : χ ≠ 1) {s : ℂ} (hF : χ.completedLFunction s ≠ 0)
    (him : s.im ≠ 0) : χ.LFunction s ≠ 0 := by
  rw [dirichletLFunction_eq_completed_div_gammaFactor χ s
      (Or.inr (dirichletCharacter_level_ne_one_of_ne_one hne))]
  exact div_ne_zero hF (gammaFactor_ne_zero_of_im_ne_zero him)

/-- At scale n>=1, scaled good-height data give ordinary L-function nonvanishing at both
signed heights across the growing strip. The positive height excludes gamma poles, so the
completed nonvanishing fields transfer through the continuation identity. -/
theorem PrimitiveScaledHorizontalStripData.LFunction_nonzero {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hne : χ ≠ 1) {n : ℝ} (hn : 1 ≤ n)
    (d : PrimitiveScaledHorizontalStripData χ n) {v : ℝ} (hv : |v| ≤ 2 * n) :
    χ.LFunction ((v : ℂ) + d.T * Complex.I) ≠ 0 ∧ χ.LFunction ((v : ℂ) - d.T * Complex.I) ≠ 0 := by
  have hT : 0 < d.T := zero_lt_one.trans_le (hn.trans d.T_mem.1)
  have hp := (d.nonzero v hv).1
  have hm := (d.nonzero v hv).2
  constructor
  · apply LFunction_ne_zero_of_completed_ne_zero_of_im_ne_zero hne hp
    simpa only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      Complex.I_re, mul_one, mul_zero, add_zero, zero_add] using hT.ne'
  · apply LFunction_ne_zero_of_completed_ne_zero_of_im_ne_zero hne hm
    simpa only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      Complex.I_re, mul_one, mul_zero, add_zero, zero_sub] using neg_ne_zero.mpr hT.ne'

/-- Individual RH for a primitive non-principal character with non-principal inverse gives
heights tending to infinity, a vanishing ordinary derivative envelope, and nonvanishing on
both horizontal edges of any fixed strip. Shift the scaled family and retain its nonzero
fields together with the gamma-corrected envelope for finite residue assembly. -/
theorem exists_fixedStrip_LLogDeriv_envelope_nonzero_of_dirichletRH {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (A : ℕ) :
    ∃ T η : ℕ → ℝ,
      Filter.Tendsto T Filter.atTop Filter.atTop ∧
        (∀ k, 1 ≤ T k) ∧
        Filter.Tendsto η Filter.atTop (nhds 0) ∧
        ∀ k v,
          -(A : ℝ) - 1 / 2 ≤ v →
            v ≤ (A : ℝ) + 3 / 2 →
            ‖logDeriv χ.LFunction ((v : ℂ) + T k * Complex.I)‖ / (T k) ^ 2 ≤ η k ∧
              ‖logDeriv χ.LFunction ((v : ℂ) - T k * Complex.I)‖ / (T k) ^ 2 ≤ η k ∧
              χ.LFunction ((v : ℂ) + T k * Complex.I) ≠ 0 ∧
              χ.LFunction ((v : ℂ) - T k * Complex.I) ≠ 0 := by
  let data := primitiveScaledHorizontalStripDataSeq_of_dirichletRH hN2 hRH hp hne hinv
  obtain ⟨η, hη, hbound⟩ :=
    exists_envelope_scaledHorizontalStrip_LLogDeriv_small hN2 data A hp hne hinv
  have hT : Filter.Tendsto (fun k => (data k).T) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono (fun k => (data k).T_mem.1)
      (Filter.tendsto_atTop_add_const_right Filter.atTop 1 tendsto_natCast_atTop_atTop)
  refine ⟨fun k => (data (k + A + 1)).T, fun k => η (k + A + 1), ?_, ?_, ?_, ?_⟩
  · exact hT.comp ((Filter.tendsto_add_atTop_nat 1).comp (Filter.tendsto_add_atTop_nat A))
  · intro k
    have hn := (data (k + A + 1)).T_mem.1
    have hnonneg : (0 : ℝ) ≤ ((k + A + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    exact le_trans (by linarith only [hnonneg]) hn
  · exact hη.comp ((Filter.tendsto_add_atTop_nat 1).comp (Filter.tendsto_add_atTop_nat A))
  · intro k v hlo hhi
    have hv : |v| ≤ 2 * (((k + A + 1 : ℕ) : ℝ) + 1) := by
      rw [abs_le]
      have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      simp only [Nat.cast_add, Nat.cast_one]
      constructor <;> linarith only [hk, hlo, hhi, (Nat.cast_nonneg A : (0 : ℝ) ≤ (A : ℝ))]
    have hn : (1 : ℝ) ≤ ((k + A + 1 : ℕ) : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg _)
    have hb := hbound (k + A + 1) v hv hlo hhi
    have hz := (data (k + A + 1)).LFunction_nonzero hne hn hv
    exact ⟨hb.1, hb.2, hz⟩

/-- An ordered rectangle containing the origin in its interior has an interior shifted
ledger when L is nonzero on its boundary. Origin entries use the interior premise; zero
entries cannot lie on any edge. This prepares the finite shifted contour identity. -/
theorem shiftedLogSingularities_mem_open_of_boundary_nonzero {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hne : χ ≠ 1) {σ : ℝ} {z w : ℂ} (hre : z.re < w.re)
    (him : z.im < w.im) (h0 : (0 : ℂ) ∈ RectangleGeometry.rectangleOpenBox z w)
    (hboundary :
      ∀ s ∈ Rectangle.rectangleClosedBox z w,
        s.re = z.re ∨ s.re = w.re ∨ s.im = z.im ∨ s.im = w.im → χ.LFunction ((σ : ℂ) + s) ≠ 0) :
    ∀ s ∈ shiftedLogSingularitiesInRectangle χ hne σ z w,
      s ∈ RectangleGeometry.rectangleOpenBox z w := by
  intro s hs
  obtain ⟨hrect, hs0 | hz⟩ := mem_shiftedLogSingularitiesInRectangle.mp hs
  · exact hs0 ▸ h0
  · have hzl : s.re ≠ z.re := fun h => hboundary s hrect (Or.inl h) hz
    have hzr : s.re ≠ w.re := fun h => hboundary s hrect (Or.inr (Or.inl h)) hz
    have hzb : s.im ≠ z.im := fun h => hboundary s hrect (Or.inr (Or.inr (Or.inl h))) hz
    have hzt : s.im ≠ w.im := fun h => hboundary s hrect (Or.inr (Or.inr (Or.inr h))) hz
    exact
      RectangleGeometry.mem_rectangleOpenBox_of_mem_closedBox_of_ne hre him hrect hzl hzr hzb hzt

/-- For a primitive non-principal character and inverse, sigma>=1, tau>0, positive height
and A>=2, horizontal nonvanishing puts the shifted ledger strictly inside the rectangle.
The functional equation excludes left-edge zeros, Euler nonvanishing excludes right-edge
zeros, and the positive height puts the origin inside. No additional RH is needed here. -/
theorem shiftedRectangle_ledger_mem_open {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {σ τ T : ℝ} (hσ : 1 ≤ σ) (hτ : 0 < τ)
    (hT : 0 < T) (A : ℕ) (hA : 2 ≤ A)
    (hhor :
      ∀ v,
        -(A : ℝ) - 1 / 2 ≤ v →
          v ≤ σ + τ →
          χ.LFunction ((v : ℂ) + T * Complex.I) ≠ 0 ∧ χ.LFunction ((v : ℂ) - T * Complex.I) ≠ 0) :
    ∀
      s ∈
        shiftedLogSingularitiesInRectangle χ hne σ
          (((-(A : ℝ) - 1 / 2 - σ : ℝ) : ℂ) - T * Complex.I) ((τ : ℂ) + T * Complex.I),
      s ∈
        RectangleGeometry.rectangleOpenBox (((-(A : ℝ) - 1 / 2 - σ : ℝ) : ℂ) - T * Complex.I)
          ((τ : ℂ) + T * Complex.I) := by
  let a : ℝ := -(A : ℝ) - 1 / 2 - σ
  let z : ℂ := (a : ℂ) - T * Complex.I
  let w : ℂ := (τ : ℂ) + T * Complex.I
  have hzre : z.re = a := by
    simp only [z, Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_im, mul_zero, zero_mul, sub_zero]
  have hzim : z.im = -T := by
    simp only [z, Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_sub]
  have hwre : w.re = τ := by
    simp only [w, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]
  have hwim : w.im = T := by
    simp only [w, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add]
  have ha : a < 0 := by
    dsimp only [a]
    linarith only [hσ, (Nat.cast_nonneg A : (0 : ℝ) ≤ (A : ℝ))]
  have hre : z.re < w.re := by
    rw [hzre, hwre]; exact ha.trans hτ
  have him : z.im < w.im := by
    rw [hzim, hwim]; linarith only [hT]
  have h0 : (0 : ℂ) ∈ RectangleGeometry.rectangleOpenBox z w := by
    simp only [RectangleGeometry.rectangleOpenBox, Complex.mem_reProdIm, Complex.zero_re,
      Complex.zero_im, hzre, hzim, hwre, hwim, min_eq_left (ha.trans hτ).le,
      max_eq_right (ha.trans hτ).le, min_eq_left (by linarith only [hT] : -T ≤ T),
      max_eq_right (by linarith only [hT] : -T ≤ T), Set.mem_Ioo]
    exact ⟨⟨ha, hτ⟩, ⟨neg_lt_zero.mpr hT, hT⟩⟩
  apply shiftedLogSingularities_mem_open_of_boundary_nonzero hne hre him h0
  intro s hs hside
  have hrepr : (σ : ℂ) + s = ((σ + s.re : ℝ) : ℂ) + s.im * Complex.I := by
    rw [Complex.ofReal_add, add_assoc, Complex.re_add_im]
  have hvrange : -(A : ℝ) - 1 / 2 ≤ σ + s.re ∧ σ + s.re ≤ σ + τ := by
    have hx := hs.1
    rw [hzre, hwre, Set.uIcc_of_le (ha.trans hτ).le] at hx
    dsimp only [a] at hx
    constructor <;> linarith only [hx.1, hx.2]
  rcases hside with hl | hr | hb | ht
  · have hev : σ + s.re = -(A : ℝ) - 1 / 2 := by
      rw [hl, hzre]; dsimp only [a]; ring
    rw [hrepr, hev]
    exact dirichletLFunction_ne_zero_leftVertical hp hne hinv A hA s.im
  · apply χ.LFunction_ne_zero_of_one_le_re (Or.inl hne)
    rw [Complex.add_re, Complex.ofReal_re, hr, hwre]
    linarith only [hσ, hτ]
  · rw [hrepr, hb, hzim, Complex.ofReal_neg, neg_mul, ← sub_eq_add_neg]
    exact (hhor (σ + s.re) hvrange.1 hvrange.2).2
  · rw [hrepr, ht, hwim]
    exact (hhor (σ + s.re) hvrange.1 hvrange.2).1

/-- Under individual character RH, with primitive non-principal character and inverse,
x>=1, sigma>=1, tau>0 and A>=2, choose positive heights tending to infinity so the finite
shifted residue sums converge to the arithmetic sum minus the left integral. Retain the
good-height nonvanishing, assemble each finite contour, and apply the proved edge limits.
This removes the finite-contour identity as an external premise of the logarithmic formula. -/
theorem exists_tendsto_shiftedLogResidueSum_of_dirichletRH {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x σ τ : ℝ} (hx : 1 ≤ x) (hσ : 1 ≤ σ) (hτ : 0 < τ) {A : ℕ}
    (hA : 2 ≤ A) :
    ∃ T : ℕ → ℝ,
      Filter.Tendsto T Filter.atTop Filter.atTop ∧
        (∀ k, 1 ≤ T k) ∧
        Filter.Tendsto
          (fun k =>
            ∑
              s ∈
                shiftedLogSingularitiesInRectangle χ hne σ
                  (((-(A : ℝ) - 1 / 2 - σ : ℝ) : ℂ) - T k * Complex.I) ((τ : ℂ) + T k * Complex.I),
              shiftedLogResidueAt χ x σ s)
          Filter.atTop
          (nhds
            (General.logarithmicWeightedSum
                (General.shiftedLSeriesCoefficient
                  (fun n => χ (n : ZMod N) * (ArithmeticFunction.vonMangoldt n : ℂ)) σ)
                x -
              (2 * Real.pi : ℝ)⁻¹ •
                ∫ t : ℝ,
                  shiftedLogContourKernel χ x σ
                    (((-(A : ℝ) - 1 / 2 - σ : ℝ) : ℂ) + t * Complex.I))) := by
  obtain ⟨B, hB⟩ := exists_nat_gt (max (A : ℝ) (σ + τ))
  have hAB : (A : ℝ) ≤ (B : ℝ) := (le_max_left _ _).trans hB.le
  have hright : σ + τ ≤ (B : ℝ) := (le_max_right _ _).trans hB.le
  obtain ⟨T, η, hT, hT1, hη, hb⟩ :=
    exists_fixedStrip_LLogDeriv_envelope_nonzero_of_dirichletRH hN2 hRH hp hne hinv B
  have hbounds :
    ∀ k v,
      -(A : ℝ) - 1 / 2 ≤ v →
        v ≤ σ + τ →
        ‖logDeriv χ.LFunction ((v : ℂ) + T k * Complex.I)‖ / (T k) ^ 2 ≤ η k ∧
          ‖logDeriv χ.LFunction ((v : ℂ) - T k * Complex.I)‖ / (T k) ^ 2 ≤ η k ∧
          χ.LFunction ((v : ℂ) + T k * Complex.I) ≠ 0 ∧
          χ.LFunction ((v : ℂ) - T k * Complex.I) ≠ 0 := by
    intro k v hlo hhi
    exact hb k v (by linarith only [hlo, hAB]) (by linarith only [hhi, hright])
  have hboundary :=
    tendsto_normalized_shiftedLogBoundary_of_envelopes hp hne hinv hx hσ hτ hA T η η hT
      (fun k => ne_of_gt (zero_lt_one.trans_le (hT1 k))) hη hη
      (by
        intro k u hu
        have hlo : -(A : ℝ) - 1 / 2 ≤ σ + u := by linarith only [hu.1]
        have hhi : σ + u ≤ σ + τ := add_le_add le_rfl hu.2
        simpa only [Complex.ofReal_add, add_assoc] using (hbounds k (σ + u) hlo hhi).1)
      (by
        intro k u hu
        have hlo : -(A : ℝ) - 1 / 2 ≤ σ + u := by linarith only [hu.1]
        have hhi : σ + u ≤ σ + τ := add_le_add le_rfl hu.2
        simpa only [Complex.ofReal_add, add_sub_assoc] using (hbounds k (σ + u) hlo hhi).2.1)
  refine ⟨T, hT, hT1, Filter.Tendsto.congr' (Filter.Eventually.of_forall ?_) hboundary⟩
  intro k
  have hTk : 0 < T k := zero_lt_one.trans_le (hT1 k)
  have hopen :=
    shiftedRectangle_ledger_mem_open hp hne hinv hσ hτ hTk A hA
      (fun v hlo hhi => (hbounds k v hlo hhi).2.2)
  apply shiftedLogFiniteContourIdentity_normalized hne (zero_lt_one.trans_le hx) hσ _ _ hopen
  · simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]
    linarith only [hσ, hτ, (Nat.cast_nonneg A : (0 : ℝ) ≤ (A : ℝ))]
  · simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_sub, zero_add]
    linarith only [hTk]

/-- For x>1 and individual character RH, the shifted finite residue sums recover the
arithmetic logarithmic sum by first taking good heights to infinity, then moving the left
edge to minus infinity. Primitive non-principal character and inverse, sigma>=1 and tau>0
supply the contour hypotheses. Choose the good-height sequences for A+2 and remove the
remaining left integrals with their proved decay. No contour limit is an extra premise. -/
theorem exists_iteratedLimit_shiftedLogResidueSum_of_dirichletRH {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x σ τ : ℝ} (hx : 1 < x) (hσ : 1 ≤ σ) (hτ : 0 < τ) :
    ∃ (T : ℕ → ℕ → ℝ) (F : ℕ → ℂ),
      (∀ A, Filter.Tendsto (T A) Filter.atTop Filter.atTop ∧ (∀ k, 1 ≤ T A k)) ∧
        (∀ A,
          Filter.Tendsto
            (fun k =>
              ∑
                s ∈
                  shiftedLogSingularitiesInRectangle χ hne σ
                    (((-((A + 2 : ℕ) : ℝ) - 1 / 2 - σ : ℝ) : ℂ) - T A k * Complex.I)
                    ((τ : ℂ) + T A k * Complex.I),
                shiftedLogResidueAt χ x σ s)
            Filter.atTop (nhds (F A))) ∧
        Filter.Tendsto F Filter.atTop
          (nhds
            (General.logarithmicWeightedSum
              (General.shiftedLSeriesCoefficient
                (fun n => χ (n : ZMod N) * (ArithmeticFunction.vonMangoldt n : ℂ)) σ)
              x)) := by
  choose T hT hT1 hlimit using fun A : ℕ =>
    exists_tendsto_shiftedLogResidueSum_of_dirichletRH hN2 hRH hp hne hinv hx.le hσ hτ
      (Nat.le_add_left 2 A)
  let F : ℕ → ℂ := fun A =>
    General.logarithmicWeightedSum
        (General.shiftedLSeriesCoefficient
          (fun n => χ (n : ZMod N) * (ArithmeticFunction.vonMangoldt n : ℂ)) σ)
        x -
      (2 * Real.pi : ℝ)⁻¹ •
        ∫ t : ℝ,
          shiftedLogContourKernel χ x σ (((-((A + 2 : ℕ) : ℝ) - 1 / 2 - σ : ℝ) : ℂ) + t * Complex.I)
  refine ⟨T, F, fun A => ⟨hT A, hT1 A⟩, hlimit, ?_⟩
  have hl :=
    (tendsto_shiftedLogContourKernel_left_integral hp hne hinv hx (zero_le_one.trans hσ)).comp
      (Filter.tendsto_add_atTop_nat 2)
  have hc :
    Filter.Tendsto F Filter.atTop
      (nhds
        (General.logarithmicWeightedSum
            (General.shiftedLSeriesCoefficient
              (fun n => χ (n : ZMod N) * (ArithmeticFunction.vonMangoldt n : ℂ)) σ)
            x -
          (2 * Real.pi : ℝ)⁻¹ • (0 : ℂ))) :=
    tendsto_const_nhds.sub (hl.const_smul ((2 * Real.pi : ℝ)⁻¹))
  simpa only [smul_zero, sub_zero] using hc

/-- If a finite ledger contains the origin, its residue sum is the origin coefficient
minus the positive-signed shifted zero sum on the erased ledger. Separate the origin and
unfold the nonzero branch; this connects contour residues to zero-series estimates. -/
theorem shiftedLogResidueSum_eq_origin_sub_zeroSum {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (x σ : ℝ) (S : Finset ℂ) (h0 : (0 : ℂ) ∈ S) :
    ∑ s ∈ S, shiftedLogResidueAt χ x σ s =
      shiftedLogResidueAt χ x σ 0 -
        ∑ s ∈ S.erase 0,
          (dirichletLFunctionZeroMultiplicity χ ((σ : ℂ) + s) : ℂ) * (x : ℂ) ^ s / s ^ 2 := by
  classical
  rw [← Finset.sum_erase_add S (shiftedLogResidueAt χ x σ) h0]
  have hs :
    ∑ s ∈ S.erase 0, shiftedLogResidueAt χ x σ s =
      -∑ s ∈ S.erase 0,
          (dirichletLFunctionZeroMultiplicity χ ((σ : ℂ) + s) : ℂ) * (x : ℂ) ^ s / s ^ 2 := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro s hs
    simp only [shiftedLogResidueAt, ite_eq_right (Finset.ne_of_mem_erase hs), neg_mul, neg_div]
  rw [hs]
  exact neg_add_eq_sub _ _

/-- For sigma>=1, tau>0 and positive height, every shifted left rectangle contains the
Mellin origin. Coordinate bounds prove membership, independently of RH and primitivity;
this justifies removing the origin from its finite zero ledger. -/
theorem zero_mem_shiftedLogRectangleLedger {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hne : χ ≠ 1) {σ τ T : ℝ} (hσ : 1 ≤ σ) (hτ : 0 < τ) (hT : 0 < T) (A : ℕ) :
    (0 : ℂ) ∈
      shiftedLogSingularitiesInRectangle χ hne σ (((-(A : ℝ) - 1 / 2 - σ : ℝ) : ℂ) - T * Complex.I)
        ((τ : ℂ) + T * Complex.I) := by
  apply mem_shiftedLogSingularitiesInRectangle.mpr
  refine ⟨?_, Or.inl rfl⟩
  rw [Rectangle.rectangleClosedBox, Complex.mem_reProdIm]
  simp only [Complex.zero_re, Complex.zero_im, Complex.sub_re, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.I_re, Complex.ofReal_im, mul_zero, sub_zero, add_zero, Complex.sub_im,
    Complex.add_im, Complex.mul_im, Complex.I_im, mul_one, zero_sub, zero_add]
  constructor
  · apply Set.mem_uIcc_of_le
    · linarith only [hσ, (Nat.cast_nonneg A : (0 : ℝ) ≤ (A : ℝ))]
    · exact hτ.le
  · exact Set.mem_uIcc_of_le (neg_lt_zero.mpr hT).le hT.le

/-- Under individual RH and primitive non-principal character and inverse, x>1,
sigma>=1 and tau>0, the iterated finite shifted L-zero sums converge to the origin residue
minus the arithmetic sum. Remove the origin from each ledger and subtract the already
proved residue limits. This isolates the zero contribution before splitting completed
zeros from gamma-induced trivial zeros and integrating in sigma. -/
theorem exists_iteratedLimit_shiftedLZeroSum_of_dirichletRH {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x σ τ : ℝ} (hx : 1 < x) (hσ : 1 ≤ σ) (hτ : 0 < τ) :
    ∃ (T : ℕ → ℕ → ℝ) (G : ℕ → ℂ),
      (∀ A, Filter.Tendsto (T A) Filter.atTop Filter.atTop ∧ (∀ k, 1 ≤ T A k)) ∧
        (∀ A,
          Filter.Tendsto
            (fun k =>
              ∑
                s ∈
                  (shiftedLogSingularitiesInRectangle χ hne σ
                        (((-((A + 2 : ℕ) : ℝ) - 1 / 2 - σ : ℝ) : ℂ) - T A k * Complex.I)
                        ((τ : ℂ) + T A k * Complex.I)).erase
                    0,
                (dirichletLFunctionZeroMultiplicity χ ((σ : ℂ) + s) : ℂ) * (x : ℂ) ^ s / s ^ 2)
            Filter.atTop (nhds (G A))) ∧
        Filter.Tendsto G Filter.atTop
          (nhds
            (shiftedLogResidueAt χ x σ 0 -
              General.logarithmicWeightedSum
                (General.shiftedLSeriesCoefficient
                  (fun n => χ (n : ZMod N) * (ArithmeticFunction.vonMangoldt n : ℂ)) σ)
                x)) := by
  classical
  obtain ⟨T, F, hT, hlim, hF⟩ :=
    exists_iteratedLimit_shiftedLogResidueSum_of_dirichletRH hN2 hRH hp hne hinv hx hσ hτ
  let G : ℕ → ℂ := fun A => shiftedLogResidueAt χ x σ 0 - F A
  refine ⟨T, G, hT, ?_, tendsto_const_nhds.sub hF⟩
  intro A
  have hc :
    Filter.Tendsto
      (fun k =>
        shiftedLogResidueAt χ x σ 0 -
          ∑
            s ∈
              shiftedLogSingularitiesInRectangle χ hne σ
                (((-((A + 2 : ℕ) : ℝ) - 1 / 2 - σ : ℝ) : ℂ) - T A k * Complex.I)
                ((τ : ℂ) + T A k * Complex.I),
            shiftedLogResidueAt χ x σ s)
      Filter.atTop (nhds (G A)) :=
    tendsto_const_nhds.sub (hlim A)
  apply Filter.Tendsto.congr' (Filter.Eventually.of_forall ?_) hc
  intro k
  rw [shiftedLogResidueSum_eq_origin_sub_zeroSum χ x σ _
      (zero_mem_shiftedLogRectangleLedger hne hσ hτ (zero_lt_one.trans_le ((hT A).2 k)) (A + 2)),
    sub_sub_cancel]

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
