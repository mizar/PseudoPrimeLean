/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.BacklundGammaComplexIntegral

/-! # Unit-interval expansion of the Gamma remainder integral -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private theorem weight_ae (n : ℤ) :
    ∀ᵐ t ∂(MeasureTheory.volume),
      t ∈ Set.uIoc (n : ℝ) (n + 1) → backlundGammaWeight t = (t - n) * (1 - (t - n)) := by
  rw [Set.uIoc_of_le (le_add_of_nonneg_right (by norm_num only : (0 : ℝ) ≤ 1))]
  filter_upwards [(MeasureTheory.Ioo_ae_eq_Ioc (μ := MeasureTheory.volume) (a := (n : ℝ)) (b :=
        n + 1)).mem_iff] with
    t ht₁ ht₂
  have ht₄ := ht₁.mpr ht₂
  have ht₃ : t ∈ Set.Ico (n : ℝ) (n + 1) := ⟨ht₄.1.le, ht₄.2⟩
  unfold backlundGammaWeight
  rw [← Int.self_sub_floor, Int.floor_eq_on_Ico n t ht₃]

/-- On any integer interval, replace the periodic quadratic weight in the
complex kernel by its polynomial representative. The two integrands agree
almost everywhere, including when the right endpoint is an integer. -/
theorem gamma_complex_integral_cell (a y : ℝ) (n : ℤ) :
    (∫ t in (n : ℝ)..(n + 1 : ℝ), backlundGammaComplexKernel a y t) =
      ∫ t in (n : ℝ)..(n + 1 : ℝ),
        ((((t - n) * (1 - (t - n)) : ℝ) : ℂ) / 2) *
          ((((a + t : ℝ) : ℂ) + (y : ℂ) * Complex.I)⁻¹ ^ 2) := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards [weight_ae n] with t ht htmem
  unfold backlundGammaComplexKernel
  rw [ht htmem]

/-- For positive `a`, the integral of the complex Gamma kernel from zero to
an integer `N` is the sum of its unit-interval integrals. Integrability on
the half-line justifies concatenating the intervals. -/
theorem gamma_complex_integral_sum {a y : ℝ} (ha : 0 < a) (N : ℕ) :
    (∑ k ∈ Finset.range N, ∫ t in (k : ℝ)..((k : ℝ) + 1), backlundGammaComplexKernel a y t) =
      ∫ t in (0 : ℝ)..(N : ℝ), backlundGammaComplexKernel a y t := by
  have h (k : ℕ) :
    IntervalIntegrable (backlundGammaComplexKernel a y) MeasureTheory.volume (k : ℝ)
      ((k : ℝ) + 1) := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith only : (k : ℝ) ≤ k + 1)).2
    apply (backlundGammaComplexKernel_integrable (y := y) ha).mono_set
    intro x hx
    exact lt_of_le_of_lt (Nat.cast_nonneg k) hx.1
  have hs :=
    intervalIntegral.sum_integral_adjacent_intervals (a := fun k : ℕ ↦ (k : ℝ)) (f :=
      backlundGammaComplexKernel a y) (n := N)
      (fun k _ ↦ by simpa only [Nat.cast_add, Nat.cast_one] using h k)
  simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero] using hs

/-- For positive `a`, the partial sums of the unit-interval Gamma kernel
integrals converge to its improper integral. This connects cellwise
Euler–Maclaurin calculations with the Gamma remainder integral. -/
theorem gamma_complex_cell_sum_tendsto {a y : ℝ} (ha : 0 < a) :
    Filter.Tendsto
      (fun N : ℕ ↦
        ∑ k ∈ Finset.range N, ∫ t in (k : ℝ)..((k : ℝ) + 1), backlundGammaComplexKernel a y t)
      Filter.atTop (nhds (∫ t in Set.Ioi (0 : ℝ), backlundGammaComplexKernel a y t)) := by
  have h :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi 0
      (backlundGammaComplexKernel_integrable (y := y) ha) tendsto_natCast_atTop_atTop
  apply h.congr'
  exact Filter.Eventually.of_forall (fun N ↦ (gamma_complex_integral_sum ha N).symm)

/-- For positive `a`, the sums of the polynomial unit-interval integrals
converge to the complex Gamma kernel integral. The cellwise replacement and
the improper-integral limit make the finite-sum interface explicit. -/
theorem gamma_complex_polynomial_sum_tendsto {a y : ℝ} (ha : 0 < a) :
    Filter.Tendsto
      (fun N : ℕ ↦
        ∑ k ∈ Finset.range N,
          ∫ t in (k : ℝ)..((k : ℝ) + 1),
            ((((t - k) * (1 - (t - k)) : ℝ) : ℂ) / 2) *
              ((((a + t : ℝ) : ℂ) + (y : ℂ) * Complex.I)⁻¹ ^ 2))
      Filter.atTop (nhds (∫ t in Set.Ioi (0 : ℝ), backlundGammaComplexKernel a y t)) := by
  apply (gamma_complex_cell_sum_tendsto (y := y) ha).congr'
  apply Filter.Eventually.of_forall
  intro N
  apply Finset.sum_congr rfl
  intro k hk
  simpa only [Int.cast_natCast] using gamma_complex_integral_cell a y (k : ℤ)

/-- The cellwise Euler–Maclaurin limit needed for the Gamma phase: at each
required height, the imaginary parts of the polynomial kernel sums converge
to the Gamma logarithm remainder. This is a proposition, not a proof. -/
def BacklundGammaCellImaginaryLimit : Prop :=
  ∀ t : ℝ,
    2 * Real.pi * Real.exp 1 ≤ t →
      Filter.Tendsto
        (fun N : ℕ ↦
          (∑ k ∈ Finset.range N,
              ∫ u in (k : ℝ)..((k : ℝ) + 1),
                ((((u - k) * (1 - (u - k)) : ℝ) : ℂ) / 2) *
                  (((((1 / 4 : ℝ) + u : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * Complex.I)⁻¹ ^ 2)).im)
        Filter.atTop (nhds (backlundGammaRemainder t))

/-- The imaginary cell limit implies the Gamma remainder identity. Uniqueness
of limits and the proved complex-kernel integral formula eliminate any need
to determine a real Stirling constant. -/
theorem gamma_remainder_identity_of_cells (h : BacklundGammaCellImaginaryLimit) :
    BacklundGammaRemainderIdentity := by
  intro t ht
  have hc :=
    (Complex.imCLM.continuous.tendsto _).comp
      (gamma_complex_polynomial_sum_tendsto (a := 1 / 4) (y := t / 2) (by norm_num only))
  simp only [Complex.imCLM_apply] at hc
  have he := tendsto_nhds_unique hc (h t ht)
  rw [backlundGammaComplexKernel_integral_im (by norm_num only)] at he
  exact he.symm

/-- Under GRH, the Euler-normalized zero-count identity and the imaginary
cell limit imply the least-prime `3/11` witness bound for odd composites.
The real Stirling constant is unnecessary for this conditional conclusion. -/
theorem three_eleven_least_of_gamma_cells {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hV : EulerRiemannVonMangoldt)
    (hI : BacklundGammaCellImaginaryLimit) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ max 2 ((3 / 11 : ℝ) * Real.log n ^ 2) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  exact three_eleven_least_of_gamma_integral hn ho hc hGRH hV (gamma_remainder_identity_of_cells hI)

end PseudoPrime.PrimeTestBounds.MillerRabin
