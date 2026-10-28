/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.EulerDerivatives
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.LargeSieve
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.OccurrenceCounting
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.Counting
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.LocalZeroDetector
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.PrimePolynomialHybrid

/-! # Mean-square bounds for differentiated Euler-series blocks -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity

/--
Inputs: a symmetric interval radius, a nonnegative lower bound, a function, and its interval
integrability.
Claim: a pointwise norm lower bound on the interval gives the corresponding lower bound for its
squared norm integral.
Proof: square the pointwise inequality and compare the integrand with the constant lower bound.
Role: converts a physical detector window into an integrated energy lower bound.
-/
theorem interval_sq_lower (δ b : ℝ) (hδ : 0 ≤ δ) (hb : 0 ≤ b) (f : ℝ → ℂ)
    (hf : ∀ x ∈ Set.Icc (-δ) δ, b ≤ ‖f x‖)
    (hi : IntervalIntegrable (fun x => ‖f x‖ ^ 2) MeasureTheory.volume (-δ) δ) :
    (2 * δ) * b ^ 2 ≤ ∫ x in (-δ)..δ, ‖f x‖ ^ 2 ∂MeasureTheory.volume := by
  have hpoint : ∀ x ∈ Set.Icc (-δ) δ, b ^ 2 ≤ ‖f x‖ ^ 2 := by
    intro x hx
    exact pow_le_pow_left₀ hb (hf x hx) 2
  have hmono :=
    intervalIntegral.integral_mono_on (by linarith only [hδ]) (intervalIntegrable_const) hi hpoint
  rw [intervalIntegral.integral_const] at hmono
  simpa only [smul_eq_mul, sub_neg_eq_add, two_mul] using hmono

/--
Inputs: a finite index set, a complex-valued function, and a nonnegative threshold after scaling.
Claim: the number of indices whose scaled norm reaches the threshold, times its square, is at most
the scaled sum of squared norms.
Proof: square the threshold inequality on the filtered set, then enlarge that set using
nonnegativity of every squared norm.
Role: converts polynomial large-value counts into the primitive-family mean square.
-/
theorem card_filter_scaled_norm_sq {α : Type*} (s : Finset α) (f : α → ℂ) (A B : ℝ) (hB : 0 ≤ B) :
    ((s.filter fun x => B ≤ A * ‖f x‖).card : ℝ) * B ^ 2 ≤ A ^ 2 * ∑ x ∈ s, ‖f x‖ ^ 2 := by
  classical
  let t := s.filter fun x => B ≤ A * ‖f x‖
  have hinside : ∑ x ∈ t, B ^ 2 ≤ ∑ x ∈ t, A ^ 2 * ‖f x‖ ^ 2 := by
    apply Finset.sum_le_sum
    intro x hx
    have hnorm := (Finset.mem_filter.mp hx).2
    have hpow := pow_le_pow_left₀ hB hnorm 2
    simpa only [mul_pow] using hpow
  have houtside : ∑ x ∈ t, A ^ 2 * ‖f x‖ ^ 2 ≤ ∑ x ∈ s, A ^ 2 * ‖f x‖ ^ 2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro x hx hnot
    exact mul_nonneg (sq_nonneg A) (sq_nonneg ‖f x‖)
  calc
    _ = ∑ x ∈ t, B ^ 2 := by simp only [Finset.sum_const, t, nsmul_eq_mul]
    _ ≤ ∑ x ∈ t, A ^ 2 * ‖f x‖ ^ 2 := hinside
    _ ≤ ∑ x ∈ s, A ^ 2 * ‖f x‖ ^ 2 := houtside
    _ = A ^ 2 * ∑ x ∈ s, ‖f x‖ ^ 2 := by rw [Finset.mul_sum]

/--
Inputs: a conductor, finite prime support, derivative order, height, and a normalized polynomial
threshold.
Claim: the number of primitive characters reaching that threshold, times its square, is bounded by
the normalized primitive-character polynomial mean square.
Proof: apply the finite scaled-norm count bound and unfold the mean-square definition.
Role: turns the uniform zero-window detector into the mean-square quantity controlled by the hybrid
large sieve.
-/
theorem poly_count_sq_mean {q : ℕ} (hq : 1 < q) (s : Finset ℕ) (r : ℕ) (η t B : ℝ) (hB : 0 ≤ B) :
    (((primitiveDirichletCharacterSet q).filter fun χ =>
              B ≤
                (η ^ (r + 1) / (r.factorial : ℝ)) *
                  ‖primeLogPowerPolynomial s r (1 + η) (fun p => χ (p : ZMod q)) t‖).card :
          ℝ) *
        B ^ 2 ≤
      (η ^ (r + 1) / (r.factorial : ℝ)) ^ 2 *
        primitiveCharacterPolynomialMeanSquare q hq s
          (fun p =>
            (((Real.log p : ℝ) ^ (r + 1) : ℂ) *
                Complex.exp (-((Real.log p : ℝ) * (1 + η) : ℝ) : ℂ)) *
              Complex.exp ((-(t * Real.log p) : ℝ) * Complex.I)) := by
  let A : ℝ := η ^ (r + 1) / (r.factorial : ℝ)
  let P : DirichletCharacter ℂ q → ℂ := fun χ =>
    primeLogPowerPolynomial s r (1 + η) (fun p => χ (p : ZMod q)) t
  have hcount := card_filter_scaled_norm_sq (primitiveDirichletCharacterSet q) P A B hB
  change
    (((primitiveDirichletCharacterSet q).filter fun χ => B ≤ A * ‖P χ‖).card : ℝ) * B ^ 2 ≤
      A ^ 2 * ∑ χ ∈ primitiveDirichletCharacterSet q, ‖P χ‖ ^ 2 at hcount
  have hmean :
    (∑ χ ∈ primitiveDirichletCharacterSet q, ‖P χ‖ ^ 2) =
      primitiveCharacterPolynomialMeanSquare q hq s
        (fun p =>
          (((Real.log p : ℝ) ^ (r + 1) : ℂ) * Complex.exp (-((Real.log p : ℝ) * (1 + η) : ℝ) : ℂ)) *
            Complex.exp ((-(t * Real.log p) : ℝ) * Complex.I)) := by
    simp only [P, primeLogPowerPolynomial, primitiveCharacterPolynomialMeanSquare,
      Complex.normSq_eq_norm_sq]
  simpa only [A, hmean] using hcount

/--
Inputs: a finite prime support, an equally spaced height mesh, and the hypotheses of the normalized
prime-log hybrid bound.
Claim: the scaled count of primitive characters exceeding a fixed polynomial threshold on that mesh
is bounded by the explicit hybrid coefficient-energy estimate.
Proof: apply `poly_count_sq_mean` at every conductor and mesh point, sum the bounds, then apply the
normalized prime-log grid hybrid theorem.
Role: connects the zero-window large-value events to the hybrid mean-square estimate.
-/
theorem poly_grid_hybrid (R : ℕ) (hR : 2 ≤ R) (T : ℝ) (hT : 1 ≤ T) (hTupper : T ≤ 2 * R) (r : ℕ)
    (s : Finset ℕ) (hprime : ∀ p ∈ s, Nat.Prime p) (hlower : ∀ p ∈ s, R ^ 6 ≤ p) (X : ℕ)
    (hupper : ∀ p ∈ s, p ≤ X) (a h : ℝ) (n : ℕ) (hh : 0 < h) (ha : -T ≤ a)
    (hb : a + (n : ℝ) * h ≤ T) (η c₁ : ℝ) (K : ℕ) (hη : 0 < η) (hc₁ : 0 ≤ c₁) (hhη : h ≤ η / 8)
    (hX : 1 ≤ X) (hlogX : η * Real.log X ≤ c₁ * K) (N : ℕ) (hN : 1 ≤ N) (hηsmall : 2 * η ≤ 1)
    (hmoment : ((2 * r + 1 : ℕ) : ℝ) ≤ (1 + 2 * η) * Real.log N) (habove : ∀ p ∈ s, N < p) (B : ℝ)
    (hB : 0 ≤ B) :
    B ^ 2 * (h / 2) *
        (∑ q ∈ ((Finset.Ioc 1 (R ^ 2)).attach.filter fun q => q.val ≤ R),
          ∑ k ∈ Finset.range n,
            (((primitiveDirichletCharacterSet q.val).filter fun χ =>
                  B ≤
                    (η ^ (r + 1) / (r.factorial : ℝ)) *
                      ‖primeLogPowerPolynomial s r (1 + η) (fun p => χ (p : ZMod q.val))
                          (a + ((k : ℝ) + 1 / 2) * h)‖).card :
              ℝ)) ≤
      (4096 : ℝ) / Real.log R * (1 + (c₁ * K / 8) ^ 2 / 2) *
        (((r + 1 : ℝ) * (2 : ℝ) ^ (2 * r + 1)) *
          ((3 / 2 : ℝ) * (Real.log 4 + 4) * Real.exp (-(η * Real.log N)))) := by
  let qset := (Finset.Ioc 1 (R ^ 2)).attach.filter fun q => q.val ≤ R
  let A : ℝ := η ^ (r + 1) / (r.factorial : ℝ)
  let E :=
    ∑ q ∈ qset,
      ∑ k ∈ Finset.range n,
        primitiveCharacterPolynomialMeanSquare q.val
          (show 1 < q.val from (Finset.mem_Ioc.mp q.property).1) s
          (fun p =>
            (((Real.log p : ℝ) ^ (r + 1) : ℂ) *
                Complex.exp (-((Real.log p : ℝ) * (1 + η) : ℝ) : ℂ)) *
              Complex.exp ((-((a + ((k : ℝ) + 1 / 2) * h) * Real.log p : ℝ) : ℝ) * Complex.I))
  let C :=
    ∑ q ∈ qset,
      ∑ k ∈ Finset.range n,
        (((primitiveDirichletCharacterSet q.val).filter fun χ =>
              B ≤
                A *
                  ‖primeLogPowerPolynomial s r (1 + η) (fun p => χ (p : ZMod q.val))
                      (a + ((k : ℝ) + 1 / 2) * h)‖).card :
          ℝ)
  have hcount : B ^ 2 * C ≤ A ^ 2 * E := by
    calc
      B ^ 2 * C =
          ∑ q ∈ qset,
            ∑ k ∈ Finset.range n,
              B ^ 2 *
                (((primitiveDirichletCharacterSet q.val).filter fun χ =>
                      B ≤
                        A *
                          ‖primeLogPowerPolynomial s r (1 + η) (fun p => χ (p : ZMod q.val))
                              (a + ((k : ℝ) + 1 / 2) * h)‖).card :
                  ℝ) :=
        by simp only [C, Finset.mul_sum]
      _ ≤
          ∑ q ∈ qset,
            ∑ k ∈ Finset.range n,
              A ^ 2 *
                primitiveCharacterPolynomialMeanSquare q.val
                  (show 1 < q.val from (Finset.mem_Ioc.mp q.property).1) s
                  (fun p =>
                    (((Real.log p : ℝ) ^ (r + 1) : ℂ) *
                        Complex.exp (-((Real.log p : ℝ) * (1 + η) : ℝ) : ℂ)) *
                      Complex.exp
                        ((-((a + ((k : ℝ) + 1 / 2) * h) * Real.log p : ℝ) : ℝ) * Complex.I)) :=
        by
        apply Finset.sum_le_sum
        intro q hq
        apply Finset.sum_le_sum
        intro k hk
        have hpoint :=
          poly_count_sq_mean (show 1 < q.val from (Finset.mem_Ioc.mp q.property).1) s r η
            (a + ((k : ℝ) + 1 / 2) * h) B hB
        change
          ((primitiveDirichletCharacterSet q.val).filter fun χ =>
                  B ≤
                    A *
                      ‖primeLogPowerPolynomial s r (1 + η) (fun p => χ (p : ZMod q.val))
                          (a + ((k : ℝ) + 1 / 2) * h)‖).card *
              B ^ 2 ≤
            A ^ 2 *
              primitiveCharacterPolynomialMeanSquare q.val
                (show 1 < q.val from (Finset.mem_Ioc.mp q.property).1) s
                (fun p =>
                  (((Real.log p : ℝ) ^ (r + 1) : ℂ) *
                      Complex.exp (-((Real.log p : ℝ) * (1 + η) : ℝ) : ℂ)) *
                    Complex.exp
                      ((-((a + ((k : ℝ) + 1 / 2) * h) * Real.log p : ℝ) : ℝ) * Complex.I)) at hpoint
        simpa only [A, mul_comm] using hpoint
      _ = A ^ 2 * E := by simp only [E, Finset.mul_sum]
  have hgrid :=
    primitiveCharacterPrimeLogPower_grid_hybrid_normalized_detector_order_bound R hR T hT hTupper r
      s hprime hlower X hupper a h n hh ha hb η c₁ K hη hc₁ hhη hX hlogX N hN hηsmall hmoment habove
  calc
    B ^ 2 * (h / 2) * C = (h / 2) * (B ^ 2 * C) := by ring
    _ ≤ (h / 2) * (A ^ 2 * E) := mul_le_mul_of_nonneg_left hcount (by positivity)
    _ = A ^ 2 * (h / 2) * E := by ring
    _ ≤ _ := by simpa only [A, E, qset] using hgrid

/--
Inputs: a physical window, a positive normalization, and a uniform normalized signal lower bound
for a finite prime-log polynomial throughout that window.
Claim: the squared polynomial norm has an explicit lower bound on the corresponding height
integral.
Proof: translate the window to a symmetric interval, use polynomial continuity for integrability,
and apply `interval_sq_lower`.
Role: converts the zero-wise prime detector into the continuous energy input for the hybrid sieve.
-/
theorem poly_window_integral (δ B A : ℝ) (hδ : 0 ≤ δ) (hB : 0 ≤ B) (hA : 0 < A) (s : Finset ℕ)
    (r : ℕ) (σ t : ℝ) (χ : ℕ → ℂ)
    (hwindow : ∀ u, |u - t| ≤ δ → B ≤ A * ‖primeLogPowerPolynomial s r σ χ u‖) :
    (2 * δ) * (B / A) ^ 2 ≤ ∫ u in (t - δ)..(t + δ), ‖primeLogPowerPolynomial s r σ χ u‖ ^ 2 := by
  let P := primeLogPowerPolynomial s r σ χ
  have hcont : Continuous P := primePoly_cont s r σ χ
  have hI : IntervalIntegrable (fun x => ‖P (t + x)‖ ^ 2) MeasureTheory.volume (-δ) δ :=
    ((hcont.norm.pow 2).comp (continuous_const.add continuous_id)).intervalIntegrable _ _
  have hpoint : ∀ x ∈ Set.Icc (-δ) δ, B / A ≤ ‖P (t + x)‖ := by
    intro x hx
    have hxabs : |x| ≤ δ := abs_le.mpr ⟨by linarith only [hx.1], by linarith only [hx.2]⟩
    have hdist : |(t + x) - t| ≤ δ := by
      calc
        |(t + x) - t| = |x| := by
          congr 1; ring
        _ ≤ δ := hxabs
    apply (div_le_iff₀ hA).2
    simpa only [P, mul_comm] using hwindow (t + x) hdist
  have hlower := interval_sq_lower δ (B / A) hδ (div_nonneg hB hA.le) (fun x => P (t + x)) hpoint hI
  have hlower' : (2 * δ) * (B / A) ^ 2 ≤ ∫ x in (-δ)..δ, (fun u => ‖P u‖ ^ 2) (t + x) := by
    simpa only [P] using hlower
  have hcomm :
    ∫ x in (-δ)..δ, (fun u => ‖P u‖ ^ 2) (t + x) =
      ∫ x in (-δ)..δ, (fun u => ‖P u‖ ^ 2) (x + t) := by
    congr 1
    funext x
    rw [add_comm]
  calc
    (2 * δ) * (B / A) ^ 2 ≤ ∫ x in (-δ)..δ, (fun u => ‖P u‖ ^ 2) (t + x) := hlower'
    _ = ∫ x in (-δ)..δ, (fun u => ‖P u‖ ^ 2) (x + t) := hcomm
    _ = ∫ u in (-δ) + t..δ + t, ‖P u‖ ^ 2 :=
      intervalIntegral.integral_comp_add_right (f := fun u => ‖P u‖ ^ 2) t
    _ = ∫ u in (t - δ)..(t + δ), ‖P u‖ ^ 2 := by congr 1 <;> ring
    _ = ∫ u in (t - δ)..(t + δ), ‖primeLogPowerPolynomial s r σ χ u‖ ^ 2 := by rfl

/-- Given a nonnegative normalization and signal, an Euler-polynomial error at most
one eighth of the signal preserves at least half the signal in the polynomial norm.
Apply the triangle inequality and remove the unit sign factor.
This transfers all points of a family to a shared finite truncation. -/
theorem normalized_polynomial_signal_of_error (n : ℕ) (F P : ℂ) (A signal : ℝ) (hA : 0 ≤ A)
    (hsignal : 0 ≤ signal) (hdet : signal ≤ A * ‖F‖)
    (herr : A * ‖F + (-1 : ℂ) ^ n * P‖ ≤ signal / 8) : signal / 2 ≤ A * ‖P‖ := by
  have hsign : ‖(-1 : ℂ) ^ n * P‖ = ‖P‖ := by
    simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  have ht := norm_sub_le (F + (-1 : ℂ) ^ n * P) ((-1 : ℂ) ^ n * P)
  rw [add_sub_cancel_right, hsign] at ht
  have hscaled := mul_le_mul_of_nonneg_left ht hA
  rw [mul_add] at hscaled
  linarith only [hdet, herr, hscaled, hsignal]

/-- For a finite derivative-order range and positive rate at most one, one cutoff
above the prescribed minimum retains half of every normalized derivative signal
`exp(-D K)`, for every Dirichlet character and every height on `Re(s)=1+η`.
Use the uniform truncation-error certificate and the signal-transfer inequality.
The explicit logarithmic support bound feeds a common-support hybrid incidence estimate. -/
theorem exists_uniform_finite_Euler_signal_cutoff (η D K : ℝ) (nmax cutoffMin : ℕ) (hη : 0 < η)
    (hηsmall : η ≤ 1) (hD : 0 ≤ D) (hK : 0 ≤ K) (hmin : 1 ≤ cutoffMin) :
    ∃ N : ℕ,
      cutoffMin ≤ N ∧
        1 ≤ N ∧
        η * Real.log ((N : ℝ) + 1) ≤
          2 * ((nmax : ℝ) + D * K + Real.log (24 * (Real.log 4 + 4))) + η * Real.log cutoffMin +
            η * Real.log 3 ∧
        ∀ n ≤ nmax,
          ∀ {q : ℕ} [NeZero q],
            ∀ χ : DirichletCharacter ℂ q,
              ∀ {s : ℂ},
                s.re = 1 + η →
                  Real.exp (-(D * K)) ≤
                    η ^ (n + 1) / (n.factorial : ℝ) *
                      ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) s‖ →
                  Real.exp (-(D * K)) / 2 ≤
                    η ^ (n + 1) / (n.factorial : ℝ) *
                      ‖∑ k ∈ Finset.range (N + 1),
                          LSeries.term
                            (LSeries.logMul^[n]
                              (fun j : ℕ ↦ χ (j : ZMod q) * (ArithmeticFunction.vonMangoldt j : ℂ)))
                            s k‖ := by
  obtain ⟨N, hminN, hN, hlog, herr⟩ :=
    exists_uniform_quantitative_finite_series_cutoff η D K nmax cutoffMin hη hηsmall hD hK hmin
  refine ⟨N, hminN, hN, hlog, ?_⟩
  intro n hn q hq χ s hs hdet
  exact
    normalized_polynomial_signal_of_error n _ _ _ (Real.exp (-(D * K)))
      (div_nonneg (pow_nonneg hη.le (n + 1)) (Nat.cast_nonneg n.factorial)) (Real.exp_pos _).le hdet
      (herr n hn χ hs)

/-- For bounded detector parameters `K ≤ Kmax` and derivative orders `n ≤ nmax`,
choose one finite Euler cutoff that retains half of each point's own signal
`exp(-D K)`, for all characters and heights on the fixed abscissa.
The error budget uses `Kmax`; monotonicity of the exponential compares it with each
local signal. This preserves the local order parameter needed for prime-power removal. -/
theorem exists_uniform_finite_Euler_signal_cutoff_for_order_family (η D : ℝ)
    (Kmax nmax cutoffMin : ℕ) (hη : 0 < η) (hηsmall : η ≤ 1) (hD : 0 ≤ D) (hmin : 1 ≤ cutoffMin) :
    ∃ N : ℕ,
      cutoffMin ≤ N ∧
        1 ≤ N ∧
        η * Real.log ((N : ℝ) + 1) ≤
          2 * ((nmax : ℝ) + D * Kmax + Real.log (24 * (Real.log 4 + 4))) + η * Real.log cutoffMin +
            η * Real.log 3 ∧
        ∀ n ≤ nmax,
          ∀ K : ℕ,
            K ≤ Kmax →
              ∀ {q : ℕ} [NeZero q],
                ∀ χ : DirichletCharacter ℂ q,
                  ∀ {s : ℂ},
                    s.re = 1 + η →
                      Real.exp (-(D * K)) ≤
                        η ^ (n + 1) / (n.factorial : ℝ) *
                          ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) s‖ →
                      Real.exp (-(D * K)) / 2 ≤
                        η ^ (n + 1) / (n.factorial : ℝ) *
                          ‖∑ k ∈ Finset.range (N + 1),
                              LSeries.term
                                (LSeries.logMul^[n]
                                  (fun j : ℕ ↦
                                    χ (j : ZMod q) * (ArithmeticFunction.vonMangoldt j : ℂ)))
                                s k‖ := by
  obtain ⟨N, hminN, hN, hlog, herr⟩ :=
    exists_uniform_quantitative_finite_series_cutoff η D Kmax nmax cutoffMin hη hηsmall hD
      (Nat.cast_nonneg Kmax) hmin
  refine ⟨N, hminN, hN, hlog, ?_⟩
  intro n hn K hK q hq χ s hs hdet
  have hKreal : (K : ℝ) ≤ Kmax := by exact_mod_cast hK
  have hsignal : Real.exp (-(D * (Kmax : ℝ))) ≤ Real.exp (-(D * (K : ℝ))) :=
    Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left hKreal hD))
  have herror :=
    (herr n hn χ hs).trans (div_le_div_of_nonneg_right hsignal (by norm_num only : (0 : ℝ) ≤ 8))
  exact
    normalized_polynomial_signal_of_error n _ _ _ (Real.exp (-(D * (K : ℝ))))
      (div_nonneg (pow_nonneg hη.le (n + 1)) (Nat.cast_nonneg n.factorial)) (Real.exp_pos _).le hdet
      herror

/-- Under the shared requested-order budgets, choose one quantitative cutoff for
all bounded detector parameters, derivative orders, characters, and heights on the
fixed abscissa. Each normalized derivative signal yields a high-prime signal of
one eighth its size on the same support above `R^6`.
Apply the common Euler cutoff and the uniform prime-removal margins.
This supplies the common prime support needed for incidence aggregation. -/
theorem exists_uniform_high_prime_signal_cutoff_for_order_family (η D : ℝ)
    (Krequested Kmax nmax R : ℕ) (hη : 0 < η) (hηsmall : η ≤ 1) (hD : 0 ≤ D) (hR : 2 ≤ R)
    (hDrequested : D + 5 ≤ 5 * ((Krequested - 1 : ℕ) : ℝ)) (hRscale : η * Real.log (R : ℝ) ≤ 3)
    (hRorder : 18 ≤ Real.exp (-(D + 6)) * ((Krequested - 1 : ℕ) : ℝ))
    (hηratio : 4 * η ≤ Real.exp (-(D + 5)))
    (hm : Nat.ceil (Real.log higherPrimePowerEulerMajorantConstant) ≤ Krequested) :
    ∃ cutoff : ℕ,
      R ^ 6 ≤ cutoff ∧
        1 ≤ cutoff ∧
        η * Real.log ((cutoff : ℝ) + 1) ≤
          2 * ((nmax : ℝ) + D * Kmax + Real.log (24 * (Real.log 4 + 4))) +
            η * Real.log ((R ^ 6 : ℕ) : ℝ) +
            η * Real.log 3 ∧
        ∀ n ≤ nmax,
          ∀ K : ℕ,
            Krequested ≤ K →
              K ≤ Kmax →
              K ≤ n + 1 →
              ∀ {q : ℕ} [NeZero q],
                ∀ χ : DirichletCharacter ℂ q,
                  ∀ {s : ℂ},
                    s.re = 1 + η →
                      Real.exp (-(D * (K : ℝ))) ≤
                        η ^ (n + 1) / (n.factorial : ℝ) *
                          ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) s‖ →
                      Real.exp (-(D * (K : ℝ))) / 8 ≤
                        η ^ (n + 1) / (n.factorial : ℝ) *
                          ‖∑
                              p ∈
                                ((Finset.range (cutoff + 1)).filter Nat.Prime).filter
                                  (fun p ↦ ¬p ≤ R ^ 6),
                              LSeries.term
                                (LSeries.logMul^[n]
                                  (fun k : ℕ ↦
                                    χ (k : ZMod q) * (ArithmeticFunction.vonMangoldt k : ℂ)))
                                s p‖ := by
  have hmin : 1 ≤ R ^ 6 := Nat.one_le_pow 6 R ((by norm_num only : 1 ≤ 2).trans hR)
  obtain ⟨cutoff, hcutoff, hpos, hlog, hsignal⟩ :=
    exists_uniform_finite_Euler_signal_cutoff_for_order_family η D Kmax nmax (R ^ 6) hη hηsmall hD
      hmin
  refine ⟨cutoff, hcutoff, hpos, hlog, ?_⟩
  intro n hn K hKreq hKmax hKorder q hq χ s hs hdet
  exact
    finite_high_prime_signal_of_requested_order χ η D Krequested R n K cutoff hη hηsmall hD hR hKreq
      hKorder hcutoff hDrequested hRscale hRorder hηratio hm hs (hsignal n hn K hKmax χ hs hdet)

/-- Under the shared detector and scale budgets, obtain one high-prime support
whose normalized polynomial signal stays above `exp(-D Kmax)/16` on a physical
height window of radius `η exp(-D Kmax)/(16 C(nmax))`.
The radius is uniform in the character, zero height, and bounded local detector order.
Transfer to the common support, compare local signals with the weakest signal,
and apply the sharp normalized variation bound.
This supplies an incidence window proportional to `η` independently of the mesh spacing. -/
theorem exists_uniform_high_prime_signal_physical_window (η D : ℝ) (Krequested Kmax nmax R : ℕ)
    (hη : 0 < η) (hηsmall : η ≤ 1) (hD : 0 ≤ D) (hR : 2 ≤ R)
    (hDrequested : D + 5 ≤ 5 * ((Krequested - 1 : ℕ) : ℝ)) (hRscale : η * Real.log (R : ℝ) ≤ 3)
    (hRorder : 18 ≤ Real.exp (-(D + 6)) * ((Krequested - 1 : ℕ) : ℝ))
    (hηratio : 4 * η ≤ Real.exp (-(D + 5)))
    (hm : Nat.ceil (Real.log higherPrimePowerEulerMajorantConstant) ≤ Krequested)
    (hlarge : ((2 * nmax + 1 : ℕ) : ℝ) ≤ 6 * Real.log (R : ℝ)) :
    ∃ cutoff : ℕ,
      R ^ 6 ≤ cutoff ∧
        1 ≤ cutoff ∧
        η * Real.log ((cutoff : ℝ) + 1) ≤
          2 * ((nmax : ℝ) + D * Kmax + Real.log (24 * (Real.log 4 + 4))) +
            η * Real.log ((R ^ 6 : ℕ) : ℝ) +
            η * Real.log 3 ∧
        ∀ r ≤ nmax,
          ∀ K : ℕ,
            Krequested ≤ K →
              K ≤ Kmax →
              K ≤ r + 1 →
              ∀ {q : ℕ} [NeZero q],
                ∀ χ : DirichletCharacter ℂ q,
                  ∀ t : ℝ,
                    Real.exp (-(D * (K : ℝ))) ≤
                        (η ^ (r + 1) / (r.factorial : ℝ)) *
                          ‖iteratedDeriv r (logDeriv (DirichletCharacter.LFunction χ))
                              (((1 + η : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ →
                      ∀ u : ℝ,
                        |u - t| ≤
                            η * Real.exp (-(D * (Kmax : ℝ))) /
                              (16 * primeLogPowerVariationBound nmax) →
                          Real.exp (-(D * (Kmax : ℝ))) / 16 ≤
                            (η ^ (r + 1) / (r.factorial : ℝ)) *
                              ‖primeLogPowerPolynomial (highPrimeEulerSupport R cutoff) r (1 + η)
                                  (fun k ↦ χ (k : ZMod q)) u‖ := by
  obtain ⟨cutoff, hcutoff, hpos, hlog, hsignal⟩ :=
    exists_uniform_high_prime_signal_cutoff_for_order_family η D Krequested Kmax nmax R hη hηsmall
      hD hR hDrequested hRscale hRorder hηratio hm
  refine ⟨cutoff, hcutoff, hpos, hlog, ?_⟩
  intro r hr K hKreq hKmax hKorder q hq χ t hdet u hdist
  have hs : ((((1 + η : ℝ) : ℂ) + (t : ℂ) * Complex.I).re) = 1 + η := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      zero_mul, mul_zero, sub_zero, add_zero]
  have hhigh := hsignal r hr K hKreq hKmax hKorder χ hs hdet
  change
    Real.exp (-(D * (K : ℝ))) / 8 ≤
      (η ^ (r + 1) / (r.factorial : ℝ)) *
        ‖∑ p ∈ highPrimeEulerSupport R cutoff,
            LSeries.term
              (LSeries.logMul^[r]
                (fun k : ℕ ↦ χ (k : ZMod q) * (ArithmeticFunction.vonMangoldt k : ℂ)))
              (((1 + η : ℝ) : ℂ) + (t : ℂ) * Complex.I) p‖ at hhigh
  rw [finite_highPrimeEuler_sum_eq_primeLogPowerPolynomial] at hhigh
  have hKreal : (K : ℝ) ≤ Kmax := by exact_mod_cast hKmax
  have he := Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left hKreal hD))
  have hcenter := (div_le_div_of_nonneg_right he (by norm_num only : (0 : ℝ) ≤ 8)).trans hhigh
  have hRone : 1 ≤ R := (by norm_num only : 1 ≤ 2).trans hR
  have hmoment :=
    prime_energy_decreasing_range_of_order_envelope (η / 2) r nmax R
      (div_nonneg hη.le (by norm_num only)) hr hRone hlarge
  rw [show 2 * (η / 2) = η by ring] at hmoment
  have hrnext : r + 1 ≤ 2 * r + 1 := by
    rw [two_mul]
    exact Nat.add_le_add_right (Nat.le_add_right r r) 1
  have hrreal : ((r + 1 : ℕ) : ℝ) ≤ ((2 * r + 1 : ℕ) : ℝ) := by exact_mod_cast hrnext
  have hradius :
    η * (Real.exp (-(D * (Kmax : ℝ))) / 8) / (2 * primeLogPowerVariationBound nmax) =
      η * Real.exp (-(D * (Kmax : ℝ))) / (16 * primeLogPowerVariationBound nmax) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hwindow :=
    normalized_primeLogPowerPolynomial_window η (Real.exp (-(D * (Kmax : ℝ))) / 8) r nmax (R ^ 6)
      (highPrimeEulerSupport R cutoff) t u (fun k ↦ χ (k : ZMod q)) hη hηsmall
      (Nat.one_le_pow 6 R hRone) hr (hrreal.trans hmoment)
      (fun p hp ↦ (mem_highPrimeEulerSupport.mp hp).2.1)
      (fun p hp ↦ (mem_highPrimeEulerSupport.mp hp).2.2) (fun p hp ↦ χ.norm_le_one (p : ZMod q))
      hcenter (by rwa [hradius])
  simpa only [div_div, show (8 : ℝ) * 2 = 16 by norm_num only] using hwindow

/-- For any positive physical radius and prescribed minimum mesh density, choose
a finer rational grid and an integer window whose physical width is at most that
radius and whose incidence count divided by mesh density is at least the radius.
Use ceilings for the density and window size. This retains the gain when refining the mesh. -/
theorem exists_mesh_window_with_physical_radius (δ : ℝ) (Mmin : ℕ) (hδ : 0 < δ) :
    ∃ M K : ℕ, Mmin ≤ M ∧ 0 < M ∧ (K + 1 : ℝ) / M ≤ δ ∧ δ ≤ (2 * K + 1 : ℝ) / M := by
  let M := max Mmin (Nat.ceil (4 / δ))
  have hlower : 4 / δ ≤ (M : ℝ) :=
    (Nat.le_ceil (4 / δ)).trans (Nat.cast_le.mpr (le_max_right Mmin _))
  have hMreal : (0 : ℝ) < M := (div_pos (by norm_num only) hδ).trans_le hlower
  have hδM : 4 ≤ δ * (M : ℝ) := by
    have h := (div_le_iff₀ hδ).mp hlower
    simpa only [mul_comm] using h
  let K := Nat.ceil (δ * (M : ℝ) / 2)
  have hKlower : δ * (M : ℝ) / 2 ≤ (K : ℝ) := Nat.le_ceil _
  have hKupper : (K : ℝ) < δ * (M : ℝ) / 2 + 1 :=
    Nat.ceil_lt_add_one (div_nonneg (mul_nonneg hδ.le hMreal.le) (by norm_num only))
  refine ⟨M, K, le_max_left _ _, Nat.cast_pos.mp hMreal, ?_, ?_⟩
  · apply (div_le_iff₀ hMreal).mpr
    nlinarith only [hKupper, hδM]
  · apply (le_div_iff₀ hMreal).mpr
    nlinarith only [hKlower]

/-- A physical lower bound for normalized window incidence controls mesh density
divided by window gain by the inverse radius. Cross-multiply positive denominators.
This cancels the mesh density introduced by a sampled mean-square bound. -/
theorem mesh_density_div_window_gain_le_inverse_radius (δ : ℝ) (M K : ℕ) (hδ : 0 < δ) (hM : 0 < M)
    (hgain : δ ≤ (2 * K + 1 : ℝ) / M) : (M : ℝ) / (2 * K + 1 : ℝ) ≤ 1 / δ := by
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hM
  have hKreal : (0 : ℝ) < 2 * K + 1 :=
    add_pos_of_nonneg_of_pos (mul_nonneg (by norm_num only) (Nat.cast_nonneg K)) zero_lt_one
  have hmul := (le_div_iff₀ hMreal).mp hgain
  apply (div_le_div_iff₀ hKreal hδ).mpr
  nlinarith only [hmul]

/-- Under the common high-prime detector budgets, choose one cutoff, rational mesh,
and integer incidence window. Retain the normalized prime signal on every incident
grid point, while window gain divided by mesh density is bounded below by the explicit
physical radius proportional to `η`. The window also lies inside `η/8`.
Combine the physical-window detector with the ceiling-based mesh construction.
This supplies a mesh-density gain compatible with the normalized hybrid estimate. -/
theorem exists_uniform_high_prime_signal_mesh_window (η D : ℝ) (Krequested Kmax nmax R Mmin : ℕ)
    (hη : 0 < η) (hηsmall : η ≤ 1) (hD : 0 ≤ D) (hR : 2 ≤ R)
    (hDrequested : D + 5 ≤ 5 * ((Krequested - 1 : ℕ) : ℝ)) (hRscale : η * Real.log (R : ℝ) ≤ 3)
    (hRorder : 18 ≤ Real.exp (-(D + 6)) * ((Krequested - 1 : ℕ) : ℝ))
    (hηratio : 4 * η ≤ Real.exp (-(D + 5)))
    (hm : Nat.ceil (Real.log higherPrimePowerEulerMajorantConstant) ≤ Krequested)
    (hlarge : ((2 * nmax + 1 : ℕ) : ℝ) ≤ 6 * Real.log (R : ℝ)) :
    ∃ cutoff M W : ℕ,
      R ^ 6 ≤ cutoff ∧
        1 ≤ cutoff ∧
        Mmin ≤ M ∧
        0 < M ∧
        (W + 1 : ℝ) / M ≤ η / 8 ∧
        η * Real.exp (-(D * (Kmax : ℝ))) / (16 * primeLogPowerVariationBound nmax) ≤
          (2 * W + 1 : ℝ) / M ∧
        η * Real.log ((cutoff : ℝ) + 1) ≤
          2 * ((nmax : ℝ) + D * Kmax + Real.log (24 * (Real.log 4 + 4))) +
            η * Real.log ((R ^ 6 : ℕ) : ℝ) +
            η * Real.log 3 ∧
        ∀ r ≤ nmax,
          ∀ K : ℕ,
            Krequested ≤ K →
              K ≤ Kmax →
              K ≤ r + 1 →
              ∀ {q : ℕ} [NeZero q],
                ∀ χ : DirichletCharacter ℂ q,
                  ∀ t : ℝ,
                    Real.exp (-(D * (K : ℝ))) ≤
                        (η ^ (r + 1) / (r.factorial : ℝ)) *
                          ‖iteratedDeriv r (logDeriv (DirichletCharacter.LFunction χ))
                              (((1 + η : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ →
                      ∀ j : ℤ,
                        |t - (j : ℝ) / M| ≤ (W + 1 : ℝ) / M →
                          Real.exp (-(D * (Kmax : ℝ))) / 16 ≤
                            (η ^ (r + 1) / (r.factorial : ℝ)) *
                              ‖primeLogPowerPolynomial (highPrimeEulerSupport R cutoff) r (1 + η)
                                  (fun k ↦ χ (k : ZMod q)) ((j : ℝ) / M)‖ := by
  obtain ⟨cutoff, hcutoff, hpos, hlog, hsignal⟩ :=
    exists_uniform_high_prime_signal_physical_window η D Krequested Kmax nmax R hη hηsmall hD hR
      hDrequested hRscale hRorder hηratio hm hlarge
  let δ := η * Real.exp (-(D * (Kmax : ℝ))) / (16 * primeLogPowerVariationBound nmax)
  have hδ : 0 < δ := by
    rw [show δ = η * (Real.exp (-(D * (Kmax : ℝ))) / (16 * primeLogPowerVariationBound nmax)) by
        dsimp only [δ]; ring]
    exact mul_pos hη (uniform_high_prime_window_factor_pos D Kmax nmax)
  obtain ⟨M, W, hMmin, hM, hwidth, hgain⟩ := exists_mesh_window_with_physical_radius δ Mmin hδ
  have hδsmall : δ ≤ η / 8 := by
    have h := mul_le_mul_of_nonneg_left (uniform_high_prime_window_factor_le D Kmax nmax hD) hη.le
    simpa only [δ, ← mul_div_assoc, mul_one] using h
  refine ⟨cutoff, M, W, hcutoff, hpos, hMmin, hM, hwidth.trans hδsmall, hgain, hlog, ?_⟩
  intro r hr K hKreq hKmax hKorder q hq χ t hdet j hj
  apply hsignal r hr K hKreq hKmax hKorder χ t hdet ((j : ℝ) / M)
  have hd := hj.trans hwidth
  simpa only [abs_sub_comm] using hd

/-- At the boundary scale `η log R = 1`, the explicit physical-window incidence
gain cancels both mesh density and the hybrid logarithmic factor. The sampling loss
is at most `32 C(nmax) exp(D Kmax)`, independent of `R` and the mesh density.
Apply the inverse-radius bound and simplify using the boundary identity.
This checks that the normalized high-prime route leaves no additional height-grid factor. -/
theorem mesh_hybrid_sampling_loss_le_at_boundary_scale (η D : ℝ) (Kmax nmax R M W : ℕ) (hη : 0 < η)
    (hM : 0 < M) (hboundary : η * Real.log (R : ℝ) = 1)
    (hgain :
      η * Real.exp (-(D * (Kmax : ℝ))) / (16 * primeLogPowerVariationBound nmax) ≤
        (2 * W + 1 : ℝ) / M) :
    2 * (M : ℝ) / ((2 * W + 1 : ℝ) * Real.log R) ≤
      32 * primeLogPowerVariationBound nmax * Real.exp (D * (Kmax : ℝ)) := by
  have hlogeq : Real.log (R : ℝ) = 1 / η :=
    (eq_div_iff (ne_of_gt hη)).mpr (by simpa only [mul_comm] using hboundary)
  have hlog : 0 < Real.log (R : ℝ) := by
    rw [hlogeq]; exact div_pos zero_lt_one hη
  have hδ : 0 < η * Real.exp (-(D * (Kmax : ℝ))) / (16 * primeLogPowerVariationBound nmax) :=
    div_pos (mul_pos hη (Real.exp_pos _))
      (mul_pos (by norm_num only) (primeLogPowerVariationBound_pos _))
  have hdensity := mesh_density_div_window_gain_le_inverse_radius _ M W hδ hM hgain
  have hscaled :=
    mul_le_mul_of_nonneg_right hdensity (div_nonneg (by norm_num only : (0 : ℝ) ≤ 2) hlog.le)
  have hrhs :
    (1 / (η * Real.exp (-(D * (Kmax : ℝ))) / (16 * primeLogPowerVariationBound nmax))) *
        (2 / Real.log R) =
      32 * primeLogPowerVariationBound nmax * Real.exp (D * (Kmax : ℝ)) := by
    rw [one_div_div]
    calc
      _ =
          (32 * primeLogPowerVariationBound nmax) /
            ((η * Real.log (R : ℝ)) * Real.exp (-(D * (Kmax : ℝ)))) :=
        by
        rw [div_mul_div_comm]
        congr 1 <;> ring
      _ = _ := by rw [hboundary, one_mul, Real.exp_neg, div_inv_eq_mul]
  rw [hrhs] at hscaled
  calc
    _ = ((M : ℝ) / (2 * W + 1 : ℝ)) * (2 / Real.log R) := by
      rw [div_mul_div_comm]
      congr 1
      ring
    _ ≤ _ := hscaled

/-- For a character with a normalized derivative signal, a positive rate at most one,
and nonnegative detector exponent, retain half the signal in a finite Euler polynomial.
The cutoff exceeds any prescribed minimum and has an explicit scaled logarithmic upper
bound. Use the quantitative truncation error and the norm triangle inequality.
This carries the cutoff length required by the hybrid sampling estimate. -/
theorem exists_finite_Euler_polynomial_large_with_logarithmic_cutoff {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {η : ℝ} (hη : 0 < η) (hηsmall : η ≤ 1) (D : ℝ) (hD : 0 ≤ D)
    (K n cutoffMin : ℕ) (hmin : 1 ≤ cutoffMin) {s : ℂ} (hs : s.re = 1 + η)
    (hdet :
      Real.exp (-(D * (K : ℝ))) ≤
        (η ^ (n + 1) / (n.factorial : ℝ)) *
          ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) s‖) :
    ∃ N : ℕ,
      cutoffMin ≤ N ∧
        1 ≤ N ∧
        η * Real.log ((N : ℝ) + 1) ≤
          2 * ((n : ℝ) + D * K + Real.log (24 * (Real.log 4 + 4))) + η * Real.log cutoffMin +
            η * Real.log 3 ∧
        Real.exp (-(D * (K : ℝ))) / 2 ≤
          (η ^ (n + 1) / (n.factorial : ℝ)) *
            ‖∑ k ∈ Finset.range (N + 1),
                LSeries.term
                  (LSeries.logMul^[n]
                    (fun j : ℕ ↦ χ (j : ZMod q) * (ArithmeticFunction.vonMangoldt j : ℂ)))
                  s k‖ := by
  obtain ⟨N, hminN, hN, hlog, herr⟩ :=
    exists_quantitative_normalized_finite_series_error_le χ hη hηsmall D K hD (Nat.cast_nonneg K) n
      cutoffMin hmin hs
  let P : ℂ :=
    ∑ k ∈ Finset.range (N + 1),
      LSeries.term
        (LSeries.logMul^[n] (fun j : ℕ ↦ χ (j : ZMod q) * (ArithmeticFunction.vonMangoldt j : ℂ))) s
        k
  have hsign : ‖(-1 : ℂ) ^ n * P‖ = ‖P‖ := by
    rw [norm_mul]
    simp only [norm_pow, norm_neg, norm_one, one_pow, one_mul]
  have htriangle :
    ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) s‖ ≤
      ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) s + (-1 : ℂ) ^ n * P‖ + ‖P‖ := by
    have h :=
      norm_sub_le (iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) s + (-1 : ℂ) ^ n * P)
        ((-1 : ℂ) ^ n * P)
    rw [add_sub_cancel_right, hsign] at h
    exact h
  have hscaled :=
    mul_le_mul_of_nonneg_left htriangle
      (div_nonneg (pow_nonneg hη.le (n + 1)) (Nat.cast_nonneg n.factorial))
  rw [mul_add] at hscaled
  have hsignal := (Real.exp_pos (-(D * (K : ℝ)))).le
  refine ⟨N, hminN, hN, hlog, ?_⟩
  change Real.exp (-(D * (K : ℝ))) / 2 ≤ (η ^ (n + 1) / (n.factorial : ℝ)) * ‖P‖
  change
    (η ^ (n + 1) / (n.factorial : ℝ)) *
        ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) s + (-1 : ℂ) ^ n * P‖ ≤
      Real.exp (-(D * (K : ℝ))) / 8 at herr
  linarith only [hdet, hscaled, herr, hsignal]

/-- The ordinary near-one detector exponent is nonnegative, since each defining
logarithm has argument at least one. This supplies the exponent budget for the
quantitative finite Euler cutoff without an extra analytic hypothesis. -/
theorem ordinaryLFunctionNearOneDetectorExponent_nonneg :
    0 ≤ ordinaryLFunctionNearOneDetectorExponent := by
  have hcap :=
    (Nat.cast_nonneg completedLFunctionNearOneDetectorMultiplicityCap :
      (0 : ℝ) ≤ completedLFunctionNearOneDetectorMultiplicityCap)
  have hlog : 0 ≤ Real.log (8 * ((completedLFunctionNearOneDetectorMultiplicityCap : ℝ) + 1)) :=
    Real.log_nonneg (by linarith only [hcap])
  exact
    add_nonneg (add_nonneg (mul_nonneg hcap (Real.log_nonneg (by norm_num only))) hlog)
      (div_nonneg (Real.log_nonneg (by norm_num only)) (by norm_num only))

/-- For a primitive nonprincipal character with a completed zero near one and the
bounded conductor-height scale, obtain a finite Euler detector above any positive
minimum cutoff. Retain half the normalized signal, the multiplicity-controlled
detector order, and an explicit logarithmic support bound.
Apply the completed-to-ordinary detector and the quantitative truncation theorem.
This connects local zero detection to the support length used in the hybrid estimate. -/
theorem exists_finite_Euler_polynomial_large_at_near_one_zero_with_logarithmic_cutoff {q : ℕ}
    [NeZero q] {χ : DirichletCharacter ℂ q} (hq : 2 ≤ q) (hχ : χ ≠ 1) (hp : χ.IsPrimitive)
    (hinv : χ⁻¹ ≠ 1) {η : ℝ} (hη : 0 < η) (hηsmall : η ≤ 1 / 1288) (Krequested cutoffMin : ℕ)
    (hKrequested : 2 ≤ Krequested) (hmin : 1 ≤ cutoffMin) {c ρ : ℂ} (hcre : c.re = 1 + η)
    (hcim : c.im = ρ.im) (hρre : |ρ.re - 1| ≤ η)
    (hzero : DirichletCharacter.completedLFunction χ ρ = 0)
    (hc : DirichletCharacter.completedLFunction χ c ≠ 0)
    (hscale : η * Real.log ((q : ℝ) * (|ρ.im| + 3)) ≤ 3) :
    ∃ K n N : ℕ,
      Krequested ≤ K ∧
        2 ≤ K ∧
        0 < n ∧
        K ≤ n + 1 ∧
        n + 1 ≤ K * completedLFunctionNearOneDetectorMultiplicityCap ∧
        cutoffMin ≤ N ∧
        1 ≤ N ∧
        η * Real.log ((N : ℝ) + 1) ≤
          2 *
              ((n : ℝ) + ordinaryLFunctionNearOneDetectorExponent * K +
                Real.log (24 * (Real.log 4 + 4))) +
            η * Real.log cutoffMin +
            η * Real.log 3 ∧
        Real.exp (-(ordinaryLFunctionNearOneDetectorExponent * (K : ℝ))) / 2 ≤
          (η ^ (n + 1) / (n.factorial : ℝ)) *
            ‖∑ k ∈ Finset.range (N + 1),
                LSeries.term
                  (LSeries.logMul^[n]
                    (fun j : ℕ ↦ χ (j : ZMod q) * (ArithmeticFunction.vonMangoldt j : ℂ)))
                  c k‖ := by
  obtain ⟨_, _, _, _, _, _, K, m, n, hKrequested', _, _, _, hK, hn, hnm, hmK, hmCap, _, _, hdet⟩ :=
    exists_completedLFunction_positive_LFunction_logDeriv_iterate hq hχ hp hinv hη hηsmall
      Krequested hKrequested hcre hcim hρre hzero hc hscale
  obtain ⟨N, hminN, hN, hlog, hfinite⟩ :=
    exists_finite_Euler_polynomial_large_with_logarithmic_cutoff χ hη
      (hηsmall.trans (by norm_num only)) ordinaryLFunctionNearOneDetectorExponent
      ordinaryLFunctionNearOneDetectorExponent_nonneg K n cutoffMin hmin hcre hdet
  refine ⟨K, n, N, hKrequested', hK, hn, ?_, ?_, hminN, hN, hlog, hfinite⟩
  · rw [hnm]
    exact hmK
  · rw [hnm]
    exact hmCap

/--
Inputs: a primitive nonprincipal character, a completed-function zero near one, a requested
minimum detector order and Euler cutoff, and the bounded conductor-height scale.
Claim: a finite differentiated Euler polynomial retains at least half the normalized exponential
signal detected in the ordinary logarithmic derivative.
Proof: choose an Euler-series truncation above the requested cutoff whose error is less than half
the detected signal, then apply the norm triangle inequality.
Role: connects the local zero detector to finite Euler blocks with a prescribed lower support.
-/
theorem exists_finite_Euler_polynomial_large_at_near_one_zero_with_minimum_cutoff {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hq : 2 ≤ q) (hχ : χ ≠ 1) (hp : χ.IsPrimitive) (hinv : χ⁻¹ ≠ 1)
    {η : ℝ} (hη : 0 < η) (hηsmall : η ≤ 1 / 1288) (Krequested : ℕ) (hKrequested : 2 ≤ Krequested)
    (cutoffMin : ℕ) (hcutoffMin : 1 ≤ cutoffMin) {c ρ : ℂ} (hcre : c.re = 1 + η)
    (hcim : c.im = ρ.im) (hρre : |ρ.re - 1| ≤ η)
    (hzero : DirichletCharacter.completedLFunction χ ρ = 0)
    (hc : DirichletCharacter.completedLFunction χ c ≠ 0)
    (hscale : η * Real.log ((q : ℝ) * (|ρ.im| + 3)) ≤ 3) :
    ∃ massConstA massConstB : ℝ,
      0 < massConstA ∧
        0 < massConstB ∧
        ∃ Kmin C K m n cutoff : ℕ,
          Krequested ≤ K ∧
            K ≤ completedGenusRemoteTailUniformCutoff q η ρ.im ((C : ℝ) + 1) Kmin ∧
            K ≤ max completedGenusRemoteTailUniformOrderBound Kmin ∧
            Kmin ≤ K ∧
            C =
              Nat.ceil
                (completedZeroLocalLogBoundConstant *
                  (1 + 644 * η * Real.log ((q : ℝ) * (|ρ.im| + 3)))) ∧
            2 ≤ K ∧
            0 < n ∧
            n + 1 = m ∧
            K ≤ m ∧
            m ≤ K * completedLFunctionNearOneDetectorMultiplicityCap ∧
            cutoffMin ≤ cutoff ∧
            1 ≤ cutoff ∧
            (η / (2 * ((n + 1 : ℕ) : ℝ))) ^ (-((n + 1 : ℕ) : ℝ)) * (cutoff : ℝ) ^ (-η / 2) /
                (η / 2) <
              Real.exp (-(ordinaryLFunctionNearOneDetectorExponent * (K : ℝ))) /
                (2 * (η ^ (n + 1) / (n.factorial : ℝ))) ∧
            Real.exp (-(ordinaryLFunctionNearOneDetectorExponent * (K : ℝ))) / 2 ≤
              (η ^ (n + 1) / (n.factorial : ℝ)) *
                ‖∑ k ∈ Finset.range (cutoff + 1),
                    LSeries.term
                      (LSeries.logMul^[n]
                        (fun j : ℕ ↦ χ (j : ZMod q) * (ArithmeticFunction.vonMangoldt j : ℂ)))
                      c k‖ := by
  obtain
    ⟨massConstA, massConstB, hmassConstA, hmassConstB, Kmin, C, K, m, n, hKrequested', hKupper,
      hKupperFixed, hKmin, hK, hn, hnm, hmK, hmCap, hCeq, hpositive, hdet⟩ :=
    exists_completedLFunction_positive_LFunction_logDeriv_iterate hq hχ hp hinv hη hηsmall
      Krequested hKrequested hcre hcim hρre hzero hc hscale
  let A : ℝ := η ^ (n + 1) / (n.factorial : ℝ)
  let signal : ℝ := Real.exp (-(ordinaryLFunctionNearOneDetectorExponent * (K : ℝ)))
  let ε : ℝ := signal / (2 * A)
  have hA : 0 < A := by
    dsimp only [A]; positivity
  have hsignal : 0 < signal := by
    dsimp only [signal]; positivity
  have hε : 0 < ε := by
    dsimp only [ε]; positivity
  obtain ⟨cutoff, hcutoffGe, hExplicit⟩ :=
    exists_explicit_vonMangoldt_log_weight_cutoff_ge (show 1 < 1 + η by linarith only [hη]) n
      cutoffMin hε
  have hcutoff : 1 ≤ cutoff := le_trans hcutoffMin hcutoffGe
  have hExplicitEta :
    (η / (2 * ((n + 1 : ℕ) : ℝ))) ^ (-((n + 1 : ℕ) : ℝ)) * (cutoff : ℝ) ^ (-η / 2) / (η / 2) <
      ε := by
    simpa only [show (1 + η : ℝ) - 1 = η by ring] using hExplicit
  let M := cutoff + 1
  let P : ℂ :=
    ∑ k ∈ Finset.range M,
      LSeries.term
        (LSeries.logMul^[n] (fun j : ℕ ↦ χ (j : ZMod q) * (ArithmeticFunction.vonMangoldt j : ℂ))) c
        k
  have herrorBound :=
    iteratedDeriv_logDeriv_finite_series_error_le_explicit_of_re_ge χ
      (show 1 < 1 + η by linarith only [hη]) n cutoff hcutoff (show 1 + η ≤ c.re by rw [hcre])
  have herror :
    ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) c + (-1 : ℂ) ^ n * P‖ < ε := by
    have herrorBound' :
      ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) c + (-1 : ℂ) ^ n * P‖ ≤
        (η / (2 * ((n + 1 : ℕ) : ℝ))) ^ (-((n + 1 : ℕ) : ℝ)) * (cutoff : ℝ) ^ (-η / 2) /
          (η / 2) := by
      simpa only [M, show (1 + η : ℝ) - 1 = η by ring] using herrorBound
    exact lt_of_le_of_lt herrorBound' hExplicitEta
  have hsignNorm : ‖(-1 : ℂ) ^ n * P‖ = ‖P‖ := by
    rw [norm_mul]
    simp only [norm_pow, norm_neg, norm_one, one_pow, one_mul]
  have htriangle : ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) c‖ ≤ ε + ‖P‖ := by
    calc
      _ =
          ‖(iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) c + (-1 : ℂ) ^ n * P) -
              (-1 : ℂ) ^ n * P‖ :=
        by
        congr 1; ring
      _ ≤
          ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) c + (-1 : ℂ) ^ n * P‖ +
            ‖(-1 : ℂ) ^ n * P‖ :=
        norm_sub_le _ _
      _ ≤ ε + ‖P‖ := add_le_add (le_of_lt herror) (le_of_eq hsignNorm)
  have hAε : A * ε = signal / 2 := by
    dsimp only [ε]
    field_simp [ne_of_gt hA]
  have hscaledTriangle := mul_le_mul_of_nonneg_left htriangle hA.le
  have hsignalLe := hdet
  have hfinite : signal / 2 ≤ A * ‖P‖ := by
    rw [mul_add, hAε] at hscaledTriangle
    nlinarith only [hscaledTriangle, hsignalLe]
  exact
    ⟨massConstA, massConstB, hmassConstA, hmassConstB, Kmin, C, K, m, n, cutoff, hKrequested',
      hKupper, hKupperFixed, hKmin, hCeq, hK, hn, hnm, hmK, hmCap, hcutoffGe, hcutoff, by
      simpa only [signal, A] using hExplicitEta, by simpa only [P, A, M] using hfinite⟩

/--
Inputs: a primitive nonprincipal character, a completed-function zero near one, a requested
minimum detector order, and the bounded conductor-height scale.
Claim: some finite differentiated Euler polynomial retains at least half the normalized detector
signal, with a positive cutoff.
Proof: apply the minimum-cutoff theorem with cutoff lower bound one.
Role: preserves the general finite Euler detector interface without an additional support choice.
-/
theorem exists_finite_Euler_polynomial_large_at_near_one_zero {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hq : 2 ≤ q) (hχ : χ ≠ 1) (hp : χ.IsPrimitive) (hinv : χ⁻¹ ≠ 1)
    {η : ℝ} (hη : 0 < η) (hηsmall : η ≤ 1 / 1288) (Krequested : ℕ) (hKrequested : 2 ≤ Krequested)
    {c ρ : ℂ} (hcre : c.re = 1 + η) (hcim : c.im = ρ.im) (hρre : |ρ.re - 1| ≤ η)
    (hzero : DirichletCharacter.completedLFunction χ ρ = 0)
    (hc : DirichletCharacter.completedLFunction χ c ≠ 0)
    (hscale : η * Real.log ((q : ℝ) * (|ρ.im| + 3)) ≤ 3) :
    ∃ massConstA massConstB : ℝ,
      0 < massConstA ∧
        0 < massConstB ∧
        ∃ Kmin C K m n cutoff : ℕ,
          Krequested ≤ K ∧
            K ≤ completedGenusRemoteTailUniformCutoff q η ρ.im ((C : ℝ) + 1) Kmin ∧
            K ≤ max completedGenusRemoteTailUniformOrderBound Kmin ∧
            Kmin ≤ K ∧
            C =
              Nat.ceil
                (completedZeroLocalLogBoundConstant *
                  (1 + 644 * η * Real.log ((q : ℝ) * (|ρ.im| + 3)))) ∧
            2 ≤ K ∧
            0 < n ∧
            n + 1 = m ∧
            K ≤ m ∧
            m ≤ K * completedLFunctionNearOneDetectorMultiplicityCap ∧
            1 ≤ cutoff ∧
            (η / (2 * ((n + 1 : ℕ) : ℝ))) ^ (-((n + 1 : ℕ) : ℝ)) * (cutoff : ℝ) ^ (-η / 2) /
                (η / 2) <
              Real.exp (-(ordinaryLFunctionNearOneDetectorExponent * (K : ℝ))) /
                (2 * (η ^ (n + 1) / (n.factorial : ℝ))) ∧
            Real.exp (-(ordinaryLFunctionNearOneDetectorExponent * (K : ℝ))) / 2 ≤
              (η ^ (n + 1) / (n.factorial : ℝ)) *
                ‖∑ k ∈ Finset.range (cutoff + 1),
                    LSeries.term
                      (LSeries.logMul^[n]
                        (fun j : ℕ ↦ χ (j : ZMod q) * (ArithmeticFunction.vonMangoldt j : ℂ)))
                      c k‖ := by
  obtain
    ⟨massConstA, massConstB, hmassConstA, hmassConstB, Kmin, C, K, m, n, cutoff, hKrequested',
      hKupper, hKupperFixed, hKmin, hCeq, hK, hn, hnm, hmK, hmCap, hcutoffMin, hcutoff, hExplicit,
      hfinite⟩ :=
    exists_finite_Euler_polynomial_large_at_near_one_zero_with_minimum_cutoff hq hχ hp hinv hη
      hηsmall Krequested hKrequested 1 (by norm_num) hcre hcim hρre hzero hc hscale
  exact
    ⟨massConstA, massConstB, hmassConstA, hmassConstB, Kmin, C, K, m, n, cutoff, hKrequested',
      hKupper, hKupperFixed, hKmin, hCeq, hK, hn, hnm, hmK, hmCap, hcutoff, hExplicit, hfinite⟩

/-- For detector order at most `a K`, scale `η ≤ 1`, and `η log R ≤ 3`,
the quantitative cutoff length is at most an absolute coefficient times `K`.
Use the multiplicity cap and absorb the fixed logarithmic terms using `K ≥ 1`.
This supplies a uniform support constant for the hybrid mesh estimate. -/
theorem cutoff_log_le_uniform_detector_order (η D : ℝ) (K n R N a : ℕ) (hK : 1 ≤ K) (hn : n ≤ K * a)
    (hηsmall : η ≤ 1) (hRscale : η * Real.log (R : ℝ) ≤ 3)
    (hlog :
      η * Real.log ((N : ℝ) + 1) ≤
        2 * ((n : ℝ) + D * K + Real.log (24 * (Real.log 4 + 4))) + η * Real.log ((R ^ 6 : ℕ) : ℝ) +
          η * Real.log 3) :
    η * Real.log ((N : ℝ) + 1) ≤
      (2 * ((a : ℝ) + D + Real.log (24 * (Real.log 4 + 4))) + 18 + Real.log 3) * K := by
  have hKreal : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hnreal : (n : ℝ) ≤ (K : ℝ) * a := by exact_mod_cast hn
  have hL : 0 ≤ Real.log (24 * (Real.log 4 + 4)) :=
    Real.log_nonneg
      (by
        have hlog4 := Real.log_nonneg (by norm_num only : (1 : ℝ) ≤ 4)
        nlinarith only [hlog4])
  have hLscale := mul_le_mul_of_nonneg_left hKreal hL
  have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num only)
  have hthree := mul_le_mul_of_nonneg_right hηsmall hlog3
  have hconstant :=
    mul_le_mul_of_nonneg_left hKreal (add_nonneg (by norm_num only : (0 : ℝ) ≤ 18) hlog3)
  rw [Nat.cast_pow, Real.log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  nlinarith only [hlog, hnreal, hLscale, hthree, hconstant, hRscale]

/-- Under the near-one zero detector and the low-prime removal budgets, produce a
positive prime signal above `R^6` with a cutoff whose scaled logarithmic length is
bounded by an explicit absolute multiple of the detector order. Preserve the order cap.
Use the quantitative Euler cutoff, remove prime powers and low primes, and absorb the
fixed support terms. This supplies both ends of the finite support for the hybrid estimate. -/
theorem exists_high_prime_detector_signal_at_R_six_with_logarithmic_cutoff {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hq : 2 ≤ q) (hχ : χ ≠ 1) (hp : χ.IsPrimitive) (hinv : χ⁻¹ ≠ 1)
    {η D : ℝ} (hDdet : D = ordinaryLFunctionNearOneDetectorExponent) (hη : 0 < η)
    (hηsmall : η ≤ 1 / 1288) (hD : 0 ≤ D) (Krequested R : ℕ) (hKrequested : 2 ≤ Krequested)
    (hR : 2 ≤ R) (hDrequested : D + 5 ≤ 5 * ((Krequested - 1 : ℕ) : ℝ))
    (hRscale : η * Real.log (R : ℝ) ≤ 3)
    (hRorder : 18 ≤ Real.exp (-(D + 6)) * ((Krequested - 1 : ℕ) : ℝ))
    (hηratio : 4 * η ≤ Real.exp (-(D + 5)))
    (hm : Nat.ceil (Real.log higherPrimePowerEulerMajorantConstant) ≤ Krequested) {c ρ : ℂ}
    (hcre : c.re = 1 + η) (hcim : c.im = ρ.im) (hρre : |ρ.re - 1| ≤ η)
    (hzero : DirichletCharacter.completedLFunction χ ρ = 0)
    (hc : DirichletCharacter.completedLFunction χ c ≠ 0)
    (hzeroScale : η * Real.log ((q : ℝ) * (|ρ.im| + 3)) ≤ 3) :
    ∃ K n cutoff : ℕ,
      Krequested ≤ K ∧
        K ≤ n + 1 ∧
        n + 1 ≤ K * completedLFunctionNearOneDetectorMultiplicityCap ∧
        R ^ 6 ≤ cutoff ∧
        η * Real.log ((cutoff : ℝ) + 1) ≤
          (2 *
                ((completedLFunctionNearOneDetectorMultiplicityCap : ℝ) + D +
                  Real.log (24 * (Real.log 4 + 4))) +
              18 +
              Real.log 3) *
            K ∧
        Real.exp (-(D * (K : ℝ))) / 8 ≤
          (η ^ (n + 1) / (n.factorial : ℝ)) *
            ‖∑ p ∈ ((Finset.range (cutoff + 1)).filter Nat.Prime).filter (fun p => ¬p ≤ R ^ 6),
                LSeries.term
                  (LSeries.logMul^[n]
                    (fun j : ℕ ↦ χ (j : ZMod q) * (ArithmeticFunction.vonMangoldt j : ℂ)))
                  c p‖ := by
  have hcutmin : 1 ≤ R ^ 6 := by exact Nat.one_le_pow 6 R ((by norm_num only : 1 ≤ 2).trans hR)
  obtain ⟨K, n, cutoff, hKrequested', hK, hn, hKorder, hncap, hcutoffGe, hcutoff, hlog, hfinite⟩ :=
    exists_finite_Euler_polynomial_large_at_near_one_zero_with_logarithmic_cutoff hq hχ hp hinv hη
      hηsmall Krequested (R ^ 6) hKrequested hcutmin hcre hcim hρre hzero hc hzeroScale
  have hnorder : Krequested - 1 ≤ n := Nat.sub_le_iff_le_add.mpr (hKrequested'.trans hKorder)
  have hmargin := detector_order_exponential_margin Krequested n K D hD hDrequested hnorder hKorder
  have hceil : Nat.ceil (Real.log higherPrimePowerEulerMajorantConstant) ≤ n + 1 := by
    calc
      _ ≤ Krequested := hm
      _ ≤ K := hKrequested'
      _ ≤ n + 1 := hKorder
  let c₀ : ℝ := Real.exp (-(D + 6))
  have hc₀ : 0 ≤ c₀ := by
    dsimp only [c₀]; exact (Real.exp_pos _).le
  have hnreal : ((Krequested - 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hnorder
  have hRscale' : η * Real.log (R : ℝ) * 6 ≤ c₀ * (n : ℝ) := by
    calc
      η * Real.log (R : ℝ) * 6 ≤ 3 * 6 := mul_le_mul_of_nonneg_right hRscale (by norm_num only)
      _ = 18 := by norm_num only
      _ ≤ c₀ * ((Krequested - 1 : ℕ) : ℝ) := by simpa only [c₀] using hRorder
      _ ≤ c₀ * (n : ℝ) := mul_le_mul_of_nonneg_left hnreal hc₀
  have hscale : η * Real.log ((R ^ 6 : ℕ) : ℝ) ≤ c₀ * (n : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]
    calc
      η * (6 * Real.log (R : ℝ)) = 6 * (η * Real.log (R : ℝ)) := by ring
      _ ≤ 6 * 3 := mul_le_mul_of_nonneg_left hRscale (by norm_num only)
      _ = 18 := by norm_num only
      _ ≤ c₀ * (n : ℝ) := by
        calc
          18 ≤ c₀ * ((Krequested - 1 : ℕ) : ℝ) := by simpa only [c₀] using hRorder
          _ ≤ c₀ * (n : ℝ) := mul_le_mul_of_nonneg_left hnreal hc₀
  have hη1 : η ≤ 1 := le_trans hηsmall (by norm_num only)
  have hcexp : c₀ * Real.exp 1 ≤ Real.exp (-(D + 5)) := by
    dsimp only [c₀]
    have hexp : Real.exp (-(D + 6)) * Real.exp 1 = Real.exp (-(D + 5)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    exact le_of_eq hexp
  have hfinite' := hfinite
  rw [← hDdet] at hfinite'
  have hprime :=
    finite_high_prime_sum_norm_ge_of_detector_signal χ (R ^ 6) cutoff n K
      (by
        calc
          2 ≤ R := hR
          _ ≤ R ^ 6 := Nat.le_self_pow (by decide) R)
      hcutoffGe hη hη1 hD hc₀ hKorder hmargin hscale hcexp hηratio hceil c hcre hfinite'
  rw [← hDdet] at hlog
  have hlogUniform :=
    cutoff_log_le_uniform_detector_order η D K n R cutoff
      completedLFunctionNearOneDetectorMultiplicityCap ((by norm_num only : 1 ≤ 2).trans hK)
      ((Nat.le_succ n).trans hncap) hη1 hRscale hlog
  exact ⟨K, n, cutoff, hKrequested', hKorder, hncap, hcutoffGe, hlogUniform, hprime⟩

/--
Inputs: a primitive nonprincipal character, a nearby completed-function zero, a requested
detector order, and explicit order and scale budgets for the cutoff `R^6`.
Claim: the finite differentiated Euler detector yields a positive prime sum supported above
`R^6`, with at least one eighth of the exponential detector signal.
Proof: choose the Euler cutoff above `R^6`, derive the detector-order margin and logarithmic
scale, then remove the low primes and prime powers using the established remainder bounds.
Role: connects near-one zero detection to a positive prime polynomial at the scale needed by
the pre-sifted hybrid estimate.
-/
theorem exists_high_prime_detector_signal_at_R_six {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hq : 2 ≤ q) (hχ : χ ≠ 1) (hp : χ.IsPrimitive) (hinv : χ⁻¹ ≠ 1) {η D : ℝ}
    (hDdet : D = ordinaryLFunctionNearOneDetectorExponent) (hη : 0 < η) (hηsmall : η ≤ 1 / 1288)
    (hD : 0 ≤ D) (Krequested R : ℕ) (hKrequested : 2 ≤ Krequested) (hR : 2 ≤ R)
    (hDrequested : D + 5 ≤ 5 * ((Krequested - 1 : ℕ) : ℝ)) (hRscale : η * Real.log (R : ℝ) ≤ 3)
    (hRorder : 18 ≤ Real.exp (-(D + 6)) * ((Krequested - 1 : ℕ) : ℝ))
    (hηratio : 4 * η ≤ Real.exp (-(D + 5)))
    (hm : Nat.ceil (Real.log higherPrimePowerEulerMajorantConstant) ≤ Krequested) {c ρ : ℂ}
    (hcre : c.re = 1 + η) (hcim : c.im = ρ.im) (hρre : |ρ.re - 1| ≤ η)
    (hzero : DirichletCharacter.completedLFunction χ ρ = 0)
    (hc : DirichletCharacter.completedLFunction χ c ≠ 0)
    (hzeroScale : η * Real.log ((q : ℝ) * (|ρ.im| + 3)) ≤ 3) :
    ∃ K n cutoff : ℕ,
      Krequested ≤ K ∧
        K ≤ n + 1 ∧
        R ^ 6 ≤ cutoff ∧
        Real.exp (-(D * (K : ℝ))) / 8 ≤
          (η ^ (n + 1) / (n.factorial : ℝ)) *
            ‖∑ p ∈ ((Finset.range (cutoff + 1)).filter Nat.Prime).filter (fun p => ¬p ≤ R ^ 6),
                LSeries.term
                  (LSeries.logMul^[n]
                    (fun j : ℕ ↦ χ (j : ZMod q) * (ArithmeticFunction.vonMangoldt j : ℂ)))
                  c p‖ := by
  have hcutmin : 1 ≤ R ^ 6 := by exact Nat.one_le_pow 6 R (by omega)
  obtain
    ⟨massA, massB, hmassA, hmassB, Kmin, C, K, m, n, cutoff, hKrequested', hKupper, hKfixed, hKmin,
      hCeq, hK, hn, hnm, hmK, hmCap, hcutoffGe, hcutoff, hExplicit, hfinite⟩ :=
    exists_finite_Euler_polynomial_large_at_near_one_zero_with_minimum_cutoff hq hχ hp hinv hη
      hηsmall Krequested hKrequested (R ^ 6) hcutmin hcre hcim hρre hzero hc hzeroScale
  have hnorder : Krequested - 1 ≤ n := by omega
  have hKorder : K ≤ n + 1 := by omega
  have hmargin := detector_order_exponential_margin Krequested n K D hD hDrequested hnorder hKorder
  have hceil : Nat.ceil (Real.log higherPrimePowerEulerMajorantConstant) ≤ n + 1 := by
    calc
      _ ≤ Krequested := hm
      _ ≤ K := hKrequested'
      _ ≤ m := hmK
      _ = n + 1 := hnm.symm
  let c₀ : ℝ := Real.exp (-(D + 6))
  have hc₀ : 0 ≤ c₀ := by
    dsimp only [c₀]; positivity
  have hnreal : ((Krequested - 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hnorder
  have hRscale' : η * Real.log (R : ℝ) * 6 ≤ c₀ * (n : ℝ) := by
    calc
      η * Real.log (R : ℝ) * 6 ≤ 3 * 6 := mul_le_mul_of_nonneg_right hRscale (by norm_num)
      _ = 18 := by norm_num
      _ ≤ c₀ * ((Krequested - 1 : ℕ) : ℝ) := by simpa only [c₀] using hRorder
      _ ≤ c₀ * (n : ℝ) := mul_le_mul_of_nonneg_left hnreal hc₀
  have hscale : η * Real.log ((R ^ 6 : ℕ) : ℝ) ≤ c₀ * (n : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]
    calc
      η * (6 * Real.log (R : ℝ)) = 6 * (η * Real.log (R : ℝ)) := by ring
      _ ≤ 6 * 3 := mul_le_mul_of_nonneg_left hRscale (by norm_num)
      _ = 18 := by norm_num
      _ ≤ c₀ * (n : ℝ) := by
        calc
          18 ≤ c₀ * ((Krequested - 1 : ℕ) : ℝ) := by simpa only [c₀] using hRorder
          _ ≤ c₀ * (n : ℝ) := mul_le_mul_of_nonneg_left hnreal hc₀
  have hη1 : η ≤ 1 := le_trans hηsmall (by norm_num)
  have hcexp : c₀ * Real.exp 1 ≤ Real.exp (-(D + 5)) := by
    dsimp only [c₀]
    have hexp : Real.exp (-(D + 6)) * Real.exp 1 = Real.exp (-(D + 5)) := by
      rw [← Real.exp_add]
      congr 1
      ring_nf
    exact le_of_eq hexp
  have hfinite' := hfinite
  rw [← hDdet] at hfinite'
  have hprime :=
    finite_high_prime_sum_norm_ge_of_detector_signal χ (R ^ 6) cutoff n K
      (by
        calc
          2 ≤ R := hR
          _ ≤ R ^ 6 := Nat.le_self_pow (by decide) R)
      hcutoffGe hη hη1 hD hc₀ hKorder hmargin hscale hcexp hηratio hceil c hcre hfinite'
  exact ⟨K, n, cutoff, hKrequested', hKorder, hcutoffGe, hprime⟩

/--
Inputs: a dyadic interval `[N, 2N)`, a derivative order, and an exponent `σ ≥ 0`.

Claim: each von Mangoldt logarithmic weight on the interval is bounded by its logarithmic endpoint
majorant divided by `N^σ`.

Proof: use `Λ(k) ≤ log k`, monotonicity of the logarithm and real powers, and positivity of the
denominator.

Role: converts the differentiated Euler coefficients into the coefficient energy required by the
dyadic large-sieve estimate.
-/
theorem vonMangoldt_log_weight_le_dyadic_majorant {N r k : ℕ} (hN : 2 ≤ N) {σ : ℝ} (hσ : 0 ≤ σ)
    (hk : k ∈ Finset.Ico N (2 * N)) :
    ArithmeticFunction.vonMangoldt k * (Real.log k) ^ r / (k : ℝ) ^ σ ≤
      (Real.log (2 * N)) ^ (r + 1) / (N : ℝ) ^ σ := by
  rcases Finset.mem_Ico.mp hk with ⟨hlo, hhi⟩
  have hNposNat : 0 < N := lt_of_lt_of_le (by decide) hN
  have hkposNat : 0 < k := lt_of_lt_of_le hNposNat hlo
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNposNat
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hkposNat
  have hupperNat : k ≤ 2 * N := Nat.le_of_lt hhi
  have hupper : (k : ℝ) ≤ (2 * N : ℝ) := by exact_mod_cast hupperNat
  have hlog0 : 0 ≤ Real.log k := Real.log_natCast_nonneg k
  have hlogUpper0 : 0 ≤ Real.log (2 * N) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using Real.log_natCast_nonneg (2 * N)
  have hlogUpper : Real.log k ≤ Real.log (2 * N) := Real.log_le_log hkpos hupper
  have hlambda : ArithmeticFunction.vonMangoldt k ≤ Real.log k :=
    ArithmeticFunction.vonMangoldt_le_log
  have hlogpow : (Real.log k) ^ r ≤ (Real.log (2 * N)) ^ r := pow_le_pow_left₀ hlog0 hlogUpper r
  have hnum :
    ArithmeticFunction.vonMangoldt k * (Real.log k) ^ r ≤ (Real.log (2 * N)) ^ (r + 1) := by
    calc
      _ ≤ Real.log k * (Real.log k) ^ r := mul_le_mul_of_nonneg_right hlambda (pow_nonneg hlog0 r)
      _ ≤ Real.log (2 * N) * (Real.log (2 * N)) ^ r :=
        mul_le_mul hlogUpper hlogpow (pow_nonneg hlog0 r) hlogUpper0
      _ = (Real.log (2 * N)) ^ (r + 1) := by rw [← pow_succ']
  have hloR : (N : ℝ) ≤ (k : ℝ) := by exact_mod_cast hlo
  have hpow : (N : ℝ) ^ σ ≤ (k : ℝ) ^ σ := Real.rpow_le_rpow hNpos.le hloR hσ
  have hdenN : 0 < (N : ℝ) ^ σ := Real.rpow_pos_of_pos hNpos σ
  have hdenk : 0 < (k : ℝ) ^ σ := Real.rpow_pos_of_pos hkpos σ
  calc
    _ ≤ (Real.log (2 * N)) ^ (r + 1) / (k : ℝ) ^ σ := div_le_div_of_nonneg_right hnum hdenk.le
    _ ≤ (Real.log (2 * N)) ^ (r + 1) / (N : ℝ) ^ σ :=
      div_le_div_of_nonneg_left (pow_nonneg hlogUpper0 _) hdenN hpow

/--
Inputs: a dyadic interval `[N, 2N)`, a derivative order, and an exponent `σ ≥ 0`.

Claim: the sum of squared von Mangoldt logarithmic weights on the interval is at most its length
times the squared endpoint majorant.

Proof: apply the pointwise interval estimate and bound the finite sum by its cardinality times the
common majorant.

Role: supplies an explicit coefficient energy bound for the dyadic large-value estimate.
-/
theorem vonMangoldt_log_weight_sq_sum_Ico_le {N r : ℕ} (hN : 2 ≤ N) {σ : ℝ} (hσ : 0 ≤ σ) :
    (∑ k ∈ Finset.Ico N (2 * N),
        (ArithmeticFunction.vonMangoldt k * (Real.log k) ^ r / (k : ℝ) ^ σ) ^ 2) ≤
      (N : ℝ) * ((Real.log (2 * N)) ^ (r + 1) / (N : ℝ) ^ σ) ^ 2 := by
  let C : ℝ := (Real.log (2 * N)) ^ (r + 1) / (N : ℝ) ^ σ
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide) hN)
  have hlog : 0 ≤ Real.log (2 * N) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using Real.log_natCast_nonneg (2 * N)
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact div_nonneg (pow_nonneg hlog _) (le_of_lt (Real.rpow_pos_of_pos hNpos σ))
  have hpoint :
    ∀ k ∈ Finset.Ico N (2 * N),
      (ArithmeticFunction.vonMangoldt k * (Real.log k) ^ r / (k : ℝ) ^ σ) ^ 2 ≤ C ^ 2 := by
    intro k hk
    have hweight := vonMangoldt_log_weight_le_dyadic_majorant (r := r) hN hσ hk
    have hkposNat : 0 < k := lt_of_lt_of_le (lt_of_lt_of_le (by decide) hN) (Finset.mem_Ico.mp hk).1
    have hweight0 : 0 ≤ ArithmeticFunction.vonMangoldt k * (Real.log k) ^ r / (k : ℝ) ^ σ := by
      apply div_nonneg
      · exact
          mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
            (pow_nonneg (Real.log_natCast_nonneg k) r)
      · exact (Real.rpow_pos_of_pos (by exact_mod_cast hkposNat) σ).le
    dsimp only [C] at hweight ⊢
    exact (sq_le_sq₀ hweight0 (hweight0.trans hweight)).mpr hweight
  have hsum :=
    Finset.sum_le_card_nsmul (Finset.Ico N (2 * N))
      (fun k ↦ (ArithmeticFunction.vonMangoldt k * (Real.log k) ^ r / (k : ℝ) ^ σ) ^ 2) (C ^ 2)
      hpoint
  have hcard : (Finset.Ico N (2 * N)).card = N := by
    rw [Nat.card_Ico]
    omega
  simpa only [nsmul_eq_mul, hcard] using hsum

/--
Inputs: the scale assumptions for `primitiveCharacterLargeValueCount_mul_le_dyadic_large_sieve`,
a derivative order, `σ ≥ 0`, and a real threshold.

Claim: the number of primitive characters whose von Mangoldt logarithmic polynomial on `[N, 2N)`
has squared norm at least the threshold is bounded by an explicit endpoint weight.

Proof: apply the dyadic large-value estimate to the real coefficient sequence and use
`vonMangoldt_log_weight_sq_sum_Ico_le` to bound its coefficient energy.

Role: supplies the finite-block large-value estimate for the differentiated Euler series.
-/
theorem primitiveCharacterLargeValueCount_mul_le_vonMangoldt_dyadic (Qmax N r : ℕ) (hQ : 2 ≤ Qmax)
    (hN : Qmax * Qmax ≤ N) {σ : ℝ} (hσ : 0 ≤ σ) (threshold : ℝ) :
    (∑ q ∈ (Finset.Ioc 1 Qmax).attach,
          (((primitiveDirichletCharacterSet q.val).filter
                (fun χ =>
                  threshold ≤
                    Complex.normSq
                      (∑ n ∈ Finset.Ico N (2 * N),
                        ((ArithmeticFunction.vonMangoldt n * (Real.log n) ^ r / (n : ℝ) ^ σ : ℝ) :
                            ℂ) *
                          χ (n : ZMod q.val)))).card :
            ℝ)) *
        threshold ≤
      (21 / 2 : ℝ) * (Qmax : ℝ) * (N : ℝ) * (N : ℝ) *
        ((Real.log (2 * N)) ^ (r + 1) / (N : ℝ) ^ σ) ^ 2 := by
  let a : ℕ → ℂ := fun n ↦
    ((ArithmeticFunction.vonMangoldt n * (Real.log n) ^ r / (n : ℝ) ^ σ : ℝ) : ℂ)
  have hN2 : 2 ≤ N := by
    have hQQ : 2 * 2 ≤ Qmax * Qmax := Nat.mul_le_mul hQ hQ
    omega
  have hbase := primitiveCharacterLargeValueCount_mul_le_dyadic_large_sieve Qmax N hQ hN a threshold
  have henergy := vonMangoldt_log_weight_sq_sum_Ico_le (N := N) (r := r) hN2 hσ
  have hcoeff :
    ∑ n ∈ Finset.Ico N (2 * N), ‖a n‖ ^ 2 ≤
      (N : ℝ) * ((Real.log (2 * N)) ^ (r + 1) / (N : ℝ) ^ σ) ^ 2 := by
    simpa only [a, Complex.norm_real, Real.norm_eq_abs, sq_abs] using henergy
  have hscale0 : 0 ≤ (21 / 2 : ℝ) * (Qmax : ℝ) * (N : ℝ) := by
    exact mul_nonneg (mul_nonneg (by norm_num only) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  calc
    _ ≤ (21 / 2 : ℝ) * (Qmax : ℝ) * (N : ℝ) * ∑ n ∈ Finset.Ico N (2 * N), ‖a n‖ ^ 2 := by
      simpa only [a] using hbase
    _ ≤
        (21 / 2 : ℝ) * (Qmax : ℝ) * (N : ℝ) *
          ((N : ℝ) * ((Real.log (2 * N)) ^ (r + 1) / (N : ℝ) ^ σ) ^ 2) :=
      mul_le_mul_of_nonneg_left hcoeff hscale0
    _ =
        (21 / 2 : ℝ) * (Qmax : ℝ) * (N : ℝ) * (N : ℝ) *
          ((Real.log (2 * N)) ^ (r + 1) / (N : ℝ) ^ σ) ^ 2 :=
      by ring

/--
Inputs: the dyadic scale assumptions, a derivative order, a complex point with nonnegative real
part, and a threshold.

Claim: the number of primitive characters for which a differentiated von Mangoldt Euler block has
squared norm at least the threshold obeys the explicit dyadic large-value bound.

Proof: apply the character large-value estimate to the untwisted Euler coefficients and transfer
their complex norm-square sum to the real dyadic weight estimate.

Role: gives the fixed-height finite-block error estimate used by zero detection.
-/
theorem primitiveCharacterLargeValueCount_mul_le_euler_dyadic (Qmax N r : ℕ) (hQ : 2 ≤ Qmax)
    (hN : Qmax * Qmax ≤ N) {s : ℂ} (hs : 0 ≤ s.re) (threshold : ℝ) :
    (∑ q ∈ (Finset.Ioc 1 Qmax).attach,
          (((primitiveDirichletCharacterSet q.val).filter
                (fun χ =>
                  threshold ≤
                    Complex.normSq
                      (∑ n ∈ Finset.Ico N (2 * N),
                        LSeries.term
                            (LSeries.logMul^[r]
                              (fun j : ℕ ↦ (ArithmeticFunction.vonMangoldt j : ℂ)))
                            s n *
                          χ (n : ZMod q.val)))).card :
            ℝ)) *
        threshold ≤
      (21 / 2 : ℝ) * (Qmax : ℝ) * (N : ℝ) * (N : ℝ) *
        ((Real.log (2 * N)) ^ (r + 1) / (N : ℝ) ^ s.re) ^ 2 := by
  let a : ℕ → ℂ := fun n ↦
    LSeries.term (LSeries.logMul^[r] (fun j : ℕ ↦ (ArithmeticFunction.vonMangoldt j : ℂ))) s n
  have hN2 : 2 ≤ N := by
    have hQQ : 2 * 2 ≤ Qmax * Qmax := Nat.mul_le_mul hQ hQ
    omega
  have hbase := primitiveCharacterLargeValueCount_mul_le_dyadic_large_sieve Qmax N hQ hN a threshold
  have henergy := vonMangoldt_log_weight_sq_sum_Ico_le (N := N) (r := r) hN2 hs
  have hnorm :
    ∀ n ∈ Finset.Ico N (2 * N),
      ‖a n‖ = ArithmeticFunction.vonMangoldt n * (Real.log n) ^ r / (n : ℝ) ^ s.re := by
    intro n hn
    have hnpos : 0 < n := lt_of_lt_of_le (lt_of_lt_of_le (by decide) hN2) (Finset.mem_Ico.mp hn).1
    exact norm_vonMangoldt_logMul_term_eq r n hnpos
  have hcoeff :
    ∑ n ∈ Finset.Ico N (2 * N), ‖a n‖ ^ 2 ≤
      (N : ℝ) * ((Real.log (2 * N)) ^ (r + 1) / (N : ℝ) ^ s.re) ^ 2 := by
    calc
      _ =
          ∑ n ∈ Finset.Ico N (2 * N),
            (ArithmeticFunction.vonMangoldt n * (Real.log n) ^ r / (n : ℝ) ^ s.re) ^ 2 :=
        by
        apply Finset.sum_congr rfl
        intro n hn
        rw [hnorm n hn]
      _ ≤ _ := henergy
  have hscale0 : 0 ≤ (21 / 2 : ℝ) * (Qmax : ℝ) * (N : ℝ) := by
    exact mul_nonneg (mul_nonneg (by norm_num only) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  calc
    _ ≤ (21 / 2 : ℝ) * (Qmax : ℝ) * (N : ℝ) * ∑ n ∈ Finset.Ico N (2 * N), ‖a n‖ ^ 2 := by
      simpa only [a] using hbase
    _ ≤
        (21 / 2 : ℝ) * (Qmax : ℝ) * (N : ℝ) *
          ((N : ℝ) * ((Real.log (2 * N)) ^ (r + 1) / (N : ℝ) ^ s.re) ^ 2) :=
      mul_le_mul_of_nonneg_left hcoeff hscale0
    _ =
        (21 / 2 : ℝ) * (Qmax : ℝ) * (N : ℝ) * (N : ℝ) *
          ((Real.log (2 * N)) ^ (r + 1) / (N : ℝ) ^ s.re) ^ 2 :=
      by ring

/--
Inputs: a Dirichlet character, a complex point, a derivative order, and a finite interval whose
lower endpoint is at least two.

Claim: the norm of the twisted differentiated Euler-series block is bounded by the sum of its
positive von Mangoldt logarithmic weights.

Proof: apply the norm triangle inequality to the finite sum and bound each twisted term by its
untwisted positive majorant.

Role: provides the finite block decomposition estimate needed to combine dyadic large-value bounds.
-/
theorem norm_twisted_vonMangoldt_logMul_sum_Ico_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (s : ℂ) (r M K : ℕ) (hM : 2 ≤ M) :
    ‖∑ n ∈ Finset.Ico M K,
          LSeries.term
            (LSeries.logMul^[r]
              (fun j : ℕ ↦ χ (j : ZMod q) * (ArithmeticFunction.vonMangoldt j : ℂ)))
            s n‖ ≤
      ∑ n ∈ Finset.Ico M K,
        ArithmeticFunction.vonMangoldt n * (Real.log n) ^ r / (n : ℝ) ^ s.re := by
  calc
    _ ≤
        ∑ n ∈ Finset.Ico M K,
          ‖LSeries.term
              (LSeries.logMul^[r]
                (fun j : ℕ ↦ χ (j : ZMod q) * (ArithmeticFunction.vonMangoldt j : ℂ)))
              s n‖ :=
      norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro n hn
      have hnpos : 0 < n := lt_of_lt_of_le (lt_of_lt_of_le (by decide) hM) (Finset.mem_Ico.mp hn).1
      exact twistedVonMangoldt_log_term_bound χ r n (s := s) hnpos

/--
Inputs: a summand on the natural numbers, an initial block width, and a number of blocks.

Claim: summing over consecutive intervals whose endpoints double from `N` gives the sum over
`[N, N * 2^J)`.

Proof: induct on the number of blocks and join the last interval to the preceding interval.

Role: partitions a finite Euler tail into the dyadic blocks controlled by the large-sieve bound.
-/
theorem sum_Ico_geometric_dyadic_blocks {M : Type*} [AddCommMonoid M] (f : ℕ → M) (N J : ℕ) :
    (∑ j ∈ Finset.range J, ∑ n ∈ Finset.Ico (N * 2 ^ j) (N * 2 ^ (j + 1)), f n) =
      ∑ n ∈ Finset.Ico (N * 1) (N * 2 ^ J), f n := by
  induction J with
  | zero =>
    simp only [Finset.sum_range_zero, Nat.pow_zero, Nat.mul_one, Finset.Ico_self, Finset.sum_empty]
  | succ J ih =>
    rw [Finset.sum_range_succ, ih]
    have hpow : 2 ^ J ≤ 2 ^ (J + 1) := by
      calc
        2 ^ J = 2 ^ J * 1 := by simp only [Nat.mul_one]
        _ ≤ 2 ^ J * 2 := Nat.mul_le_mul_left _ (by decide : 1 ≤ 2)
        _ = 2 ^ (J + 1) := by rw [Nat.pow_succ]
    rw [Finset.sum_Ico_consecutive f (Nat.mul_le_mul_left N (Nat.one_le_pow J 2 (by decide)))
        (Nat.mul_le_mul_left N hpow)]

/--
Inputs: a Dirichlet character, a complex point, a derivative order, and the endpoints for a finite
sequence of dyadic blocks.

Claim: the twisted differentiated Euler sum over the combined interval equals the sum of its
individual dyadic blocks.

Proof: specialize `sum_Ico_geometric_dyadic_blocks` to the Euler-series summand.

Role: presents one finite Euler tail in the block form used by the large-sieve estimates.
-/
theorem twisted_vonMangoldt_logMul_sum_eq_dyadic_blocks {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (s : ℂ) (r N J : ℕ) :
    ∑ n ∈ Finset.Ico (N * 1) (N * 2 ^ J),
        LSeries.term
          (LSeries.logMul^[r] (fun j : ℕ ↦ χ (j : ZMod q) * (ArithmeticFunction.vonMangoldt j : ℂ)))
          s n =
      ∑ j ∈ Finset.range J,
        ∑ n ∈ Finset.Ico (N * 2 ^ j) (N * 2 ^ (j + 1)),
          LSeries.term
            (LSeries.logMul^[r]
              (fun k : ℕ ↦ χ (k : ZMod q) * (ArithmeticFunction.vonMangoldt k : ℂ)))
            s n := by
  exact
    (sum_Ico_geometric_dyadic_blocks (f := fun n : ℕ =>
        LSeries.term
          (LSeries.logMul^[r] (fun k : ℕ ↦ χ (k : ZMod q) * (ArithmeticFunction.vonMangoldt k : ℂ)))
          s n)
        N J).symm

/--
Inputs: a Dirichlet character, a complex point, a derivative order, and a finite dyadic range
beginning at `N ≥ 2`.

Claim: the norm of the combined twisted Euler blocks is at most the sum of their positive
von Mangoldt logarithmic weights.

Proof: rewrite the block sum as one interval sum, apply the finite interval majorant, and partition
the positive weight sum back into the same dyadic blocks.

Role: combines finite block decomposition with its pointwise majorant for later mean-square tail
estimates.
-/
theorem norm_twisted_vonMangoldt_logMul_dyadic_sum_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (s : ℂ) (r N J : ℕ) (hN : 2 ≤ N) :
    ‖∑ j ∈ Finset.range J,
          ∑ n ∈ Finset.Ico (N * 2 ^ j) (N * 2 ^ (j + 1)),
            LSeries.term
              (LSeries.logMul^[r]
                (fun k : ℕ ↦ χ (k : ZMod q) * (ArithmeticFunction.vonMangoldt k : ℂ)))
              s n‖ ≤
      ∑ j ∈ Finset.range J,
        ∑ n ∈ Finset.Ico (N * 2 ^ j) (N * 2 ^ (j + 1)),
          ArithmeticFunction.vonMangoldt n * (Real.log n) ^ r / (n : ℝ) ^ s.re := by
  calc
    _ =
        ‖∑ n ∈ Finset.Ico (N * 1) (N * 2 ^ J),
            LSeries.term
              (LSeries.logMul^[r]
                (fun k : ℕ ↦ χ (k : ZMod q) * (ArithmeticFunction.vonMangoldt k : ℂ)))
              s n‖ :=
      by rw [twisted_vonMangoldt_logMul_sum_eq_dyadic_blocks]
    _ ≤
        ∑ n ∈ Finset.Ico (N * 1) (N * 2 ^ J),
          ArithmeticFunction.vonMangoldt n * (Real.log n) ^ r / (n : ℝ) ^ s.re :=
      norm_twisted_vonMangoldt_logMul_sum_Ico_le χ s r (N * 1) (N * 2 ^ J)
        (by simpa only [Nat.mul_one] using hN)
    _ =
        ∑ j ∈ Finset.range J,
          ∑ n ∈ Finset.Ico (N * 2 ^ j) (N * 2 ^ (j + 1)),
            ArithmeticFunction.vonMangoldt n * (Real.log n) ^ r / (n : ℝ) ^ s.re :=
      (sum_Ico_geometric_dyadic_blocks (f := fun n : ℕ =>
          ArithmeticFunction.vonMangoldt n * (Real.log n) ^ r / (n : ℝ) ^ s.re) N J).symm

/--
Inputs: a finite coordinate type, a finite set of summands, and a complex vector for each summand.

Claim: the square root of the total coordinatewise squared norm of the sum is at most the sum of
the corresponding square-root norms.

Proof: represent each vector in `PiLp 2`, apply the norm triangle inequality, and use the formula
for the `L²` norm.

Role: combines dyadic block bounds in one finite family of moduli and primitive characters.
-/
theorem l2_minkowski_finite {ι κ : Type*} [Fintype ι] (s : Finset κ) (f : κ → ι → ℂ) :
    Real.sqrt (∑ i, Complex.normSq (∑ k ∈ s, f k i)) ≤
      ∑ k ∈ s, Real.sqrt (∑ i, Complex.normSq (f k i)) := by
  classical
  let v : κ → PiLp 2 (fun _ : ι => ℂ) := fun k => WithLp.toLp 2 (f k)
  have hvsum : (∑ k ∈ s, v k) = WithLp.toLp 2 (fun i => ∑ k ∈ s, f k i) := by
    apply PiLp.ext
    intro i
    induction s using Finset.induction_on with
    | empty => simp
    | @insert k s hk ih =>
      simp only [Finset.sum_insert hk, PiLp.add_apply, ih]
      simp only [v]
  calc
    _ = ‖∑ k ∈ s, v k‖ := by
      rw [hvsum, PiLp.norm_eq_of_L2]
      simp only [Complex.normSq_eq_norm_sq]
    _ ≤ ∑ k ∈ s, ‖v k‖ := norm_sum_le _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [PiLp.norm_eq_of_L2]
      simp only [v, Complex.normSq_eq_norm_sq]

/--
Inputs: a finite number of complex summands, a complex sequence, and a positive squared-norm
threshold.

Claim: if the sum has squared norm at least `V`, then some summand has squared norm at least
`V / J²`.

Proof: if every summand were smaller, its norm would be below `sqrt V / J`; the triangle
inequality and the exact cardinality of `range J` would then put the norm of the sum below
`sqrt V`.

Role: reduces a finite dyadic-block large-value event to a union of blockwise large-value events.
-/
theorem exists_dyadic_block_large_of_normSq_sum (J : ℕ) (f : ℕ → ℂ) (V : ℝ) (hJ : 0 < J)
    (hV : 0 < V) (hlarge : V ≤ Complex.normSq (∑ j ∈ Finset.range J, f j)) :
    ∃ j ∈ Finset.range J, V / (J : ℝ) ^ 2 ≤ Complex.normSq (f j) := by
  classical
  by_contra hnone
  have hsmall (j : ℕ) (hj : j ∈ Finset.range J) : Complex.normSq (f j) < V / (J : ℝ) ^ 2 := by
    have hnot : ¬V / (J : ℝ) ^ 2 ≤ Complex.normSq (f j) := by
      intro h
      exact hnone ⟨j, hj, h⟩
    exact lt_of_not_ge hnot
  have hterm (j : ℕ) (hj : j ∈ Finset.range J) : ‖f j‖ < Real.sqrt V / J := by
    have hden : 0 < (J : ℝ) ^ 2 := by exact pow_pos (by exact_mod_cast hJ) 2
    have hmul := (lt_div_iff₀ hden).mp (by simpa only [Complex.normSq_eq_norm_sq] using hsmall j hj)
    have hJr : 0 < (J : ℝ) := by exact_mod_cast hJ
    by_contra hle
    have hrootle : Real.sqrt V ≤ ‖f j‖ * J := by
      apply (div_le_iff₀ hJr).mp
      exact le_of_not_gt hle
    have hsqrt : (Real.sqrt V) ^ 2 = V := Real.sq_sqrt hV.le
    have hsquare : (Real.sqrt V) ^ 2 ≤ (‖f j‖ * J) ^ 2 :=
      (sq_le_sq₀ (Real.sqrt_nonneg V) (mul_nonneg (norm_nonneg _) (le_of_lt hJr))).2 hrootle
    have hproduct : (‖f j‖ * J) ^ 2 = ‖f j‖ ^ 2 * (J : ℝ) ^ 2 := by ring
    rw [hsqrt, hproduct] at hsquare
    linarith only [hmul, hsquare]
  have hsum : (∑ j ∈ Finset.range J, ‖f j‖) < ∑ _j ∈ Finset.range J, Real.sqrt V / J := by
    apply Finset.sum_lt_sum
    · intro j hj
      exact le_of_lt (hterm j hj)
    · refine ⟨0, Finset.mem_range.mpr hJ, ?_⟩
      exact hterm 0 (Finset.mem_range.mpr hJ)
  have hnorm : ‖∑ j ∈ Finset.range J, f j‖ ≤ ∑ j ∈ Finset.range J, ‖f j‖ := norm_sum_le _ _
  have hsqrtle : Real.sqrt V ≤ ‖∑ j ∈ Finset.range J, f j‖ := by
    by_contra h
    have hlt : ‖∑ j ∈ Finset.range J, f j‖ < Real.sqrt V := lt_of_not_ge h
    have hsqrt : (Real.sqrt V) ^ 2 = V := Real.sq_sqrt hV.le
    have hlt_sq : (‖∑ j ∈ Finset.range J, f j‖) ^ 2 < (Real.sqrt V) ^ 2 :=
      (sq_lt_sq₀ (norm_nonneg _) (Real.sqrt_nonneg V)).2 hlt
    rw [hsqrt] at hlt_sq
    rw [Complex.normSq_eq_norm_sq] at hlarge
    linarith only [hlarge, hlt_sq]
  have hconst : (∑ _j ∈ Finset.range J, Real.sqrt V / J) = Real.sqrt V := by
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hJr : (J : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hJ)
    field_simp
  linarith only [hsqrtle, hnorm, hsum, hconst]

/--
Inputs: a finite sequence of complex summands, positive weights summing to one, and a positive
squared-norm threshold.

Claim: if the sum has squared norm at least `V`, then some block has squared norm at least
`V * w_j²`.

Proof: if every block were smaller, each block norm would be below `sqrt V * w_j`; summing and using
the weight identity would put the norm of the total below `sqrt V`.

Role: allocates a total large-value threshold among dyadic blocks without an equal `J²` loss.
-/
theorem exists_weighted_block_large_of_normSq_sum (J : ℕ) (f : ℕ → ℂ) (w : ℕ → ℝ) (V : ℝ)
    (hJ : 0 < J) (hV : 0 < V) (hwpos : ∀ j ∈ Finset.range J, 0 < w j)
    (hwSum : ∑ j ∈ Finset.range J, w j = 1)
    (hlarge : V ≤ Complex.normSq (∑ j ∈ Finset.range J, f j)) :
    ∃ j ∈ Finset.range J, V * (w j) ^ 2 ≤ Complex.normSq (f j) := by
  classical
  by_contra hnone
  have hsmall (j : ℕ) (hj : j ∈ Finset.range J) : Complex.normSq (f j) < V * (w j) ^ 2 := by
    have hnot : ¬V * (w j) ^ 2 ≤ Complex.normSq (f j) := by
      intro h
      exact hnone ⟨j, hj, h⟩
    exact lt_of_not_ge hnot
  have hterm (j : ℕ) (hj : j ∈ Finset.range J) : ‖f j‖ < Real.sqrt V * w j := by
    have hprod : (Real.sqrt V * w j) ^ 2 = V * (w j) ^ 2 := by
      calc
        _ = (Real.sqrt V) ^ 2 * (w j) ^ 2 := by ring
        _ = V * (w j) ^ 2 := by rw [Real.sq_sqrt hV.le]
    have hsmall' := hsmall j hj
    rw [Complex.normSq_eq_norm_sq] at hsmall'
    have hsq : ‖f j‖ ^ 2 < (Real.sqrt V * w j) ^ 2 := by
      calc
        _ < V * (w j) ^ 2 := hsmall'
        _ = (Real.sqrt V * w j) ^ 2 := hprod.symm
    exact
      (sq_lt_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg V) (le_of_lt (hwpos j hj)))).mp hsq
  have hsum : (∑ j ∈ Finset.range J, ‖f j‖) < ∑ j ∈ Finset.range J, Real.sqrt V * w j := by
    apply Finset.sum_lt_sum
    · intro j hj
      exact le_of_lt (hterm j hj)
    · refine ⟨0, Finset.mem_range.mpr hJ, ?_⟩
      exact hterm 0 (Finset.mem_range.mpr hJ)
  have hweighted : (∑ j ∈ Finset.range J, Real.sqrt V * w j) = Real.sqrt V := by
    calc
      _ = Real.sqrt V * (∑ j ∈ Finset.range J, w j) := by
        symm
        exact Finset.mul_sum (Finset.range J) w (Real.sqrt V)
      _ = Real.sqrt V := by
        rw [hwSum]; ring
  have hnorm : ‖∑ j ∈ Finset.range J, f j‖ ≤ ∑ j ∈ Finset.range J, ‖f j‖ := norm_sum_le _ _
  have hsqrtle : Real.sqrt V ≤ ‖∑ j ∈ Finset.range J, f j‖ := by
    by_contra h
    have hlt : ‖∑ j ∈ Finset.range J, f j‖ < Real.sqrt V := lt_of_not_ge h
    have hsqrt : (Real.sqrt V) ^ 2 = V := Real.sq_sqrt hV.le
    have hlt_sq : (‖∑ j ∈ Finset.range J, f j‖) ^ 2 < (Real.sqrt V) ^ 2 :=
      (sq_lt_sq₀ (norm_nonneg _) (Real.sqrt_nonneg V)).2 hlt
    rw [hsqrt] at hlt_sq
    rw [Complex.normSq_eq_norm_sq] at hlarge
    linarith only [hlarge, hlt_sq]
  linarith only [hsqrtle, hnorm, hsum, hweighted]

/--
Inputs: a finite set of coordinates, a positive number of blocks, a complex block value for each
coordinate, and a positive squared-norm threshold.

Claim: the number of coordinates whose sum over all blocks reaches the threshold is at most the sum
of the numbers reaching the reduced threshold `V / J²` in each block.

Proof: use `exists_dyadic_block_large_of_normSq_sum` to include the total large-value set in the
finite union of the blockwise large-value sets, then apply the finite-union cardinality bound.

Role: aggregates blockwise large-value estimates for a finite character set at one fixed modulus.
-/
theorem card_large_sum_le_sum_card_large_blocks {κ : Type*} (s : Finset κ) (J : ℕ) (f : ℕ → κ → ℂ)
    (V : ℝ) (hJ : 0 < J) (hV : 0 < V) :
    (s.filter fun x => V ≤ Complex.normSq (∑ j ∈ Finset.range J, f j x)).card ≤
      ∑ j ∈ Finset.range J, (s.filter fun x => V / (J : ℝ) ^ 2 ≤ Complex.normSq (f j x)).card := by
  classical
  let bad := s.filter fun x => V ≤ Complex.normSq (∑ j ∈ Finset.range J, f j x)
  let blocks := fun j => s.filter fun x => V / (J : ℝ) ^ 2 ≤ Complex.normSq (f j x)
  have hsub : bad ⊆ (Finset.range J).biUnion blocks := by
    intro x hx
    rcases Finset.mem_filter.mp hx with ⟨hxs, hlarge⟩
    obtain ⟨j, hj, hblock⟩ :=
      exists_dyadic_block_large_of_normSq_sum J (fun j => f j x) V hJ hV hlarge
    exact Finset.mem_biUnion.mpr ⟨j, hj, Finset.mem_filter.mpr ⟨hxs, hblock⟩⟩
  calc
    _ = bad.card := rfl
    _ ≤ ((Finset.range J).biUnion blocks).card := Finset.card_le_card hsub
    _ ≤ ∑ j ∈ Finset.range J, (blocks j).card := Finset.card_biUnion_le
    _ = _ := rfl

/--
Inputs: a finite coordinate set, complex block values, positive weights summing to one, and a
positive squared-norm threshold.

Claim: the total large-value count is at most the sum of blockwise counts at thresholds `V * w_j²`.

Proof: include the total large-value set in the finite union supplied by
`exists_weighted_block_large_of_normSq_sum` and bound the union cardinality.

Role: prepares weighted block thresholds for primitive-character large-sieve estimates.
-/
theorem card_large_sum_le_sum_card_weighted_blocks {κ : Type*} (s : Finset κ) (J : ℕ)
    (f : ℕ → κ → ℂ) (w : ℕ → ℝ) (V : ℝ) (hJ : 0 < J) (hV : 0 < V)
    (hwpos : ∀ j ∈ Finset.range J, 0 < w j) (hwSum : ∑ j ∈ Finset.range J, w j = 1) :
    (s.filter fun x => V ≤ Complex.normSq (∑ j ∈ Finset.range J, f j x)).card ≤
      ∑ j ∈ Finset.range J, (s.filter fun x => V * (w j) ^ 2 ≤ Complex.normSq (f j x)).card := by
  classical
  let bad := s.filter fun x => V ≤ Complex.normSq (∑ j ∈ Finset.range J, f j x)
  let blocks := fun j => s.filter fun x => V * (w j) ^ 2 ≤ Complex.normSq (f j x)
  have hsub : bad ⊆ (Finset.range J).biUnion blocks := by
    intro x hx
    rcases Finset.mem_filter.mp hx with ⟨hxs, hlarge⟩
    obtain ⟨j, hj, hblock⟩ :=
      exists_weighted_block_large_of_normSq_sum J (fun j => f j x) w V hJ hV hwpos hwSum hlarge
    exact Finset.mem_biUnion.mpr ⟨j, hj, Finset.mem_filter.mpr ⟨hxs, hblock⟩⟩
  calc
    _ = bad.card := rfl
    _ ≤ ((Finset.range J).biUnion blocks).card := Finset.card_le_card hsub
    _ ≤ ∑ j ∈ Finset.range J, (blocks j).card := Finset.card_biUnion_le
    _ = _ := rfl

/--
Inputs: a modulus cutoff, a common dyadic starting point and block count, Euler coefficients, and a
positive squared-norm threshold.

Claim: the number of primitive characters over all moduli up to `Qmax` whose sum over the finite
dyadic blocks reaches `V` is at most the sum of the blockwise counts at threshold `V / J²`.

Proof: apply `card_large_sum_le_sum_card_large_blocks` for each modulus and interchange the two
finite sums.

Role: arranges the finite family estimate in the order needed to apply the dyadic large sieve block
by block.
-/
theorem primitiveCharacterFamily_dyadic_largeCount_le_sum_block_counts (Qmax J N : ℕ) (a : ℕ → ℂ)
    (V : ℝ) (hJ : 0 < J) (hV : 0 < V) :
    (∑ q ∈ (Finset.Ioc 1 Qmax).attach,
        ((primitiveDirichletCharacterSet q.val).filter fun χ =>
            V ≤
              Complex.normSq
                (∑ j ∈ Finset.range J,
                  ∑ n ∈ Finset.Ico (N * 2 ^ j) (N * 2 ^ (j + 1)), a n * χ (n : ZMod q.val))).card) ≤
      ∑ j ∈ Finset.range J,
        ∑ q ∈ (Finset.Ioc 1 Qmax).attach,
          ((primitiveDirichletCharacterSet q.val).filter fun χ =>
              V / (J : ℝ) ^ 2 ≤
                Complex.normSq
                  (∑ n ∈ Finset.Ico (N * 2 ^ j) (N * 2 ^ (j + 1)),
                    a n * χ (n : ZMod q.val))).card := by
  classical
    calc
    _ ≤
        ∑ q ∈ (Finset.Ioc 1 Qmax).attach,
          ∑ j ∈ Finset.range J,
            ((primitiveDirichletCharacterSet q.val).filter fun χ =>
                V / (J : ℝ) ^ 2 ≤
                  Complex.normSq
                    (∑ n ∈ Finset.Ico (N * 2 ^ j) (N * 2 ^ (j + 1)),
                      a n * χ (n : ZMod q.val))).card :=
      by
      apply Finset.sum_le_sum
      intro q hq
      exact
        card_large_sum_le_sum_card_large_blocks (primitiveDirichletCharacterSet q.val) J
          (fun j χ => ∑ n ∈ Finset.Ico (N * 2 ^ j) (N * 2 ^ (j + 1)), a n * χ (n : ZMod q.val)) V hJ
          hV
    _ = _ := by rw [Finset.sum_comm]

/--
Inputs: a modulus cutoff, a finite dyadic range, coefficients, and positive block weights summing to
one.

Claim: the total primitive-character large-value count is at most the sum of blockwise counts at
the allocated thresholds `V * w_j²`.

Proof: apply `card_large_sum_le_sum_card_weighted_blocks` at each modulus and interchange finite
sums.

Role: exposes the weighted count split in the family order used by blockwise large-sieve estimates.
-/
theorem primitiveCharacterFamily_dyadic_weightedLargeCount_le_sum_block_counts (Qmax J N : ℕ)
    (a : ℕ → ℂ) (w : ℕ → ℝ) (V : ℝ) (hJ : 0 < J) (hV : 0 < V)
    (hwpos : ∀ j ∈ Finset.range J, 0 < w j) (hwSum : ∑ j ∈ Finset.range J, w j = 1) :
    (∑ q ∈ (Finset.Ioc 1 Qmax).attach,
        ((primitiveDirichletCharacterSet q.val).filter fun χ =>
            V ≤
              Complex.normSq
                (∑ j ∈ Finset.range J,
                  ∑ n ∈ Finset.Ico (N * 2 ^ j) (N * 2 ^ (j + 1)), a n * χ (n : ZMod q.val))).card) ≤
      ∑ j ∈ Finset.range J,
        ∑ q ∈ (Finset.Ioc 1 Qmax).attach,
          ((primitiveDirichletCharacterSet q.val).filter fun χ =>
              V * (w j) ^ 2 ≤
                Complex.normSq
                  (∑ n ∈ Finset.Ico (N * 2 ^ j) (N * 2 ^ (j + 1)),
                    a n * χ (n : ZMod q.val))).card := by
  classical
    calc
    _ ≤
        ∑ q ∈ (Finset.Ioc 1 Qmax).attach,
          ∑ j ∈ Finset.range J,
            ((primitiveDirichletCharacterSet q.val).filter fun χ =>
                V * (w j) ^ 2 ≤
                  Complex.normSq
                    (∑ n ∈ Finset.Ico (N * 2 ^ j) (N * 2 ^ (j + 1)),
                      a n * χ (n : ZMod q.val))).card :=
      by
      apply Finset.sum_le_sum
      intro q hq
      exact
        card_large_sum_le_sum_card_weighted_blocks (primitiveDirichletCharacterSet q.val) J
          (fun j χ => ∑ n ∈ Finset.Ico (N * 2 ^ j) (N * 2 ^ (j + 1)), a n * χ (n : ZMod q.val)) w V
          hJ hV hwpos hwSum
    _ = _ := by rw [Finset.sum_comm]

/--
Inputs: a modulus cutoff, a dyadic range starting at `N`, a coefficient sequence, and a threshold.

Claim: the sum over all dyadic blocks of the primitive-character large-value count multiplied by
the threshold is bounded by the sum of the corresponding dyadic large-sieve energy bounds.

Proof: apply `primitiveCharacterLargeValueCount_mul_le_dyadic_large_sieve` to each block; its
scale hypothesis propagates from `Qmax² ≤ N` to `Qmax² ≤ N * 2^j`.

Role: supplies the blockwise bounds used with
`primitiveCharacterFamily_dyadic_largeCount_le_sum_block_counts`.
-/
theorem primitiveCharacterFamily_dyadic_blockCount_mul_le (Qmax N J : ℕ) (hQ : 2 ≤ Qmax)
    (hN : Qmax * Qmax ≤ N) (a : ℕ → ℂ) (threshold : ℝ) :
    (∑ j ∈ Finset.range J,
        (∑ q ∈ (Finset.Ioc 1 Qmax).attach,
            (((primitiveDirichletCharacterSet q.val).filter fun χ =>
                  threshold ≤
                    Complex.normSq
                      (∑ n ∈ Finset.Ico (N * 2 ^ j) (N * 2 ^ (j + 1)),
                        a n * χ (n : ZMod q.val))).card :
              ℝ)) *
          threshold) ≤
      ∑ j ∈ Finset.range J,
        (21 / 2 : ℝ) * (Qmax : ℝ) * ((N * 2 ^ j : ℕ) : ℝ) *
          ∑ n ∈ Finset.Ico (N * 2 ^ j) (N * 2 ^ (j + 1)), ‖a n‖ ^ 2 := by
  apply Finset.sum_le_sum
  intro j hj
  have hpow : 1 ≤ 2 ^ j := Nat.one_le_pow j 2 (by decide)
  have hNj : Qmax * Qmax ≤ N * 2 ^ j := by
    calc
      Qmax * Qmax ≤ N := hN
      _ = N * 1 := by simp only [Nat.mul_one]
      _ ≤ N * 2 ^ j := Nat.mul_le_mul_left N hpow
  have hinterval :
    Finset.Ico (N * 2 ^ j) (N * 2 ^ (j + 1)) = Finset.Ico (N * 2 ^ j) (2 * (N * 2 ^ j)) := by
    congr 1
    rw [Nat.pow_succ]
    ring
  rw [hinterval]
  exact
    primitiveCharacterLargeValueCount_mul_le_dyadic_large_sieve Qmax (N * 2 ^ j) hQ hNj a threshold

/--
Inputs: the hypotheses for a finite dyadic range, a positive total squared-norm threshold, and
complex coefficients.

Claim: the total large-value count multiplied by `V / J²` is bounded by the sum of the dyadic
large-sieve energy estimates.

Proof: reduce the total event to blockwise events, cast the cardinality inequality to `ℝ`, and
apply the blockwise large-sieve bounds at the reduced threshold.

Role: gives a finite-range family estimate without enumerating all modulus-character pairs as one
dependent `Fintype`.
-/
theorem primitiveCharacterFamily_dyadic_sumLargeCount_mul_le (Qmax N J : ℕ) (hQ : 2 ≤ Qmax)
    (hN : Qmax * Qmax ≤ N) (a : ℕ → ℂ) (V : ℝ) (hJ : 0 < J) (hV : 0 < V) :
    (∑ q ∈ (Finset.Ioc 1 Qmax).attach,
          (((primitiveDirichletCharacterSet q.val).filter fun χ =>
                V ≤
                  Complex.normSq
                    (∑ j ∈ Finset.range J,
                      ∑ n ∈ Finset.Ico (N * 2 ^ j) (N * 2 ^ (j + 1)),
                        a n * χ (n : ZMod q.val))).card :
            ℝ)) *
        (V / (J : ℝ) ^ 2) ≤
      ∑ j ∈ Finset.range J,
        (21 / 2 : ℝ) * (Qmax : ℝ) * ((N * 2 ^ j : ℕ) : ℝ) *
          ∑ n ∈ Finset.Ico (N * 2 ^ j) (N * 2 ^ (j + 1)), ‖a n‖ ^ 2 := by
  have hcount := primitiveCharacterFamily_dyadic_largeCount_le_sum_block_counts Qmax J N a V hJ hV
  have hcountReal :
    (∑ q ∈ (Finset.Ioc 1 Qmax).attach,
        (((primitiveDirichletCharacterSet q.val).filter fun χ =>
              V ≤
                Complex.normSq
                  (∑ j ∈ Finset.range J,
                    ∑ n ∈ Finset.Ico (N * 2 ^ j) (N * 2 ^ (j + 1)),
                      a n * χ (n : ZMod q.val))).card :
          ℝ)) ≤
      ∑ j ∈ Finset.range J,
        ∑ q ∈ (Finset.Ioc 1 Qmax).attach,
          (((primitiveDirichletCharacterSet q.val).filter fun χ =>
                V / (J : ℝ) ^ 2 ≤
                  Complex.normSq
                    (∑ n ∈ Finset.Ico (N * 2 ^ j) (N * 2 ^ (j + 1)),
                      a n * χ (n : ZMod q.val))).card :
            ℝ) := by
    exact_mod_cast hcount
  have hthreshold : 0 ≤ V / (J : ℝ) ^ 2 := div_nonneg hV.le (sq_nonneg _)
  calc
    _ ≤
        (∑ j ∈ Finset.range J,
            ∑ q ∈ (Finset.Ioc 1 Qmax).attach,
              (((primitiveDirichletCharacterSet q.val).filter fun χ =>
                    V / (J : ℝ) ^ 2 ≤
                      Complex.normSq
                        (∑ n ∈ Finset.Ico (N * 2 ^ j) (N * 2 ^ (j + 1)),
                          a n * χ (n : ZMod q.val))).card :
                ℝ)) *
          (V / (J : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right hcountReal hthreshold
    _ =
        ∑ j ∈ Finset.range J,
          ((∑ q ∈ (Finset.Ioc 1 Qmax).attach,
              (((primitiveDirichletCharacterSet q.val).filter fun χ =>
                    V / (J : ℝ) ^ 2 ≤
                      Complex.normSq
                        (∑ n ∈ Finset.Ico (N * 2 ^ j) (N * 2 ^ (j + 1)),
                          a n * χ (n : ZMod q.val))).card :
                ℝ)) *
            (V / (J : ℝ) ^ 2)) :=
      by rw [Finset.sum_mul]
    _ ≤ _ := primitiveCharacterFamily_dyadic_blockCount_mul_le Qmax N J hQ hN a (V / (J : ℝ) ^ 2)

/--
Inputs: a modulus cutoff, a finite dyadic range, a derivative order, a complex point with
nonnegative real part, and a positive total squared-norm threshold.

Claim: the total large-value count for the differentiated Euler sum, multiplied by `V / J²`, is
bounded by an explicit sum of endpoint-weight estimates for the dyadic blocks.

Proof: reduce the total event to blockwise events and apply
`primitiveCharacterLargeValueCount_mul_le_euler_dyadic` at each block scale.

Role: gives an explicit finite dyadic-tail large-value bound over all primitive characters and
moduli up to `Qmax`.
-/
theorem primitiveCharacterFamily_euler_dyadic_sumLargeCount_mul_le (Qmax N J r : ℕ) (hQ : 2 ≤ Qmax)
    (hN : Qmax * Qmax ≤ N) {s : ℂ} (hs : 0 ≤ s.re) (V : ℝ) (hJ : 0 < J) (hV : 0 < V) :
    (∑ q ∈ (Finset.Ioc 1 Qmax).attach,
          (((primitiveDirichletCharacterSet q.val).filter fun χ =>
                V ≤
                  Complex.normSq
                    (∑ j ∈ Finset.range J,
                      ∑ n ∈ Finset.Ico (N * 2 ^ j) (N * 2 ^ (j + 1)),
                        LSeries.term
                            (LSeries.logMul^[r]
                              (fun k : ℕ ↦ (ArithmeticFunction.vonMangoldt k : ℂ)))
                            s n *
                          χ (n : ZMod q.val))).card :
            ℝ)) *
        (V / (J : ℝ) ^ 2) ≤
      ∑ j ∈ Finset.range J,
        (21 / 2 : ℝ) * (Qmax : ℝ) * ((N * 2 ^ j : ℕ) : ℝ) * ((N * 2 ^ j : ℕ) : ℝ) *
          ((Real.log (2 * (N * 2 ^ j)) ^ (r + 1) / ((N * 2 ^ j : ℕ) : ℝ) ^ s.re) ^ 2) := by
  let a : ℕ → ℂ := fun n =>
    LSeries.term (LSeries.logMul^[r] (fun k : ℕ ↦ (ArithmeticFunction.vonMangoldt k : ℂ))) s n
  have hcount := primitiveCharacterFamily_dyadic_largeCount_le_sum_block_counts Qmax J N a V hJ hV
  have hcountReal :
    (∑ q ∈ (Finset.Ioc 1 Qmax).attach,
        (((primitiveDirichletCharacterSet q.val).filter fun χ =>
              V ≤
                Complex.normSq
                  (∑ j ∈ Finset.range J,
                    ∑ n ∈ Finset.Ico (N * 2 ^ j) (N * 2 ^ (j + 1)),
                      a n * χ (n : ZMod q.val))).card :
          ℝ)) ≤
      ∑ j ∈ Finset.range J,
        ∑ q ∈ (Finset.Ioc 1 Qmax).attach,
          (((primitiveDirichletCharacterSet q.val).filter fun χ =>
                V / (J : ℝ) ^ 2 ≤
                  Complex.normSq
                    (∑ n ∈ Finset.Ico (N * 2 ^ j) (N * 2 ^ (j + 1)),
                      a n * χ (n : ZMod q.val))).card :
            ℝ) := by
    exact_mod_cast hcount
  have hthreshold : 0 ≤ V / (J : ℝ) ^ 2 := div_nonneg hV.le (sq_nonneg _)
  calc
    _ ≤
        (∑ j ∈ Finset.range J,
            ∑ q ∈ (Finset.Ioc 1 Qmax).attach,
              (((primitiveDirichletCharacterSet q.val).filter fun χ =>
                    V / (J : ℝ) ^ 2 ≤
                      Complex.normSq
                        (∑ n ∈ Finset.Ico (N * 2 ^ j) (N * 2 ^ (j + 1)),
                          a n * χ (n : ZMod q.val))).card :
                ℝ)) *
          (V / (J : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right hcountReal hthreshold
    _ =
        ∑ j ∈ Finset.range J,
          ((∑ q ∈ (Finset.Ioc 1 Qmax).attach,
              (((primitiveDirichletCharacterSet q.val).filter fun χ =>
                    V / (J : ℝ) ^ 2 ≤
                      Complex.normSq
                        (∑ n ∈ Finset.Ico (N * 2 ^ j) (N * 2 ^ (j + 1)),
                          a n * χ (n : ZMod q.val))).card :
                ℝ)) *
            (V / (J : ℝ) ^ 2)) :=
      by rw [Finset.sum_mul]
    _ ≤
        ∑ j ∈ Finset.range J,
          (21 / 2 : ℝ) * (Qmax : ℝ) * ((N * 2 ^ j : ℕ) : ℝ) * ((N * 2 ^ j : ℕ) : ℝ) *
            ((Real.log (2 * (N * 2 ^ j)) ^ (r + 1) / ((N * 2 ^ j : ℕ) : ℝ) ^ s.re) ^ 2) :=
      by
      apply Finset.sum_le_sum
      intro j hj
      have hpow : 1 ≤ 2 ^ j := Nat.one_le_pow j 2 (by decide)
      have hNj : Qmax * Qmax ≤ N * 2 ^ j := by
        calc
          Qmax * Qmax ≤ N := hN
          _ = N * 1 := by simp only [Nat.mul_one]
          _ ≤ N * 2 ^ j := Nat.mul_le_mul_left N hpow
      have hinterval :
        Finset.Ico (N * 2 ^ j) (N * 2 ^ (j + 1)) = Finset.Ico (N * 2 ^ j) (2 * (N * 2 ^ j)) := by
        congr 1
        rw [Nat.pow_succ]
        ring
      simpa only [a, ← hinterval, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
        primitiveCharacterLargeValueCount_mul_le_euler_dyadic Qmax (N * 2 ^ j) r hQ hNj hs
          (V / (J : ℝ) ^ 2)

/--
Inputs: the finite Euler dyadic range, positive block weights summing to one, and a positive total
squared-norm threshold.

Claim: the total primitive-character large-value count multiplied by `V` is bounded by the sum of
the explicit block estimates divided by `w_j²`.

Proof: allocate threshold `V * w_j²` to each block, apply the Euler large-value estimate, and divide
by the positive squared weight.

Role: removes the uniform `J²` loss and leaves a weighted endpoint sum to optimize for zero-density
applications.
-/
theorem primitiveCharacterFamily_euler_dyadic_weightedSumLargeCount_mul_le (Qmax N J r : ℕ)
    (hQ : 2 ≤ Qmax) (hN : Qmax * Qmax ≤ N) {s : ℂ} (hs : 0 ≤ s.re) (w : ℕ → ℝ) (V : ℝ) (hJ : 0 < J)
    (hV : 0 < V) (hwpos : ∀ j ∈ Finset.range J, 0 < w j) (hwSum : ∑ j ∈ Finset.range J, w j = 1) :
    (∑ q ∈ (Finset.Ioc 1 Qmax).attach,
          (((primitiveDirichletCharacterSet q.val).filter fun χ =>
                V ≤
                  Complex.normSq
                    (∑ j ∈ Finset.range J,
                      ∑ n ∈ Finset.Ico (N * 2 ^ j) (N * 2 ^ (j + 1)),
                        LSeries.term
                            (LSeries.logMul^[r]
                              (fun k : ℕ ↦ (ArithmeticFunction.vonMangoldt k : ℂ)))
                            s n *
                          χ (n : ZMod q.val))).card :
            ℝ)) *
        V ≤
      ∑ j ∈ Finset.range J,
        ((21 / 2 : ℝ) * (Qmax : ℝ) * ((N * 2 ^ j : ℕ) : ℝ) * ((N * 2 ^ j : ℕ) : ℝ) *
            ((Real.log (2 * (N * 2 ^ j)) ^ (r + 1) / ((N * 2 ^ j : ℕ) : ℝ) ^ s.re) ^ 2) /
          (w j) ^ 2) := by
  let a : ℕ → ℂ := fun n =>
    LSeries.term (LSeries.logMul^[r] (fun k : ℕ ↦ (ArithmeticFunction.vonMangoldt k : ℂ))) s n
  have hcount :=
    primitiveCharacterFamily_dyadic_weightedLargeCount_le_sum_block_counts Qmax J N a w V hJ hV
      hwpos hwSum
  have hcountReal :
    (∑ q ∈ (Finset.Ioc 1 Qmax).attach,
        (((primitiveDirichletCharacterSet q.val).filter fun χ =>
              V ≤
                Complex.normSq
                  (∑ j ∈ Finset.range J,
                    ∑ n ∈ Finset.Ico (N * 2 ^ j) (N * 2 ^ (j + 1)),
                      a n * χ (n : ZMod q.val))).card :
          ℝ)) ≤
      ∑ j ∈ Finset.range J,
        ∑ q ∈ (Finset.Ioc 1 Qmax).attach,
          (((primitiveDirichletCharacterSet q.val).filter fun χ =>
                V * (w j) ^ 2 ≤
                  Complex.normSq
                    (∑ n ∈ Finset.Ico (N * 2 ^ j) (N * 2 ^ (j + 1)),
                      a n * χ (n : ZMod q.val))).card :
            ℝ) := by
    exact_mod_cast hcount
  calc
    _ ≤
        (∑ j ∈ Finset.range J,
            ∑ q ∈ (Finset.Ioc 1 Qmax).attach,
              (((primitiveDirichletCharacterSet q.val).filter fun χ =>
                    V * (w j) ^ 2 ≤
                      Complex.normSq
                        (∑ n ∈ Finset.Ico (N * 2 ^ j) (N * 2 ^ (j + 1)),
                          a n * χ (n : ZMod q.val))).card :
                ℝ)) *
          V :=
      mul_le_mul_of_nonneg_right hcountReal hV.le
    _ =
        ∑ j ∈ Finset.range J,
          ((∑ q ∈ (Finset.Ioc 1 Qmax).attach,
              (((primitiveDirichletCharacterSet q.val).filter fun χ =>
                    V * (w j) ^ 2 ≤
                      Complex.normSq
                        (∑ n ∈ Finset.Ico (N * 2 ^ j) (N * 2 ^ (j + 1)),
                          a n * χ (n : ZMod q.val))).card :
                ℝ)) *
            V) :=
      by rw [Finset.sum_mul]
    _ ≤
        ∑ j ∈ Finset.range J,
          ((21 / 2 : ℝ) * (Qmax : ℝ) * ((N * 2 ^ j : ℕ) : ℝ) * ((N * 2 ^ j : ℕ) : ℝ) *
              ((Real.log (2 * (N * 2 ^ j)) ^ (r + 1) / ((N * 2 ^ j : ℕ) : ℝ) ^ s.re) ^ 2) /
            (w j) ^ 2) :=
      by
      apply Finset.sum_le_sum
      intro j hj
      have hpow : 1 ≤ 2 ^ j := Nat.one_le_pow j 2 (by decide)
      have hNj : Qmax * Qmax ≤ N * 2 ^ j := by
        calc
          Qmax * Qmax ≤ N := hN
          _ = N * 1 := by simp only [Nat.mul_one]
          _ ≤ N * 2 ^ j := Nat.mul_le_mul_left N hpow
      have hinterval :
        Finset.Ico (N * 2 ^ j) (N * 2 ^ (j + 1)) = Finset.Ico (N * 2 ^ j) (2 * (N * 2 ^ j)) := by
        congr 1
        rw [Nat.pow_succ]
        ring
      have hblock :=
        primitiveCharacterLargeValueCount_mul_le_euler_dyadic Qmax (N * 2 ^ j) r hQ hNj hs
          (V * (w j) ^ 2)
      have hblock' :
        (∑ q ∈ (Finset.Ioc 1 Qmax).attach,
              (((primitiveDirichletCharacterSet q.val).filter fun χ =>
                    V * (w j) ^ 2 ≤
                      Complex.normSq
                        (∑ n ∈ Finset.Ico (N * 2 ^ j) (N * 2 ^ (j + 1)),
                          a n * χ (n : ZMod q.val))).card :
                ℝ)) *
            (V * (w j) ^ 2) ≤
          (21 / 2 : ℝ) * (Qmax : ℝ) * ((N * 2 ^ j : ℕ) : ℝ) * ((N * 2 ^ j : ℕ) : ℝ) *
            ((Real.log (2 * (N * 2 ^ j)) ^ (r + 1) / ((N * 2 ^ j : ℕ) : ℝ) ^ s.re) ^ 2) := by
        simpa only [a, ← hinterval, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hblock
      have hw2 : 0 < (w j) ^ 2 := sq_pos_of_pos (hwpos j hj)
      apply (le_div_iff₀ hw2).2
      calc
        _ =
            (∑ q ∈ (Finset.Ioc 1 Qmax).attach,
                (((primitiveDirichletCharacterSet q.val).filter fun χ =>
                      V * (w j) ^ 2 ≤
                        Complex.normSq
                          (∑ n ∈ Finset.Ico (N * 2 ^ j) (N * 2 ^ (j + 1)),
                            a n * χ (n : ZMod q.val))).card :
                  ℝ)) *
              (V * (w j) ^ 2) :=
          by ring
        _ ≤ _ := hblock'

/-!
The following identity gives the exact endpoint cost for normalized square-root weights.
-/

/--
Inputs: a finite set of indices and a real cost at each index.

Definition: assigns each index the square root of its cost divided by the sum of all square roots
on the finite set. Outside the set, the same formula is still defined.

Role: these normalized weights distribute the large-value threshold according to endpoint costs.
-/
noncomputable def normalizedSqrtWeights {ι : Type*} [DecidableEq ι] (s : Finset ι) (b : ι → ℝ) :
    ι → ℝ := fun i => Real.sqrt (b i) / (∑ k ∈ s, Real.sqrt (b k))

/-- Positive costs and a positive normalizing sum make every in-set weight positive. -/
theorem normalizedSqrtWeights_pos {ι : Type*} [DecidableEq ι] (s : Finset ι) (b : ι → ℝ) (i : ι)
    (hi : i ∈ s) (hb : ∀ i ∈ s, 0 < b i) (hS : 0 < ∑ k ∈ s, Real.sqrt (b k)) :
    0 < normalizedSqrtWeights s b i := by
  unfold normalizedSqrtWeights
  exact div_pos (Real.sqrt_pos.2 (hb i hi)) hS

/-- The normalized square-root weights sum to one on their finite index set. -/
theorem normalizedSqrtWeights_sum_one {ι : Type*} [DecidableEq ι] (s : Finset ι) (b : ι → ℝ)
    (hS : 0 < ∑ k ∈ s, Real.sqrt (b k)) : ∑ i ∈ s, normalizedSqrtWeights s b i = 1 := by
  unfold normalizedSqrtWeights
  let S := ∑ k ∈ s, Real.sqrt (b k)
  have hSne : S ≠ 0 := ne_of_gt hS
  calc
    _ = (∑ i ∈ s, Real.sqrt (b i)) * S⁻¹ := by
      simp only [div_eq_mul_inv]
      rw [Finset.sum_mul]
    _ = 1 := by
      dsimp only [S]
      field_simp

/--
Inputs: a finite index set, a positive cost at each index, and a real multiplier.

Claim: normalizing the square roots of the costs gives an exact expression for the weighted cost
sum, namely the multiplier times the square of the sum of square roots times the sum of costs.

Proof: each term simplifies using `(sqrt b)² = b`, after which finite-sum distributivity factors
out the common normalization.

Role: provides an explicit weight choice for optimizing the endpoint sum in the preceding
large-value estimate.
-/
theorem normalized_sqrt_weights_cost {ι : Type*} [DecidableEq ι] (s : Finset ι) (b : ι → ℝ) (K : ℝ)
    (hb : ∀ i ∈ s, 0 < b i) (hS : 0 < ∑ i ∈ s, Real.sqrt (b i)) :
    let S := ∑ i ∈ s, Real.sqrt (b i)
    let w := normalizedSqrtWeights s b
    (∑ i ∈ s, K * (b i) ^ 2 / (w i) ^ 2) = K * S ^ 2 * (∑ i ∈ s, b i) := by
  dsimp only
  let S := ∑ i ∈ s, Real.sqrt (b i)
  let w := fun i => Real.sqrt (b i) / S
  have hS' : 0 < S := hS
  have hterm (i : ι) (hi : i ∈ s) : K * (b i) ^ 2 / (w i) ^ 2 = K * b i * S ^ 2 := by
    dsimp only [w, normalizedSqrtWeights]
    rw [div_pow, Real.sq_sqrt (le_of_lt (hb i hi))]
    have hSne : S ≠ 0 := ne_of_gt hS'
    field_simp
  calc
    _ = ∑ i ∈ s, K * b i * S ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hterm i hi
    _ = ∑ i ∈ s, (K * S ^ 2) * b i := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = K * S ^ 2 * (∑ i ∈ s, b i) := by
      symm
      exact Finset.mul_sum s b (K * S ^ 2)

/--
Inputs: a base point `N`, a derivative order, an exponent, and a dyadic index.

Definition: the square root of the explicit endpoint coefficient after removing its common
`(21/2) * Q` factor.

Role: this positive quantity determines the normalized square-root allocation for the finite
Euler-tail estimate.
-/
noncomputable def endpointCostBase (N r : ℕ) (σ : ℝ) (j : ℕ) : ℝ :=
  ((N * 2 ^ j : ℕ) : ℝ) * (Real.log (2 * (N * 2 ^ j)) ^ (r + 1) / ((N * 2 ^ j : ℕ) : ℝ) ^ σ)

/-- The endpoint cost base is positive whenever the initial scale is at least two. -/
theorem endpointCostBase_pos (N r j : ℕ) (σ : ℝ) (hN : 2 ≤ N) : 0 < endpointCostBase N r σ j := by
  unfold endpointCostBase
  have hj : 1 ≤ 2 ^ j := Nat.one_le_pow j 2 (by decide)
  have hM : 2 ≤ N * 2 ^ j := by
    calc
      2 ≤ N := hN
      _ = N * 1 := by simp only [Nat.mul_one]
      _ ≤ N * 2 ^ j := Nat.mul_le_mul_left N hj
  have hMpos : (0 : ℝ) < (N * 2 ^ j : ℕ) := by
    exact_mod_cast Nat.lt_of_lt_of_le (by decide : 0 < 2) hM
  have hargNat : 1 < 2 * (N * 2 ^ j) := by
    have hfour : 4 ≤ 2 * (N * 2 ^ j) := Nat.mul_le_mul_left 2 hM
    exact lt_of_lt_of_le (by norm_num only) hfour
  have harg : (1 : ℝ) < 2 * (N * 2 ^ j) := by exact_mod_cast hargNat
  have hlog : 0 < Real.log (2 * (N * 2 ^ j)) := Real.log_pos harg
  have hden : 0 < ((N * 2 ^ j : ℕ) : ℝ) ^ σ := Real.rpow_pos_of_pos hMpos σ
  exact mul_pos hMpos (div_pos (pow_pos hlog _) hden)

/--
Inputs: a modulus bound, a base point, a derivative order, an exponent, and a dyadic index.

Claim: each endpoint coefficient in the Euler large-value estimate is the common factor
`(21/2) * Q` times the square of `endpointCostBase`.

Proof: unfold the endpoint cost and normalize the products and squares.

Role: puts the weighted large-value estimate into the exact form optimized by
`normalized_sqrt_weights_cost`.
-/
theorem endpoint_cost_factorization (Q N r j : ℕ) (σ : ℝ) :
    (21 / 2 : ℝ) * (Q : ℝ) * ((N * 2 ^ j : ℕ) : ℝ) * ((N * 2 ^ j : ℕ) : ℝ) *
        ((Real.log (2 * (N * 2 ^ j)) ^ (r + 1) / ((N * 2 ^ j : ℕ) : ℝ) ^ σ) ^ 2) =
      ((21 / 2 : ℝ) * (Q : ℝ)) * (endpointCostBase N r σ j) ^ 2 := by
  unfold endpointCostBase
  ring

/-- The square-root endpoint weights sum to one on every nonempty dyadic range. -/
noncomputable def endpointCostWeights (N r J : ℕ) (σ : ℝ) : ℕ → ℝ :=
  normalizedSqrtWeights (Finset.range J) (endpointCostBase N r σ)

/-- Positive endpoint costs give positive normalized weights for each dyadic block. -/
theorem endpointCostWeights_pos (N r J j : ℕ) (σ : ℝ) (hN : 2 ≤ N) (hj : j ∈ Finset.range J)
    (hS : 0 < ∑ k ∈ Finset.range J, Real.sqrt (endpointCostBase N r σ k)) :
    0 < endpointCostWeights N r J σ j := by
  exact
    normalizedSqrtWeights_pos (Finset.range J) (endpointCostBase N r σ) j hj
      (fun k hk => endpointCostBase_pos N r k σ hN) hS

/-- The normalized endpoint weights sum to one when the dyadic range is nonempty. -/
theorem endpointCostWeights_sum_one (N r J : ℕ) (σ : ℝ)
    (hS : 0 < ∑ k ∈ Finset.range J, Real.sqrt (endpointCostBase N r σ k)) :
    ∑ j ∈ Finset.range J, endpointCostWeights N r J σ j = 1 := by
  exact normalizedSqrtWeights_sum_one (Finset.range J) (endpointCostBase N r σ) hS

/-- Positive initial scale and nonempty dyadic range provide a positive normalizing sum. -/
theorem endpointCostWeights_normalizer_pos (N r J : ℕ) (σ : ℝ) (hN : 2 ≤ N) (hJ : 0 < J) :
    0 < ∑ j ∈ Finset.range J, Real.sqrt (endpointCostBase N r σ j) := by
  apply Finset.sum_pos
  · intro j hj
    exact Real.sqrt_pos.2 (endpointCostBase_pos N r j σ hN)
  · exact ⟨0, Finset.mem_range.mpr hJ⟩

/--
Inputs: a modulus bound, a dyadic range, a derivative order, an exponent, and an initial scale
at least two, and a positive dyadic range.

Claim: the explicit endpoint-cost sum divided by the squared normalized endpoint weights equals
its optimized form, `(21/2) * Q` times the squared square-root sum times the cost sum.

Proof: factor each endpoint coefficient as a square and apply
`normalized_sqrt_weights_cost`.

Role: gives the concrete optimized right-hand side for the weighted Euler large-value theorem.
-/
theorem endpoint_weighted_cost_eq (Q N r J : ℕ) (σ : ℝ) (hN : 2 ≤ N) (hJ : 0 < J) :
    ∑ j ∈ Finset.range J,
        ((21 / 2 : ℝ) * (Q : ℝ) * ((N * 2 ^ j : ℕ) : ℝ) * ((N * 2 ^ j : ℕ) : ℝ) *
            ((Real.log (2 * (N * 2 ^ j)) ^ (r + 1) / ((N * 2 ^ j : ℕ) : ℝ) ^ σ) ^ 2) /
          (endpointCostWeights N r J σ j) ^ 2) =
      ((21 / 2 : ℝ) * (Q : ℝ)) * (∑ j ∈ Finset.range J, Real.sqrt (endpointCostBase N r σ j)) ^ 2 *
        (∑ j ∈ Finset.range J, endpointCostBase N r σ j) := by
  have hS := endpointCostWeights_normalizer_pos N r J σ hN hJ
  have hbase :=
    normalized_sqrt_weights_cost (Finset.range J) (endpointCostBase N r σ) ((21 / 2 : ℝ) * (Q : ℝ))
      (fun j hj => endpointCostBase_pos N r j σ hN) hS
  have hfactor :
    (∑ j ∈ Finset.range J,
        ((21 / 2 : ℝ) * (Q : ℝ) * ((N * 2 ^ j : ℕ) : ℝ) * ((N * 2 ^ j : ℕ) : ℝ) *
            ((Real.log (2 * (N * 2 ^ j)) ^ (r + 1) / ((N * 2 ^ j : ℕ) : ℝ) ^ σ) ^ 2) /
          (endpointCostWeights N r J σ j) ^ 2)) =
      ∑ j ∈ Finset.range J,
        ((21 / 2 : ℝ) * (Q : ℝ) * (endpointCostBase N r σ j) ^ 2 /
          (endpointCostWeights N r J σ j) ^ 2) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [endpoint_cost_factorization]
  simpa only [endpointCostWeights] using hfactor.trans hbase

/--
Inputs: a modulus cutoff, a dyadic tail range, a derivative order, and a complex point with
nonnegative real part.

Claim: the finite Euler-tail large-value count, multiplied by its threshold, is bounded by the
explicit endpoint cost after optimizing the block thresholds with normalized square-root weights.

Proof: instantiate the weighted block estimate with `endpointCostWeights`, then rewrite its right
side using `endpoint_weighted_cost_eq`.

Role: gives a direct optimized finite-tail estimate for later zero-detection arguments.
-/
theorem primitiveCharacterFamily_euler_dyadic_sqrtWeightedSumLargeCount_mul_le (Qmax N J r : ℕ)
    (hQ : 2 ≤ Qmax) (hN : Qmax * Qmax ≤ N) {s : ℂ} (hs : 0 ≤ s.re) (V : ℝ) (hJ : 0 < J)
    (hV : 0 < V) :
    (∑ q ∈ (Finset.Ioc 1 Qmax).attach,
          (((primitiveDirichletCharacterSet q.val).filter fun χ =>
                V ≤
                  Complex.normSq
                    (∑ j ∈ Finset.range J,
                      ∑ n ∈ Finset.Ico (N * 2 ^ j) (N * 2 ^ (j + 1)),
                        LSeries.term
                            (LSeries.logMul^[r]
                              (fun k : ℕ ↦ (ArithmeticFunction.vonMangoldt k : ℂ)))
                            s n *
                          χ (n : ZMod q.val))).card :
            ℝ)) *
        V ≤
      ((21 / 2 : ℝ) * (Qmax : ℝ)) *
        (∑ j ∈ Finset.range J, Real.sqrt (endpointCostBase N r s.re j)) ^ 2 *
        (∑ j ∈ Finset.range J, endpointCostBase N r s.re j) := by
  have hone : 1 ≤ Qmax := le_trans (by decide) hQ
  have hNbase : 2 ≤ N := by
    calc
      2 = 2 * 1 := by norm_num only
      _ ≤ 2 * Qmax := Nat.mul_le_mul_left 2 hone
      _ ≤ Qmax * Qmax := Nat.mul_le_mul_right Qmax hQ
      _ ≤ N := hN
  have hS := endpointCostWeights_normalizer_pos N r J s.re hNbase hJ
  have hwpos : ∀ j ∈ Finset.range J, 0 < endpointCostWeights N r J s.re j := by
    intro j hj
    exact endpointCostWeights_pos N r J j s.re hNbase hj hS
  have hwSum := endpointCostWeights_sum_one N r J s.re hS
  calc
    _ ≤
        ∑ j ∈ Finset.range J,
          ((21 / 2 : ℝ) * (Qmax : ℝ) * ((N * 2 ^ j : ℕ) : ℝ) * ((N * 2 ^ j : ℕ) : ℝ) *
              ((Real.log (2 * (N * 2 ^ j)) ^ (r + 1) / ((N * 2 ^ j : ℕ) : ℝ) ^ s.re) ^ 2) /
            (endpointCostWeights N r J s.re j) ^ 2) :=
      primitiveCharacterFamily_euler_dyadic_weightedSumLargeCount_mul_le Qmax N J r hQ hN hs
        (endpointCostWeights N r J s.re) V hJ hV hwpos hwSum
    _ =
        ((21 / 2 : ℝ) * (Qmax : ℝ)) *
          (∑ j ∈ Finset.range J, Real.sqrt (endpointCostBase N r s.re j)) ^ 2 *
          (∑ j ∈ Finset.range J, endpointCostBase N r s.re j) :=
      endpoint_weighted_cost_eq Qmax N r J s.re hNbase hJ

/--
Inputs: a sequence of complex coefficients, a derivative order, and an index.

Claim: applying `logMul` repeatedly to coefficients twisted by a character value equals twisting
the corresponding untwisted coefficients by the same value.

Proof: induct on the number of iterations and use commutativity of complex multiplication.

Role: identifies differentiated twisted Euler coefficients with a Dirichlet polynomial whose
coefficients are independent of the character.
-/
theorem twist_iterate_logMul_identity (χ : ℕ → ℂ) (n k : ℕ) :
    (LSeries.logMul^[n] (fun j : ℕ => χ j * (ArithmeticFunction.vonMangoldt j : ℂ))) k =
      χ k * (LSeries.logMul^[n] (fun j : ℕ => (ArithmeticFunction.vonMangoldt j : ℂ))) k := by
  induction n with
  | zero => rfl
  | succ n
    ih =>
    change
      (LSeries.logMul^[n.succ] (fun j : ℕ => χ j * (ArithmeticFunction.vonMangoldt j : ℂ))) k =
        χ k * (LSeries.logMul^[n.succ] (fun j : ℕ => (ArithmeticFunction.vonMangoldt j : ℂ))) k
    rw [Function.iterate_succ_apply']
    rw [Function.iterate_succ_apply']
    simp only [LSeries.logMul, ih]
    ring

/-- The L-series term operation preserves the coefficient twist under `logMul` iteration. -/
theorem term_twist_iterate_identity (χ : ℕ → ℂ) (n : ℕ) (s : ℂ) (k : ℕ) :
    LSeries.term (LSeries.logMul^[n] (fun j : ℕ => χ j * (ArithmeticFunction.vonMangoldt j : ℂ))) s
        k =
      LSeries.term (LSeries.logMul^[n] (fun j : ℕ => (ArithmeticFunction.vonMangoldt j : ℂ))) s k *
        χ k := by
  by_cases hk : k = 0
  · subst k
    simp only [LSeries.term_zero, zero_mul]
  · simp only [LSeries.term, ite_eq_right hk]
    rw [twist_iterate_logMul_identity χ n k]
    ring

/--
Inputs: a lower bound for a complex value and an approximation error at most half that bound.

Claim: the approximating complex value has squared norm at least one quarter of the squared lower
bound.

Proof: apply the triangle inequality to the approximation identity, remove the unit factor
`(-1)^n`, and square the resulting nonnegative norm inequality.

Role: turns a large logarithmic derivative into a large finite Dirichlet polynomial value.
-/
theorem normSq_lower_from_approximation {D P : ℂ} {n : ℕ} {R : ℝ} (hD : R ≤ ‖D‖)
    (hE : ‖D + (-1 : ℂ) ^ n * P‖ ≤ R / 2) (hR : 0 ≤ R) : (R / 2) ^ 2 ≤ Complex.normSq P := by
  have hdecomp : D = (D + (-1 : ℂ) ^ n * P) + -((-1 : ℂ) ^ n * P) := by ring
  have htriangle : ‖D‖ ≤ ‖D + (-1 : ℂ) ^ n * P‖ + ‖(-1 : ℂ) ^ n * P‖ := by
    calc
      _ = ‖(D + (-1 : ℂ) ^ n * P) + -((-1 : ℂ) ^ n * P)‖ := by congr 1
      _ ≤ ‖D + (-1 : ℂ) ^ n * P‖ + ‖-((-1 : ℂ) ^ n * P)‖ := norm_add_le _ _
      _ = _ := by rw [norm_neg]
  have hP : R / 2 ≤ ‖(-1 : ℂ) ^ n * P‖ := by linarith only [hD, hE, htriangle]
  have hunit : ‖(-1 : ℂ) ^ n‖ = 1 := by simp only [norm_pow, norm_neg, norm_one, one_pow]
  rw [norm_mul, hunit, one_mul] at hP
  rw [Complex.normSq_eq_norm_sq]
  apply (sq_le_sq₀ (div_nonneg hR (by norm_num)) (norm_nonneg P)).2
  exact hP

/--
Purpose: the primitive characters modulo `q` whose `n`th logarithmic derivative is large at `s`.

Definition: filters the primitive-character set by a norm threshold. The proof-level nonzero
modulus instance is derived from `1 < q`.

Inputs: a modulus with `1 < q`, a derivative order, a complex point, and a real threshold.

Role: packages the characters counted by the derivative-to-polynomial estimate below.
-/
noncomputable def primitiveCharacterDerivativeLargeSet (q : ℕ) (hq : 1 < q) (n : ℕ) (s : ℂ)
    (R : ℝ) : Finset (DirichletCharacter ℂ q) := by
  classical
  let hqne : NeZero q := ⟨Nat.ne_of_gt (lt_trans Nat.zero_lt_one hq)⟩
  exact
    (primitiveDirichletCharacterSet q).filter fun χ =>
      R ≤ ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) s‖

/--
Inputs: a primitive character and a strict lower bound for a scaled logarithmic-derivative value.
Claim: the character belongs to the derivative large set at some point of a finite rational-height
grid.
Proof: select the grid from the strict margin, transfer the bound to an unscaled derivative, and
unfold the primitive-character large set.
Role: supplies the character-level witness consumed by the finite-grid family count.
-/
theorem mem_primitiveCharacterDerivativeLargeSet_of_strict_scaled_bound (q : ℕ) [NeZero q]
    (hq : 1 < q) (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) {σ t : ℝ}
    (hσ : 1 < σ) {T : ℕ} (htlo : -(T : ℝ) ≤ t) (hthi : t ≤ T) (n : ℕ) (Rscale : ℝ)
    (hRscale : 0 < Rscale) (c : ℂ) (hc : c = (σ : ℂ) + Complex.I * (t : ℂ)) (L threshold : ℝ)
    (hscale :
      iteratedDeriv n
          (logDeriv (fun z : ℂ => DirichletCharacter.LFunction χ (z * (Rscale : ℂ) + c))) 0 =
        (Rscale : ℂ) ^ (n + 1) * iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) c)
    (hbound :
      L ≤
        ‖(iteratedDeriv n
            (logDeriv (fun z : ℂ => DirichletCharacter.LFunction χ (z * (Rscale : ℂ) + c))) 0)‖)
    (hstrict : threshold < L / Rscale ^ (n + 1)) :
    ∃ Mgrid : ℕ,
      0 < Mgrid ∧
        ∃ m : ℤ,
          m ∈ Finset.Icc (-(T * Mgrid : ℤ)) (T * Mgrid : ℤ) ∧
            χ ∈
              primitiveCharacterDerivativeLargeSet q hq n
                ((σ : ℂ) + Complex.I * (((m : ℝ) / (Mgrid : ℝ) : ℝ) : ℂ)) threshold := by
  obtain ⟨Mgrid, hMgrid, m, hm, hlarge⟩ :=
    exists_rational_height_large_of_strict_scaled_derivative_bound χ hχ hσ htlo hthi n Rscale
      hRscale c hc L threshold hscale hbound hstrict
  have hχmem : χ ∈ primitiveDirichletCharacterSet q := by
    simp only [primitiveDirichletCharacterSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hprim
  refine ⟨Mgrid, hMgrid, m, hm, ?_⟩
  simpa only [primitiveCharacterDerivativeLargeSet, Finset.mem_filter] using And.intro hχmem hlarge

/--
Inputs: a primitive nonprincipal character, a completed-function zero in a bounded height window,
and a requested minimum detector order.
Claim: some order in the local block and some point of a finite rational-height grid have a
logarithmic-derivative norm at least half the explicit exponential detector threshold.
Proof: apply the positive ordinary-derivative detector, halve its normalized lower bound, and
transfer the strict margin to the grid.
Role: connects zero detection to the finite-grid large-value family.
-/
theorem exists_character_derivative_large_grid_of_completed_zero {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hq : 2 ≤ q) (hχ : χ ≠ 1) (hp : χ.IsPrimitive) (hinv : χ⁻¹ ≠ 1)
    {η : ℝ} (hη : 0 < η) (hηsmall : η ≤ 1 / 1288) (Krequested : ℕ) (hKrequested : 2 ≤ Krequested)
    {ρ : ℂ} (hρre : |ρ.re - 1| ≤ η) (hzero : DirichletCharacter.completedLFunction χ ρ = 0)
    (hc : DirichletCharacter.completedLFunction χ (((1 + η : ℝ) : ℂ) + Complex.I * (ρ.im : ℂ)) ≠ 0)
    (hscale : η * Real.log ((q : ℝ) * (|ρ.im| + 3)) ≤ 3) {T : ℕ} (hheight : |ρ.im| ≤ T) :
    ∃ massConstA massConstB : ℝ,
      0 < massConstA ∧
        0 < massConstB ∧
        ∃ Kmin C K m n M : ℕ,
          ∃ j : ℤ,
            Krequested ≤ K ∧
              K ≤ completedGenusRemoteTailUniformCutoff q η ρ.im ((C : ℝ) + 1) Kmin ∧
              K ≤ max completedGenusRemoteTailUniformOrderBound Kmin ∧
              Kmin ≤ K ∧
              C =
                Nat.ceil
                  (completedZeroLocalLogBoundConstant *
                    (1 + 644 * η * Real.log ((q : ℝ) * (|ρ.im| + 3)))) ∧
              2 ≤ K ∧
              0 < n ∧
              n + 1 = m ∧
              K ≤ m ∧
              m ≤ K * completedLFunctionNearOneDetectorMultiplicityCap ∧
              j ∈ Finset.Icc (-(T * M : ℤ)) (T * M : ℤ) ∧
              (Real.exp (-(ordinaryLFunctionNearOneDetectorExponent * (K : ℝ))) /
                  ((η ^ (n + 1) / (n.factorial : ℝ)) * 2)) ≤
                ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ))
                    (((1 + η : ℝ) : ℂ) + Complex.I * (((j : ℝ) / (M : ℝ) : ℝ) : ℂ))‖ := by
  have hcre : ((((1 + η : ℝ) : ℂ) + Complex.I * (ρ.im : ℂ)).re = 1 + η) := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, sub_zero, mul_zero, add_zero]
  have hcim : ((((1 + η : ℝ) : ℂ) + Complex.I * (ρ.im : ℂ)).im = ρ.im) := by
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re]
    ring
  obtain
    ⟨massConstA, massConstB, hmassConstA, hmassConstB, Kmin, C, K, m, n, hKreq, hKupper,
      hKupperFixed, hKmin, hK, hn, hnm, hmK, hmCap, hCeq, _, hnormalized⟩ :=
    exists_completedLFunction_positive_LFunction_logDeriv_iterate hq hχ hp hinv hη hηsmall
      Krequested hKrequested hcre hcim hρre hzero hc hscale
  let D : ℝ := η ^ (n + 1) / (n.factorial : ℝ)
  have hD : 0 < D := by
    dsimp only [D]; positivity
  have hnormLower :
    Real.exp (-(ordinaryLFunctionNearOneDetectorExponent * (K : ℝ))) / D ≤
      ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ))
          (((1 + η : ℝ) : ℂ) + Complex.I * (ρ.im : ℂ))‖ := by
    apply (div_le_iff₀ hD).2
    simpa only [D, mul_comm] using hnormalized
  have hBpos : 0 < Real.exp (-(ordinaryLFunctionNearOneDetectorExponent * (K : ℝ))) / (D * 2) := by
    positivity
  have hstrict :
    Real.exp (-(ordinaryLFunctionNearOneDetectorExponent * (K : ℝ))) / (D * 2) <
      ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ))
          (((1 + η : ℝ) : ℂ) + Complex.I * (ρ.im : ℂ))‖ := by
    have hhalfEq :
      Real.exp (-(ordinaryLFunctionNearOneDetectorExponent * (K : ℝ))) / (D * 2) =
        (Real.exp (-(ordinaryLFunctionNearOneDetectorExponent * (K : ℝ))) / D) / 2 := by
      field_simp
    rw [hhalfEq]
    have hbasepos : 0 < Real.exp (-(ordinaryLFunctionNearOneDetectorExponent * (K : ℝ))) / D :=
      div_pos (Real.exp_pos _) hD
    nlinarith only [hbasepos, hnormLower]
  have hTlo : -(T : ℝ) ≤ ρ.im := (abs_le.mp hheight).1
  have hThi : ρ.im ≤ T := (abs_le.mp hheight).2
  obtain ⟨M, hM, j, hj, hjlarge⟩ :=
    exists_rational_height_large_of_strict_derivative_bound χ hχ (by linarith only [hη]) hTlo hThi n
      (Real.exp (-(ordinaryLFunctionNearOneDetectorExponent * (K : ℝ))) / (D * 2)) hstrict
  have hgrid :
    (Real.exp (-(ordinaryLFunctionNearOneDetectorExponent * (K : ℝ))) /
        ((η ^ (n + 1) / (n.factorial : ℝ)) * 2)) ≤
      ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ))
          (((1 + η : ℝ) : ℂ) + Complex.I * (((j : ℝ) / (M : ℝ) : ℝ) : ℂ))‖ := by
    simpa only [D, mul_comm, mul_left_comm, mul_assoc] using hjlarge
  exact
    ⟨massConstA, massConstB, hmassConstA, hmassConstB, Kmin, C, K, m, n, M, j, hKreq, hKupper,
      hKupperFixed, hKmin, hCeq, hK, hn, hnm, hmK, hmCap, hj, hgrid⟩

/--
Inputs: a primitive nonprincipal character, a completed-function zero near one, and a requested
minimum detector order.
Claim: one order block and one mesh make every grid point within `(K + 1) / M` of the zero height
retain at least half the explicit ordinary-derivative threshold.
Proof: apply the positive ordinary-derivative detector and choose the mesh so the vertical
variation allowance is smaller than half its lower bound.
Role: gives each zero occurrence a full window of large derivative values for incidence counting.
-/
theorem zero_grid_window {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hq : 2 ≤ q) (hχ : χ ≠ 1)
    (hp : χ.IsPrimitive) (hinv : χ⁻¹ ≠ 1) {η : ℝ} (hη : 0 < η) (hηsmall : η ≤ 1 / 1288)
    (Krequested : ℕ) (hKrequested : 2 ≤ Krequested) {ρ : ℂ} (hρre : |ρ.re - 1| ≤ η)
    (hzero : DirichletCharacter.completedLFunction χ ρ = 0)
    (hc : DirichletCharacter.completedLFunction χ (((1 + η : ℝ) : ℂ) + Complex.I * (ρ.im : ℂ)) ≠ 0)
    (hscale : η * Real.log ((q : ℝ) * (|ρ.im| + 3)) ≤ 3) :
    ∃ massConstA massConstB : ℝ,
      0 < massConstA ∧
        0 < massConstB ∧
        ∃ Kmin C K m n M : ℕ,
          Krequested ≤ K ∧
            K ≤ completedGenusRemoteTailUniformCutoff q η ρ.im ((C : ℝ) + 1) Kmin ∧
            K ≤ max completedGenusRemoteTailUniformOrderBound Kmin ∧
            Kmin ≤ K ∧
            C =
              Nat.ceil
                (completedZeroLocalLogBoundConstant *
                  (1 + 644 * η * Real.log ((q : ℝ) * (|ρ.im| + 3)))) ∧
            2 ≤ K ∧
            0 < n ∧
            n + 1 = m ∧
            K ≤ m ∧
            m ≤ K * completedLFunctionNearOneDetectorMultiplicityCap ∧
            0 < M ∧
            ((K + 1 : ℝ) / M) ≤ η / 8 ∧
            ∀ j : ℤ,
              |ρ.im - (j : ℝ) / M| ≤ (K + 1 : ℝ) / M →
                (Real.exp (-(ordinaryLFunctionNearOneDetectorExponent * (K : ℝ))) /
                    ((η ^ (n + 1) / (n.factorial : ℝ)) * 2)) ≤
                  ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ))
                      (((1 + η : ℝ) : ℂ) + Complex.I * (((j : ℝ) / M : ℝ) : ℂ))‖ := by
  have hcre : ((((1 + η : ℝ) : ℂ) + Complex.I * (ρ.im : ℂ)).re = 1 + η) := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, sub_zero, mul_zero, add_zero]
  have hcim : ((((1 + η : ℝ) : ℂ) + Complex.I * (ρ.im : ℂ)).im = ρ.im) := by
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re]
    ring
  obtain
    ⟨massConstA, massConstB, hmassConstA, hmassConstB, Kmin, C, K, m, n, hKreq, hKupper,
      hKupperFixed, hKmin, hK, hn, hnm, hmK, hmCap, hCeq, _, hnormalized⟩ :=
    exists_completedLFunction_positive_LFunction_logDeriv_iterate hq hχ hp hinv hη hηsmall
      Krequested hKrequested hcre hcim hρre hzero hc hscale
  let D : ℝ := η ^ (n + 1) / (n.factorial : ℝ)
  let B : ℝ := Real.exp (-(ordinaryLFunctionNearOneDetectorExponent * (K : ℝ))) / D
  have hD : 0 < D := by
    dsimp only [D]; positivity
  have hB : 0 < B := by
    dsimp only [B]; positivity
  have hlarge :
    B ≤
      ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ))
          (((1 + η : ℝ) : ℂ) + Complex.I * (ρ.im : ℂ))‖ := by
    apply (div_le_iff₀ hD).2
    simpa only [D, B, mul_comm] using hnormalized
  let Mmin : ℕ := Nat.ceil (8 * (K + 1 : ℝ) / η)
  obtain ⟨M, hMmin, hM, hgrid⟩ :=
    mesh_deriv_window_ge χ hχ (by linarith only [hη]) n K Mmin hB hlarge
  have hwidth : ((K + 1 : ℝ) / M) ≤ η / 8 := by
    apply (div_le_iff₀ (by exact_mod_cast hM : (0 : ℝ) < (M : ℝ))).2
    have hceil : 8 * (K + 1 : ℝ) / η ≤ (M : ℝ) := by
      exact le_trans (Nat.le_ceil _) (Nat.cast_le.mpr hMmin)
    have hmul : 8 * (K + 1 : ℝ) ≤ (M : ℝ) * η := (div_le_iff₀ hη).1 hceil
    nlinarith only [hmul]
  refine
    ⟨massConstA, massConstB, hmassConstA, hmassConstB, Kmin, C, K, m, n, M, hKreq, hKupper,
      hKupperFixed, hKmin, hCeq, hK, hn, hnm, hmK, hmCap, hM, hwidth, ?_⟩
  intro j hj
  have hresult := hgrid j hj
  change B / 2 ≤ _ at hresult
  have hhalfEq :
    Real.exp (-(ordinaryLFunctionNearOneDetectorExponent * (K : ℝ))) / (D * 2) =
      (Real.exp (-(ordinaryLFunctionNearOneDetectorExponent * (K : ℝ))) / D) / 2 := by
    field_simp
  rw [← hhalfEq] at hresult
  simpa only [B, D] using hresult

/--
Inputs: a primitive nonprincipal character, a completed-function zero in a bounded height window,
and a requested minimum detector order.
Claim: the character belongs to the derivative large set at a point of a finite rational-height
grid, with the explicit normalized detector threshold.
Proof: apply the grid witness theorem and unfold the primitive-character filter.
Role: connects zero detection directly to the family large-value count.
-/
theorem exists_primitiveCharacterDerivativeLargeSet_mem_of_completed_zero {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hq : 2 ≤ q) (hχ : χ ≠ 1) (hp : χ.IsPrimitive) (hinv : χ⁻¹ ≠ 1)
    {η : ℝ} (hη : 0 < η) (hηsmall : η ≤ 1 / 1288) (Krequested : ℕ) (hKrequested : 2 ≤ Krequested)
    {ρ : ℂ} (hρre : |ρ.re - 1| ≤ η) (hzero : DirichletCharacter.completedLFunction χ ρ = 0)
    (hc : DirichletCharacter.completedLFunction χ (((1 + η : ℝ) : ℂ) + Complex.I * (ρ.im : ℂ)) ≠ 0)
    (hscale : η * Real.log ((q : ℝ) * (|ρ.im| + 3)) ≤ 3) {T : ℕ} (hheight : |ρ.im| ≤ T) :
    ∃ massConstA massConstB : ℝ,
      0 < massConstA ∧
        0 < massConstB ∧
        ∃ Kmin C K m n M : ℕ,
          ∃ j : ℤ,
            Krequested ≤ K ∧
              K ≤ completedGenusRemoteTailUniformCutoff q η ρ.im ((C : ℝ) + 1) Kmin ∧
              K ≤ max completedGenusRemoteTailUniformOrderBound Kmin ∧
              Kmin ≤ K ∧
              C =
                Nat.ceil
                  (completedZeroLocalLogBoundConstant *
                    (1 + 644 * η * Real.log ((q : ℝ) * (|ρ.im| + 3)))) ∧
              2 ≤ K ∧
              0 < n ∧
              n + 1 = m ∧
              K ≤ m ∧
              m ≤ K * completedLFunctionNearOneDetectorMultiplicityCap ∧
              j ∈ Finset.Icc (-(T * M : ℤ)) (T * M : ℤ) ∧
              χ ∈
                primitiveCharacterDerivativeLargeSet q (by omega) n
                  (((1 + η : ℝ) : ℂ) + Complex.I * (((j : ℝ) / (M : ℝ) : ℝ) : ℂ))
                  (Real.exp (-(ordinaryLFunctionNearOneDetectorExponent * (K : ℝ))) /
                    ((η ^ (n + 1) / (n.factorial : ℝ)) * 2)) := by
  obtain
    ⟨massConstA, massConstB, hmassConstA, hmassConstB, Kmin, C, K, m, n, M, j, hKreq, hKupper,
      hKupperFixed, hKmin, hCeq, hK, hn, hnm, hmK, hmCap, hj, hlarge⟩ :=
    exists_character_derivative_large_grid_of_completed_zero hq hχ hp hinv hη hηsmall Krequested
      hKrequested hρre hzero hc hscale hheight
  have hq1 : 1 < q := by omega
  have hχmem : χ ∈ primitiveDirichletCharacterSet q := by
    simp only [primitiveDirichletCharacterSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hp
  have hlargeSet :
    χ ∈
      primitiveCharacterDerivativeLargeSet q hq1 n
        (((1 + η : ℝ) : ℂ) + Complex.I * (((j : ℝ) / (M : ℝ) : ℝ) : ℂ))
        (Real.exp (-(ordinaryLFunctionNearOneDetectorExponent * (K : ℝ))) /
          ((η ^ (n + 1) / (n.factorial : ℝ)) * 2)) := by
    simpa only [primitiveCharacterDerivativeLargeSet, Finset.mem_filter] using
      And.intro hχmem hlarge
  exact
    ⟨massConstA, massConstB, hmassConstA, hmassConstB, Kmin, C, K, m, n, M, j, hKreq, hKupper,
      hKupperFixed, hKmin, hCeq, hK, hn, hnm, hmK, hmCap, hj, hlargeSet⟩

/--
Inputs: a primitive nonprincipal character, a completed-function zero near one, and a requested
minimum detector order.
Claim: the character belongs to the derivative large set at every grid point in the detector
window, with the explicit half-strength threshold.
Proof: apply the all-points window detector and unfold the primitive-character filter.
Role: exposes the window detector in the finite-set form used by incidence and family counting.
-/
theorem zero_grid_mem {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hq : 2 ≤ q) (hχ : χ ≠ 1)
    (hp : χ.IsPrimitive) (hinv : χ⁻¹ ≠ 1) {η : ℝ} (hη : 0 < η) (hηsmall : η ≤ 1 / 1288)
    (Krequested : ℕ) (hKrequested : 2 ≤ Krequested) {ρ : ℂ} (hρre : |ρ.re - 1| ≤ η)
    (hzero : DirichletCharacter.completedLFunction χ ρ = 0)
    (hc : DirichletCharacter.completedLFunction χ (((1 + η : ℝ) : ℂ) + Complex.I * (ρ.im : ℂ)) ≠ 0)
    (hscale : η * Real.log ((q : ℝ) * (|ρ.im| + 3)) ≤ 3) :
    ∃ massConstA massConstB : ℝ,
      0 < massConstA ∧
        0 < massConstB ∧
        ∃ Kmin C K m n M : ℕ,
          Krequested ≤ K ∧
            K ≤ completedGenusRemoteTailUniformCutoff q η ρ.im ((C : ℝ) + 1) Kmin ∧
            K ≤ max completedGenusRemoteTailUniformOrderBound Kmin ∧
            Kmin ≤ K ∧
            C =
              Nat.ceil
                (completedZeroLocalLogBoundConstant *
                  (1 + 644 * η * Real.log ((q : ℝ) * (|ρ.im| + 3)))) ∧
            2 ≤ K ∧
            0 < n ∧
            n + 1 = m ∧
            K ≤ m ∧
            m ≤ K * completedLFunctionNearOneDetectorMultiplicityCap ∧
            0 < M ∧
            ((K + 1 : ℝ) / M) ≤ η / 8 ∧
            ∀ j : ℤ,
              |ρ.im - (j : ℝ) / M| ≤ (K + 1 : ℝ) / M →
                χ ∈
                  primitiveCharacterDerivativeLargeSet q (by omega) n
                    (((1 + η : ℝ) : ℂ) + Complex.I * (((j : ℝ) / M : ℝ) : ℂ))
                    (Real.exp (-(ordinaryLFunctionNearOneDetectorExponent * (K : ℝ))) /
                      ((η ^ (n + 1) / (n.factorial : ℝ)) * 2)) := by
  obtain
    ⟨massConstA, massConstB, hmassConstA, hmassConstB, Kmin, C, K, m, n, M, hKreq, hKupper,
      hKupperFixed, hKmin, hCeq, hK, hn, hnm, hmK, hmCap, hM, hwidth, hlarge⟩ :=
    zero_grid_window hq hχ hp hinv hη hηsmall Krequested hKrequested hρre hzero hc hscale
  have hq1 : 1 < q := by omega
  have hχmem : χ ∈ primitiveDirichletCharacterSet q := by
    simp only [primitiveDirichletCharacterSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hp
  refine
    ⟨massConstA, massConstB, hmassConstA, hmassConstB, Kmin, C, K, m, n, M, hKreq, hKupper,
      hKupperFixed, hKmin, hCeq, hK, hn, hnm, hmK, hmCap, hM, hwidth, ?_⟩
  intro j hj
  have hlarge' :
    (Real.exp (-(ordinaryLFunctionNearOneDetectorExponent * (K : ℝ))) /
        ((η ^ (n + 1) / (n.factorial : ℝ)) * 2)) ≤
      ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ))
          (((1 + η : ℝ) : ℂ) + Complex.I * (((j : ℝ) / M : ℝ) : ℂ))‖ :=
    hlarge j hj
  simpa only [primitiveCharacterDerivativeLargeSet, Finset.mem_filter] using And.intro hχmem hlarge'

/-- The character set detected by a Dirichlet polynomial of the stated cutoff and threshold. -/
noncomputable def primitiveCharacterPolynomialLargeSet (q : ℕ) (n cutoff : ℕ) (s : ℂ)
    (threshold : ℝ) : Finset (DirichletCharacter ℂ q) := by
  classical
    exact
    (primitiveDirichletCharacterSet q).filter fun χ =>
      threshold ≤
        Complex.normSq
          (∑ k ∈ Finset.range (cutoff + 1),
            LSeries.term (LSeries.logMul^[n] (fun j : ℕ => (ArithmeticFunction.vonMangoldt j : ℂ)))
                s k *
              χ (k : ZMod q))

/--
Inputs: a primitive-character modulus, a derivative order, a finite cutoff, a point to the right
of `σ > 1`, and a uniform truncation error at most `R/2`.

Claim: every character with logarithmic derivative norm at least `R` has its truncated Euler
polynomial squared norm at least `(R/2)^2`.

Proof: apply the explicit finite-series approximation, identify its twisted coefficients with the
untwisted coefficients times the character, and use the triangle inequality lemma above.

Role: supplies the set inclusion used to count large logarithmic derivatives by the additive large
sieve.
-/
theorem primitiveCharacterDerivativeLargeSet_subset_polynomialLargeSet (q : ℕ) (hq : 1 < q)
    (n cutoff : ℕ) (hcutoff : 1 ≤ cutoff) (σ : ℝ) (hσ : 1 < σ) (s : ℂ) (hs : σ ≤ s.re) (R : ℝ)
    (hR : 0 < R)
    (herror :
      ((σ - 1) / (2 * ((n + 1 : ℕ) : ℝ))) ^ (-((n + 1 : ℕ) : ℝ)) * (cutoff : ℝ) ^ (-(σ - 1) / 2) /
          ((σ - 1) / 2) ≤
        R / 2) :
    primitiveCharacterDerivativeLargeSet q hq n s R ⊆
      primitiveCharacterPolynomialLargeSet q n cutoff s ((R / 2) ^ 2) := by
  classical
  intro χ hχ
  let hqne : NeZero q := ⟨Nat.ne_of_gt (lt_trans Nat.zero_lt_one hq)⟩
  simp only [primitiveCharacterDerivativeLargeSet, Finset.mem_filter] at hχ
  rcases hχ with ⟨hprimitive, hlarge⟩
  let fχ : ℕ → ℂ := fun k => χ (k : ZMod q) * (ArithmeticFunction.vonMangoldt k : ℂ)
  have happrox :=
    iteratedDeriv_logDeriv_finite_series_error_le_explicit_of_re_ge χ hσ n cutoff hcutoff hs
  have happrox' :
    ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) s +
          (-1 : ℂ) ^ n *
            (∑ k ∈ Finset.range (cutoff + 1), LSeries.term (LSeries.logMul^[n] fχ) s k)‖ ≤
      R / 2 := by
    simpa only [fχ] using le_trans happrox herror
  have hpoly :
    (∑ k ∈ Finset.range (cutoff + 1), LSeries.term (LSeries.logMul^[n] fχ) s k) =
      ∑ k ∈ Finset.range (cutoff + 1),
        LSeries.term (LSeries.logMul^[n] (fun j : ℕ => (ArithmeticFunction.vonMangoldt j : ℂ))) s
            k *
          χ (k : ZMod q) := by
    apply Finset.sum_congr rfl
    intro k hk
    exact term_twist_iterate_identity (fun j => χ (j : ZMod q)) n s k
  have happrox'' :
    ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) s +
          (-1 : ℂ) ^ n *
            (∑ k ∈ Finset.range (cutoff + 1),
              LSeries.term
                  (LSeries.logMul^[n] (fun j : ℕ => (ArithmeticFunction.vonMangoldt j : ℂ))) s k *
                χ (k : ZMod q))‖ ≤
      R / 2 := by
    rw [← hpoly]
    exact happrox'
  exact
    Finset.mem_filter.mpr
      ⟨hprimitive, normSq_lower_from_approximation hlarge happrox'' (le_of_lt hR)⟩

/--
Purpose: count primitive characters up to a cutoff whose differentiated logarithmic derivative
exceeds a fixed threshold.

Definition: sums the cardinalities of `primitiveCharacterDerivativeLargeSet` over moduli in
`1 < q ≤ Qmax`.

Role: states the family count controlled by the large-sieve consequence that follows.
-/
noncomputable def primitiveCharacterDerivativeFamilyLargeCount (Qmax n : ℕ) (s : ℂ) (R : ℝ) :
    ℝ := by
  classical
    exact
    ∑ q ∈ (Finset.Ioc 1 Qmax).attach,
      (primitiveCharacterDerivativeLargeSet q.val (Finset.mem_Ioc.mp q.property).1 n s R).card

/--
Inputs: a real-valued height function, a positive mesh denominator, an occurrence, and an
integer grid index.
Definition: records whether the grid height is within one mesh step of the occurrence height.
Role: expresses the finite height incidence used to transfer a multiplicity-preserving ledger to
the rational height grid.
-/
noncomputable def heightGridIncidence {α : Type*} (height : α → ℝ) (M : ℕ) (a : α) (m : ℤ) :
    Bool := by classical exact if h : |height a - (m : ℝ) / M| ≤ 1 / M then true else false

/--
Inputs: a finite set of occurrences whose heights lie in `[-T,T]`, a positive mesh denominator,
and a uniform bound on the number of occurrences incident to each grid point.
Claim: the occurrence count is at most the grid size times that uniform bound.
Proof: approximate each bounded height by an integer grid point, then apply finite incidence
counting.
Role: converts a multiplicity-preserving height ledger into a finite grid count.
-/
theorem card_le_integer_height_grid_card_mul_of_fiber_bound {α : Type*} (s : Finset α)
    (height : α → ℝ) (T M B : ℕ) (hM : 0 < M)
    (hheight : ∀ a ∈ s, -(T : ℝ) ≤ height a ∧ height a ≤ T)
    (hfiber :
      ∀ m ∈ Finset.Icc (-(T * M : ℤ)) (T * M : ℤ),
        (s.filter fun a => heightGridIncidence height M a m = true).card ≤ B) :
    s.card ≤ (Finset.Icc (-(T * M : ℤ)) (T * M : ℤ)).card * B := by
  have hcoverage :
    ∀ a ∈ s,
      1 ≤
        ((Finset.Icc (-(T * M : ℤ)) (T * M : ℤ)).filter fun m =>
            heightGridIncidence height M a m = true).card := by
    intro a ha
    obtain ⟨m, hm, happrox⟩ :=
      exists_integer_height_grid_approximation hM (hheight a ha).1 (hheight a ha).2
    have hinc : heightGridIncidence height M a m = true := by
      unfold heightGridIncidence
      simp only [dite_eq_left happrox]
    have hpos :
      0 <
        ((Finset.Icc (-(T * M : ℤ)) (T * M : ℤ)).filter fun m =>
            heightGridIncidence height M a m = true).card :=
      Finset.card_pos.mpr ⟨m, Finset.mem_filter.mpr ⟨hm, hinc⟩⟩
    omega
  simpa only [Nat.mul_one] using
    card_mul_le_card_mul_of_incidence s (Finset.Icc (-(T * M : ℤ)) (T * M : ℤ))
      (fun a m => heightGridIncidence height M a m) 1 B hcoverage hfiber

/--
Inputs: a real-valued height, a positive mesh denominator, a natural window radius, and an
occurrence whose height lies in `[-T,T]`.
Definition: records whether a grid height is within `(K + 1) / M` of the occurrence height.
Role: retains all grid points in a fixed integer neighborhood of a ceiling approximation, so one
occurrence contributes a controlled block of incidences.
-/
noncomputable def heightWindowGridIncidence {α : Type*} (height : α → ℝ) (M K : ℕ) (a : α) (m : ℤ) :
    Bool := by classical exact if h : |height a - (m : ℝ) / M| ≤ (K + 1) / M then true else false

/--
Inputs: a finite set of occurrences with heights in `[-T,T]`, a positive mesh denominator, and
a natural integer window radius.
Claim: every occurrence is incident to at least `2*K+1` points of the expanded finite grid.
Proof: take a ceiling grid point within `1/M`; its integer neighborhood of radius `K` remains in
the expanded grid and lies within `(K+1)/M` of the occurrence height.
Role: supplies the multiplicity gain required by height-window incidence counting.
-/
theorem window_grid_incidence_card_lower_bound {α : Type*} (s : Finset α) (height : α → ℝ)
    (T M K : ℕ) (hM : 0 < M) (hheight : ∀ a ∈ s, -(T : ℝ) ≤ height a ∧ height a ≤ T) :
    ∀ a ∈ s,
      2 * K + 1 ≤
        ((Finset.Icc (-(T * M : ℤ) - (K + 1 : ℤ)) ((T * M : ℤ) + (K + 1 : ℤ))).filter
            (fun m => heightWindowGridIncidence height M K a m = true)).card := by
  intro a ha
  obtain ⟨m₀, hm₀, happrox⟩ :=
    exists_integer_height_grid_approximation hM (hheight a ha).1 (hheight a ha).2
  let localGrid := Finset.Icc (m₀ - K) (m₀ + K)
  let grid := Finset.Icc (-(T * M : ℤ) - (K + 1 : ℤ)) ((T * M : ℤ) + (K + 1 : ℤ))
  have hlocal :
    localGrid ⊆ grid.filter (fun m => heightWindowGridIncidence height M K a m = true) := by
    intro m hm
    have hmLocal := Finset.mem_Icc.mp hm
    have hm₀' := Finset.mem_Icc.mp hm₀
    have hmGrid : m ∈ grid := by
      apply Finset.mem_Icc.mpr
      constructor
      · calc
          -(T * M : ℤ) - (K + 1 : ℤ) ≤ -(T * M : ℤ) - K := by omega
          _ ≤ m₀ - K := sub_le_sub_right hm₀'.1 K
          _ ≤ m := hmLocal.1
      · calc
          m ≤ m₀ + K := hmLocal.2
          _ ≤ (T * M : ℤ) + K := by simpa only [add_comm] using add_le_add_right hm₀'.2 (K : ℤ)
          _ ≤ (T * M : ℤ) + (K + 1 : ℤ) := by omega
    have hmDistance : |(m₀ : ℝ) - m| ≤ K := by
      rw [abs_le]
      constructor <;> exact_mod_cast (show _ from by omega)
    have hMreal : 0 < (M : ℝ) := by exact_mod_cast hM
    have hsecond : |(m₀ : ℝ) / M - (m : ℝ) / M| ≤ (K : ℝ) / M := by
      rw [← sub_div, abs_div, abs_of_pos hMreal]
      exact div_le_div_of_nonneg_right (by exact_mod_cast hmDistance) hMreal.le
    have hdistance : |height a - (m : ℝ) / M| ≤ (K + 1) / M := by
      calc
        |height a - (m : ℝ) / M| = |(height a - (m₀ : ℝ) / M) + ((m₀ : ℝ) / M - (m : ℝ) / M)| := by
          congr 1
          ring
        _ ≤ |height a - (m₀ : ℝ) / M| + |(m₀ : ℝ) / M - (m : ℝ) / M| := abs_add_le _ _
        _ ≤ 1 / M + (K : ℝ) / M := add_le_add happrox hsecond
        _ = (K + 1) / M := by
          rw [add_div]; ring
    have hinc : heightWindowGridIncidence height M K a m = true := by
      unfold heightWindowGridIncidence
      simp only [dite_eq_left hdistance]
    exact Finset.mem_filter.mpr ⟨hmGrid, hinc⟩
  have hcard := Finset.card_le_card hlocal
  have hlocalCard : localGrid.card = 2 * K + 1 := by
    dsimp only [localGrid]
    rw [Int.card_Icc]
    omega
  rw [hlocalCard] at hcard
  exact hcard

/--
Inputs: a finite set of bounded-height occurrences, a positive mesh denominator, an integer
window radius, and a uniform bound on each expanded-grid fiber.
Claim: the occurrence count times `2*K+1` is at most the expanded grid size times the fiber bound.
Proof: combine the block of incidences contributed by every occurrence with finite double
counting.
Role: retains the grid-density gain needed when zero occurrences are assigned to height windows.
-/
theorem card_mul_window_grid_size_le_expanded_grid_card_mul_of_fiber_bound {α : Type*}
    (s : Finset α) (height : α → ℝ) (T M K B : ℕ) (hM : 0 < M)
    (hheight : ∀ a ∈ s, -(T : ℝ) ≤ height a ∧ height a ≤ T)
    (hfiber :
      ∀ m ∈ Finset.Icc (-(T * M : ℤ) - (K + 1 : ℤ)) ((T * M : ℤ) + (K + 1 : ℤ)),
        (s.filter fun a => heightWindowGridIncidence height M K a m = true).card ≤ B) :
    s.card * (2 * K + 1) ≤
      (Finset.Icc (-(T * M : ℤ) - (K + 1 : ℤ)) ((T * M : ℤ) + (K + 1 : ℤ))).card * B := by
  exact
    card_mul_le_card_mul_of_incidence s
      (Finset.Icc (-(T * M : ℤ) - (K + 1 : ℤ)) ((T * M : ℤ) + (K + 1 : ℤ)))
      (fun a m => heightWindowGridIncidence height M K a m) (2 * K + 1) B
      (window_grid_incidence_card_lower_bound s height T M K hM hheight) hfiber

/--
Inputs: a nonprincipal character, a zero occurrence in the family height rectangle, a nearby
height-grid point, and local scale hypotheses.
Claim: every occurrence in the grid window also belongs to the completed-zero occurrence set in a
small rectangle centered at `1 + i*m/M`.
Proof: the family rectangle bounds the real part by `σ` and `1`; the incidence bounds the imaginary
part, placing both coordinates in the local rectangle.
Role: transfers each character's multiplicity-preserving ledger fiber to the local count bounded
by the unconditional local multiplicity theorem.
-/
theorem completedZeroMultiplicityOccurrences_window_filter_subset_local {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {σ η : ℝ} (hσ1 : σ ≤ 1) (hσ : 1 - σ ≤ η / 8)
    (hη : 0 < η) (n M K : ℕ) (hwindow : (K + 1 : ℝ) / M ≤ η / 8) (m : ℤ) :
    ((completedZeroMultiplicityOccurrences χ hχ ((σ : ℂ) - (n : ℝ) * Complex.I)
            ((1 : ℂ) + (n : ℝ) * Complex.I)).filter
        (fun x => heightWindowGridIncidence (fun y => y.1.im) M K x m = true)) ⊆
      completedZeroMultiplicityOccurrences χ hχ
        (((1 - η / 8 : ℝ) : ℂ) + Complex.I * (((m : ℝ) / M - η / 8 : ℝ) : ℂ))
        (((1 + η / 8 : ℝ) : ℂ) + Complex.I * (((m : ℝ) / M + η / 8 : ℝ) : ℂ)) := by
  intro x hx
  rcases x with ⟨ρ, i⟩
  rcases Finset.mem_filter.mp hx with ⟨hocc, hinc⟩
  simp only [completedZeroMultiplicityOccurrences, Finset.mem_sigma] at hocc ⊢
  rcases hocc with ⟨hρ, hi⟩
  have hdist : |ρ.im - (m : ℝ) / M| ≤ (K + 1 : ℝ) / M := by
    by_cases h : |ρ.im - (m : ℝ) / M| ≤ (K + 1 : ℝ) / M
    · exact h
    · unfold heightWindowGridIncidence at hinc
      simp only [dite_eq_right h] at hinc
      cases hinc
  have hrect := (mem_completedZerosInRectangle_iff.mp hρ).1
  rw [dirichletCompletedLFunctionRectangleBox, Rectangle.rectangleClosedBox,
    Complex.mem_reProdIm] at hrect
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    zero_mul, sub_zero, mul_zero, add_zero, Complex.sub_im, Complex.ofReal_im, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, zero_add, sub_zero,
    add_zero] at hrect
  rcases hrect with ⟨hreBox, himBox⟩
  have hre : σ ≤ ρ.re ∧ ρ.re ≤ 1 := by
    rcases Set.mem_uIcc.mp hreBox with hcase | hcase
    · exact hcase
    · constructor <;> linarith only [hσ1, hcase.1, hcase.2]
  have hnegN : -(n : ℝ) ≤ (n : ℝ) := by
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith only [hn0]
  have him : -(n : ℝ) ≤ ρ.im ∧ ρ.im ≤ n := by
    rcases Set.mem_uIcc.mp himBox with hcase | hcase
    · simpa only [zero_sub, mul_one] using hcase
    · constructor <;> linarith only [hnegN, hcase.1, hcase.2]
  have hreLocal : ρ.re ∈ Set.uIcc (1 - η / 8) (1 + η / 8) := by
    apply Set.mem_uIcc.mpr
    left
    constructor
    · linarith only [hσ, hre.1]
    · linarith only [hre.2, hη]
  have himLocal : ρ.im ∈ Set.uIcc ((m : ℝ) / M - η / 8) ((m : ℝ) / M + η / 8) := by
    apply Set.mem_uIcc.mpr
    left
    constructor <;> rw [abs_le] at hdist
    · linarith only [hdist.1, hwindow]
    · linarith only [hdist.2, hwindow]
  have hlocalBox :
    ρ ∈
      dirichletCompletedLFunctionRectangleBox
        (((1 - η / 8 : ℝ) : ℂ) + Complex.I * (((m : ℝ) / M - η / 8 : ℝ) : ℂ))
        (((1 + η / 8 : ℝ) : ℂ) + Complex.I * (((m : ℝ) / M + η / 8 : ℝ) : ℂ)) := by
    rw [dirichletCompletedLFunctionRectangleBox, Rectangle.rectangleClosedBox, Complex.mem_reProdIm]
    constructor
    · simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.ofReal_im, zero_mul, sub_zero, mul_zero, add_zero, zero_add] using hreLocal
    · simpa only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, zero_mul, mul_one, add_zero, zero_add, one_mul] using himLocal
  have hzero := (mem_completedZerosInRectangle_iff.mp hρ).2
  refine ⟨mem_completedZerosInRectangle_iff.mpr ⟨hlocalBox, hzero⟩, hi⟩

/--
Inputs: a nonprincipal character, a family zero rectangle, and a height-grid window contained in
a local rectangle near `1 + i*m/M`.
Claim: the multiplicity of occurrences from this one character in the grid window is bounded by
the completed-zero multiplicity count in the local rectangle.
Proof: use the occurrence-set inclusion and the identity between its cardinality and analytic
multiplicity.
Role: turns the local zero-count estimate into a genuine upper bound for a character's incidence
fiber without collapsing repeated zeros.
-/
theorem completedZeroMultiplicityOccurrences_window_filter_card_le_local_count {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {σ η : ℝ} (hσ1 : σ ≤ 1) (hσ : 1 - σ ≤ η / 8)
    (hη : 0 < η) (n M K : ℕ) (hwindow : (K + 1 : ℝ) / M ≤ η / 8) (m : ℤ) :
    (((completedZeroMultiplicityOccurrences χ hχ ((σ : ℂ) - (n : ℝ) * Complex.I)
                ((1 : ℂ) + (n : ℝ) * Complex.I)).filter
            (fun x => heightWindowGridIncidence (fun y => y.1.im) M K x m = true)).card :
        ℝ) ≤
      completedZeroMultiplicityCountInRectangle χ hχ
        (((1 - η / 8 : ℝ) : ℂ) + Complex.I * (((m : ℝ) / M - η / 8 : ℝ) : ℂ))
        (((1 + η / 8 : ℝ) : ℂ) + Complex.I * (((m : ℝ) / M + η / 8 : ℝ) : ℂ)) := by
  let localOccurrences :=
    completedZeroMultiplicityOccurrences χ hχ
      (((1 - η / 8 : ℝ) : ℂ) + Complex.I * (((m : ℝ) / M - η / 8 : ℝ)))
      (((1 + η / 8 : ℝ) : ℂ) + Complex.I * (((m : ℝ) / M + η / 8 : ℝ)))
  calc
    _ ≤ (localOccurrences.card : ℝ) := by
      exact_mod_cast
        (show
          ((completedZeroMultiplicityOccurrences χ hχ ((σ : ℂ) - (n : ℝ) * Complex.I)
                    ((1 : ℂ) + (n : ℝ) * Complex.I)).filter
                (fun x => heightWindowGridIncidence (fun y => y.1.im) M K x m = true)).card ≤
            localOccurrences.card
          from by
          simpa only [localOccurrences] using
            Finset.card_le_card
              (completedZeroMultiplicityOccurrences_window_filter_subset_local χ hχ hσ1 hσ hη n M K
                hwindow m))
    _ = _ := by
      dsimp only [localOccurrences]
      exact (completedZeroMultiplicityCountInRectangle_eq_occurrence_card χ hχ _ _).symm

/--
Inputs: an occurrence in a completed-zero rectangle whose vertical endpoints are `-n` and `n`.
Claim: its imaginary part lies in `[-n,n]`.
Proof: unfold rectangle membership and simplify the imaginary coordinates of its two corners.
Role: provides the height-domain hypothesis for finite-grid window incidence on the zero ledger.
-/
theorem completedZeroMultiplicityOccurrences_height_mem {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (σ : ℝ) (n : ℕ)
    {x : Σ ρ : ℂ, Fin (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ)}
    (hx :
      x ∈
        completedZeroMultiplicityOccurrences χ hχ ((σ : ℂ) - (n : ℝ) * Complex.I)
          ((1 : ℂ) + (n : ℝ) * Complex.I)) :
    -(n : ℝ) ≤ x.1.im ∧ x.1.im ≤ n := by
  rcases x with ⟨ρ, i⟩
  have hρ :
    ρ ∈
      completedZerosInRectangle χ hχ ((σ : ℂ) - (n : ℝ) * Complex.I)
        ((1 : ℂ) + (n : ℝ) * Complex.I) := by
    exact (Finset.mem_sigma.mp (by simpa only [completedZeroMultiplicityOccurrences] using hx)).1
  have hbox := (mem_completedZerosInRectangle_iff.mp hρ).1
  rw [dirichletCompletedLFunctionRectangleBox, Rectangle.rectangleClosedBox,
    Complex.mem_reProdIm] at hbox
  have himBox : ρ.im ∈ Set.uIcc (-(n : ℝ)) (n : ℝ) := by
    simpa only [Complex.add_im, Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.one_im, zero_mul, mul_one, one_mul, zero_sub,
      add_zero, zero_add] using hbox.2
  rcases Set.mem_uIcc.mp himBox with hcase | hcase
  · exact hcase
  · have hnegN : -(n : ℝ) ≤ n := by
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith only [hn0]
    exact ⟨by linarith only [hcase.1, hcase.2, hnegN], by linarith only [hcase.1, hcase.2, hnegN]⟩

/--
Inputs: a primitive nonprincipal character, its multiplicity-preserving zero occurrences up to
height `n`, a mesh, and a window radius satisfying the local-scale hypotheses.
Claim: the occurrence count times `2*K+1` is at most the sum of the local multiplicity counts at
all points of the expanded height grid.
Proof: each occurrence meets at least `2*K+1` grid windows; each grid fiber is contained in the
completed-zero occurrence set of its local rectangle; apply incidence double counting with the
pointwise local fiber sizes.
Role: connects the actual per-character zero ledger to local multiplicity windows without a
single global fiber bound.
-/
theorem primitiveCharacter_zero_occurrences_window_card_mul_le_local_sum {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {σ η : ℝ} (hσ1 : σ ≤ 1) (hσ : 1 - σ ≤ η / 8)
    (hη : 0 < η) (n M K : ℕ) (hM : 0 < M) (hwindow : (K + 1 : ℝ) / M ≤ η / 8) :
    (completedZeroMultiplicityOccurrences χ hχ ((σ : ℂ) - (n : ℝ) * Complex.I)
            ((1 : ℂ) + (n : ℝ) * Complex.I)).card *
        (2 * K + 1) ≤
      ∑ m ∈ Finset.Icc (-(n * M : ℤ) - (K + 1 : ℤ)) ((n * M : ℤ) + (K + 1 : ℤ)),
        (completedZeroMultiplicityOccurrences χ hχ
            (((1 - η / 8 : ℝ) : ℂ) + Complex.I * (((m : ℝ) / M - η / 8 : ℝ) : ℂ))
            (((1 + η / 8 : ℝ) : ℂ) + Complex.I * (((m : ℝ) / M + η / 8 : ℝ) : ℂ))).card := by
  let occurrences :=
    completedZeroMultiplicityOccurrences χ hχ ((σ : ℂ) - (n : ℝ) * Complex.I)
      ((1 : ℂ) + (n : ℝ) * Complex.I)
  let height :
    (Σ ρ : ℂ, Fin (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ)) → ℝ := fun x =>
    x.1.im
  let grid : Finset ℤ := Finset.Icc (-(n * M : ℤ) - (K + 1 : ℤ)) ((n * M : ℤ) + (K + 1 : ℤ))
  let incidence :
    (Σ ρ : ℂ, Fin (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ)) → ℤ → Bool :=
    fun x m => heightWindowGridIncidence height M K x m
  let localOccurrences :
    ℤ → Finset (Σ ρ : ℂ, Fin (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ)) :=
    fun m =>
    completedZeroMultiplicityOccurrences χ hχ
      (((1 - η / 8 : ℝ) : ℂ) + Complex.I * (((m : ℝ) / M - η / 8 : ℝ) : ℂ))
      (((1 + η / 8 : ℝ) : ℂ) + Complex.I * (((m : ℝ) / M + η / 8 : ℝ) : ℂ))
  have hheight : ∀ x ∈ occurrences, -(n : ℝ) ≤ height x ∧ height x ≤ n := by
    intro x hx
    exact completedZeroMultiplicityOccurrences_height_mem χ hχ σ n hx
  have hlower := window_grid_incidence_card_lower_bound occurrences height n M K hM hheight
  have hupper :
    ∀ m ∈ grid,
      (occurrences.filter fun x => incidence x m = true).card ≤ (localOccurrences m).card := by
    intro m hm
    exact
      Finset.card_le_card
        (by
          simpa only [occurrences, height, incidence, localOccurrences] using
            completedZeroMultiplicityOccurrences_window_filter_subset_local χ hχ hσ1 hσ hη n M K
              hwindow m)
  have hcount :=
    card_mul_le_sum_window_fiber_bounds occurrences grid incidence (2 * K + 1)
      (fun m => (localOccurrences m).card) hlower hupper
  simpa only [occurrences, grid, localOccurrences] using hcount

/--
Purpose: sum local height-window occurrence counts over the same primitive nonprincipal family as
the zero-occurrence ledger.
Definition: for each conductor and character, sum multiplicity-indexed local rectangle counts over
the expanded integer height grid; nonprimitive and principal characters contribute zero.
Inputs: a conductor cutoff, a real-part threshold, a positive local scale, a natural height, a
mesh denominator, and an integer window radius.
Output: a real-valued sum that preserves the conductor, character, zero, and multiplicity index.
Role: provides the family-side quantity to which the per-character window-incidence estimate
applies before the local multiplicity and hybrid large-sieve bounds are inserted.
-/
noncomputable def primitiveCharacterFamilyLocalWindowOccurrenceCount (Q : ℕ) (η : ℝ) (n M K : ℕ) :
    ℝ := by
  classical
  let grid : Finset ℤ := Finset.Icc (-(n * M : ℤ) - (K + 1 : ℤ)) ((n * M : ℤ) + (K + 1 : ℤ))
  exact
    ∑ q : Fin Q,
      ∑ χ : DirichletCharacter ℂ (q.val + 1),
        if hχ : χ ≠ 1 then
          if hprim : χ.IsPrimitive then
            ∑ m ∈ grid,
              ((completedZeroMultiplicityOccurrences χ hχ
                    (((1 - η / 8 : ℝ) : ℂ) + Complex.I * (((m : ℝ) / M - η / 8 : ℝ) : ℂ))
                    (((1 + η / 8 : ℝ) : ℂ) + Complex.I * (((m : ℝ) / M + η / 8 : ℝ) : ℂ))).card :
                ℝ)
          else 0
        else 0

/--
Purpose: sum the absolute logarithmic local-window majorant over the same conductor, character,
and height-grid ranges as `primitiveCharacterFamilyLocalWindowOccurrenceCount`.
Definition: for every primitive nonprincipal character and grid point, use
`1 + η * log(q * (|m/M| + 3))`; all other characters contribute zero.
Role: records the explicit right side obtained by summing the uniform local zero-count estimate.
-/
noncomputable def primitiveCharacterFamilyLocalWindowLogWeightSum (Q : ℕ) (η : ℝ) (n M K : ℕ) :
    ℝ := by
  classical
  let grid : Finset ℤ := Finset.Icc (-(n * M : ℤ) - (K + 1 : ℤ)) ((n * M : ℤ) + (K + 1 : ℤ))
  exact
    ∑ q : Fin Q,
      ∑ χ : DirichletCharacter ℂ (q.val + 1),
        if hχ : χ ≠ 1 then
          if hprim : χ.IsPrimitive then
            ∑ m ∈ grid, (1 + η * Real.log (((q.val + 1 : ℕ) : ℝ) * (|((m : ℝ) / M)| + 3)))
          else 0
        else 0

/--
Inputs: a conductor cutoff, a real-part threshold close to one, a positive local scale, a natural
height, and a height grid with a valid integer window radius.
Claim: the primitive-family zero-occurrence count times `2*K+1` is at most the family sum of local
window occurrence counts.
Proof: apply the per-character multiplicity-preserving incidence bound and sum over conductors
and primitive nonprincipal characters.
Role: assembles the actual family ledger incidence without introducing a global fiber cap.
-/
theorem primitiveCharacterFamilyZeroOccurrenceCount_mul_window_size_le_local_window_sum (Q : ℕ)
    {σ η : ℝ} (hσ1 : σ ≤ 1) (hσ : 1 - σ ≤ η / 8) (hη : 0 < η) (n M K : ℕ) (hM : 0 < M)
    (hwindow : (K + 1 : ℝ) / M ≤ η / 8) :
    primitiveCharacterFamilyZeroOccurrenceCountAtNatHeight Q σ n * (2 * K + 1 : ℝ) ≤
      primitiveCharacterFamilyLocalWindowOccurrenceCount Q η n M K := by
  classical
  unfold primitiveCharacterFamilyZeroOccurrenceCountAtNatHeight
    primitiveCharacterFamilyLocalWindowOccurrenceCount
  calc
    _ =
        ∑ q : Fin Q,
          ∑ χ : DirichletCharacter ℂ (q.val + 1),
            (if hχ : χ ≠ 1 then
                if hprim : χ.IsPrimitive then
                  ((completedZeroMultiplicityOccurrences χ hχ ((σ : ℂ) - (n : ℝ) * Complex.I)
                        ((1 : ℂ) + (n : ℝ) * Complex.I)).card :
                    ℝ)
                else 0
              else 0) *
              (2 * K + 1 : ℝ) :=
      by simp only [Finset.sum_mul]
    _ ≤
        ∑ q : Fin Q,
          ∑ χ : DirichletCharacter ℂ (q.val + 1),
            if hχ : χ ≠ 1 then
              if hprim : χ.IsPrimitive then
                ∑ m ∈ Finset.Icc (-(n * M : ℤ) - (K + 1 : ℤ)) ((n * M : ℤ) + (K + 1 : ℤ)),
                  ((completedZeroMultiplicityOccurrences χ hχ
                        (((1 - η / 8 : ℝ) : ℂ) + Complex.I * (((m : ℝ) / M - η / 8 : ℝ) : ℂ))
                        (((1 + η / 8 : ℝ) : ℂ) +
                          Complex.I * (((m : ℝ) / M + η / 8 : ℝ) : ℂ))).card :
                    ℝ)
              else 0
            else 0 :=
      by
      apply Finset.sum_le_sum
      intro q hq
      apply Finset.sum_le_sum
      intro χ hχmem
      by_cases hχ : χ ≠ 1
      · by_cases hprim : χ.IsPrimitive
        · simp only [dite_eq_left hχ, dite_eq_left hprim]
          have hchar :=
            primitiveCharacter_zero_occurrences_window_card_mul_le_local_sum χ hχ hσ1 hσ hη n M K hM
              hwindow
          exact_mod_cast hchar
        · simp only [dite_eq_left hχ, dite_eq_right hprim, zero_mul]
          exact le_rfl
      · simp only [dite_eq_right hχ, zero_mul]
        exact le_rfl
    _ = _ := by rfl

/--
Inputs: a positive local scale and a real height center.
Claim: the completed-zero rectangle with both half-widths `η / 8` lies in the closed disk of
radius `η / 4` around `1 + i * t`.
Proof: bound the real and imaginary coordinate deviations separately and apply the triangle
inequality for the complex norm.
Role: supplies the geometric hypothesis of the uniform local multiplicity estimate.
-/
theorem heightWindowRectangle_norm_le (η t : ℝ) (hη : 0 < η) :
    ∀
      ρ ∈
        dirichletCompletedLFunctionRectangleBox
          (((1 - η / 8 : ℝ) : ℂ) + Complex.I * ((t - η / 8 : ℝ) : ℂ))
          (((1 + η / 8 : ℝ) : ℂ) + Complex.I * ((t + η / 8 : ℝ) : ℂ)),
      ‖ρ - ((1 : ℂ) + (t : ℝ) * Complex.I)‖ ≤ η / 4 := by
  let z : ℂ := ((1 - η / 8 : ℝ) : ℂ) + Complex.I * ((t - η / 8 : ℝ) : ℂ)
  let w : ℂ := ((1 + η / 8 : ℝ) : ℂ) + Complex.I * ((t + η / 8 : ℝ) : ℂ)
  let center : ℂ := (1 : ℂ) + (t : ℝ) * Complex.I
  have hRealEnds : 1 - η / 8 ≤ 1 + η / 8 := by linarith only [hη]
  intro ρ hρ
  rw [dirichletCompletedLFunctionRectangleBox, Rectangle.rectangleClosedBox,
    Complex.mem_reProdIm] at hρ
  have hreBox : ρ.re ∈ Set.uIcc (1 - η / 8) (1 + η / 8) := by
    simpa only [z, w, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_im, zero_mul, sub_zero, mul_zero, sub_self, add_zero] using hρ.1
  have himBox : ρ.im ∈ Set.uIcc (t - η / 8) (t + η / 8) := by
    simpa only [z, w, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, zero_mul, mul_one, one_mul, add_zero, zero_add] using hρ.2
  have hre : 1 - η / 8 ≤ ρ.re ∧ ρ.re ≤ 1 + η / 8 := by
    rcases Set.mem_uIcc.mp hreBox with hcase | hcase
    · exact hcase
    · constructor <;> linarith only [hRealEnds, hcase.1, hcase.2]
  have him : t - η / 8 ≤ ρ.im ∧ ρ.im ≤ t + η / 8 := by
    rcases Set.mem_uIcc.mp himBox with hcase | hcase
    · exact hcase
    · constructor <;> linarith only [hRealEnds, hcase.1, hcase.2]
  have hreAbs : |ρ.re - 1| ≤ η / 8 := by
    rw [abs_le]
    constructor <;> linarith only [hre.1, hre.2]
  have himAbs : |ρ.im - t| ≤ η / 8 := by
    rw [abs_le]
    constructor <;> linarith only [him.1, him.2]
  have hdecomp : ρ - center = ((ρ.re - 1 : ℝ) : ℂ) + Complex.I * ((ρ.im - t : ℝ) : ℂ) := by
    apply Complex.ext
    · simp only [center, Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.mul_re, Complex.I_re, Complex.one_re, Complex.I_im, zero_mul, sub_zero, mul_zero,
        add_zero]
    · simp only [center, Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.I_re, Complex.I_im, Complex.one_im, Complex.ofReal_re, zero_mul, mul_one, one_mul,
        add_zero, zero_add]
  calc
    ‖ρ - center‖ = ‖((ρ.re - 1 : ℝ) : ℂ) + Complex.I * ((ρ.im - t : ℝ) : ℂ)‖ := by rw [hdecomp]
    _ ≤ ‖((ρ.re - 1 : ℝ) : ℂ)‖ + ‖Complex.I * ((ρ.im - t : ℝ) : ℂ)‖ := norm_add_le _ _
    _ = |ρ.re - 1| + |ρ.im - t| := by
      simp only [Complex.norm_real, Real.norm_eq_abs, Complex.norm_mul, Complex.norm_I, one_mul]
    _ ≤ η / 8 + η / 8 := add_le_add hreAbs himAbs
    _ = η / 4 := by ring

/--
Inputs: a primitive nonprincipal character, a family zero rectangle, and a height-grid window
whose horizontal and vertical widths are at most `η/8`.
Claim: the multiplicity of occurrences from this character in the grid window is bounded by an
absolute constant times `1 + η * log(q * (|t| + 3))`.
Proof: place the incident occurrences in the local rectangle around `1 + i*t`, apply the
unconditional completed-zero multiplicity estimate, and use the occurrence-cardinality bound.
Role: supplies the analytic fiber bound required to apply the window incidence counting theorem to
primitive zero occurrences.
-/
theorem primitiveCharacter_zero_window_fiber_le_local_log_bound {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) (hinv : χ⁻¹ ≠ 1) {σ η : ℝ}
    (hσ1 : σ ≤ 1) (hσ : 1 - σ ≤ η / 8) (hη : 0 < η) (hη1 : η ≤ 1 / 2) (n M K : ℕ)
    (hwindow : (K + 1 : ℝ) / M ≤ η / 8) (m : ℤ) :
    (((completedZeroMultiplicityOccurrences χ hχ ((σ : ℂ) - (n : ℝ) * Complex.I)
                ((1 : ℂ) + (n : ℝ) * Complex.I)).filter
            (fun x => heightWindowGridIncidence (fun y => y.1.im) M K x m = true)).card :
        ℝ) ≤
      completedZeroLocalLogBoundConstant *
        (1 + η * Real.log ((q : ℝ) * (|((m : ℝ) / M)| + 3))) := by
  let t : ℝ := (m : ℝ) / M
  let z : ℂ := ((1 - η / 8 : ℝ) : ℂ) + Complex.I * ((t - η / 8 : ℝ) : ℂ)
  let w : ℂ := ((1 + η / 8 : ℝ) : ℂ) + Complex.I * ((t + η / 8 : ℝ) : ℂ)
  let center : ℂ := (1 : ℂ) + (t : ℝ) * Complex.I
  have hRealEnds : 1 - η / 8 ≤ 1 + η / 8 := by linarith only [hη]
  have hbox : ∀ ρ, ρ ∈ dirichletCompletedLFunctionRectangleBox z w → ‖ρ - center‖ ≤ η / 4 := by
    intro ρ hρ
    rw [dirichletCompletedLFunctionRectangleBox, Rectangle.rectangleClosedBox,
      Complex.mem_reProdIm] at hρ
    have hreBox : ρ.re ∈ Set.uIcc (1 - η / 8) (1 + η / 8) := by
      simpa only [z, w, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.ofReal_im, zero_mul, sub_zero, mul_zero, sub_self, add_zero] using hρ.1
    have himBox : ρ.im ∈ Set.uIcc (t - η / 8) (t + η / 8) := by
      simpa only [z, w, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
        Complex.I_im, Complex.ofReal_re, zero_mul, mul_one, one_mul, add_zero, zero_add] using hρ.2
    have hre : 1 - η / 8 ≤ ρ.re ∧ ρ.re ≤ 1 + η / 8 := by
      rcases Set.mem_uIcc.mp hreBox with hcase | hcase
      · exact hcase
      · constructor <;> linarith only [hRealEnds, hcase.1, hcase.2]
    have him : t - η / 8 ≤ ρ.im ∧ ρ.im ≤ t + η / 8 := by
      rcases Set.mem_uIcc.mp himBox with hcase | hcase
      · exact hcase
      · constructor <;> linarith only [hRealEnds, hcase.1, hcase.2]
    have hreAbs : |ρ.re - 1| ≤ η / 8 := by
      rw [abs_le]
      constructor <;> linarith only [hre.1, hre.2]
    have himAbs : |ρ.im - t| ≤ η / 8 := by
      rw [abs_le]
      constructor <;> linarith only [him.1, him.2]
    have hdecomp : ρ - center = ((ρ.re - 1 : ℝ) : ℂ) + Complex.I * ((ρ.im - t : ℝ) : ℂ) := by
      apply Complex.ext
      · simp only [center, Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
          Complex.mul_re, Complex.I_re, Complex.one_re, Complex.I_im, zero_mul, sub_zero, mul_zero,
          add_zero]
      · simp only [center, Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
          Complex.I_re, Complex.I_im, Complex.one_im, Complex.ofReal_re, zero_mul, mul_one, one_mul,
          add_zero, zero_add]
    calc
      ‖ρ - center‖ = ‖((ρ.re - 1 : ℝ) : ℂ) + Complex.I * ((ρ.im - t : ℝ) : ℂ)‖ := by rw [hdecomp]
      _ ≤ ‖((ρ.re - 1 : ℝ) : ℂ)‖ + ‖Complex.I * ((ρ.im - t : ℝ) : ℂ)‖ := norm_add_le _ _
      _ = |ρ.re - 1| + |ρ.im - t| := by
        simp only [Complex.norm_real, Real.norm_eq_abs, Complex.norm_mul, Complex.norm_I, one_mul]
      _ ≤ η / 8 + η / 8 := add_le_add hreAbs himAbs
      _ = η / 4 := by ring
  simpa only [t] using
    (calc
      (((completedZeroMultiplicityOccurrences χ hχ ((σ : ℂ) - (n : ℝ) * Complex.I)
                    ((1 : ℂ) + (n : ℝ) * Complex.I)).filter
                (fun x => heightWindowGridIncidence (fun y => y.1.im) M K x m = true)).card :
            ℝ) ≤
          completedZeroMultiplicityCountInRectangle χ hχ z w :=
        by
        simpa only [t, z, w] using
          completedZeroMultiplicityOccurrences_window_filter_card_le_local_count χ hχ hσ1 hσ hη n M
            K hwindow m
      _ ≤ completedZeroLocalLogBoundConstant * (1 + η * Real.log ((q : ℝ) * (|t| + 3))) :=
        completedZeroMultiplicityCountInRectangle_le_uniform_local_log_bound hq hχ hprim hinv hη hη1
          z w hbox)

set_option maxHeartbeats 1000000 in
-- The local fiber estimate unfolds nested zero-occurrence finsets and needs the larger budget.
open Classical in
/--
Inputs: a fixed primitive character, its zero-occurrence height window, and a detector that assigns
an order-dependent threshold to every occurrence.
Claim: the window fiber is at most its local multiplicity bound times the number of derivative
orders whose values exceed their assigned thresholds at the grid point.
Proof: if the fiber is nonempty, detect one occurrence to activate one order; bound the whole
fiber by the unconditional local multiplicity estimate. The empty case is immediate.
Role: transfers multiplicity-preserving zero incidence to a sum of derivative large-value events.
-/
theorem primitiveCharacter_zero_window_fiber_le_detector_order_count {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) (hinv : χ⁻¹ ≠ 1) {σ η : ℝ}
    (R : ℕ → ℝ) (hσ1 : σ ≤ 1) (hσeta : 1 - σ ≤ η) (hη : 0 < η) (hηsmall : η ≤ 1 / 1288)
    (T nmax M K : ℕ) (hwindow : (K + 1 : ℝ) / M ≤ η)
    (hdetector :
      ∀
        x ∈
          completedZeroMultiplicityOccurrences χ hχ ((σ : ℂ) - (T : ℝ) * Complex.I)
            ((1 : ℂ) + (T : ℝ) * Complex.I),
        ∃ n : ℕ,
          n ≤ nmax ∧
            ∀ j : ℤ,
              |x.1.im - (j : ℝ) / M| ≤ (K + 1 : ℝ) / M →
                R n ≤
                  ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ))
                      (((1 + η : ℝ) : ℂ) + Complex.I * (((j : ℝ) / M : ℝ) : ℂ))‖)
    (m : ℤ) :
    ((completedZeroMultiplicityOccurrences χ hχ ((σ : ℂ) - (T : ℝ) * Complex.I)
              ((1 : ℂ) + (T : ℝ) * Complex.I)).filter
          (fun x => heightWindowGridIncidence (fun y => y.1.im) M K x m = true)).card ≤
      Nat.ceil
          (completedZeroLocalLogBoundConstant *
            (1 + 8 * η * Real.log ((q : ℝ) * (|((m : ℝ) / M)| + 3)))) *
        (∑ n ∈ Finset.range (nmax + 1),
          if
              R n ≤
                ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ))
                    (((1 + η : ℝ) : ℂ) + Complex.I * (((m : ℝ) / M : ℝ) : ℂ))‖ then
            1
          else 0) := by
  classical
  let occ :=
    completedZeroMultiplicityOccurrences χ hχ ((σ : ℂ) - (T : ℝ) * Complex.I)
      ((1 : ℂ) + (T : ℝ) * Complex.I)
  let fiber := occ.filter fun x => heightWindowGridIncidence (fun y => y.1.im) M K x m = true
  let weight :=
    completedZeroLocalLogBoundConstant * (1 + 8 * η * Real.log ((q : ℝ) * (|((m : ℝ) / M)| + 3)))
  have hηlocal : 0 < 8 * η := by positivity
  have hηlocalSmall : 8 * η ≤ 1 / 2 := by nlinarith only [hηsmall]
  have hwindowLocal : (K + 1 : ℝ) / M ≤ (8 * η) / 8 := by
    simpa only [mul_div_cancel_left₀ η (by norm_num : (8 : ℝ) ≠ 0)] using hwindow
  have hσlocal : 1 - σ ≤ (8 * η) / 8 := by nlinarith only [hσeta]
  have hlocal :=
    primitiveCharacter_zero_window_fiber_le_local_log_bound hq χ hχ hprim hinv hσ1 hσlocal hηlocal
      hηlocalSmall T M K hwindowLocal m
  have hfiberReal : (fiber.card : ℝ) ≤ weight := by
    simpa only [fiber, occ, weight, mul_assoc] using hlocal
  have hfiberNat : fiber.card ≤ Nat.ceil weight := by
    have hceil : (fiber.card : ℝ) ≤ (Nat.ceil weight : ℝ) := hfiberReal.trans (Nat.le_ceil weight)
    exact_mod_cast hceil
  change
    fiber.card ≤
      Nat.ceil weight *
        (∑ n ∈ Finset.range (nmax + 1),
          if
              R n ≤
                ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ))
                    (((1 + η : ℝ) : ℂ) + Complex.I * (((m : ℝ) / M : ℝ) : ℂ))‖ then
            1
          else 0)
  by_cases hpos : 0 < fiber.card
  · obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
    obtain ⟨n, hn, hgrid⟩ := hdetector x (Finset.mem_filter.mp hx).1
    have hinc := (Finset.mem_filter.mp hx).2
    unfold heightWindowGridIncidence at hinc
    split at hinc
    · rename_i hdist
      have hnmem : n ∈ Finset.range (nmax + 1) := by
        simp only [Finset.mem_range]
        omega
      have hterm :
        (if
              R n ≤
                ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ))
                    (((1 + η : ℝ) : ℂ) + Complex.I * (((m : ℝ) / M : ℝ) : ℂ))‖ then
            1
          else 0) =
          1 := by
        simp only [hgrid m hdist, ↓reduceIte]
      have hsum :
        1 ≤
          ∑ n ∈ Finset.range (nmax + 1),
            if
                R n ≤
                  ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ))
                      (((1 + η : ℝ) : ℂ) + Complex.I * (((m : ℝ) / M : ℝ) : ℂ))‖ then
              1
            else 0 := by
        calc
          1 =
              if
                  R n ≤
                    ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ))
                        (((1 + η : ℝ) : ℂ) + Complex.I * (((m : ℝ) / M : ℝ) : ℂ))‖ then
                1
              else 0 :=
            hterm.symm
          _ ≤ _ :=
            Finset.single_le_sum (s := Finset.range (nmax + 1)) (f := fun k =>
              if
                  R k ≤
                    ‖iteratedDeriv k (logDeriv (DirichletCharacter.LFunction χ))
                        (((1 + η : ℝ) : ℂ) + Complex.I * (((m : ℝ) / M : ℝ) : ℂ))‖ then
                1
              else 0)
              (fun k hk => by split_ifs <;> omega) hnmem
      calc
        fiber.card ≤ Nat.ceil weight := hfiberNat
        _ ≤ Nat.ceil weight * _ := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left _ hsum
    · simp only [Bool.false_eq_true] at hinc
  · have hcard : fiber.card = 0 := Nat.eq_zero_of_not_pos hpos
    simp only [hcard, Nat.zero_le]

set_option maxHeartbeats 1000000 in
-- Incidence counting composes the local fiber estimate with the expanded grid bound.
open Classical in
/--
Inputs: a primitive nonprincipal character, a bounded zero-occurrence window, a detector order
bound, and a height mesh whose width is at most the near-one scale.
Claim: the number of occurrences times the number of grid points in each occurrence window is at
most the sum over the expanded grid of a local multiplicity weight times the derivative-order
large-value count.
Proof: each occurrence contributes at least `2*K+1` incidences; at each grid point, bound the
fiber by the local multiplicity estimate and the detector-order count, then double-count incidences.
Role: transfers multiplicity-preserving zero incidence to a weighted finite family of derivative
large-value events.
-/
theorem primitiveCharacter_zero_occurrences_window_mul_le_detector_order_sum {q : ℕ} [NeZero q]
    (hq : 2 ≤ q) (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) (hinv : χ⁻¹ ≠ 1)
    {σ η : ℝ} (R : ℕ → ℝ) (hσ1 : σ ≤ 1) (hσeta : 1 - σ ≤ η) (hη : 0 < η) (hηsmall : η ≤ 1 / 1288)
    (T nmax M K : ℕ) (hM : 0 < M) (hwindow : (K + 1 : ℝ) / M ≤ η)
    (hdetector :
      ∀
        x ∈
          completedZeroMultiplicityOccurrences χ hχ ((σ : ℂ) - (T : ℝ) * Complex.I)
            ((1 : ℂ) + (T : ℝ) * Complex.I),
        ∃ n : ℕ,
          n ≤ nmax ∧
            ∀ j : ℤ,
              |x.1.im - (j : ℝ) / M| ≤ (K + 1 : ℝ) / M →
                R n ≤
                  ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ))
                      (((1 + η : ℝ) : ℂ) + Complex.I * (((j : ℝ) / M : ℝ) : ℂ))‖) :
    (completedZeroMultiplicityOccurrences χ hχ ((σ : ℂ) - (T : ℝ) * Complex.I)
            ((1 : ℂ) + (T : ℝ) * Complex.I)).card *
        (2 * K + 1) ≤
      ∑ m ∈ Finset.Icc (-(T * M : ℤ) - (K + 1 : ℤ)) ((T * M : ℤ) + (K + 1 : ℤ)),
        Nat.ceil
            (completedZeroLocalLogBoundConstant *
              (1 + 8 * η * Real.log ((q : ℝ) * (|((m : ℝ) / M)| + 3)))) *
          (∑ n ∈ Finset.range (nmax + 1),
            if
                R n ≤
                  ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ))
                      (((1 + η : ℝ) : ℂ) + Complex.I * (((m : ℝ) / M : ℝ) : ℂ))‖ then
              1
            else 0) := by
  let occ :=
    completedZeroMultiplicityOccurrences χ hχ ((σ : ℂ) - (T : ℝ) * Complex.I)
      ((1 : ℂ) + (T : ℝ) * Complex.I)
  let height :
    (Σ ρ : ℂ, Fin (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ)) → ℝ := fun x =>
    x.1.im
  let grid := Finset.Icc (-(T * M : ℤ) - (K + 1 : ℤ)) ((T * M : ℤ) + (K + 1 : ℤ))
  let incidence := fun x m => heightWindowGridIncidence height M K x m
  let fiberBound : ℤ → ℕ := fun m =>
    Nat.ceil
        (completedZeroLocalLogBoundConstant *
          (1 + 8 * η * Real.log ((q : ℝ) * (|((m : ℝ) / M)| + 3)))) *
      (∑ n ∈ Finset.range (nmax + 1),
        if
            R n ≤
              ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ))
                  (((1 + η : ℝ) : ℂ) + Complex.I * (((m : ℝ) / M : ℝ) : ℂ))‖ then
          1
        else 0)
  have hheight : ∀ x ∈ occ, -(T : ℝ) ≤ height x ∧ height x ≤ T := by
    intro x hx
    exact completedZeroMultiplicityOccurrences_height_mem χ hχ σ T hx
  have hlower := window_grid_incidence_card_lower_bound occ height T M K hM hheight
  have hupper : ∀ m ∈ grid, (occ.filter fun x => incidence x m = true).card ≤ fiberBound m := by
    intro m hm
    simpa only [occ, height, incidence, fiberBound] using
      primitiveCharacter_zero_window_fiber_le_detector_order_count hq χ hχ hprim hinv R hσ1 hσeta hη
        hηsmall T nmax M K hwindow hdetector m
  have hcount :=
    card_mul_le_sum_window_fiber_bounds occ grid incidence (2 * K + 1) fiberBound hlower hupper
  simpa only [occ, grid, incidence, height, fiberBound] using hcount

set_option maxHeartbeats 1000000 in
-- Summation over the family only unfolds finite sums and preserves each occurrence index.
open Classical in
/--
Inputs: a shared detector on the primitive-family occurrence ledger and a height mesh of width at
most the near-one scale.
Claim: the family occurrence count times the window-incidence gain is bounded by a conductor,
character, and grid sum of local multiplicity weights times derivative-order event counts.
Proof: apply the fixed-character incidence estimate in each nonprincipal primitive branch, using
ledger membership to obtain its detector, then sum the finite inequalities over conductors and
characters.
Role: aggregates the multiplicity-preserving incidence estimate at the family level before the
global cutoff bounds its local weights.
-/
theorem primitiveCharacterFamilyZeroOccurrenceCount_mul_window_size_le_derivative_order_sum (Q : ℕ)
    {σ η : ℝ} (R : ℕ → ℝ) (hσ1 : σ ≤ 1) (hσeta : 1 - σ ≤ η) (hη : 0 < η) (hηsmall : η ≤ 1 / 1288)
    (T nmax M K : ℕ) (hM : 0 < M) (hwindow : (K + 1 : ℝ) / M ≤ η)
    (hdetector :
      ∀
        {x :
          Σ q : Fin Q,
            Σ χ : DirichletCharacter ℂ (q.val + 1),
              Σ ρ : ℂ, Fin (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ)},
        x ∈ primitiveCharacterFamilyZeroOccurrenceLedger Q σ T →
          ∃ n : ℕ,
            n ≤ nmax ∧
              ∀ j : ℤ,
                |x.2.2.1.im - (j : ℝ) / M| ≤ (K + 1 : ℝ) / M →
                  R n ≤
                    ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction x.2.1))
                        (((1 + η : ℝ) : ℂ) + Complex.I * (((j : ℝ) / M : ℝ) : ℂ))‖) :
    primitiveCharacterFamilyZeroOccurrenceCountAtNatHeight Q σ T * (2 * K + 1 : ℝ) ≤
      ∑ q : Fin Q,
        ∑ χ : DirichletCharacter ℂ (q.val + 1),
          if _hχ : χ ≠ 1 then
            if _hprim : χ.IsPrimitive then
              ∑ m ∈ Finset.Icc (-(T * M : ℤ) - (K + 1 : ℤ)) ((T * M : ℤ) + (K + 1 : ℤ)),
                (Nat.ceil
                    (completedZeroLocalLogBoundConstant *
                        (1 + 8 * η * Real.log (((q.val + 1 : ℕ) : ℝ) * (|((m : ℝ) / M)| + 3))) :
                      ℝ) *
                  (∑ n ∈ Finset.range (nmax + 1),
                    if
                        R n ≤
                          ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ))
                              (((1 + η : ℝ) : ℂ) + Complex.I * (((m : ℝ) / M : ℝ) : ℂ))‖ then
                      (1 : ℝ)
                    else 0))
            else 0
          else 0 := by
  unfold primitiveCharacterFamilyZeroOccurrenceCountAtNatHeight
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro q hqmem
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro χ hχmem
  by_cases hχ : χ ≠ 1
  · by_cases hprim : χ.IsPrimitive
    · simp only [dite_eq_left hχ, dite_eq_left hprim]
      have hmod : 2 ≤ q.val + 1 := by
        by_contra hmod
        have hqzero : q.val = 0 := by omega
        have hqone : q.val + 1 = 1 := by omega
        have hsub : Subsingleton (DirichletCharacter ℂ (q.val + 1)) := by
          rw [hqone]
          exact (inferInstance : Subsingleton (DirichletCharacter ℂ 1))
        exact hχ (hsub.elim χ 1)
      have hneZero : NeZero (q.val + 1) := ⟨Nat.ne_of_gt (by omega)⟩
      have hinv : χ⁻¹ ≠ 1 := by
        intro hinv
        exact hχ (inv_eq_one.mp hinv)
      have hdetectorChar :
        ∀
          x ∈
            completedZeroMultiplicityOccurrences χ hχ ((σ : ℂ) - (T : ℝ) * Complex.I)
              ((1 : ℂ) + (T : ℝ) * Complex.I),
          ∃ n : ℕ,
            n ≤ nmax ∧
              ∀ j : ℤ,
                |x.1.im - (j : ℝ) / M| ≤ (K + 1 : ℝ) / M →
                  R n ≤
                    ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ))
                        (((1 + η : ℝ) : ℂ) + Complex.I * (((j : ℝ) / M : ℝ) : ℂ))‖ := by
        intro x hx
        let event :
          Σ q : Fin Q,
            Σ χ : DirichletCharacter ℂ (q.val + 1),
              Σ ρ : ℂ, Fin (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ) :=
          ⟨q, ⟨χ, x⟩⟩
        have hxledger : event ∈ primitiveCharacterFamilyZeroOccurrenceLedger Q σ T := by
          simp only [event, primitiveCharacterFamilyZeroOccurrenceLedger, Finset.mem_sigma,
            Finset.mem_univ, dite_eq_left hχ, dite_eq_left hprim]
          exact ⟨trivial, trivial, hx⟩
        obtain ⟨n, hn, hgrid⟩ := hdetector hxledger
        refine ⟨n, hn, ?_⟩
        intro j hj
        simpa only [event] using hgrid j hj
      have hchar :=
        @primitiveCharacter_zero_occurrences_window_mul_le_detector_order_sum (q.val + 1) hneZero
          hmod χ hχ hprim hinv σ η R hσ1 hσeta hη hηsmall T nmax M K hM hwindow hdetectorChar
      exact_mod_cast hchar
    · simp only [dite_eq_left hχ, dite_eq_right hprim, zero_mul]
      exact le_rfl
  · simp only [dite_eq_right hχ, zero_mul]
    exact le_rfl

/--
Inputs: a conductor cutoff and the local-scale, height-grid, and real-part hypotheses for the
primitive zero-occurrence ledger.
Claim: its total local-window occurrence count is bounded by the absolute local logarithmic
constant times the explicit sum of `1 + η * log(q * (|m/M| + 3))` over primitive nonprincipal
characters and grid points.
Proof: apply the uniform rectangle-count bound at each character and grid point, then sum the
pointwise inequalities over the finite family.
Role: makes the local multiplicity contribution available as a finite family quantity.
-/
theorem primitiveCharacterFamilyLocalWindowOccurrenceCount_le_log_weight_sum (Q : ℕ) (η : ℝ)
    (hη : 0 < η) (hη1 : η ≤ 1 / 2) (n M K : ℕ) :
    primitiveCharacterFamilyLocalWindowOccurrenceCount Q η n M K ≤
      completedZeroLocalLogBoundConstant *
        primitiveCharacterFamilyLocalWindowLogWeightSum Q η n M K := by
  classical
  let grid : Finset ℤ := Finset.Icc (-(n * M : ℤ) - (K + 1 : ℤ)) ((n * M : ℤ) + (K + 1 : ℤ))
  unfold primitiveCharacterFamilyLocalWindowOccurrenceCount
    primitiveCharacterFamilyLocalWindowLogWeightSum
  change
    (∑ q : Fin Q,
        ∑ χ : DirichletCharacter ℂ (q.val + 1),
          if hχ : χ ≠ 1 then
            if hprim : χ.IsPrimitive then
              ∑ m ∈ grid,
                ((completedZeroMultiplicityOccurrences χ hχ
                      (((1 - η / 8 : ℝ) : ℂ) + Complex.I * (((m : ℝ) / M - η / 8 : ℝ) : ℂ))
                      (((1 + η / 8 : ℝ) : ℂ) + Complex.I * (((m : ℝ) / M + η / 8 : ℝ) : ℂ))).card :
                  ℝ)
            else 0
          else 0) ≤
      completedZeroLocalLogBoundConstant *
        (∑ q : Fin Q,
          ∑ χ : DirichletCharacter ℂ (q.val + 1),
            if hχ : χ ≠ 1 then
              if hprim : χ.IsPrimitive then
                ∑ m ∈ grid, (1 + η * Real.log (((q.val + 1 : ℕ) : ℝ) * (|((m : ℝ) / M)| + 3)))
              else 0
            else 0)
  calc
    _ ≤
        ∑ q : Fin Q,
          ∑ χ : DirichletCharacter ℂ (q.val + 1),
            if hχ : χ ≠ 1 then
              if hprim : χ.IsPrimitive then
                ∑ m ∈ grid,
                  completedZeroLocalLogBoundConstant *
                    (1 + η * Real.log (((q.val + 1 : ℕ) : ℝ) * (|((m : ℝ) / M)| + 3)))
              else 0
            else 0 :=
      by
      apply Finset.sum_le_sum
      intro q hqmem
      apply Finset.sum_le_sum
      intro χ hχmem
      by_cases hχ : χ ≠ 1
      · by_cases hprim : χ.IsPrimitive
        · simp only [dite_eq_left hχ, dite_eq_left hprim]
          have hmod : 2 ≤ q.val + 1 := by
            by_contra hmod
            have hqzero : q.val = 0 := by omega
            have hqone : q.val + 1 = 1 := by omega
            have hsub : Subsingleton (DirichletCharacter ℂ (q.val + 1)) := by
              rw [hqone]
              exact (inferInstance : Subsingleton (DirichletCharacter ℂ 1))
            exact hχ (hsub.elim χ 1)
          have hinv : χ⁻¹ ≠ 1 := by
            intro hinv
            apply hχ
            exact inv_eq_one.mp hinv
          apply Finset.sum_le_sum
          intro m hm
          let t : ℝ := (m : ℝ) / M
          let z : ℂ := ((1 - η / 8 : ℝ) : ℂ) + Complex.I * ((t - η / 8 : ℝ) : ℂ)
          let w : ℂ := ((1 + η / 8 : ℝ) : ℂ) + Complex.I * ((t + η / 8 : ℝ) : ℂ)
          have hbox := heightWindowRectangle_norm_le η t hη
          have hlocal :=
            completedZeroMultiplicityCountInRectangle_le_uniform_local_log_bound hmod hχ hprim hinv
              hη hη1 z w (by simpa only [t, z, w] using hbox)
          have hcard := completedZeroMultiplicityCountInRectangle_eq_occurrence_card χ hχ z w
          calc
            ((completedZeroMultiplicityOccurrences χ hχ z w).card : ℝ) =
                completedZeroMultiplicityCountInRectangle χ hχ z w :=
              hcard.symm
            _ ≤
                completedZeroLocalLogBoundConstant *
                  (1 + η * Real.log ((q.val + 1 : ℕ) * (|t| + 3))) :=
              by exact hlocal
        · simp only [dite_eq_left hχ, dite_eq_right hprim]
          exact le_rfl
      · simp only [dite_eq_right hχ]
        exact le_rfl
    _ =
        completedZeroLocalLogBoundConstant *
          (∑ q : Fin Q,
            ∑ χ : DirichletCharacter ℂ (q.val + 1),
              if hχ : χ ≠ 1 then
                if hprim : χ.IsPrimitive then
                  ∑ m ∈ grid, (1 + η * Real.log (((q.val + 1 : ℕ) : ℝ) * (|((m : ℝ) / M)| + 3)))
                else 0
              else 0) :=
      by simp only [Finset.mul_sum, mul_dite, mul_zero]

/--
Inputs: the hypotheses for the family height-window incidence bound and the local logarithmic
scale.
Claim: the multiplicity-preserving zero-occurrence count, multiplied by the number of grid
windows covering each occurrence, is bounded by the absolute local constant times the explicit
family logarithmic window sum.
Proof: compose the ledger incidence inequality with the uniform local-window majorant.
Role: supplies the local-count side of the later zero-detection and hybrid large-sieve comparison.
-/
theorem primitiveCharacterFamilyZeroOccurrenceCount_mul_window_size_le_log_weight_sum (Q : ℕ)
    {σ η : ℝ} (hσ1 : σ ≤ 1) (hσ : 1 - σ ≤ η / 8) (hη : 0 < η) (hη1 : η ≤ 1 / 2) (n M K : ℕ)
    (hM : 0 < M) (hwindow : (K + 1 : ℝ) / M ≤ η / 8) :
    primitiveCharacterFamilyZeroOccurrenceCountAtNatHeight Q σ n * (2 * K + 1 : ℝ) ≤
      completedZeroLocalLogBoundConstant *
        primitiveCharacterFamilyLocalWindowLogWeightSum Q η n M K := by
  calc
    _ ≤ primitiveCharacterFamilyLocalWindowOccurrenceCount Q η n M K :=
      primitiveCharacterFamilyZeroOccurrenceCount_mul_window_size_le_local_window_sum Q hσ1 hσ hη n
        M K hM hwindow
    _ ≤
        completedZeroLocalLogBoundConstant *
          primitiveCharacterFamilyLocalWindowLogWeightSum Q η n M K :=
      primitiveCharacterFamilyLocalWindowOccurrenceCount_le_log_weight_sum Q η hη hη1 n M K

/--
Inputs: a modulus, a finite set of derivative orders, a rational height grid, and a threshold.

Claim: the number of primitive characters whose derivative exceeds the threshold at some order
and grid point is at most the sum of the corresponding single-order, single-point counts.

Proof: include the existentially defined set in the finite union of its order-height blocks, then
apply the cardinality bound for finite unions and expand the product sum.

Role: prepares variable Turán orders and discretized zero heights for the family large-sieve bound.
-/
theorem primitiveCharacterDerivativeLargeSet_union_count_le_grid_sum (q Nmax T M : ℕ) [NeZero q]
    (hq : 1 < q) (σ R : ℝ) :
    ((primitiveDirichletCharacterSet q).filter fun χ ↦
          ∃ n ∈ Finset.range Nmax,
            ∃ m ∈ Finset.Icc (-(T * M : ℤ)) (T * M : ℤ),
              R ≤
                ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ))
                    ((σ : ℂ) + Complex.I * (((m : ℝ) / (M : ℝ) : ℝ) : ℂ))‖).card ≤
      ∑ n ∈ Finset.range Nmax,
        ∑ m ∈ Finset.Icc (-(T * M : ℤ)) (T * M : ℤ),
          (primitiveCharacterDerivativeLargeSet q hq n
              ((σ : ℂ) + Complex.I * (((m : ℝ) / (M : ℝ) : ℝ) : ℂ)) R).card := by
  classical
  let grid : Finset ℤ := Finset.Icc (-(T * M : ℤ)) (T * M : ℤ)
  let pairs : Finset (ℕ × ℤ) := (Finset.range Nmax).product grid
  let point : ℤ → ℂ := fun m ↦ (σ : ℂ) + Complex.I * (((m : ℝ) / (M : ℝ) : ℝ) : ℂ)
  let blocks : ℕ × ℤ → Finset (DirichletCharacter ℂ q) := fun p ↦
    primitiveCharacterDerivativeLargeSet q hq p.1 (point p.2) R
  let bad : Finset (DirichletCharacter ℂ q) :=
    (primitiveDirichletCharacterSet q).filter fun χ ↦
      ∃ n ∈ Finset.range Nmax,
        ∃ m ∈ grid, R ≤ ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) (point m)‖
  have hsub : bad ⊆ pairs.biUnion blocks := by
    intro χ hχ
    rcases Finset.mem_filter.mp hχ with ⟨hprimitive, n, hn, m, hm, hlarge⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨(n, m), Finset.mem_product.mpr ⟨hn, hm⟩, ?_⟩
    simpa only [blocks, point, primitiveCharacterDerivativeLargeSet, Finset.mem_filter] using
      And.intro hprimitive hlarge
  calc
    _ = bad.card := by rfl
    _ ≤ (pairs.biUnion blocks).card := Finset.card_le_card hsub
    _ ≤ ∑ p ∈ pairs, (blocks p).card := Finset.card_biUnion_le
    _ =
        ∑ n ∈ Finset.range Nmax,
          ∑ m ∈ grid, (primitiveCharacterDerivativeLargeSet q hq n (point m) R).card :=
      by
      change (∑ p ∈ (Finset.range Nmax) ×ˢ grid, (blocks p).card) = _
      rw [Finset.sum_product]
    _ = _ := by simp only [grid, point]

/--
Inputs: a modulus cutoff, finite derivative-order range, rational height grid, and threshold.

Claim: the total number of primitive characters up to the modulus cutoff detected at some order
and grid point is bounded by the sum of the family large counts over all order-height pairs.

Proof: apply `primitiveCharacterDerivativeLargeSet_union_count_le_grid_sum` at each modulus,
then interchange the finite sums over moduli, orders, and grid points.

Role: combines the discretized local detection with the family large-sieve estimates.
-/
theorem primitiveCharacterDerivativeFamily_union_count_le_grid_sum (Qmax Nmax T M : ℕ) (σ R : ℝ) :
    (∑ q ∈ (Finset.Ioc 1 Qmax).attach,
        (fun q ↦ by
            letI : NeZero q.val :=
              ⟨Nat.ne_of_gt (lt_trans Nat.zero_lt_one (Finset.mem_Ioc.mp q.property).1)⟩
            exact
              (((primitiveDirichletCharacterSet q.val).filter fun χ ↦
                    ∃ n ∈ Finset.range Nmax,
                      ∃ m ∈ Finset.Icc (-(T * M : ℤ)) (T * M : ℤ),
                        R ≤
                          ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ))
                              ((σ : ℂ) + Complex.I * (((m : ℝ) / (M : ℝ) : ℝ) : ℂ))‖).card :
                ℝ))
          q) ≤
      ∑ n ∈ Finset.range Nmax,
        ∑ m ∈ Finset.Icc (-(T * M : ℤ)) (T * M : ℤ),
          primitiveCharacterDerivativeFamilyLargeCount Qmax n
            ((σ : ℂ) + Complex.I * (((m : ℝ) / (M : ℝ) : ℝ) : ℂ)) R := by
  classical
  let grid : Finset ℤ := Finset.Icc (-(T * M : ℤ)) (T * M : ℤ)
  let point : ℤ → ℂ := fun m ↦ (σ : ℂ) + Complex.I * (((m : ℝ) / (M : ℝ) : ℝ) : ℂ)
  let badCount : (q : ↥(Finset.Ioc 1 Qmax)) → ℝ := fun q ↦ by
    letI : NeZero q.val :=
      ⟨Nat.ne_of_gt (lt_trans Nat.zero_lt_one (Finset.mem_Ioc.mp q.property).1)⟩
    exact
      (((primitiveDirichletCharacterSet q.val).filter fun χ ↦
            ∃ n ∈ Finset.range Nmax,
              ∃ m ∈ grid,
                R ≤ ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) (point m)‖).card :
        ℝ)
  calc
    _ ≤
        ∑ q ∈ (Finset.Ioc 1 Qmax).attach,
          ∑ n ∈ Finset.range Nmax,
            ∑ m ∈ grid,
              ((primitiveCharacterDerivativeLargeSet q.val (Finset.mem_Ioc.mp q.property).1 n
                    (point m) R).card :
                ℝ) :=
      by
      apply Finset.sum_le_sum
      intro q hqmem
      let hq : 1 < q.val := (Finset.mem_Ioc.mp q.property).1
      have hqne : NeZero q.val := ⟨Nat.ne_of_gt (lt_trans Nat.zero_lt_one hq)⟩
      simpa only [grid, point, Nat.cast_sum] using
        ((Nat.cast_le (α := ℝ)).mpr
          (@primitiveCharacterDerivativeLargeSet_union_count_le_grid_sum q.val Nmax T M hqne hq σ
            R))
    _ =
        ∑ n ∈ Finset.range Nmax,
          ∑ q ∈ (Finset.Ioc 1 Qmax).attach,
            ∑ m ∈ grid,
              ((primitiveCharacterDerivativeLargeSet q.val (Finset.mem_Ioc.mp q.property).1 n
                    (point m) R).card :
                ℝ) :=
      by exact Finset.sum_comm
    _ =
        ∑ n ∈ Finset.range Nmax,
          ∑ m ∈ grid,
            ∑ q ∈ (Finset.Ioc 1 Qmax).attach,
              ((primitiveCharacterDerivativeLargeSet q.val (Finset.mem_Ioc.mp q.property).1 n
                    (point m) R).card :
                ℝ) :=
      by
      apply Finset.sum_congr rfl
      intro n hn
      exact Finset.sum_comm
    _ = _ := by simp only [grid, point, primitiveCharacterDerivativeFamilyLargeCount]

/--
Inputs: a modulus cutoff, derivative order, finite series cutoff, a point with real part at least
`σ > 1`, and an explicit truncation error at most `R/2`.

Claim: the derivative family count times `(R/2)^2` is bounded by the additive large-sieve bound
for the truncated von Mangoldt polynomial's coefficient energy, with no factor for the number of
moduli.

Proof: apply the per-modulus set inclusion, sum its cardinality bound, and invoke the additive
large-sieve large-value estimate for support below `cutoff + 1`.

Role: gives the family large-value estimate needed to connect local zero detection to the
log-free density argument.
-/
theorem primitiveCharacterDerivativeFamilyLargeCount_mul_le_additive_large_sieve (Qmax cutoff n : ℕ)
    (hQ : 0 < Qmax) (hcutoff : 1 ≤ cutoff) {σ : ℝ} (hσ : 1 < σ) {s : ℂ} (hs : σ ≤ s.re) (R : ℝ)
    (hR : 0 < R)
    (herror :
      ((σ - 1) / (2 * ((n + 1 : ℕ) : ℝ))) ^ (-((n + 1 : ℕ) : ℝ)) * (cutoff : ℝ) ^ (-(σ - 1) / 2) /
          ((σ - 1) / 2) ≤
        R / 2) :
    primitiveCharacterDerivativeFamilyLargeCount Qmax n s R * (R / 2) ^ 2 ≤
      (2 * ((cutoff + 1 : ℕ) : ℝ) + 3 * ((Qmax * Qmax : ℕ) : ℝ)) *
        ∑ k ∈ Finset.range (cutoff + 1),
          ‖LSeries.term (LSeries.logMul^[n] (fun j : ℕ => (ArithmeticFunction.vonMangoldt j : ℂ))) s
                k‖ ^
            2 := by
  classical
  let support : Finset ℕ := Finset.range (cutoff + 1)
  let coeff : ℕ → ℂ := fun k =>
    LSeries.term (LSeries.logMul^[n] (fun j : ℕ => (ArithmeticFunction.vonMangoldt j : ℂ))) s k
  have hcount :
    (∑ q ∈ (Finset.Ioc 1 Qmax).attach,
        (primitiveCharacterDerivativeLargeSet q.val (Finset.mem_Ioc.mp q.property).1 n s R).card) ≤
      ∑ q ∈ (Finset.Ioc 1 Qmax).attach,
        (primitiveCharacterPolynomialLargeSet q.val n cutoff s ((R / 2) ^ 2)).card := by
    apply Finset.sum_le_sum
    intro q hq
    exact
      Finset.card_le_card
        (primitiveCharacterDerivativeLargeSet_subset_polynomialLargeSet q.val
          (Finset.mem_Ioc.mp q.property).1 n cutoff hcutoff σ hσ s hs R hR herror)
  have hcountR :
    primitiveCharacterDerivativeFamilyLargeCount Qmax n s R ≤
      ∑ q ∈ (Finset.Ioc 1 Qmax).attach,
        (primitiveCharacterPolynomialLargeSet q.val n cutoff s ((R / 2) ^ 2)).card := by
    unfold primitiveCharacterDerivativeFamilyLargeCount
    exact_mod_cast hcount
  have hlargeCount :=
    primitiveCharacterLargeValueCount_mul_le_additive_large_sieve_Ioc Qmax hQ (cutoff + 1) support
      (Finset.Subset.refl _) coeff ((R / 2) ^ 2)
  have hcounts :
    (∑ q ∈ (Finset.Ioc 1 Qmax).attach,
          ((primitiveCharacterPolynomialLargeSet q.val n cutoff s ((R / 2) ^ 2)).card : ℝ)) *
        ((R / 2) ^ 2) ≤
      (2 * ((cutoff + 1 : ℕ) : ℝ) + 3 * ((Qmax * Qmax : ℕ) : ℝ)) *
        ∑ k ∈ support, ‖coeff k‖ ^ 2 := by
    simpa only [primitiveCharacterPolynomialLargeSet, support, coeff, Real.norm_eq_abs] using
      hlargeCount
  calc
    _ ≤
        (∑ q ∈ (Finset.Ioc 1 Qmax).attach,
            (primitiveCharacterPolynomialLargeSet q.val n cutoff s ((R / 2) ^ 2)).card) *
          ((R / 2) ^ 2) :=
      mul_le_mul_of_nonneg_right hcountR (sq_nonneg (R / 2))
    _ ≤ _ := by simpa only [support, coeff, Nat.cast_sum] using hcounts

/--
Inputs: a real exponent greater than one, a derivative order, and a positive error tolerance.

Claim: some positive truncation cutoff makes the explicit differentiated Euler-tail bound smaller
than the tolerance.

Proof: the cutoff power has negative exponent, so its product with the fixed coefficient tends
to zero; choose a sufficiently large natural cutoff.

Role: discharges the truncation-error hypothesis in the family derivative large-value estimate.
-/
theorem exists_explicit_vonMangoldt_derivative_cutoff {σ ε : ℝ} (hσ : 1 < σ) (n : ℕ) (hε : 0 < ε) :
    ∃ cutoff : ℕ,
      1 ≤ cutoff ∧
        ((σ - 1) / (2 * ((n + 1 : ℕ) : ℝ))) ^ (-((n + 1 : ℕ) : ℝ)) * (cutoff : ℝ) ^ (-(σ - 1) / 2) /
            ((σ - 1) / 2) <
          ε := by
  let δ := (σ - 1) / 2
  let α := (σ - 1) / (2 * ((n + 1 : ℕ) : ℝ))
  let C := α ^ (-((n + 1 : ℕ) : ℝ)) / δ
  have hδ : 0 < δ := by
    dsimp only [δ]
    linarith only [hσ]
  have hpow : Filter.Tendsto (fun m : ℕ => (m : ℝ) ^ (-δ)) Filter.atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hδ).comp tendsto_natCast_atTop_atTop
  have hC : Filter.Tendsto (fun _ : ℕ => C) Filter.atTop (nhds C) := tendsto_const_nhds
  have hbound : Filter.Tendsto (fun m : ℕ => C * (m : ℝ) ^ (-δ)) Filter.atTop (nhds 0) := by
    simpa only [mul_zero] using hC.mul hpow
  have hsmall : ∀ᶠ m : ℕ in Filter.atTop, C * (m : ℝ) ^ (-δ) < ε :=
    hbound.eventually (Iio_mem_nhds hε)
  have hlarge : ∀ᶠ m : ℕ in Filter.atTop, 1 ≤ m := Filter.eventually_ge_atTop 1
  obtain ⟨cutoff, hcutoff, hcutoffPos⟩ := (hsmall.and hlarge).exists
  have hExplicitBound :
    α ^ (-((n + 1 : ℕ) : ℝ)) * (cutoff : ℝ) ^ (-(σ - 1) / 2) / ((σ - 1) / 2) < ε := by
    have heq :
      α ^ (-((n + 1 : ℕ) : ℝ)) * (cutoff : ℝ) ^ (-(σ - 1) / 2) / ((σ - 1) / 2) =
        C * (cutoff : ℝ) ^ (-δ) := by
      dsimp only [C, α, δ]
      have hexp : -(σ - 1) / 2 = -((σ - 1) / 2) := by ring
      rw [hexp]
      ring
    rw [heq]
    exact hcutoff
  refine ⟨cutoff, hcutoffPos, ?_⟩
  simpa only [α] using hExplicitBound

/--
Inputs: a modulus cutoff, derivative order, a point with real part greater than one, and a
positive derivative threshold.

Claim: there is a finite Euler cutoff for which the family count of large logarithmic derivatives
is bounded by the additive large-sieve coefficient energy, without a factor for the number of
moduli.

Proof: choose a cutoff making the explicit Euler-tail error less than half the threshold, then
apply `primitiveCharacterDerivativeFamilyLargeCount_mul_le_additive_large_sieve`.

Role: gives an unconditional finite-polynomial large-value bound for the derivative family at a
fixed point to the right of one.
-/
theorem exists_cutoff_primitiveCharacterDerivativeFamilyLargeCount_mul_le_additive_large_sieve
    (Qmax n : ℕ) (hQ : 0 < Qmax) {σ : ℝ} (hσ : 1 < σ) {s : ℂ} (hs : σ ≤ s.re) (R : ℝ) (hR : 0 < R) :
    ∃ cutoff : ℕ,
      1 ≤ cutoff ∧
        primitiveCharacterDerivativeFamilyLargeCount Qmax n s R * (R / 2) ^ 2 ≤
          (2 * ((cutoff + 1 : ℕ) : ℝ) + 3 * ((Qmax * Qmax : ℕ) : ℝ)) *
            ∑ k ∈ Finset.range (cutoff + 1),
              ‖LSeries.term
                    (LSeries.logMul^[n] (fun j : ℕ => (ArithmeticFunction.vonMangoldt j : ℂ))) s
                    k‖ ^
                2 := by
  obtain ⟨cutoff, hcutoff, herror⟩ :=
    exists_explicit_vonMangoldt_derivative_cutoff (ε := R / 2) hσ n (by linarith only [hR])
  exact
    ⟨cutoff, hcutoff,
      primitiveCharacterDerivativeFamilyLargeCount_mul_le_additive_large_sieve Qmax cutoff n hQ
        hcutoff hσ hs R hR (le_of_lt herror)⟩

/--
Inputs: a near-one scale, its smallness condition, and a requested minimum detector order.
Claim: one order bound, positive normalized threshold, and rational-height mesh work uniformly for
every primitive nonprincipal character and every completed-function zero satisfying the scaled
conductor-height bound; the mesh preserves the factor `η^(n+1)/n!` at each derivative order.
Proof: choose a single gamma-factor estimate, apply the fixed-gamma detector, and use the normalized
uniform Euler-series mesh theorem at the resulting common order and threshold.
Role: supplies common parameters for incidence counting without dropping the order normalization.
-/
theorem exists_uniform_mesh_for_completed_near_one_zero_family {η : ℝ} (hη : 0 < η)
    (hηsmall : η ≤ 1 / 1288) (Krequested : ℕ) (hKrequested : 2 ≤ Krequested) :
    ∃ Kmax nmax M : ℕ,
      ∃ B : ℝ,
        0 < B ∧
          0 < M ∧
          (Kmax + 1 : ℝ) / M ≤ η / 8 ∧
          ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q},
            2 ≤ q →
              χ ≠ 1 →
              χ.IsPrimitive →
              χ⁻¹ ≠ 1 →
              ∀ {ρ : ℂ},
                |ρ.re - 1| ≤ η →
                  DirichletCharacter.completedLFunction χ ρ = 0 →
                  DirichletCharacter.completedLFunction χ
                      (((1 + η : ℝ) : ℂ) + Complex.I * (ρ.im : ℂ)) ≠
                    0 →
                  η * Real.log ((q : ℝ) * (|ρ.im| + 3)) ≤ 3 →
                  ∃ n : ℕ,
                    n ≤ nmax ∧
                      ∀ j : ℤ,
                        |ρ.im - (j : ℝ) / M| ≤ (Kmax + 1 : ℝ) / M →
                          B / 2 ≤
                            (η ^ (n + 1) / (n.factorial : ℝ)) *
                              ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ))
                                  (((1 + η : ℝ) : ℂ) + Complex.I * (((j : ℝ) / M : ℝ) : ℂ))‖ := by
  obtain ⟨G, hG, hgamma⟩ := exists_uniform_gamma_subtraction_for_ordinary_LFunction_derivative_all
  let Kmax : ℕ :=
    max completedGenusRemoteTailUniformOrderBound
      (max (uniformGammaAbsorptionOrderCutoff G + 1) Krequested)
  let nmax : ℕ := Kmax * completedLFunctionNearOneDetectorMultiplicityCap
  let Mmin : ℕ := Nat.ceil (8 * (Kmax + 1 : ℝ) / η)
  let B : ℝ := Real.exp (-(ordinaryLFunctionNearOneDetectorExponent * (Kmax : ℝ)))
  have hB : 0 < B := by
    dsimp only [B]; positivity
  have hCapNonneg : 0 ≤ (completedLFunctionNearOneDetectorMultiplicityCap : ℝ) := by positivity
  have hLog3 : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  have hLogDen : 0 < Real.log (8 * ((completedLFunctionNearOneDetectorMultiplicityCap : ℝ) + 1)) :=
    Real.log_pos (by nlinarith only [hCapNonneg])
  have hLog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hExponent : 0 < ordinaryLFunctionNearOneDetectorExponent := by
    unfold ordinaryLFunctionNearOneDetectorExponent completedLFunctionNearOneDetectorExponent
    have hmul : 0 ≤ (completedLFunctionNearOneDetectorMultiplicityCap : ℝ) * Real.log 3 :=
      mul_nonneg hCapNonneg hLog3.le
    nlinarith only [hmul, hLogDen, hLog2]
  have hσ : 1 < 1 + η := by linarith only [hη]
  have hσsmall : (1 + η) - 1 ≤ 1 := by
    have hηone : η ≤ 1 := le_trans hηsmall (by norm_num)
    nlinarith only [hηone]
  obtain ⟨M, hMmin, hM, hmesh⟩ :=
    exists_uniform_mesh_for_normalized_vonMangoldt_log_weight_window hσ nmax Kmax Mmin hB
  have hwidth : (Kmax + 1 : ℝ) / M ≤ η / 8 := by
    apply (div_le_iff₀ (by exact_mod_cast hM : (0 : ℝ) < M)).2
    have hceil : 8 * (Kmax + 1 : ℝ) / η ≤ (M : ℝ) := by
      exact le_trans (Nat.le_ceil _) (Nat.cast_le.mpr hMmin)
    have hmul : 8 * (Kmax + 1 : ℝ) ≤ (M : ℝ) * η := (div_le_iff₀ hη).1 hceil
    nlinarith only [hmul]
  refine ⟨Kmax, nmax, M, B, hB, hM, hwidth, ?_⟩
  intro q hq χ hqbound hχ hprimitive hinv ρ hρre hzero hc hscale
  have hcre : ((((1 + η : ℝ) : ℂ) + Complex.I * (ρ.im : ℂ)).re = 1 + η) := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, sub_zero, mul_zero, add_zero]
  have hcim : ((((1 + η : ℝ) : ℂ) + Complex.I * (ρ.im : ℂ)).im = ρ.im) := by
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re]
    ring
  obtain
    ⟨massA, massB, hmassA, hmassB, Kmin, C, K, m, n, hKreq, hKremote, hKfixed, hKglobal, hKmin,
      hKtwo, hn, hnm, hmK, hmCap, hCeq, hnormPos, hnormalized⟩ :=
    exists_completedLFunction_positive_LFunction_logDeriv_iterate_with_fixed_gamma hqbound hχ
      hprimitive hinv hη hηsmall Krequested hKrequested hcre hcim hρre hzero hc hscale G hG hgamma
  have hKmax : K ≤ Kmax := by simpa only [Kmax] using hKglobal
  have hnmax : n ≤ nmax := by
    dsimp only [nmax]
    have hmul : m ≤ Kmax * completedLFunctionNearOneDetectorMultiplicityCap :=
      hmCap.trans (Nat.mul_le_mul_right _ hKmax)
    omega
  have hηeq : 1 + η - 1 = η := by ring
  have hnorm :
    B ≤
      ((1 + η - 1) ^ (n + 1) / (n.factorial : ℝ)) *
        ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ))
            (((1 + η : ℝ) : ℂ) + Complex.I * (ρ.im : ℂ))‖ := by
    dsimp only [B]
    rw [hηeq]
    have horder :
      -(ordinaryLFunctionNearOneDetectorExponent * (Kmax : ℝ)) ≤
        -(ordinaryLFunctionNearOneDetectorExponent * (K : ℝ)) := by
      have hKreal : (K : ℝ) ≤ (Kmax : ℝ) := by exact_mod_cast hKmax
      nlinarith only [hExponent, hKreal]
    have hsignal := Real.exp_le_exp.mpr horder
    exact le_trans hsignal hnormalized
  refine ⟨n, hnmax, ?_⟩
  intro j hj
  have hgrid := hmesh χ hχ (t := ρ.im) n hnmax hnorm j hj
  simpa only [hηeq] using hgrid

/-
Inputs: a global conductor-height cutoff, a nonnegative scale, and a finite modulus/height pair.
Claim: the global logarithmic bound implies the corresponding bound at every modulus and height.
Proof: bound each local conductor and height factor by the global factors, then use monotonicity of
the logarithm and multiplication by a nonnegative scale.
Role: converts the global cutoff hypothesis into the local hypothesis required by the detector.
-/
theorem eta_log_conductor_height_le_of_cutoff_bound {Q T : ℕ} (hQ : 0 < Q) {η : ℝ} (hη : 0 ≤ η)
    (hglobal : η * Real.log ((Q : ℝ) * ((T : ℝ) + 3)) ≤ 3) (q : Fin Q) {t : ℝ} (ht : |t| ≤ T) :
    η * Real.log (((q.val + 1 : ℕ) : ℝ) * (|t| + 3)) ≤ 3 := by
  have hqNat : q.val + 1 ≤ Q := by omega
  have hq : ((q.val + 1 : ℕ) : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hqNat
  have ht' : |t| + 3 ≤ (T : ℝ) + 3 := by
    have htcast : (|t| : ℝ) ≤ (T : ℝ) := by exact_mod_cast ht
    simpa only [add_comm] using add_le_add_right htcast 3
  have harg : ((q.val + 1 : ℕ) : ℝ) * (|t| + 3) ≤ (Q : ℝ) * ((T : ℝ) + 3) := by
    exact mul_le_mul hq ht' (by positivity) (by positivity)
  have hlog := Real.log_le_log (by positivity) harg
  exact (mul_le_mul_of_nonneg_left hlog hη).trans hglobal

/--
Inputs: a global conductor-height cutoff, a positive scale, a mesh-width bound, and a point in the
expanded integer height grid.
Claim: the local conductor-height logarithm at that grid point, multiplied by the scale, is at
most six.
Proof: the expanded grid gives `|m/M| ≤ T+1`; bound the local logarithm argument by the square of
the global argument, then apply the cutoff hypothesis.
Role: makes the local multiplicity weight uniformly bounded before summing derivative events.
-/
theorem eta_log_conductor_expanded_height_le_six {Q T M K : ℕ} {η : ℝ} (hQ : 0 < Q) (hη : 0 < η)
    (hηsmall : η ≤ 1 / 1288) (hM : 0 < M) (hwindow : (K + 1 : ℝ) / M ≤ η / 8)
    (hglobal : η * Real.log ((Q : ℝ) * ((T : ℝ) + 3)) ≤ 3) (q : Fin Q) (m : ℤ)
    (hm : m ∈ Finset.Icc (-(T * M : ℤ) - (K + 1 : ℤ)) ((T * M : ℤ) + (K + 1 : ℤ))) :
    η * Real.log (((q.val + 1 : ℕ) : ℝ) * (|((m : ℝ) / M)| + 3)) ≤ 6 := by
  have hqNat : q.val + 1 ≤ Q := by omega
  have hq : ((q.val + 1 : ℕ) : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hqNat
  have hmInt : |m| ≤ (T * M : ℤ) + (K + 1 : ℤ) := by
    rw [abs_le]
    constructor <;> have hm' := Finset.mem_Icc.mp hm <;> omega
  have hmReal : |(m : ℝ)| ≤ (T : ℝ) * M + (K + 1 : ℝ) := by exact_mod_cast hmInt
  have hMreal : 0 < (M : ℝ) := by exact_mod_cast hM
  have hratio : |(m : ℝ) / M| ≤ (T : ℝ) + (K + 1 : ℝ) / M := by
    rw [abs_div, abs_of_pos hMreal]
    apply (div_le_iff₀ hMreal).2
    calc
      |(m : ℝ)| ≤ (T : ℝ) * M + (K + 1 : ℝ) := hmReal
      _ = ((T : ℝ) + (K + 1 : ℝ) / M) * M := by rw [add_mul, div_mul_cancel₀ _ hMreal.ne']
  have hηle1 : η ≤ 1 := by nlinarith only [hηsmall]
  have hratioT : |(m : ℝ) / M| ≤ (T : ℝ) + 1 := by
    calc
      |(m : ℝ) / M| ≤ (T : ℝ) + (K + 1 : ℝ) / M := hratio
      _ ≤ (T : ℝ) + η / 8 := by simpa only [add_comm] using add_le_add_left hwindow (T : ℝ)
      _ ≤ (T : ℝ) + 1 := by nlinarith only [hηle1]
  have hheight : |(m : ℝ) / M| + 3 ≤ (T : ℝ) + 4 := by linarith only [hratioT]
  have hT : (T : ℝ) + 4 ≤ ((T : ℝ) + 3) ^ 2 := by
    have hTnonneg : 0 ≤ (T : ℝ) := by positivity
    nlinarith only [hTnonneg]
  have hQreal : 1 ≤ (Q : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hQ)
  have hQsq : (Q : ℝ) ≤ (Q : ℝ) ^ 2 := by nlinarith only [hQreal]
  have harg : ((q.val + 1 : ℕ) : ℝ) * (|((m : ℝ) / M)| + 3) ≤ ((Q : ℝ) * ((T : ℝ) + 3)) ^ 2 := by
    calc
      _ ≤ (Q : ℝ) * ((T : ℝ) + 4) := mul_le_mul hq hheight (by positivity) (by positivity)
      _ ≤ (Q : ℝ) * (((T : ℝ) + 3) ^ 2) := mul_le_mul_of_nonneg_left hT (by positivity)
      _ ≤ (Q : ℝ) ^ 2 * (((T : ℝ) + 3) ^ 2) := mul_le_mul_of_nonneg_right hQsq (sq_nonneg _)
      _ = ((Q : ℝ) * ((T : ℝ) + 3)) ^ 2 := by ring
  have hargpos : 0 < ((q.val + 1 : ℕ) : ℝ) * (|((m : ℝ) / M)| + 3) := by positivity
  have hlog := Real.log_le_log hargpos harg
  rw [Real.log_pow] at hlog
  have hscaled := mul_le_mul_of_nonneg_left hlog (le_of_lt hη)
  calc
    η * Real.log (((q.val + 1 : ℕ) : ℝ) * (|((m : ℝ) / M)| + 3)) ≤
        η * (2 * Real.log ((Q : ℝ) * ((T : ℝ) + 3))) :=
      hscaled
    _ ≤ 6 := by nlinarith only [hglobal]

/--
Inputs: a global conductor-height cutoff and a point in the expanded integer height grid.
Claim: the ceiling of the local multiplicity weight is bounded by the absolute integer
`ceil (49 * completedZeroLocalLogBoundConstant)`.
Proof: apply the expanded-grid logarithm bound, use positivity of the local constant, and
monotonicity of `Nat.ceil`.
Role: removes conductor- and height-dependent weights before the family derivative-event sum.
-/
theorem completedZeroLocalLogBoundCeil_le_uniform_expanded_grid {Q T M K : ℕ} {η : ℝ} (hQ : 0 < Q)
    (hη : 0 < η) (hηsmall : η ≤ 1 / 1288) (hM : 0 < M) (hwindow : (K + 1 : ℝ) / M ≤ η / 8)
    (hglobal : η * Real.log ((Q : ℝ) * ((T : ℝ) + 3)) ≤ 3) (q : Fin Q) (m : ℤ)
    (hm : m ∈ Finset.Icc (-(T * M : ℤ) - (K + 1 : ℤ)) ((T * M : ℤ) + (K + 1 : ℤ))) :
    Nat.ceil
        (completedZeroLocalLogBoundConstant *
          (1 + 8 * η * Real.log (((q.val + 1 : ℕ) : ℝ) * (|((m : ℝ) / M)| + 3)))) ≤
      Nat.ceil (49 * completedZeroLocalLogBoundConstant) := by
  have hlog := eta_log_conductor_expanded_height_le_six hQ hη hηsmall hM hwindow hglobal q m hm
  have hweight :
    completedZeroLocalLogBoundConstant *
        (1 + 8 * η * Real.log (((q.val + 1 : ℕ) : ℝ) * (|((m : ℝ) / M)| + 3))) ≤
      49 * completedZeroLocalLogBoundConstant := by
    have hC := completedZeroLocalLogBoundConstant_pos
    calc
      _ ≤ completedZeroLocalLogBoundConstant * 49 :=
        mul_le_mul_of_nonneg_left (by nlinarith only [hlog]) (le_of_lt hC)
      _ = 49 * completedZeroLocalLogBoundConstant := by ring
  exact Nat.ceil_mono hweight

/-
Inputs: a primitive-family height ledger, a common near-one scale, a requested detector order, and
a uniform conductor-height logarithm bound.
Claim: one positive normalized threshold and one finite mesh work for every ledger occurrence; each
occurrence has an order whose derivative exceeds the corresponding order-dependent raw threshold
throughout its window.
Proof: choose the family-wide mesh once, then extract each character and zero, recover the
rectangle bounds and height, establish nonvanishing at the shifted center, and apply the detector.
Role: supplies common parameters for multiplicity-preserving incidence with the family large set.
-/
set_option maxHeartbeats 1000000 in
-- This wrapper unfolds a nested occurrence ledger and applies a uniform all-orders detector.
theorem exists_uniform_mesh_for_family_occurrences {Q : ℕ} {σ η : ℝ} (hσ : σ ≤ 1)
    (hσeta : 1 - σ ≤ η) (hη : 0 < η) (hηsmall : η ≤ 1 / 1288) (Krequested : ℕ)
    (hKrequested : 2 ≤ Krequested) (T : ℕ) (hglobal : η * Real.log ((Q : ℝ) * ((T : ℝ) + 3)) ≤ 3) :
    ∃ Kmax nmax M : ℕ,
      ∃ B : ℝ,
        0 < B ∧
          0 < M ∧
          (Kmax + 1 : ℝ) / M ≤ η / 8 ∧
          ∀
            {x :
              Σ q : Fin Q,
                Σ χ : DirichletCharacter ℂ (q.val + 1),
                  Σ ρ : ℂ, Fin (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ)},
            x ∈ primitiveCharacterFamilyZeroOccurrenceLedger Q σ T →
              ∃ n : ℕ,
                n ≤ nmax ∧
                  ∀ j : ℤ,
                    |x.2.2.1.im - (j : ℝ) / M| ≤ (Kmax + 1 : ℝ) / M →
                      B / (2 * (η ^ (n + 1) / (n.factorial : ℝ))) ≤
                        ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction x.2.1))
                            (((1 + η : ℝ) : ℂ) + Complex.I * (((j : ℝ) / M : ℝ) : ℂ))‖ := by
  obtain ⟨Kmax, nmax, M, B, hB, hM, hwidth, hdetector⟩ :=
    exists_uniform_mesh_for_completed_near_one_zero_family hη hηsmall Krequested hKrequested
  refine ⟨Kmax, nmax, M, B, hB, hM, hwidth, ?_⟩
  intro x hx
  obtain ⟨q, χ, ρ, i, hχ, hxEq, hprim, hρ⟩ :=
    primitiveCharacterFamilyZeroOccurrenceLedger_mem_extract hx
  subst x
  have hmod : 2 ≤ q.val + 1 := by
    by_contra hmod
    have hqzero : q.val = 0 := by omega
    have hqone : q.val + 1 = 1 := by omega
    have hsub : Subsingleton (DirichletCharacter ℂ (q.val + 1)) := by
      rw [hqone]
      exact (inferInstance : Subsingleton (DirichletCharacter ℂ 1))
    exact hχ (hsub.elim χ 1)
  have hQ : 0 < Q := Nat.zero_lt_of_lt q.isLt
  have hneZero : NeZero (q.val + 1) := ⟨Nat.ne_of_gt (by omega)⟩
  have hbox := (mem_completedZerosInRectangle_iff.mp hρ).1
  rw [dirichletCompletedLFunctionRectangleBox, Rectangle.rectangleClosedBox,
    Complex.mem_reProdIm] at hbox
  have hreBox : ρ.re ∈ Set.uIcc σ 1 := by
    simpa only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, sub_zero, mul_zero, Complex.add_re, Complex.one_re,
      add_zero] using hbox.1
  have hre : σ ≤ ρ.re ∧ ρ.re ≤ 1 := by
    rcases Set.mem_uIcc.mp hreBox with hcase | hcase
    · exact hcase
    · exact ⟨le_trans hσ hcase.1, le_trans hcase.2 hσ⟩
  have hρre : |ρ.re - 1| ≤ η := by
    rw [abs_le]
    constructor <;> linarith only [hre.1, hre.2, hσeta]
  have hxocc :
    (⟨ρ, i⟩ : Σ z : ℂ, Fin (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) z)) ∈
      completedZeroMultiplicityOccurrences χ hχ ((σ : ℂ) - (T : ℝ) * Complex.I)
        ((1 : ℂ) + (T : ℝ) * Complex.I) := by
    simp only [completedZeroMultiplicityOccurrences, Finset.mem_sigma]
    exact ⟨hρ, Finset.mem_univ i⟩
  have hheight := completedZeroMultiplicityOccurrences_height_mem χ hχ σ T hxocc
  have hheight' : |ρ.im| ≤ (T : ℝ) := by
    apply abs_le.mpr
    simpa only using hheight
  have hzero := (mem_completedZerosInRectangle_iff.mp hρ).2
  have hcenter :
    DirichletCharacter.completedLFunction χ (((1 + η : ℝ) : ℂ) + Complex.I * (ρ.im : ℂ)) ≠ 0 := by
    apply @DirichletLFunction.completedLFunction_ne_zero_of_one_le_re (q.val + 1) hneZero χ hχ
    have hreCenter : ((((1 + η : ℝ) : ℂ) + Complex.I * (ρ.im : ℂ)).re = 1 + η) := by
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_im, zero_mul, sub_zero, mul_zero, add_zero]
    rw [hreCenter]
    linarith only [hη]
  have hscaled := eta_log_conductor_height_le_of_cutoff_bound hQ hη.le hglobal q hheight'
  obtain ⟨n, hn, hgrid⟩ :=
    @hdetector (q.val + 1) hneZero χ hmod hχ hprim
      (by
        intro hinv; exact hχ (inv_eq_one.mp hinv))
      ρ hρre hzero hcenter hscaled
  have hcoeff : 0 < η ^ (n + 1) / (n.factorial : ℝ) := by positivity
  refine ⟨n, hn, ?_⟩
  intro j hj
  have hlarge := hgrid j hj
  apply (div_le_iff₀ (mul_pos (by norm_num) hcoeff)).2
  have hprod :=
    mul_nonneg (le_of_lt hcoeff)
      (norm_nonneg
        (iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ))
          (((1 + η : ℝ) : ℂ) + Complex.I * (((j : ℝ) / M : ℝ) : ℂ))))
  nlinarith only [hlarge, hprod]

/-
Inputs: a zero occurrence in the primitive-family ledger and a uniform detector valid for every
ledger entry.
Claim: the occurrence's character belongs to one order-indexed derivative large set at every grid
point in its detector window.
Proof: extract the primitive character and multiplicity-indexed zero, then unfold the large-set
filter using the uniform derivative lower bound.
Role: converts the shared-mesh output into the finite event membership used in incidence counting.
-/
theorem primitiveCharacterFamilyZeroOccurrenceLedger_mem_derivative_large_window (Q T nmax M K : ℕ)
    {σ η B : ℝ}
    (hdetector :
      ∀
        {x :
          Σ q : Fin Q,
            Σ χ : DirichletCharacter ℂ (q.val + 1),
              Σ ρ : ℂ, Fin (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ)},
        x ∈ primitiveCharacterFamilyZeroOccurrenceLedger Q σ T →
          ∃ n : ℕ,
            n ≤ nmax ∧
              ∀ j : ℤ,
                |x.2.2.1.im - (j : ℝ) / M| ≤ (K + 1 : ℝ) / M →
                  B / (2 * (η ^ (n + 1) / (n.factorial : ℝ))) ≤
                    ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction x.2.1))
                        (((1 + η : ℝ) : ℂ) + Complex.I * (((j : ℝ) / M : ℝ) : ℂ))‖)
    {x :
      Σ q : Fin Q,
        Σ χ : DirichletCharacter ℂ (q.val + 1),
          Σ ρ : ℂ, Fin (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ)}
    (hx : x ∈ primitiveCharacterFamilyZeroOccurrenceLedger Q σ T) :
    ∃ q χ ρ i,
      x = ⟨q, ⟨χ, ⟨ρ, i⟩⟩⟩ ∧
        χ.IsPrimitive ∧
        ∃ (hq : 1 < q.val + 1) (n : ℕ),
          n ≤ nmax ∧
            ∀ j : ℤ,
              |ρ.im - (j : ℝ) / M| ≤ (K + 1 : ℝ) / M →
                χ ∈
                  primitiveCharacterDerivativeLargeSet (q.val + 1) hq n
                    (((1 + η : ℝ) : ℂ) + Complex.I * (((j : ℝ) / M : ℝ) : ℂ))
                    (B / (2 * (η ^ (n + 1) / (n.factorial : ℝ)))) := by
  obtain ⟨q, χ, ρ, i, hχ, hxEq, hprim, hρ⟩ :=
    primitiveCharacterFamilyZeroOccurrenceLedger_mem_extract hx
  subst x
  have hmod : 2 ≤ q.val + 1 := by
    by_contra hmod
    have hqzero : q.val = 0 := by omega
    have hqone : q.val + 1 = 1 := by omega
    have hsub : Subsingleton (DirichletCharacter ℂ (q.val + 1)) := by
      rw [hqone]
      exact (inferInstance : Subsingleton (DirichletCharacter ℂ 1))
    exact hχ (hsub.elim χ 1)
  have hq : 1 < q.val + 1 := by omega
  obtain ⟨n, hn, hgrid⟩ := hdetector hx
  have hχmem : χ ∈ primitiveDirichletCharacterSet (q.val + 1) := by
    simp only [primitiveDirichletCharacterSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hprim
  refine ⟨q, χ, ρ, i, rfl, hprim, hq, n, hn, ?_⟩
  intro j hj
  have hlarge := hgrid j hj
  have hlargeSet :
    χ ∈
      primitiveCharacterDerivativeLargeSet (q.val + 1) hq n
        (((1 + η : ℝ) : ℂ) + Complex.I * (((j : ℝ) / M : ℝ) : ℂ))
        (B / (2 * (η ^ (n + 1) / (n.factorial : ℝ)))) := by
    simpa only [primitiveCharacterDerivativeLargeSet, Finset.mem_filter] using
      And.intro hχmem hlarge
  exact hlargeSet

/-
Inputs: a global conductor-height cutoff, a near-one scale, and a requested minimum derivative
order.
Claim: one common mesh and threshold assign every ledger occurrence an order whose entire detector
window belongs to the corresponding primitive-character derivative large set.
Proof: obtain the uniform norm detector, then apply the ledger-to-large-set membership interface.
Role: provides the finite event form needed to count multiplicity-preserving zero incidences.
-/
theorem exists_family_occurrence_derivative_large_window {Q : ℕ} {σ η : ℝ} (hσ : σ ≤ 1)
    (hσeta : 1 - σ ≤ η) (hη : 0 < η) (hηsmall : η ≤ 1 / 1288) (Krequested : ℕ)
    (hKrequested : 2 ≤ Krequested) (T : ℕ) (hglobal : η * Real.log ((Q : ℝ) * ((T : ℝ) + 3)) ≤ 3) :
    ∃ Kmax nmax M : ℕ,
      ∃ B : ℝ,
        0 < B ∧
          0 < M ∧
          (Kmax + 1 : ℝ) / M ≤ η / 8 ∧
          ∀
            {x :
              Σ q : Fin Q,
                Σ χ : DirichletCharacter ℂ (q.val + 1),
                  Σ ρ : ℂ, Fin (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ)},
            x ∈ primitiveCharacterFamilyZeroOccurrenceLedger Q σ T →
              ∃ q χ ρ i,
                x = ⟨q, ⟨χ, ⟨ρ, i⟩⟩⟩ ∧
                  χ.IsPrimitive ∧
                  ∃ (hq : 1 < q.val + 1) (n : ℕ),
                    n ≤ nmax ∧
                      ∀ j : ℤ,
                        |ρ.im - (j : ℝ) / M| ≤ (Kmax + 1 : ℝ) / M →
                          χ ∈
                            primitiveCharacterDerivativeLargeSet (q.val + 1) hq n
                              (((1 + η : ℝ) : ℂ) + Complex.I * (((j : ℝ) / M : ℝ) : ℂ))
                              (B / (2 * (η ^ (n + 1) / (n.factorial : ℝ)))) := by
  obtain ⟨Kmax, nmax, M, B, hB, hM, hwidth, hdetector⟩ :=
    exists_uniform_mesh_for_family_occurrences hσ hσeta hη hηsmall Krequested hKrequested T hglobal
  refine ⟨Kmax, nmax, M, B, hB, hM, hwidth, ?_⟩
  intro x hx
  exact
    primitiveCharacterFamilyZeroOccurrenceLedger_mem_derivative_large_window Q T nmax M Kmax
      hdetector hx

open Classical in
/--
Inputs: a shared detector on the primitive-family occurrence ledger, a global conductor-height
cutoff, and a height mesh whose width is at most `η/8`.
Claim: the family zero-occurrence count times the window-incidence gain is bounded by an absolute
local multiplicity factor times the sum of derivative-order large-value events over conductors,
characters, and the expanded height grid.
Proof: use the family incidence estimate, bound every expanded-grid local logarithmic weight by
`ceil (49 * completedZeroLocalLogBoundConstant)`, and distribute that constant over the finite sums.
Role: gives the finite zero-density-to-derivative-event inequality needed before the hybrid sieve.
-/
theorem primitiveCharacterFamilyZeroOccurrence_mul_window_le_uniform_derivative_sum (Q : ℕ)
    (hQ : 0 < Q) {σ η : ℝ} (R : ℕ → ℝ) (hσ1 : σ ≤ 1) (hσeta : 1 - σ ≤ η) (hη : 0 < η)
    (hηsmall : η ≤ 1 / 1288) (T nmax M K : ℕ) (hM : 0 < M) (hwindow : (K + 1 : ℝ) / M ≤ η / 8)
    (hglobal : η * Real.log ((Q : ℝ) * ((T : ℝ) + 3)) ≤ 3)
    (hdetector :
      ∀
        {x :
          Σ q : Fin Q,
            Σ χ : DirichletCharacter ℂ (q.val + 1),
              Σ ρ : ℂ, Fin (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ)},
        x ∈ primitiveCharacterFamilyZeroOccurrenceLedger Q σ T →
          ∃ n : ℕ,
            n ≤ nmax ∧
              ∀ j : ℤ,
                |x.2.2.1.im - (j : ℝ) / M| ≤ (K + 1 : ℝ) / M →
                  R n ≤
                    ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction x.2.1))
                        (((1 + η : ℝ) : ℂ) + Complex.I * (((j : ℝ) / M : ℝ) : ℂ))‖) :
    primitiveCharacterFamilyZeroOccurrenceCountAtNatHeight Q σ T * (2 * K + 1 : ℝ) ≤
      (Nat.ceil (49 * completedZeroLocalLogBoundConstant) : ℝ) *
        (∑ q : Fin Q,
          ∑ χ : DirichletCharacter ℂ (q.val + 1),
            if _hχ : χ ≠ 1 then
              if _hprim : χ.IsPrimitive then
                ∑ m ∈ Finset.Icc (-(T * M : ℤ) - (K + 1 : ℤ)) ((T * M : ℤ) + (K + 1 : ℤ)),
                  ∑ n ∈ Finset.range (nmax + 1),
                    if
                        R n ≤
                          ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ))
                              (((1 + η : ℝ) : ℂ) + Complex.I * (((m : ℝ) / M : ℝ) : ℂ))‖ then
                      (1 : ℝ)
                    else 0
              else 0
            else 0) := by
  have hinc :=
    primitiveCharacterFamilyZeroOccurrenceCount_mul_window_size_le_derivative_order_sum Q R hσ1
      hσeta hη hηsmall T nmax M K hM (by nlinarith only [hwindow, hη]) hdetector
  let uniform : ℝ := (Nat.ceil (49 * completedZeroLocalLogBoundConstant) : ℝ)
  calc
    _ ≤
        ∑ q : Fin Q,
          ∑ χ : DirichletCharacter ℂ (q.val + 1),
            if _hχ : χ ≠ 1 then
              if _hprim : χ.IsPrimitive then
                ∑ m ∈ Finset.Icc (-(T * M : ℤ) - (K + 1 : ℤ)) ((T * M : ℤ) + (K + 1 : ℤ)),
                  (Nat.ceil
                      (completedZeroLocalLogBoundConstant *
                          (1 + 8 * η * Real.log (((q.val + 1 : ℕ) : ℝ) * (|((m : ℝ) / M)| + 3))) :
                        ℝ) *
                    (∑ n ∈ Finset.range (nmax + 1),
                      if
                          R n ≤
                            ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ))
                                (((1 + η : ℝ) : ℂ) + Complex.I * (((m : ℝ) / M : ℝ) : ℂ))‖ then
                        (1 : ℝ)
                      else 0))
              else 0
            else 0 :=
      hinc
    _ ≤
        ∑ q : Fin Q,
          ∑ χ : DirichletCharacter ℂ (q.val + 1),
            if _hχ : χ ≠ 1 then
              if _hprim : χ.IsPrimitive then
                ∑ m ∈ Finset.Icc (-(T * M : ℤ) - (K + 1 : ℤ)) ((T * M : ℤ) + (K + 1 : ℤ)),
                  (uniform *
                    (∑ n ∈ Finset.range (nmax + 1),
                      if
                          R n ≤
                            ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ))
                                (((1 + η : ℝ) : ℂ) + Complex.I * (((m : ℝ) / M : ℝ) : ℂ))‖ then
                        (1 : ℝ)
                      else 0))
              else 0
            else 0 :=
      by
      apply Finset.sum_le_sum
      intro q hqmem
      apply Finset.sum_le_sum
      intro χ hχmem
      by_cases hχ : χ ≠ 1
      · by_cases hprim : χ.IsPrimitive
        · simp only [dite_eq_left hχ, dite_eq_left hprim]
          apply Finset.sum_le_sum
          intro m hm
          have hceil :=
            completedZeroLocalLogBoundCeil_le_uniform_expanded_grid hQ hη hηsmall hM hwindow hglobal
              q m hm
          have hceilReal :
            ((Nat.ceil
                    (completedZeroLocalLogBoundConstant *
                      (1 + 8 * η * Real.log (((q.val + 1 : ℕ) : ℝ) * (|((m : ℝ) / M)| + 3)))) :
                  ℕ) :
                ℝ) ≤
              uniform := by
            change
              ((Nat.ceil
                      (completedZeroLocalLogBoundConstant *
                        (1 + 8 * η * Real.log (((q.val + 1 : ℕ) : ℝ) * (|((m : ℝ) / M)| + 3)))) :
                    ℕ) :
                  ℝ) ≤
                (Nat.ceil (49 * completedZeroLocalLogBoundConstant) : ℝ)
            exact_mod_cast hceil
          have hcountNonneg :
            0 ≤
              ∑ n ∈ Finset.range (nmax + 1),
                if
                    R n ≤
                      ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ))
                          (((1 + η : ℝ) : ℂ) + Complex.I * (((m : ℝ) / M : ℝ) : ℂ))‖ then
                  (1 : ℝ)
                else 0 := by
            positivity
          exact mul_le_mul_of_nonneg_right hceilReal hcountNonneg
        · simp only [dite_eq_left hχ, dite_eq_right hprim]
          exact le_rfl
      · simp only [dite_eq_right hχ]
        exact le_rfl
    _ =
        uniform *
          (∑ q : Fin Q,
            ∑ χ : DirichletCharacter ℂ (q.val + 1),
              if _hχ : χ ≠ 1 then
                if _hprim : χ.IsPrimitive then
                  ∑ m ∈ Finset.Icc (-(T * M : ℤ) - (K + 1 : ℤ)) ((T * M : ℤ) + (K + 1 : ℤ)),
                    ∑ n ∈ Finset.range (nmax + 1),
                      if
                          R n ≤
                            ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ))
                                (((1 + η : ℝ) : ℂ) + Complex.I * (((m : ℝ) / M : ℝ) : ℂ))‖ then
                        (1 : ℝ)
                      else 0
                else 0
              else 0) :=
      by simp only [uniform, Finset.mul_sum, mul_dite, mul_zero]

open Classical in
/--
Inputs: a primitive character modulo `q`, a derivative order, a point, and a norm threshold.
Claim: the event indicator for a nonprincipal primitive character is bounded by membership in
the corresponding primitive-character derivative large set.
Proof: unfold the filtered set and split on nonprincipality, primitivity, and the norm threshold.
Role: converts the analytic event sum into cardinalities of the large sets used by the sieve.
-/
theorem primitiveCharacterDerivativeEvent_le_largeSet_indicator {q n : ℕ} [NeZero q] (hq : 1 < q)
    (s : ℂ) (R : ℝ) (χ : DirichletCharacter ℂ q) :
    (if _hχ : χ ≠ 1 then
        if _hprim : χ.IsPrimitive then
          if R ≤ ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) s‖ then (1 : ℝ) else 0
        else 0
      else 0) ≤
      if χ ∈ primitiveCharacterDerivativeLargeSet q hq n s R then (1 : ℝ) else 0 := by
  classical
  by_cases hχ1 : χ ≠ 1
  · by_cases hprim : χ.IsPrimitive
    · by_cases hlarge : R ≤ ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) s‖
      · simp only [dite_eq_left hχ1, dite_eq_left hprim, ite_eq_left hlarge,
          primitiveCharacterDerivativeLargeSet, Finset.mem_filter, primitiveDirichletCharacterSet,
          Finset.mem_filter, Finset.mem_univ]
        simp only [hprim, hlarge, and_self, ite_true, le_rfl]
      · simp only [dite_eq_left hχ1, dite_eq_left hprim, ite_eq_right hlarge,
          primitiveCharacterDerivativeLargeSet, Finset.mem_filter, primitiveDirichletCharacterSet,
          Finset.mem_filter, Finset.mem_univ]
        simp only [hprim, hlarge, and_false, ite_false]
        exact le_rfl
    · simp only [dite_eq_left hχ1, dite_eq_right hprim]
      split_ifs <;> norm_num only
  · simp only [dite_eq_right hχ1]
    split_ifs <;> norm_num only

open Classical in
/--
Inputs: a modulus greater than one, a derivative order, a complex point, and a real threshold.
Claim: the nonprincipal primitive-character event sum is bounded by the cardinality of the
primitive-character derivative large set.
Proof: apply the pointwise event-to-membership bound and rewrite the indicator sum as a cardinality.
Role: packages the event-to-count conversion needed to feed the expanded grid into the family
large-sieve estimate.
-/
theorem primitiveCharacterDerivativeEventSum_le_largeSet_card {q n : ℕ} [NeZero q] (hq : 1 < q)
    (s : ℂ) (R : ℝ) :
    (∑ χ : DirichletCharacter ℂ q,
        if _hχ : χ ≠ 1 then
          if _hprim : χ.IsPrimitive then
            if R ≤ ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) s‖ then (1 : ℝ)
            else 0
          else 0
        else 0) ≤
      (primitiveCharacterDerivativeLargeSet q hq n s R).card := by
  classical
    calc
    _ ≤
        ∑ χ : DirichletCharacter ℂ q,
          if χ ∈ primitiveCharacterDerivativeLargeSet q hq n s R then (1 : ℝ) else 0 :=
      Finset.sum_le_sum fun χ _ => primitiveCharacterDerivativeEvent_le_largeSet_indicator hq s R χ
    _ = _ := by
      rw [Finset.sum_ite_mem_eq]
      exact_mod_cast
        (Finset.card_eq_sum_ones (primitiveCharacterDerivativeLargeSet q hq n s R)).symm

open Classical in
/--
Inputs: a positive cutoff and a real-valued function on natural-number moduli that vanishes at 1.
Claim: summing the function over moduli `q.val + 1` for `q : Fin Q` equals its sum over `1 < q ≤ Q`.
Proof: reindex `Fin Q` onto `1 ≤ q ≤ Q`, then remove the modulus-one term using the vanishing
hypothesis.
Role: transfers the zero-ledger conductor index to the family large-count conductor range.
-/
theorem sum_fin_shift_eq_sum_Ioc {Q : ℕ} (hQ : 0 < Q) (f : ℕ → ℝ) (hf : f 1 = 0) :
    (∑ q : Fin Q, f (q.val + 1)) = ∑ q ∈ Finset.Ioc 1 Q, f q := by
  classical
  have hsum : (∑ q : Fin Q, f (q.val + 1)) = ∑ q ∈ Finset.Icc 1 Q, f q := by
    apply Finset.sum_bij (fun (q : Fin Q) _ => q.val + 1)
    · intro q hq
      simp only [Finset.mem_Icc]
      constructor
      · exact Nat.succ_le_succ (Nat.zero_le q.val)
      · exact Nat.succ_le_of_lt q.isLt
    · intro q hq r hr hqr
      apply Fin.ext
      exact Nat.add_right_cancel hqr
    · intro r hr
      obtain ⟨hr1, hrQ⟩ := Finset.mem_Icc.mp hr
      refine ⟨⟨r - 1, ?_⟩, Finset.mem_univ _, ?_⟩
      · exact lt_of_lt_of_le (Nat.sub_lt_self (by decide) hr1) hrQ
      · exact Nat.sub_add_cancel hr1
    · intro q hq
      rfl
  rw [hsum, Finset.Icc_eq_cons_Ioc (Nat.succ_le_iff.mpr hQ)]
  simp only [Finset.sum_cons, hf, zero_add]

open Classical in
/--
Inputs: a positive modulus cutoff, a derivative order, a complex point, and a norm threshold.
Claim: the sum of nonprincipal primitive derivative events over moduli `2` through `Q` is bounded
by `primitiveCharacterDerivativeFamilyLargeCount` at that point and order.
Proof: bound each character event sum by its large-set cardinality, reindex `q.val + 1` onto the
modulus interval, and remove the zero event at modulus one.
Role: transfers the finite event sum from the zero-occurrence ledger to the family count consumed
by the additive large-sieve bound.
-/
theorem primitiveCharacterDerivativeEventSum_le_family_large_count (Q n : ℕ) (hQ : 0 < Q) (s : ℂ)
    (R : ℕ → ℝ) :
    (∑ q : Fin Q,
        ∑ χ : DirichletCharacter ℂ (q.val + 1),
          if _hχ : χ ≠ 1 then
            if _hprim : χ.IsPrimitive then
              if R n ≤ ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) s‖ then (1 : ℝ)
              else 0
            else 0
          else 0) ≤
      primitiveCharacterDerivativeFamilyLargeCount Q n s (R n) := by
  classical
  let eventSum : ℕ → ℝ := fun r =>
    if hr : 1 < r then
      letI : NeZero r := ⟨Nat.ne_of_gt (lt_trans Nat.zero_lt_one hr)⟩
      ∑ χ : DirichletCharacter ℂ r,
        if _hχ : χ ≠ 1 then
          if _hprim : χ.IsPrimitive then
            if R n ≤ ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) s‖ then (1 : ℝ)
            else 0
          else 0
        else 0
    else 0
  let countSum : ℕ → ℝ := fun r =>
    if hr : 1 < r then
      letI : NeZero r := ⟨Nat.ne_of_gt (lt_trans Nat.zero_lt_one hr)⟩
      (primitiveCharacterDerivativeLargeSet r hr n s (R n)).card
    else 0
  have hone : ¬(1 < 1) := Nat.lt_irrefl 1
  have heventOne : eventSum 1 = 0 := by simp only [eventSum, dite_eq_right hone]
  have hcountOne : countSum 1 = 0 := by simp only [countSum, dite_eq_right hone]
  have hterm (q : Fin Q) :
    (∑ χ : DirichletCharacter ℂ (q.val + 1),
        if _hχ : χ ≠ 1 then
          if _hprim : χ.IsPrimitive then
            if R n ≤ ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) s‖ then (1 : ℝ)
            else 0
          else 0
        else 0) =
      eventSum (q.val + 1) := by
    by_cases hzero : q.val = 0
    · rw [hzero]
      simp only [Nat.zero_add] at *
      simp only [eventSum, dite_eq_right hone]
      apply Finset.sum_eq_zero
      intro χ hχ
      have hsub : Subsingleton (DirichletCharacter ℂ (0 + 1)) := by
        simpa only [Nat.zero_add] using (inferInstance : Subsingleton (DirichletCharacter ℂ 1))
      have hχeq : χ = 1 := @Subsingleton.elim _ hsub χ 1
      have hnot : ¬((1 : DirichletCharacter ℂ (0 + 1)) ≠ 1) := by
        intro h
        exact h rfl
      simp only [hχeq, dite_eq_right hnot]
    · have hpos : 0 < q.val := Nat.pos_of_ne_zero hzero
      have hmod : 1 < q.val + 1 := Nat.succ_lt_succ hpos
      simp only [eventSum, dite_eq_left hmod]
  have hsumBound : (∑ q : Fin Q, eventSum (q.val + 1)) ≤ ∑ q : Fin Q, countSum (q.val + 1) := by
    apply Finset.sum_le_sum
    intro q hq
    by_cases hzero : q.val = 0
    · rw [hzero]
      simp only [Nat.zero_add, heventOne, hcountOne]
      exact le_rfl
    · have hpos : 0 < q.val := Nat.pos_of_ne_zero hzero
      have hmod : 1 < q.val + 1 := Nat.succ_lt_succ hpos
      have hlocal := primitiveCharacterDerivativeEventSum_le_largeSet_card (n := n) hmod s (R n)
      simpa only [eventSum, countSum, dite_eq_left hmod] using hlocal
  have hcountShift : (∑ q : Fin Q, countSum (q.val + 1)) = ∑ q ∈ Finset.Ioc 1 Q, countSum q :=
    sum_fin_shift_eq_sum_Ioc hQ countSum hcountOne
  calc
    _ = ∑ q : Fin Q, eventSum (q.val + 1) := by
      apply Finset.sum_congr rfl
      intro q hq
      exact hterm q
    _ ≤ ∑ q : Fin Q, countSum (q.val + 1) := hsumBound
    _ = ∑ q ∈ Finset.Ioc 1 Q, countSum q := hcountShift
    _ = primitiveCharacterDerivativeFamilyLargeCount Q n s (R n) := by
      unfold primitiveCharacterDerivativeFamilyLargeCount
      rw [← Finset.sum_attach]
      apply Finset.sum_congr rfl
      intro q hq
      simp only [countSum, dite_eq_left (Finset.mem_Ioc.mp q.property).1]

open Classical in
/--
Inputs: a positive conductor cutoff, derivative-order and height-grid bounds, a grid width, a real
part, and a large-value threshold.
Claim: the sum of nonprincipal primitive derivative events over conductors, characters, grid
heights, and derivative orders is bounded by the corresponding family large-count sum.
Proof: commute the finite sums, convert each fixed-point event sum to a family count, and retain
the expanded height-grid endpoints.
Role: supplies the event-sum estimate needed to pass the zero-occurrence incidence bound to the
pre-sifted large-sieve interface.
-/
theorem primitiveCharacterDerivativeEvent_grid_sum_le_family_count (Q nmax T M K : ℕ) (hQ : 0 < Q)
    (σ : ℝ) (R : ℕ → ℝ) :
    (∑ q : Fin Q,
        ∑ χ : DirichletCharacter ℂ (q.val + 1),
          if _hχ : χ ≠ 1 then
            if _hprim : χ.IsPrimitive then
              ∑ m ∈ Finset.Icc (-(T * M : ℤ) - (K + 1 : ℤ)) ((T * M : ℤ) + (K + 1 : ℤ)),
                ∑ n ∈ Finset.range nmax,
                  if
                      R n ≤
                        ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ))
                            ((σ : ℂ) + Complex.I * (((m : ℝ) / M : ℝ) : ℂ))‖ then
                    (1 : ℝ)
                  else 0
            else 0
          else 0) ≤
      ∑ n ∈ Finset.range nmax,
        ∑ m ∈ Finset.Icc (-(T * M : ℤ) - (K + 1 : ℤ)) ((T * M : ℤ) + (K + 1 : ℤ)),
          primitiveCharacterDerivativeFamilyLargeCount Q n
            ((σ : ℂ) + Complex.I * (((m : ℝ) / M : ℝ) : ℂ)) (R n) := by
  classical
  let grid : Finset ℤ := Finset.Icc (-(T * M : ℤ) - (K + 1 : ℤ)) ((T * M : ℤ) + (K + 1 : ℤ))
  let point : ℤ → ℂ := fun m => (σ : ℂ) + Complex.I * (((m : ℝ) / M : ℝ) : ℂ)
  let event : (q : Fin Q) → DirichletCharacter ℂ (q.val + 1) → ℤ → ℕ → ℝ := fun q χ m n =>
    if χ ≠ 1 then
      if χ.IsPrimitive then
        if R n ≤ ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) (point m)‖ then 1
        else 0
      else 0
    else 0
  have hsplit :
    (∑ q : Fin Q,
        ∑ χ : DirichletCharacter ℂ (q.val + 1),
          if _hχ : χ ≠ 1 then
            if _hprim : χ.IsPrimitive then
              ∑ m ∈ grid,
                ∑ n ∈ Finset.range nmax,
                  if
                      R n ≤
                        ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) (point m)‖ then
                    (1 : ℝ)
                  else 0
            else 0
          else 0) =
      ∑ q : Fin Q,
        ∑ χ : DirichletCharacter ℂ (q.val + 1),
          ∑ m ∈ grid, ∑ n ∈ Finset.range nmax, event q χ m n := by
    apply Finset.sum_congr rfl
    intro q hq
    apply Finset.sum_congr rfl
    intro χ hχ
    by_cases hχ1 : χ ≠ 1
    · by_cases hprim : χ.IsPrimitive
      · simp only [dite_eq_left hχ1, dite_eq_left hprim, event, point, ite_eq_left hχ1,
          ite_eq_left hprim]
      · simp only [dite_eq_left hχ1, dite_eq_right hprim, event, point, ite_eq_left hχ1,
          ite_eq_right hprim, Finset.sum_const_zero]
    · simp only [dite_eq_right hχ1, event, point, ite_eq_right hχ1, Finset.sum_const_zero]
  calc
    _ =
        ∑ q : Fin Q,
          ∑ χ : DirichletCharacter ℂ (q.val + 1),
            ∑ m ∈ grid, ∑ n ∈ Finset.range nmax, event q χ m n :=
      by simpa only [grid, point] using hsplit
    _ =
        ∑ q : Fin Q,
          ∑ m ∈ grid,
            ∑ χ : DirichletCharacter ℂ (q.val + 1), ∑ n ∈ Finset.range nmax, event q χ m n :=
      by
      apply Finset.sum_congr rfl
      intro q hq
      exact Finset.sum_comm
    _ =
        ∑ q : Fin Q,
          ∑ m ∈ grid,
            ∑ n ∈ Finset.range nmax, ∑ χ : DirichletCharacter ℂ (q.val + 1), event q χ m n :=
      by
      apply Finset.sum_congr rfl
      intro q hq
      apply Finset.sum_congr rfl
      intro m hm
      exact Finset.sum_comm
    _ =
        ∑ n ∈ Finset.range nmax,
          ∑ m ∈ grid, ∑ q : Fin Q, ∑ χ : DirichletCharacter ℂ (q.val + 1), event q χ m n :=
      by
      calc
        _ =
            ∑ q : Fin Q,
              ∑ n ∈ Finset.range nmax,
                ∑ m ∈ grid, ∑ χ : DirichletCharacter ℂ (q.val + 1), event q χ m n :=
          by
          apply Finset.sum_congr rfl
          intro q hq
          exact Finset.sum_comm
        _ =
            ∑ n ∈ Finset.range nmax,
              ∑ q : Fin Q, ∑ m ∈ grid, ∑ χ : DirichletCharacter ℂ (q.val + 1), event q χ m n :=
          by exact Finset.sum_comm
        _ =
            ∑ n ∈ Finset.range nmax,
              ∑ m ∈ grid, ∑ q : Fin Q, ∑ χ : DirichletCharacter ℂ (q.val + 1), event q χ m n :=
          by
          apply Finset.sum_congr rfl
          intro n hn
          exact Finset.sum_comm
    _ ≤
        ∑ n ∈ Finset.range nmax,
          ∑ m ∈ grid, primitiveCharacterDerivativeFamilyLargeCount Q n (point m) (R n) :=
      by
      apply Finset.sum_le_sum
      intro n hn
      apply Finset.sum_le_sum
      intro m hm
      exact primitiveCharacterDerivativeEventSum_le_family_large_count Q n hQ (point m) R

open Classical in
/--
Inputs: a shared detector for the primitive-family zero-occurrence ledger, a global conductor-height
cutoff, and a mesh whose width is at most `η/8`.
Claim: the zero-occurrence count times the window-incidence gain is bounded by an absolute local
factor times the family derivative large-count sum over all derivative orders and expanded grid
heights.
Proof: combine the weighted incidence estimate with the finite event-to-family-count bound.
Role: gives the zero-density side of the pre-sifted large-sieve connection without dropping window
multiplicity or expanded grid endpoints.
-/
theorem primitiveCharacterFamilyZeroOccurrence_mul_window_le_uniform_family_large_count (Q : ℕ)
    (hQ : 0 < Q) {σ η : ℝ} (R : ℕ → ℝ) (hσ1 : σ ≤ 1) (hσeta : 1 - σ ≤ η) (hη : 0 < η)
    (hηsmall : η ≤ 1 / 1288) (T nmax M K : ℕ) (hM : 0 < M) (hwindow : (K + 1 : ℝ) / M ≤ η / 8)
    (hglobal : η * Real.log ((Q : ℝ) * ((T : ℝ) + 3)) ≤ 3)
    (hdetector :
      ∀
        {x :
          Σ q : Fin Q,
            Σ χ : DirichletCharacter ℂ (q.val + 1),
              Σ ρ : ℂ, Fin (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ)},
        x ∈ primitiveCharacterFamilyZeroOccurrenceLedger Q σ T →
          ∃ n : ℕ,
            n ≤ nmax ∧
              ∀ j : ℤ,
                |x.2.2.1.im - (j : ℝ) / M| ≤ (K + 1 : ℝ) / M →
                  R n ≤
                    ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction x.2.1))
                        (((1 + η : ℝ) : ℂ) + Complex.I * (((j : ℝ) / M : ℝ) : ℂ))‖) :
    primitiveCharacterFamilyZeroOccurrenceCountAtNatHeight Q σ T * (2 * K + 1 : ℝ) ≤
      (Nat.ceil (49 * completedZeroLocalLogBoundConstant) : ℝ) *
        (∑ n ∈ Finset.range (nmax + 1),
          ∑ m ∈ Finset.Icc (-(T * M : ℤ) - (K + 1 : ℤ)) ((T * M : ℤ) + (K + 1 : ℤ)),
            primitiveCharacterDerivativeFamilyLargeCount Q n
              (((1 + η : ℝ) : ℂ) + Complex.I * (((m : ℝ) / M : ℝ) : ℂ)) (R n)) := by
  classical
  have hbase :=
    primitiveCharacterFamilyZeroOccurrence_mul_window_le_uniform_derivative_sum Q hQ R hσ1 hσeta hη
      hηsmall T nmax M K hM hwindow hglobal hdetector
  have hgrid :=
    primitiveCharacterDerivativeEvent_grid_sum_le_family_count Q (nmax + 1) T M K hQ (1 + η) R
  calc
    _ ≤ _ := hbase
    _ ≤ _ := mul_le_mul_of_nonneg_left hgrid (Nat.cast_nonneg _)

/--
Inputs: a positive conductor cutoff, a near-one scale, a requested detector order, a height bound,
and a uniform conductor-height logarithm bound.
Claim: one common mesh bounds the zero-occurrence count by the family large-count sum with the
order-dependent threshold inherited from the normalized derivative detector.
Proof: obtain the uniform mesh and apply the normalized incidence-to-count estimate with threshold
`B / (2 * (η^(n+1)/n!))` at each derivative order.
Role: connects the completed-zero occurrence ledger to the family large-count interface.
-/
theorem exists_uniform_normalized_zero_occurrence_family_large_count (Q : ℕ) (hQ : 0 < Q) {σ η : ℝ}
    (hσ1 : σ ≤ 1) (hσeta : 1 - σ ≤ η) (hη : 0 < η) (hηsmall : η ≤ 1 / 1288) (Krequested : ℕ)
    (hKrequested : 2 ≤ Krequested) (T : ℕ) (hglobal : η * Real.log ((Q : ℝ) * ((T : ℝ) + 3)) ≤ 3) :
    ∃ Kmax nmax M : ℕ,
      ∃ B : ℝ,
        0 < B ∧
          0 < M ∧
          (Kmax + 1 : ℝ) / M ≤ η / 8 ∧
          primitiveCharacterFamilyZeroOccurrenceCountAtNatHeight Q σ T * (2 * Kmax + 1 : ℝ) ≤
            (Nat.ceil (49 * completedZeroLocalLogBoundConstant) : ℝ) *
              (∑ n ∈ Finset.range (nmax + 1),
                ∑ m ∈ Finset.Icc (-(T * M : ℤ) - (Kmax + 1 : ℤ)) ((T * M : ℤ) + (Kmax + 1 : ℤ)),
                  primitiveCharacterDerivativeFamilyLargeCount Q n
                    (((1 + η : ℝ) : ℂ) + Complex.I * (((m : ℝ) / M : ℝ) : ℂ))
                    (B / (2 * (η ^ (n + 1) / (n.factorial : ℝ))))) := by
  obtain ⟨Kmax, nmax, M, B, hB, hM, hwidth, hdetector⟩ :=
    exists_uniform_mesh_for_family_occurrences hσ1 hσeta hη hηsmall Krequested hKrequested T hglobal
  let R : ℕ → ℝ := fun n => B / (2 * (η ^ (n + 1) / (n.factorial : ℝ)))
  have hcount :=
    primitiveCharacterFamilyZeroOccurrence_mul_window_le_uniform_family_large_count Q hQ R hσ1 hσeta
      hη hηsmall T nmax M Kmax hM hwidth hglobal hdetector
  refine ⟨Kmax, nmax, M, B, hB, hM, hwidth, ?_⟩
  simpa only [R] using hcount

/-- For a requested minimum order, choose one detector-order envelope independent
of the near-one rate, modulus, character, and height. A primitive nonprincipal
character and a completed zero satisfying the local scale conditions yield local
orders inside this envelope and the ordinary normalized derivative signal.
Choose the uniform Gamma estimate once and apply the fixed-Gamma detector.
This supplies rate-independent order bounds for the common high-prime mesh. -/
theorem exists_uniform_near_one_detector_order_envelope (Krequested : ℕ)
    (hKrequested : 2 ≤ Krequested) :
    ∃ Kmax nmax : ℕ,
      Krequested ≤ Kmax ∧
        nmax = Kmax * completedLFunctionNearOneDetectorMultiplicityCap ∧
        ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q},
          2 ≤ q →
            χ ≠ 1 →
            χ.IsPrimitive →
            χ⁻¹ ≠ 1 →
            ∀ {η : ℝ},
              0 < η →
                η ≤ 1 / 1288 →
                ∀ {c ρ : ℂ},
                  c.re = 1 + η →
                    c.im = ρ.im →
                    |ρ.re - 1| ≤ η →
                    DirichletCharacter.completedLFunction χ ρ = 0 →
                    DirichletCharacter.completedLFunction χ c ≠ 0 →
                    η * Real.log ((q : ℝ) * (|ρ.im| + 3)) ≤ 3 →
                    ∃ K n : ℕ,
                      Krequested ≤ K ∧
                        K ≤ Kmax ∧
                        0 < n ∧
                        n ≤ nmax ∧
                        K ≤ n + 1 ∧
                        n + 1 ≤ K * completedLFunctionNearOneDetectorMultiplicityCap ∧
                        Real.exp (-(ordinaryLFunctionNearOneDetectorExponent * (K : ℝ))) ≤
                          (η ^ (n + 1) / (n.factorial : ℝ)) *
                            ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) c‖ := by
  obtain ⟨G, hG, hgamma⟩ := exists_uniform_gamma_subtraction_for_ordinary_LFunction_derivative_all
  let Kmax :=
    max completedGenusRemoteTailUniformOrderBound
      (max (uniformGammaAbsorptionOrderCutoff G + 1) Krequested)
  refine
    ⟨Kmax, Kmax * completedLFunctionNearOneDetectorMultiplicityCap,
      (le_max_right _ _).trans (le_max_right _ _), rfl, ?_⟩
  intro q hq χ hqbound hχ hp hinv η hη hηsmall c ρ hcre hcim hρre hzero hc hscale
  obtain
    ⟨_, _, _, _, _, _, K, m, n, hKreq, _, _, hKglobal, _, _, hn, hnm, hmK, hmCap, _, _, hdet⟩ :=
    exists_completedLFunction_positive_LFunction_logDeriv_iterate_with_fixed_gamma hqbound hχ hp
      hinv hη hηsmall Krequested hKrequested hcre hcim hρre hzero hc hscale G hG hgamma
  have hKmax : K ≤ Kmax := hKglobal
  have hcap : n + 1 ≤ K * completedLFunctionNearOneDetectorMultiplicityCap := by
    rw [hnm]
    exact hmCap
  exact
    ⟨K, n, hKreq, hKmax, hn, (Nat.le_succ n).trans (hcap.trans (Nat.mul_le_mul_right _ hKmax)), by
      rw [hnm]; exact hmK, hcap, hdet⟩

/-- Under the numerical requested-order budgets, choose rate-independent detector
order bounds. For every admissible rate and sufficiently large scale, one finite
high-prime support and one incidence mesh work for all primitive characters and
near-one completed zeros satisfying the conductor-height scale condition.
Keep the physical-radius incidence gain and normalized signal at every incident point.
Apply the fixed-Gamma order envelope and the common high-prime window theorem.
This connects actual completed zeros to the shared finite-polynomial incidence interface. -/
theorem exists_uniform_high_prime_mesh_for_completed_near_one_zeros (Krequested : ℕ)
    (hKrequested : 2 ≤ Krequested)
    (hDrequested : ordinaryLFunctionNearOneDetectorExponent + 5 ≤ 5 * ((Krequested - 1 : ℕ) : ℝ))
    (hRorder :
      18 ≤ Real.exp (-(ordinaryLFunctionNearOneDetectorExponent + 6)) * ((Krequested - 1 : ℕ) : ℝ))
    (hm : Nat.ceil (Real.log higherPrimePowerEulerMajorantConstant) ≤ Krequested) :
    ∃ Kmax nmax : ℕ,
      Krequested ≤ Kmax ∧
        nmax = Kmax * completedLFunctionNearOneDetectorMultiplicityCap ∧
        ∀ (η : ℝ) (R Mmin : ℕ),
          0 < η →
            η ≤ 1 / 1288 →
            2 ≤ R →
            η * Real.log (R : ℝ) ≤ 3 →
            4 * η ≤ Real.exp (-(ordinaryLFunctionNearOneDetectorExponent + 5)) →
            ((2 * nmax + 1 : ℕ) : ℝ) ≤ 6 * Real.log (R : ℝ) →
            ∃ cutoff M W : ℕ,
              R ^ 6 ≤ cutoff ∧
                1 ≤ cutoff ∧
                Mmin ≤ M ∧
                0 < M ∧
                (W + 1 : ℝ) / M ≤ η / 8 ∧
                η * Real.exp (-(ordinaryLFunctionNearOneDetectorExponent * (Kmax : ℝ))) /
                    (16 * primeLogPowerVariationBound nmax) ≤
                  (2 * W + 1 : ℝ) / M ∧
                η * Real.log ((cutoff : ℝ) + 1) ≤
                  2 *
                      ((nmax : ℝ) + ordinaryLFunctionNearOneDetectorExponent * Kmax +
                        Real.log (24 * (Real.log 4 + 4))) +
                    η * Real.log ((R ^ 6 : ℕ) : ℝ) +
                    η * Real.log 3 ∧
                ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q},
                  2 ≤ q →
                    χ ≠ 1 →
                    χ.IsPrimitive →
                    χ⁻¹ ≠ 1 →
                    ∀ {ρ : ℂ},
                      |ρ.re - 1| ≤ η →
                        DirichletCharacter.completedLFunction χ ρ = 0 →
                        DirichletCharacter.completedLFunction χ
                            (((1 + η : ℝ) : ℂ) + (ρ.im : ℂ) * Complex.I) ≠
                          0 →
                        η * Real.log ((q : ℝ) * (|ρ.im| + 3)) ≤ 3 →
                        ∃ n ≤ nmax,
                          ∀ j : ℤ,
                            |ρ.im - (j : ℝ) / M| ≤ (W + 1 : ℝ) / M →
                              Real.exp (-(ordinaryLFunctionNearOneDetectorExponent * (Kmax : ℝ))) /
                                  16 ≤
                                (η ^ (n + 1) / (n.factorial : ℝ)) *
                                  ‖primeLogPowerPolynomial (highPrimeEulerSupport R cutoff) n
                                      (1 + η) (fun k ↦ χ (k : ZMod q)) ((j : ℝ) / M)‖ := by
  obtain ⟨Kmax, nmax, hKreqmax, hnmax, hdetector⟩ :=
    exists_uniform_near_one_detector_order_envelope Krequested hKrequested
  refine ⟨Kmax, nmax, hKreqmax, hnmax, ?_⟩
  intro η R Mmin hη hηsmall hR hRscale hηratio hlarge
  obtain ⟨cutoff, M, W, hcutoff, hcutpos, hMmin, hM, hwidth, hgain, hlog, hmesh⟩ :=
    exists_uniform_high_prime_signal_mesh_window η ordinaryLFunctionNearOneDetectorExponent
      Krequested Kmax nmax R Mmin hη (hηsmall.trans (by norm_num only))
      ordinaryLFunctionNearOneDetectorExponent_nonneg hR hDrequested hRscale hRorder hηratio hm
      hlarge
  refine ⟨cutoff, M, W, hcutoff, hcutpos, hMmin, hM, hwidth, hgain, hlog, ?_⟩
  intro q hq χ hqbound hχ hp hinv ρ hρre hzero hc hscale
  have hcre : ((((1 + η : ℝ) : ℂ) + (ρ.im : ℂ) * Complex.I).re) = 1 + η := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      zero_mul, mul_zero, sub_zero, add_zero]
  have hcim : ((((1 + η : ℝ) : ℂ) + (ρ.im : ℂ) * Complex.I).im) = ρ.im := by
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      Complex.I_re, mul_one, zero_mul, add_zero, zero_add]
  obtain ⟨K, n, hKreq, hKmax, _, hn, hKorder, _, hdet⟩ :=
    hdetector hqbound hχ hp hinv hη hηsmall hcre hcim hρre hzero hc hscale
  refine ⟨n, hn, ?_⟩
  intro j hj
  exact hmesh n hn K hKreq hKmax hKorder χ ρ.im hdet j hj

/-- For a primitive-family zero occurrence in a near-one rectangle, recover the
nonprincipal primitive character, nontrivial inverse, near-one zero, height bound,
nonvanishing shifted center, and local conductor-height scale.
Extract the occurrence and use the rectangle bounds and right-half-plane nonvanishing.
This discharges the completed-zero detector hypotheses without losing multiplicity indices. -/
theorem primitiveFamilyOccurrence_near_one_detector_context {Q : ℕ} {σ η : ℝ} (hσ : σ ≤ 1)
    (hσeta : 1 - σ ≤ η) (hη : 0 < η) (T : ℕ) (hglobal : η * Real.log ((Q : ℝ) * ((T : ℝ) + 3)) ≤ 3)
    {x :
      Σ q : Fin Q,
        Σ χ : DirichletCharacter ℂ (q.val + 1),
          Σ ρ : ℂ, Fin (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ)}
    (hx : x ∈ primitiveCharacterFamilyZeroOccurrenceLedger Q σ T) :
    2 ≤ x.1.val + 1 ∧
      x.2.1 ≠ 1 ∧
      x.2.1.IsPrimitive ∧
      x.2.1⁻¹ ≠ 1 ∧
      |x.2.2.1.re - 1| ≤ η ∧
      |x.2.2.1.im| ≤ (T : ℝ) ∧
      DirichletCharacter.completedLFunction x.2.1 x.2.2.1 = 0 ∧
      DirichletCharacter.completedLFunction x.2.1
          (((1 + η : ℝ) : ℂ) + (x.2.2.1.im : ℂ) * Complex.I) ≠
        0 ∧
      η * Real.log (((x.1.val + 1 : ℕ) : ℝ) * (|x.2.2.1.im| + 3)) ≤ 3 := by
  obtain ⟨q, χ, ρ, i, hχ, hxEq, hprim, hρ⟩ :=
    primitiveCharacterFamilyZeroOccurrenceLedger_mem_extract hx
  subst x
  have hmod : 2 ≤ q.val + 1 := by
    by_contra hmod
    have hqle : q.val + 1 ≤ 1 := Nat.le_of_lt_succ (Nat.lt_of_not_ge hmod)
    have hqone : q.val + 1 = 1 := Nat.le_antisymm hqle (Nat.succ_le_succ (Nat.zero_le q.val))
    have hsub : Subsingleton (DirichletCharacter ℂ (q.val + 1)) := by
      rw [hqone]
      exact (inferInstance : Subsingleton (DirichletCharacter ℂ 1))
    exact hχ (hsub.elim χ 1)
  have hneZero : NeZero (q.val + 1) := ⟨Nat.succ_ne_zero q.val⟩
  have hbox := (mem_completedZerosInRectangle_iff.mp hρ).1
  rw [dirichletCompletedLFunctionRectangleBox, Rectangle.rectangleClosedBox,
    Complex.mem_reProdIm] at hbox
  have hreBox : ρ.re ∈ Set.uIcc σ 1 := by
    simpa only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, sub_zero, mul_zero, Complex.add_re, Complex.one_re,
      add_zero] using hbox.1
  have hre : σ ≤ ρ.re ∧ ρ.re ≤ 1 := by simpa only [Set.uIcc_of_le hσ, Set.mem_Icc] using hreBox
  have hρre : |ρ.re - 1| ≤ η := by
    rw [abs_le]
    constructor <;> linarith only [hre.1, hre.2, hσeta]
  have hxocc :
    (⟨ρ, i⟩ : Σ z : ℂ, Fin (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) z)) ∈
      completedZeroMultiplicityOccurrences χ hχ ((σ : ℂ) - (T : ℝ) * Complex.I)
        ((1 : ℂ) + (T : ℝ) * Complex.I) := by
    simp only [completedZeroMultiplicityOccurrences, Finset.mem_sigma]
    exact ⟨hρ, Finset.mem_univ i⟩
  have hheight : |ρ.im| ≤ (T : ℝ) :=
    abs_le.mpr (completedZeroMultiplicityOccurrences_height_mem χ hχ σ T hxocc)
  have hzero := (mem_completedZerosInRectangle_iff.mp hρ).2
  have hcenter :
    DirichletCharacter.completedLFunction χ (((1 + η : ℝ) : ℂ) + (ρ.im : ℂ) * Complex.I) ≠ 0 := by
    apply @DirichletLFunction.completedLFunction_ne_zero_of_one_le_re (q.val + 1) hneZero χ hχ
    have hcre : ((((1 + η : ℝ) : ℂ) + (ρ.im : ℂ) * Complex.I).re) = 1 + η := by
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
        zero_mul, mul_zero, sub_zero, add_zero]
    rw [hcre]
    exact le_add_of_nonneg_right hη.le
  have hscale :=
    eta_log_conductor_height_le_of_cutoff_bound (Nat.zero_lt_of_lt q.isLt) hη.le hglobal q hheight
  exact
    ⟨hmod, hχ, hprim, by
      intro h; exact hχ (inv_eq_one.mp h), hρre, hheight, hzero, hcenter, hscale⟩

/-- For any detector exponent, choose a natural requested order satisfying the
low-prime, prime-power, and exponential margins. Take a natural number above the
finite maximum of the three real thresholds.
This removes external numerical order-budget assumptions from the family detector. -/
theorem exists_requested_high_prime_detector_order (D : ℝ) :
    ∃ Krequested : ℕ,
      2 ≤ Krequested ∧
        D + 5 ≤ 5 * ((Krequested - 1 : ℕ) : ℝ) ∧
        18 ≤ Real.exp (-(D + 6)) * ((Krequested - 1 : ℕ) : ℝ) ∧
        Nat.ceil (Real.log higherPrimePowerEulerMajorantConstant) ≤ Krequested := by
  let C : ℕ := Nat.ceil (Real.log higherPrimePowerEulerMajorantConstant)
  let A : ℝ := max 1 (max ((D + 5) / 5) (max (18 / Real.exp (-(D + 6))) (C : ℝ)))
  obtain ⟨N, hN⟩ := exists_nat_gt A
  have hA : A ≤ (N : ℝ) := hN.le
  have hN1 : (1 : ℝ) ≤ N := (le_max_left _ _).trans hA
  have hNorder : (D + 5) / 5 ≤ (N : ℝ) := (le_max_left _ _).trans ((le_max_right _ _).trans hA)
  have hNexp : 18 / Real.exp (-(D + 6)) ≤ (N : ℝ) :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hA))
  have hNC : (C : ℝ) ≤ N :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hA))
  refine
    ⟨N + 1, Nat.succ_le_succ (by exact_mod_cast hN1), ?_, ?_,
      (by exact_mod_cast hNC : C ≤ N).trans (Nat.le_succ N)⟩
  · rw [Nat.add_sub_cancel]
    have h := (div_le_iff₀ (by norm_num only : (0 : ℝ) < 5)).mp hNorder
    simpa only [mul_comm] using h
  · rw [Nat.add_sub_cancel]
    have h := (div_le_iff₀ (Real.exp_pos (-(D + 6)))).mp hNexp
    simpa only [mul_comm] using h

/-- Choose absolute near-one rate and scale thresholds and fixed order envelopes.
For any admissible primitive-family zero-occurrence ledger, one high-prime support
and one rational incidence mesh retain the normalized prime signal at every point
of each occurrence's detection window. Keep the physical-radius incidence gain,
support-length bound, and multiplicity-indexed ledger.
Select the numerical budgets, use the fixed-Gamma detector, and extract each occurrence.
This supplies actual zero-occurrence data for the normalized hybrid counting step. -/
theorem exists_uniform_high_prime_mesh_for_family_occurrences :
    ∃ η₀ : ℝ,
      0 < η₀ ∧
        ∃ R₀ Kmax nmax : ℕ,
          2 ≤ R₀ ∧
            2 ≤ Kmax ∧
            nmax = Kmax * completedLFunctionNearOneDetectorMultiplicityCap ∧
            ∀ (Q : ℕ) (σ : ℝ) (T : ℕ) (η : ℝ) (R Mmin : ℕ),
              σ ≤ 1 →
                1 - σ ≤ η →
                0 < η →
                η ≤ η₀ →
                R₀ ≤ R →
                η * Real.log (R : ℝ) ≤ 3 →
                η * Real.log ((Q : ℝ) * ((T : ℝ) + 3)) ≤ 3 →
                ∃ cutoff M W : ℕ,
                  R ^ 6 ≤ cutoff ∧
                    1 ≤ cutoff ∧
                    Mmin ≤ M ∧
                    0 < M ∧
                    (W + 1 : ℝ) / M ≤ η / 8 ∧
                    η * Real.exp (-(ordinaryLFunctionNearOneDetectorExponent * (Kmax : ℝ))) /
                        (16 * primeLogPowerVariationBound nmax) ≤
                      (2 * W + 1 : ℝ) / M ∧
                    η * Real.log ((cutoff : ℝ) + 1) ≤
                      2 *
                          ((nmax : ℝ) + ordinaryLFunctionNearOneDetectorExponent * Kmax +
                            Real.log (24 * (Real.log 4 + 4))) +
                        η * Real.log ((R ^ 6 : ℕ) : ℝ) +
                        η * Real.log 3 ∧
                    ∀
                      {x :
                        Σ q : Fin Q,
                          Σ χ : DirichletCharacter ℂ (q.val + 1),
                            Σ ρ : ℂ,
                              Fin (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ)},
                      x ∈ primitiveCharacterFamilyZeroOccurrenceLedger Q σ T →
                        ∃ n ≤ nmax,
                          ∀ j : ℤ,
                            |x.2.2.1.im - (j : ℝ) / M| ≤ (W + 1 : ℝ) / M →
                              Real.exp (-(ordinaryLFunctionNearOneDetectorExponent * (Kmax : ℝ))) /
                                  16 ≤
                                (η ^ (n + 1) / (n.factorial : ℝ)) *
                                  ‖primeLogPowerPolynomial (highPrimeEulerSupport R cutoff) n
                                      (1 + η) (fun k ↦ x.2.1 (k : ZMod (x.1.val + 1)))
                                      ((j : ℝ) / M)‖ := by
  obtain ⟨Krequested, hKrequested, hDrequested, hRorder, hm⟩ :=
    exists_requested_high_prime_detector_order ordinaryLFunctionNearOneDetectorExponent
  obtain ⟨Kmax, nmax, hKmax, hnmax, hfamily⟩ :=
    exists_uniform_high_prime_mesh_for_completed_near_one_zeros Krequested hKrequested hDrequested
      hRorder hm
  obtain ⟨R₀, hR₀, hdecrease⟩ := eventually_prime_energy_decreasing_range nmax
  let η₀ := min (1 / 1288 : ℝ) (Real.exp (-(ordinaryLFunctionNearOneDetectorExponent + 5)) / 4)
  have hη₀ : 0 < η₀ := lt_min (by norm_num only) (div_pos (Real.exp_pos _) (by norm_num only))
  refine ⟨η₀, hη₀, R₀, Kmax, nmax, hR₀, hKrequested.trans hKmax, hnmax, ?_⟩
  intro Q σ T η R Mmin hσ hσeta hη hηbound hRbound hRscale hglobal
  have hηsmall : η ≤ 1 / 1288 := hηbound.trans (min_le_left _ _)
  have hηratio : 4 * η ≤ Real.exp (-(ordinaryLFunctionNearOneDetectorExponent + 5)) := by
    have h := hηbound.trans (min_le_right _ _)
    have hmul := (le_div_iff₀ (by norm_num only : (0 : ℝ) < 4)).mp h
    simpa only [mul_comm] using hmul
  have hlarge : ((2 * nmax + 1 : ℕ) : ℝ) ≤ 6 * Real.log (R : ℝ) := by
    have h := hdecrease R hRbound 0 (le_refl 0) nmax le_rfl
    simpa only [zero_mul, mul_zero, add_zero, one_mul, Nat.cast_pow, Real.log_pow,
      Nat.cast_ofNat] using h
  obtain ⟨cutoff, M, W, hcutoff, hcutpos, hMmin, hM, hwidth, hgain, hlog, hzeros⟩ :=
    hfamily η R Mmin hη hηsmall (hR₀.trans hRbound) hRscale hηratio hlarge
  refine ⟨cutoff, M, W, hcutoff, hcutpos, hMmin, hM, hwidth, hgain, hlog, ?_⟩
  intro x hx
  obtain ⟨hmod, hχ, hprim, hinv, hρre, _, hzero, hcenter, hscale⟩ :=
    primitiveFamilyOccurrence_near_one_detector_context hσ hσeta hη T hglobal hx
  exact
    @hzeros (x.1.val + 1) ⟨Nat.succ_ne_zero x.1.val⟩ x.2.1 hmod hχ hprim hinv x.2.2.1 hρre hzero
      hcenter hscale

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity
