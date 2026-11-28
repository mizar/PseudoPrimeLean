/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrincipal644
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterEulerEndpoints644
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterReflectedCoefficients644
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMass644
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterGammaSeries644
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterTriangleZeroMass
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCosinePoles644
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCosineSplit644
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterZetaMass644
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSquare570
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCosinePoles644
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCosineSplit644
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMainGamma644
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMainEuler644
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterReflectedCoefficients644
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterTwoShiftZeta

/-! # Four comparisons using the principal, Euler and reflected estimates -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The signed reflected contribution of the section 122 trace at radius
`r`, including the physical power and kernel normalization. -/
noncomputable def quarterSignedReflected644 (r : ℝ) (τ : ℕ → ℝ) : ℝ :=
  let z := 2687 / 1000 + 2 * Real.log r
  let D :=
    (107 / 100 : ℝ) ^ 5 * Real.exp (-(107 / 100) * (2687 / 1000)) / 120 * r ^ (-(107 / 50) : ℝ)
  0 - D * (∑' n, τ n * (ArithmeticFunction.vonMangoldt n * quarterReflectedWeight z n))

private theorem comparison_row {r u E P S M A F : ℝ}
    (hE :
      0.03138163 * r + (quarterConductor644 r + 4 * positiveTail644 (r ^ 2)) ≤ 0.03138163 * u + E)
    (hP : 0.71798235 * r - P < quarterAdjustedGap644 r) (hS : F ≤ S - 0.0013281)
    (hM : M ≤ 3 / 4 * r - 11.7421197 + 4 * positiveTail644 (r ^ 2))
    (hC : quarterAdjustedGap644 r + 0.00063602 * r + A ≤ M + quarterConductor644 r + F) :
    A < 0.03138163 * u + E + P - 11.7421197 + S - 0.0013281 := by linarith only [hE, hP, hS, hM, hC]

/-- For radii from 316 to 322, the proved mass, principal, Euler and reflected
bounds contradict the section 122 passing inequality once the remaining
recovered terms reach their four stated thresholds. The residue at one is
already included in the adjusted principal gap. -/
theorem quarter_comparison_644 (hRH : RiemannHypothesis) {r M A : ℝ} (hr : r ∈ Set.Icc 316 322)
    (τ : ℕ → ℝ) (ht : ∀ n, -1 ≤ τ n ∧ τ n ≤ 3)
    (hp : ∀ n ∈ Finset.Ioc 0 99000, ArithmeticFunction.vonMangoldt n ≠ 0 → τ n = 3)
    (hM : M ≤ 3 / 4 * r - 11.7421197 + 4 * positiveTail644 (r ^ 2))
    (hA :
      (if r ≤ 320 then 0.783042
        else if r ≤ 1287 / 4 then 0.809968 else if r ≤ 1609 / 5 then 0.823698 else 0.816491) ≤
        A)
    (hC :
      quarterAdjustedGap644 r + 0.00063602 * r + A ≤
        M + quarterConductor644 r + quarterSignedReflected644 r τ) :
    False := by
  have he := quarter_euler_rows_644 hr
  have hP := quarter_principal_lower_rows_644 hRH
  by_cases h1 : r ≤ 320
  · rw [ite_eq_left h1] at he hA
    have hr' : r ∈ Set.Icc 316 (320) := ⟨hr.1, h1⟩
    have hs :=
      quarter_reflected_endpoint_644 hRH hr
        (show (320 : ℝ) ∈ Set.Icc 316 322 from ⟨by norm_num only, by norm_num only⟩) h1 τ ht hp
    have hs' : quarterSignedReflected644 r τ ≤ reflectedEnvelope644 (320) - 0.0013281 := hs
    have hv := comparison_row he (hP.1 r hr') hs' hM hC
    linarith only [hv, hA, reflected_envelope_644_320]
  rw [ite_eq_right h1] at he hA
  by_cases h2 : r ≤ 1287 / 4
  · rw [ite_eq_left h2] at he hA
    have hr' : r ∈ Set.Icc 320 (1287 / 4) := ⟨le_of_not_ge h1, h2⟩
    have hs :=
      quarter_reflected_endpoint_644 hRH hr
        (show (1287 / 4 : ℝ) ∈ Set.Icc 316 322 from ⟨by norm_num only, by norm_num only⟩) h2 τ ht hp
    have hs' : quarterSignedReflected644 r τ ≤ reflectedEnvelope644 (1287 / 4) - 0.0013281 := hs
    have hv := comparison_row he (hP.2.1 r hr') hs' hM hC
    linarith only [hv, hA, reflected_envelope_644_32175]
  rw [ite_eq_right h2] at he hA
  by_cases h3 : r ≤ 1609 / 5
  · rw [ite_eq_left h3] at he hA
    have hr' : r ∈ Set.Icc (1287 / 4) (1609 / 5) := ⟨le_of_not_ge h2, h3⟩
    have hs :=
      quarter_reflected_endpoint_644 hRH hr
        (show (1609 / 5 : ℝ) ∈ Set.Icc 316 322 from ⟨by norm_num only, by norm_num only⟩) h3 τ ht hp
    have hs' : quarterSignedReflected644 r τ ≤ reflectedEnvelope644 (1609 / 5) - 0.0013281 := hs
    have hv := comparison_row he (hP.2.2.1 r hr') hs' hM hC
    linarith only [hv, hA, reflected_envelope_644_3218]
  rw [ite_eq_right h3] at he hA
  have hr' : r ∈ Set.Icc (1609 / 5) 322 := ⟨le_of_not_ge h3, hr.2⟩
  have hs :=
    quarter_reflected_endpoint_644 hRH hr
      (show (322 : ℝ) ∈ Set.Icc 316 322 from ⟨by norm_num only, by norm_num only⟩) hr.2 τ ht hp
  have hs' : quarterSignedReflected644 r τ ≤ reflectedEnvelope644 (322) - 0.0013281 := hs
  have hv := comparison_row he (hP.2.2.2 r hr') hs' hM hC
  linarith only [hv, hA, reflected_envelope_644_322]

/-- Apply the four comparisons to the sum of the three even primitive
character masses. Agreement on primes through the cutoff also supplies
the trace-three hypothesis on the reflected prefix. -/
theorem quarter_character_comparison_644 {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ s)
    (hq : 2 ≤ p) (hs : 2 ≤ q) (ht : 2 ≤ s)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (pa : a.IsPrimitive)
    (pb : b.IsPrimitive) (pc : c.IsPrimitive) (na : a ≠ 1) (nb : b ≠ 1) (nc : c ≠ 1) (ea : a.Even)
    (eb : b.Even) (ec : c.Even) {r A : ℝ} (hr : r ∈ Set.Icc 316 322)
    (hlog : Real.log p + Real.log q + Real.log s ≤ 4 * r)
    (htr : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re)
    (ha : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → a l = 1)
    (hb : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → b l = 1)
    (hc : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → c l = 1)
    (hA :
      (if r ≤ 320 then 0.783042
        else if r ≤ 1287 / 4 then 0.809968 else if r ≤ 1609 / 5 then 0.823698 else 0.816491) ≤
        A)
    (hC :
      quarterAdjustedGap644 r + 0.00063602 * r + A ≤
        quarterMass644 a + quarterMass644 b + quarterMass644 c + quarterConductor644 r +
          quarterSignedReflected644 r (fun n ↦ (a n).re + (b n).re + (c n).re)) :
    False := by
  let τ := fun n : ℕ ↦ (a n).re + (b n).re + (c n).re
  have hX : 99000 ≤ r ^ 2 :=
    (by norm_num only : (99000 : ℝ) ≤ 316 ^ 2).trans (pow_le_pow_left₀ (by norm_num only) hr.1 2)
  have hhi : r ^ 2 ≤ 1000000 :=
    (pow_le_pow_left₀ (by linarith only [hr.1]) hr.2 2).trans (by norm_num only)
  have hsmall : ∀ l : ℕ, l ≤ 99000 → (l : ℝ) ≤ r ^ 2 := fun l hl ↦
    (show (l : ℝ) ≤ 99000 by exact_mod_cast hl).trans hX
  have hM :=
    quarter_even_cutoff_mass_644 a b c hq hs ht hG hG.riemann pa pb pc na nb nc ea eb ec hlog
      ((by norm_num only : (2701 : ℝ) ≤ 99000).trans hX) hhi htr ha hb hc
  apply quarter_comparison_644 hG.riemann hr τ _ _ hM hA hC
  · intro n
    exact
      ⟨htr n, by
        dsimp only [τ]
        linarith only [(Complex.re_le_norm _).trans (a.norm_le_one n),
          (Complex.re_le_norm _).trans (b.norm_le_one n),
          (Complex.re_le_norm _).trans (c.norm_le_one n)]⟩
  · intro n hn _
    have ⟨hn₀, hn₁⟩ := Finset.mem_Ioc.mp hn
    dsimp only [τ]
    rw [character_one_on_initial_interval (fun l hl h ↦ ha l hl (hsmall l h)) n hn₀ hn₁,
      character_one_on_initial_interval (fun l hl h ↦ hb l hl (hsmall l h)) n hn₀ hn₁,
      character_one_on_initial_interval (fun l hl h ↦ hc l hl (hsmall l h)) n hn₀ hn₁]
    norm_num only [Complex.one_re]

/-- The three main contour remainders absorb the principal logarithmic
adjustment and retain the certified gamma recovery on the section 122 interval. -/
theorem quarter_main_remainders_644 {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ s}
    (pa : a.IsPrimitive) (pb : b.IsPrimitive) (pc : c.IsPrimitive) (ha : a ≠ 1 ∧ a⁻¹ = a ∧ a.Even)
    (hb : b ≠ 1 ∧ b⁻¹ = b ∧ b.Even) (hc : c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) {r : ℝ}
    (hr : r ∈ Set.Icc 316 322) (hlog : Real.log p + Real.log q + Real.log s ≤ 4 * r) :
    let x := r ^ 2
    let R := quarterWeight644 x 1
    (contourRemainder644 a x).re + (contourRemainder644 b x).re + (contourRemainder644 c x).re +
        3 * Real.log (2 * Real.pi) * R ≤
      quarterConductor644 r + quarterSignedReflected644 r (fun n ↦ (a n).re + (b n).re + (c n).re) -
        1.023 * R -
        0.08136 := by
  intro x R
  have hr₁ : 1 ≤ r := by linarith only [hr.1]
  have hx : 1 ≤ x := one_le_pow₀ hr₁
  have hp := zero_lt_one.trans_le hx
  have ht := quarter_conductor_profile_644 hr₁
  have hprof :
    (quarterKernel644.transform x⁻¹).re =
      Analysis.rationalPoleProfile 3 (50 / 107) (2687 / 2000) x⁻¹ := by
    rw [quarterKernel644, LLS.PaperStatements.rationalPole_transform _ _ _ _ (inv_pos.mpr hp),
      Complex.ofReal_re]
  have hn := quarterKernel644.mellin_nonneg _ (inv_pos.mpr hp)
  change 0 ≤ (quarterKernel644.transform x⁻¹).re at hn
  change 4 * r * (quarterKernel644.transform x⁻¹).re = _ at ht
  rw [hprof] at hn ht
  have hcond := mul_le_mul_of_nonneg_right hlog hn
  have hE :
    -(quarterMainEuler644 a x + quarterMainEuler644 b x + quarterMainEuler644 c x) =
      quarterSignedReflected644 r (fun n ↦ (a n).re + (b n).re + (c n).re) := by
    rw [quarter_main_euler_trace_644 a b c hx]
    unfold quarterSignedReflected644
    dsimp only [x]
    rw [← Real.rpow_natCast_mul (zero_le_one.trans hr₁), Real.log_pow]
    norm_num only [Nat.cast_ofNat, zero_sub]
  have hG := quarter_gamma_adjusted_recovery_644 ha hb hc hr
  rw [quarter_main_arch_split_644 pa ha.1 ha.2.1 hp, quarter_main_arch_split_644 pb hb.1 hb.2.1 hp,
    quarter_main_arch_split_644 pc hc.1 hc.2.1 hp]
  dsimp only [R, x] at hG hcond ht hE ⊢
  linarith only [hG, hE, hcond, ht]

/-- The three shifted main contours have one common even Gamma contribution.
Their reflected Euler sums can be written as the level-one contribution plus
the trace deficit already bounded in the section 122 comparison. -/
theorem quarter_shifted_remainders_644 {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ s}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) {r : ℝ} (hr : 0 < r) (h : ℝ) :
    let x := r ^ 2 * Real.exp (-(2687 / 1000 + h))
    (contourRemainder644 a x).re + (contourRemainder644 b x).re + (contourRemainder644 c x).re =
      (Real.log p + Real.log q + Real.log s) *
          Analysis.rationalPoleProfile 3 (50 / 107) (2687 / 2000) x⁻¹ +
        3 * ((quarterLevelGamma644 x).re - quarterMainEuler644 (1 : DirichletCharacter ℂ 1) x) +
        quarterShiftLoss644 a b c r h := by
  intro x
  have hx : 0 < x := mul_pos (pow_pos hr _) (Real.exp_pos _)
  rw [quarter_main_arch_split_644 ha.1 ha.2.1 ha.2.2.1 hx,
    quarter_main_arch_split_644 hb.1 hb.2.1 hb.2.2.1 hx,
    quarter_main_arch_split_644 hc.1 hc.2.1 hc.2.2.1 hx,
    quarter_even_level_gamma_644 a ha.2.1 ha.2.2.2 x,
    quarter_even_level_gamma_644 b hb.2.1 hb.2.2.2 x,
    quarter_even_level_gamma_644 c hc.2.1 hc.2.2.2 x]
  change
    _ =
      _ +
        (3 * quarterMainEuler644 (1 : DirichletCharacter ℂ 1) x -
          (quarterMainEuler644 a x + quarterMainEuler644 b x + quarterMainEuler644 c x))
  ring

/-- For scales at least one, the normalized right-minus-left pole integral
of the main kernel is its weighted value at either half-unit point. -/
theorem quarter_main_xi_pole_644 {x u : ℝ} (hx : 1 ≤ x) (hl : -9 / 16 < u) (hu : u < 9 / 16) :
    quarterCosinePole quarterKernel644 (9 / 16) u x -
        quarterCosinePole quarterKernel644 (-9 / 16) u x =
      quarterKernel644.function (u : ℂ) * (x : ℂ) ^ (u : ℂ) := by
  apply quarter_cosine_pole_diff quarterKernel644 _ _ hx hl hu
  · norm_num only [quarterKernel644, LLS.PaperStatements.rationalPoleMellinKernel,
      min_eq_right (by norm_num only : (1 / 8 : ℝ) ≤ 57 / 400)]
  · intro z hz _
    have hn : z + (107 / 100 : ℂ) ≠ 0 := by
      intro he
      have hre := congrArg Complex.re he
      have hcast : (107 / 100 : ℂ) = ((107 / 100 : ℝ) : ℂ) := by
        norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat]
      rw [hcast, Complex.add_re, Complex.ofReal_re, Complex.zero_re] at hre
      linarith only [hz, hre]
    rw [show quarterKernel644.function = fun z : ℂ ↦ _ from funext quarter_function_644]
    have hnum :
      AnalyticAt ℂ (fun w : ℂ ↦ (107 / 100 : ℂ) ^ 5 * Complex.exp ((2687 / 1000) * w)) z := by
      fun_prop
    have hden : AnalyticAt ℂ (fun w : ℂ ↦ (w + (107 / 100 : ℂ)) ^ 6) z := by fun_prop
    exact hnum.div hden (pow_ne_zero 6 hn)

/-- On the main left contour, reflect the negative xi logarithmic
derivative to the right half-plane and separate Gamma, zeta and the poles. -/
theorem quarter_main_left_xi_644 (t : ℝ) :
    let z : ℂ := ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    let w : ℂ := ((17 / 16 : ℝ) : ℂ) - Complex.I * t
    (-logDeriv AnalyticNumberTheory.RiemannXi.riemannXi (z + 1 / 2)) =
      logDeriv (1 : DirichletCharacter ℂ 1).gammaFactor w + logDeriv riemannZeta w -
        1 / (z - 1 / 2) -
        1 / (z + 1 / 2) := by
  intro z w
  have hw : 1 < w.re := by
    simp only [w, Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul]
    norm_num only
  have h₁ : z + 1 / 2 = 1 - w := by
    dsimp only [z, w]; push_cast; ring
  have h₂ : w = -(z - 1 / 2) := by linear_combination h₁
  have h₃ : w - 1 = -(z + 1 / 2) := by linear_combination h₂
  rw [h₁, AnalyticNumberTheory.RiemannXi.logDeriv_one_sub, neg_neg,
    AnalyticNumberTheory.RiemannXi.logDeriv_eq_poles_gamma_zeta_of_re_gt_one hw]
  rw [h₃, h₂, div_neg, div_neg]
  ring

/-- On the main right contour, separate the positive xi logarithmic
derivative into Gamma, zeta and the two shifted simple poles. -/
theorem quarter_main_right_xi_644 (t : ℝ) :
    let z : ℂ := ((9 / 16 : ℝ) : ℂ) + Complex.I * t
    let w : ℂ := z + 1 / 2
    logDeriv AnalyticNumberTheory.RiemannXi.riemannXi w =
      logDeriv (1 : DirichletCharacter ℂ 1).gammaFactor w + logDeriv riemannZeta w +
        1 / (z - 1 / 2) +
        1 / (z + 1 / 2) := by
  intro z w
  have hw : 1 < w.re := by
    simp only [z, w, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, Complex.div_ofNat_re, Complex.one_re]
    norm_num only
  have h : w - 1 = z - 1 / 2 := by
    dsimp only [w]
    ring
  rw [AnalyticNumberTheory.RiemannXi.logDeriv_eq_poles_gamma_zeta_of_re_gt_one hw, h]
  ring

/-- The normalized negative xi logarithmic derivative integral of the main
kernel at a real scale and vertical line. The shifted comparison uses the
left and right lines at minus and plus nine sixteenths. -/
noncomputable def quarterMainXiLine644 (d x : ℝ) : ℂ :=
  let z := fun t : ℝ ↦ (d : ℂ) + Complex.I * t
  ((1 / (2 * Real.pi) : ℝ) : ℂ) *
    ∫ t : ℝ,
      -logDeriv AnalyticNumberTheory.RiemannXi.riemannXi (z t + 1 / 2) *
        (quarterKernel644.function (z t) * (x : ℂ) ^ z t)

/-- The forward level-one sum at positive scale decomposes into the right
xi line, its two pole integrals, and the right Gamma integral. -/
theorem quarter_main_level_forward_644 {x : ℝ} (hx : 0 < x) :
    (∑' n : ℕ, quarterKernel644.summand (1 : DirichletCharacter ℂ 1) x n) =
      quarterMainXiLine644 (9 / 16) x + quarterCosinePole quarterKernel644 (9 / 16) (-1 / 2) x +
        quarterCosinePole quarterKernel644 (9 / 16) (1 / 2) x +
        quarterRightGamma644 (1 : DirichletCharacter ℂ 1) x := by
  have hd : quarterKernel644.delta = (1 / 8 : ℝ) := by
    norm_num only [quarterKernel644, LLS.PaperStatements.rationalPoleMellinKernel,
      min_eq_right (by norm_num only : (1 / 8 : ℝ) ≤ 57 / 400)]
  rw [twoShift_level_one_forward quarterKernel644 hd hx]
  unfold quarterMainXiLine644 quarterCosinePole quarterRightGamma644
  dsimp only
  ring

/-- At positive scale, the left Gamma integral less the reflected Euler
integral equals the left xi line and its two pole integrals in real part. -/
theorem quarter_main_level_left_644 {x : ℝ} (hx : 0 < x) :
    (quarterLevelGamma644 x - quarterRightGamma644 (1 : DirichletCharacter ℂ 1) x).re -
        quarterMainEuler644 (1 : DirichletCharacter ℂ 1) x =
      (quarterMainXiLine644 (-9 / 16) x + quarterCosinePole quarterKernel644 (-9 / 16) (-1 / 2) x +
          quarterCosinePole quarterKernel644 (-9 / 16) (1 / 2) x).re := by
  let z := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
  let w := fun t : ℝ ↦ ((17 / 16 : ℝ) : ℂ) - Complex.I * t
  let W := fun t ↦ quarterKernel644.function (z t) * (x : ℂ) ^ z t
  let F := fun t ↦ -logDeriv AnalyticNumberTheory.RiemannXi.riemannXi (z t + 1 / 2) * W t
  let E := fun t ↦ -logDeriv riemannZeta (w t) * W t
  let P := fun t ↦ (1 / (z t - ((-1 / 2 : ℝ) : ℂ))) * W t
  let Q := fun t ↦ (1 / (z t - ((1 / 2 : ℝ) : ℂ))) * W t
  let G := fun t ↦ logDeriv (1 : DirichletCharacter ℂ 1).gammaFactor (w t) * W t
  have hd : quarterKernel644.delta = (1 / 8 : ℝ) := by
    norm_num only [quarterKernel644, LLS.PaperStatements.rationalPoleMellinKernel,
      min_eq_right (by norm_num only : (1 / 8 : ℝ) ≤ 57 / 400)]
  have hl : -1 / 2 - quarterKernel644.delta < (-9 / 16 : ℝ) := by
    rw [hd]; norm_num only
  have hu : (-9 / 16 : ℝ) ≤ 1 / 2 + quarterKernel644.delta := by
    rw [hd]; norm_num only
  have hiF : MeasureTheory.Integrable F :=
    LLS.PaperStatements.MellinKernel.integrable_xi_left_line quarterKernel644 hl (by norm_num only)
      (by norm_num only) hx
  have hiE : MeasureTheory.Integrable E := by
    simpa only [E, w, W, z, Complex.ofReal_neg, mul_neg, ← sub_eq_add_neg,
      DirichletCharacter.LFunction_modOne_eq] using
      quarter_ordinary_integrable_644 (1 : DirichletCharacter ℂ 1) hx
  have hiP : MeasureTheory.Integrable P := by
    simpa only [P, W, z, mul_assoc] using
      LLS.PaperStatements.MellinKernel.integrable_pole_power_line quarterKernel644 hl hu
        (by norm_num only) (by norm_num only : (-9 / 16 : ℝ) ≠ -1 / 2) hx
  have hiQ : MeasureTheory.Integrable Q := by
    simpa only [Q, W, z, mul_assoc] using
      LLS.PaperStatements.MellinKernel.integrable_pole_power_line quarterKernel644 hl hu
        (by norm_num only) (by norm_num only : (-9 / 16 : ℝ) ≠ 1 / 2) hx
  have hG : G = (F + E + P + Q) := by
    funext t
    dsimp only [Pi.add_apply, G, F, E, P, Q]
    rw [quarter_main_left_xi_644 t]
    simp only [z, w, Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_ofNat]
    ring
  have hw (t : ℝ) : 1 / 2 - z t = w t := by
    dsimp only [z, w]
    push_cast
    ring
  unfold quarterLevelGamma644 quarterMainEuler644 quarterMainXiLine644 quarterCosinePole
  dsimp only [z, w] at hw
  simp only [add_sub_cancel_right, hw, DirichletCharacter.LFunction_modOne_eq]
  change (_ * ∫ t, G t).re - (_ * ∫ t, E t).re = (_ * (∫ t, F t) + _ * (∫ t, P t) + _ * ∫ t, Q t).re
  have h₁ := MeasureTheory.integral_add ((hiF.add hiE).add hiP) hiQ
  have h₂ := MeasureTheory.integral_add (hiF.add hiE) hiP
  have h₃ := MeasureTheory.integral_add hiF hiE
  simp only [Pi.add_apply] at h₁ h₂ h₃
  simp only [hG, Pi.add_apply]
  rw [h₁, h₂, h₃]
  simp only [mul_add, Complex.add_re]
  ring

/-- At scale at least one, the principal forward and reflected terms cancel
the two Gamma integrals, leaving the xi line difference and the two residues. -/
theorem quarter_main_level_cancel_644 {x : ℝ} (hx : 1 ≤ x) :
    (quarterLevelGamma644 x).re - quarterMainEuler644 (1 : DirichletCharacter ℂ 1) x -
        (∑' n : ℕ, quarterKernel644.summand (1 : DirichletCharacter ℂ 1) x n).re =
      (quarterMainXiLine644 (-9 / 16) x - quarterMainXiLine644 (9 / 16) x -
          quarterKernel644.function ((-1 / 2 : ℝ) : ℂ) * (x : ℂ) ^ ((-1 / 2 : ℝ) : ℂ) -
          quarterKernel644.function ((1 / 2 : ℝ) : ℂ) * (x : ℂ) ^ ((1 / 2 : ℝ) : ℂ)).re := by
  have hp := zero_lt_one.trans_le hx
  have hL := quarter_main_level_left_644 hp
  have hR := congrArg Complex.re (quarter_main_level_forward_644 hp)
  have ha :=
    congrArg Complex.re
      (quarter_main_xi_pole_644 hx (u := -1 / 2) (by norm_num only) (by norm_num only))
  have hb :=
    congrArg Complex.re
      (quarter_main_xi_pole_644 hx (u := 1 / 2) (by norm_num only) (by norm_num only))
  simp only [Complex.add_re, Complex.sub_re] at hL hR ha hb ⊢
  linarith only [hL, hR, ha, hb]

/-- Under RH and at scale at least one, the main left-minus-right xi contour
is the oscillating zeta zero sum. The main kernel has no extra residue. -/
theorem quarter_main_xi_zeros_644 (hRH : RiemannHypothesis) {x : ℝ} (hx : 1 ≤ x) :
    quarterMainXiLine644 (-9 / 16) x - quarterMainXiLine644 (9 / 16) x =
      ∑' ρ, quarterKernel644.zetaOscillatingZeroTerm x ρ := by
  have hd : quarterKernel644.delta = (1 / 8 : ℝ) := by
    norm_num only [quarterKernel644, LLS.PaperStatements.rationalPoleMellinKernel,
      min_eq_right (by norm_num only : (1 / 8 : ℝ) ≤ 57 / 400)]
  have he :=
    LLS.PaperStatements.MellinKernel.xiContourIdentity quarterKernel644 hRH (a := -9 / 16) (b :=
      9 / 16)
      (by
        rw [hd]; norm_num only)
      (by
        rw [hd]; norm_num only)
      (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only) hx
  simp only [pole_residue_zero_644, zero_sub, mul_comm _ Complex.I] at he
  rw [mul_assoc] at he
  have h := mul_left_cancel₀ Complex.I_ne_zero he
  let d : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ)
  have hi : d * (2 * (Real.pi : ℂ)) = 1 := by
    dsimp only [d]
    rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_ofNat, one_div,
      inv_mul_cancel₀ (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))]
  have hh := congrArg (fun u : ℂ ↦ d * u) h
  rw [mul_sub, ← mul_assoc, hi, one_mul] at hh
  unfold quarterMainXiLine644
  linear_combination -hh

/-- Under RH the main xi contour difference at any scale at least one is
bounded in absolute value by the certified unmodulated zero mass. -/
theorem quarter_main_xi_abs_644 (hRH : RiemannHypothesis) {x : ℝ} (hx : 1 ≤ x) :
    |(quarterMainXiLine644 (-9 / 16) x - quarterMainXiLine644 (9 / 16) x).re| ≤ 32 / 75000000 := by
  rw [quarter_main_xi_zeros_644 hRH hx]
  have hp := zero_lt_one.trans_le hx
  have hs :=
    LLS.PaperStatements.MellinKernel.summable_zetaOscillatingZeroTerm quarterKernel644 hRH hp
  refine (Complex.abs_re_le_norm _).trans ((norm_tsum_le_tsum_norm hs.norm).trans ?_)
  simpa only [LLS.PaperStatements.MellinKernel.norm_zetaOscillatingZeroTerm _ hp] using
    quarter_zeta_mass_644 hRH

/-- Above radius 316, the three shifted xi contour differences from the
three pair characters contribute at least minus 0.00000402 under RH. -/
theorem quarter_main_xi_mix_lower_644 (hRH : RiemannHypothesis) {r : ℝ} (hr : 316 ≤ r) :
    let D := fun h : ℝ ↦
      let x := r ^ 2 * Real.exp (-(2687 / 1000 + h))
      (quarterMainXiLine644 (-9 / 16) x - quarterMainXiLine644 (9 / 16) x).re
    (-0.00000402 : ℝ) ≤ 3 * (1.54 * D 0 - 1.508 * D (1 / 50) - 0.0917 * D (11 / 10)) := by
  intro D
  have h (t : ℝ) (ht : t ≤ 11 / 10) : |D t| ≤ 32 / 75000000 :=
    quarter_main_xi_abs_644 hRH (quarter_shift_scale_ge_one_644 hr ht)
  linarith only [(abs_le.mp (h 0 (by norm_num only))).1,
    (abs_le.mp (h (1 / 50) (by norm_num only))).2, (abs_le.mp (h _ le_rfl)).2]

/-- At a shifted scale at least one, subtract the three level-one forward
sums from the main contours. The remainder consists of conductor and
reflected trace deficit terms, the xi zero sum, and the two residues. -/
theorem quarter_shifted_forward_diff_644 {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ s}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hRH : RiemannHypothesis) {r h : ℝ}
    (hr : 316 ≤ r) (hh : h ≤ 11 / 10) :
    let x := r ^ 2 * Real.exp (-(2687 / 1000 + h))
    (contourRemainder644 a x).re + (contourRemainder644 b x).re + (contourRemainder644 c x).re -
        3 * (∑' n : ℕ, quarterKernel644.summand (1 : DirichletCharacter ℂ 1) x n).re =
      (Real.log p + Real.log q + Real.log s) *
          Analysis.rationalPoleProfile 3 (50 / 107) (2687 / 2000) x⁻¹ +
        quarterShiftLoss644 a b c r h +
        3 *
          ((∑' ρ, quarterKernel644.zetaOscillatingZeroTerm x ρ) -
              quarterKernel644.function ((-1 / 2 : ℝ) : ℂ) * (x : ℂ) ^ ((-1 / 2 : ℝ) : ℂ) -
              quarterKernel644.function ((1 / 2 : ℝ) : ℂ) * (x : ℂ) ^ ((1 / 2 : ℝ) : ℂ)).re := by
  intro x
  have hx : 1 ≤ x := quarter_shift_scale_ge_one_644 hr hh
  have hR := quarter_shifted_remainders_644 ha hb hc (by linarith only [hr]) h
  have hL := quarter_main_level_cancel_644 hx
  rw [quarter_main_xi_zeros_644 hRH hx] at hL
  dsimp only [x] at hR hL ⊢
  linarith only [hR, hL]

/-- On the section 122 radius range, the three shifted forward differences
have a joint lower bound retaining the conductor and residue terms and
using the certified xi mass and reflected trace deficit. -/
theorem quarter_shifted_forward_mix_644 {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ s}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hRH : RiemannHypothesis) {r : ℝ} (hr : 316 ≤ r)
    (ht : ∀ n : ℕ, (a n).re + (b n).re + (c n).re ∈ Set.Icc (-1) 3)
    (hp :
      ∀ n ∈ Finset.Ioc 0 99000,
        ArithmeticFunction.vonMangoldt n ≠ 0 → (a n).re + (b n).re + (c n).re = 3) :
    let X := fun h : ℝ ↦ r ^ 2 * Real.exp (-(2687 / 1000 + h))
    let T := fun h : ℝ ↦
      (contourRemainder644 a (X h)).re + (contourRemainder644 b (X h)).re +
          (contourRemainder644 c (X h)).re -
        3 * (∑' n : ℕ, quarterKernel644.summand (1 : DirichletCharacter ℂ 1) (X h) n).re
    let P := fun h : ℝ ↦
      (Real.log p + Real.log q + Real.log s) *
          Analysis.rationalPoleProfile 3 (50 / 107) (2687 / 2000) (X h)⁻¹ -
        3 *
          (quarterKernel644.function ((-1 / 2 : ℝ) : ℂ) * (X h : ℂ) ^ ((-1 / 2 : ℝ) : ℂ) +
              quarterKernel644.function ((1 / 2 : ℝ) : ℂ) * (X h : ℂ) ^ ((1 / 2 : ℝ) : ℂ)).re
    let ν := 1.508 - 1.54 * Real.exp (-((107 / 100) * (1 / 50)))
    1.54 * P 0 - 1.508 * P (1 / 50) - 0.0917 * P (11 / 10) - 0.00000402 -
        ν * quarterShiftCap644 r (1 / 50) -
        0.0917 * quarterShiftCap644 r (11 / 10) ≤
      1.54 * T 0 - 1.508 * T (1 / 50) - 0.0917 * T (11 / 10) := by
  intro X T P ν
  have h (t : ℝ) (ht' : t ≤ 11 / 10) := quarter_shifted_forward_diff_644 ha hb hc hRH hr ht'
  have hD (t : ℝ) (ht' : t ≤ 11 / 10) :=
    quarter_main_xi_zeros_644 hRH (quarter_shift_scale_ge_one_644 hr ht')
  have he (t : ℝ) (ht' : t ≤ 11 / 10) :
    T t =
      P t + quarterShiftLoss644 a b c r t +
        3 * (quarterMainXiLine644 (-9 / 16) (X t) - quarterMainXiLine644 (9 / 16) (X t)).re := by
    dsimp only [T, P, X]
    rw [h t ht', hD t ht']
    simp only [Complex.add_re, Complex.sub_re]
    ring
  rw [he 0 (by norm_num only), he (1 / 50) (by norm_num only), he (11 / 10) le_rfl]
  have hξ := quarter_main_xi_mix_lower_644 hRH hr
  have hE := quarter_shift_mix_at_radius_644 a b c hRH hr (fun n ↦ (ht n : _ ∧ _)) hp
  dsimp only [X, P, ν] at hξ hE ⊢
  linarith only [hξ, hE]

/-- At positive radius the negative half-point residue of the shifted
main kernel is an inverse-radius term times the exponential of half the shift. -/
theorem quarter_shifted_neg_pole_644 {r : ℝ} (hr : 0 < r) (h : ℝ) :
    let x := r ^ 2 * Real.exp (-(2687 / 1000 + h))
    (quarterKernel644.function ((-1 / 2 : ℝ) : ℂ) * (x : ℂ) ^ ((-1 / 2 : ℝ) : ℂ)).re =
      ((107 / 100 : ℝ) ^ 5 / (57 / 100) ^ 6) / r * Real.exp (h / 2) := by
  intro x
  have he : Real.log x * (-1 / 2) = (2687 / 1000 + h) / 2 - Real.log r := by
    dsimp only [x]
    rw [Real.log_mul (pow_ne_zero _ hr.ne') (Real.exp_pos _).ne', Real.log_pow, Real.log_exp]
    ring
  have hx : 0 < x := mul_pos (pow_pos hr _) (Real.exp_pos _)
  have hf :
    quarterKernel644.function ((-1 / 2 : ℝ) : ℂ) =
      ((((107 / 100 : ℝ) ^ 5 / (57 / 100) ^ 6) * Real.exp (-(2687 / 2000)) : ℝ) : ℂ) := by
    rw [quarter_function_644, Complex.ofReal_mul, Complex.ofReal_exp]
    push_cast
    norm_num only
    ring
  rw [hf, ← Complex.ofReal_cpow hx.le, ← Complex.ofReal_mul, Complex.ofReal_re,
    Real.rpow_def_of_pos hx, he, Real.exp_sub, Real.exp_log hr,
    show ((2687 / 1000 : ℝ) + h) / 2 = 2687 / 2000 + h / 2 by ring, Real.exp_add, Real.exp_neg]
  field_simp [hr.ne', (Real.exp_pos (2687 / 2000)).ne']

/-- On the section 122 interval the signed negative half-point residues
contribute at least 0.05413. Lower Taylor sums suffice for both exponentials. -/
theorem quarter_neg_pole_mix_lower_644 {r : ℝ} (hr : r ∈ Set.Icc 316 322) :
    (0.05413 : ℝ) ≤
      3 * (((107 / 100 : ℝ) ^ 5 / (57 / 100) ^ 6) / r) *
        (1.508 * Real.exp (1 / 100) + 0.0917 * Real.exp (11 / 20) - 1.54) := by
  have h₁ := Real.sum_le_exp_of_nonneg (by norm_num only : 0 ≤ (1 / 100 : ℝ)) 3
  have h₂ := Real.sum_le_exp_of_nonneg (by norm_num only : 0 ≤ (11 / 20 : ℝ)) 6
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
    Nat.cast_one, Nat.cast_zero] at h₁ h₂
  have hr₀ : 0 < r := by linarith only [hr.1]
  rw [show
      3 * ((107 / 100 : ℝ) ^ 5 / (57 / 100) ^ 6 / r) *
          (1.508 * Real.exp (1 / 100) + 0.0917 * Real.exp (11 / 20) - 1.54) =
        (3 * ((107 / 100 : ℝ) ^ 5 / (57 / 100) ^ 6) *
            (1.508 * Real.exp (1 / 100) + 0.0917 * Real.exp (11 / 20) - 1.54)) /
          r
      by ring,
    le_div_iff₀ hr₀]
  linarith only [hr.2, h₁, h₂]

/-- On the section 122 radius range, write the shifted conductor profile
using the logarithm of the radius and the shift. -/
theorem quarter_shift_conductor_644 {r h : ℝ} (hr : 316 ≤ r) (hh : h ≤ 11 / 10) :
    let x := r ^ 2 * Real.exp (-(2687 / 1000 + h))
    let z := (107 / 100 : ℝ) * (2 * Real.log r - h)
    4 * r * Analysis.rationalPoleProfile 3 (50 / 107) (2687 / 2000) x⁻¹ =
      4 * r * (z ^ 5 * Real.exp (-z) / 120) := by
  intro x z
  have hr₀ : 0 < r := by linarith only [hr]
  have hx := zero_lt_one.trans_le (quarter_shift_scale_ge_one_644 hr hh)
  have hl : Real.log (x⁻¹) = 2687 / 1000 + h - 2 * Real.log r := by
    dsimp only [x]
    rw [Real.log_inv, Real.log_mul (pow_ne_zero _ hr₀.ne') (Real.exp_pos _).ne', Real.log_pow,
      Real.log_exp]
    ring
  have hs : Real.log (x⁻¹) ≤ 2687 / 1000 :=
    (Real.log_nonpos (inv_pos.mpr hx).le
          (inv_le_one_of_one_le₀ (quarter_shift_scale_ge_one_644 hr hh))).trans
      (by norm_num only)
  have hp :
    (quarterKernel644.transform x⁻¹).re =
      Analysis.rationalPoleProfile 3 (50 / 107) (2687 / 2000) x⁻¹ := by
    rw [quarterKernel644, LLS.PaperStatements.rationalPole_transform _ _ _ _ (inv_pos.mpr hx),
      Complex.ofReal_re]
  rw [← hp, quarter_transform_644 (inv_pos.mpr hx) hs, hl]
  rw [show (107 / 100 : ℝ) * (2687 / 1000 - (2687 / 1000 + h - 2 * Real.log r)) = z
      by
      dsimp only [z]
      ring]

/-- Factor out the same positive power of the radius from each shifted
conductor term. The remaining dependence on the radius is polynomial in its logarithm. -/
theorem quarter_shift_conductor_factor_644 {r : ℝ} (hr : 0 < r) (h : ℝ) :
    let a := (107 / 100 : ℝ)
    let z := a * (2 * Real.log r - h)
    4 * r * (z ^ 5 * Real.exp (-z) / 120) =
      (a ^ 5 / 30 * r ^ (-(57 / 50) : ℝ)) * (Real.exp (a * h) * (2 * Real.log r - h) ^ 5) := by
  intro a z
  have he : -z = (-(57 / 50) : ℝ) * Real.log r - Real.log r + a * h := by
    dsimp only [z, a]
    ring
  rw [he, Real.exp_add, Real.exp_sub, Real.exp_log hr, Real.rpow_def_of_pos hr]
  rw [mul_comm (Real.log r) (-(57 / 50) : ℝ)]
  dsimp only [z]
  field_simp [hr.ne']
  ring

/-- Bound a shifted monomial by a multiple of the unshifted monomial,
using monotonicity of the shift ratio up to the upper logarithmic endpoint. -/
private theorem shifted_monomial_cap {y h w u B : ℝ} (hy : y ≤ 11.55) (hh : 0 ≤ h) (hhy : h ≤ y)
    (hw : 0 ≤ w) (he : Real.exp ((107 / 100) * h) ≤ u) (hB : w * u * (1 - h / 11.55) ^ 5 ≤ B) :
    w * (Real.exp ((107 / 100) * h) * (y - h) ^ 5) ≤ B * y ^ 5 := by
  have hy₀ := hh.trans hhy
  have hu := (Real.exp_pos _).le.trans he
  have hm : y - h ≤ (1 - h / 11.55) * y := by
    calc
      y - h ≤ y - h + h * (11.55 - y) / 11.55 :=
        le_add_of_nonneg_right (div_nonneg (mul_nonneg hh (sub_nonneg.mpr hy)) (by norm_num only))
      _ = _ := by ring
  have hp := pow_le_pow_left₀ (sub_nonneg.mpr hhy) hm 5
  rw [mul_pow] at hp
  calc
    _ ≤ (w * u) * ((1 - h / 11.55) ^ 5 * y ^ 5) := by
      rw [← mul_assoc]
      exact
        mul_le_mul (mul_le_mul_of_nonneg_left he hw) hp (pow_nonneg (sub_nonneg.mpr hhy) _)
          (mul_nonneg hw hu)
    _ = (w * u * (1 - h / 11.55) ^ 5) * y ^ 5 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hB (pow_nonneg hy₀ _)

/-- For the section 122 logarithmic argument, bound the signed conductor
polynomial below by minus 0.167715 times the unshifted fifth power. -/
theorem quarter_shift_poly_lower_644 {y : ℝ} (hl : 11 / 10 ≤ y) (hu : y ≤ 11.55) :
    -0.167715 * y ^ 5 ≤
      1.54 * y ^ 5 - 1.508 * (Real.exp ((107 / 100) * (1 / 50)) * (y - 1 / 50) ^ 5) -
        0.0917 * (Real.exp ((107 / 100) * (11 / 10)) * (y - 11 / 10) ^ 5) := by
  have he₁ :=
    Analysis.exp_le_taylor_add_two_next (x := (107 / 5000 : ℝ)) (n := 12) (by norm_num only)
      (by norm_num only)
  have he₂ :=
    Analysis.exp_le_taylor_add_two_next (x := (1177 / 1000 : ℝ)) (n := 12) (by norm_num only)
      (by norm_num only)
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
    Nat.cast_one, Nat.cast_zero] at he₁ he₂
  have h₁ : Real.exp ((107 / 100) * (1 / 50)) ≤ 1.021631 := by
    rw [show (107 / 100 : ℝ) * (1 / 50) = 107 / 5000 by norm_num only]
    linarith only [he₁]
  have h₂ : Real.exp ((107 / 100) * (11 / 10)) ≤ 3.24464 := by
    rw [show (107 / 100 : ℝ) * (11 / 10) = 1177 / 1000 by norm_num only]
    linarith only [he₂]
  have hA :=
    shifted_monomial_cap (w := 1.508) (B := 1.527327) hu (by norm_num only) (by linarith only [hl])
      (by norm_num only) h₁ (by norm_num only)
  have hB :=
    shifted_monomial_cap (w := 0.0917) (B := 0.180388) hu (by norm_num only) hl (by norm_num only)
      h₂ (by norm_num only)
  linarith only [hA, hB]

/-- The radial factor of the unshifted conductor decreases throughout
the section 122 radius interval. -/
theorem quarter_radial_antitone_644 :
    AntitoneOn (fun r : ℝ ↦ (107 / 100 : ℝ) ^ 5 / 30 * r ^ (-(57 / 50) : ℝ) * (2 * Real.log r) ^ 5)
      (Set.Icc 316 322) := by
  let C : ℝ := (107 / 100) ^ 5 / 30
  let F := fun x : ℝ ↦ C * x ^ (-(57 / 50) : ℝ) * (2 * Real.log x) ^ 5
  have hlog :=
    Analysis.rationalLogIntervalCheck_sound
      (show Analysis.rationalLogIntervalCheck 99856 17 22 11 (115114844473 / 10000000000) = true by
        decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlog
  rw [show (99856 : ℝ) = (316 : ℝ) ^ 2 by norm_num only, Real.log_pow, Nat.cast_ofNat] at hlog
  have hd (x : ℝ) (hx : 0 < x) :
    HasDerivAt F
      (C * x ^ (-(57 / 50) : ℝ) * (2 * Real.log x) ^ 4 * (10 - (57 / 50) * (2 * Real.log x)) / x)
      x := by
    have h :=
      ((Real.hasDerivAt_rpow_const (p := -(57 / 50 : ℝ)) (Or.inl hx.ne')).mul
            (((Real.hasDerivAt_log hx.ne').const_mul 2).pow 5)).const_mul
        C
    have h' :
      HasDerivAt F
        (C *
          (-(57 / 50 : ℝ) * x ^ (-(57 / 50 : ℝ) - 1) * (2 * Real.log x) ^ 5 +
            x ^ (-(57 / 50) : ℝ) * (5 * (2 * Real.log x) ^ (5 - 1 : ℕ) * (2 * x⁻¹))))
        x := by
      simpa only [F, Pi.mul_apply, Pi.pow_apply, mul_assoc, Nat.cast_ofNat] using h
    apply h'.congr_deriv
    rw [Real.rpow_sub_one hx.ne']
    field_simp [hx.ne']
    ring
  have hpos (x : ℝ) (hx : x ∈ Set.Icc (316 : ℝ) 322) : 0 < x := by linarith only [hx.1]
  change AntitoneOn F (Set.Icc 316 322)
  apply
    antitoneOn_of_deriv_nonpos (convex_Icc _ _)
      (fun x hx ↦ (hd x (hpos x hx)).continuousAt.continuousWithinAt)
      (fun x hx ↦ (hd x (hpos x (interior_subset hx))).differentiableAt.differentiableWithinAt)
  intro x hx
  have hi : x ∈ Set.Icc (316 : ℝ) 322 := interior_subset hx
  have hp := hpos x hi
  have he := Real.log_le_log (by norm_num only : (0 : ℝ) < 316) hi.1
  rw [(hd x hp).deriv]
  exact
    div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg (mul_nonneg (by norm_num only [C]) (Real.rpow_nonneg hp.le _))
          (pow_nonneg (by linarith only [he, hlog.1]) _))
        (by linarith only [he, hlog.1]))
      hp.le

/-- The radial factor of the unshifted conductor decreases throughout the
section 122 interval. A logarithm and power certificate at 316 bound it. -/
theorem quarter_radial_conductor_cap_644 {r : ℝ} (hr : r ∈ Set.Icc 316 322) :
    (107 / 100 : ℝ) ^ 5 / 30 * r ^ (-(57 / 50) : ℝ) * (2 * Real.log r) ^ 5 ≤ 13.361 := by
  have hlog :=
    Analysis.rationalLogIntervalCheck_sound
      (show Analysis.rationalLogIntervalCheck 99856 17 22 11 (115114844473 / 10000000000) = true by
        decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlog
  rw [show (99856 : ℝ) = (316 : ℝ) ^ 2 by norm_num only, Real.log_pow, Nat.cast_ofNat] at hlog
  have hm :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 99856) (p := 57) (d :=
        100) (lo := 0) (hi := 141369826767 / 100000000000000) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat, neg_div] at hm
  rw [show (99856 : ℝ) = (316 : ℝ) ^ 2 by norm_num only, ←
    Real.rpow_natCast_mul (by norm_num only : (0 : ℝ) ≤ 316)] at hm
  norm_num only [Nat.cast_ofNat] at hm
  have hpow := pow_le_pow_left₀ (by linarith only [hlog.1]) hlog.2 5
  refine (quarter_radial_antitone_644 ⟨le_rfl, by norm_num only⟩ hr hr.1).trans ?_
  dsimp only
  rw [mul_assoc]
  exact
    (mul_le_mul_of_nonneg_left (mul_le_mul hm hpow (by positivity) (by norm_num only))
          (by norm_num only)).trans
      (by norm_num only)

private theorem radial_cost_box {r z m : ℝ} (hr : 0 ≤ r) (hl : 11 ≤ Real.log (r ^ 2))
    (hu : Real.log (r ^ 2) ≤ z) (hp : (r ^ 2) ^ (-(57 / 100) : ℝ) ≤ m) :
    (0.167715 : ℝ) * ((107 / 100) ^ 5 / 30 * r ^ (-(57 / 50) : ℝ) * (2 * Real.log r) ^ 5) ≤
      0.167715 * ((107 / 100) ^ 5 / 30 * (m * z ^ 5)) := by
  rw [Real.log_pow, Nat.cast_ofNat] at hl hu
  rw [← Real.rpow_natCast_mul hr] at hp
  norm_num only [Nat.cast_ofNat] at hp
  rw [mul_assoc ((107 / 100 : ℝ) ^ 5 / 30)]
  apply mul_le_mul_of_nonneg_left _ (by norm_num only)
  apply mul_le_mul_of_nonneg_left _ (by norm_num only)
  exact
    mul_le_mul hp (pow_le_pow_left₀ (by linarith only [hl]) hu 5)
      (pow_nonneg (by linarith only [hl]) _) ((Real.rpow_nonneg hr _).trans hp)

private theorem radial_cost_1 :
    (0.167715 : ℝ) * ((107 / 100) ^ 5 / 30 * (320) ^ (-(57 / 50) : ℝ) * (2 * Real.log (320)) ^ 5) ≤
      2.235 := by
  have hl :=
    Analysis.rationalLogIntervalCheck_sound (N := 102400) (j := 17) (n := 22) (lo := 11) (hi :=
      115366420117 / 10000000000) (by decide +kernel)
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 102400) (p := 57) (d :=
        100) (lo := 0) (hi := 139357075794 / 100000000000000) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat, neg_div] at hl hp
  rw [show (102400 : ℝ) = (320) ^ 2 by norm_num only] at hl hp
  exact (radial_cost_box (by norm_num only) hl.1 hl.2 hp).trans (by norm_num only)

private theorem radial_cost_2 :
    (0.167715 : ℝ) *
        ((107 / 100) ^ 5 / 30 * (1287 / 4) ^ (-(57 / 50) : ℝ) * (2 * Real.log (1287 / 4)) ^ 5) ≤
      2.22971 := by
  have hl :=
    Analysis.rationalLogIntervalCheck_sound (N := 1656369 / 16) (j := 17) (n := 22) (lo := 11)
      (hi := 115475497131 / 10000000000) (by decide +kernel)
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 1656369 / 16) (p := 57)
        (d := 100) (lo := 0) (hi := 138493326451 / 100000000000000) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat, neg_div] at hl hp
  rw [show (1656369 / 16 : ℝ) = (1287 / 4) ^ 2 by norm_num only] at hl hp
  exact (radial_cost_box (by norm_num only) hl.1 hl.2 hp).trans (by norm_num only)

/-- A row-wise bound for the cost of the shifted conductor combination.
The radial factor decreases, so each row uses only its left endpoint. -/
theorem quarter_radial_cost_rows_644 {r : ℝ} (hr : r ∈ Set.Icc 316 322) :
    (0.167715 : ℝ) * ((107 / 100) ^ 5 / 30 * r ^ (-(57 / 50) : ℝ) * (2 * Real.log r) ^ 5) ≤
      if r ≤ 320 then 2.242 else if r ≤ 1287 / 4 then 2.235 else 2.22971 := by
  by_cases h₁ : r ≤ 320
  · rw [ite_eq_left h₁]
    exact
      (mul_le_mul_of_nonneg_left (quarter_radial_conductor_cap_644 hr) (by norm_num only)).trans
        (by norm_num only)
  rw [ite_eq_right h₁]
  by_cases h₂ : r ≤ 1287 / 4
  · rw [ite_eq_left h₂]
    exact
      (mul_le_mul_of_nonneg_left
            (quarter_radial_antitone_644 ⟨by norm_num only, by norm_num only⟩ hr (le_of_not_ge h₁))
            (by norm_num only)).trans
        radial_cost_1
  rw [ite_eq_right h₂]
  exact
    (mul_le_mul_of_nonneg_left
          (quarter_radial_antitone_644 ⟨by norm_num only, by norm_num only⟩ hr (le_of_not_ge h₂))
          (by norm_num only)).trans
      radial_cost_2

/-- The signed sum of the seven cosine residue pairs contributes at
least 3.21112. Use rational Taylor bounds at the six positive half-frequencies. -/
theorem quarter_cosine_residue_lower_644 :
    (3.21112 : ℝ) ≤
      quarterCosineMix644
        (fun t ↦
          -3 * ((107 / 100 : ℝ) ^ 5 / ((107 / 100 : ℝ) ^ 2 - 1 / 4) ^ 3) *
            (Real.exp (-t / 2) + Real.exp (t / 2))) := by
  have box {x l u : ℝ} (hx : 0 ≤ x) (hs : x / 17 ≤ 1 / 2)
    (hl : l ≤ ∑ k ∈ Finset.range 16, x ^ k / (k.factorial : ℝ))
    (hu :
      (∑ k ∈ Finset.range 16, x ^ k / (k.factorial : ℝ)) + x ^ 16 / ((16 : ℕ).factorial : ℝ) * 2 ≤
        u) :
    l ≤ Real.exp x ∧ Real.exp x ≤ u :=
    ⟨hl.trans (Real.sum_le_exp_of_nonneg hx _),
      (Analysis.exp_le_taylor_add_two_next (n := 16) hx hs).trans hu⟩
  have h1 :=
    box (x := 2687 / 2000) (l := 3832433 / 1000000) (u := 3832434 / 1000000) (by norm_num only)
      (by norm_num only)
      (by
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
          Nat.cast_one, Nat.cast_zero])
      (by
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
          Nat.cast_one, Nat.cast_zero])
  have h2 :=
    box (x := 2707 / 2000) (l := 3870950 / 1000000) (u := 3870951 / 1000000) (by norm_num only)
      (by norm_num only)
      (by
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
          Nat.cast_one, Nat.cast_zero])
      (by
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
          Nat.cast_one, Nat.cast_zero])
  have h3 :=
    box (x := 3787 / 2000) (l := 6642577 / 1000000) (u := 6642578 / 1000000) (by norm_num only)
      (by norm_num only)
      (by
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
          Nat.cast_one, Nat.cast_zero])
      (by
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
          Nat.cast_one, Nat.cast_zero])
  have h4 :=
    box (x := 1 / 100) (l := 1010050 / 1000000) (u := 1010051 / 1000000) (by norm_num only)
      (by norm_num only)
      (by
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
          Nat.cast_one, Nat.cast_zero])
      (by
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
          Nat.cast_one, Nat.cast_zero])
  have h5 :=
    box (x := 11 / 20) (l := 1733253 / 1000000) (u := 1733254 / 1000000) (by norm_num only)
      (by norm_num only)
      (by
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
          Nat.cast_one, Nat.cast_zero])
      (by
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
          Nat.cast_one, Nat.cast_zero])
  have h6 :=
    box (x := 27 / 50) (l := 1716006 / 1000000) (u := 1716007 / 1000000) (by norm_num only)
      (by norm_num only)
      (by
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
          Nat.cast_one, Nat.cast_zero])
      (by
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
          Nat.cast_one, Nat.cast_zero])
  have add_inv {x l u : ℝ} (hl : 0 < l) (h : l ≤ Real.exp x ∧ Real.exp x ≤ u) :
    l + 1 / u ≤ Real.exp x + Real.exp (-x) ∧ Real.exp x + Real.exp (-x) ≤ u + 1 / l := by
    rw [Real.exp_neg, ← one_div]
    exact
      ⟨add_le_add h.1 (one_div_le_one_div_of_le (Real.exp_pos _) h.2),
        add_le_add h.2 (one_div_le_one_div_of_le hl h.1)⟩
  have k1 := add_inv (by norm_num only) h1
  have k2 := add_inv (by norm_num only) h2
  have k3 := add_inv (by norm_num only) h3
  have k4 := add_inv (by norm_num only) h4
  have k5 := add_inv (by norm_num only) h5
  have k6 := add_inv (by norm_num only) h6
  unfold quarterCosineMix644
  dsimp only
  norm_num only [neg_div, Real.exp_zero] at k1 k2 k3 k4 k5 k6 ⊢
  linarith only [k1.2, k2.1, k3.1, k4.2, k5.2, k6.1]

/-- Bound the reflected shift cap using the upper logarithmic endpoint
and the lower radial endpoint. The six moment constants are shared with
the unshifted reflected comparison. -/
private theorem shifted_reflection_cap {r h u : ℝ} (hr : 316 ≤ r) (hy : 2 * Real.log r ≤ 11.55)
    (hh : h ≤ 2 * Real.log r) (he : Real.exp ((107 / 100) * h) ≤ u) :
    quarterShiftCap644 r h ≤
      (107 / 100 : ℝ) ^ 5 / 30 * 0.000004474 * u *
        (∑ j ∈ Finset.range 6,
          (Nat.choose 5 j : ℝ) * (11.55 - h) ^ (5 - j) *
            (0.001420653 * Analysis.logPowerTailPoly (57 / 100) j 11.502876 +
              (4 / 5) * (0.000004515131 * (11.502876 : ℝ) ^ j) +
              (4 / 5 * (157 / 100)) *
                (0.000004515131 * Analysis.logPowerTailPoly (107 / 100) j 11.502876) +
              (157 / 100 / 24) *
                (0.0000003802 * Analysis.logPowerTailPoly (107 / 100) (j + 2) 13.816))) := by
  have hr₀ : 0 < r := by linarith only [hr]
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 99856) (p := 107) (d :=
        100) (lo := 0) (hi := 4474 / 1000000000) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat, neg_div] at hp
  rw [show (99856 : ℝ) = (316 : ℝ) ^ 2 by norm_num only, ←
    Real.rpow_natCast_mul (by norm_num only : (0 : ℝ) ≤ 316)] at hp
  norm_num only [Nat.cast_ofNat] at hp
  have hp' : r ^ (-(107 / 50) : ℝ) ≤ 0.000004474 := by
    norm_num only
    exact
      (Real.rpow_le_rpow_of_nonpos (by norm_num only : (0 : ℝ) < 316) hr
            (by norm_num only : (-(107 / 50) : ℝ) ≤ 0)).trans
        hp
  have hC (j : ℕ) : 0 ≤ reflectedCapFrom644 99000 j := by
    have hm {d t : ℝ} (hd : 0 < d) (ht : 1 ≤ t) (k : ℕ) : 0 ≤ eulerMomentValue570 d k t := by
      unfold eulerMomentValue570
      exact
        mul_nonneg (Real.rpow_nonneg (by linarith only [ht]) _)
          (Analysis.log_power_tail_poly_nonneg hd (Real.log_nonneg ht) k)
    have h₁ := hm (d := 57 / 100) (t := 99000) (by norm_num only) (by norm_num only) j
    have h₂ := hm (d := 107 / 100) (t := 99000) (by norm_num only) (by norm_num only) j
    have h₃ := hm (d := 107 / 100) (t := 1000000) (by norm_num only) (by norm_num only) (j + 2)
    have h₄ : 0 ≤ eulerMoment570 (57 / 100) j 99000 := by
      unfold eulerMoment570
      exact
        mul_nonneg (pow_nonneg (Real.log_nonneg (by norm_num only)) _)
          (Real.rpow_nonneg (by norm_num only) _)
    unfold reflectedCapFrom644
    exact
      add_nonneg
        (add_nonneg (add_nonneg h₁ (mul_nonneg (by positivity) h₄))
          (mul_nonneg (by norm_num only) h₂))
        (mul_nonneg (by norm_num only) h₃)
  unfold quarterShiftCap644
  have hf (S : ℝ) :
    ((107 / 100 : ℝ) ^ 5 / 120 * r ^ (-(107 / 50) : ℝ) * Real.exp ((107 / 100) * h)) * (4 * S) =
      ((107 / 100 : ℝ) ^ 5 / 30 * r ^ (-(107 / 50) : ℝ) * Real.exp ((107 / 100) * h)) * S := by
    ring
  rw [hf]
  have hu := (Real.exp_pos _).le.trans he
  have hz : 0 ≤ 2 * Real.log r - h := sub_nonneg.mpr hh
  have hz' : 0 ≤ 11.55 - h := hz.trans (sub_le_sub_right hy h)
  gcongr
  all_goals
    first
    | exact reflected_shift_cap_upper_644 _
    | exact hC _
    | exact Finset.sum_nonneg (fun j _ ↦ mul_nonneg (by positivity) (hC j))

/-- The sum of both residual reflected shift allowances is at most 0.00126
for the logarithmic arguments used in section 122. -/
private theorem reflected_shift_loss_cap {r : ℝ} (hr : 316 ≤ r) (hl : 11 / 10 ≤ 2 * Real.log r)
    (hu : 2 * Real.log r ≤ 11.55) :
    (1.508 - 1.54 * Real.exp (-((107 / 100) * (1 / 50)))) * quarterShiftCap644 r (1 / 50) +
        0.0917 * quarterShiftCap644 r (11 / 10) ≤
      0.00126 := by
  have he :=
    Analysis.exp_le_taylor_add_two_next (x := (1177 / 1000 : ℝ)) (n := 12) (by norm_num only)
      (by norm_num only)
  have he' :=
    Analysis.exp_le_taylor_add_two_next (x := (107 / 5000 : ℝ)) (n := 12) (by norm_num only)
      (by norm_num only)
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
    Nat.cast_one, Nat.cast_zero] at he he'
  have h₁ : Real.exp ((107 / 100) * (1 / 50)) ≤ 1.022 := by
    rw [show (107 / 100 : ℝ) * (1 / 50) = 107 / 5000 by norm_num only]
    linarith only [he']
  have h₂ : Real.exp ((107 / 100) * (11 / 10)) ≤ 3.245 := by
    rw [show (107 / 100 : ℝ) * (11 / 10) = 1177 / 1000 by norm_num only]
    linarith only [he]
  have hν : 1.508 - 1.54 * Real.exp (-((107 / 100) * (1 / 50))) ≤ (0.002 : ℝ) := by
    rw [Real.exp_neg, ← div_eq_mul_inv]
    have h :=
      (le_div_iff₀ (Real.exp_pos ((107 / 100) * (1 / 50)))).mpr
        (show (1.506 : ℝ) * Real.exp ((107 / 100) * (1 / 50)) ≤ 1.54 by linarith only [h₁])
    linarith only [h]
  have hA := shifted_reflection_cap hr hu (by linarith only [hl]) h₁
  have hB := shifted_reflection_cap hr hu hl h₂
  have hA' : quarterShiftCap644 r (1 / 50) ≤ 0.00531 :=
    hA.trans
      (by
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Analysis.logPowerTailPoly,
          Nat.choose, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.reduceAdd, Nat.reduceSub])
  have hB' : quarterShiftCap644 r (11 / 10) ≤ 0.01356 :=
    hB.trans
      (by
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Analysis.logPowerTailPoly,
          Nat.choose, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.reduceAdd, Nat.reduceSub])
  have hv :=
    (mul_le_mul_of_nonneg_left hA' quarter_shift_loss_coeff_644).trans
      (mul_le_mul_of_nonneg_right hν (by norm_num only))
  linarith only [hv, hB']

/-- The positive half-point residues cancel between the cosine and shifted
main comparisons. The lower bound includes the certified negative half-point
contribution, shifted conductor profiles and explicit error allowances. -/
theorem quarter_shift_cosine_lower_644 {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ s}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hRH : RiemannHypothesis) {r : ℝ}
    (hr : r ∈ Set.Icc 316 322) (hlog : Real.log p + Real.log q + Real.log s = 4 * r)
    (hpa : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → a l = 1)
    (hpb : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → b l = 1)
    (hpc : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → c l = 1)
    (ht : ∀ n : ℕ, (a n).re + (b n).re + (c n).re ∈ Set.Icc (-1) 3)
    (hp :
      ∀ n ∈ Finset.Ioc 0 99000,
        ArithmeticFunction.vonMangoldt n ≠ 0 → (a n).re + (b n).re + (c n).re = 3) :
    let X := fun h : ℝ ↦ r ^ 2 * Real.exp (-(2687 / 1000 + h))
    let mix := fun F : ℝ → ℝ ↦ 1.54 * F 0 - 1.508 * F (1 / 50) - 0.0917 * F (11 / 10)
    let T := fun h : ℝ ↦
      (contourRemainder644 a (X h)).re + (contourRemainder644 b (X h)).re +
          (contourRemainder644 c (X h)).re -
        3 * (∑' n : ℕ, quarterKernel644.summand (1 : DirichletCharacter ℂ 1) (X h) n).re
    3.21112 + 0.00063602 * r + 0.05413 -
          (if r ≤ 320 then 2.242 else if r ≤ 1287 / 4 then 2.235 else 2.22971) -
          0.00001502 -
          0.00126 +
        (if r ≤ 320 then -0.456620
        else if r ≤ 1287 / 4 then -0.452096 else if r ≤ 1609 / 5 then -0.450144 else -0.450088) ≤
      mix T +
        quarterCosineMix644
          (fun t ↦
            quarterCosineContour644 a t + quarterCosineContour644 b t +
              quarterCosineContour644 c t) := by
  intro X mix T
  let P := fun h : ℝ ↦ Real.exp ((107 / 100 : ℝ) * h) * (2 * Real.log r - h) ^ 5
  have hS := quarter_shifted_forward_mix_644 ha hb hc hRH hr.1 ht hp
  have hC :=
    quarter_cosine_rows_without_xi_644 ha hb hc hRH hr.1 hlog hpa hpb hpc (fun n ↦ (ht n).1)
  dsimp only at hS hC
  rw [hlog] at hS
  rw [quarter_shift_conductor_644 hr.1 (h := 0) (by norm_num only),
    quarter_shift_conductor_644 hr.1 (h := 1 / 50) (by norm_num only),
    quarter_shift_conductor_644 hr.1 (h := 11 / 10) le_rfl] at hS
  simp only [Complex.add_re] at hS
  have hr₀ : 0 < r := by linarith only [hr.1]
  have hl : 1 ≤ Real.log r :=
    (Real.le_log_iff_exp_le hr₀).mpr (by linarith only [Real.exp_one_lt_three, hr.1])
  have hu :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 322 9 27 (5774 / 1000) (5775 / 1000) = true by
          decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hu
  have hlogU := (Real.log_le_log hr₀ hr.2).trans hu
  have hpoly :=
    quarter_shift_poly_lower_644 (y := 2 * Real.log r) (by linarith only [hl])
      (by linarith only [hlogU])
  have hmix : -0.167715 * (2 * Real.log r) ^ 5 ≤ mix P := by
    simpa only [mix, P, sub_zero, mul_zero, Real.exp_zero, one_mul] using hpoly
  have hcond :=
    mul_le_mul_of_nonneg_left hmix
      (show 0 ≤ (107 / 100 : ℝ) ^ 5 / 30 * r ^ (-(57 / 50) : ℝ) by positivity)
  rw [quarter_shift_conductor_factor_644 hr₀ 0, quarter_shift_conductor_factor_644 hr₀ (1 / 50),
    quarter_shift_conductor_factor_644 hr₀ (11 / 10)] at hS
  rw [quarter_shifted_neg_pole_644 hr₀ 0, quarter_shifted_neg_pole_644 hr₀ (1 / 50),
    quarter_shifted_neg_pole_644 hr₀ (11 / 10)] at hS
  dsimp only [mix, P] at hcond
  dsimp only [mix, X, T]
  simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at hS hC ⊢
  have hP := quarter_neg_pole_mix_lower_644 hr
  have h₀ : Real.exp ((0 : ℝ) / 2) = 1 := by norm_num only [zero_div, Real.exp_zero]
  have h₁ : (1 / 50 : ℝ) / 2 = 1 / 100 := by norm_num only
  have h₂ : (11 / 10 : ℝ) / 2 = 11 / 20 := by norm_num only
  rw [h₀, h₁, h₂] at hS
  have hrad := quarter_radial_cost_rows_644 hr
  have hLoss := reflected_shift_loss_cap hr.1 (by linarith only [hl]) (by linarith only [hlogU])
  linarith only [hS, hC, hP, hcond, hrad, hLoss, quarter_cosine_residue_lower_644]

/-- Under GRH, agreement of three even primitive characters on the cutoff
primes bounds their main forward sum using the common shifted comparison. -/
theorem quarter_three_forward_upper_644 {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ s}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hp : 2 ≤ p) (hq : 2 ≤ q) (hs : 2 ≤ s)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {r : ℝ} (hr : r ∈ Set.Icc 316 322)
    (hlog : Real.log p + Real.log q + Real.log s = 4 * r)
    (hpa : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → a l = 1)
    (hpb : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → b l = 1)
    (hpc : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → c l = 1)
    (ht : ∀ n : ℕ, (a n).re + (b n).re + (c n).re ∈ Set.Icc (-1) 3)
    (hprefix :
      ∀ n ∈ Finset.Ioc 0 99000,
        ArithmeticFunction.vonMangoldt n ≠ 0 → (a n).re + (b n).re + (c n).re = 3) :
    let X := r ^ 2
    (∑' n, quarterKernel644.summand a X n).re + (∑' n, quarterKernel644.summand b X n).re +
            (∑' n, quarterKernel644.summand c X n).re +
            3.26397498 -
          (if r ≤ 320 then 2.242 else if r ≤ 1287 / 4 then 2.235 else 2.22971) +
        0.00063602 * r +
        (if r ≤ 320 then -0.456620
        else if r ≤ 1287 / 4 then -0.452096 else if r ≤ 1609 / 5 then -0.450144 else -0.450088) ≤
      quarterMass644 a + quarterMass644 b + quarterMass644 c + (contourRemainder644 a X).re +
        (contourRemainder644 b X).re +
        (contourRemainder644 c X).re := by
  intro X
  have hX : 1 ≤ X := one_le_pow₀ (by linarith only [hr.1] : 1 ≤ r)
  have hcut : 1 ≤ X * Real.exp (-(3787 / 1000)) := by
    rw [show (3787 / 1000 : ℝ) = 2687 / 1000 + 11 / 10 by norm_num only]
    exact quarter_shift_scale_ge_one_644 hr.1 le_rfl
  have h₁ := quarter_three_contour_upper_644 hp hG ha.1 ha.2.1 hX hcut hpa
  have h₂ := quarter_three_contour_upper_644 hq hG hb.1 hb.2.1 hX hcut hpb
  have h₃ := quarter_three_contour_upper_644 hs hG hc.1 hc.2.1 hX hcut hpc
  have h := quarter_shift_cosine_lower_644 ha hb hc hG.riemann hr hlog hpa hpb hpc ht hprefix
  dsimp only [quarterCosineMix644, X] at h h₁ h₂ h₃ ⊢
  rw [← quarter_mass_cosine_644 hp hG ha.1 ha.2.1, ← quarter_mass_cosine_644 hq hG hb.1 hb.2.1, ←
    quarter_mass_cosine_644 hs hG hc.1 hc.2.1] at h
  simp only [add_zero, show (2687 / 1000 : ℝ) + 1 / 50 = 2707 / 1000 by norm_num only,
    show (2687 / 1000 : ℝ) + 11 / 10 = 3787 / 1000 by norm_num only] at h
  linarith only [h, h₁, h₂, h₃]

/-- With the section 122 kernel, any finite set of powers above the
cutoff whose bases pass supplies a fourfold credit in the main forward sum. -/
theorem quarter_power_credit_644 {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ s) {X : ℝ}
    (hX : 0 < X) (T : Finset ℕ) (hT : ∀ m ∈ T, X < m ∧ ∃ l k : ℕ, l.Prime ∧ (l : ℝ) ≤ X ∧ m = l ^ k)
    (ht : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re)
    (ha : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → a l = 1) (hb : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → b l = 1)
    (hc : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → c l = 1) :
    let f := fun n : ℕ ↦ (quarterKernel644.summand (1 : DirichletCharacter ℂ 1) X n).re
    4 * (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, f n) + 4 * (∑ n ∈ T, f n) - (∑' n : ℕ, f n) ≤
      (∑' n, quarterKernel644.summand a X n).re + (∑' n, quarterKernel644.summand b X n).re +
        (∑' n, quarterKernel644.summand c X n).re := by
  intro f
  have hs := quarterKernel644.summable_summand (1 : DirichletCharacter ℂ 1) hX
  rw [← Complex.re_tsum hs]
  exact kernel_recover_fixed_powers quarterKernel644 a b c hX T hT ht ha hb hc

end PseudoPrime.PrimeTestBounds.MillerRabin
