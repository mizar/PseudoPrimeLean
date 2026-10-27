/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
module

public import Mathlib.Analysis.Complex.JensenFormula
public import Mathlib.Analysis.Complex.BorelCaratheodory
public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.Analysis.Meromorphic.LogDeriv
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.PSeries
public import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.NumberTheory.LSeries.Nonvanishing
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.ConductorPrimeFactors
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaFactorVerticalGrowth
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.CenteredHadamard
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.HadamardLimit
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.ShiftedPoissonEulerBounds
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveFunctionalEquation
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveZeroTransfer
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.ZeroCounting
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.PowerSumInterpolation

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.LocalZeroCounting

/-! # Completed genus sums and remote tails -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity

/-!
## Summability of the inverse-square genus weights
-/

/--
Inputs: an open set, a positive derivative order, an integer coefficient, and two complex points.
Claim: the derivative of a genus-one resolvent term is the corresponding reciprocal power term.
Proof: remove the constant correction, differentiate `1 / (z - ρ)` by translation, and use the
iterated derivative formula for reciprocal powers.
Role: identifies the terms used when differentiating the completed genus expansion.
-/
theorem iteratedDerivWithin_completed_genus_term {U : Set ℂ} (hU : IsOpen U) {n : ℕ} (hn : 0 < n)
    (D : ℤ) (ρ z : ℂ) (hz : z ∈ U) :
    iteratedDerivWithin n (fun w : ℂ => (D : ℂ) * (1 / (w - ρ) + 1 / ρ)) U z =
      (D : ℂ) * ((-1 : ℂ) ^ n * (n.factorial : ℂ) * (z - ρ) ^ (-1 - (n : ℕ) : ℤ)) := by
  have hsplit :
    (fun w : ℂ => (D : ℂ) * (1 / (w - ρ) + 1 / ρ)) = fun w =>
      (D : ℂ) / ρ + (D : ℂ) * (1 / (w - ρ)) := by
    funext w
    ring
  rw [hsplit, iteratedDerivWithin_const_add hn, iteratedDerivWithin_const_mul_field]
  rw [iteratedDerivWithin_of_isOpen hU hz]
  have hrecip :
    iteratedDeriv n (fun w : ℂ => 1 / (w - ρ)) z =
      (-1 : ℂ) ^ n * (n.factorial : ℂ) * (z - ρ) ^ (-1 - (n : ℕ) : ℤ) := by
    rw [← iteratedDerivWithin_univ, iteratedDerivWithin_comp_sub_const]
    open scoped
      Pointwise in
      have hset : -ρ +ᵥ (Set.univ : Set ℂ) = Set.univ := by
        ext w
        simp only [Set.mem_vadd_set, Set.mem_univ]
        constructor
        · rintro ⟨y, hy, h⟩
          trivial
        · intro _
          refine ⟨ρ +ᵥ w, trivial, ?_⟩
          rw [vadd_vadd, neg_add_cancel, zero_vadd]
      rw [hset]
      change iteratedDerivWithin n (fun y : ℂ => 1 / y) Set.univ (z - ρ) = _
      rw [iteratedDerivWithin_one_div n isOpen_univ]
      simp only [Set.mem_univ]
  rw [hrecip]

/--
Inputs: an open set, a positive derivative order, a nonnegative integer multiplicity, and two
complex points.
Claim: the norm of the differentiated genus term is the multiplicity times the factorial and the
corresponding reciprocal-distance power.
Proof: use the explicit derivative formula and rewrite the norm of the negative integer power.
Role: provides a real-valued majorant for locally uniform summability of differentiated terms.
-/
theorem norm_iteratedDerivWithin_completed_genus_term {U : Set ℂ} (hU : IsOpen U) {n : ℕ}
    (hn : 0 < n) (D : ℤ) (hD : 0 ≤ D) (ρ z : ℂ) (hz : z ∈ U) :
    ‖iteratedDerivWithin n (fun w : ℂ => (D : ℂ) * (1 / (w - ρ) + 1 / ρ)) U z‖ =
      (D : ℝ) * (n.factorial : ℝ) * ‖(z - ρ)⁻¹‖ ^ (n + 1) := by
  rw [iteratedDerivWithin_completed_genus_term hU hn D ρ z hz]
  simp only [norm_mul, norm_pow, norm_neg, norm_one, norm_natCast]
  rw [show (-1 - (n : ℕ) : ℤ) = -(n + 1 : ℕ) by omega]
  rw [zpow_neg, norm_inv, zpow_natCast, norm_pow, norm_inv, ← inv_pow]
  rw [Complex.norm_intCast]
  simp only [one_pow, one_mul]
  have hDreal : 0 ≤ (D : ℝ) := by exact_mod_cast hD
  rw [abs_of_nonneg hDreal]
  ring_nf

/--
Inputs: an order at least one and positive lower bounds for two positive distances, together with
an additive bound between those distances.
Claim: a reciprocal power of the first distance is bounded by the inverse-square weight of the
second distance times a constant depending only on the bounds and the order.
Proof: compare the distances by division, raise the comparison to the required power, and split off
two powers controlled by the second distance.
Role: supplies the real inequality needed to majorize differentiated genus terms on compact sets.
-/
theorem inv_pow_le_inv_sq_majorant {n : ℕ} (hn : 1 ≤ n) {a b δ ε R : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    (hR : 0 ≤ R) (hδa : δ ≤ a) (hεb : ε ≤ b) (hab : b ≤ a + R) :
    a⁻¹ ^ (n + 1) ≤ (1 + R / δ) ^ (n + 1) * ε⁻¹ ^ (n - 1) * b⁻¹ ^ 2 := by
  have ha : 0 < a := lt_of_lt_of_le hδ hδa
  have hb : 0 < b := lt_of_lt_of_le hε hεb
  have hratio : b / a ≤ 1 + R / δ := by
    apply (div_le_iff₀ ha).2
    calc
      b ≤ a + R := hab
      _ = a + δ * (R / δ) := by rw [mul_div_cancel₀ R (ne_of_gt hδ)]
      _ ≤ a + a * (R / δ) := by
        calc
          a + δ * (R / δ) = δ * (R / δ) + a := by ring
          _ ≤ a * (R / δ) + a :=
            add_le_add_left (mul_le_mul_of_nonneg_right hδa (div_nonneg hR hδ.le)) a
          _ = a + a * (R / δ) := by ring
      _ = (1 + R / δ) * a := by ring
  have hbase' : 1 / a ≤ (1 + R / δ) / b := by
    apply (div_le_div_iff₀ ha hb).2
    have hba := (div_le_iff₀ ha).mp hratio
    simpa only [one_mul] using hba
  have hbase : a⁻¹ ≤ (1 + R / δ) * b⁻¹ := by
    simpa only [one_mul, one_div, div_eq_mul_inv] using hbase'
  have hpow : a⁻¹ ^ (n + 1) ≤ ((1 + R / δ) * b⁻¹) ^ (n + 1) :=
    pow_le_pow_left₀ (inv_nonneg.mpr ha.le) hbase (n + 1)
  rw [mul_pow] at hpow
  have hexp : n + 1 = 2 + (n - 1) := by omega
  have hsplit : b⁻¹ ^ (n + 1) = b⁻¹ ^ 2 * b⁻¹ ^ (n - 1) := by rw [← pow_add, hexp]
  have hbinv : b⁻¹ ≤ ε⁻¹ := by simpa only [one_div] using one_div_le_one_div_of_le hε hεb
  have hbinvPow : b⁻¹ ^ (n - 1) ≤ ε⁻¹ ^ (n - 1) :=
    pow_le_pow_left₀ (inv_nonneg.mpr hb.le) hbinv (n - 1)
  have hC : 0 ≤ 1 + R / δ := add_nonneg (by norm_num only) (div_nonneg hR hδ.le)
  calc
    a⁻¹ ^ (n + 1) ≤ (1 + R / δ) ^ (n + 1) * (b⁻¹ ^ 2 * b⁻¹ ^ (n - 1)) := by
      rw [← hsplit]
      exact hpow
    _ ≤ (1 + R / δ) ^ (n + 1) * (b⁻¹ ^ 2 * ε⁻¹ ^ (n - 1)) := by
      apply mul_le_mul_of_nonneg_left
      · exact mul_le_mul_of_nonneg_left hbinvPow (sq_nonneg _)
      · exact pow_nonneg hC _
    _ = _ := by ring

/--
Inputs: a primitive nonprincipal completed Dirichlet `L`-function and a point to the right of
the line `Re s = 1`.
Claim: the zero multiplicities weighted by squared inverse distances to `s` have finite sum.
Proof: dominate each inverse-square term by the nonnegative real part of the completed genus
kernel, using `Re ρ < 1` for every completed zero, and use summability of the genus expansion.
Role: supplies the square-summability hypothesis for infinite remote-tail power-sum estimates.
-/
theorem summable_completed_genus_inverse_square {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (hp : χ.IsPrimitive) (hinv : χ⁻¹ ≠ 1) {s : ℂ}
    (hs : 1 < s.re) :
    Summable
      (fun ρ : ℂ =>
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) * ‖(s - ρ)⁻¹‖ ^ 2) := by
  let F : ℂ → ℂ := χ.completedLFunction
  let D : ℂ → ℤ := MeromorphicOn.divisor F Set.univ
  let cterm : ℂ → ℂ := fun ρ => (D ρ : ℂ) * (1 / (s - ρ) + 1 / ρ)
  let rterm : ℂ → ℝ := fun ρ => (cterm ρ).re
  have hseries : Summable cterm := by
    simpa only [cterm, D, F] using summable_completed_genus_terms_right hq hp hχ hinv hs
  have hrseries : Summable rterm := by
    apply Summable.of_norm_bounded hseries.norm
    intro ρ
    exact Complex.abs_re_le_norm (cterm ρ)
  have hF : AnalyticOnNhd ℂ F Set.univ := by
    have hdiff := DirichletCharacter.differentiable_completedLFunction hχ
    intro u hu
    exact hdiff.analyticAt u
  have hDnonneg (ρ : ℂ) : 0 ≤ (D ρ : ℝ) := by
    exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hF ρ
  have hcast (ρ : ℂ) : (D ρ : ℂ) = ((D ρ : ℝ) : ℂ) := by
    push_cast
    ring
  have hterm (ρ : ℂ) : rterm ρ = (D ρ : ℝ) * ((1 / (s - ρ)).re + (1 / ρ).re) := by
    dsimp [rterm, cterm]
    rw [hcast, Complex.re_ofReal_mul, Complex.add_re]
  have hnonneg (ρ : ℂ) : 0 ≤ rterm ρ := by
    by_cases hD : D ρ = 0
    · simp only [rterm, cterm, D, hD, Int.cast_zero, zero_mul, Complex.zero_re, le_refl]
    · have hz := dirichletCompletedLFunction_zero_of_divisor_univ_ne_zero hχ hD
      have hrepos := completedLFunction_zero_re_pos hp hinv hz
      have hrelt := completedLFunction_zero_re_lt_one hχ hz
      rw [hterm]
      apply mul_nonneg (hDnonneg ρ)
      apply add_nonneg
      · rw [one_div, Complex.inv_re]
        apply div_nonneg
        · rw [Complex.sub_re]
          linarith only [hs, hrelt]
        · exact Complex.normSq_nonneg _
      · rw [one_div, Complex.inv_re]
        exact div_nonneg hrepos.le (Complex.normSq_nonneg _)
  have hshift : 0 < s.re - 1 := by linarith only [hs]
  have hpoint (ρ : ℂ) : (D ρ : ℝ) * ‖(s - ρ)⁻¹‖ ^ 2 ≤ rterm ρ / (s.re - 1) := by
    by_cases hD : D ρ = 0
    · rw [hterm, hD]
      simp only [Int.cast_zero, zero_mul, zero_div, le_refl]
    · have hz := dirichletCompletedLFunction_zero_of_divisor_univ_ne_zero hχ hD
      have hrelt := completedLFunction_zero_re_lt_one hχ hz
      have hreal : s.re - 1 ≤ (s - ρ).re := by
        rw [Complex.sub_re]
        linarith only [hrelt]
      have hdiff : 0 < (s - ρ).re := lt_of_lt_of_le hshift hreal
      have hneq : s - ρ ≠ 0 := by
        intro heq
        have hre : (s - ρ).re = 0 := by
          rw [heq]; exact Complex.zero_re
        linarith only [hdiff, hre]
      have hnormsq : 0 < Complex.normSq (s - ρ) := by
        rw [Complex.normSq_eq_norm_sq]
        exact sq_pos_of_pos (norm_pos_iff.mpr hneq)
      have hinvsq : ‖(s - ρ)⁻¹‖ ^ 2 = (Complex.normSq (s - ρ))⁻¹ := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_inv]
      have hkernel : ‖(s - ρ)⁻¹‖ ^ 2 ≤ ((1 / (s - ρ)).re) / (s.re - 1) := by
        rw [hinvsq]
        conv_rhs => rw [one_div, Complex.inv_re]
        have hscaled : (s.re - 1) / Complex.normSq (s - ρ) ≤ (s - ρ).re / Complex.normSq (s - ρ) :=
          div_le_div_of_nonneg_right hreal hnormsq.le
        calc
          (Complex.normSq (s - ρ))⁻¹ = ((s.re - 1) / Complex.normSq (s - ρ)) / (s.re - 1) := by
            field_simp [ne_of_gt hshift, ne_of_gt hnormsq]
          _ ≤ ((s - ρ).re / Complex.normSq (s - ρ)) / (s.re - 1) :=
            div_le_div_of_nonneg_right hscaled hshift.le
      have hkernelNonneg : 0 ≤ (1 / (s - ρ)).re := by
        rw [one_div, Complex.inv_re]
        exact div_nonneg (le_of_lt hdiff) (Complex.normSq_nonneg _)
      have hDpos := hDnonneg ρ
      calc
        (D ρ : ℝ) * ‖(s - ρ)⁻¹‖ ^ 2 ≤ ((D ρ : ℝ) * ((1 / (s - ρ)).re)) / (s.re - 1) := by
          calc
            (D ρ : ℝ) * ‖(s - ρ)⁻¹‖ ^ 2 ≤ (D ρ : ℝ) * (((1 / (s - ρ)).re) / (s.re - 1)) :=
              mul_le_mul_of_nonneg_left hkernel hDpos
            _ = _ := by rw [mul_div_assoc]
        _ ≤ ((D ρ : ℝ) * ((1 / (s - ρ)).re + (1 / ρ).re)) / (s.re - 1) := by
          apply div_le_div_of_nonneg_right
          · apply mul_le_mul_of_nonneg_left
            · exact
                le_add_of_nonneg_right
                  (by
                    rw [one_div, Complex.inv_re]
                    exact
                      div_nonneg (completedLFunction_zero_re_pos hp hinv hz).le
                        (Complex.normSq_nonneg _))
            · exact hDpos
          · exact hshift.le
        _ = rterm ρ / (s.re - 1) := by rw [hterm]
  have hscaled : Summable (fun ρ : ℂ => (s.re - 1)⁻¹ * rterm ρ) := hrseries.mul_left _
  apply Summable.of_norm_bounded hscaled
  intro ρ
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hDnonneg ρ) (sq_nonneg _))]
  have h := hpoint ρ
  rw [div_eq_mul_inv] at h
  simpa only [mul_comm] using h

/--
Inputs: a primitive nonprincipal completed Dirichlet `L`-function, a point to the right of
`Re s = 1`, and a positive derivative order.
Claim: the differentiated genus-one resolvent terms are summable locally uniformly on that
half-plane.
Proof: on each compact set, use its positive distance from the boundary and its bounded diameter
to dominate every derivative term by a constant multiple of the inverse-square mass at the fixed
point; then apply the locally bounded summability criterion.
Role: supplies the convergence hypothesis for exchanging higher derivatives with the completed
genus sum.
-/
theorem summableLocallyUniformlyOn_completed_genus_term_iteratedDerivWithin {q : ℕ} [NeZero q]
    (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (hp : χ.IsPrimitive) (hinv : χ⁻¹ ≠ 1)
    {s₀ : ℂ} (hs₀ : 1 < s₀.re) (n : ℕ) (hn : 0 < n) :
    SummableLocallyUniformlyOn
      (fun ρ : ℂ =>
        iteratedDerivWithin n
          (fun s : ℂ =>
            (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℂ) * (1 / (s - ρ) + 1 / ρ))
          {s : ℂ | 1 < s.re})
      {s : ℂ | 1 < s.re} := by
  let V : Set ℂ := {s | 1 < s.re}
  let D : ℂ → ℤ := MeromorphicOn.divisor χ.completedLFunction Set.univ
  change
    SummableLocallyUniformlyOn
      (fun ρ : ℂ => iteratedDerivWithin n (fun s : ℂ => (D ρ : ℂ) * (1 / (s - ρ) + 1 / ρ)) V) V
  have hV : IsOpen V := isOpen_lt continuous_const Complex.continuous_re
  apply SummableLocallyUniformlyOn_of_locally_bounded hV
  intro K hK hKcompact
  by_cases hKne : K.Nonempty
  · obtain ⟨z₀, hz₀, hmin⟩ := hKcompact.exists_isMinOn hKne Complex.continuous_re.continuousOn
    let δ : ℝ := z₀.re - 1
    have hδ : 0 < δ := sub_pos.mpr (hK hz₀)
    have hδz (z : ℂ) (hz : z ∈ K) : δ ≤ z.re - 1 := by exact sub_le_sub_right (hmin hz) 1
    obtain ⟨R, hR⟩ := hKcompact.isBounded.subset_closedBall s₀
    let R₀ : ℝ := max R 0
    have hR₀ : 0 ≤ R₀ := le_max_right R 0
    have hRsub : K ⊆ Metric.closedBall s₀ R₀ := by
      exact Set.Subset.trans hR (Metric.closedBall_subset_closedBall (le_max_left R 0))
    let ε : ℝ := s₀.re - 1
    have hε : 0 < ε := sub_pos.mpr hs₀
    let C : ℝ := (n.factorial : ℝ) * (1 + R₀ / δ) ^ (n + 1) * ε⁻¹ ^ (n - 1)
    have hC : 0 ≤ C := by
      dsimp [C]
      have hbase : 0 ≤ 1 + R₀ / δ := add_nonneg (by norm_num only) (div_nonneg hR₀ hδ.le)
      apply mul_nonneg
      · apply mul_nonneg
        · exact Nat.cast_nonneg _
        · exact pow_nonneg hbase _
      · exact pow_nonneg (inv_nonneg.mpr hε.le) _
    let u : ℂ → ℝ := fun ρ => C * ((D ρ : ℝ) * ‖(s₀ - ρ)⁻¹‖ ^ 2)
    have hu : Summable u := by
      have hsum := summable_completed_genus_inverse_square hq hχ hp hinv hs₀
      have hscale : Summable (fun ρ : ℂ => C * ((D ρ : ℝ) * ‖(s₀ - ρ)⁻¹‖ ^ 2)) := hsum.mul_left C
      simpa only [u, D] using hscale
    refine ⟨u, hu, ?_⟩
    intro ρ z hz
    have hF : AnalyticOnNhd ℂ χ.completedLFunction Set.univ := by
      have hdiff := DirichletCharacter.differentiable_completedLFunction hχ
      intro w hw
      exact hdiff.analyticAt w
    have hDint : 0 ≤ D ρ := by exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hF ρ
    have hDreal : 0 ≤ (D ρ : ℝ) := by exact_mod_cast hDint
    by_cases hDzero : D ρ = 0
    · change
        ‖iteratedDerivWithin n (fun s : ℂ => (D ρ : ℂ) * (1 / (s - ρ) + 1 / ρ)) V z‖ ≤
          C * ((D ρ : ℝ) * ‖(s₀ - ρ)⁻¹‖ ^ 2)
      rw [norm_iteratedDerivWithin_completed_genus_term hV hn (D ρ) hDint ρ z (hK hz)]
      simp only [hDzero, Int.cast_zero, zero_mul, mul_zero]
      exact le_rfl
    · have hzero := dirichletCompletedLFunction_zero_of_divisor_univ_ne_zero hχ hDzero
      have hρlt := completedLFunction_zero_re_lt_one hχ hzero
      have hgeom : δ ≤ ‖z - ρ‖ ∧ ε ≤ ‖s₀ - ρ‖ ∧ ‖s₀ - ρ‖ ≤ ‖z - ρ‖ + R₀ := by
        have hrealz : δ ≤ (z - ρ).re := by
          rw [Complex.sub_re]
          linarith only [hδz z hz, hρlt]
        have hnormz : δ ≤ ‖z - ρ‖ := by
          calc
            δ ≤ |(z - ρ).re| := le_trans hrealz (le_abs_self _)
            _ ≤ ‖z - ρ‖ := Complex.abs_re_le_norm _
        have hreals₀ : ε ≤ (s₀ - ρ).re := by
          rw [Complex.sub_re]
          linarith only [hs₀, hρlt]
        have hnorms₀ : ε ≤ ‖s₀ - ρ‖ := by
          calc
            ε ≤ |(s₀ - ρ).re| := le_trans hreals₀ (le_abs_self _)
            _ ≤ ‖s₀ - ρ‖ := Complex.abs_re_le_norm _
        have hdist : ‖s₀ - z‖ ≤ R₀ := by
          simpa only [dist_eq_norm, norm_sub_rev] using Metric.mem_closedBall.mp (hRsub hz)
        have htri : ‖s₀ - ρ‖ ≤ ‖z - ρ‖ + R₀ := by
          calc
            ‖s₀ - ρ‖ = ‖(s₀ - z) + (z - ρ)‖ := by
              congr 1; ring
            _ ≤ ‖s₀ - z‖ + ‖z - ρ‖ := norm_add_le _ _
            _ ≤ R₀ + ‖z - ρ‖ := by
              calc
                ‖s₀ - z‖ + ‖z - ρ‖ = ‖z - ρ‖ + ‖s₀ - z‖ := by ring
                _ ≤ ‖z - ρ‖ + R₀ := add_le_add le_rfl hdist
                _ = R₀ + ‖z - ρ‖ := by ring
            _ = ‖z - ρ‖ + R₀ := by ring
        exact ⟨hnormz, hnorms₀, htri⟩
      have hpower := inv_pow_le_inv_sq_majorant hn hδ hε hR₀ hgeom.1 hgeom.2.1 hgeom.2.2
      change
        ‖iteratedDerivWithin n (fun s : ℂ => (D ρ : ℂ) * (1 / (s - ρ) + 1 / ρ)) V z‖ ≤
          C * ((D ρ : ℝ) * ‖(s₀ - ρ)⁻¹‖ ^ 2)
      rw [norm_iteratedDerivWithin_completed_genus_term hV hn (D ρ) hDint ρ z (hK hz), norm_inv]
      calc
        (D ρ : ℝ) * (n.factorial : ℝ) * ‖z - ρ‖⁻¹ ^ (n + 1) ≤
            (D ρ : ℝ) * (n.factorial : ℝ) *
              ((1 + R₀ / δ) ^ (n + 1) * ε⁻¹ ^ (n - 1) * ‖s₀ - ρ‖⁻¹ ^ 2) :=
          by
          apply mul_le_mul_of_nonneg_left hpower
          exact mul_nonneg hDreal (Nat.cast_nonneg _)
        _ = C * ((D ρ : ℝ) * ‖(s₀ - ρ)⁻¹‖ ^ 2) := by
          dsimp [C]
          rw [norm_inv]
          ring
  · refine ⟨fun _ : ℂ => (0 : ℝ), summable_zero, ?_⟩
    intro ρ z hz
    exact (hKne ⟨z, hz⟩).elim

/--
Inputs: a primitive nonprincipal completed Dirichlet `L`-function and a point to the right of
`Re s = 1`.
Claim: the centered genus-one resolvent sum is differentiable, and its derivative is the
reciprocal-square sum over completed zeros with multiplicity.
Proof: differentiate the resolvent terms on a small ball and dominate their derivatives uniformly
by four times the inverse-square mass at the center.
Role: identifies the completed genus expansion's derivative with the full zero divisor mass.
-/
theorem hasDerivAt_completed_genus_sum_right {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (hp : χ.IsPrimitive) (hinv : χ⁻¹ ≠ 1) {s : ℂ}
    (hs : 1 < s.re) :
    HasDerivAt
      (fun z : ℂ =>
        ∑' ρ : ℂ,
          (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℂ) * (1 / (z - ρ) + 1 / ρ))
      (∑' ρ : ℂ, -(MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℂ) * (s - ρ)⁻¹ ^ 2)
      s := by
  let D : ℂ → ℤ := MeromorphicOn.divisor χ.completedLFunction Set.univ
  let g : ℂ → ℂ → ℂ := fun ρ z => (D ρ : ℂ) * (1 / (z - ρ) + 1 / ρ)
  let g' : ℂ → ℂ → ℂ := fun ρ z => -(D ρ : ℂ) * (z - ρ)⁻¹ ^ 2
  let δ : ℝ := (s.re - 1) / 2
  let U : Set ℂ := Metric.ball s δ
  have hδ : 0 < δ := by
    dsimp only [δ]
    linarith only [hs]
  have hUopen : IsOpen U := Metric.isOpen_ball
  have hUconvex : Convex ℝ U := convex_ball s δ
  have hbase : Summable (g · s) := by
    simpa only [g, D] using summable_completed_genus_terms_right hq hp hχ hinv hs
  have hmajor : Summable (fun ρ : ℂ => 4 * ((D ρ : ℝ) * ‖(s - ρ)⁻¹‖ ^ 2)) := by
    simpa only [mul_assoc] using
      (summable_completed_genus_inverse_square hq hχ hp hinv hs).mul_left 4
  have hF : AnalyticOnNhd ℂ χ.completedLFunction Set.univ := by
    have hdiff := DirichletCharacter.differentiable_completedLFunction hχ
    intro z hz
    exact hdiff.analyticAt z
  have hDnonneg (ρ : ℂ) : 0 ≤ (D ρ : ℝ) := by
    exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hF ρ
  have hDcast (ρ : ℂ) : (D ρ : ℂ) = ((D ρ : ℝ) : ℂ) := by
    push_cast
    ring
  have hformula (ρ z : ℂ) (hz : z ∈ U) : HasDerivAt (g ρ) (g' ρ z) z := by
    by_cases hD : D ρ = 0
    · simpa only [g, g', D, hD, Int.cast_zero, zero_mul, neg_zero] using
        (hasDerivAt_const z (0 : ℂ))
    · have hzero := dirichletCompletedLFunction_zero_of_divisor_univ_ne_zero hχ hD
      have hre := completedLFunction_zero_re_lt_one hχ hzero
      have hclose : ‖z - s‖ < δ := by simpa only [dist_eq_norm] using Metric.mem_ball.mp hz
      have hzre : (s.re + 1) / 2 < z.re := by
        have habs : |(z - s).re| ≤ ‖z - s‖ := Complex.abs_re_le_norm (z - s)
        rw [Complex.sub_re] at habs
        dsimp only [δ] at hclose
        change (s.re + 1) / 2 < z.re
        have hlower := (abs_le.mp habs).1
        linarith only [hlower, hclose]
      have hden : z - ρ ≠ 0 := by
        intro heq
        have hre0 : (z - ρ).re = 0 := by
          rw [heq]; exact Complex.zero_re
        rw [Complex.sub_re] at hre0
        linarith only [hs, hzre, hre, hre0]
      have hInv := ((hasDerivAt_id z).sub_const ρ).inv hden
      have hterm := (hInv.add_const (1 / ρ)).const_mul (D ρ : ℂ)
      convert hterm using 1
      · funext w
        dsimp only [g, D]
        have hval : (fun x : ℂ => id x - ρ)⁻¹ w = (w - ρ)⁻¹ := by rfl
        rw [hval]
        simp only [one_div]
      · dsimp only [g', D]
        field_simp [hden]
        simp only [id_eq]
  have hbound (ρ z : ℂ) (hz : z ∈ U) : ‖g' ρ z‖ ≤ 4 * ((D ρ : ℝ) * ‖(s - ρ)⁻¹‖ ^ 2) := by
    by_cases hD : D ρ = 0
    · simp only [g', D, hD, Int.cast_zero, zero_mul, neg_zero, norm_zero, mul_zero, le_refl]
    · have hzero := dirichletCompletedLFunction_zero_of_divisor_univ_ne_zero hχ hD
      have hre := completedLFunction_zero_re_lt_one hχ hzero
      have hclose : ‖z - s‖ < δ := by simpa only [dist_eq_norm] using Metric.mem_ball.mp hz
      have hzre : (s.re + 1) / 2 < z.re := by
        have habs : |(z - s).re| ≤ ‖z - s‖ := Complex.abs_re_le_norm (z - s)
        rw [Complex.sub_re] at habs
        dsimp only [δ] at hclose
        change (s.re + 1) / 2 < z.re
        have hlower := (abs_le.mp habs).1
        linarith only [hlower, hclose]
      have hdenz : δ ≤ ‖z - ρ‖ := by
        have hreal : 0 < (z - ρ).re := by
          rw [Complex.sub_re]
          linarith only [hs, hzre, hre]
        have habs : |(z - ρ).re| ≤ ‖z - ρ‖ := Complex.abs_re_le_norm (z - ρ)
        rw [abs_of_pos hreal, Complex.sub_re] at habs
        dsimp only [δ]
        linarith only [hzre, hre, habs]
      have hdenS : δ ≤ ‖s - ρ‖ := by
        have hreal : 0 < (s - ρ).re := by
          rw [Complex.sub_re]
          linarith only [hs, hre]
        have habs : |(s - ρ).re| ≤ ‖s - ρ‖ := Complex.abs_re_le_norm (s - ρ)
        rw [abs_of_pos hreal, Complex.sub_re] at habs
        dsimp only [δ]
        linarith only [hs, hre, habs]
      have htriangle : ‖s - ρ‖ ≤ ‖z - ρ‖ + δ := by
        have heq : s - ρ = (s - z) + (z - ρ) := by ring
        have hclose' : ‖s - z‖ ≤ δ := by
          calc
            ‖s - z‖ = ‖z - s‖ := norm_sub_rev _ _
            _ ≤ δ := hclose.le
        rw [heq]
        calc
          ‖(s - z) + (z - ρ)‖ ≤ ‖s - z‖ + ‖z - ρ‖ := norm_add_le _ _
          _ ≤ δ + ‖z - ρ‖ := add_le_add hclose' le_rfl
          _ = ‖z - ρ‖ + δ := by ring_nf
      have hpow :=
        inv_pow_le_inv_sq_majorant (n := 1) (by norm_num only) hδ hδ hδ.le hdenz hdenS htriangle
      have hpow' : ‖(z - ρ)⁻¹‖ ^ 2 ≤ 4 * ‖(s - ρ)⁻¹‖ ^ 2 := by
        rw [norm_inv, norm_inv]
        norm_num only [div_self hδ.ne', Nat.sub_self, pow_zero] at hpow
        simpa only [mul_one, one_mul] using hpow
      have hnorm : ‖g' ρ z‖ = (D ρ : ℝ) * ‖(z - ρ)⁻¹‖ ^ 2 := by
        change ‖-(D ρ : ℂ) * (z - ρ)⁻¹ ^ 2‖ = _
        rw [hDcast, norm_mul, norm_neg, norm_pow, Complex.norm_of_nonneg (hDnonneg ρ)]
      rw [hnorm]
      calc
        (D ρ : ℝ) * ‖(z - ρ)⁻¹‖ ^ 2 ≤ (D ρ : ℝ) * (4 * ‖(s - ρ)⁻¹‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hpow' (hDnonneg ρ)
        _ = 4 * ((D ρ : ℝ) * ‖(s - ρ)⁻¹‖ ^ 2) := by ring
  exact
    hasDerivAt_tsum_of_isPreconnected hmajor hUopen hUconvex.isPreconnected hformula hbound
      (Metric.mem_ball_self hδ) hbase (Metric.mem_ball_self hδ)

/--
Inputs: a primitive nonprincipal completed Dirichlet `L`-function, a point to the right of
`Re s = 1`, and a positive derivative order.
Claim: the iterated derivative of the completed genus sum equals the sum of the iterated derivatives
of its individual zero terms.
Proof: apply the locally uniform convergence theorem for iterated derivatives, using the inverse-
square summability bound as a local majorant for every positive derivative order.
Role: permits higher derivatives of the zero expansion to be computed term by term.
-/
theorem iteratedDerivWithin_completed_genus_sum_right {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (hp : χ.IsPrimitive) (hinv : χ⁻¹ ≠ 1) {s : ℂ}
    (hs : 1 < s.re) (n : ℕ) (_hn : 0 < n) :
    iteratedDerivWithin n
        (fun z : ℂ =>
          ∑' ρ : ℂ,
            (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℂ) * (1 / (z - ρ) + 1 / ρ))
        {z : ℂ | 1 < z.re} s =
      ∑' ρ : ℂ,
        iteratedDerivWithin n
          (fun z : ℂ =>
            (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℂ) * (1 / (z - ρ) + 1 / ρ))
          {z : ℂ | 1 < z.re} s := by
  let V : Set ℂ := {z : ℂ | 1 < z.re}
  let D : ℂ → ℤ := MeromorphicOn.divisor χ.completedLFunction Set.univ
  let f : ℂ → ℂ → ℂ := fun ρ z => (D ρ : ℂ) * (1 / (z - ρ) + 1 / ρ)
  have hV : IsOpen V := isOpen_lt continuous_const Complex.continuous_re
  have hsV : s ∈ V := hs
  have hsum (z : ℂ) (hz : z ∈ V) : Summable (fun ρ : ℂ => f ρ z) := by
    simpa only [f, D] using summable_completed_genus_terms_right hq hp hχ hinv hz
  have hloc (k : ℕ) (hk₁ : 1 ≤ k) (hkn : k ≤ n) :
    SummableLocallyUniformlyOn (fun ρ : ℂ => iteratedDerivWithin k (f ρ) V) V := by
    exact
      summableLocallyUniformlyOn_completed_genus_term_iteratedDerivWithin hq hχ hp hinv hs k
        (Nat.lt_of_lt_of_le Nat.zero_lt_one hk₁)
  have hdiff (ρ : ℂ) (k : ℕ) (z : ℂ) (hk : k ≤ n) (hz : z ∈ V) :
    DifferentiableAt ℂ (iteratedDerivWithin k (f ρ) V) z := by
    have hF : AnalyticOnNhd ℂ χ.completedLFunction Set.univ := by
      have hderiv := DirichletCharacter.differentiable_completedLFunction hχ
      intro w hw
      exact hderiv.analyticAt w
    have ha : AnalyticOnNhd ℂ (f ρ) V := by
      intro w hw
      by_cases hD : D ρ = 0
      · simp only [f, hD, Int.cast_zero, zero_mul]
        exact analyticAt_const
      · have hzero := dirichletCompletedLFunction_zero_of_divisor_univ_ne_zero hχ hD
        have hρlt := completedLFunction_zero_re_lt_one hχ hzero
        have hden : w - ρ ≠ 0 := by
          intro heq
          have hre0 : (w - ρ).re = 0 := by
            rw [heq]; exact Complex.zero_re
          change 1 < w.re at hw
          rw [Complex.sub_re] at hre0
          linarith only [hw, hρlt, hre0]
        have hinv : AnalyticAt ℂ (fun z : ℂ => 1 / (z - ρ)) w := by
          exact analyticAt_const.div (analyticAt_id.sub analyticAt_const) hden
        exact analyticAt_const.mul (hinv.add analyticAt_const)
    have hcont : ContDiffOn ℂ ⊤ (f ρ) V := ha.contDiffOn_of_completeSpace
    have hderivOn : DifferentiableOn ℂ (iteratedDerivWithin k (f ρ) V) V :=
      hcont.differentiableOn_iteratedDerivWithin (WithTop.coe_lt_top (k : ℕ∞)) hV.uniqueDiffOn
    exact (hderivOn z hz).differentiableAt (hV.mem_nhds hz)
  change
    iteratedDerivWithin n (fun z : ℂ => ∑' ρ : ℂ, f ρ z) V s =
      ∑' ρ : ℂ, iteratedDerivWithin n (f ρ) V s
  exact
    iteratedDerivWithin_tsum n hV hsV hsum hloc
      (by
        intro ρ k r hk hr
        exact hdiff ρ k r hk hr)

/--
Inputs: a primitive nonprincipal completed Dirichlet `L`-function, a point right of `Re s = 1`,
and a positive derivative order.
Claim: the iterated derivative of the centered genus sum is the corresponding reciprocal-power
sum over completed zeros, counted with divisor multiplicity.
Proof: exchange the iterated derivative with the genus sum, then apply the explicit derivative
formula to each resolvent term.
Role: supplies higher zero moments for decompositions into local and remote zero sets.
-/
theorem iteratedDerivWithin_completed_genus_sum_eq_zero_moment {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (hp : χ.IsPrimitive) (hinv : χ⁻¹ ≠ 1) {s : ℂ}
    (hs : 1 < s.re) (n : ℕ) (hn : 0 < n) :
    iteratedDerivWithin n
        (fun z : ℂ =>
          ∑' ρ : ℂ,
            (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℂ) * (1 / (z - ρ) + 1 / ρ))
        {z : ℂ | 1 < z.re} s =
      ∑' ρ : ℂ,
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℂ) *
          ((-1 : ℂ) ^ n * (n.factorial : ℂ) * (s - ρ) ^ (-1 - (n : ℕ) : ℤ)) := by
  rw [iteratedDerivWithin_completed_genus_sum_right hq hχ hp hinv hs n hn]
  apply tsum_congr
  intro ρ
  exact
    iteratedDerivWithin_completed_genus_term (isOpen_lt continuous_const Complex.continuous_re) hn
      (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ) ρ s hs

/--
Inputs: a primitive nonprincipal completed Dirichlet `L`-function and a point right of `Re s = 1`.
Claim: the derivative of its logarithmic derivative equals the negative reciprocal-square sum over
all completed zeros, counted with divisor multiplicity.
Proof: differentiate the centered genus expansion and identify it locally with the centered
logarithmic derivative by the Hadamard identity.
Role: supplies the analytic inverse-square zero moment used in local and remote zero estimates.
-/
theorem deriv_logDeriv_eq_completed_genus_inverse_square {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (hp : χ.IsPrimitive) (hinv : χ⁻¹ ≠ 1) {s : ℂ}
    (hs : 1 < s.re) :
    deriv (logDeriv χ.completedLFunction) s =
      ∑' ρ : ℂ, -(MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℂ) * (s - ρ)⁻¹ ^ 2 := by
  let F : ℂ → ℂ := χ.completedLFunction
  have hF : AnalyticAt ℂ F s :=
    (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt s
  have hsne : F s ≠ 0 := completedLFunction_ne_zero_of_one_le_re hχ hs.le
  have hlog : AnalyticAt ℂ (logDeriv F) s := hF.deriv.div hF hsne
  have hcentered := (hlog.differentiableAt.hasDerivAt).sub_const (logDeriv F 0)
  have hGenus := hasDerivAt_completed_genus_sum_right hq hχ hp hinv hs
  have hEq :
    (fun z : ℂ => logDeriv F z - logDeriv F 0) =ᶠ[nhds s]
      (fun z : ℂ =>
        ∑' ρ : ℂ, (MeromorphicOn.divisor F Set.univ ρ : ℂ) * (1 / (z - ρ) + 1 / ρ)) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
    exact completed_centered_logDeriv_eq_genusSum_right hq hp hχ hinv hz
  have hGenus' := hGenus.congr_of_eventuallyEq hEq
  have hderiv := hcentered.unique hGenus'
  simpa only [F] using hderiv

/--
Inputs: a primitive nonprincipal completed Dirichlet `L`-function, a point to the right of
`Re s = 1`, and a positive derivative order.
Claim: the iterated derivative of the logarithmic derivative is a weighted reciprocal-power sum
over the completed zeros, with divisor multiplicity.
Proof: transfer the centered Hadamard expansion to iterated derivatives, exchange the derivative
and zero sum using local uniform convergence, and differentiate each resolvent term explicitly.
Role: provides higher zero moments for the Turán detection argument.
-/
theorem iteratedDerivWithin_logDeriv_eq_completed_genus_power_sum {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (hp : χ.IsPrimitive) (hinv : χ⁻¹ ≠ 1) {s : ℂ}
    (hs : 1 < s.re) (n : ℕ) (hn : 0 < n) :
    iteratedDerivWithin n (fun z : ℂ => logDeriv χ.completedLFunction z) {z : ℂ | 1 < z.re} s =
      ∑' ρ : ℂ,
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℂ) *
          ((-1 : ℂ) ^ n * (n.factorial : ℂ) * (s - ρ) ^ (-1 - (n : ℕ) : ℤ)) := by
  let V : Set ℂ := {z : ℂ | 1 < z.re}
  let F : ℂ → ℂ := χ.completedLFunction
  have hV : IsOpen V := isOpen_lt continuous_const Complex.continuous_re
  have hsV : s ∈ V := hs
  have hEq :
    Set.EqOn (fun z : ℂ => logDeriv F z - logDeriv F 0)
      (fun z : ℂ => ∑' ρ : ℂ, (MeromorphicOn.divisor F Set.univ ρ : ℂ) * (1 / (z - ρ) + 1 / ρ))
      V := by
    intro z hz
    exact completed_centered_logDeriv_eq_genusSum_right hq hp hχ hinv hz
  have hwithin := iteratedDerivWithin_congr (n := n) hEq
  have hcenterFun :
    (fun z : ℂ => logDeriv F z - logDeriv F 0) = fun z => -logDeriv F 0 + logDeriv F z := by
    funext z
    ring
  have hcenter :
    iteratedDerivWithin n (fun z : ℂ => logDeriv F z - logDeriv F 0) V s =
      iteratedDerivWithin n (fun z : ℂ => logDeriv F z) V s := by
    rw [hcenterFun, iteratedDerivWithin_const_add hn]
  have hsum := iteratedDerivWithin_completed_genus_sum_right hq hχ hp hinv hs n hn
  calc
    iteratedDerivWithin n (fun z : ℂ => logDeriv F z) V s =
        iteratedDerivWithin n (fun z : ℂ => logDeriv F z - logDeriv F 0) V s :=
      hcenter.symm
    _ =
        iteratedDerivWithin n
          (fun z : ℂ => ∑' ρ : ℂ, (MeromorphicOn.divisor F Set.univ ρ : ℂ) * (1 / (z - ρ) + 1 / ρ))
          V s :=
      hwithin hsV
    _ =
        ∑' ρ : ℂ,
          iteratedDerivWithin n
            (fun z : ℂ => (MeromorphicOn.divisor F Set.univ ρ : ℂ) * (1 / (z - ρ) + 1 / ρ)) V s :=
      hsum
    _ =
        ∑' ρ : ℂ,
          (MeromorphicOn.divisor F Set.univ ρ : ℂ) *
            ((-1 : ℂ) ^ n * (n.factorial : ℂ) * (s - ρ) ^ (-1 - (n : ℕ) : ℤ)) :=
      by
      apply tsum_congr
      intro ρ
      exact
        iteratedDerivWithin_completed_genus_term hV hn (MeromorphicOn.divisor F Set.univ ρ) ρ s hsV

/--
Inputs: a primitive nonprincipal completed Dirichlet `L`-function, a point right of `Re s = 1`,
a positive derivative order, and a finite set of zero locations.
Claim: its higher logarithmic-derivative moment is the finite sum over the set plus the sum over
the complementary locations, retaining divisor multiplicity in both terms.
Proof: obtain summability from local uniform convergence, then split the summable zero moment by
the finite-set complement identity.
Role: separates near zeros from the remaining zeros in the detector estimate.
-/
theorem iteratedDerivWithin_logDeriv_split_finite_complement {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (hp : χ.IsPrimitive) (hinv : χ⁻¹ ≠ 1) {s : ℂ}
    (hs : 1 < s.re) (n : ℕ) (hn : 0 < n) (S : Finset ℂ) :
    iteratedDerivWithin n (fun z : ℂ => logDeriv χ.completedLFunction z) {z : ℂ | 1 < z.re} s =
      (∑ ρ ∈ S,
          (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℂ) *
            ((-1 : ℂ) ^ n * (n.factorial : ℂ) * (s - ρ) ^ (-1 - (n : ℕ) : ℤ))) +
        ∑' (ρ : { ρ : ℂ // ρ ∉ S }),
          (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℂ) *
            ((-1 : ℂ) ^ n * (n.factorial : ℂ) * (s - ρ) ^ (-1 - (n : ℕ) : ℤ)) := by
  classical
  let V : Set ℂ := {z : ℂ | 1 < z.re}
  let term : ℂ → ℂ := fun ρ =>
    (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℂ) *
      ((-1 : ℂ) ^ n * (n.factorial : ℂ) * (s - ρ) ^ (-1 - (n : ℕ) : ℤ))
  have hlocal :=
    summableLocallyUniformlyOn_completed_genus_term_iteratedDerivWithin hq hχ hp hinv hs n hn
  have hsumDeriv :
    Summable
      (fun ρ : ℂ =>
        iteratedDerivWithin n
          (fun z : ℂ =>
            (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℂ) * (1 / (z - ρ) + 1 / ρ))
          V s) :=
    hlocal.summable hs
  have hsumTerm : Summable term :=
    hsumDeriv.congr fun ρ => by
      dsimp only [term]
      exact
        iteratedDerivWithin_completed_genus_term (isOpen_lt continuous_const Complex.continuous_re)
          hn (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ) ρ s hs
  calc
    iteratedDerivWithin n (fun z : ℂ => logDeriv χ.completedLFunction z) V s = ∑' ρ : ℂ, term ρ :=
      by
      simpa only [term, V] using
        iteratedDerivWithin_logDeriv_eq_completed_genus_power_sum hq hχ hp hinv hs n hn
    _ = (∑ ρ ∈ S, term ρ) + ∑' ρ : ↑((↑S : Set ℂ)ᶜ), term ρ := by
      simpa only [term] using (hsumTerm.sum_add_tsum_compl (s := S)).symm

/--
Inputs: a primitive nonprincipal completed Dirichlet `L`-function, a center right of `Re s = 1`,
a finite-radius local divisor disk, and a positive derivative order.
Claim: the higher logarithmic-derivative moment splits into the local divisor sum and the global
complementary zero sum, with the divisor multiplicities agreeing on the disk.
Proof: apply the finite-complement identity to the finite local support, then identify each local
divisor value with its global value on that support.
Role: connects the local zero power-sum block to the global derivative and its remote tail.
-/
theorem iteratedDerivWithin_logDeriv_eq_local_divisor_sum_add_complement {q : ℕ} [NeZero q]
    (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (hp : χ.IsPrimitive) (hinv : χ⁻¹ ≠ 1)
    {c : ℂ} (hc : 1 < c.re) (R : ℝ) (n : ℕ) (hn : 0 < n) :
    iteratedDerivWithin n (fun z : ℂ => logDeriv χ.completedLFunction z) {z : ℂ | 1 < z.re} c =
      (∑ ρ ∈ (completedLFunction_local_zero_support_finite χ hχ c R).toFinset,
          (MeromorphicOn.divisor χ.completedLFunction (Metric.ball c |R|) ρ : ℂ) *
            ((-1 : ℂ) ^ n * (n.factorial : ℂ) * (c - ρ) ^ (-1 - (n : ℕ) : ℤ))) +
        ∑' (ρ : { ρ : ℂ // ρ ∉ (completedLFunction_local_zero_support_finite χ hχ c R).toFinset }),
          (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℂ) *
            ((-1 : ℂ) ^ n * (n.factorial : ℂ) * (c - ρ) ^ (-1 - (n : ℕ) : ℤ)) := by
  classical
  let S := (completedLFunction_local_zero_support_finite χ hχ c R).toFinset
  have hsplit := iteratedDerivWithin_logDeriv_split_finite_complement hq hχ hp hinv hc n hn S
  have hsum :
    (∑ ρ ∈ S,
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℂ) *
          ((-1 : ℂ) ^ n * (n.factorial : ℂ) * (c - ρ) ^ (-1 - (n : ℕ) : ℤ))) =
      ∑ ρ ∈ S,
        (MeromorphicOn.divisor χ.completedLFunction (Metric.ball c |R|) ρ : ℂ) *
          ((-1 : ℂ) ^ n * (n.factorial : ℂ) * (c - ρ) ^ (-1 - (n : ℕ) : ℤ)) := by
    apply Finset.sum_congr rfl
    intro ρ hρ
    have hfinite :
      (MeromorphicOn.divisor χ.completedLFunction (Metric.ball c |R|)).support.Finite :=
      completedLFunction_local_zero_support_finite χ hχ c R
    have hmem : ρ ∈ (MeromorphicOn.divisor χ.completedLFunction (Metric.ball c |R|)).support :=
      (Set.Finite.mem_toFinset hfinite).mp (by simpa only [S] using hρ)
    have hball : ρ ∈ Metric.ball c |R| :=
      (MeromorphicOn.divisor χ.completedLFunction (Metric.ball c |R|)).supportWithinDomain hmem
    rw [completedLFunction_local_divisor_eq_global_at χ hχ c R hball]
  calc
    _ =
        (∑ ρ ∈ S,
            (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℂ) *
              ((-1 : ℂ) ^ n * (n.factorial : ℂ) * (c - ρ) ^ (-1 - (n : ℕ) : ℤ))) +
          ∑' (ρ : { ρ : ℂ // ρ ∉ S }),
            (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℂ) *
              ((-1 : ℂ) ^ n * (n.factorial : ℂ) * (c - ρ) ^ (-1 - (n : ℕ) : ℤ)) :=
      hsplit
    _ = _ := by
      simpa only [S] using
        congrArg
          (fun x : ℂ =>
            x +
              ∑' (ρ : { ρ : ℂ // ρ ∉ S }),
                (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℂ) *
                  ((-1 : ℂ) ^ n * (n.factorial : ℂ) * (c - ρ) ^ (-1 - (n : ℕ) : ℤ)))
          hsum

/--
Inputs: a nontrivial completed Dirichlet `L`-function, a positive local scale, and a power.
Claim: the global divisor sum over the complement of the local support equals the remote sum
filtered by distance from the center.
Proof: rewrite the subtype sum as an indicator sum; inside the disk the local and global divisors
agree, while every nonzero complementary term lies outside the disk.
Role: transfers the remote-tail estimate to the complementary term in the derivative split.
-/
theorem completedLFunction_local_support_complement_eq_remote_power_sum {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (c : ℂ) {η : ℝ} (hη : 0 < η) (k : ℕ) :
    ∑' (v :
        { v : ℂ // v ∉ (completedLFunction_local_zero_support_finite χ hχ c (80 * η)).toFinset }),
        (MeromorphicOn.divisor χ.completedLFunction Set.univ v : ℂ) * (c - v)⁻¹ ^ k =
      ∑' v : ℂ,
        ((if 80 * η ≤ ‖c - v‖ then (MeromorphicOn.divisor χ.completedLFunction Set.univ v : ℝ)
              else 0 :
              ℝ) :
            ℂ) *
          (if 80 * η ≤ ‖c - v‖ then (c - v)⁻¹ else 0) ^ k := by
  classical
  let U : Set ℂ := Metric.ball c |80 * η|
  let Dlocal : ℂ → ℤ := MeromorphicOn.divisor χ.completedLFunction U
  let Dglobal : ℂ → ℤ := MeromorphicOn.divisor χ.completedLFunction Set.univ
  let S : Finset ℂ := (completedLFunction_local_zero_support_finite χ hχ c (80 * η)).toFinset
  let Sc : Set ℂ := {v : ℂ | v ∉ S}
  let term : ℂ → ℂ := fun v => (Dglobal v : ℂ) * (c - v)⁻¹ ^ k
  let remoteTerm : ℂ → ℂ := fun v =>
    ((if 80 * η ≤ ‖c - v‖ then (Dglobal v : ℝ) else 0 : ℝ) : ℂ) *
      (if 80 * η ≤ ‖c - v‖ then (c - v)⁻¹ else 0) ^ k
  have hfinite : Dlocal.support.Finite := by
    simpa only [Dlocal, U] using completedLFunction_local_zero_support_finite χ hχ c (80 * η)
  have hpoint (v : ℂ) : Sc.indicator term v = remoteTerm v := by
    by_cases hremote : 80 * η ≤ ‖c - v‖
    · have hnotS : v ∉ S := by
        intro hvS
        have hsupport : v ∈ Dlocal.support := by
          apply (Set.Finite.mem_toFinset hfinite).mp
          simpa only [S, Dlocal, U] using hvS
        have hball : v ∈ U :=
          (MeromorphicOn.divisor χ.completedLFunction U).supportWithinDomain hsupport
        have hnorm : ‖c - v‖ < 80 * η := by
          have hball' := Metric.mem_ball.mp hball
          rw [dist_eq_norm, abs_of_pos (mul_pos (by norm_num) hη)] at hball'
          simpa only [norm_sub_rev] using hball'
        exact (not_lt_of_ge hremote hnorm)
      have hmemCompl : v ∈ Sc := by
        change v ∉ S
        exact hnotS
      rw [Set.indicator_of_mem hmemCompl]
      simp only [term, remoteTerm, Dglobal, hremote]
      push_cast
      rfl
    · by_cases hvS : v ∈ S
      · have hnot : v ∉ Sc := by
          change ¬v ∉ S
          exact not_not.mpr hvS
        simp only [Set.indicator_apply, hnot, remoteTerm, hremote, ite_false, Complex.ofReal_zero,
          zero_mul]
      · have hball : v ∈ U := by
          apply Metric.mem_ball.mpr
          rw [dist_eq_norm, norm_sub_rev, abs_of_pos (mul_pos (by norm_num) hη)]
          exact lt_of_not_ge hremote
        have hlocalzero : Dlocal v = 0 := by
          by_contra hne
          have hsupport : v ∈ Dlocal.support := by
            simp only [Function.mem_support]
            exact hne
          have hmemS : v ∈ S := by
            apply (Set.Finite.mem_toFinset hfinite).mpr
            simpa only [S, Dlocal, U] using hsupport
          exact hvS hmemS
        have hglobalzero : Dglobal v = 0 := by
          have heq := completedLFunction_local_divisor_eq_global_at χ hχ c (80 * η) hball
          have heq' : Dlocal v = Dglobal v := by simpa only [Dlocal, Dglobal, U] using heq
          rw [hlocalzero] at heq'
          exact heq'.symm
        have hmemCompl : v ∈ Sc := by
          change v ∉ S
          exact hvS
        rw [Set.indicator_of_mem hmemCompl]
        simp only [term, Dglobal, hglobalzero, remoteTerm, hremote, ite_false, Int.cast_zero,
          Complex.ofReal_zero, zero_mul]
  change ∑' (v : ↑Sc), term v = ∑' v : ℂ, remoteTerm v
  rw [tsum_subtype Sc term]
  apply tsum_congr
  intro v
  exact hpoint v

/--
Inputs: a primitive completed Dirichlet `L`-function, a point right of `Re s = 1`, and a subset
of its zeros.
Claim: the inverse-square mass restricted to the subset is bounded by the full inverse-square mass.
Proof: compare the nonnegative summands pointwise and use summability of the full genus mass.
Role: transfers the uniform global mass estimate to remote zero sets.
-/
theorem completed_genus_inverse_square_subset_mass_le {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (hp : χ.IsPrimitive) (hinv : χ⁻¹ ≠ 1) (S : Set ℂ)
    [DecidablePred fun ρ : ℂ => ρ ∈ S] {s : ℂ} (hs : 1 < s.re) :
    ∑' ρ : ℂ,
        (if ρ ∈ S then (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) else 0) *
          ‖if ρ ∈ S then (s - ρ)⁻¹ else 0‖ ^ 2 ≤
      ∑' ρ : ℂ, (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) * ‖(s - ρ)⁻¹‖ ^ 2 := by
  classical
  let D : ℂ → ℝ := fun ρ => (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ)
  let w : ℂ → ℝ := fun ρ => if ρ ∈ S then D ρ else 0
  let z : ℂ → ℂ := fun ρ => if ρ ∈ S then (s - ρ)⁻¹ else 0
  have hsum := summable_completed_genus_inverse_square hq hχ hp hinv hs
  have hF : AnalyticOnNhd ℂ χ.completedLFunction Set.univ := by
    have hdiff := DirichletCharacter.differentiable_completedLFunction hχ
    intro u hu
    exact hdiff.analyticAt u
  have hDnonneg (ρ : ℂ) : 0 ≤ D ρ := by
    change 0 ≤ (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ)
    exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hF ρ
  have hbase : Summable (fun ρ : ℂ => w ρ * ‖z ρ‖ ^ 2) := by
    apply Summable.of_norm_bounded hsum.norm
    intro ρ
    by_cases hρ : ρ ∈ S
    · simp only [w, z, D, hρ, ite_true, Real.norm_eq_abs]
      rfl
    · simp only [w, z, hρ, ite_false, zero_mul, Real.norm_eq_abs, abs_zero]
      exact abs_nonneg _
  have hpoint (ρ : ℂ) : w ρ * ‖z ρ‖ ^ 2 ≤ D ρ * ‖(s - ρ)⁻¹‖ ^ 2 := by
    by_cases hρ : ρ ∈ S
    · simp only [w, z, D, hρ, ite_true]
      rfl
    · simp only [w, z, hρ, ite_false, zero_mul]
      exact mul_nonneg (hDnonneg ρ) (sq_nonneg _)
  have hmass := hbase.tsum_le_tsum hpoint hsum
  simpa only [w, z, D] using hmass

/--
Inputs: a primitive nonprincipal completed Dirichlet `L`-function and a point to the right of
`Re s = 1`.
Claim: the total inverse-square zero mass is bounded by the real genus sum centered at `-1`,
divided by the horizontal distance to the zero-free half-plane.
Proof: dominate each inverse-square term by its nonnegative genus-kernel real part and sum the
pointwise inequalities.
Role: gives a quantitative square-mass input for absorbing remote zeros in the positive detector.
-/
theorem completed_genus_inverse_square_mass_le_right_genus_sum {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (hp : χ.IsPrimitive) (hinv : χ⁻¹ ≠ 1) {s : ℂ}
    (hs : 1 < s.re) :
    ∑' ρ : ℂ, (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) * ‖(s - ρ)⁻¹‖ ^ 2 ≤
      (s.re - 1)⁻¹ * (logDeriv χ.completedLFunction s - logDeriv χ.completedLFunction (-1)).re := by
  let F : ℂ → ℂ := χ.completedLFunction
  let D : ℂ → ℤ := MeromorphicOn.divisor F Set.univ
  let cterm : ℂ → ℂ := fun ρ => (D ρ : ℂ) * (1 / (s - ρ) + 1 / (1 + ρ))
  let rterm : ℂ → ℝ := fun ρ => (cterm ρ).re
  have hsum := summable_completed_genus_inverse_square hq hχ hp hinv hs
  have hseries : Summable cterm := by
    simpa only [cterm, D, F] using summable_completed_genus_terms_minus_one hq hp hχ hinv hs
  have hrseries : Summable rterm := by
    apply Summable.of_norm_bounded hseries.norm
    intro ρ
    exact Complex.abs_re_le_norm (cterm ρ)
  have hF : AnalyticOnNhd ℂ F Set.univ := by
    have hdiff := DirichletCharacter.differentiable_completedLFunction hχ
    intro u hu
    exact hdiff.analyticAt u
  have hDnonneg (ρ : ℂ) : 0 ≤ (D ρ : ℝ) := by
    exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hF ρ
  have hcast (ρ : ℂ) : (D ρ : ℂ) = ((D ρ : ℝ) : ℂ) := by
    push_cast
    ring
  have hterm (ρ : ℂ) : rterm ρ = (D ρ : ℝ) * ((1 / (s - ρ)).re + (1 / (1 + ρ)).re) := by
    dsimp [rterm, cterm]
    rw [hcast, Complex.re_ofReal_mul, Complex.add_re]
  have hpoint (ρ : ℂ) : (D ρ : ℝ) * ‖(s - ρ)⁻¹‖ ^ 2 ≤ (s.re - 1)⁻¹ * rterm ρ := by
    by_cases hD : D ρ = 0
    · rw [hterm, hD]
      simp only [Int.cast_zero, zero_mul, mul_zero]
      exact le_rfl
    · have hz := dirichletCompletedLFunction_zero_of_divisor_univ_ne_zero hχ hD
      have hrelt := completedLFunction_zero_re_lt_one hχ hz
      have hshift : 0 < s.re - 1 := by linarith only [hs]
      have hreal : s.re - 1 ≤ (s - ρ).re := by
        rw [Complex.sub_re]
        linarith only [hrelt]
      have hdiff : 0 < (s - ρ).re := lt_of_lt_of_le (by linarith only [hs]) hreal
      have hneq : s - ρ ≠ 0 := by
        intro heq
        have hre : (s - ρ).re = 0 := by
          rw [heq]; exact Complex.zero_re
        linarith only [hdiff, hre]
      have hnormsq : 0 < Complex.normSq (s - ρ) := by
        rw [Complex.normSq_eq_norm_sq]
        exact sq_pos_of_pos (norm_pos_iff.mpr hneq)
      have hinvsq : ‖(s - ρ)⁻¹‖ ^ 2 = (Complex.normSq (s - ρ))⁻¹ := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_inv]
      have hkernel : ‖(s - ρ)⁻¹‖ ^ 2 ≤ ((1 / (s - ρ)).re) / (s.re - 1) := by
        rw [hinvsq]
        conv_rhs => rw [one_div, Complex.inv_re]
        have hscaled : (s.re - 1) / Complex.normSq (s - ρ) ≤ (s - ρ).re / Complex.normSq (s - ρ) :=
          div_le_div_of_nonneg_right hreal hnormsq.le
        calc
          (Complex.normSq (s - ρ))⁻¹ = ((s.re - 1) / Complex.normSq (s - ρ)) / (s.re - 1) := by
            field_simp [ne_of_gt hshift]
          _ ≤ ((s - ρ).re / Complex.normSq (s - ρ)) / (s.re - 1) :=
            div_le_div_of_nonneg_right hscaled hshift.le
      have hkernelNonneg : 0 ≤ (1 / (s - ρ)).re := by
        rw [one_div, Complex.inv_re]
        exact div_nonneg (le_of_lt hdiff) (Complex.normSq_nonneg _)
      have hDpos := hDnonneg ρ
      have hρpos := completedLFunction_zero_re_pos hp hinv hz
      have h1ρpos : 0 < (1 + ρ).re := by
        rw [Complex.add_re, Complex.one_re]
        linarith only [hρpos]
      have htermBound :
        (D ρ : ℝ) * ‖(s - ρ)⁻¹‖ ^ 2 ≤
          ((D ρ : ℝ) * ((1 / (s - ρ)).re + (1 / (1 + ρ)).re)) / (s.re - 1) := by
        calc
          (D ρ : ℝ) * ‖(s - ρ)⁻¹‖ ^ 2 ≤ (D ρ : ℝ) * (((1 / (s - ρ)).re) / (s.re - 1)) :=
            mul_le_mul_of_nonneg_left hkernel hDpos
          _ = ((D ρ : ℝ) * ((1 / (s - ρ)).re)) / (s.re - 1) := by rw [mul_div_assoc]
          _ ≤ ((D ρ : ℝ) * ((1 / (s - ρ)).re + (1 / (1 + ρ)).re)) / (s.re - 1) :=
            div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left
                (le_add_of_nonneg_right
                  (by
                    rw [one_div, Complex.inv_re]
                    exact div_nonneg h1ρpos.le (Complex.normSq_nonneg _)))
                hDpos)
              hshift.le
      have hden : 0 < s.re - 1 := by linarith only [hs]
      calc
        (D ρ : ℝ) * ‖(s - ρ)⁻¹‖ ^ 2 ≤
            ((D ρ : ℝ) * ((1 / (s - ρ)).re + (1 / (1 + ρ)).re)) / (s.re - 1) :=
          htermBound
        _ = (s.re - 1)⁻¹ * rterm ρ := by
          rw [hterm]; ring
  have hscaled : Summable (fun ρ : ℂ => (s.re - 1)⁻¹ * rterm ρ) := hrseries.mul_left _
  have htotal := hsum.tsum_le_tsum hpoint hscaled
  have hglobal :
    (logDeriv χ.completedLFunction s - logDeriv χ.completedLFunction (-1)).re =
      ∑' ρ : ℂ, rterm ρ := by
    rw [completed_centered_logDeriv_eq_genusSum_minus_one hq hp hχ hinv hs, Complex.re_tsum hseries]
  calc
    _ ≤ ∑' ρ : ℂ, (s.re - 1)⁻¹ * rterm ρ := htotal
    _ = (s.re - 1)⁻¹ * ∑' ρ : ℂ, rterm ρ := by rw [tsum_mul_left]
    _ = (s.re - 1)⁻¹ * (logDeriv χ.completedLFunction s - logDeriv χ.completedLFunction (-1)).re :=
      by rw [hglobal]

/-! The fixed constants below make the inverse-square mass estimate uniform in the
conductor, character, and height. -/

/-- The uniform shift constant selected from the completed logarithmic-derivative estimate. -/
noncomputable def completedGenusMassShiftConstant : ℝ :=
  Classical.choose exists_uniform_norm_completed_logDeriv_small_shift_bound

/-- The fixed center constant selected from the completed logarithmic-derivative estimate. -/
noncomputable def completedGenusMassCenterConstant : ℝ :=
  Classical.choose
    (exists_norm_completed_logDeriv_small_shift_bound (r := 1) (by norm_num only)
      (by norm_num only))

/--
Inputs: a primitive nonprincipal completed Dirichlet `L`-function, a positive shift at most `1/2`,
and a height.
Claim: the inverse-square zero mass at `1 + η + it` has an explicit conductor-height bound with
leading term `4 / η^2`.
Proof: bound the genus sum using the uniform vertical logarithmic-derivative estimate and the
functional equation at `2`, then apply the inverse-square mass comparison.
Role: supplies the global mass estimate needed to verify remote-tail absorption quantitatively.
-/
theorem exists_completed_genus_inverse_square_mass_le_uniform_bound {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (hp : χ.IsPrimitive) (hinv : χ⁻¹ ≠ 1) {η : ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1 / 2) (t : ℝ) :
    ∃ A B : ℝ,
      A = completedGenusMassShiftConstant ∧
        B = completedGenusMassCenterConstant ∧
        0 < A ∧
        0 < B ∧
        ∑' ρ : ℂ,
            (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
              ‖((((1 + η : ℝ) : ℂ) + Complex.I * t) - ρ)⁻¹‖ ^ 2 ≤
          (1 / η) *
            (4 / η + A * (Real.log (4 + |t|) + 1) + Real.log q + 4 + B * (Real.log 4 + 1)) := by
  let A := completedGenusMassShiftConstant
  have hA : 0 < A := by
    dsimp only [A, completedGenusMassShiftConstant]
    exact (Classical.choose_spec exists_uniform_norm_completed_logDeriv_small_shift_bound).1
  have hderiv :
    ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q),
      χ ≠ 1 →
        ∀ {r : ℝ},
          0 < r →
            r ≤ 1 / 2 →
            ∀ t : ℝ,
              ‖logDeriv χ.completedLFunction (((1 + r : ℝ) : ℂ) + Complex.I * t)‖ ≤
                4 / r + A * (Real.log (4 + |t|) + 1) := by
    intro q inst χ hχ r hr hr1 t
    dsimp only [A, completedGenusMassShiftConstant]
    exact
      (Classical.choose_spec exists_uniform_norm_completed_logDeriv_small_shift_bound).2 χ hχ hr hr1
        t
  let B := completedGenusMassCenterConstant
  have hB : 0 < B := by
    dsimp only [B, completedGenusMassCenterConstant]
    exact
      (Classical.choose_spec
          (exists_norm_completed_logDeriv_small_shift_bound (r := 1) (by norm_num only)
            (by norm_num only))).1
  have hbase :
    ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q),
      χ ≠ 1 →
        ∀ t : ℝ,
          ‖logDeriv χ.completedLFunction (((1 + 1 : ℝ) : ℂ) + Complex.I * t)‖ ≤
            4 / 1 + B * (Real.log (4 + |t|) + 1) := by
    intro q inst χ hχ t
    dsimp only [B, completedGenusMassCenterConstant]
    exact
      (Classical.choose_spec
            (exists_norm_completed_logDeriv_small_shift_bound (r := 1) (by norm_num only)
              (by norm_num only))).2
        χ hχ t
  let s : ℂ := ((1 + η : ℝ) : ℂ) + Complex.I * t
  have hsre : s.re = 1 + η := by
    simp only [s, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
  have hnorm := hderiv χ hχ hη hη1 t
  let u : ℂ := ((1 + 1 : ℝ) : ℂ) + Complex.I * (0 : ℝ)
  have htwo : ‖logDeriv χ⁻¹.completedLFunction u‖ ≤ 4 + B * (Real.log 4 + 1) := by
    have hh := hbase χ⁻¹ hinv 0
    simpa only [u, abs_zero, div_one, add_zero] using hh
  have huEq : u = (2 : ℂ) := by
    dsimp only [u]
    rw [Complex.ofReal_zero, mul_zero, add_zero]
    rw [Complex.ofReal_add, Complex.ofReal_one]
    norm_num only
  have huRe : (1 : ℝ) ≤ u.re := by
    rw [huEq]
    change (1 : ℝ) ≤ 2
    norm_num only
  have hF2 : χ⁻¹.completedLFunction u ≠ 0 := completedLFunction_ne_zero_of_one_le_re hinv huRe
  have hfe := completedLFunction_logDeriv_functionalEquation_at hp hχ (s := u) hF2
  have hone : (1 : ℂ) - u = -1 := by
    rw [huEq]; norm_num only
  rw [hone] at hfe
  have hqreal : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast le_trans (by norm_num only : 1 ≤ 2) hq
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg hqreal
  have hlognorm : ‖Complex.log (q : ℂ)‖ = Real.log q := by
    rw [← Complex.natCast_log, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlogq]
  have hcenternorm :
    ‖logDeriv χ.completedLFunction (-1)‖ ≤ Real.log q + 4 + B * (Real.log 4 + 1) := by
    calc
      ‖logDeriv χ.completedLFunction (-1)‖ = ‖-logDeriv χ.completedLFunction (-1)‖ := by
        rw [norm_neg]
      _ = ‖Complex.log (q : ℂ) + logDeriv χ⁻¹.completedLFunction u‖ := by rw [hfe]
      _ ≤ ‖Complex.log (q : ℂ)‖ + ‖logDeriv χ⁻¹.completedLFunction u‖ := norm_add_le _ _
      _ ≤ Real.log q + (4 + B * (Real.log 4 + 1)) := add_le_add hlognorm.le htwo
      _ = _ := by ring
  have hcenterre :
    |(logDeriv χ.completedLFunction (-1)).re| ≤ Real.log q + 4 + B * (Real.log 4 + 1) :=
    (Complex.abs_re_le_norm _).trans hcenternorm
  have hnorm' : ‖logDeriv χ.completedLFunction s‖ ≤ 4 / η + A * (Real.log (4 + |t|) + 1) := by
    simpa only [s] using hnorm
  have hgenus :
    (logDeriv χ.completedLFunction s - logDeriv χ.completedLFunction (-1)).re ≤
      4 / η + A * (Real.log (4 + |t|) + 1) + Real.log q + 4 + B * (Real.log 4 + 1) := by
    rw [Complex.sub_re]
    have hpoint : (logDeriv χ.completedLFunction s).re ≤ ‖logDeriv χ.completedLFunction s‖ :=
      Complex.re_le_norm _
    have hcenter :
      -(logDeriv χ.completedLFunction (-1)).re ≤ |(logDeriv χ.completedLFunction (-1)).re| :=
      neg_le_abs _
    linarith only [hpoint, hcenter, hnorm', hcenterre]
  have hmass :=
    completed_genus_inverse_square_mass_le_right_genus_sum hq hχ hp hinv (s := s)
      (by
        rw [hsre]; linarith only [hη])
  have hηinv : 0 ≤ 1 / η := (one_div_pos.mpr hη).le
  refine ⟨A, B, rfl, rfl, hA, hB, ?_⟩
  have hmass' :
    ∑' ρ : ℂ, (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) * ‖(s - ρ)⁻¹‖ ^ 2 ≤
      (1 / η) * (logDeriv χ.completedLFunction s - logDeriv χ.completedLFunction (-1)).re := by
    rw [hsre, show (1 + η : ℝ) - 1 = η by ring] at hmass
    convert hmass using 1; ring
  simpa only [s] using hmass'.trans (mul_le_mul_of_nonneg_left hgenus hηinv)

/--
Inputs: two points `s` and `w`, a positive lower bound `δ` for the distance from `s` to `ρ`, a
nonnegative weight, and an order `k ≥ 2`.
Claim: the reciprocal-power term at `w` is bounded by a fixed multiple of the inverse-square
term at `s`, uniformly whenever `w` is within `δ / 2` of `s`.
Proof: the denominator at `w` is at least half its distance at `s`, while the latter is at least
`δ`; split the power into its square and the remaining `k - 2` factors.
Role: supplies a local uniform majorant for differentiating the completed genus series.
-/
private theorem weighted_reciprocal_power_uniform_bound {δ D : ℝ} {w s ρ : ℂ} {k : ℕ} (hδ : 0 < δ)
    (hD : 0 ≤ D) (hsep : δ ≤ ‖s - ρ‖) (hclose : ‖w - s‖ ≤ δ / 2) (hk : 2 ≤ k) :
    D * ‖(w - ρ)⁻¹‖ ^ k ≤ 4 * (2 / δ) ^ (k - 2) * (D * ‖(s - ρ)⁻¹‖ ^ 2) := by
  have hleft : ‖s - ρ‖ ≤ ‖s - w‖ + ‖w - ρ‖ := by
    calc
      ‖s - ρ‖ = ‖(s - w) + (w - ρ)‖ := by
        congr 1; abel
      _ ≤ ‖s - w‖ + ‖w - ρ‖ := norm_add_le _ _
  have hws : ‖s - w‖ = ‖w - s‖ := norm_sub_rev _ _
  have hdist : ‖s - ρ‖ / 2 ≤ ‖w - ρ‖ := by
    rw [hws] at hleft
    nlinarith only [hleft, hclose, hsep]
  have hw0 : w - ρ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hdist
    have hspos : 0 < ‖s - ρ‖ := lt_of_lt_of_le hδ hsep
    linarith only [hspos, hdist]
  have hden : 0 < ‖s - ρ‖ := lt_of_lt_of_le hδ hsep
  have hdenw : 0 < ‖w - ρ‖ := norm_pos_iff.mpr hw0
  have hinv : ‖(w - ρ)⁻¹‖ ≤ 2 * ‖(s - ρ)⁻¹‖ := by
    rw [norm_inv, norm_inv]
    have hratio : 1 / ‖w - ρ‖ ≤ 2 / ‖s - ρ‖ := by
      apply (div_le_div_iff₀ hdenw hden).2
      nlinarith only [hdist]
    simpa only [one_div, div_eq_mul_inv, one_mul] using hratio
  have hsInv : ‖(s - ρ)⁻¹‖ ≤ 1 / δ := by
    rw [norm_inv]
    simpa only [one_div] using one_div_le_one_div_of_le hδ hsep
  have hsmall : ‖(w - ρ)⁻¹‖ ≤ 2 / δ := by
    calc
      ‖(w - ρ)⁻¹‖ ≤ 2 * ‖(s - ρ)⁻¹‖ := hinv
      _ ≤ 2 * (1 / δ) := mul_le_mul_of_nonneg_left hsInv (by norm_num)
      _ = 2 / δ := by ring
  have hpow : ‖(w - ρ)⁻¹‖ ^ k ≤ (2 / δ) ^ (k - 2) * ‖(w - ρ)⁻¹‖ ^ 2 := by
    rw [← Nat.sub_add_cancel hk, pow_add]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hsmall _) (sq_nonneg _)
  have hsq : ‖(w - ρ)⁻¹‖ ^ 2 ≤ 4 * ‖(s - ρ)⁻¹‖ ^ 2 := by
    calc
      ‖(w - ρ)⁻¹‖ ^ 2 ≤ (2 * ‖(s - ρ)⁻¹‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hinv _
      _ = 4 * ‖(s - ρ)⁻¹‖ ^ 2 := by ring
  calc
    D * ‖(w - ρ)⁻¹‖ ^ k ≤ D * ((2 / δ) ^ (k - 2) * ‖(w - ρ)⁻¹‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hpow hD
    _ ≤ D * ((2 / δ) ^ (k - 2) * (4 * ‖(s - ρ)⁻¹‖ ^ 2)) := by
      apply mul_le_mul_of_nonneg_left
      · exact mul_le_mul_of_nonneg_left hsq (pow_nonneg (by positivity) _)
      · exact hD
    _ = _ := by ring

/-! ## Remote reciprocal-power tails -/

/--
Inputs: a primitive nonprincipal completed Dirichlet `L`-function, a point right of `Re s = 1`,
a set of divisor points separated from `s`, and a power `k ≥ 2`.
Claim: the divisor-weighted reciprocal-power sum over that set is absolutely summable and is
bounded by its inverse-square mass times the remote radius to the power `k - 2`.
Proof: apply the generic weighted power-sum estimate to the divisor multiplicities restricted to
the set, using `summable_completed_genus_inverse_square` for the square mass.
Role: controls the infinite remote contribution in the local zero detector.
-/
theorem norm_tsum_completed_genus_remote_reciprocal_power_le {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (hp : χ.IsPrimitive) (hinv : χ⁻¹ ≠ 1) (S : Set ℂ)
    [DecidablePred fun ρ : ℂ => ρ ∈ S] {s : ℂ} (hs : 1 < s.re) {η : ℝ} (hη : 0 < η)
    (hremote : ∀ ρ ∈ S, 8 * η ≤ ‖s - ρ‖) (k : ℕ) (hk : 2 ≤ k) :
    Summable
        (fun ρ : ℂ =>
          ((if ρ ∈ S then (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) else 0 : ℝ) :
              ℂ) *
            (if ρ ∈ S then (s - ρ)⁻¹ else 0) ^ k) ∧
      ‖∑' ρ : ℂ,
            ((if ρ ∈ S then (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) else 0 :
                  ℝ) :
                ℂ) *
              (if ρ ∈ S then (s - ρ)⁻¹ else 0) ^ k‖ ≤
        (8 * η)⁻¹ ^ (k - 2) *
          ∑' ρ : ℂ,
            (if ρ ∈ S then (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) else 0) *
              ‖if ρ ∈ S then (s - ρ)⁻¹ else 0‖ ^ 2 := by
  classical
  let D : ℂ → ℝ := fun ρ => (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ)
  let w : ℂ → ℝ := fun ρ => if ρ ∈ S then D ρ else 0
  let z : ℂ → ℂ := fun ρ => if ρ ∈ S then (s - ρ)⁻¹ else 0
  have hsum := summable_completed_genus_inverse_square hq hχ hp hinv hs
  have hF : AnalyticOnNhd ℂ χ.completedLFunction Set.univ := by
    have hdiff := DirichletCharacter.differentiable_completedLFunction hχ
    intro u hu
    exact hdiff.analyticAt u
  have hDnonneg (ρ : ℂ) : 0 ≤ D ρ := by
    change 0 ≤ (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ)
    exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hF ρ
  have hw (ρ : ℂ) : 0 ≤ w ρ := by
    by_cases hρ : ρ ∈ S
    · simp only [w, hρ, ite_true]
      exact hDnonneg ρ
    · simp only [w, hρ, ite_false]
      exact le_rfl
  have hz (ρ : ℂ) : ‖z ρ‖ ≤ (8 * η)⁻¹ := by
    by_cases hρ : ρ ∈ S
    · simp only [z, hρ, ite_true]
      rw [norm_inv]
      have hpos : 0 < 8 * η := by positivity
      simpa only [one_div] using one_div_le_one_div_of_le hpos (hremote ρ hρ)
    · simp only [z, hρ, ite_false]
      simp only [norm_zero]
      positivity
  have hbase : Summable (fun ρ : ℂ => w ρ * ‖z ρ‖ ^ 2) := by
    apply Summable.of_norm_bounded hsum.norm
    intro ρ
    by_cases hρ : ρ ∈ S
    · simp only [w, z, hρ, ite_true, D, Real.norm_eq_abs]
      rfl
    · simp only [w, z, hρ, ite_false, zero_mul, Real.norm_eq_abs, abs_zero]
      exact abs_nonneg _
  have hbound := norm_tsum_weighted_power_le_of_summable_square w z hw hz hbase k hk
  rcases hbound with ⟨hpower, hbound⟩
  exact ⟨by simpa only [w, z, D] using hpower, by simpa only [w, z, D] using hbound⟩

/--
Inputs: positive `η` and `N`, a natural order `k`, and a bound on a nonnegative square mass.
Claim: the square-mass tail at distance `8η` is at most half of the near-zero scale
`(1 / (4N)) * (1 / (3η))^(k + 1)`.
Proof: compare the two inverse powers by multiplying through their positive denominators.
Role: gives the exact numerical absorption step for the remote completed-zero contribution.
-/
private theorem remote_inverse_power_tail_le_half_near_scale {η N S : ℝ} {k : ℕ} (hη : 0 < η)
    (hN : 0 < N) (hsmall : 8 * N * S * (3 * η) ^ (k + 1) ≤ (8 * η) ^ (k - 2)) :
    S * (1 / (8 * η)) ^ (k - 2) ≤ (1 / (8 * N)) * (1 / (3 * η)) ^ (k + 1) := by
  have hleft : S * (1 / (8 * η)) ^ (k - 2) = S / (8 * η) ^ (k - 2) := by
    rw [one_div_pow]
    ring
  have hright : (1 / (8 * N)) * (1 / (3 * η)) ^ (k + 1) = 1 / ((8 * N) * (3 * η) ^ (k + 1)) := by
    rw [one_div_pow, one_div_mul_one_div]
  rw [hleft, hright]
  have hdenLeft : 0 < (8 * η) ^ (k - 2) := pow_pos (mul_pos (by norm_num only) hη) _
  have hdenRight : 0 < (8 * N) * (3 * η) ^ (k + 1) :=
    mul_pos (mul_pos (by norm_num only) hN) (pow_pos (mul_pos (by norm_num only) hη) _)
  have hsmall' : S * (8 * N * (3 * η) ^ (k + 1)) ≤ 1 * (8 * η) ^ (k - 2) := by
    convert hsmall using 1 <;> ring
  exact (div_le_div_iff₀ hdenLeft hdenRight).2 hsmall'

/--
Inputs: positive `η` and a fixed real coefficient multiplying the geometric ratio `3 / 8`.
Claim: beyond some natural order `K`, the remote-tail absorption inequality holds at every order
`k ≥ K`.
Proof: powers of `3 / 8` tend to zero; rewrite the desired inequality as a constant multiple of
that geometric power times the positive scale `(8η)^(k - 2)`.
Role: chooses the derivative order needed to absorb the remote inverse-square mass.
-/
private theorem exists_nat_ge_geometric_remote_tail {η N S : ℝ} (hη : 0 < η) :
    ∃ K : ℕ, 2 ≤ K ∧ ∀ k : ℕ, K ≤ k → 8 * N * S * (3 * η) ^ (k + 1) ≤ (8 * η) ^ (k - 2) := by
  let A : ℝ := 216 * N * S * η ^ 3
  have hpow : Filter.Tendsto (fun n : ℕ => ((3 : ℝ) / 8) ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hlim : Filter.Tendsto (fun n : ℕ => A * ((3 : ℝ) / 8) ^ n) Filter.atTop (nhds 0) := by
    simpa only [mul_zero] using hpow.const_mul A
  have hev := hlim.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  rcases Filter.eventually_atTop.mp hev with ⟨m₀, hm₀⟩
  refine ⟨m₀ + 2, by omega, ?_⟩
  intro k hk
  let m : ℕ := k - 2
  have hm : A * ((3 : ℝ) / 8) ^ m < 1 := by
    apply hm₀
    dsimp only [m]
    omega
  have heq : 8 * N * S * (3 * η) ^ (k + 1) = A * (((3 : ℝ) / 8) ^ m * (8 * η) ^ m) := by
    have hkp : k + 1 = m + 3 := by
      dsimp only [m]; omega
    rw [hkp, pow_add, ← mul_pow]
    have hmul : ((3 : ℝ) / 8) * (8 * η) = 3 * η := by ring
    rw [hmul]
    dsimp only [A]
    ring
  have hη8 : 0 < (8 : ℝ) * η := mul_pos (by norm_num) hη
  calc
    8 * N * S * (3 * η) ^ (k + 1) = _ := heq
    _ = (A * ((3 : ℝ) / 8) ^ m) * (8 * η) ^ m := by ring
    _ ≤ 1 * (8 * η) ^ m := mul_le_mul_of_nonneg_right hm.le (pow_nonneg hη8.le m)
    _ = (8 * η) ^ (k - 2) := by ring

/--
Inputs: positive `η`, a positive near-signal scale, and an order satisfying the geometric tail
condition with matching inverse-power exponents.
Claim: the remote reciprocal-power sum is bounded by the near-signal scale at the same power.
Proof: rewrite both sides as quotients and apply the stated cross-multiplied inequality.
Role: aligns the remote estimate with the exponent `n + 1` in the completed logarithmic derivative.
-/
private theorem remote_inverse_power_tail_le_matching_scale {η N S : ℝ} {k : ℕ} (hη : 0 < η)
    (hN : 0 < N) (hsmall : 8 * N * S * (3 * η) ^ k ≤ (8 * η) ^ (k - 2)) :
    S * (1 / (8 * η)) ^ (k - 2) ≤ (1 / (8 * N)) * (1 / (3 * η)) ^ k := by
  have hleft : S * (1 / (8 * η)) ^ (k - 2) = S / (8 * η) ^ (k - 2) := by
    rw [one_div_pow]
    ring
  have hright : (1 / (8 * N)) * (1 / (3 * η)) ^ k = 1 / ((8 * N) * (3 * η) ^ k) := by
    rw [one_div_pow, one_div_mul_one_div]
  rw [hleft, hright]
  have hdenLeft : 0 < (8 * η) ^ (k - 2) := pow_pos (mul_pos (by norm_num only) hη) _
  have hdenRight : 0 < (8 * N) * (3 * η) ^ k :=
    mul_pos (mul_pos (by norm_num only) hN) (pow_pos (mul_pos (by norm_num only) hη) _)
  have hsmall' : S * (8 * N * (3 * η) ^ k) ≤ 1 * (8 * η) ^ (k - 2) := by
    convert hsmall using 1 <;> ring
  exact (div_le_div_iff₀ hdenLeft hdenRight).2 hsmall'

/--
Inputs: positive `η` and a fixed real coefficient multiplying the geometric ratio `3 / 8`.
Claim: beyond an explicit natural order, the matching-exponent remote-tail condition holds for
every larger order.
Proof: Bernoulli's inequality bounds the geometric threshold by a ceiling; rewrite the condition
as that geometric factor times `(8η)^(k - 2)`.
Role: chooses a quantified order threshold for the completed logarithmic-derivative moment.
-/
private theorem exists_nat_ge_geometric_remote_tail_matching_scale {η N S : ℝ} (hη : 0 < η)
    (Kmin : ℕ) (hKmin : 2 ≤ Kmin) :
    ∃ K : ℕ,
      Kmin ≤ K ∧
        K ≤ max (Nat.ceil (max (72 * N * S * η ^ 2) 0) + 3) Kmin ∧
        2 ≤ K ∧ ∀ k : ℕ, K ≤ k → 8 * N * S * (3 * η) ^ k ≤ (8 * η) ^ (k - 2) := by
  let A : ℝ := 72 * N * S * η ^ 2
  let Apos : ℝ := max A 0
  let M : ℕ := Nat.ceil Apos + 1
  let K : ℕ := max (Nat.ceil Apos + 3) Kmin
  have hApos : 0 ≤ Apos := le_max_right _ _
  have hAle : A ≤ Apos := le_max_left _ _
  have hAposceil : Apos ≤ (Nat.ceil Apos : ℝ) := Nat.le_ceil Apos
  have hceil_lt : (Nat.ceil Apos : ℝ) < (Nat.ceil Apos + 1 : ℕ) := by
    exact_mod_cast Nat.lt_succ_self (Nat.ceil Apos)
  have hA_lt_M : A < (M : ℝ) := by
    dsimp only [M]
    exact lt_of_le_of_lt (hAle.trans hAposceil) hceil_lt
  have hMleK : M + 2 ≤ K := by
    dsimp only [M, K]; omega
  have hKupper : K ≤ max (Nat.ceil (max (72 * N * S * η ^ 2) 0) + 3) Kmin := by
    dsimp only [K, Apos, A]
    simp only [max_comm]
    exact le_rfl
  refine ⟨K, le_max_right _ _, hKupper, le_trans hKmin (le_max_right _ _), ?_⟩
  intro k hk
  have hkbase : M + 2 ≤ k := le_trans hMleK hk
  let m : ℕ := k - 2
  have hmM : M ≤ m := by
    dsimp only [m]; omega
  have hceil_lt_m : Nat.ceil Apos < m := by
    dsimp only [M] at hmM; omega
  have hceil_lt_mR : (Nat.ceil Apos : ℝ) < (m : ℝ) := by exact_mod_cast hceil_lt_m
  have hmA : A < (m : ℝ) := lt_of_le_of_lt (hAle.trans hAposceil) hceil_lt_mR
  have hgeo := Real.mul_add_one_le_add_one_pow (a := (5 : ℝ) / 3) (by positivity) m
  have hbase : (5 : ℝ) / 3 + 1 = 8 / 3 := by norm_num
  rw [hbase] at hgeo
  have hgeo' : 1 + (5 : ℝ) / 3 * m ≤ (8 / 3 : ℝ) ^ m := by simpa only [add_comm] using hgeo
  have hden : 0 < 1 + (5 : ℝ) / 3 * m := by positivity
  have hpow : ((3 : ℝ) / 8) ^ m ≤ 1 / (1 + (5 : ℝ) / 3 * m) := by
    apply (le_div_iff₀ hden).2
    calc
      (3 / 8 : ℝ) ^ m * (1 + 5 / 3 * m) ≤ (3 / 8 : ℝ) ^ m * (8 / 3 : ℝ) ^ m :=
        mul_le_mul_of_nonneg_left hgeo' (pow_nonneg (by positivity) m)
      _ = 1 := by
        rw [← mul_pow]; norm_num
  have hmnonneg : 0 ≤ (m : ℝ) := by exact_mod_cast (Nat.zero_le m)
  have hnum : Apos < 1 + (5 : ℝ) / 3 * m := by
    have hAposltm : Apos < (m : ℝ) := lt_of_le_of_lt hAposceil hceil_lt_mR
    nlinarith only [hAposltm, hmnonneg]
  have hsmallpos : Apos * ((3 : ℝ) / 8) ^ m < 1 := by
    calc
      Apos * ((3 : ℝ) / 8) ^ m ≤ Apos * (1 / (1 + (5 : ℝ) / 3 * m)) :=
        mul_le_mul_of_nonneg_left hpow hApos
      _ = Apos / (1 + (5 : ℝ) / 3 * m) := by simp only [div_eq_mul_inv, one_mul]
      _ < 1 := (div_lt_one hden).2 hnum
  have hm : A * ((3 : ℝ) / 8) ^ m < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right hAle (pow_nonneg (by positivity) m)) hsmallpos
  have heq : 8 * N * S * (3 * η) ^ k = A * (((3 : ℝ) / 8) ^ m * (8 * η) ^ m) := by
    have hkp : k = m + 2 := by
      dsimp only [m]; omega
    rw [hkp, pow_add, ← mul_pow]
    have hmul : ((3 : ℝ) / 8) * (8 * η) = 3 * η := by ring
    rw [hmul]
    dsimp only [A]
    ring
  have hη8 : 0 < (8 : ℝ) * η := mul_pos (by norm_num) hη
  calc
    8 * N * S * (3 * η) ^ k = _ := heq
    _ = (A * ((3 : ℝ) / 8) ^ m) * (8 * η) ^ m := by ring
    _ ≤ 1 * (8 * η) ^ m := mul_le_mul_of_nonneg_right hm.le (pow_nonneg hη8.le m)
    _ = (8 * η) ^ (k - 2) := by ring

/--
Inputs: a primitive completed Dirichlet `L`-function, a remote set of zeros, and a square-mass
condition at a center right of `Re s = 1`.
Claim: the remote reciprocal-power sum is at most half the near-zero signal at order `k`.
Proof: apply the inverse-square tail estimate and the explicit denominator comparison above.
Role: separates the remaining analytic task, proving the stated square-mass condition, from the
already formalized absorption of the remote terms.
-/
theorem norm_tsum_completed_genus_remote_reciprocal_power_le_half_near_scale {q : ℕ} [NeZero q]
    (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (hp : χ.IsPrimitive) (hinv : χ⁻¹ ≠ 1)
    (S : Set ℂ) [DecidablePred fun ρ : ℂ => ρ ∈ S] {s : ℂ} (hs : 1 < s.re) {η N : ℝ} (hη : 0 < η)
    (hN : 0 < N) (hremote : ∀ ρ ∈ S, 8 * η ≤ ‖s - ρ‖) (k : ℕ) (hk : 2 ≤ k)
    (hsmall :
      8 * N *
          (∑' ρ : ℂ,
            (if ρ ∈ S then (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) else 0) *
              ‖if ρ ∈ S then (s - ρ)⁻¹ else 0‖ ^ 2) *
          (3 * η) ^ (k + 1) ≤
        (8 * η) ^ (k - 2)) :
    ‖∑' ρ : ℂ,
          ((if ρ ∈ S then (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) else 0 : ℝ) :
              ℂ) *
            (if ρ ∈ S then (s - ρ)⁻¹ else 0) ^ k‖ ≤
      (1 / (8 * N)) * (1 / (3 * η)) ^ (k + 1) := by
  have htail :=
    norm_tsum_completed_genus_remote_reciprocal_power_le hq hχ hp hinv S hs hη hremote k hk
  have habsorb := remote_inverse_power_tail_le_half_near_scale hη hN hsmall
  calc
    _ ≤
        (8 * η)⁻¹ ^ (k - 2) *
          ∑' ρ : ℂ,
            (if ρ ∈ S then (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) else 0) *
              ‖if ρ ∈ S then (s - ρ)⁻¹ else 0‖ ^ 2 :=
      htail.2
    _ ≤ (1 / (8 * N)) * (1 / (3 * η)) ^ (k + 1) := by simpa only [one_div, mul_comm] using habsorb

/--
Inputs: a remote set of zeros, a positive inverse-square mass bound, and a matching-exponent
geometric tail condition.
Claim: the remote reciprocal-power sum is bounded by the near-signal scale at the same power.
Proof: apply the inverse-square tail estimate, then use the matching-exponent denominator bound.
Role: supplies the tail estimate needed to compare with the local power sum in an order-`n`
logarithmic derivative.
-/
theorem norm_tsum_completed_genus_remote_reciprocal_power_le_matching_scale {q : ℕ} [NeZero q]
    (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (hp : χ.IsPrimitive) (hinv : χ⁻¹ ≠ 1)
    (S : Set ℂ) [DecidablePred fun ρ : ℂ => ρ ∈ S] {s : ℂ} (hs : 1 < s.re) {η N : ℝ} (hη : 0 < η)
    (hN : 0 < N) (hremote : ∀ ρ ∈ S, 8 * η ≤ ‖s - ρ‖) (k : ℕ) (hk : 2 ≤ k)
    (hsmall :
      8 * N *
          (∑' ρ : ℂ,
            (if ρ ∈ S then (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) else 0) *
              ‖if ρ ∈ S then (s - ρ)⁻¹ else 0‖ ^ 2) *
          (3 * η) ^ k ≤
        (8 * η) ^ (k - 2)) :
    ‖∑' ρ : ℂ,
          ((if ρ ∈ S then (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) else 0 : ℝ) :
              ℂ) *
            (if ρ ∈ S then (s - ρ)⁻¹ else 0) ^ k‖ ≤
      (1 / (8 * N)) * (1 / (3 * η)) ^ k := by
  have htail :=
    norm_tsum_completed_genus_remote_reciprocal_power_le hq hχ hp hinv S hs hη hremote k hk
  have habsorb := remote_inverse_power_tail_le_matching_scale hη hN hsmall
  calc
    _ ≤
        (8 * η)⁻¹ ^ (k - 2) *
          ∑' ρ : ℂ,
            (if ρ ∈ S then (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) else 0) *
              ‖if ρ ∈ S then (s - ρ)⁻¹ else 0‖ ^ 2 :=
      htail.2
    _ ≤ (1 / (8 * N)) * (1 / (3 * η)) ^ k := by simpa only [one_div, mul_comm] using habsorb

/--
Inputs: a remote set of completed zeros and an upper bound for its inverse-square mass.
Claim: some derivative order has remote reciprocal-power sum at most half the near-zero scale.
Proof: choose an order from geometric decay, use the mass bound to establish the absorption
inequality, then apply the remote-tail estimate.
Role: removes the order-dependent square-mass condition from the remote-tail interface.
-/
theorem exists_k_completed_genus_remote_reciprocal_power_le_half_near_scale {q : ℕ} [NeZero q]
    (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (hp : χ.IsPrimitive) (hinv : χ⁻¹ ≠ 1)
    (S : Set ℂ) [DecidablePred fun ρ : ℂ => ρ ∈ S] {s : ℂ} (hs : 1 < s.re) {η N M : ℝ} (hη : 0 < η)
    (hN : 0 < N) (hremote : ∀ ρ ∈ S, 8 * η ≤ ‖s - ρ‖)
    (hMass :
      ∑' ρ : ℂ,
          (if ρ ∈ S then (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) else 0) *
            ‖if ρ ∈ S then (s - ρ)⁻¹ else 0‖ ^ 2 ≤
        M) :
    ∃ k : ℕ,
      2 ≤ k ∧
        ‖∑' ρ : ℂ,
              ((if ρ ∈ S then (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) else 0 :
                    ℝ) :
                  ℂ) *
                (if ρ ∈ S then (s - ρ)⁻¹ else 0) ^ k‖ ≤
          (1 / (8 * N)) * (1 / (3 * η)) ^ (k + 1) := by
  obtain ⟨k, hk, hsmallM⟩ := exists_nat_ge_geometric_remote_tail (η := η) (N := N) (S := M) hη
  have hη3 : 0 ≤ (3 * η) ^ (k + 1) := by positivity
  have hsmall :
    8 * N *
        (∑' ρ : ℂ,
          (if ρ ∈ S then (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) else 0) *
            ‖if ρ ∈ S then (s - ρ)⁻¹ else 0‖ ^ 2) *
        (3 * η) ^ (k + 1) ≤
      (8 * η) ^ (k - 2) := by
    calc
      _ ≤ (8 * N * M) * (3 * η) ^ (k + 1) := by
        apply mul_le_mul_of_nonneg_right _ hη3
        exact mul_le_mul_of_nonneg_left hMass (by positivity)
      _ = 8 * N * M * (3 * η) ^ (k + 1) := by ring
      _ ≤ (8 * η) ^ (k - 2) := hsmallM k le_rfl
  exact
    ⟨k, hk,
      norm_tsum_completed_genus_remote_reciprocal_power_le_half_near_scale hq hχ hp hinv S hs hη hN
        hremote k hk hsmall⟩

/--
Purpose: express the explicit derivative-order cutoff obtained from the conductor-height
inverse-square mass estimate.
Definition: take the ceiling of the geometric threshold computed from the mass constants, height,
conductor, shift, and requested minimum order.
Inputs: the conductor, shift, height, mass scale and constants, and minimum derivative order.
Output: an order beyond which the remote reciprocal-power tail is absorbed.
Role: makes the matching-scale bound available to the local zero detector and its callers.
-/
noncomputable def completedGenusRemoteTailCutoffFromMass (q : ℕ) (η t N A B : ℝ) (Kmin : ℕ) : ℕ :=
  max
    (Nat.ceil
        (max
          (72 * N *
            ((1 / η) *
              (4 / η + A * (Real.log (4 + |t|) + 1) + Real.log q + 4 + B * (Real.log 4 + 1))) *
            η ^ 2)
          0) +
      3)
    Kmin

/-- The remote-tail order cutoff using the fixed completed-genus mass constants. -/
noncomputable def completedGenusRemoteTailUniformCutoff (q : ℕ) (η t N : ℝ) (Kmin : ℕ) : ℕ :=
  completedGenusRemoteTailCutoffFromMass q η t N completedGenusMassShiftConstant
    completedGenusMassCenterConstant Kmin

/--
Inputs: a primitive character, a positive shift at most `1/2`, a height, and a remote set of zeros.
Claim: a threshold order exists beyond which every remote power sum is absorbed using the explicit
conductor-height inverse-square mass bound.
Proof: bound the mass on the remote set by the global mass, then apply geometric decay and the
remote-tail comparison.
Role: supplies the unconditional mass estimate needed by local zero detection.
-/
theorem exists_k_completed_genus_remote_reciprocal_power_le_uniform_half_near_scale {q : ℕ}
    [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (hp : χ.IsPrimitive)
    (hinv : χ⁻¹ ≠ 1) (S : Set ℂ) [DecidablePred fun ρ : ℂ => ρ ∈ S] {η : ℝ} (hη : 0 < η)
    (hη1 : η ≤ 1 / 2) (t : ℝ) {N : ℝ} (hN : 0 < N) (Kmin : ℕ)
    (hremote : ∀ ρ ∈ S, 8 * η ≤ ‖(((1 + η : ℝ) : ℂ) + Complex.I * t) - ρ‖) :
    ∃ A B : ℝ,
      0 < A ∧
        0 < B ∧
        ∃ K : ℕ,
          Kmin ≤ K ∧
            2 ≤ K ∧
            ∀ k : ℕ,
              K ≤ k →
                ‖∑' ρ : ℂ,
                      ((if ρ ∈ S then (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ)
                            else 0 :
                            ℝ) :
                          ℂ) *
                        (if ρ ∈ S then ((((1 + η : ℝ) : ℂ) + Complex.I * t) - ρ)⁻¹ else 0) ^ k‖ ≤
                  (1 / (8 * N)) * (1 / (3 * η)) ^ (k + 1) := by
  let s : ℂ := ((1 + η : ℝ) : ℂ) + Complex.I * t
  have hs : 1 < s.re := by
    dsimp only [s]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
    linarith only [hη]
  obtain ⟨A, B, _, _, hA, hB, hglobal⟩ :=
    exists_completed_genus_inverse_square_mass_le_uniform_bound hq hχ hp hinv hη hη1 t
  have hsubset := completed_genus_inverse_square_subset_mass_le hq hχ hp hinv S hs
  have hremote' : ∀ ρ ∈ S, 8 * η ≤ ‖s - ρ‖ := by simpa only [s] using hremote
  let M := (1 / η) * (4 / η + A * (Real.log (4 + |t|) + 1) + Real.log q + 4 + B * (Real.log 4 + 1))
  have hglobal' :
    ∑' ρ : ℂ, (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) * ‖(s - ρ)⁻¹‖ ^ 2 ≤
      M := by
    simpa only [M, s] using hglobal
  have hMass := hsubset.trans hglobal'
  obtain ⟨K₀, hK₀, hsmallM⟩ := exists_nat_ge_geometric_remote_tail (η := η) (N := N) (S := M) hη
  let K := max K₀ Kmin
  have hKmin' : Kmin ≤ K := le_max_right _ _
  have hK : 2 ≤ K := le_trans hK₀ (le_max_left _ _)
  refine ⟨A, B, hA, hB, K, hKmin', hK, ?_⟩
  intro k hk
  have hk₀ : K₀ ≤ k := le_trans (le_max_left _ _) hk
  have hsmall :
    8 * N *
        (∑' ρ : ℂ,
          (if ρ ∈ S then (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) else 0) *
            ‖if ρ ∈ S then (s - ρ)⁻¹ else 0‖ ^ 2) *
        (3 * η) ^ (k + 1) ≤
      (8 * η) ^ (k - 2) := by
    have hη3 : 0 ≤ (3 * η) ^ (k + 1) := by positivity
    calc
      _ ≤ (8 * N * M) * (3 * η) ^ (k + 1) := by
        apply mul_le_mul_of_nonneg_right _ hη3
        exact mul_le_mul_of_nonneg_left hMass (by positivity)
      _ = 8 * N * M * (3 * η) ^ (k + 1) := by ring
      _ ≤ (8 * η) ^ (k - 2) := hsmallM k hk₀
  have htail :=
    norm_tsum_completed_genus_remote_reciprocal_power_le_half_near_scale hq hχ hp hinv S hs hη hN
      hremote' k (le_trans hK hk) hsmall
  simpa only [s] using htail

/--
Inputs: a primitive character, a positive shift at most `1/2`, a height, and a remote set of zeros.
Claim: every sufficiently high remote reciprocal-power sum is bounded at its own inverse-power
scale by the explicit conductor-height inverse-square mass estimate.
Proof: bound the remote mass by the global inverse-square mass and apply the matching-exponent
geometric tail estimate.
Role: aligns the unconditional remote bound with the completed logarithmic-derivative formula.
-/
theorem exists_k_completed_genus_remote_reciprocal_power_le_uniform_matching_scale {q : ℕ}
    [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (hp : χ.IsPrimitive)
    (hinv : χ⁻¹ ≠ 1) (S : Set ℂ) [DecidablePred fun ρ : ℂ => ρ ∈ S] {η : ℝ} (hη : 0 < η)
    (hη1 : η ≤ 1 / 2) (t : ℝ) {N : ℝ} (hN : 0 < N) (Kmin : ℕ) (hKmin : 2 ≤ Kmin)
    (hremote : ∀ ρ ∈ S, 8 * η ≤ ‖(((1 + η : ℝ) : ℂ) + Complex.I * t) - ρ‖) :
    ∃ A B : ℝ,
      0 < A ∧
        0 < B ∧
        ∃ K : ℕ,
          Kmin ≤ K ∧
            K ≤ completedGenusRemoteTailUniformCutoff q η t N Kmin ∧
            2 ≤ K ∧
            ∀ k : ℕ,
              K ≤ k →
                ‖∑' ρ : ℂ,
                      ((if ρ ∈ S then (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ)
                            else 0 :
                            ℝ) :
                          ℂ) *
                        (if ρ ∈ S then ((((1 + η : ℝ) : ℂ) + Complex.I * t) - ρ)⁻¹ else 0) ^ k‖ ≤
                  (1 / (8 * N)) * (1 / (3 * η)) ^ k := by
  let s : ℂ := ((1 + η : ℝ) : ℂ) + Complex.I * t
  have hs : 1 < s.re := by
    dsimp only [s]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
    linarith only [hη]
  obtain ⟨A, B, hAeq, hBeq, hA, hB, hglobal⟩ :=
    exists_completed_genus_inverse_square_mass_le_uniform_bound hq hχ hp hinv hη hη1 t
  have hsubset := completed_genus_inverse_square_subset_mass_le hq hχ hp hinv S hs
  have hremote' : ∀ ρ ∈ S, 8 * η ≤ ‖s - ρ‖ := by simpa only [s] using hremote
  let M := (1 / η) * (4 / η + A * (Real.log (4 + |t|) + 1) + Real.log q + 4 + B * (Real.log 4 + 1))
  have hglobal' :
    ∑' ρ : ℂ, (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) * ‖(s - ρ)⁻¹‖ ^ 2 ≤
      M := by
    simpa only [M, s] using hglobal
  have hMass := hsubset.trans hglobal'
  obtain ⟨K, hKmin', hKupper, hK, hsmallM⟩ :=
    exists_nat_ge_geometric_remote_tail_matching_scale (η := η) (N := N) (S := M) hη Kmin hKmin
  have hKupper' : K ≤ completedGenusRemoteTailUniformCutoff q η t N Kmin := by
    simpa only [hAeq, hBeq, completedGenusRemoteTailUniformCutoff,
      completedGenusRemoteTailCutoffFromMass, M] using hKupper
  refine ⟨A, B, hA, hB, K, hKmin', hKupper', hK, ?_⟩
  intro k hk
  have hsmall :
    8 * N *
        (∑' ρ : ℂ,
          (if ρ ∈ S then (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) else 0) *
            ‖if ρ ∈ S then (s - ρ)⁻¹ else 0‖ ^ 2) *
        (3 * η) ^ k ≤
      (8 * η) ^ (k - 2) := by
    have hηk : 0 ≤ (3 * η) ^ k := by positivity
    calc
      _ ≤ (8 * N * M) * (3 * η) ^ k := by
        apply mul_le_mul_of_nonneg_right _ hηk
        exact mul_le_mul_of_nonneg_left hMass (by positivity)
      _ = 8 * N * M * (3 * η) ^ k := by ring
      _ ≤ (8 * η) ^ (k - 2) := hsmallM k hk
  have htail :=
    norm_tsum_completed_genus_remote_reciprocal_power_le_matching_scale hq hχ hp hinv S hs hη hN
      hremote' k (le_trans hK hk) hsmall
  simpa only [s] using htail

/-- For a primitive character, the local zero multiplicity is bounded by the genus sum centered
at `-1`. Both reciprocal kernels are nonnegative at completed zeros in the critical strip.
Inputs: a near-one rectangle contained within distance `η / 4` of `1 + it`.
Claim: its multiplicity is at most `2η` times the real part of the shifted logarithmic
derivative difference.
Role: removes the uncontrolled center at zero from the local multiplicity estimate.
-/
theorem completedZeroMultiplicityCountInRectangle_le_minus_one_genus_sum {q : ℕ} [NeZero q]
    (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (hp : χ.IsPrimitive) (hinv : χ⁻¹ ≠ 1)
    {η : ℝ} (hη : 0 < η) {t : ℝ} (z w : ℂ)
    (hbox :
      ∀ ρ ∈ dirichletCompletedLFunctionRectangleBox z w,
        ‖ρ - ((1 : ℂ) + (t : ℂ) * Complex.I)‖ ≤ η / 4) :
    completedZeroMultiplicityCountInRectangle χ hχ z w ≤
      2 * η *
        (logDeriv χ.completedLFunction ((1 + η) + (t : ℂ) * Complex.I) -
            logDeriv χ.completedLFunction (-1)).re := by
  let F : ℂ → ℂ := χ.completedLFunction
  let s : ℂ := (1 + η) + (t : ℂ) * Complex.I
  let D : ℂ → ℤ := MeromorphicOn.divisor F Set.univ
  let cterm : ℂ → ℂ := fun ρ => (D ρ : ℂ) * (1 / (s - ρ) + 1 / (1 + ρ))
  let rterm : ℂ → ℝ := fun ρ => (cterm ρ).re
  have hs : 1 < s.re := by
    dsimp [s]
    simp only [Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im,
      mul_zero, mul_one, sub_zero]
    linarith only [hη]
  have hseries : Summable cterm := by
    simpa only [cterm, D, F, s] using (summable_completed_genus_terms_minus_one hq hp hχ hinv hs)
  have hrseries : Summable rterm := by
    apply Summable.of_norm_bounded hseries.norm
    intro ρ
    exact Complex.abs_re_le_norm (cterm ρ)
  have hF : AnalyticOnNhd ℂ F Set.univ := by
    have hdiff := DirichletCharacter.differentiable_completedLFunction hχ
    intro u hu
    exact hdiff.analyticAt u
  have hDnonneg (ρ : ℂ) : 0 ≤ (D ρ : ℝ) := by
    exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hF ρ
  have hcast (ρ : ℂ) : (D ρ : ℂ) = ((D ρ : ℝ) : ℂ) := by
    push_cast
    ring
  have hterm (ρ : ℂ) : rterm ρ = (D ρ : ℝ) * ((1 / (s - ρ)).re + (1 / (1 + ρ)).re) := by
    dsimp [rterm, cterm]
    rw [hcast, Complex.re_ofReal_mul, Complex.add_re]
  have hnonneg (ρ : ℂ) : 0 ≤ rterm ρ := by
    by_cases hD : D ρ = 0
    · simp only [rterm, cterm, D, hD, Int.cast_zero, zero_mul, Complex.zero_re, le_refl]
    · have hz := dirichletCompletedLFunction_zero_of_divisor_univ_ne_zero hχ hD
      have hrepos := completedLFunction_zero_re_pos hp hinv hz
      have hrelt := completedLFunction_zero_re_lt_one hχ hz
      rw [hterm]
      apply mul_nonneg (hDnonneg ρ)
      apply add_nonneg
      · rw [one_div, Complex.inv_re]
        apply div_nonneg
        · dsimp [s]
          simp only [Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
            Complex.ofReal_im, mul_one, mul_zero, sub_zero]
          linarith only [hη, hrelt]
        · exact Complex.normSq_nonneg _
      · rw [one_div, Complex.inv_re]
        have hplus : 0 ≤ (1 + ρ).re := by
          simp only [Complex.add_re, Complex.one_re]
          linarith only [hrepos]
        exact div_nonneg hplus (Complex.normSq_nonneg _)
  have hglobal : (logDeriv F s - logDeriv F (-1)).re = ∑' ρ, rterm ρ := by
    rw [completed_centered_logDeriv_eq_genusSum_minus_one hq hp hχ hinv hs, Complex.re_tsum hseries]
  let S := completedZerosInRectangle χ hχ z w
  have hpoint (ρ : ℂ) (hρ : ρ ∈ S) : (analyticOrderNatAt F ρ : ℝ) ≤ 2 * η * rterm ρ := by
    have hmem := mem_completedZerosInRectangle_iff.mp hρ
    have hzero := hmem.2
    have hclose := hbox ρ hmem.1
    have hk : (1 / (s - ρ)).re ≥ 1 / (2 * η) := by
      simpa only [s] using re_inv_ge_half_inv_of_completed_zero_near_one hχ hη hclose hzero
    have hpos := completedLFunction_zero_re_pos hp hinv hzero
    have horder : D ρ = (analyticOrderNatAt F ρ : ℤ) := by
      rw [show D = MeromorphicOn.divisor F Set.univ from rfl,
        MeromorphicOn.AnalyticOnNhd.divisor_apply hF (Set.mem_univ ρ)]
      change
        ((analyticOrderAt F ρ).map (fun k : ℕ => (k : ℤ))).untop₀ =
          ((analyticOrderAt F ρ).toNat : ℤ)
      induction analyticOrderAt F ρ using ENat.recTopCoe
      · rfl
      · rfl
    have hm : 0 ≤ (analyticOrderNatAt F ρ : ℝ) := Nat.cast_nonneg _
    have hd : (D ρ : ℝ) = (analyticOrderNatAt F ρ : ℝ) := by
      rw [horder]
      push_cast
      rfl
    rw [hterm, hd]
    have hkernel : 0 ≤ (1 / (1 + ρ)).re := by
      rw [one_div, Complex.inv_re]
      have hplus : 0 ≤ (1 + ρ).re := by
        simp only [Complex.add_re, Complex.one_re]
        linarith only [hpos]
      exact div_nonneg hplus (Complex.normSq_nonneg _)
    have hmain :
      (analyticOrderNatAt F ρ : ℝ) ≤ 2 * η * ((analyticOrderNatAt F ρ : ℝ) * (1 / (s - ρ)).re) := by
      have hden : 0 < 2 * η := mul_pos (by norm_num only : (0 : ℝ) < 2) hη
      have hmul := mul_le_mul_of_nonneg_left hk hm
      have hdiv :
        (analyticOrderNatAt F ρ : ℝ) / (2 * η) ≤
          (analyticOrderNatAt F ρ : ℝ) * (1 / (s - ρ)).re := by
        convert hmul using 1; ring
      calc
        (analyticOrderNatAt F ρ : ℝ) = ((analyticOrderNatAt F ρ : ℝ) / (2 * η)) * (2 * η) := by
          rw [div_mul_cancel₀ _ hden.ne']
        _ ≤ ((analyticOrderNatAt F ρ : ℝ) * (1 / (s - ρ)).re) * (2 * η) :=
          mul_le_mul_of_nonneg_right hdiv hden.le
        _ = _ := by ring
    calc
      (analyticOrderNatAt F ρ : ℝ) ≤ 2 * η * ((analyticOrderNatAt F ρ : ℝ) * (1 / (s - ρ)).re) :=
        hmain
      _ ≤ 2 * η * ((analyticOrderNatAt F ρ : ℝ) * ((1 / (s - ρ)).re + (1 / (1 + ρ)).re)) := by
        apply mul_le_mul_of_nonneg_left
        · exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hkernel) hm
        · exact mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2) hη.le
  have hcount : (∑ ρ ∈ S, (analyticOrderNatAt F ρ : ℝ)) ≤ 2 * η * ∑' ρ, rterm ρ := by
    calc
      (∑ ρ ∈ S, (analyticOrderNatAt F ρ : ℝ)) ≤ ∑ ρ ∈ S, 2 * η * rterm ρ := by
        apply Finset.sum_le_sum
        intro ρ hρ
        exact hpoint ρ hρ
      _ = 2 * η * ∑ ρ ∈ S, rterm ρ := by rw [Finset.mul_sum]
      _ ≤ 2 * η * ∑' ρ, rterm ρ := by
        apply mul_le_mul_of_nonneg_left
        · exact hrseries.sum_le_tsum S (fun ρ _ => hnonneg ρ)
        · exact mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2) hη.le
  unfold completedZeroMultiplicityCountInRectangle
  simpa only [S, F, s] using hcount.trans_eq (by rw [hglobal])

open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/--
Inputs: a nontrivial character, an explicit local center `re c = 2 - σ`, and `29/30 ≤ σ < 1`.
Claim: the local divisor support in the ball of radius `4(1 - σ)` has cardinality at most a
logarithmic expression in the conductor and height, with no local-center L-value in the bound.
Content: move the Jensen center to `2 + im(c) * I`, where the existing product inequality gives
a uniform lower bound for the ordinary L-value; the local square lies in radius `4/3` there.
Proof: compare support cardinality with a rectangular zero count, apply Jensen with outer radius
`3/2`, and substitute the lower bound at the real-part-two center.
Role: controls the variable order in the local Turán argument using only conductor and height.
-/
theorem completedLFunction_explicit_local_divisor_support_card_le_log_bound {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hq : 1 < q) {σ : ℝ} (hσ : (29 / 30 : ℝ) ≤ σ)
    (hσlt : σ < 1) (c : ℂ) (hcre : c.re = 2 - σ) :
    (((completedLFunction_local_zero_support_finite χ hχ c (4 * (1 - σ))).toFinset.card : ℕ) : ℝ) ≤
      Real.log (2 * max (1 : ℝ) (2 * (q : ℝ) * (‖(2 + Complex.I * c.im : ℂ)‖ + 3 / 2))) /
        Real.log (9 / 8) := by
  let δ : ℝ := 1 - σ
  let r : ℝ := 4 * δ
  let z : ℂ := ⟨c.re - r, c.im - r⟩
  let w : ℂ := ⟨c.re + r, c.im + r⟩
  let C : ℂ := 2 + Complex.I * c.im
  have hδpos : 0 < δ := by
    dsimp [δ]
    linarith only [hσlt]
  have hδle : δ ≤ 1 / 30 := by
    dsimp [δ]
    linarith only [hσ]
  have hrpos : 0 < r := by
    dsimp [r]
    positivity
  have hrle : r ≤ 2 / 15 := by
    dsimp [r]
    nlinarith only [hδle]
  have hscale : 0 < 4 * (1 - σ) := by nlinarith only [hσlt]
  have habs : |4 * (1 - σ)| = 4 * (1 - σ) := abs_of_pos hscale
  have hbox :
    ∀ u,
      u ∈
          (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
              (Metric.ball c |4 * (1 - σ)|)).support →
        u ∈ dirichletCompletedLFunctionRectangleBox z w := by
    intro u hu
    have hu' :
      u ∈
        (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.ball c (4 * (1 - σ)))).support := by
      rw [← habs]
      exact hu
    have hu'' :
      u ∈
        (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.ball c r)).support := by
      simpa only [r, δ] using hu'
    have hmem := completedLFunction_local_divisor_support_mem_centered_square χ c hrpos hu''
    simpa only [z, w, r] using hmem
  have hcard :=
    completedLFunction_local_divisor_support_card_le_rectangle_count χ hχ c (4 * (1 - σ)) z w hbox
  have hcoord :
    ∀ x ∈ Set.uIcc z.re w.re,
      ∀ y ∈ Set.uIcc z.im w.im, (x - C.re) ^ 2 + (y - C.im) ^ 2 ≤ |(4 / 3 : ℝ)| ^ 2 := by
    intro x hx y hy
    have horderX : z.re ≤ w.re := by
      dsimp [z, w, r]
      linarith only [hrpos]
    have horderY : z.im ≤ w.im := by
      dsimp [z, w, r]
      linarith only [hrpos]
    have hx' : c.re - r ≤ x ∧ x ≤ c.re + r := by
      simpa only [Set.uIcc_of_le horderX, Set.mem_Icc, z, w] using hx
    have hy' : c.im - r ≤ y ∧ y ≤ c.im + r := by
      simpa only [Set.uIcc_of_le horderY, Set.mem_Icc, z, w] using hy
    have hxlow : -(11 / 10 : ℝ) ≤ x - 2 := by
      dsimp [r] at hx'
      rw [hcre] at hx'
      nlinarith only [hx'.1, hδle]
    have hxhigh : x - 2 ≤ 0 := by
      dsimp [r] at hx'
      rw [hcre] at hx'
      nlinarith only [hx'.2, hδle]
    have hylo : -(1 / 6 : ℝ) ≤ y - c.im := by nlinarith only [hy'.1, hrle]
    have hyhi : y - c.im ≤ 1 / 6 := by nlinarith only [hy'.2, hrle]
    have hcreC : C.re = 2 := by
      simp only [C, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.re_ofNat, zero_mul, mul_zero, sub_zero, add_zero]
    have hcimC : C.im = c.im := by
      simp only [C, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.im_ofNat, zero_mul]
      ring
    rw [hcreC, hcimC]
    nlinarith only [hxlow, hxhigh, hylo, hyhi]
  have hcenter : (1 / 2 : ℝ) ≤ ‖DirichletCharacter.LFunction χ C‖ := by
    simpa only [C] using norm_LFunction_lower_bound_at_two χ c.im
  have hc : DirichletCharacter.LFunction χ C ≠ 0 := by
    intro hz0
    have hnorm0 : ‖DirichletCharacter.LFunction χ C‖ = 0 := by rw [hz0, norm_zero]
    linarith only [hcenter, hnorm0]
  have hcircle : ∀ u ∈ Metric.sphere C |(3 / 2 : ℝ)|, 1 / 2 ≤ u.re := by
    intro u hu
    have hd : dist u C = 3 / 2 := by
      simpa only [abs_of_pos (by norm_num only : (0 : ℝ) < (3 / 2 : ℝ))] using
        Metric.mem_sphere.mp hu
    have hn : ‖u - C‖ = 3 / 2 := by
      rw [← dist_eq_norm]
      exact hd
    have hre : |u.re - C.re| ≤ 3 / 2 := by
      rw [← Complex.sub_re]
      calc
        |(u - C).re| ≤ ‖u - C‖ := Complex.abs_re_le_norm (u - C)
        _ = 3 / 2 := hn
    have hC : C.re = 2 := by
      simp only [C, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.re_ofNat, zero_mul, mul_zero, sub_zero, add_zero]
    linarith only [(abs_le.mp hre).1, hC]
  have hJ :=
    completedZeroMultiplicityCountInRectangle_le_LFunction_Jensen_bound hq hχ z w C (r := 4 / 3)
      (R := 3 / 2) (by norm_num only) (by norm_num only) hc hcircle
      (by simpa only [abs_of_pos (by norm_num only : (0 : ℝ) < (4 / 3 : ℝ))] using hcoord)
  have hJ' :
    completedZeroMultiplicityCountInRectangle χ hχ z w ≤
      Real.log (max (1 : ℝ) (2 * (q : ℝ) * (‖C‖ + 3 / 2)) / ‖DirichletCharacter.LFunction χ C‖) /
        Real.log (9 / 8) := by
    have hrati : (3 / 2 : ℝ) / (4 / 3) = 9 / 8 := by norm_num only
    simpa only [abs_of_pos (by norm_num only : (0 : ℝ) < (3 / 2 : ℝ)),
      abs_of_pos (by norm_num only : (0 : ℝ) < (4 / 3 : ℝ)), hrati] using hJ
  have hnormpos : 0 < ‖DirichletCharacter.LFunction χ C‖ :=
    lt_of_lt_of_le (by norm_num only) hcenter
  have hlog :
    Real.log (max (1 : ℝ) (2 * (q : ℝ) * (‖C‖ + 3 / 2)) / ‖DirichletCharacter.LFunction χ C‖) ≤
      Real.log (2 * max (1 : ℝ) (2 * (q : ℝ) * (‖C‖ + 3 / 2))) := by
    apply Real.log_le_log
    · positivity
    · apply (div_le_iff₀ hnormpos).2
      have hm :
        max (1 : ℝ) (2 * (q : ℝ) * (‖C‖ + 3 / 2)) ≤
          2 * max (1 : ℝ) (2 * (q : ℝ) * (‖C‖ + 3 / 2)) := by
        nlinarith only [le_max_left (1 : ℝ) (2 * (q : ℝ) * (‖C‖ + 3 / 2))]
      nlinarith only [hcenter, hm]
  have hdenpos : 0 < Real.log (9 / 8) := by
    apply Real.log_pos
    norm_num only
  have hJ'' := hJ'.trans (div_le_div_of_nonneg_right hlog (le_of_lt hdenpos))
  have hcard' :
    (((completedLFunction_local_zero_support_finite χ hχ c (4 * (1 - σ))).toFinset.card : ℕ) : ℝ) ≤
      completedZeroMultiplicityCountInRectangle χ hχ z w :=
    hcard
  simpa only [C] using hcard'.trans hJ''

/--
Inputs: a nontrivial character, a completed-zero rectangle, and a positive multiplicity count.
Claim: the rectangle contains a zero and a radius-at-most-one ball where that zero lies in the
completed function's divisor support and the center is nonzero.
Content: select a counted zero, move the center to a nearby nonzero point, and identify zero-set
membership with divisor support.
Proof: combine the positive-count extraction with the isolated-zero and support lemmas above.
Role: supplies the geometric and support hypotheses to the local Turán derivative estimate.
-/
theorem exists_completedZeroCount_local_support_of_pos {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {σ T : ℝ} (hσ : σ ≤ 1) (hT : 0 ≤ T)
    (hcount : 0 < PseudoPrime.AnalyticNumberTheory.DirichletLFunction.completedZeroCount χ hχ σ T) :
    ∃ ρ : ℂ,
      σ ≤ ρ.re ∧
        ρ.re ≤ 1 ∧
        -T ≤ ρ.im ∧
        ρ.im ≤ T ∧
        DirichletCharacter.completedLFunction χ ρ = 0 ∧
        ∃ c : ℂ,
          ∃ R : ℝ,
            0 < R ∧
              R ≤ 1 ∧
              DirichletCharacter.completedLFunction χ c ≠ 0 ∧
              ρ ∈
                (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
                    (Metric.ball c |R|)).support := by
  obtain ⟨ρ, hregion⟩ :=
    PseudoPrime.AnalyticNumberTheory.DirichletLFunction.exists_mem_completedZeroCountRegion_of_pos χ
      hχ hσ hT hcount
  have hzero : DirichletCharacter.completedLFunction χ ρ = 0 := hregion.2.2.2.2
  obtain ⟨c, R, hR, hRle, hc, hball⟩ :=
    exists_completedLFunction_nonzero_center_ball_of_zero χ hχ hzero
  have hballAbs : ρ ∈ Metric.ball c |R| := by simpa only [abs_of_pos hR] using hball
  have hsupport := completedLFunction_zero_mem_local_divisor_support χ hχ hballAbs hzero
  exact
    ⟨ρ, hregion.1, hregion.2.1, hregion.2.2.1, hregion.2.2.2.1, hzero, c, R, hR, hRle, hc, hsupport⟩

/--
Inputs: a nontrivial character, a positive completed-zero count, and a counted region with
`3/4 ≤ σ ≤ 1`.
Claim: a counted zero has an explicit nonzero center `c` with `re c = 2 - σ`, and belongs to
the divisor support on the ball of radius `4(1 - σ)`.
Content: the center is in the half-plane of completed `L` nonvanishing, and the radius is fixed
by the zero-counting threshold rather than selected from an arbitrary neighborhood.
Proof: extract a zero, apply the explicit-center construction, and identify zero membership
with local divisor support.
Role: supplies controlled geometric data for uniform local zero estimates near `Re s = 1`.
-/
theorem exists_completedZeroCount_explicit_local_support_of_pos {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {σ T : ℝ} (hσlower : (3 / 4 : ℝ) ≤ σ)
    (hσupper : σ ≤ 1) (hT : 0 ≤ T)
    (hcount : 0 < PseudoPrime.AnalyticNumberTheory.DirichletLFunction.completedZeroCount χ hχ σ T) :
    ∃ ρ : ℂ,
      σ ≤ ρ.re ∧
        ρ.re ≤ 1 ∧
        -T ≤ ρ.im ∧
        ρ.im ≤ T ∧
        DirichletCharacter.completedLFunction χ ρ = 0 ∧
        ∃ c : ℂ,
          ∃ R : ℝ,
            R = 4 * (1 - σ) ∧
              0 < R ∧
              R ≤ 1 ∧
              c.re = 2 - σ ∧
              c.im = ρ.im ∧
              DirichletCharacter.completedLFunction χ c ≠ 0 ∧
              ρ ∈
                (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
                    (Metric.ball c |R|)).support := by
  obtain ⟨ρ, hregion⟩ :=
    PseudoPrime.AnalyticNumberTheory.DirichletLFunction.exists_mem_completedZeroCountRegion_of_pos χ
      hχ hσupper hT hcount
  have hzero : DirichletCharacter.completedLFunction χ ρ = 0 := hregion.2.2.2.2
  obtain ⟨c, R, hRdef, hR, hRle, hcre, hcim, hc, hball⟩ :=
    exists_completedLFunction_explicit_center_ball_of_zero χ hχ hσlower hregion.1 hzero
  have hballAbs : ρ ∈ Metric.ball c |R| := by simpa only [abs_of_pos hR] using hball
  have hsupport := completedLFunction_zero_mem_local_divisor_support χ hχ hballAbs hzero
  exact
    ⟨ρ, hregion.1, hregion.2.1, hregion.2.2.1, hregion.2.2.2.1, hzero, c, R, hRdef, hR, hRle, hcre,
      hcim, hc, hsupport⟩

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity
