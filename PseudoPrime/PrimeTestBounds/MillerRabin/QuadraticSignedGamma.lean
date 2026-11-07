/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.GammaReflectedResolventComparison
public import PseudoPrime.AnalyticNumberTheory.Gamma.EvenResolventCertificate
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaSignedEulerIdentity
public import Mathlib.Tactic.LinearCombination
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticTripleEuler
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticTripleMain

/-! # Signed Gamma bounds retaining the actual Euler series -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- An even character has signed Gamma cost at most minus 159/100. Identify
its Gamma factor with the real Gamma factor and use the certified finite
resolvent correction. This retains the sharper constant in formula (G). -/
theorem even_gamma_cost_le {m : ℕ} (χ : DirichletCharacter ℂ m) (he : χ.Even) :
    LLS.PaperStatements.gammaSignedGammaCost χ.gammaFactor ≤ (-159 / 100 : ℝ) := by
  have hf : χ.gammaFactor = Complex.Gammaℝ := funext he.gammaFactor_def
  rw [hf]
  exact AnalyticNumberTheory.Gamma.gammaResolvent_even_correction_le

/-- Under GRH, an even primitive nonprincipal character at level at least
20000 has its actual Gamma sum bounded by the conductor term, the sharp
negative Gamma correction, its signed Euler series, and reflected errors.
Use the exact zero-mass identity before applying the even correction;
retaining the Euler series permits simultaneous three-character savings. -/
theorem even_gamma_sum_signed_le {m : ℕ} [NeZero m] (hm : 20000 ≤ m) (χ : DirichletCharacter ℂ m)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (he : χ.Even)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 2 ≤ x) :
    (∑' k : ℕ, LLS.PaperStatements.gammaMellinKernel.summand χ x k).re ≤
      (11783423 / 25000000 : ℝ) * Real.log m - 159 / 100 +
        (∑' k : ℕ, -(χ k).re * Analysis.gammaResolventMangoldtWeight k) +
        ((7 / 6 : ℝ) * Real.log m + 4) / Real.sqrt x +
        (35 / 2 : ℝ) * x ^ (-9 / 16 : ℝ) +
        1 / (x * Real.sqrt x) := by
  have hm3 : 3 ≤ m := (by decide : 3 ≤ 20000).trans hm
  have hm2 : 2 ≤ m := (by decide : 2 ≤ 20000).trans hm
  have hsum :=
    LLS.PaperStatements.gamma_sum_le_reflected_resolvent hm hm3 (le_refl m) hGRH hp hne
      (inv_ne_one.mpr hne) hx
  have hmass :=
    AnalyticNumberTheory.DirichletLFunction.gammaMass_eq_signedEuler_RH hm2 (hGRH m χ hp) hp hne
      (inv_ne_one.mpr hne)
  have hcost := even_gamma_cost_le χ he
  change
    (AnalyticNumberTheory.Gamma.gammaResolventCoefficients.map
          (fun ab ↦
            (ab.2 : ℝ) * (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re)).sum ≤
      (-159 / 100 : ℝ) at hcost
  rw [hmass] at hsum
  linarith only [hsum, hcost]

/-- Three even primitive nonprincipal characters with logarithmic level
sum twice L have a combined Gamma bound with correction minus 477/100.
Retain the three signed Euler series and sum the reflected remainders.
The exact log identity combines the pole costs. This is the analytic
three-character input to formula (G) before applying the coupled Euler bound. -/
theorem three_even_gamma_signed_le {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r)
    (hp : 20000 ≤ p) (hq : 20000 ≤ q) (hr : 20000 ≤ r) (ha : a.IsPrimitive) (hb : b.IsPrimitive)
    (hc : c.IsPrimitive) (hna : a ≠ 1) (hnb : b ≠ 1) (hnc : c ≠ 1) (hea : a.Even) (heb : b.Even)
    (hec : c.Even) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x L : ℝ}
    (hx : 2 ≤ x) (hlogs : Real.log p + Real.log q + Real.log r = 2 * L) :
    (∑' k : ℕ, LLS.PaperStatements.gammaMellinKernel.summand a x k).re +
        (∑' k : ℕ, LLS.PaperStatements.gammaMellinKernel.summand b x k).re +
        (∑' k : ℕ, LLS.PaperStatements.gammaMellinKernel.summand c x k).re ≤
      2 * (11783423 / 25000000 : ℝ) * L - 477 / 100 +
        ((∑' k : ℕ, -(a k).re * Analysis.gammaResolventMangoldtWeight k) +
          (∑' k : ℕ, -(b k).re * Analysis.gammaResolventMangoldtWeight k) +
          (∑' k : ℕ, -(c k).re * Analysis.gammaResolventMangoldtWeight k)) +
        ((7 / 3 : ℝ) * L + 12) / Real.sqrt x +
        (105 / 2 : ℝ) * x ^ (-9 / 16 : ℝ) +
        3 / (x * Real.sqrt x) := by
  have hA := even_gamma_sum_signed_le hp a ha hna hea hGRH hx
  have hB := even_gamma_sum_signed_le hq b hb hnb heb hGRH hx
  have hC := even_gamma_sum_signed_le hr c hc hnc hec hGRH hx
  linear_combination hA + hB + hC + ((11783423 / 25000000 : ℝ) + (7 / 6 : ℝ) / Real.sqrt x) * hlogs

/-- Three even primitive nonprincipal characters with the exact conductor
log sum and common small-prime triviality have a combined Gamma bound with
one Euler mass and four prefix masses saved. Sum the reflected analytic
bounds, use convergence to combine the signed Euler series, and apply the
simultaneous prefix estimate. This supplies the analytic side of formula (G). -/
theorem three_even_gamma_coupled_le {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r)
    (hp : 20000 ≤ p) (hq : 20000 ≤ q) (hr : 20000 ≤ r) (ha : a.IsPrimitive) (hb : b.IsPrimitive)
    (hc : c.IsPrimitive) (hna : a ≠ 1) (hnb : b ≠ 1) (hnc : c ≠ 1) (hea : a.Even) (heb : b.Even)
    (hec : c.Even) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x L : ℝ}
    (hx : 2 ≤ x) (hlogs : Real.log p + Real.log q + Real.log r = 2 * L) {X : ℝ} (s : Finset ℕ)
    (hS : ∀ k ∈ s, (k : ℝ) ≤ X) (ht : ∀ k ∉ s, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → a l = 1) (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → c l = 1) :
    (∑' k : ℕ, LLS.PaperStatements.gammaMellinKernel.summand a x k).re +
        (∑' k : ℕ, LLS.PaperStatements.gammaMellinKernel.summand b x k).re +
        (∑' k : ℕ, LLS.PaperStatements.gammaMellinKernel.summand c x k).re ≤
      2 * (11783423 / 25000000 : ℝ) * L - 477 / 100 +
        ((∑' k : ℕ, Analysis.gammaResolventMangoldtWeight k) -
          4 * ∑ k ∈ s, Analysis.gammaResolventMangoldtWeight k) +
        ((7 / 3 : ℝ) * L + 12) / Real.sqrt x +
        (105 / 2 : ℝ) * x ^ (-9 / 16 : ℝ) +
        3 / (x * Real.sqrt x) := by
  have hu :=
    three_even_gamma_signed_le a b c hp hq hr ha hb hc hna hnb hnc hea heb hec hGRH hx hlogs
  have hsA :=
    Analysis.summable_gamma_signed_euler (fun k ↦ (a k).re)
      (fun k ↦ (Complex.abs_re_le_norm (a k)).trans (a.norm_le_one k))
  have hsB :=
    Analysis.summable_gamma_signed_euler (fun k ↦ (b k).re)
      (fun k ↦ (Complex.abs_re_le_norm (b k)).trans (b.norm_le_one k))
  have hsC :=
    Analysis.summable_gamma_signed_euler (fun k ↦ (c k).re)
      (fun k ↦ (Complex.abs_re_le_norm (c k)).trans (c.norm_le_one k))
  have hE := gamma_three_prime_one_prefix_le a b c s hS ht hA hB hC
  rw [(hsA.add hsB).tsum_add hsC, hsA.tsum_add hsB] at hE
  linarith only [hu, hE]

/-- Three even primitive nonprincipal quadratic characters satisfy the
finite-scale Gamma gap inequality when their conductor logs sum to twice L,
their simultaneous sign sum is at least minus one, and all small primes
have value one. Combine the actual main-sum lower bound with the coupled
Euler upper bound, preserving all reflected errors. This is formula (G)
before supplying the MR arithmetic and numerical certificates. -/
theorem three_even_gamma_gap_le {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r)
    (hp : 20000 ≤ p) (hq : 20000 ≤ q) (hr : 20000 ≤ r) (hqa : a.IsQuadratic) (hqb : b.IsQuadratic)
    (hqc : c.IsQuadratic) (ha : a.IsPrimitive) (hb : b.IsPrimitive) (hc : c.IsPrimitive)
    (hna : a ≠ 1) (hnb : b ≠ 1) (hnc : c ≠ 1) (hea : a.Even) (heb : b.Even) (hec : c.Even)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x L : ℝ} (hx : 2 ≤ x)
    (hlogs : Real.log p + Real.log q + Real.log r = 2 * L) {X : ℝ} (s : Finset ℕ)
    (hS : ∀ k ∈ s, (k : ℝ) ≤ X) (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → a l = 1) (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → c l = 1) :
    4 * (∑ k ∈ s, Real.exp (-(k : ℝ) / x) * ArithmeticFunction.vonMangoldt k / Real.sqrt x) ≤
      (∑' k : ℕ, Real.exp (-(k : ℝ) / x) * ArithmeticFunction.vonMangoldt k / Real.sqrt x) +
            2 * (11783423 / 25000000 : ℝ) * L -
          477 / 100 +
        ((∑' k : ℕ, Analysis.gammaResolventMangoldtWeight k) -
          4 * ∑ k ∈ s, Analysis.gammaResolventMangoldtWeight k) +
        ((7 / 3 : ℝ) * L + 12) / Real.sqrt x +
        (105 / 2 : ℝ) * x ^ (-9 / 16 : ℝ) +
        3 / (x * Real.sqrt x) := by
  have hu :=
    three_even_gamma_coupled_le a b c hp hq hr ha hb hc hna hnb hnc hea heb hec hGRH hx hlogs s hS
      (fun k _ ↦ ht k) hA hB hC
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 2) hx
  have hl := gamma_three_main_split_le a b c hqa hqb hqc hx0 s hS ht hA hB hC
  linarith only [hu, hl]

end PseudoPrime.PrimeTestBounds.MillerRabin
