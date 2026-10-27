/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.EulerTailLargeSieve
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.LocalZeroConsecutive

/-! # High-prime detector transfer at general conductor-height scales -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity

/-- For positive shift at most one, bounded orders, and a requested order absorbing
the scaled logarithmic lower cutoff, one common Euler truncation retains one eighth
of each derivative signal on primes above `R^6`. The requested order controls the
low-prime loss directly, without bounding `η log R` by an absolute constant.
The prime-power error uses the independent small-shift budget. This supplies the
common support for general-scale hybrid incidence. -/
theorem exists_uniform_high_prime_signal_cutoff_of_order_budget (η D : ℝ)
    (Krequested Kmax nmax R : ℕ) (hη : 0 < η) (hηsmall : η ≤ 1) (hD : 0 ≤ D) (hR : 2 ≤ R)
    (hDrequested : D + 5 ≤ 5 * ((Krequested - 1 : ℕ) : ℝ))
    (hRbudget : 6 * η * Real.log (R : ℝ) ≤ Real.exp (-(D + 6)) * ((Krequested - 1 : ℕ) : ℝ))
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
  have hnmin : Krequested - 1 ≤ n := Nat.sub_le_iff_le_add.mpr (hKreq.trans hKorder)
  have hnreal : ((Krequested - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnmin
  have hscale : η * Real.log ((R ^ 6 : ℕ) : ℝ) ≤ Real.exp (-(D + 6)) * (n : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    nlinarith only [hRbudget, hnreal, Real.exp_pos (-(D + 6))]
  exact
    finite_high_prime_sum_norm_ge_of_detector_signal χ (R ^ 6) cutoff n K
      (hR.trans (Nat.le_self_pow (by decide) R)) hcutoff hη hηsmall hD (Real.exp_pos _).le hKorder
      (detector_order_exponential_margin Krequested n K D hD hDrequested hnmin hKorder) hscale
      (low_prime_exponential_budget D) hηratio (hm.trans (hKreq.trans hKorder)) s hs
      (hsignal n hn K hKmax χ hs hdet)

/-- Under the general-scale order budget and the prime-energy monotonicity budget,
one shared high-prime support retains the weakest signal on a physical height window.
Transfer the derivative signal and apply the normalized variation bound.
The radius is proportional to the shift and is independent of the mesh density,
so the result can feed multiplicity-preserving incidence estimates. -/
theorem exists_uniform_high_prime_signal_physical_window_of_order_budget (η D : ℝ)
    (Krequested Kmax nmax R : ℕ) (hη : 0 < η) (hηsmall : η ≤ 1) (hD : 0 ≤ D) (hR : 2 ≤ R)
    (hDrequested : D + 5 ≤ 5 * ((Krequested - 1 : ℕ) : ℝ))
    (hRbudget : 6 * η * Real.log (R : ℝ) ≤ Real.exp (-(D + 6)) * ((Krequested - 1 : ℕ) : ℝ))
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
    exists_uniform_high_prime_signal_cutoff_of_order_budget η D Krequested Kmax nmax R hη hηsmall hD
      hR hDrequested hRbudget hηratio hm
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

/-- One absolute gamma constant works for every primitive completed zero satisfying
the explicit cap budgets. A shared cap and conductor scale yield one common high-prime
support, an order between three and four times the cap, and a positive signal on a
physical height window. Apply the consecutive-moment detector, weaken its explicit
signal to an exponential, and transfer it using the general-scale order budget.
This connects actual zeros to the common support used in hybrid incidence. -/
theorem exists_uniform_completed_zero_high_prime_window_of_cap :
    ∃ G : ℝ,
      0 ≤ G ∧
        ∀ (η : ℝ) (R N : ℕ),
          0 < η →
            η ≤ 1 / 1288 →
            2 ≤ R →
            4 ≤ N →
            Real.log 414720 + 5 ≤ 5 * ((N - 1 : ℕ) : ℝ) →
            6 * η * Real.log (R : ℝ) ≤ Real.exp (-(Real.log 414720 + 6)) * ((N - 1 : ℕ) : ℝ) →
            4 * η ≤ Real.exp (-(Real.log 414720 + 5)) →
            Nat.ceil (Real.log higherPrimePowerEulerMajorantConstant) ≤ N →
            ((2 * (4 * N) + 1 : ℕ) : ℝ) ≤ 6 * Real.log (R : ℝ) →
            ∃ cutoff : ℕ,
              R ^ 6 ≤ cutoff ∧
                1 ≤ cutoff ∧
                η * Real.log ((cutoff : ℝ) + 1) ≤
                  2 * ((4 * N : ℕ) + Real.log 414720 * N + Real.log (24 * (Real.log 4 + 4))) +
                    η * Real.log ((R ^ 6 : ℕ) : ℝ) +
                    η * Real.log 3 ∧
                ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q},
                  2 ≤ q →
                    χ ≠ 1 →
                    χ.IsPrimitive →
                    χ⁻¹ ≠ 1 →
                    ∀ {ρ : ℂ},
                      |ρ.re - 1| ≤ η →
                        χ.completedLFunction ρ = 0 →
                        χ.completedLFunction (((1 + η : ℝ) : ℂ) + (ρ.im : ℂ) * Complex.I) ≠ 0 →
                        Nat.ceil
                            (completedZeroLocalLogBoundConstant *
                              (1 + 644 * η * Real.log ((q : ℝ) * (|ρ.im| + 3)))) ≤
                          N →
                        completedGenusScaledMassUpperBound q η ρ.im ≤ N →
                        η * G * (Real.log (4 * |ρ.im| + 4) + 1) ≤ N →
                        ∃ n : ℕ,
                          3 * N ≤ n ∧
                            n + 1 ≤ 4 * N ∧
                            ∀ u : ℝ,
                              |u - ρ.im| ≤
                                  η * Real.exp (-(Real.log 414720 * N)) /
                                    (16 * primeLogPowerVariationBound (4 * N)) →
                                Real.exp (-(Real.log 414720 * N)) / 16 ≤
                                  η ^ (n + 1) / (n.factorial : ℝ) *
                                    ‖primeLogPowerPolynomial (highPrimeEulerSupport R cutoff) n
                                        (1 + η) (fun k ↦ χ (k : ZMod q)) u‖ := by
  obtain ⟨G, hG, hdetector⟩ := exists_ordinary_LFunction_linear_order_detector_of_cap
  refine ⟨G, hG, ?_⟩
  intro η R N hη hηsmall hR hN hDrequested hRbudget hηratio hm hlarge
  have hηone : η ≤ 1 := by linarith only [hηsmall]
  have hD : 0 ≤ Real.log 414720 := Real.log_nonneg (by norm_num only)
  obtain ⟨cutoff, hcutoff, hpos, hlog, hwindow⟩ :=
    exists_uniform_high_prime_signal_physical_window_of_order_budget η (Real.log 414720) N N (4 * N)
      R hη hηone hD hR hDrequested hRbudget hηratio hm hlarge
  refine ⟨cutoff, hcutoff, hpos, hlog, ?_⟩
  intro q hq χ hqtwo hχ hp hinv ρ hρre hzero hc hlocal hmass hgamma
  have hcre : ((((1 + η : ℝ) : ℂ) + (ρ.im : ℂ) * Complex.I).re) = 1 + η := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      zero_mul, mul_zero, sub_zero, add_zero]
  have hcim : ((((1 + η : ℝ) : ℂ) + (ρ.im : ℂ) * Complex.I).im) = ρ.im := by
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      Complex.I_re, mul_one, zero_mul, add_zero, zero_add]
  obtain ⟨n, hnlow, hnupper, hsignal⟩ :=
    hdetector hqtwo hχ hp hinv hη hηsmall hcre hcim hρre hzero hc N hN hlocal hmass hgamma
  have hNpos : 1 ≤ N := (by norm_num only : 1 ≤ 4).trans hN
  have hsignal' := (linear_cap_signal_ge_exp_neg N (n + 1) hNpos hnupper).trans hsignal
  have hnmax : n ≤ 4 * N := (Nat.le_succ n).trans hnupper
  have hNorder : N ≤ n + 1 :=
    (Nat.le_mul_of_pos_left N (by decide : 0 < 3)).trans (hnlow.trans (Nat.le_succ n))
  exact ⟨n, hnlow, hnupper, hwindow n hnmax N (le_refl N) (le_refl N) hNorder χ ρ.im hsignal'⟩

/-- For a cap coefficient, exponential detector constant, and fixed minimum order,
an absolute linear enlargement of any scale at least one meets the multiplicity cap,
the exponential order margin, the scaled low-prime budget, and the minimum order.
Take a ceiling above the maximum of the required absolute coefficients.
This keeps the common detector order linear in the conductor-height scale. -/
theorem exists_general_scale_order_cap (C D : ℝ) (m : ℕ) :
    ∃ B : ℝ,
      0 < B ∧
        ∀ L S : ℝ,
          1 ≤ L →
            S ≤ L →
            ∃ N : ℕ,
              4 ≤ N ∧
                Nat.ceil (C * L) ≤ N ∧
                (N : ℝ) ≤ B * L ∧
                D + 5 ≤ 5 * ((N - 1 : ℕ) : ℝ) ∧
                6 * S ≤ Real.exp (-(D + 6)) * ((N - 1 : ℕ) : ℝ) ∧ m ≤ N := by
  let b := max 4 (max C (max ((D + 5) / 5) (max (m : ℝ) (6 * Real.exp (D + 6)))))
  have hb4 : 4 ≤ b := le_max_left _ _
  have hbC : C ≤ b := (le_max_left _ _).trans (le_max_right _ _)
  have hbd : (D + 5) / 5 ≤ b :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hbm : (m : ℝ) ≤ b :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hbe : 6 * Real.exp (D + 6) ≤ b :=
    (le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hb : 0 ≤ b := (by norm_num only : (0 : ℝ) ≤ 4).trans hb4
  refine ⟨b + 2, by linarith only [hb4], ?_⟩
  intro L S hL hSL
  let N := Nat.ceil (b * L) + 1
  have hLpos : 0 ≤ L := (by norm_num only : (0 : ℝ) ≤ 1).trans hL
  have hbL : b ≤ b * L := le_mul_of_one_le_right hb hL
  have hceil : b * L ≤ ((N - 1 : ℕ) : ℝ) := by
    simpa only [N, Nat.add_sub_cancel] using Nat.le_ceil (b * L)
  have hNcast : ((N - 1 : ℕ) : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr (Nat.sub_le N 1)
  have hNfour : 4 ≤ N := by exact_mod_cast (hb4.trans (hbL.trans (hceil.trans hNcast)))
  have hNC : Nat.ceil (C * L) ≤ N :=
    (Nat.ceil_mono (mul_le_mul_of_nonneg_right hbC hLpos)).trans (Nat.le_add_right _ 1)
  have hNupper : (N : ℝ) ≤ (b + 2) * L := by
    have hceilupper := Nat.ceil_lt_add_one (mul_nonneg hb hLpos)
    dsimp only [N]
    push_cast
    linarith only [hceilupper, hL]
  have hmargin : D + 5 ≤ 5 * ((N - 1 : ℕ) : ℝ) := by linarith only [hbd, hbL, hceil]
  have hexpcancel : Real.exp (-(D + 6)) * Real.exp (D + 6) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hscaledL :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hbe hLpos) (Real.exp_nonneg (-(D + 6)))
  have hscaledceil := mul_le_mul_of_nonneg_left hceil (Real.exp_nonneg (-(D + 6)))
  have hbudget : 6 * S ≤ Real.exp (-(D + 6)) * ((N - 1 : ℕ) : ℝ) := by
    have hcancelL : Real.exp (-(D + 6)) * (6 * Real.exp (D + 6) * L) = 6 * L := by
      calc
        _ = 6 * (Real.exp (-(D + 6)) * Real.exp (D + 6)) * L := by ring
        _ = 6 * L := by rw [hexpcancel, mul_one]
    rw [hcancelL] at hscaledL
    exact
      (mul_le_mul_of_nonneg_left hSL (by norm_num only : (0 : ℝ) ≤ 6)).trans
        (hscaledL.trans hscaledceil)
  have hm : m ≤ N := by exact_mod_cast (hbm.trans (hbL.trans (hceil.trans hNcast)))
  exact ⟨N, hNfour, hNC, hNupper, hmargin, hbudget, hm⟩

/-- A nonnegative gamma constant admits a shared cap linear in
`1+η log(R(R+3))` for all conductors and heights bounded by `R`.
The cap controls local multiplicity, scaled genus mass, gamma growth, low-prime
removal, and prime-power minimum order. Enlarge the existing detector cap and
compare each conductor-height logarithm with the common logarithm.
This discharges all cap assumptions uniformly over the zero family. -/
theorem exists_uniform_general_scale_detector_cap (G : ℝ) (hG : 0 ≤ G) :
    ∃ B : ℝ,
      0 < B ∧
        ∀ (η : ℝ) (R : ℕ),
          0 < η →
            η ≤ 1 →
            2 ≤ R →
            ∃ N : ℕ,
              4 ≤ N ∧
                (N : ℝ) ≤ B * (1 + η * Real.log ((R : ℝ) * ((R : ℝ) + 3))) ∧
                Real.log 414720 + 5 ≤ 5 * ((N - 1 : ℕ) : ℝ) ∧
                6 * η * Real.log (R : ℝ) ≤ Real.exp (-(Real.log 414720 + 6)) * ((N - 1 : ℕ) : ℝ) ∧
                Nat.ceil (Real.log higherPrimePowerEulerMajorantConstant) ≤ N ∧
                ∀ (q : ℕ),
                  2 ≤ q →
                    q ≤ R →
                    ∀ t : ℝ,
                      |t| ≤ R →
                        Nat.ceil
                              (completedZeroLocalLogBoundConstant *
                                (1 + 644 * η * Real.log ((q : ℝ) * (|t| + 3)))) ≤
                            N ∧
                          completedGenusScaledMassUpperBound q η t ≤ N ∧
                          η * G * (Real.log (4 * |t| + 4) + 1) ≤ N := by
  let C := linearOrderDetectorCapCoefficient G
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num only)
  have hC : 0 ≤ C := by
    dsimp only [C, linearOrderDetectorCapCoefficient]
    have hBterm := mul_nonneg completedGenusMassCenterConstant_pos.le (add_nonneg hlog4 zero_le_one)
    have hGterm := mul_nonneg hG (add_nonneg hlog4 (by norm_num only : (0 : ℝ) ≤ 2))
    linarith only [completedZeroLocalLogBoundConstant_pos, completedGenusMassShiftConstant_pos,
      hBterm, hGterm]
  obtain ⟨B, hB, hcap⟩ :=
    exists_general_scale_order_cap C (Real.log 414720)
      (Nat.ceil (Real.log higherPrimePowerEulerMajorantConstant))
  refine ⟨B, hB, ?_⟩
  intro η R hη hηone hR
  have hRreal : (2 : ℝ) ≤ R := by exact_mod_cast hR
  have hRpos : (0 : ℝ) < R := lt_of_lt_of_le (by norm_num only) hRreal
  have hXlog : 0 ≤ Real.log ((R : ℝ) * ((R : ℝ) + 3)) :=
    Real.log_nonneg (by nlinarith only [hRreal])
  have hlogR : Real.log (R : ℝ) ≤ Real.log ((R : ℝ) * ((R : ℝ) + 3)) :=
    Real.log_le_log hRpos (by nlinarith only [hRreal])
  have hL : 1 ≤ 1 + η * Real.log ((R : ℝ) * ((R : ℝ) + 3)) :=
    le_add_of_nonneg_right (mul_nonneg hη.le hXlog)
  have hSL : η * Real.log (R : ℝ) ≤ 1 + η * Real.log ((R : ℝ) * ((R : ℝ) + 3)) := by
    linarith only [mul_le_mul_of_nonneg_left hlogR hη.le]
  obtain ⟨N, hN, hNC, hNupper, hmargin, hbudget, hm⟩ :=
    hcap (1 + η * Real.log ((R : ℝ) * ((R : ℝ) + 3))) (η * Real.log (R : ℝ)) hL hSL
  refine ⟨N, hN, hNupper, hmargin, ?_, hm, ?_⟩
  · simpa only [mul_assoc] using hbudget
  · intro q hq hqR t ht
    have hqpos : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hq)
    have hqreal : (q : ℝ) ≤ R := by exact_mod_cast hqR
    have harg : (q : ℝ) * (|t| + 3) ≤ (R : ℝ) * ((R : ℝ) + 3) :=
      mul_le_mul hqreal (by linarith only [ht]) (by linarith only [abs_nonneg t])
        (by linarith only [hRreal])
    have htpos : 0 < |t| + 3 := by linarith only [abs_nonneg t]
    have hlog := Real.log_le_log (mul_pos hqpos htpos) harg
    have hlocalcap : Nat.ceil (C * (1 + η * Real.log ((q : ℝ) * (|t| + 3)))) ≤ N :=
      (Nat.ceil_mono
            (mul_le_mul_of_nonneg_left (add_le_add_right (mul_le_mul_of_nonneg_left hlog hη.le) 1)
              hC)).trans
        hNC
    obtain ⟨_, hlocal, hmass, hgamma, _⟩ :=
      linear_order_detector_numeric_caps q hq η t G hη hηone hG
    exact
      ⟨hlocal.trans hlocalcap, hmass.trans (Nat.cast_le.mpr hlocalcap),
        hgamma.trans (Nat.cast_le.mpr hlocalcap)⟩

/-- For a positive linear cap coefficient, choose a fixed positive shift threshold
and a fixed minimum conductor scale. Every cap below the linear scale then satisfies
the prime-energy monotonicity condition, uniformly over smaller shifts. Compare the
common conductor-height logarithm with three times the conductor logarithm and use
logarithmic divergence. The threshold also meets the detector and prime-power budgets.
This removes the remaining size conditions from the physical-window transfer. -/
theorem eventually_general_scale_prime_energy_budget (B : ℝ) (hB : 0 < B) :
    ∃ η₀ : ℝ,
      0 < η₀ ∧
        η₀ ≤ 1 / 1288 ∧
        4 * η₀ ≤ Real.exp (-(Real.log 414720 + 5)) ∧
        ∃ R₀ : ℕ,
          3 ≤ R₀ ∧
            ∀ R : ℕ,
              R₀ ≤ R →
                ∀ η : ℝ,
                  0 ≤ η →
                    η ≤ η₀ →
                    ∀ N : ℕ,
                      (N : ℝ) ≤ B * (1 + η * Real.log ((R : ℝ) * ((R : ℝ) + 3))) →
                        ((2 * (4 * N) + 1 : ℕ) : ℝ) ≤ 6 * Real.log (R : ℝ) := by
  let η₀ := min (1 / 1288 : ℝ) (min (Real.exp (-(Real.log 414720 + 5)) / 4) (1 / (8 * B)))
  have hη₀ : 0 < η₀ :=
    lt_min (by norm_num only)
      (lt_min (div_pos (Real.exp_pos _) (by norm_num only))
        (div_pos zero_lt_one (mul_pos (by norm_num only) hB)))
  have hsmall : η₀ ≤ 1 / 1288 := min_le_left _ _
  have hratio : 4 * η₀ ≤ Real.exp (-(Real.log 414720 + 5)) := by
    have h : η₀ ≤ Real.exp (-(Real.log 414720 + 5)) / 4 :=
      (min_le_right _ _).trans (min_le_left _ _)
    linarith only [h]
  have hηB : η₀ ≤ 1 / (8 * B) := (min_le_right _ _).trans (min_le_right _ _)
  have hlog : Filter.Tendsto (fun R : ℕ ↦ Real.log (R : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨R₁, hR₁⟩ :=
    Filter.eventually_atTop.mp (hlog.eventually (Filter.eventually_ge_atTop (8 * B + 1)))
  refine ⟨η₀, hη₀, hsmall, hratio, max 3 R₁, le_max_left _ _, ?_⟩
  intro R hR η hη hηsmall N hN
  have hRthree : 3 ≤ R := (le_max_left 3 R₁).trans hR
  have hRreal : (3 : ℝ) ≤ R := by exact_mod_cast hRthree
  have hRpos : (0 : ℝ) < R := lt_of_lt_of_le (by norm_num only) hRreal
  have hlarge : 8 * B + 1 ≤ Real.log (R : ℝ) := hR₁ R ((le_max_right 3 R₁).trans hR)
  have hlogpos : 0 ≤ Real.log (R : ℝ) := Real.log_nonneg (by linarith only [hRreal])
  have hRnext : (R : ℝ) + 3 ≤ (R : ℝ) ^ 2 := by nlinarith only [hRreal]
  have harg : (R : ℝ) * ((R : ℝ) + 3) ≤ (R : ℝ) ^ 3 := by
    calc
      _ ≤ (R : ℝ) * (R : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hRnext hRpos.le
      _ = _ := by ring
  have hlogX : Real.log ((R : ℝ) * ((R : ℝ) + 3)) ≤ 3 * Real.log (R : ℝ) := by
    have h := Real.log_le_log (mul_pos hRpos (by linarith only [hRreal])) harg
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hηbound : 8 * B * η ≤ 1 := by
    have h := (le_div_iff₀ (mul_pos (by norm_num only : (0 : ℝ) < 8) hB)).mp (hηsmall.trans hηB)
    linarith only [h]
  have hNbound :=
    hN.trans
      (mul_le_mul_of_nonneg_left (add_le_add_right (mul_le_mul_of_nonneg_left hlogX hη) 1) hB.le)
  have hproduct := mul_le_mul_of_nonneg_right hηbound hlogpos
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at ⊢
  nlinarith only [hNbound, hproduct, hlarge, hlogpos]

/-- There are absolute positive cap and shift constants and a minimum scale such
that every smaller positive shift and every larger conductor scale admit one common
high-prime support. For every primitive completed zero with bounded conductor and
height near the line one, an order between three and four times the shared cap gives
a positive polynomial signal throughout a common physical height window.
The cap is linear in the conductor-height scale; the support has an explicit
logarithmic bound. Discharge all numerical budgets, use right-half-plane nonvanishing,
and apply the cap-level transfer. No fixed bound on the scaled logarithm is assumed.
This supplies actual zero detectors for general-scale hybrid counting. -/
theorem exists_uniform_completed_zero_general_scale_high_prime_window :
    ∃ B η₀ : ℝ,
      0 < B ∧
        0 < η₀ ∧
        η₀ ≤ 1 / 1288 ∧
        ∃ R₀ : ℕ,
          3 ≤ R₀ ∧
            ∀ R : ℕ,
              R₀ ≤ R →
                ∀ η : ℝ,
                  0 < η →
                    η ≤ η₀ →
                    ∃ N cutoff : ℕ,
                      4 ≤ N ∧
                        (N : ℝ) ≤ B * (1 + η * Real.log ((R : ℝ) * ((R : ℝ) + 3))) ∧
                        R ^ 6 ≤ cutoff ∧
                        1 ≤ cutoff ∧
                        η * Real.log ((cutoff : ℝ) + 1) ≤
                          2 *
                              ((4 * N : ℕ) + Real.log 414720 * N +
                                Real.log (24 * (Real.log 4 + 4))) +
                            η * Real.log ((R ^ 6 : ℕ) : ℝ) +
                            η * Real.log 3 ∧
                        ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q},
                          2 ≤ q →
                            q ≤ R →
                            χ ≠ 1 →
                            χ.IsPrimitive →
                            ∀ {ρ : ℂ},
                              |ρ.im| ≤ R →
                                |ρ.re - 1| ≤ η →
                                χ.completedLFunction ρ = 0 →
                                ∃ n : ℕ,
                                  3 * N ≤ n ∧
                                    n + 1 ≤ 4 * N ∧
                                    ∀ u : ℝ,
                                      |u - ρ.im| ≤
                                          η * Real.exp (-(Real.log 414720 * N)) /
                                            (16 * primeLogPowerVariationBound (4 * N)) →
                                        Real.exp (-(Real.log 414720 * N)) / 16 ≤
                                          η ^ (n + 1) / (n.factorial : ℝ) *
                                            ‖primeLogPowerPolynomial
                                                (highPrimeEulerSupport R cutoff) n (1 + η)
                                                (fun k ↦ χ (k : ZMod q)) u‖ := by
  obtain ⟨G, hG, hwindow⟩ := exists_uniform_completed_zero_high_prime_window_of_cap
  obtain ⟨B, hB, hcap⟩ := exists_uniform_general_scale_detector_cap G hG
  obtain ⟨η₀, hη₀, hsmall, hratio, R₀, hR₀, henergy⟩ :=
    eventually_general_scale_prime_energy_budget B hB
  refine ⟨B, η₀, hB, hη₀, hsmall, R₀, hR₀, ?_⟩
  intro R hR η hη hηsmall
  have hRtwo : 2 ≤ R := (by norm_num only : 2 ≤ 3).trans (hR₀.trans hR)
  have hηdet : η ≤ 1 / 1288 := hηsmall.trans hsmall
  have hηone : η ≤ 1 := by linarith only [hηdet]
  obtain ⟨N, hN, hNupper, hmargin, hbudget, hm, hcaps⟩ := hcap η R hη hηone hRtwo
  have hηratio : 4 * η ≤ Real.exp (-(Real.log 414720 + 5)) := by linarith only [hηsmall, hratio]
  obtain ⟨cutoff, hcutoff, hpos, hlog, hzeros⟩ :=
    hwindow η R N hη hηdet hRtwo hN hmargin hbudget hηratio hm
      (henergy R hR η hη.le hηsmall N hNupper)
  refine ⟨N, cutoff, hN, hNupper, hcutoff, hpos, hlog, ?_⟩
  intro q hq χ hqtwo hqR hχ hp ρ hheight hρre hzero
  have hc : χ.completedLFunction (((1 + η : ℝ) : ℂ) + (ρ.im : ℂ) * Complex.I) ≠ 0 := by
    apply DirichletLFunction.completedLFunction_ne_zero_of_one_le_re hχ
    have hcre : ((((1 + η : ℝ) : ℂ) + (ρ.im : ℂ) * Complex.I).re) = 1 + η := by
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
        zero_mul, mul_zero, sub_zero, add_zero]
    rw [hcre]
    exact le_add_of_nonneg_right hη.le
  obtain ⟨hlocal, hmass, hgamma⟩ := hcaps q hqtwo hqR ρ.im hheight
  exact hzeros hqtwo hχ hp (fun h ↦ hχ (inv_eq_one.mp h)) hρre hzero hc hlocal hmass hgamma

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity
