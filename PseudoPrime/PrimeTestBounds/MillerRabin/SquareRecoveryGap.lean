/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.SquareRecoveryWeight
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformGammaNegative
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterGammaTailSeries
public import PseudoPrime.PrimeTestBounds.MillerRabin.UniformKorseltFactors

/-! # Square recovery in the three-character contour comparison -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- On the first extension interval the principal six-pole mass at square
indices above the cutoff exceeds 0.021, before its multiplicity of four. -/
theorem square_principal_sum_lower {r : ℝ} (hr : 465 / 2 ≤ r) (hr' : r ≤ 278) :
    21 / 1000 <
      ∑ k ∈ Finset.Ioc ⌊r⌋₊ ⌊Real.exp (21 / 16) * r⌋₊,
        (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) (r ^ 2) (k ^ 2)).re := by
  have h0 : 0 < r := (by norm_num only : (0 : ℝ) < 465 / 2).trans_le hr
  apply lt_of_lt_of_eq (squareRecovery_sum_lower hr hr')
  apply Finset.sum_congr rfl
  intro k hk
  obtain ⟨hl, hh⟩ := Finset.mem_Ioc.mp hk
  have hk0 := h0.trans (Nat.lt_of_floor_lt hl)
  rw [refined_square_principal_eq (pow_pos h0 2) (Nat.cast_pos.mp hk0),
    squareRootWeight_eq_scaled h0 hk0
      ((Nat.le_floor_iff (mul_nonneg (Real.exp_pos _).le h0.le)).mp hh),
    mul_comm]

/-- For three prime-trivial characters of trace at least minus one, including
squares raises the principal deficit by strictly more than 0.084 throughout
the full first extension interval. -/
theorem square_principal_deficit_lt {p q m : ℕ} [NeZero p] [NeZero q] [NeZero m]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ m) {r : ℝ}
    (hr : 465 / 2 ≤ r) (hr' : r ≤ 278) (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → a l = 1)
    (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → c l = 1) :
    let X := r ^ 2
    4 *
            (∑ k ∈ Finset.Ioc 0 ⌊X⌋₊,
              (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X k).re) -
          (∑' k : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X k).re +
        21 / 250 <
      (∑' k : ℕ, refinedSixPoleKernel.summand a X k).re +
        (∑' k : ℕ, refinedSixPoleKernel.summand b X k).re +
        (∑' k : ℕ, refinedSixPoleKernel.summand c X k).re := by
  have h0 : 0 < r := (by norm_num only : (0 : ℝ) < 465 / 2).trans_le hr
  have h :=
    refined_prefix_add_squares a b c (pow_pos h0 2) _ (fun k hk ↦ refined_square_window hr hk) ht hA
      hB hC
  dsimp only at h ⊢
  linarith only [h, square_principal_sum_lower hr hr']

/-- Include the reflected Euler prefix and the closed zero-tail estimate in the
square-enhanced deficit bound at square scale in the first extension interval. -/
theorem square_dual_prefix {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) (hP : 2 ≤ p) (hQ : 2 ≤ q) (hR : 2 ≤ r)
    (hpA : a.IsPrimitive) (hpB : b.IsPrimitive) (hpC : c.IsPrimitive) (hnA : a ≠ 1) (hnB : b ≠ 1)
    (hnC : c ≠ 1) (hiA : a⁻¹ ≠ 1) (hiB : b⁻¹ ≠ 1) (hiC : c⁻¹ ≠ 1) (heA : a.Even) (heB : b.Even)
    (heC : c.Even) {X R : ℝ} (hRlo : 465 / 2 ≤ R) (hRhi : R ≤ 278) (hXR : X = R ^ 2) (hX : 625 ≤ X)
    (s : Finset ℕ) (hS : ∀ k ∈ s, (k : ℝ) ≤ X) (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → a l = 1) (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → c l = 1) :
    4 *
            (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊,
              (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X n).re) -
          (∑' n : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X n).re +
        21 / 250 <
      refinedContourNonEuler a X + refinedContourNonEuler b X + refinedContourNonEuler c X +
            refinedReflectedEuler (1 : DirichletCharacter ℂ 1) X -
          4 * ∑ k ∈ s, refinedDualWeight X k +
        (3 / 16 : ℝ) * (Real.log p + Real.log q + Real.log r) +
        -(3117 / 400 : ℝ) * (27 / 25 : ℝ) ^ 5 +
        4 * quarterEulerClosedTailCap X := by
  have hp : ∀ k ∈ s, ArithmeticFunction.vonMangoldt k ≠ 0 → (a k).re + (b k).re + (c k).re = 3 := by
    intro k hk hΛ
    have h1 :=
      AnalyticNumberTheory.Arithmetic.character_eq_one_of_ambient_mangoldt (N := 1) a
        (fun l hl hlX _ ↦ hA l hl hlX) (hS k hk) (Nat.coprime_one_right k) hΛ
    have h2 :=
      AnalyticNumberTheory.Arithmetic.character_eq_one_of_ambient_mangoldt (N := 1) b
        (fun l hl hlX _ ↦ hB l hl hlX) (hS k hk) (Nat.coprime_one_right k) hΛ
    have h3 :=
      AnalyticNumberTheory.Arithmetic.character_eq_one_of_ambient_mangoldt (N := 1) c
        (fun l hl hlX _ ↦ hC l hl hlX) (hS k hk) (Nat.coprime_one_right k) hΛ
    rw [h1, h2, h3, Complex.one_re]
    norm_num only
  have hc :=
    quarter_uniform_summand_closed hGRH a b c hP hQ hR hpA hpB hpC hnA hnB hnC hiA hiB hiC heA heB
      heC hX ht hA hB hC (x := X) (by linarith only [hX])
  subst X
  have hrec := square_principal_deficit_lt a b c hRlo hRhi ht hA hB hC
  dsimp only at hrec
  have hd :=
    refined_contour_prefix a b c hpA hpB hpC hnA hnB hnC hiA hiB hiC
      (by linarith only [hX] : 0 < R ^ 2) s ht hp
  linarith only [hc, hd, hrec]

/-- The GRH upper bound for the enhanced principal deficit retains both negative
Gamma corrections and the reflected Euler prefix throughout the first interval. -/
theorem square_gamma_baseline {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) (hP : 2 ≤ p) (hQ : 2 ≤ q) (hR : 2 ≤ r)
    (hpA : a.IsPrimitive) (hpB : b.IsPrimitive) (hpC : c.IsPrimitive) (hnA : a ≠ 1) (hnB : b ≠ 1)
    (hnC : c ≠ 1) (hiA : a⁻¹ ≠ 1) (hiB : b⁻¹ ≠ 1) (hiC : c⁻¹ ≠ 1) (heA : a.Even) (heB : b.Even)
    (heC : c.Even) {X H R : ℝ} (hRlo : 465 / 2 ≤ R) (hRhi : R ≤ 278) (hXR : X = R ^ 2)
    (hX : 625 ≤ X) (hy : 12 ≤ Real.log X + 21 / 8)
    (hH : refinedReflectedEuler (1 : DirichletCharacter ℂ 1) X ≤ H) (s : Finset ℕ)
    (hS : ∀ k ∈ s, (k : ℝ) ≤ X) (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → a l = 1) (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → c l = 1) :
    4 *
            (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊,
              (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X n).re) -
          (∑' n : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X n).re +
        21 / 250 <
      (Real.log p + Real.log q + Real.log r) *
                (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8))) *
                  X ^ (-(27 / 25 : ℝ)) *
                  ((21 / 8 : ℝ) + Real.log X) ^ 5) -
              3 * quarterGammaFirstCorrection (Real.log X + 21 / 8) -
              4 * quarterGammaDensity (Real.log X + 21 / 8) +
            H -
          4 * ∑ k ∈ s, refinedDualWeight X k +
        (3 / 16 : ℝ) * (Real.log p + Real.log q + Real.log r) +
        -(3117 / 400 : ℝ) * (27 / 25 : ℝ) ^ 5 +
        4 * quarterEulerClosedTailCap X := by
  have h :=
    square_dual_prefix hGRH a b c hP hQ hR hpA hpB hpC hnA hnB hnC hiA hiB hiC heA heB heC hRlo hRhi
      hXR hX s hS ht hA hB hC
  have hx : 0 < X := by linarith only [hX]
  rw [refined_three_nonEuler_even a b c hiA hiB hiC heA heB heC X, refined_conductor_sum p q r X,
    refined_conductor_profile (by linarith only [hX]),
    refined_reflected_arch_eq_central a⁻¹ hiA (by linarith only [hX]),
    refined_right_gamma_eq_central a hx, refined_central_gamma_pair_eq a heA hx] at h
  have hg := quarter_gamma_first_baseline a heA hx hy
  linarith only [h, hg, hH]

/-- For the three pair characters of an accepted uniform triple, the closed
Gamma gap includes the square recovery of 21/250. -/
theorem square_pair_gap {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r] [Fact p.Prime]
    [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)] (hsq : Squarefree n)
    (hnprod : n = p * q * r) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hn : 1 < n) (ho : Odd n) (hp : Odd p) (hq : Odd q) (hr : Odd r) (hpn : p ∣ n) (hqn : q ∣ n)
    (hrn : r ∣ n) (hpqn : p * q ∣ n) (hprn : p * r ∣ n) (hqrn : q * r ∣ n) (hpK : p - 1 ∣ n - 1)
    (hqK : q - 1 ∣ n - 1) (hrK : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1)) {X H R : ℝ} (hRlo : 465 / 2 ≤ R)
    (hRhi : R ≤ 278) (hXR : X = R ^ 2) (hX : 625 ≤ X) (hy : 12 ≤ Real.log X + 21 / 8)
    (hH : refinedReflectedEuler (1 : DirichletCharacter ℂ 1) X ≤ H) (s : Finset ℕ)
    (hS : ∀ k ∈ s, (k : ℝ) ≤ X)
    (hpass : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → PrimeTest.StrongMillerRabinPass n (l : ZMod n)) :
    4 *
            (∑ k ∈ Finset.Ioc 0 ⌊X⌋₊,
              (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X k).re) -
          (∑' k : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X k).re +
        21 / 250 <
      (2 * Real.log n) *
                (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8))) *
                  X ^ (-(27 / 25 : ℝ)) *
                  ((21 / 8 : ℝ) + Real.log X) ^ 5) -
              3 * quarterGammaFirstCorrection (Real.log X + 21 / 8) -
              4 * quarterGammaDensity (Real.log X + 21 / 8) +
            H -
          4 * ∑ k ∈ s, refinedDualWeight X k +
        (3 / 8 : ℝ) * Real.log n +
        -(3117 / 400 : ℝ) * (27 / 25 : ℝ) ^ 5 +
        4 * quarterEulerClosedTailCap X := by
  let a := NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq)
  let b := NumberTheory.complexJacobiNumeratorCharacter (p * r) (hp.mul hr)
  let c := NumberTheory.complexJacobiNumeratorCharacter (q * r) (hq.mul hr)
  have hpq : 2 ≤ p * q :=
    (Fact.out : p.Prime).two_le.trans (Nat.le_mul_of_pos_right p (Fact.out : q.Prime).pos)
  have hpr : 2 ≤ p * r :=
    (Fact.out : p.Prime).two_le.trans (Nat.le_mul_of_pos_right p (Fact.out : r.Prime).pos)
  have hqr : 2 ≤ q * r :=
    (Fact.out : q.Prime).two_le.trans (Nat.le_mul_of_pos_right q (Fact.out : r.Prime).pos)
  have ha : a ≠ 1 := pair_character_ne_one hsq hpqn (hp.mul hq) ((by decide : 1 < 2).trans_le hpq)
  have hb : b ≠ 1 := pair_character_ne_one hsq hprn (hp.mul hr) ((by decide : 1 < 2).trans_le hpr)
  have hc : c ≠ 1 := pair_character_ne_one hsq hqrn (hq.mul hr) ((by decide : 1 < 2).trans_le hqr)
  have ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re := by
    intro k
    simpa only [Int.cast_natCast] using
      pair_character_sum_ge_neg_one (k : ℤ) p q r (hp.mul hq) (hp.mul hr) (hq.mul hr)
  have hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → a l = 1 := by
    intro l hl hlX
    exact pair_character_nat_eq_one hn ho hp hq hpn hqn hpqn hpK hqK hvq l (hpass l hl hlX)
  have hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → b l = 1 := by
    intro l hl hlX
    exact pair_character_nat_eq_one hn ho hp hr hpn hrn hprn hpK hrK hvr l (hpass l hl hlX)
  have hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → c l = 1 := by
    intro l hl hlX
    exact
      pair_character_nat_eq_one hn ho hq hr hqn hrn hqrn hqK hrK (hvr.trans hvq.symm) l
        (hpass l hl hlX)
  have h :=
    square_gamma_baseline hGRH a b c (by linarith only [hpq]) (by linarith only [hpr])
      (by linarith only [hqr]) (pair_character_primitive hsq hpqn (hp.mul hq))
      (pair_character_primitive hsq hprn (hp.mul hr))
      (pair_character_primitive hsq hqrn (hq.mul hr)) ha hb hc (inv_ne_one.mpr ha)
      (inv_ne_one.mpr hb) (inv_ne_one.mpr hc)
      (pair_character_even_of_korselt hn ho hp hq hpK hqK hvq)
      (pair_character_even_of_korselt hn ho hp hr hpK hrK hvr)
      (pair_character_even_of_korselt hn ho hq hr hqK hrK (hvr.trans hvq.symm)) hRlo hRhi hXR hX hy
      hH s hS ht hA hB hC
  rw [pair_level_log_sum hnprod] at h
  convert h using 1
  ring

/-- The sharp closed Euler tail and the reflected prefix bound the uniform witness gap. -/
theorem square_pair_witness {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r] [Fact p.Prime]
    [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)] (hsq : Squarefree n)
    (hnprod : n = p * q * r) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hn : 1 < n) (ho : Odd n) (hp : Odd p) (hq : Odd q) (hr : Odd r) (hpn : p ∣ n) (hqn : q ∣ n)
    (hrn : r ∣ n) (hpqn : p * q ∣ n) (hprn : p * r ∣ n) (hqrn : q * r ∣ n) (hpK : p - 1 ∣ n - 1)
    (hqK : q - 1 ∣ n - 1) (hrK : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1)) {X H R : ℝ} (hRlo : 465 / 2 ≤ R)
    (hRhi : R ≤ 278) (hXR : X = R ^ 2) (hX : 625 ≤ X) (hy : 12 ≤ Real.log X + 21 / 8)
    (hH : refinedReflectedEuler (1 : DirichletCharacter ℂ 1) X ≤ H) (s : Finset ℕ)
    (hS : ∀ k ∈ s, (k : ℝ) ≤ X)
    (hgap :
      (2 * Real.log n) *
                  (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8))) *
                    X ^ (-(27 / 25 : ℝ)) *
                    ((21 / 8 : ℝ) + Real.log X) ^ 5) -
                3 * quarterGammaFirstCorrection (Real.log X + 21 / 8) -
                4 * quarterGammaDensity (Real.log X + 21 / 8) +
              H -
            4 * ∑ k ∈ s, refinedDualWeight X k +
          (3 / 8 : ℝ) * Real.log n +
          -(3117 / 400 : ℝ) * (27 / 25 : ℝ) ^ 5 +
          4 * quarterEulerClosedTailCap X ≤
        4 *
              (∑ k ∈ Finset.Ioc 0 ⌊X⌋₊,
                (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X k).re) -
            (∑' k : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X k).re +
          21 / 250) :
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  classical
  by_contra h
  have hall : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
    intro l hl hlX
    exact Classical.byContradiction (fun hf ↦ h ⟨l, hl, hlX, hf⟩)
  exact
    (not_lt_of_ge hgap)
      (square_pair_gap hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK hqK hrK hvq hvr
        hRlo hRhi hXR hX hy hH s hS hall)

/-- Under GRH, a uniform Korselt triple admits a rejecting prime below the chosen square
whenever its principal sum and contour bounds leave a gap of at most the square recovery. -/
theorem square_uniform_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {X H R : ℝ} (hRlo : 465 / 2 ≤ R)
    (hRhi : R ≤ 278) (hXR : X = R ^ 2) (hX : 625 ≤ X) (hy : 12 ≤ Real.log X + 21 / 8)
    (hH : refinedReflectedEuler (1 : DirichletCharacter ℂ 1) X ≤ H) (s : Finset ℕ)
    (hS : ∀ k ∈ s, (k : ℝ) ≤ X)
    (hgap :
      (2 * Real.log n) *
                  (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8))) *
                    X ^ (-(27 / 25 : ℝ)) *
                    ((21 / 8 : ℝ) + Real.log X) ^ 5) -
                3 * quarterGammaFirstCorrection (Real.log X + 21 / 8) -
                4 * quarterGammaDensity (Real.log X + 21 / 8) +
              H -
            4 * ∑ k ∈ s, refinedDualWeight X k +
          (3 / 8 : ℝ) * Real.log n +
          -(3117 / 400 : ℝ) * (27 / 25 : ℝ) ^ 5 +
          4 * quarterEulerClosedTailCap X ≤
        4 *
              (∑ k ∈ Finset.Ioc 0 ⌊X⌋₊,
                (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X k).re) -
            (∑' k : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X k).re +
          21 / 250) :
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  obtain ⟨p, q, r, hp, hq, hr, _, _, hnprod⟩ := uniformKorselt_ordered_factors hu
  have hpD : p ∣ n := ⟨q * r, hnprod.trans (Nat.mul_assoc _ _ _)⟩
  have hqD : q ∣ n := ⟨p * r, hnprod.trans (by ac_rfl)⟩
  have hrD : r ∣ n := ⟨p * q, hnprod.trans (by ac_rfl)⟩
  have hpO := Odd.of_dvd_nat ho hpD
  have hqO := Odd.of_dvd_nat ho hqD
  have hrO := Odd.of_dvd_nat ho hrD
  have hp2 : p ≠ 2 := fun h ↦ (by decide : ¬Odd (2 : ℕ)) (h ▸ hpO)
  have hq2 : q ≠ 2 := fun h ↦ (by decide : ¬Odd (2 : ℕ)) (h ▸ hqO)
  have hr2 : r ≠ 2 := fun h ↦ (by decide : ¬Odd (2 : ℕ)) (h ▸ hrO)
  let : NeZero n := ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt hn)⟩
  let : NeZero p := ⟨hp.ne_zero⟩
  let : NeZero q := ⟨hq.ne_zero⟩
  let : NeZero r := ⟨hr.ne_zero⟩
  let : Fact p.Prime := ⟨hp⟩
  let : Fact q.Prime := ⟨hq⟩
  let : Fact r.Prime := ⟨hr⟩
  let : Fact (2 < p) := ⟨lt_of_le_of_ne hp.two_le (Ne.symm hp2)⟩
  let : Fact (2 < q) := ⟨lt_of_le_of_ne hq.two_le (Ne.symm hq2)⟩
  let : Fact (2 < r) := ⟨lt_of_le_of_ne hr.two_le (Ne.symm hr2)⟩
  have hpqD : p * q ∣ n := ⟨r, hnprod⟩
  have hprD : p * r ∣ n := ⟨q, hnprod.trans (by ac_rfl)⟩
  have hqrD : q * r ∣ n := ⟨p, hnprod.trans (by ac_rfl)⟩
  exact
    square_pair_witness hu.1 hnprod hGRH hn ho hpO hqO hrO hpD hqD hrD hpqD hprD hqrD
      (hu.2.2.1 p hp hpD) (hu.2.2.1 q hq hqD) (hu.2.2.1 r hr hrD) (hu.2.2.2 q p hq hp hqD hpD)
      (hu.2.2.2 r p hr hp hrD hpD) hRlo hRhi hXR hX hy hH s hS hgap

end PseudoPrime.PrimeTestBounds.MillerRabin
