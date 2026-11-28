/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131Zero
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131EulerTail
import PseudoPrime.AnalyticNumberTheory.Arithmetic.CharacterFullTriviality
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131Zero
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131EulerTail

/-! # The K131 Gram comparison at an arbitrary large radius -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private theorem raw_shifted_scale {y : ℝ} (hy : 0 < y) (hl : 14 ≤ 2 * Real.log y) (i : Fin 4) :
    1 ≤ y ^ 2 * Real.exp (-(k131GramFreq i)) := by
  have hf := (k131_gram_freq_mem i).2
  have he : Real.exp (k131GramFreq i) ≤ y ^ 2 := by
    rw [← Real.exp_log (pow_pos hy 2), Real.log_pow, Nat.cast_ofNat]
    exact Real.exp_le_exp.mpr (by linarith only [hf, hl])
  rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _), one_mul]
  exact he

private theorem raw_shifted_zero_euler {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive) (hn : χ ≠ 1)
    (hi : χ⁻¹ ≠ 1) {y : ℝ} (hy : 0 < y) (hl : 14 ≤ 2 * Real.log y) (i : Fin 4) :
    let x := y ^ 2 * Real.exp (-(k131GramFreq i))
    (∑' ρ : ℂ, k131MellinKernel.oscillatingZeroTerm χ x ρ).re =
      (Complex.log q * (k131MellinProfile x⁻¹ : ℂ)).re + (k131ReflectedIntegral χ x).re +
          (k131GammaIntegral χ x).re -
        ∑ n ∈ Finset.Icc 0 ⌊x * Real.exp (9 / 4)⌋₊,
          (χ n).re * (k131ForwardWeight (Real.sqrt x) n * ArithmeticFunction.vonMangoldt n) := by
  intro x
  have hx : 1 ≤ x := raw_shifted_scale hy hl i
  have hs : 1 ≤ Real.sqrt x := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hx
  have h := k131_euler_reflected hq hG hp hn hi hs
  rw [Real.sq_sqrt (zero_le_one.trans hx)] at h
  linarith only [h]

private theorem raw_gram_support_le {y : ℝ} (i : Fin 4) :
    y ^ 2 * Real.exp (-(k131GramFreq i)) * Real.exp (9 / 4) ≤ y ^ 2 := by
  rw [mul_assoc, ← Real.exp_add]
  have h := (k131_gram_freq_mem i).1
  exact mul_le_of_le_one_right (sq_nonneg _) (Real.exp_le_one_iff.mpr (by linarith only [h]))

/-- The K131 auxiliary contour difference at frequency `i` and radius `y`. -/
noncomputable def k131RawShiftedDifference {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (y : ℝ)
    (i : Fin 4) : ℝ :=
  let x := y ^ 2 * Real.exp (-(k131GramFreq i))
  (Complex.log q * (k131MellinProfile x⁻¹ : ℂ)).re + (k131ReflectedIntegral χ x).re +
      (k131GammaIntegral χ x).re -
    ∑ n ∈ Finset.Icc 0 ⌊x * Real.exp (9 / 4)⌋₊,
      k131ForwardWeight (Real.sqrt x) n * ArithmeticFunction.vonMangoldt n

private theorem raw_shifted_zero_main {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive) (hn : χ ≠ 1)
    (hi : χ⁻¹ ≠ 1) {y : ℝ} (hy : 0 < y) (hl : 14 ≤ 2 * Real.log y)
    (hsmall : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ y ^ 2 → χ l = 1) (i : Fin 4) :
    (∑' ρ : ℂ, k131MellinKernel.oscillatingZeroTerm χ (y ^ 2 * Real.exp (-(k131GramFreq i))) ρ).re =
      k131RawShiftedDifference χ y i := by
  let x := y ^ 2 * Real.exp (-(k131GramFreq i))
  have hx := zero_lt_one.trans_le (raw_shifted_scale hy hl i)
  have hx' : 0 ≤ x * Real.exp (9 / 4) := (mul_pos hx (Real.exp_pos _)).le
  have hb (n : ℕ) (hn' : n ∈ Finset.Icc 0 ⌊x * Real.exp (9 / 4)⌋₊) : (n : ℝ) ≤ y ^ 2 :=
    ((Nat.le_floor_iff hx').mp (Finset.mem_Icc.mp hn').2).trans (raw_gram_support_le i)
  have hsum :=
    AnalyticNumberTheory.Arithmetic.weighted_sum_re_eq_of_full_prime_trivial χ hsmall
      (Finset.Icc 0 ⌊x * Real.exp (9 / 4)⌋₊) hb (fun n ↦ k131ForwardWeight (Real.sqrt x) n)
  have h := raw_shifted_zero_euler hq hG hp hn hi hy hl i
  dsimp only at h
  unfold k131RawShiftedDifference
  convert h using 2
  simpa only [mul_comm, mul_left_comm, mul_assoc, x] using hsum.symm

private theorem raw_gram_main {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive) (hn : χ ≠ 1)
    (hi : χ⁻¹ ≠ 1) {y : ℝ} (hy : 0 < y) (hl : 14 ≤ 2 * Real.log y)
    (hsmall : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ y ^ 2 → χ l = 1) :
    let Z := k131MellinKernel.oscillatingZeroTerm χ (y ^ 2)
    let B := fun v : ℝ ↦ ∑' ρ : ℂ, ‖Z ρ‖ * Real.cos (v * ρ.im)
    let s := k131GramFreq
    let c := k131GramCoeff
    (∑ i, c i * (B (s i) + k131RawShiftedDifference χ y i)) -
        (∑ i, ∑ j, c i * c j * B (s i - s j)) / 2 ≤
      (∑' ρ : ℂ, ‖Z ρ‖) + (∑' ρ : ℂ, Z ρ).re := by
  have h := k131_gram_zero_lower hq hG hp hn hi (pow_pos hy 2) k131GramFreq k131GramCoeff
  dsimp only at h ⊢
  simpa only [raw_shifted_zero_main hq hG hp hn hi hy hl hsmall] using h

/-- At a positive radius with twice its logarithm at least fourteen, the
four-frequency K131 Gram lower bound follows from prime triviality. -/
theorem k131_raw_gram_contour_lower {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive) (hn : χ ≠ 1)
    {y : ℝ} (hy : 0 < y) (hl : 14 ≤ 2 * Real.log y)
    (hsmall : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ y ^ 2 → χ l = 1) :
    let Z := k131MellinKernel.oscillatingZeroTerm χ (y ^ 2)
    let s := k131GramFreq
    let c := k131GramCoeff
    (∑ i, c i * (k131CosineContour χ |s i| + k131RawShiftedDifference χ y i)) -
        (∑ i, ∑ j, c i * c j * k131CosineContour χ |s i - s j|) / 2 ≤
      k131CosineContour χ 0 + (∑' ρ : ℂ, Z ρ).re := by
  have hB := k131_cosine_contour hq hG hp hn (pow_pos hy 2)
  have h0 := hB 0
  simp only [zero_mul, Real.cos_zero, mul_one, abs_zero] at h0
  have h := raw_gram_main hq hG hp hn (inv_ne_one.mpr hn) hy hl hsmall
  dsimp only at h ⊢
  simpa only [hB, h0] using h

/-- Under RH and prime triviality, the shifted contour at a physical radius
equals its conductor, pole and principal zero terms plus the reflected deficit. -/
theorem k131_raw_shifted_deficit_eq {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hp : χ.IsPrimitive) (hn : χ ≠ 1) (hi : χ⁻¹ = χ) (he : χ.Even) (hRH : RiemannHypothesis) {y : ℝ}
    (hy : 0 < y) (hl : 14 ≤ 2 * Real.log y) (ht : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ y ^ 2 → χ p = 1)
    (i : Fin 4) :
    let X := y ^ 2
    let x := X * Real.exp (-(k131GramFreq i))
    k131RawShiftedDifference χ y i =
      (Complex.log q * (k131MellinProfile x⁻¹ : ℂ)).re -
          (k131MellinFn ((-1 / 2 : ℝ) : ℂ) * (x : ℂ) ^ ((-1 / 2 : ℝ) : ℂ)).re -
          (k131MellinFn ((1 / 2 : ℝ) : ℂ) * (x : ℂ) ^ ((1 / 2 : ℝ) : ℂ)).re +
        (∑' ρ, k131MellinKernel.zetaOscillatingZeroTerm x ρ).re +
        k131AuxReflect (fun n ↦ 1 - (χ n).re) X (k131GramFreq i - 9 / 4) := by
  intro X x
  have hX : 0 < X := pow_pos hy 2
  have hx : 1 ≤ x := raw_shifted_scale hy hl i
  have hs : 9 / 4 + (k131GramFreq i - 9 / 4) = k131GramFreq i := by ring
  have haux :=
    k131_aux_reflected_split hp hn hi hX
      (show 1 ≤ X * Real.exp (-(9 / 4 + (k131GramFreq i - 9 / 4))) by
        rw [hs]; exact hx)
      ht
  dsimp only at haux
  rw [hs] at haux
  have hleft := k131_left_xi_eq_reflected χ he hi (zero_lt_one.trans_le hx)
  have hdiff := congrArg Complex.re (k131_xi_poles_difference hRH hx)
  simp only [Complex.sub_re, Complex.add_re] at hdiff
  have hcancel := k131_principal_forward_eq χ he (Real.sqrt_pos.2 (zero_lt_one.trans_le hx))
  rw [Real.sq_sqrt (zero_le_one.trans hx)] at hcancel
  unfold k131RawShiftedDifference
  dsimp only [x, X] at haux hleft hdiff ⊢
  linarith only [haux, hleft, hdiff, hcancel]

/-- The signed shifted contour sum at a physical radius. -/
noncomputable def k131RawShiftedGram {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (y : ℝ) : ℝ :=
  ∑ i, k131GramCoeff i * k131RawShiftedDifference χ y i

/-- Separate the three shifted Gram sums into the principal and reflected terms. -/
theorem k131_raw_gram_shift_split {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ r}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hRH : RiemannHypothesis) {y : ℝ} (hy : 0 < y)
    (hl : 14 ≤ 2 * Real.log y)
    (ht : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ y ^ 2 → a l = 1 ∧ b l = 1 ∧ c l = 1) :
    let X := y ^ 2
    let x := fun i ↦ X * Real.exp (-(k131GramFreq i))
    let α := fun n : ℕ ↦ 3 - ((a n).re + (b n).re + (c n).re)
    k131RawShiftedGram a y + k131RawShiftedGram b y + k131RawShiftedGram c y =
      k131RawShiftPrincipal (Real.log p + Real.log q + Real.log r) y +
        3 *
          (∑ i : Fin 4,
            k131GramCoeff i * (∑' ρ, k131MellinKernel.zetaOscillatingZeroTerm (x i) ρ).re) +
        ∑ i : Fin 4, k131GramCoeff i * k131AuxReflect α X (k131GramFreq i - 9 / 4) := by
  intro X x α
  simp only [k131RawShiftedGram, k131RawShiftPrincipal, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have ea :=
    k131_raw_shifted_deficit_eq ha.1 ha.2.1 ha.2.2.1 ha.2.2.2 hRH hy hl
      (fun l hp hle ↦ (ht l hp hle).1) i
  have eb :=
    k131_raw_shifted_deficit_eq hb.1 hb.2.1 hb.2.2.1 hb.2.2.2 hRH hy hl
      (fun l hp hle ↦ (ht l hp hle).2.1) i
  have ec :=
    k131_raw_shifted_deficit_eq hc.1 hc.2.1 hc.2.2.1 hc.2.2.2 hRH hy hl
      (fun l hp hle ↦ (ht l hp hle).2.2) i
  have es :=
    k131_aux_reflect_add_three (char_gap_mem a) (char_gap_mem b) (char_gap_mem c) X
      (k131GramFreq i - 9 / 4)
  have eα : α = fun n : ℕ ↦ (1 - (a n).re) + (1 - (b n).re) + (1 - (c n).re) := by
    funext n
    dsimp only [α]
    ring
  dsimp only at ea eb ec
  rw [ea, eb, ec, eα, es]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    ← Complex.ofReal_natCast, Complex.log_ofReal_re, X, x]
  ring

private theorem raw_gram_upper_one {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive) (hn : χ ≠ 1)
    {y : ℝ} (hy : 0 < y) (hl : 14 ≤ 2 * Real.log y)
    (hsmall : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ y ^ 2 → χ l = 1) :
    -(∑' ρ : ℂ, k131MellinKernel.oscillatingZeroTerm χ (y ^ 2) ρ).re ≤
      k131CosineContour χ 0 + k131GramMix (fun t ↦ k131CosineContour χ |t|) -
        k131RawShiftedGram χ y := by
  have h := k131_raw_gram_contour_lower hq hG hp hn hy hl hsmall
  simp only [mul_add, Finset.sum_add_distrib] at h
  unfold k131GramMix k131RawShiftedGram
  linarith only [h]

/-- At any large positive radius, three primitive real even characters
have a joint zero bound with a common Euler tail and four Gram shifts. -/
theorem k131_raw_three_gram_upper {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ r}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hp : 2 ≤ p) (hq : 2 ≤ q) (hr : 2 ≤ r)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ} (hy : 0 < y)
    (hl : 14 ≤ 2 * Real.log y) (hpa : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ y ^ 2 → a l = 1)
    (hpb : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ y ^ 2 → b l = 1)
    (hpc : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ y ^ 2 → c l = 1) :
    let X := y ^ 2
    let B := k131CosineCore (Real.log p + Real.log q + Real.log r)
    let T :=
      ∑' n : { n : ℕ // ⌊X⌋₊ < n },
        ((3 - ((a n.val).re + (b n.val).re + (c n.val).re)) *
          (ArithmeticFunction.vonMangoldt n.val / (n.val : ℝ) ^ (35 / 16 : ℝ)) *
          (gaussianK131Fourier + k131GramEulerPoly).eval (Real.log n.val));
    -(∑' ρ : ℂ, k131MellinKernel.oscillatingZeroTerm a X ρ).re -
        (∑' ρ : ℂ, k131MellinKernel.oscillatingZeroTerm b X ρ).re -
        (∑' ρ : ℂ, k131MellinKernel.oscillatingZeroTerm c X ρ).re ≤
      B 0 + k131GramMix B + T -
        (k131RawShiftedGram a y + k131RawShiftedGram b y + k131RawShiftedGram c y) := by
  intro X B T
  let S := k131CosineTail a b c X
  have h (t : ℝ) :
    k131CosineContour a |t| + k131CosineContour b |t| + k131CosineContour c |t| = B t + S t :=
    k131_three_cosine_split ha hb hc (sq_nonneg _) t hpa hpb hpc
  have h0 := h 0
  rw [abs_zero] at h0
  have he := congrArg k131GramMix (funext h)
  simp only [k131_gram_mix_add] at he
  have h₁ := raw_gram_upper_one hp hG ha.1 ha.2.1 hy hl hpa
  have h₂ := raw_gram_upper_one hq hG hb.1 hb.2.1 hy hl hpb
  have h₃ := raw_gram_upper_one hr hG hc.1 hc.2.1 hy hl hpc
  have hX : Real.exp 7 ≤ X := by
    apply (Real.le_log_iff_exp_le (pow_pos hy 2)).mp
    rw [Real.log_pow, Nat.cast_ofNat]
    linarith only [hl]
  have hT : S 0 + k131GramMix S = T := k131_combined_euler_tail a b c hX
  linarith only [h₁, h₂, h₃, h0, he, hT]

/-- The K131 combined Euler-tail bound holds at arbitrary radii with
the required logarithmic support. -/
theorem k131_raw_trace_tail_le {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r)
    (hRH : RiemannHypothesis) {y : ℝ} (hy : 100 ≤ y) (hlog : 14 ≤ 2 * Real.log y)
    (htrace : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re) :
    let X := y ^ 2
    let v := Real.log X
    let P := gaussianK131Fourier + k131GramEulerPoly
    let D := Polynomial.X ^ 2 * (Polynomial.C (35 / 16 : ℝ) * P - P.derivative)
    k131CosineTail a b c X 0 + k131GramMix (k131CosineTail a b c X) ≤
      4 * Real.exp (-(19 / 16 : ℝ) * v) * (k131MomentPoly P (19 / 16) 0).eval v +
        Real.exp (-(27 / 16 : ℝ) * v) * (v ^ 2 * P.eval v + (k131MomentPoly D (27 / 16) 0).eval v) /
          6 := by
  intro X v P D
  have h101 : 101 ≤ X := by
    dsimp only [X]
    nlinarith only [hy, sq_nonneg (y - 100)]
  have hpos : 0 < X := (by norm_num only : (0 : ℝ) < 101).trans_le h101
  have hl : 14 ≤ v := by
    dsimp only [v, X]
    rw [Real.log_pow, Nat.cast_ofNat]
    exact hlog
  have h7 : Real.exp 7 ≤ X :=
    (Real.le_log_iff_exp_le hpos).mp ((by norm_num only : (7 : ℝ) ≤ 14).trans hl)
  have hweight : 0 ≤ k131TailWeight X :=
    mul_nonneg (Real.rpow_nonneg hpos.le _) (k131_tail_fourier_signs hl).1
  have hψ := tail_psi_rh hRH h101 ((by norm_num only : (1 : ℝ) ≤ 14).trans hl)
  have he := mul_le_mul_of_nonneg_right ((neg_le_abs _).trans hψ) hweight
  have hs :
    Real.sqrt X * v ^ 2 / 24 * k131TailWeight X =
      Real.exp (-(27 / 16 : ℝ) * v) * (v ^ 2 * P.eval v) / 24 := by
    rw [k131TailWeight, Real.sqrt_eq_rpow]
    have hp : X ^ (1 / 2 : ℝ) * X ^ (-(35 / 16 : ℝ)) = Real.exp (-(27 / 16 : ℝ) * v) := by
      rw [← Real.rpow_add hpos, show (1 / 2 : ℝ) + -(35 / 16) = -(27 / 16) by norm_num only,
        Real.rpow_def_of_pos hpos, mul_comm]
    change X ^ (1 / 2 : ℝ) * v ^ 2 / 24 * (X ^ (-(35 / 16 : ℝ)) * P.eval v) = _
    rw [← hp]
    ring
  change
    -(Chebyshev.psi X - X) * k131TailWeight X ≤ Real.sqrt X * v ^ 2 / 24 * k131TailWeight X at he
  rw [hs] at he
  have ht := k131_trace_tail_rh_le a b c hRH h7 h101 hl htrace
  dsimp only [v, P, D] at hs he ⊢
  linarith only [ht, he]

/-- The raw K131 Gram upper bound with its Euler tail replaced by the
explicit RH moments, at any radius in the analytic domain. -/
theorem k131_raw_three_zero_upper {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ r}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hp : 2 ≤ p) (hq : 2 ≤ q) (hr : 2 ≤ r)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ} (hy : 100 ≤ y)
    (hlog : 14 ≤ 2 * Real.log y) (hpa : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ y ^ 2 → a l = 1)
    (hpb : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ y ^ 2 → b l = 1)
    (hpc : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ y ^ 2 → c l = 1)
    (htrace : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re) :
    let X := y ^ 2
    let v := Real.log X
    let P := gaussianK131Fourier + k131GramEulerPoly
    let D := Polynomial.X ^ 2 * (Polynomial.C (35 / 16 : ℝ) * P - P.derivative)
    let B := k131CosineCore (Real.log p + Real.log q + Real.log r)
    (-(∑' ρ : ℂ, k131MellinKernel.oscillatingZeroTerm a X ρ).re -
        (∑' ρ : ℂ, k131MellinKernel.oscillatingZeroTerm b X ρ).re -
        (∑' ρ : ℂ, k131MellinKernel.oscillatingZeroTerm c X ρ).re ≤
      B 0 + k131GramMix B -
          (k131RawShiftedGram a y + k131RawShiftedGram b y + k131RawShiftedGram c y) +
        4 * Real.exp (-(19 / 16 : ℝ) * v) * (k131MomentPoly P (19 / 16) 0).eval v +
        Real.exp (-(27 / 16 : ℝ) * v) * (v ^ 2 * P.eval v + (k131MomentPoly D (27 / 16) 0).eval v) /
          6) := by
  intro X v P D B
  have hy₀ : 0 < y := (by norm_num only : (0 : ℝ) < 100).trans_le hy
  have hv : 14 ≤ v := by
    dsimp only [v, X]
    rw [Real.log_pow, Nat.cast_ofNat]
    exact hlog
  have h7 : Real.exp 7 ≤ X :=
    (Real.le_log_iff_exp_le (pow_pos hy₀ 2)).mp ((by norm_num only : (7 : ℝ) ≤ 14).trans hv)
  have hz := k131_raw_three_gram_upper ha hb hc hp hq hr hG hy₀ hlog hpa hpb hpc
  have he := k131_combined_euler_tail a b c h7
  have ht := k131_raw_trace_tail_le a b c hG.riemann hy hlog htrace
  dsimp only at ht hz
  dsimp only [X, v, P, D, B] at he ⊢
  rw [he] at ht
  linarith only [hz, ht]

private theorem raw_shift_xi_cap (hRH : RiemannHypothesis) {y : ℝ} (hy : 0 < y)
    (hl : 14 ≤ 2 * Real.log y) :
    let X := y ^ 2
    |3 *
          (∑ j : Fin 4,
            k131GramCoeff j *
              (∑' ρ,
                  k131MellinKernel.zetaOscillatingZeroTerm (X * Real.exp (-(k131GramFreq j)))
                    ρ).re)| ≤
      (3 / 5000 : ℝ) := by
  intro X
  let F := fun j : Fin 4 ↦
    (∑' ρ, k131MellinKernel.zetaOscillatingZeroTerm (X * Real.exp (-(k131GramFreq j))) ρ).re
  have hcap (j : Fin 4) : |F j| ≤ (231 / 500000 : ℝ) :=
    k131_forward_xi_cap hRH (zero_lt_one.trans_le (raw_shifted_scale hy hl j))
  have hs : |∑ j : Fin 4, k131GramCoeff j * F j| ≤ (2003 / 5000 : ℝ) * (231 / 500000) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [← k131_gram_abs_sum, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j _
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hcap j) (abs_nonneg _)
  change |3 * ∑ j : Fin 4, k131GramCoeff j * F j| ≤ _
  rw [abs_mul, abs_of_nonneg (by norm_num only : (0 : ℝ) ≤ 3)]
  linarith only [hs]

private theorem raw_aux_scalar_le_pair {α : ℕ → ℝ} (hα : ∀ n, α n ∈ Set.Icc (0 : ℝ) 4)
    (hRH : RiemannHypothesis) {y : ℝ} (hy : 100 ≤ y) (hl : 14 ≤ 2 * Real.log y) :
    logPowerPoly (-(23 / 4 : ℝ)) gaussianK131Poly23 y +
        logPowerPoly (-(27 / 4 : ℝ)) gaussianK131PolyHigher y ≤
      ∑ j : Fin 2, -reflectionWeights j * k131AuxReflect α (y ^ 2) (reflectionOffsets j) := by
  have hpos : 0 < y := (by norm_num only : (0 : ℝ) < 100).trans_le hy
  have h101 : 101 ≤ y ^ 2 := by nlinarith only [hy, sq_nonneg (y - 100)]
  have hv : 14 ≤ Real.log (y ^ 2) := by
    rw [Real.log_pow, Nat.cast_ofNat]
    exact hl
  rw [← aux_bound_scalar_eq hpos]
  apply Finset.sum_le_sum
  intro j _
  have hh := reflection_offset_le j
  have h :=
    k131_aux_reflect_bound_le hα hRH (h := reflectionOffsets j) h101 (by linarith only [hv])
      (by linarith only [hh, hv]) (by linarith only [hh, hv])
  have hm := mul_le_mul_of_nonpos_left h (neg_nonpos.mpr (reflection_weight_nonneg j))
  nlinarith only [hm]

/-- Bound the shifted Gram sum by its principal terms and the two reflection polynomials,
with the uniform RH allowance for the zeta zero sums. -/
theorem k131_raw_shift_gram_lower {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ r}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hRH : RiemannHypothesis) {y : ℝ} (hy : 100 ≤ y)
    (hl : 14 ≤ 2 * Real.log y)
    (ht : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ y ^ 2 → a l = 1 ∧ b l = 1 ∧ c l = 1)
    (htrace : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re) :
    k131RawShiftPrincipal (Real.log p + Real.log q + Real.log r) y +
          logPowerPoly (-(23 / 4 : ℝ)) gaussianK131Poly23 y +
          logPowerPoly (-(27 / 4 : ℝ)) gaussianK131PolyHigher y -
        3 / 5000 ≤
      k131RawShiftedGram a y + k131RawShiftedGram b y + k131RawShiftedGram c y := by
  have hpos : 0 < y := (by norm_num only : (0 : ℝ) < 100).trans_le hy
  let α := fun n : ℕ ↦ 3 - ((a n).re + (b n).re + (c n).re)
  have hα (n : ℕ) : α n ∈ Set.Icc (0 : ℝ) 4 := by
    dsimp only [α]
    exact
      ⟨by linarith only [(char_gap_mem a n).1, (char_gap_mem b n).1, (char_gap_mem c n).1], by
        linarith only [htrace n]⟩
  have hv : 9 / 2 ≤ Real.log (y ^ 2) := by
    rw [Real.log_pow, Nat.cast_ofNat]
    exact (by norm_num only : (9 / 2 : ℝ) ≤ 14).trans hl
  have hm := raw_aux_scalar_le_pair hα hRH hy hl
  have hg := k131_gram_aux_reflect_lower hα hv
  have hr :
    logPowerPoly (-(23 / 4 : ℝ)) gaussianK131Poly23 y +
        logPowerPoly (-(27 / 4 : ℝ)) gaussianK131PolyHigher y ≤
      ∑ i : Fin 4, k131GramCoeff i * k131AuxReflect α (y ^ 2) (k131GramFreq i - 9 / 4) :=
    hm.trans
      (by
        simpa only [reflectionWeights, reflectionOffsets, Fin.sum_univ_succ, Fin.sum_univ_zero,
          Matrix.cons_val_zero, Matrix.cons_val_succ, add_zero, neg_mul, ← sub_eq_add_neg] using hg)
  have hx := raw_shift_xi_cap hRH hpos hl
  have he := k131_raw_gram_shift_split ha hb hc hRH hpos hl ht
  dsimp only at he hx
  dsimp only [α] at hr ⊢
  linarith only [hr, (abs_le.mp hx).1, he]

/-- Bound the negative sum of the three K131 zero contributions by scalar
principal, Euler tail and reflection terms at a radius of at least 100. -/
theorem k131_raw_zero_scalar_upper {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ r}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hp : 2 ≤ p) (hq : 2 ≤ q) (hr : 2 ≤ r)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ} (hy : 100 ≤ y)
    (hlog : 14 ≤ 2 * Real.log y) (hpa : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ y ^ 2 → a l = 1)
    (hpb : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ y ^ 2 → b l = 1)
    (hpc : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ y ^ 2 → c l = 1)
    (htrace : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re) :
    let X := y ^ 2
    let v := Real.log X
    let P := gaussianK131Fourier + k131GramEulerPoly
    let D := Polynomial.X ^ 2 * (Polynomial.C (35 / 16 : ℝ) * P - P.derivative)
    let B := k131CosineCore (Real.log p + Real.log q + Real.log r)
    (-(∑' ρ : ℂ, k131MellinKernel.oscillatingZeroTerm a X ρ).re -
        (∑' ρ : ℂ, k131MellinKernel.oscillatingZeroTerm b X ρ).re -
        (∑' ρ : ℂ, k131MellinKernel.oscillatingZeroTerm c X ρ).re ≤
      B 0 + k131GramMix B -
          (k131RawShiftPrincipal (Real.log p + Real.log q + Real.log r) y +
              logPowerPoly (-(23 / 4 : ℝ)) gaussianK131Poly23 y +
              logPowerPoly (-(27 / 4 : ℝ)) gaussianK131PolyHigher y -
            3 / 5000) +
        4 * Real.exp (-(19 / 16 : ℝ) * v) * (k131MomentPoly P (19 / 16) 0).eval v +
        Real.exp (-(27 / 16 : ℝ) * v) * (v ^ 2 * P.eval v + (k131MomentPoly D (27 / 16) 0).eval v) /
          6) := by
  intro X v P D B
  have hz := k131_raw_three_zero_upper ha hb hc hp hq hr hG hy hlog hpa hpb hpc htrace
  have hs :=
    k131_raw_shift_gram_lower ha hb hc hG.riemann hy hlog
      (fun l hl hle ↦ ⟨hpa l hl hle, hpb l hl hle, hpc l hl hle⟩) htrace
  dsimp only at hz
  dsimp only [X, v, P, D, B]
  linarith only [hz, hs]

end PseudoPrime.PrimeTestBounds.MillerRabin
