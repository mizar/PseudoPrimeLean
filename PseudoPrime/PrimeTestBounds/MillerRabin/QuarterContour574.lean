/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrimeContour570

/-! # Three-character contour upper bound on the section 62 interval -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under RH, if three characters are one at primes through the squared radius and their
real sum is at least minus one, their signed reflected kernel series is below minus 0.02705
for radii from 285 through 287. Prime-power support supplies the finite prefix sign. -/
theorem reflected_triple_kernel_574 (hRH : RiemannHypothesis) {p q s : ℕ} {r : ℝ} (hl : 285 ≤ r)
    (hu : r ≤ 287) (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q)
    (c : DirichletCharacter ℂ s) (ht : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → a l = 1)
    (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → c l = 1) :
    -(∑' n : ℕ,
          ((a n).re + (b n).re + (c n).re) *
            (ArithmeticFunction.vonMangoldt n / Real.sqrt n *
              (quarterKernel570.transform (((n : ℝ) * r ^ 2)⁻¹)).re)) <
      -(2705 / 100000) := by
  let τ := fun n : ℕ ↦ (a n).re + (b n).re + (c n).re
  have hsign (n : ℕ) : -1 ≤ τ n ∧ τ n ≤ 3 := by
    refine ⟨ht n, ?_⟩
    dsimp only [τ]
    linarith only [(Complex.re_le_norm _).trans (a.norm_le_one n),
      (Complex.re_le_norm _).trans (b.norm_le_one n),
      (Complex.re_le_norm _).trans (c.norm_le_one n)]
  have hone {m : ℕ} (χ : DirichletCharacter ℂ m) (hχ : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → χ l = 1)
    {n : ℕ} (hn : n ∈ Finset.Ioc 0 2701) (hv : ArithmeticFunction.vonMangoldt n ≠ 0) : χ n = 1 := by
    have hn' : (n : ℝ) ≤ 2701 := by exact_mod_cast (Finset.mem_Ioc.mp hn).2
    have hx := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 285) hl 2
    exact
      AnalyticNumberTheory.Arithmetic.character_eq_one_of_ambient_mangoldt (N := 1) χ
        (fun l hl hlX _ ↦ hχ l hl hlX) (by linarith only [hx, hn']) (Nat.coprime_one_right n) hv
  have hprefix (n : ℕ) (hn : n ∈ Finset.Ioc 0 2701) (hv : ArithmeticFunction.vonMangoldt n ≠ 0) :
    τ n = 3 := by
    dsimp only [τ]
    rw [hone a hA hn hv, hone b hB hn hv, hone c hC hn hv, Complex.one_re]
    norm_num only
  have h := reflected_kernel_bound_574 hRH hl hu τ hsign hprefix
  let C := ((51 / 50 : ℝ) ^ 5 / 120 * Real.exp (-(51 / 50) * (14 / 5))) * r ^ (-(2 * (51 / 50 : ℝ)))
  change -(∑' n : ℕ, τ n * _) < _
  simp_rw [reflected_kernel_term_570 (show 1 ≤ r by linarith only [hl])]
  change -(∑' n : ℕ, τ n * (C * reflectedWeight570 _ n)) < _
  simp_rw [mul_left_comm (τ _) C, tsum_mul_left, ← mul_neg]
  exact h

/-- For three characters satisfying the prime-prefix and sign conditions, the negative
sum of their reflected integrals at a square cutoff is below minus 0.02705 throughout
the section 62 radius interval. Add the three absolutely convergent kernel series. -/
theorem reflected_integrals_lt_574 (hRH : RiemannHypothesis) {p q s : ℕ} [NeZero p] [NeZero q]
    [NeZero s] {r : ℝ} (hl : 285 ≤ r) (hu : r ≤ 287) (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ s)
    (ht : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → a l = 1)
    (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → c l = 1) :
    -(reflectedIntegral570 a (r ^ 2) + reflectedIntegral570 b (r ^ 2) +
          reflectedIntegral570 c (r ^ 2)) <
      -(2705 / 100000) := by
  have hx := sq_pos_of_pos (show 0 < r by linarith only [hl])
  have h :=
    ((reflected_hasSum_570 a hx).add (reflected_hasSum_570 b hx)).add (reflected_hasSum_570 c hx)
  have he := h.tsum_eq
  simp only [← add_mul] at he
  rw [← he]
  exact reflected_triple_kernel_574 hRH hl hu a b c ht hA hB hC

/-- At radii 285 to 287 the three prime sums are bounded by their conductor and gamma
costs plus their zero masses, with a strict saving of 0.02705 from the reflected integral. -/
theorem triple_contour_upper_574 {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hRH : RiemannHypothesis)
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ s)
    (hP : 2 ≤ p) (hQ : 2 ≤ q) (hS : 2 ≤ s) (pa : a.IsPrimitive) (pb : b.IsPrimitive)
    (pc : c.IsPrimitive) (na : a ≠ 1) (nb : b ≠ 1) (nc : c ≠ 1) (ia : a⁻¹ ≠ 1) (ib : b⁻¹ ≠ 1)
    (ic : c⁻¹ ≠ 1) {r : ℝ} (hl : 285 ≤ r) (hu : r ≤ 287)
    (ht : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → a l = 1)
    (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → c l = 1) :
    let x := r ^ 2
    (∑' n : ℕ, quarterKernel570.summand a x n).re + (∑' n : ℕ, quarterKernel570.summand b x n).re +
        (∑' n : ℕ, quarterKernel570.summand c x n).re <
      contourNonEuler570 a x + contourNonEuler570 b x + contourNonEuler570 c x +
          (quarterMass570 a + quarterMass570 b + quarterMass570 c) -
        2705 / 100000 := by
  intro x
  have hx : 1 ≤ x := one_le_pow₀ (show 1 ≤ r by linarith only [hl])
  have h1 := contour_prime_upper_570 hP hG pa na ia hx
  have h2 := contour_prime_upper_570 hQ hG pb nb ib hx
  have h3 := contour_prime_upper_570 hS hG pc nc ic hx
  simp only [reflected_inv_570 _ (zero_lt_one.trans_le hx)] at h1 h2 h3
  have hd := reflected_integrals_lt_574 hRH hl hu a b c ht hA hB hC
  change -(reflectedIntegral570 a x + reflectedIntegral570 b x + reflectedIntegral570 c x) < _ at hd
  linarith only [h1, h2, h3, hd]

/-- For three primitive even characters satisfying the section 62 sign and conductor bounds,
GRH bounds their prime sums throughout the radius interval from 285 to 287. Combine the
zero-mass estimate with the signed reflected Euler term and the common even Gamma integral. -/
theorem triple_explicit_upper_574 {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ s) (hP : 2 ≤ p) (hQ : 2 ≤ q) (hS : 2 ≤ s)
    (pa : a.IsPrimitive) (pb : b.IsPrimitive) (pc : c.IsPrimitive) (na : a ≠ 1) (nb : b ≠ 1)
    (nc : c ≠ 1) (ia : a⁻¹ ≠ 1) (ib : b⁻¹ ≠ 1) (ic : c⁻¹ ≠ 1) {r : ℝ} (hl : 285 ≤ r) (hu : r ≤ 287)
    (ht : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → a l = 1)
    (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → c l = 1)
    (hlog : Real.log p + Real.log q + Real.log s ≤ 4 * r) (ea : a.Even) (eb : b.Even)
    (ec : c.Even) :
    let x := r ^ 2
    (∑' n : ℕ, quarterKernel570.summand a x n).re + (∑' n : ℕ, quarterKernel570.summand b x n).re +
        (∑' n : ℕ, quarterKernel570.summand c x n).re <
      4 * r * Analysis.rationalPoleProfile 3 (25 / 51) (7 / 5) x⁻¹ +
          3 * (reflectedArch570 a⁻¹ x + rightGamma570 a x).re +
          (3 / 4 * r - 127636 / 10000) -
        2705 / 100000 := by
  intro x
  have h :=
    triple_contour_upper_574 hG hG.riemann a b c hP hQ hS pa pb pc na nb nc ia ib ic hl hu ht hA hB
      hC
  have hm :=
    quarter_mass_numeric_574 a b c hP hQ hS (hG p a pa) (hG q b pb) (hG s c pc) pa pb pc na nb nc ia
      ib ic hl hu ht hA hB hC hlog hG.riemann ea eb ec
  have hb := congrArg Complex.re (even_gamma_cost_eq_570 b a ib ia eb ea x)
  have hc := congrArg Complex.re (even_gamma_cost_eq_570 c a ic ia ec ea x)
  have hw := (quarter_reflected_weight_574 (by linarith only [hl] : 278 ≤ r) hu).1
  have hr : 0 < r := by linarith only [hl]
  rw [quarterKernel570,
    LLS.PaperStatements.rationalPole_transform _ _ _ _ (one_div_pos.mpr (sq_pos_of_pos hr)),
    Complex.ofReal_re, one_div] at hw
  have hp : 0 ≤ Analysis.rationalPoleProfile 3 (25 / 51) (7 / 5) x⁻¹ := by linarith only [hw]
  have hd := mul_le_mul_of_nonneg_right hlog hp
  dsimp only at h
  unfold contourNonEuler570 at h
  simp only [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg _),
    ← Complex.ofReal_mul, Complex.ofReal_re] at h
  simp only [Complex.add_re] at hb hc ⊢
  linarith only [h, hm, hb, hc, hd]

end PseudoPrime.PrimeTestBounds.MillerRabin
