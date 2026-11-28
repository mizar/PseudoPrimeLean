/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrimeContour570

/-! # Three-character contour bound on the section 86 radius interval -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under RH, if three characters are one at primes through the squared radius and their
real sum is at least minus one, their signed reflected kernel series is below minus 0.02691
for radii from 287 through 288. Prime-power support supplies the finite prefix sign. -/
theorem reflected_triple_kernel_576 (hRH : RiemannHypothesis) {p q s : ℕ} {r : ℝ} (hl : 287 ≤ r)
    (hu : r ≤ 288) (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q)
    (c : DirichletCharacter ℂ s) (ht : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → a l = 1)
    (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → c l = 1) :
    -(∑' n : ℕ,
          ((a n).re + (b n).re + (c n).re) *
            (ArithmeticFunction.vonMangoldt n / Real.sqrt n *
              (quarterKernel570.transform (((n : ℝ) * r ^ 2)⁻¹)).re)) <
      -(2691 / 100000) := by
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
    have hx := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 287) hl 2
    exact
      AnalyticNumberTheory.Arithmetic.character_eq_one_of_ambient_mangoldt (N := 1) χ
        (fun l hl hlX _ ↦ hχ l hl hlX) (by linarith only [hx, hn']) (Nat.coprime_one_right n) hv
  have hprefix (n : ℕ) (hn : n ∈ Finset.Ioc 0 2701) (hv : ArithmeticFunction.vonMangoldt n ≠ 0) :
    τ n = 3 := by
    dsimp only [τ]
    rw [hone a hA hn hv, hone b hB hn hv, hone c hC hn hv, Complex.one_re]
    norm_num only
  have h := reflected_kernel_bound_576 hRH hl hu τ hsign hprefix
  let C := ((51 / 50 : ℝ) ^ 5 / 120 * Real.exp (-(51 / 50) * (14 / 5))) * r ^ (-(2 * (51 / 50 : ℝ)))
  change -(∑' n : ℕ, τ n * _) < _
  simp_rw [reflected_kernel_term_570 (show 1 ≤ r by linarith only [hl])]
  change -(∑' n : ℕ, τ n * (C * reflectedWeight570 _ n)) < _
  simp_rw [mul_left_comm (τ _) C, tsum_mul_left, ← mul_neg]
  exact h

/-- For three characters satisfying the prime-prefix and sign conditions, the negative
sum of their reflected integrals at a square cutoff is below minus 0.02691 throughout
the section 86 radius interval. Add the three absolutely convergent kernel series. -/
theorem reflected_integrals_lt_576 (hRH : RiemannHypothesis) {p q s : ℕ} [NeZero p] [NeZero q]
    [NeZero s] {r : ℝ} (hl : 287 ≤ r) (hu : r ≤ 288) (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ s)
    (ht : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → a l = 1)
    (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → c l = 1) :
    -(reflectedIntegral570 a (r ^ 2) + reflectedIntegral570 b (r ^ 2) +
          reflectedIntegral570 c (r ^ 2)) <
      -(2691 / 100000) := by
  have hx := sq_pos_of_pos (show 0 < r by linarith only [hl])
  have h :=
    ((reflected_hasSum_570 a hx).add (reflected_hasSum_570 b hx)).add (reflected_hasSum_570 c hx)
  have he := h.tsum_eq
  simp only [← add_mul] at he
  rw [← he]
  exact reflected_triple_kernel_576 hRH hl hu a b c ht hA hB hC

/-- At radii 287 to 288 the three prime sums are bounded by their conductor and gamma
costs plus their zero masses, with a strict saving of 0.02691 from the reflected integral. -/
theorem triple_contour_upper_576 {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hRH : RiemannHypothesis)
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ s)
    (hP : 2 ≤ p) (hQ : 2 ≤ q) (hS : 2 ≤ s) (pa : a.IsPrimitive) (pb : b.IsPrimitive)
    (pc : c.IsPrimitive) (na : a ≠ 1) (nb : b ≠ 1) (nc : c ≠ 1) (ia : a⁻¹ ≠ 1) (ib : b⁻¹ ≠ 1)
    (ic : c⁻¹ ≠ 1) {r : ℝ} (hl : 287 ≤ r) (hu : r ≤ 288)
    (ht : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → a l = 1)
    (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → c l = 1) :
    let x := r ^ 2
    (∑' n : ℕ, quarterKernel570.summand a x n).re + (∑' n : ℕ, quarterKernel570.summand b x n).re +
        (∑' n : ℕ, quarterKernel570.summand c x n).re <
      contourNonEuler570 a x + contourNonEuler570 b x + contourNonEuler570 c x +
          (quarterMass570 a + quarterMass570 b + quarterMass570 c) -
        2691 / 100000 := by
  intro x
  have hx : 1 ≤ x := one_le_pow₀ (show 1 ≤ r by linarith only [hl])
  have h1 := contour_prime_upper_570 hP hG pa na ia hx
  have h2 := contour_prime_upper_570 hQ hG pb nb ib hx
  have h3 := contour_prime_upper_570 hS hG pc nc ic hx
  simp only [reflected_inv_570 _ (zero_lt_one.trans_le hx)] at h1 h2 h3
  have hd := reflected_integrals_lt_576 hRH hl hu a b c ht hA hB hC
  change -(reflectedIntegral570 a x + reflectedIntegral570 b x + reflectedIntegral570 c x) < _ at hd
  linarith only [h1, h2, h3, hd]

end PseudoPrime.PrimeTestBounds.MillerRabin
