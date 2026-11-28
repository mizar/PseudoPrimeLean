/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleMassDifference
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianPairCharacterData
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleMassContour
import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticTripleConductors
import PseudoPrime.AnalyticNumberTheory.Arithmetic.CharacterPrimeTriviality

/-! # Three-character middle mass and its signed Euler tail -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The signed unit-scale Mangoldt series converges absolutely for every character. -/
public theorem middle_mass_series_summable (Q : Polynomial ℚ) (a : ℚ) (d : ℕ) (ha : 2 ≤ (a : ℝ))
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    Summable
      (fun n : ℕ ↦
        ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) * χ n *
          (middleMassProfile Q a d n : ℂ)) := by
  let B := fun j ↦ balancedPoleKernel a ha (d + 1 - j)
  let c := fun j ↦ ((normSqPolynomial a Q).coeff j : ℂ)
  have hs (s : Finset ℕ) : Summable (fun n : ℕ ↦ ∑ j ∈ s, c j * (B j).summand χ 1 n) := by
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      exact summable_zero
    | @insert j s hj ih =>
      simp only [Finset.sum_insert hj]
      exact (((B j).summable_summand χ zero_lt_one).mul_left (c j)).add ih
  exact (hs (Finset.range (d + 1))).congr (middle_mass_mangoldt Q a d ha χ)

/-- Taking real parts converts the signed Mangoldt sum to the real character trace weight. -/
public theorem middle_mass_series_re (Q : Polynomial ℚ) (a : ℚ) (d : ℕ) (ha : 2 ≤ (a : ℝ)) {q : ℕ}
    [NeZero q] (χ : DirichletCharacter ℂ q) :
    let W := fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n / Real.sqrt n * middleMassProfile Q a d n
    HasSum (fun n : ℕ ↦ (χ n).re * W n)
      ((∑' n : ℕ,
          ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) * χ n *
            (middleMassProfile Q a d n : ℂ)).re) := by
  intro W
  apply (Complex.hasSum_re (middle_mass_series_summable Q a d ha χ).hasSum).congr_fun
  intro n
  simp only [W, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero]
  ac_rfl

/-- At unit scale, the Euler deficit is supported strictly above the tested cutoff. -/
private theorem middle_mass_deficit_tail (Q : Polynomial ℚ) (a : ℚ) (d : ℕ) {q : ℕ}
    (χ : DirichletCharacter ℂ q) {X : ℝ} (hX : 0 ≤ X)
    (hp : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ X → χ p = 1) :
    let W := fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n / Real.sqrt n * middleMassProfile Q a d n
    (∑' n : ℕ, (1 - (χ n).re) * W n) =
      ∑' n : { n : ℕ // ⌊X⌋₊ < n }, (1 - (χ n.val).re) * W n.val := by
  intro W
  symm
  apply
    tsum_subtype_eq_of_support_subset (f := fun n : ℕ ↦ (1 - (χ n).re) * W n) (s :=
      {n : ℕ | ⌊X⌋₊ < n})
  intro n hn
  by_contra hno
  have hcut := (Nat.le_floor_iff hX).mp (le_of_not_gt hno)
  apply hn
  by_cases hm : ArithmeticFunction.vonMangoldt n = 0
  · simp only [W, hm, zero_div, zero_mul, mul_zero]
  simp only [AnalyticNumberTheory.Arithmetic.character_apply_one_of_mangoldt_ne_zero χ hp hcut hm,
    Complex.one_re, sub_self, zero_mul]

/-- The three signed deficits combine into the coefficient three minus the pair trace. -/
private theorem middle_mass_trace_sum (Q : Polynomial ℚ) (a : ℚ) (d : ℕ) (ha : 2 ≤ (a : ℝ))
    {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r] (χ₁ : DirichletCharacter ℂ p)
    (χ₂ : DirichletCharacter ℂ q) (χ₃ : DirichletCharacter ℂ r) (X : ℝ) :
    let W := fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n / Real.sqrt n * middleMassProfile Q a d n
    let E := fun {m : ℕ} (χ : DirichletCharacter ℂ m) ↦
      ∑' n : { n : ℕ // ⌊X⌋₊ < n }, (1 - (χ n.val).re) * W n.val
    E χ₁ + E χ₂ + E χ₃ =
      ∑' n : { n : ℕ // ⌊X⌋₊ < n },
        (3 - ((χ₁ n.val).re + (χ₂ n.val).re + (χ₃ n.val).re)) * W n.val := by
  intro W E
  have hs {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) : Summable (fun n : ℕ ↦ (χ n).re * W n) :=
    (middle_mass_series_re Q a d ha χ).summable
  have hW : Summable W := by
    apply (hs (1 : DirichletCharacter ℂ 1)).congr
    intro n
    simp only [MulChar.one_apply (isUnit_of_subsingleton (n : ZMod 1)), Complex.one_re, one_mul]
  have hE {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) :
    Summable (fun n : { n : ℕ // ⌊X⌋₊ < n } ↦ (1 - (χ n.val).re) * W n.val) := by
    apply ((hW.sub (hs χ)).subtype _).congr
    intro n
    change W n.val - (χ n.val).re * W n.val = _
    rw [sub_mul, one_mul]
  symm
  apply HasSum.tsum_eq
  apply (((hE χ₁).hasSum.add (hE χ₂).hasSum).add (hE χ₃).hasSum).congr_fun
  intro n
  ring

/-- The real middle zero mass with completed-function zero multiplicities. -/
public noncomputable def middleZeroMass (Q : Polynomial ℚ) (a : ℚ) (m : ℕ) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) : ℝ :=
  ∑' ρ : ℂ,
    (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
      (middleMassExtension Q a m (Complex.I * ρ.im)).re

/-- The real mass difference uses the ordinary real trace in the Euler series. -/
public theorem middle_mass_even_real (Q : Polynomial ℚ) (a : ℚ) {d : ℕ} (ha : 2 ≤ (a : ℝ))
    (hd : 1 ≤ d) (hQ : Q.natDegree ≤ d) {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hi : χ⁻¹ = χ) (he : χ.Even) :
    let W := fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n / Real.sqrt n * middleMassProfile Q a d n
    middleZeroMass Q a (d + 2) χ - (middleXiMass Q a d).re =
      middleMassProfile Q a d 1 * Real.log q -
          2 * (middleMassExtension Q a (d + 2) ((1 / 2 : ℝ) : ℂ)).re +
        2 * ∑' n : ℕ, (1 - (χ n).re) * W n := by
  intro W
  have h₁ := middle_mass_series_re Q a d ha (1 : DirichletCharacter ℂ 1)
  have h₂ := middle_mass_series_re Q a d ha χ
  dsimp only at h₁ h₂
  simp only [MulChar.one_apply (isUnit_of_subsingleton (_ : ZMod 1)), Complex.one_re, one_mul] at h₁
  have heul : HasSum (fun n : ℕ ↦ (1 - (χ n).re) * W n) _ :=
    (h₁.sub h₂).congr_fun (fun n ↦ by rw [sub_mul, one_mul])
  have hz :
    (∑' ρ : ℂ,
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℂ) *
          middleMassExtension Q a (d + 2) (Complex.I * ρ.im)) =
      (middleZeroMass Q a (d + 2) χ : ℂ) := by
    rw [middleZeroMass, Complex.ofReal_tsum]
    apply tsum_congr
    intro ρ
    simp only [middle_mass_extension_line, Complex.ofReal_re, Complex.ofReal_mul,
      Complex.ofReal_intCast]
  have h := middle_mass_even_difference Q a ha hd hQ hq hGRH hp hne hi he
  dsimp only at h
  rw [hz, ← Complex.natCast_log] at h
  have hr := congrArg Complex.re h
  have htwo (z : ℂ) : (2 * z).re = 2 * z.re := by
    rw [← Complex.ofReal_ofNat, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero]
  simp only [Complex.sub_re, Complex.add_re, ← Complex.ofReal_mul, Complex.ofReal_re, htwo,
    MulChar.one_apply (isUnit_of_subsingleton (_ : ZMod 1))] at hr
  rw [heul.tsum_eq]
  linarith only [hr]

/-- For the three pair characters, the absolute mass equals the conductor,
principal zero and pole terms plus the Euler deficit strictly beyond the cutoff. -/
public theorem middle_three_mass (Q : Polynomial ℚ) (a : ℚ) {d : ℕ} (ha : 2 ≤ (a : ℝ)) (hd : 1 ≤ d)
    (hQ : Q.natDegree ≤ d) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {n p q r : ℕ} [NeZero p] [NeZero q] [NeZero r] [NeZero n] [Fact p.Prime] [Fact q.Prime]
    [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)] (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hprod : n = p * q * r) (hp : Odd p) (hq : Odd q) (hr : Odd r)
    {X : ℝ} (hX : 0 ≤ X)
    (hpass : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → PrimeTest.StrongMillerRabinPass n (l : ZMod n)) :
    let χ₁ := NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq)
    let χ₂ := NumberTheory.complexJacobiNumeratorCharacter (p * r) (hp.mul hr)
    let χ₃ := NumberTheory.complexJacobiNumeratorCharacter (q * r) (hq.mul hr)
    let τ := fun j : ℕ ↦ (χ₁ j).re + (χ₂ j).re + (χ₃ j).re
    let W := fun j : ℕ ↦ ArithmeticFunction.vonMangoldt j / Real.sqrt j * middleMassProfile Q a d j
    middleZeroMass Q a (d + 2) χ₁ + middleZeroMass Q a (d + 2) χ₂ + middleZeroMass Q a (d + 2) χ₃ =
      middleMassProfile Q a d 1 * (2 * Real.log n) + 3 * (middleXiMass Q a d).re -
          6 * (middleMassExtension Q a (d + 2) ((1 / 2 : ℝ) : ℂ)).re +
        2 * (∑' j : { j : ℕ // ⌊X⌋₊ < j }, (3 - τ j.val) * W j.val) := by
  intro χ₁ χ₂ χ₃ τ W
  obtain ⟨h₁, h₂, h₃, hc₁, hc₂, hc₃, hs⟩ :=
    pair_data_of_uniform_pass hn ho hu hprod hp hq hr X hpass
  have e₁ := middle_mass_even_real Q a ha hd hQ h₁ hGRH hc₁.1 hc₁.2.1 hc₁.2.2.1 hc₁.2.2.2
  have e₂ := middle_mass_even_real Q a ha hd hQ h₂ hGRH hc₂.1 hc₂.2.1 hc₂.2.2.1 hc₂.2.2.2
  have e₃ := middle_mass_even_real Q a ha hd hQ h₃ hGRH hc₃.1 hc₃.2.1 hc₃.2.2.1 hc₃.2.2.2
  dsimp only at e₁ e₂ e₃
  rw [middle_mass_deficit_tail Q a d χ₁ hX (fun l hl h ↦ (hs l hl h).1)] at e₁
  rw [middle_mass_deficit_tail Q a d χ₂ hX (fun l hl h ↦ (hs l hl h).2.1)] at e₂
  rw [middle_mass_deficit_tail Q a d χ₃ hX (fun l hl h ↦ (hs l hl h).2.2)] at e₃
  have htrace := middle_mass_trace_sum Q a d ha χ₁ χ₂ χ₃ X
  dsimp only [τ, W] at htrace ⊢
  rw [← htrace]
  dsimp only at e₁ e₂ e₃
  linear_combination e₁ + e₂ + e₃ + middleMassProfile Q a d 1 * pair_level_log_sum hprod

/-- Under passage, the three signed zero contributions are bounded by the
normalized conductor, principal mass, half-point term and signed Euler tail. -/
public theorem middle_pair_zero_mass_upper (Q : Polynomial ℚ) (a : ℚ) {d : ℕ} (ha : 2 ≤ (a : ℝ))
    (hd : 1 ≤ d) (hQ : Q.natDegree ≤ d) {κ : ℝ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n p q r : ℕ} [NeZero p]
    [NeZero q] [NeZero r] [NeZero n] [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)]
    [Fact (2 < q)] [Fact (2 < r)] (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hprod : n = p * q * r) (hp : Odd p) (hq : Odd q) (hr : Odd r) (b : ℝ) {X : ℝ} (hX : 0 < X)
    (hκ : 0 ≤ κ)
    (hpass : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → PrimeTest.StrongMillerRabinPass n (l : ZMod n)) :
    let χ₁ := NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq)
    let χ₂ := NumberTheory.complexJacobiNumeratorCharacter (p * r) (hp.mul hr)
    let χ₃ := NumberTheory.complexJacobiNumeratorCharacter (q * r) (hq.mul hr)
    let τ := fun j : ℕ ↦ (χ₁ j).re + (χ₂ j).re + (χ₃ j).re
    let W := fun j : ℕ ↦ ArithmeticFunction.vonMangoldt j / Real.sqrt j * middleMassProfile Q a d j
    let ha' : 1 / 2 < (a : ℝ) := (by norm_num only : (1 / 2 : ℝ) < 2).trans_le ha
    let K := fun i : ℕ ↦ LLS.PaperStatements.shiftedPoleKernel (max 1 i) a b (le_max_left _ _) ha'
    let Z := fun {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) ↦
      -((κ : ℂ) *
            (∑' ρ : ℂ,
              ∑ i ∈ Finset.Ico 3 (2 * (d + 2)),
                ((Q ^ 2).coeff (2 * (d + 2) - 1 - i) : ℂ) * (K i).oscillatingZeroTerm χ X ρ)).re
    Z χ₁ + Z χ₂ + Z χ₃ ≤
      κ *
        (middleMassProfile Q a d 1 * (2 * Real.log n) + 3 * (middleXiMass Q a d).re -
            6 * (middleMassExtension Q a (d + 2) ((1 / 2 : ℝ) : ℂ)).re +
          2 * (∑' j : { j : ℕ // ⌊X⌋₊ < j }, (3 - τ j.val) * W j.val)) := by
  intro χ₁ χ₂ χ₃ τ W ha' K Z
  obtain ⟨h₁, h₂, h₃, hc₁, hc₂, hc₃, _⟩ := pair_data_of_uniform_pass hn ho hu hprod hp hq hr X hpass
  have hdeg : 2 * Q.natDegree + 3 ≤ 2 * (d + 2) - 1 := by
    rw [Nat.mul_add, show 2 * 2 = 4 from rfl, ← Nat.add_sub_assoc (by decide : 1 ≤ 4)]
    exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 hQ) 3
  have e₁ : Z χ₁ ≤ κ * middleZeroMass Q a (d + 2) χ₁ :=
    middle_signed_zero_le_extension Q hdeg ha' b h₁ hGRH hc₁.1 hc₁.2.1 (hc₁.2.2.1.symm ▸ hc₁.2.1) hX
      hκ
  have e₂ : Z χ₂ ≤ κ * middleZeroMass Q a (d + 2) χ₂ :=
    middle_signed_zero_le_extension Q hdeg ha' b h₂ hGRH hc₂.1 hc₂.2.1 (hc₂.2.2.1.symm ▸ hc₂.2.1) hX
      hκ
  have e₃ : Z χ₃ ≤ κ * middleZeroMass Q a (d + 2) χ₃ :=
    middle_signed_zero_le_extension Q hdeg ha' b h₃ hGRH hc₃.1 hc₃.2.1 (hc₃.2.2.1.symm ▸ hc₃.2.1) hX
      hκ
  have h := middle_three_mass Q a ha hd hQ hGRH hn ho hu hprod hp hq hr hX.le hpass
  have hupper := add_le_add (add_le_add e₁ e₂) e₃
  rw [← mul_add, ← mul_add, h] at hupper
  exact hupper

end PseudoPrime.PrimeTestBounds.MillerRabin
