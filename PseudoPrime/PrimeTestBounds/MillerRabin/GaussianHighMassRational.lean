/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighMassCoefficients
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighKernelData
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighMassCoefficients
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighMassPolynomial
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianOppositeCoeffFast

/-! # Rational coefficient evaluation for the high Gaussian mass -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational coefficient recurrence for the even and odd parts of one power. -/
private def partCoeff (a : ℚ) : ℕ → ℕ → ℚ × ℚ
  | 0, i => (if i = 0 then 1 else 0, 0)
  | k + 1, i =>
    let (A, B) := partCoeff a k i
    let T := if 1 ≤ i then (partCoeff a k (i - 1)).2 else 0
    (a * A + (a ^ 2 * B - T), A + a * B)

/-- The two scalar recurrences reproduce the polynomial coefficients. -/
private theorem part_coeff_eq (a : ℚ) (k i : ℕ) :
    ((powerParts a k).1.coeff i, (powerParts a k).2.coeff i) = partCoeff a k i := by
  induction k generalizing i with
  | zero => simp only [powerParts, partCoeff, Polynomial.coeff_one, Polynomial.coeff_zero]
  | succ k ih =>
    rcases h : powerParts a k with ⟨A, B⟩
    have ih₁ (j : ℕ) := congrArg Prod.fst (ih j)
    have ih₂ (j : ℕ) := congrArg Prod.snd (ih j)
    simp only [h] at ih₁ ih₂
    rw [powerParts, h, partCoeff]
    rcases hr : partCoeff a k i with ⟨x, y⟩
    have hx := Polynomial.coeff_X_pow_mul' B 1 i
    simp only [pow_one] at hx
    dsimp only
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, sub_mul, Polynomial.coeff_sub, hx, ih₁,
      ih₂, hr]

/-- Each row stores the two coefficients at every index below the chosen width. -/
private def partRow (a : ℚ) (width : ℕ) : ℕ → Array (ℚ × ℚ)
  | 0 => Array.ofFn (fun i : Fin width ↦ (if i.val = 0 then 1 else 0, 0))
  | k + 1 =>
    let prev := partRow a width k
    Array.ofFn
      (fun i : Fin width ↦
        let (A, B) := prev[i.val]?.getD (0, 0)
        let T := if 1 ≤ i.val then (prev[i.val - 1]?.getD (0, 0)).2 else 0
        (a * A + (a ^ 2 * B - T), A + a * B))

/-- Every stored entry agrees with the scalar recurrence. -/
private theorem part_row_eq (a : ℚ) (width k i : ℕ) (hi : i < width) :
    (partRow a width k)[i]?.getD (0, 0) = partCoeff a k i := by
  induction k generalizing i with
  | zero => simp only [partRow, partCoeff, Array.getElem?_ofFn, dite_eq_left hi, Option.getD_some]
  | succ k ih =>
    simp only [partRow, partCoeff, Array.getElem?_ofFn, dite_eq_left hi, Option.getD_some, ih i hi,
      ih (i - 1) ((Nat.sub_le i 1).trans_lt hi)]

/-- Coefficients of the two parts of the compact numerator at the pole location. -/
private def numeratorPartCoeff (K : HighGaussianKernel) (i : ℕ) : ℚ × ℚ :=
  (∑ k ∈ Finset.range (K.degree + 1),
      compactCoeff K k * ((partRow K.pole (i + 1) k)[i]?.getD (0, 0)).1,
    ∑ k ∈ Finset.range (K.degree + 1),
      compactCoeff K k * ((partRow K.pole (i + 1) k)[i]?.getD (0, 0)).2)

/-- Changing from the actual degree to the prescribed degree adds only zero coefficients. -/
private theorem compact_sum_range (K : HighGaussianKernel) (f : ℕ → ℚ) :
    (∑ k ∈ Finset.range (K.polynomial.natDegree + 1), K.polynomial.coeff k * f k) =
      ∑ k ∈ Finset.range (K.degree + 1), compactCoeff K k * f k := by
  simp only [← compact_coeff_eq]
  apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ (high_gaussian_polynomial_degree K)))
  intro k _ hk
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt
      (Nat.lt_of_succ_le (Nat.le_of_not_gt (fun h ↦ hk (Finset.mem_range.mpr h)))),
    zero_mul]

/-- The compact numerator parts have the computed rational coefficients. -/
private theorem numerator_part_coeff_eq (K : HighGaussianKernel) (i : ℕ) :
    let AB := polynomialParts K.pole K.polynomial
    (AB.1.coeff i, AB.2.coeff i) = numeratorPartCoeff K i := by
  simp only [polynomialParts, numeratorPartCoeff, Polynomial.finsetSum_coeff,
    Polynomial.coeff_C_mul, part_row_eq _ _ _ _ (Nat.lt_succ_self i)]
  apply Prod.ext
  · have h (k : ℕ) : (powerParts K.pole k).1.coeff i = (partCoeff K.pole k i).1 :=
      congrArg Prod.fst (part_coeff_eq K.pole k i)
    simp only [h]
    exact compact_sum_range K _
  · have h (k : ℕ) : (powerParts K.pole k).2.coeff i = (partCoeff K.pole k i).2 :=
      congrArg Prod.snd (part_coeff_eq K.pole k i)
    simp only [h]
    exact compact_sum_range K _

/-- The rational coefficient of the squared absolute numerator is a convolution
of the two numerator parts and the factor `u - a²`. -/
private def normNumeratorCoeff (K : HighGaussianKernel) (i : ℕ) : ℚ :=
  let A := fun j ↦ (numeratorPartCoeff K j).1
  let B := fun j ↦ (numeratorPartCoeff K j).2
  let conv := fun (f : ℕ → ℚ) j ↦ ∑ v ∈ Finset.antidiagonal j, f v.1 * f v.2
  conv A i + ((if 1 ≤ i then conv B (i - 1) else 0) - K.pole ^ 2 * conv B i)

/-- Coefficient extraction from the squared-norm polynomial agrees with rational convolution. -/
private theorem norm_numerator_coeff_eq (K : HighGaussianKernel) (i : ℕ) :
    (normSqPolynomial K.pole K.polynomial).coeff i = normNumeratorCoeff K i := by
  let AB := polynomialParts K.pole K.polynomial
  have h₁ (j : ℕ) : AB.1.coeff j = (numeratorPartCoeff K j).1 :=
    congrArg Prod.fst (numerator_part_coeff_eq K j)
  have h₂ (j : ℕ) : AB.2.coeff j = (numeratorPartCoeff K j).2 :=
    congrArg Prod.snd (numerator_part_coeff_eq K j)
  change (AB.1 ^ 2 + (Polynomial.X - Polynomial.C (K.pole ^ 2)) * AB.2 ^ 2).coeff i = _
  have hx := Polynomial.coeff_X_pow_mul' (AB.2 ^ 2) 1 i
  simp only [pow_one] at hx
  rw [Polynomial.coeff_add, sub_mul, Polynomial.coeff_sub, hx, Polynomial.coeff_C_mul]
  simp only [normNumeratorCoeff, pow_two, Polynomial.coeff_mul, h₁, h₂]

/-- Build one positive-order row of the balanced-pole coefficient table. -/
private def poleRowStep (a : ℚ) (p j : ℕ) (prev : Array ℚ) : ℕ → Array ℚ
  | 0 => #[if p = j then 2 / (p.factorial : ℚ) else 0]
  | q + 1 =>
    let row := poleRowStep a p j prev q
    let v :=
      if p = 0 ∧ q = 0 then (if j = 0 then 1 / a else 0)
      else (1 / (2 * a)) * (prev[q + 1]?.getD 0 + row[q]?.getD 0)
    row.push v

/-- The row has one entry for every column index at most its last column. -/
private theorem pole_row_step_size (a : ℚ) (p j : ℕ) (prev : Array ℚ) (q : ℕ) :
    (poleRowStep a p j prev q).size = q + 1 := by
  induction q with
  | zero => rfl
  | succ q ih => simp only [poleRowStep, Array.size_push, ih]

/-- Row construction reproduces the rational recurrence below the column limit. -/
private theorem pole_row_step_eq (a : ℚ) (p j : ℕ) (prev : Array ℚ) (Q : ℕ)
    (hprev : ∀ q ≤ Q, prev[q]?.getD 0 = oppositePoleCoeff a p q j) (q : ℕ) (hq : q ≤ Q) :
    (poleRowStep a p j prev Q)[q]?.getD 0 = oppositePoleCoeff a (p + 1) q j := by
  induction Q generalizing q with
  | zero =>
    have hz := Nat.eq_zero_of_le_zero hq
    subst q
    simp only [poleRowStep, oppositePoleCoeff]
    rfl
  | succ Q
    ih =>
    have ht : ∀ k ≤ Q, prev[k]?.getD 0 = oppositePoleCoeff a p k j := fun k hk ↦
      hprev k (hk.trans (Nat.le_succ Q))
    rw [poleRowStep, Array.getElem?_push, pole_row_step_size]
    rcases lt_or_eq_of_le hq with hlt | he
    · simpa only [ite_eq_right hlt.ne] using ih ht q (Nat.lt_succ_iff.mp hlt)
    subst q
    simp only [ite_true, Option.getD_some]
    by_cases hh : p = 0 ∧ Q = 0
    · rcases hh with ⟨hp, hQ⟩
      subst p
      subst Q
      simp only [ite_true, and_self]
      change _ = oppositePoleCoeff a 1 1 j
      rw [oppositePoleCoeff.eq_3]
    have hne : p = 0 → Q = 0 → False := fun hp hQ ↦ hh ⟨hp, hQ⟩
    rw [ite_eq_right hh, oppositePoleCoeff.eq_4 a j p Q hne, hprev (Q + 1) le_rfl, ih ht Q le_rfl]

/-- A table row for any positive or zero first pole order. -/
private def poleRow (a : ℚ) (j Q : ℕ) : ℕ → Array ℚ
  | 0 => Array.replicate (Q + 1) 0
  | p + 1 => poleRowStep a p j (poleRow a j Q p) Q

/-- Bounded lookup gives the exact mixed-pole coefficient. -/
private theorem pole_row_eq (a : ℚ) (j Q p q : ℕ) (hq : q ≤ Q) :
    (poleRow a j Q p)[q]?.getD 0 = oppositePoleCoeff a p q j := by
  induction p generalizing q with
  | zero =>
    have hlt := Nat.lt_succ_of_le hq
    simp only [poleRow, Array.getElem?_replicate, ite_eq_left hlt, Option.getD_some,
      oppositePoleCoeff]
  | succ p ih =>
    apply pole_row_step_eq a p j (poleRow a j Q p) Q _ q hq
    exact fun k hk ↦ ih k hk

/-- The mass coefficient uses only the compact rational coefficient computations and
the opposite-pole scalar recurrence. -/
public def computedMassCoeff (K : HighGaussianKernel) (i : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (K.degree + 1),
    (K.normalization * normNumeratorCoeff K j) *
      (poleRow K.pole i (K.degree + 2 - j) (K.degree + 2 - j))[K.degree + 2 - j]?.getD 0

/-- The rational coefficient evaluator agrees with the Fourier mass polynomial. -/
public theorem high_mass_coeff_rational (K : HighGaussianKernel) (i : ℕ) :
    (highGaussianMassPolynomial K).coeff i = computedMassCoeff K i := by
  simp only [high_mass_coeff_sum, norm_numerator_coeff_eq, computedMassCoeff,
    pole_row_eq _ _ _ _ _ le_rfl]

/-- Translate the computed mass coefficients by a rational shift. -/
public def computedShiftedMassCoeff (K : HighGaussianKernel) (b : ℚ) (i : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (K.degree + 2), computedMassCoeff K j * ((j.choose i : ℚ) * b ^ (j - i))

/-- Rational translation computes the coefficients used in the tail certificate. -/
public theorem high_shifted_mass_coeff_rational (K : HighGaussianKernel) (b : ℚ) (i : ℕ) :
    ((highGaussianMassPolynomial K).comp (Polynomial.X + Polynomial.C b)).coeff i =
      computedShiftedMassCoeff K b i := by
  simp only [high_mass_shifted_coeff_sum, high_mass_coeff_rational, computedShiftedMassCoeff]

/-- Store all rows of a recurrence, using only the immediately preceding row at each step. -/
private def recurrenceRows {α : Type} (start fallback : α) (step : ℕ → α → α) : ℕ → Array α
  | 0 => #[start]
  | n + 1 =>
    let rows := recurrenceRows start fallback step n
    rows.push (step n (rows[n]?.getD fallback))

/-- The table stores exactly one entry for each index up to its last index. -/
private theorem recurrence_rows_size {α : Type} (start fallback : α) (step : ℕ → α → α) (n : ℕ) :
    (recurrenceRows start fallback step n).size = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [recurrenceRows, Array.size_push, ih]

/-- The table agrees with any sequence satisfying its initialization and step equations. -/
private theorem recurrence_rows_eq {α : Type} (start fallback : α) (step : ℕ → α → α) (f : ℕ → α)
    (h0 : f 0 = start) (hs : ∀ n, f (n + 1) = step n (f n)) (N i : ℕ) (hi : i ≤ N) :
    (recurrenceRows start fallback step N)[i]?.getD fallback = f i := by
  induction N generalizing i with
  | zero =>
    have hz := Nat.eq_zero_of_le_zero hi
    subst i
    exact h0.symm
  | succ N ih =>
    rw [recurrenceRows, Array.getElem?_push, recurrence_rows_size]
    rcases lt_or_eq_of_le hi with hlt | he
    · simpa only [ite_eq_right hlt.ne] using ih i (Nat.lt_succ_iff.mp hlt)
    subst i
    simp only [ite_true, Option.getD_some, ih N le_rfl, hs]

/-- Store all powers of the compact numerator's two coefficient parts. -/
private def allPartRows (K : HighGaussianKernel) (width : ℕ) : Array (Array (ℚ × ℚ)) :=
  recurrenceRows (partRow K.pole width 0) #[]
    (fun _ prev ↦
      Array.ofFn
        (fun i : Fin width ↦
          let (A, B) := prev[i.val]?.getD (0, 0)
          let T := if 1 ≤ i.val then (prev[i.val - 1]?.getD (0, 0)).2 else 0
          (K.pole * A + (K.pole ^ 2 * B - T), A + K.pole * B)))
    K.degree

/-- An entry of the shared table gives the same two coefficients. -/
private theorem all_part_rows_eq (K : HighGaussianKernel) (width k : ℕ) (hk : k ≤ K.degree) :
    (allPartRows K width)[k]?.getD #[] = partRow K.pole width k := by
  unfold allPartRows
  exact recurrence_rows_eq _ _ _ (partRow K.pole width) rfl (fun _ ↦ rfl) K.degree k hk

/-- Evaluate both numerator parts for all coefficient indices needed in the mass. -/
private def numeratorPartsTable (K : HighGaussianKernel) : Array (ℚ × ℚ) :=
  let rows := allPartRows K (K.degree + 1)
  let cf := Array.ofFn (fun k : Fin (K.degree + 1) ↦ compactCoeff K k.val)
  Array.ofFn
    (fun i : Fin (K.degree + 1) ↦
      (∑ k ∈ Finset.range (K.degree + 1),
          cf[k]?.getD 0 * (((rows[k]?.getD #[])[i.val]?).getD (0, 0)).1,
        ∑ k ∈ Finset.range (K.degree + 1),
          cf[k]?.getD 0 * (((rows[k]?.getD #[])[i.val]?).getD (0, 0)).2))

/-- Shared numerator computation agrees with the scalar numerator calculation. -/
private theorem numerator_parts_table_eq (K : HighGaussianKernel) (i : ℕ) (hi : i ≤ K.degree) :
    (numeratorPartsTable K)[i]?.getD (0, 0) = numeratorPartCoeff K i := by
  have h (k : ℕ) (hk : k ∈ Finset.range (K.degree + 1)) :
    (allPartRows K (K.degree + 1))[k]?.getD #[] = partRow K.pole (K.degree + 1) k :=
    all_part_rows_eq K _ k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
  simp only [numeratorPartsTable, Array.getElem?_ofFn, dite_eq_left (Nat.lt_succ_of_le hi),
    Option.getD_some, numeratorPartCoeff]
  apply Prod.ext
  · dsimp only
    apply Finset.sum_congr rfl
    intro k hk
    rw [dite_eq_left (Finset.mem_range.mp hk), Option.getD_some, h k hk,
      part_row_eq _ _ _ _ (Nat.lt_succ_of_le hi), part_row_eq _ _ _ _ (Nat.lt_succ_self i)]
  · dsimp only
    apply Finset.sum_congr rfl
    intro k hk
    rw [dite_eq_left (Finset.mem_range.mp hk), Option.getD_some, h k hk,
      part_row_eq _ _ _ _ (Nat.lt_succ_of_le hi), part_row_eq _ _ _ _ (Nat.lt_succ_self i)]

/-- All needed coefficients of the squared numerator share the same two input arrays. -/
private def numeratorNormTable (K : HighGaussianKernel) : Array ℚ :=
  let parts := numeratorPartsTable K
  let A := fun j ↦ (parts[j]?.getD (0, 0)).1
  let B := fun j ↦ (parts[j]?.getD (0, 0)).2
  let conv := fun (f : ℕ → ℚ) j ↦ ∑ v ∈ Finset.antidiagonal j, f v.1 * f v.2
  Array.ofFn
    (fun i : Fin (K.degree + 1) ↦
      conv A i.val + ((if 1 ≤ i.val then conv B (i.val - 1) else 0) - K.pole ^ 2 * conv B i.val))

/-- Bounded convolution only reads valid coefficient entries. -/
private theorem convolution_congr {n : ℕ} {f g : ℕ → ℚ} (h : ∀ j ≤ n, f j = g j) :
    (∑ v ∈ Finset.antidiagonal n, f v.1 * f v.2) = ∑ v ∈ Finset.antidiagonal n, g v.1 * g v.2 := by
  apply Finset.sum_congr rfl
  intro v hv
  have he := Finset.mem_antidiagonal.mp hv
  rw [h v.1 ((Nat.le_add_right _ _).trans_eq he), h v.2 ((Nat.le_add_left _ _).trans_eq he)]

/-- The batched squared numerator computes the corresponding scalar coefficients. -/
private theorem numerator_norm_table_eq (K : HighGaussianKernel) (i : ℕ) (hi : i ≤ K.degree) :
    (numeratorNormTable K)[i]?.getD 0 = normNumeratorCoeff K i := by
  have ha (j : ℕ) (hj : j ≤ K.degree) :
    ((numeratorPartsTable K)[j]?.getD (0, 0)).1 = (numeratorPartCoeff K j).1 :=
    congrArg Prod.fst (numerator_parts_table_eq K j hj)
  have hb (j : ℕ) (hj : j ≤ K.degree) :
    ((numeratorPartsTable K)[j]?.getD (0, 0)).2 = (numeratorPartCoeff K j).2 :=
    congrArg Prod.snd (numerator_parts_table_eq K j hj)
  simp only [numeratorNormTable, Array.getElem?_ofFn, dite_eq_left (Nat.lt_succ_of_le hi),
    Option.getD_some, normNumeratorCoeff]
  rw [convolution_congr (fun j hj ↦ ha j (hj.trans hi)),
    convolution_congr (fun j hj ↦ hb j (hj.trans ((Nat.sub_le i 1).trans hi))),
    convolution_congr (fun j hj ↦ hb j (hj.trans hi))]

/-- Compute all mass coefficients from the shared numerator and binomial pole coefficients. -/
private def massCoeffTable (K : HighGaussianKernel) : Array ℚ :=
  let numer := numeratorNormTable K
  let Q := K.degree + 2
  Array.ofFn
    (fun i : Fin Q ↦
      ∑ j ∈ Finset.range (K.degree + 1),
        let m := Q - j
        (K.normalization * numer[j]?.getD 0) * oppositeCoeffFast K.pole m m i.val)

/-- The mass table gives every relevant coefficient of the formal polynomial. -/
private theorem mass_coeff_table_eq (K : HighGaussianKernel) (i : ℕ) (hi : i < K.degree + 2) :
    (massCoeffTable K)[i]?.getD 0 = (highGaussianMassPolynomial K).coeff i := by
  rw [high_mass_coeff_rational]
  simp only [massCoeffTable, Array.getElem?_ofFn, dite_eq_left hi, Option.getD_some,
    computedMassCoeff]
  apply Finset.sum_congr rfl
  intro j hj
  rw [numerator_norm_table_eq K j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)),
    oppositeCoeffFast_eq, pole_row_eq _ _ _ _ _ le_rfl]

/-- All translated coefficients share the same unshifted mass table. -/
private def shiftedMassCoeffTable (K : HighGaussianKernel) (b : ℚ) : Array ℚ :=
  let mass := massCoeffTable K
  Array.ofFn
    (fun i : Fin (K.degree + 2) ↦
      ∑ j ∈ Finset.range (K.degree + 2),
        mass[j]?.getD 0 * ((Nat.fast_choose j i.val : ℚ) * b ^ (j - i.val)))

/-- The translated coefficient table agrees with polynomial translation. -/
private theorem shifted_mass_coeff_table_eq (K : HighGaussianKernel) (b : ℚ) (i : ℕ)
    (hi : i < K.degree + 2) :
    (shiftedMassCoeffTable K b)[i]?.getD 0 =
      ((highGaussianMassPolynomial K).comp (Polynomial.X + Polynomial.C b)).coeff i := by
  rw [high_mass_shifted_coeff_sum]
  simp only [shiftedMassCoeffTable, Array.getElem?_ofFn, dite_eq_left hi, Option.getD_some]
  apply Finset.sum_congr rfl
  intro j hj
  rw [mass_coeff_table_eq K j (Finset.mem_range.mp hj), ← Nat.choose_eq_fast_choose]

/-- Test the signs of all shifted mass coefficients with the shared rational tables. -/
public def massShiftAllNonpos (K : HighGaussianKernel) (b : ℚ) : Bool :=
  (shiftedMassCoeffTable K b).all (fun x ↦ decide (x ≤ 0))

/-- Kernel reduction verifies the signs of the translated K196 mass coefficients. -/
public theorem k196_mass_sign_check : massShiftAllNonpos .k196 (75 / 2) = true := by
  unfold massShiftAllNonpos
  rw [← Array.all_toList]
  decide +kernel

/-- A successful batched sign check certifies every translated coefficient in range. -/
public theorem shifted_mass_coeff_check (K : HighGaussianKernel) (b : ℚ)
    (h : massShiftAllNonpos K b = true) {i : ℕ} (hi : i < K.degree + 2) :
    ((highGaussianMassPolynomial K).comp (Polynomial.X + Polynomial.C b)).coeff i ≤ 0 := by
  have hs : (shiftedMassCoeffTable K b).size = K.degree + 2 := by
    simp only [shiftedMassCoeffTable, Array.size_ofFn]
  have hi' : i < (shiftedMassCoeffTable K b).size := hs.symm ▸ hi
  rw [← shifted_mass_coeff_table_eq K b i hi, Array.getElem?_eq_getElem hi', Option.getD_some]
  have hb : (shiftedMassCoeffTable K b).all (fun x ↦ decide (x ≤ 0)) = true := h
  exact of_decide_eq_true (Array.all_eq_true.mp hb i hi')

/-- A successful K196 table check supplies all coefficient signs required by
the Euler tail theorem, including zero coefficients beyond the degree bound. -/
public theorem k196_coeff_nonpos_of_check (h : massShiftAllNonpos .k196 (75 / 2) = true) :
    ∀ i,
      ((highGaussianMassPolynomial .k196).comp (Polynomial.X + Polynomial.C (75 / 2))).coeff i ≤
        0 := by
  apply k196_shifted_coeff_nonpos
  intro i hi
  exact shifted_mass_coeff_check .k196 (75 / 2) h (Finset.mem_range.mp hi)

/-- Every translated coefficient is read from the table, with out-of-range entries equal to zero. -/
private theorem shifted_mass_entry (K : HighGaussianKernel) (b : ℚ) (i : ℕ) :
    (shiftedMassCoeffTable K b)[i]?.getD 0 =
      ((highGaussianMassPolynomial K).comp (Polynomial.X + Polynomial.C b)).coeff i := by
  by_cases hi : i < K.degree + 2
  · exact shifted_mass_coeff_table_eq K b i hi
  · have h : K.degree + 2 ≤ i := Nat.le_of_not_gt hi
    have hs : (shiftedMassCoeffTable K b).size ≤ i := by
      simpa only [shiftedMassCoeffTable, Array.size_ofFn] using h
    rw [Array.getElem?_eq_none hs, Option.getD_none]
    exact
      (Polynomial.coeff_eq_zero_of_natDegree_lt
          ((high_mass_shifted_degree K b).trans_lt (Nat.lt_of_succ_le h))).symm

/-- Test both K186 polynomials using their common table of translated mass coefficients. -/
private def k186PositiveCheck : Bool :=
  let q := shiftedMassCoeffTable .k186 30
  (List.range 42).all
    (fun i ↦
      decide (0 ≤ q[i]?.getD 0) &&
        decide (0 ≤ (13 / 4 : ℚ) * q[i]?.getD 0 - ((i + 1 : ℕ) : ℚ) * q[i + 1]?.getD 0))

/-- At the translation point, both K186 polynomials have nonnegative rational coefficients
if their shared sign check passes. -/
private theorem k186_coeffs_of_check (h : k186PositiveCheck = true) (i : ℕ) :
    let Q := (highGaussianMassPolynomial .k186).comp (Polynomial.X + Polynomial.C 30)
    0 ≤ Q.coeff i ∧ 0 ≤ (Polynomial.C (13 / 4) * Q - Q.derivative).coeff i := by
  intro Q
  rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_derivative,
    mul_comm (Q.coeff (i + 1))]
  by_cases hi : i < 42
  · have hc := (List.all_eq_true.mp h) i (List.mem_range.mpr hi)
    have hc' := Bool.and_eq_true_iff.mp hc
    have h1 := of_decide_eq_true hc'.1
    have h2 := of_decide_eq_true hc'.2
    simp only [shifted_mass_entry, Nat.cast_add, Nat.cast_one] at h1 h2
    exact ⟨h1, h2⟩
  · have hdeg : Q.natDegree ≤ 41 := high_mass_shifted_degree .k186 30
    have hi' : Q.natDegree < i := hdeg.trans_lt (Nat.lt_of_succ_le (Nat.le_of_not_gt hi))
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hi',
      Polynomial.coeff_eq_zero_of_natDegree_lt (hi'.trans (Nat.lt_succ_self i)), mul_zero, mul_zero,
      sub_zero]
    exact ⟨le_rfl, le_rfl⟩

/-- Direct kernel computation checks both coefficient lists at cutoff 30. -/
private theorem k186_positive_check : k186PositiveCheck = true := by decide +kernel

/-- Nonnegative coefficients after translation imply nonnegative evaluation
at any real argument at or above the translation point. -/
private theorem shifted_mass_eval_nonneg (P : Polynomial ℚ) (b : ℚ)
    (h : ∀ i, 0 ≤ (P.comp (Polynomial.X + Polynomial.C b)).coeff i) {z : ℝ} (hz : (b : ℝ) ≤ z) :
    0 ≤ P.eval₂ (Rat.castHom ℝ) z := by
  let Q := P.comp (Polynomial.X + Polynomial.C b)
  have he : Q.eval₂ (Rat.castHom ℝ) (z - (b : ℝ)) = P.eval₂ (Rat.castHom ℝ) z := by
    unfold Q
    rw [Polynomial.eval₂_comp]
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_X, Polynomial.eval₂_C, Rat.coe_castHom,
      sub_add_cancel]
  rw [← he, Polynomial.eval₂_eq_sum_range]
  exact
    Finset.sum_nonneg
      (fun i _ ↦
        mul_nonneg (by simpa only [Rat.coe_castHom] using (Rat.cast_nonneg.mpr (h i) : (0 : ℝ) ≤ _))
          (pow_nonneg (sub_nonneg.mpr hz) i))

/-- Both K186 polynomials required by H18 are nonnegative on the entire tail from 30. -/
public theorem k186_mass_poly_signs {z : ℝ} (hz : 30 ≤ z) :
    let P := highGaussianMassPolynomial .k186
    0 ≤ P.eval₂ (Rat.castHom ℝ) z ∧
      0 ≤ (Polynomial.C (13 / 4) * P - P.derivative).eval₂ (Rat.castHom ℝ) z := by
  intro P
  have hz' : ((30 : ℚ) : ℝ) ≤ z := by simpa only [Rat.cast_ofNat] using hz
  refine
    ⟨shifted_mass_eval_nonneg P 30 (fun i ↦ (k186_coeffs_of_check k186_positive_check i).1) hz',
      shifted_mass_eval_nonneg _ 30 (fun i ↦ ?_) hz'⟩
  simp only [Polynomial.sub_comp, Polynomial.mul_comp, Polynomial.C_comp]
  have hd :
    (P.comp (Polynomial.X + Polynomial.C 30)).derivative =
      P.derivative.comp (Polynomial.X + Polynomial.C 30) := by
    rw [Polynomial.derivative_comp, Polynomial.derivative_add, Polynomial.derivative_X,
      Polynomial.derivative_C, add_zero, one_mul]
  rw [← hd]
  exact (k186_coeffs_of_check k186_positive_check i).2

end PseudoPrime.PrimeTestBounds.MillerRabin
