/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import PseudoPrime.PrimeTest.APRCL.Parameters

/-!
# Prime-power cyclotomic polynomials for APR-CL

This file fixes the prime-power parameters and connects the explicit geometric-sum polynomial to
Mathlib's cyclotomic polynomial. The quotient by that polynomial is the abstract ring model for
the later coefficient-array implementation.
-/

namespace PseudoPrime.PrimeTest.APRCL

noncomputable section

/-- The cyclotomic index `p^(k+1)` used for a prime `p` and positive exponent. -/
def primePowerIndex (p k : ℕ) : ℕ :=
  p ^ (k + 1)

/-- The geometric step `p^k` in the explicit formula for `Φ_(p^(k+1))`. -/
def primePowerStep (p k : ℕ) : ℕ :=
  p ^ k

/-- The degree parameter `(p - 1) * p^k` for `Φ_(p^(k+1))`. -/
def primePowerDegree (p k : ℕ) : ℕ :=
  (p - 1) * p ^ k

/-- Explicit geometric-sum polynomial for a prime-power cyclotomic polynomial. -/
def primePowerCyclotomic (p k : ℕ) (R : Type*) [CommRing R] : Polynomial R :=
  ∑ i ∈ Finset.range p, (Polynomial.X ^ p ^ k) ^ i

/-- The explicit geometric sum is Mathlib's cyclotomic polynomial at index `p^(k+1)`. -/
theorem primePowerCyclotomic_eq_cyclotomic {p k : ℕ} (hp : Nat.Prime p) (R : Type*) [CommRing R] :
    primePowerCyclotomic p k R = Polynomial.cyclotomic (primePowerIndex p k) R := by
  rw [primePowerCyclotomic, primePowerIndex, Nat.pow_succ]
  exact (Polynomial.cyclotomic_prime_pow_eq_geom_sum (R := R) hp).symm

/-- The explicit prime-power cyclotomic polynomial is monic. -/
theorem primePowerCyclotomic_monic {p k : ℕ} (hp : Nat.Prime p) (R : Type*) [CommRing R] :
    (primePowerCyclotomic p k R).Monic := by
  rw [primePowerCyclotomic_eq_cyclotomic hp]
  exact Polynomial.cyclotomic.monic _ _

/-- The explicit polynomial has degree `(p - 1) * p^k` over a nontrivial ring. -/
theorem primePowerCyclotomic_natDegree {p k : ℕ} (hp : Nat.Prime p) (R : Type*) [CommRing R]
    [Nontrivial R] : (primePowerCyclotomic p k R).natDegree = primePowerDegree p k := by
  rw [primePowerCyclotomic_eq_cyclotomic hp, Polynomial.natDegree_cyclotomic, primePowerIndex,
    Nat.totient_prime_pow hp (Nat.succ_pos k)]
  simp only [primePowerDegree, Nat.succ_sub_one, Nat.mul_comm]

/-- Abstract quotient ring used to specify the APR-CL coefficient-array operations. -/
abbrev cyclotomicQuotient (n p k : ℕ) :=
  AdjoinRoot (primePowerCyclotomic p k (ZMod n))

/-- The canonical element representing the indeterminate in the cyclotomic quotient. -/
def cyclotomicRoot (n p k : ℕ) : cyclotomicQuotient n p k :=
  AdjoinRoot.root (primePowerCyclotomic p k (ZMod n))

/-- Power basis identifying quotient elements with coefficient vectors of the degree length. -/
def cyclotomicPowerBasis (n p k : ℕ) (hp : Nat.Prime p) :
    PowerBasis (ZMod n) (cyclotomicQuotient n p k) :=
  AdjoinRoot.powerBasis' (primePowerCyclotomic_monic hp (ZMod n))

/-- The power basis length is the explicit prime-power cyclotomic degree. -/
theorem cyclotomicPowerBasis_dim {n : ℕ} (hn : 1 < n) {p k : ℕ} (hp : Nat.Prime p) :
    (cyclotomicPowerBasis n p k hp).dim = primePowerDegree p k := by
  have : Nontrivial (ZMod n) := ZMod.nontrivial_iff.mpr hn.ne'
  rw [cyclotomicPowerBasis, AdjoinRoot.powerBasis'_dim, primePowerCyclotomic_natDegree hp]

/-- Canonical finite array representation indexed by the power-basis interval. -/
def cyclotomicCoefficientEquiv (n p k : ℕ) (hp : Nat.Prime p) :
    cyclotomicQuotient n p k ≃ (Fin (primePowerCyclotomic p k (ZMod n)).natDegree → ZMod n) :=
  (AdjoinRoot.powerBasisAux' (primePowerCyclotomic_monic hp (ZMod n))).repr.toEquiv |>.trans
    Finsupp.equivFunOnFinite

/-- Decoding the canonical coefficient representation recovers the quotient element. -/
theorem cyclotomicCoefficientEquiv_decode_encode (n p k : ℕ) (hp : Nat.Prime p)
    (x : cyclotomicQuotient n p k) :
    (cyclotomicCoefficientEquiv n p k hp).symm (cyclotomicCoefficientEquiv n p k hp x) = x := by
  exact (cyclotomicCoefficientEquiv n p k hp).symm_apply_apply x

/-- Encoding then decoding any finite coefficient vector recovers that vector. -/
theorem cyclotomicCoefficientEquiv_encode_decode (n p k : ℕ) (hp : Nat.Prime p)
    (v : Fin (primePowerCyclotomic p k (ZMod n)).natDegree → ZMod n) :
    cyclotomicCoefficientEquiv n p k hp ((cyclotomicCoefficientEquiv n p k hp).symm v) = v := by
  exact (cyclotomicCoefficientEquiv n p k hp).apply_symm_apply v

/-- Coefficient arrays represent addition in the abstract quotient pointwise. -/
theorem cyclotomicCoefficientEquiv_add (n p k : ℕ) (hp : Nat.Prime p)
    (x y : cyclotomicQuotient n p k) :
    cyclotomicCoefficientEquiv n p k hp (x + y) = fun i =>
      cyclotomicCoefficientEquiv n p k hp x i + cyclotomicCoefficientEquiv n p k hp y i := by
  funext i
  change
    ((AdjoinRoot.powerBasisAux' (primePowerCyclotomic_monic hp (ZMod n))).repr (x + y)) i =
      ((AdjoinRoot.powerBasisAux' (primePowerCyclotomic_monic hp (ZMod n))).repr x) i +
        ((AdjoinRoot.powerBasisAux' (primePowerCyclotomic_monic hp (ZMod n))).repr y) i
  rw [map_add]
  rfl

/-- Coefficient arrays represent subtraction in the abstract quotient pointwise. -/
theorem cyclotomicCoefficientEquiv_sub (n p k : ℕ) (hp : Nat.Prime p)
    (x y : cyclotomicQuotient n p k) :
    cyclotomicCoefficientEquiv n p k hp (x - y) = fun i =>
      cyclotomicCoefficientEquiv n p k hp x i - cyclotomicCoefficientEquiv n p k hp y i := by
  funext i
  change
    ((AdjoinRoot.powerBasisAux' (primePowerCyclotomic_monic hp (ZMod n))).repr (x - y)) i =
      ((AdjoinRoot.powerBasisAux' (primePowerCyclotomic_monic hp (ZMod n))).repr x) i -
        ((AdjoinRoot.powerBasisAux' (primePowerCyclotomic_monic hp (ZMod n))).repr y) i
  rw [map_sub]
  rfl

end

/-- Fixed-size coefficient arrays use the explicit degree, so their length is computational. -/
abbrev cyclotomicFixedArray (n p k : ℕ) :=
  Fin (primePowerDegree p k) → ZMod n

/-- Pointwise addition on fixed-size coefficient arrays. -/
def cyclotomicFixedArrayAdd (n p k : ℕ) (a b : cyclotomicFixedArray n p k) :
    cyclotomicFixedArray n p k := fun i => a i + b i

/-- Pointwise subtraction on fixed-size coefficient arrays. -/
def cyclotomicFixedArraySub (n p k : ℕ) (a b : cyclotomicFixedArray n p k) :
    cyclotomicFixedArray n p k := fun i => a i - b i

/-- Scalar multiplication on fixed-size coefficient arrays. -/
def cyclotomicFixedArrayScale (n p k : ℕ) (c : ZMod n) (a : cyclotomicFixedArray n p k) :
    cyclotomicFixedArray n p k := fun i => c * a i

/-- View a fixed array as a coefficient function on all exponents, extended by zero. -/
def cyclotomicFixedArrayCoeff (n p k : ℕ) (a : cyclotomicFixedArray n p k) (d : ℕ) : ZMod n :=
  if hd : d < primePowerDegree p k then a ⟨d, hd⟩ else 0

/-- Unreduced product coefficients, computed by a finite antidiagonal convolution. -/
def cyclotomicFixedArrayConvolution (n p k : ℕ) (a b : cyclotomicFixedArray n p k) :
    Fin (2 * primePowerDegree p k) → ZMod n := fun e =>
  ∑ ij ∈ Finset.antidiagonal e.val,
    cyclotomicFixedArrayCoeff n p k a ij.1 * cyclotomicFixedArrayCoeff n p k b ij.2

/-- Reduce a monomial exponent into the fixed degree interval using the cyclotomic block relation.
-/
def cyclotomicFixedArrayMonomialReduce (n : ℕ) {p k : ℕ} (hp : Nat.Prime p) (e : ℕ) :
    cyclotomicFixedArray n p k :=
  if _he : e < primePowerDegree p k then fun j => if j.val = e then 1 else 0
  else
    -∑ i : Fin (p - 1),
        cyclotomicFixedArrayMonomialReduce n hp
          (e - primePowerDegree p k + primePowerStep p k * i.val)
termination_by e
decreasing_by
  have hdpos : 0 < p ^ k := Nat.pow_pos hp.pos
  have hi : i.val < p - 1 := i.isLt
  have hblock : i.val * p ^ k < (p - 1) * p ^ k := Nat.mul_lt_mul_of_pos_right hi hdpos
  have hblock' : p ^ k * i.val < (p - 1) * p ^ k := by simpa only [Nat.mul_comm] using hblock
  have hdegree : primePowerDegree p k = (p - 1) * p ^ k := rfl
  have he' : (p - 1) * p ^ k ≤ e := by
    rw [← hdegree]
    exact Nat.le_of_not_gt _he
  change e - ((p - 1) * p ^ k) + p ^ k * i.val < e
  calc
    e - (p - 1) * p ^ k + p ^ k * i.val < e - (p - 1) * p ^ k + (p - 1) * p ^ k :=
      Nat.add_lt_add_left hblock' _
    _ = e := Nat.sub_add_cancel he'

/-- The coefficient vector of a single monomial below the cyclotomic degree. -/
def cyclotomicFixedArrayMonomialUnit (n p k : ℕ) (e : ℕ) : cyclotomicFixedArray n p k := fun j =>
  if j.val = e then 1 else 0

/-- Concrete coefficient-array representation of a fixed-size coefficient vector. -/
def cyclotomicFixedArrayToArray (n p k : ℕ) (a : cyclotomicFixedArray n p k) : Array (ZMod n) :=
  Array.ofFn a

/-- A concrete all-zero coefficient row used for out-of-range table lookups. -/
def cyclotomicFixedArrayZeroRow (n p k : ℕ) : Array (ZMod n) :=
  Array.replicate (primePowerDegree p k) 0

/-- Dynamic-programming table of monomial reductions for all exponents below `count`. -/
def cyclotomicFixedArrayMonomialReduceTableAux (n : ℕ) {p k : ℕ} (hp : Nat.Prime p) :
    ℕ → Array (Array (ZMod n))
  | 0 => #[]
  | count + 1 =>
      let previous := @cyclotomicFixedArrayMonomialReduceTableAux n p k hp count
      let row :=
      if count < primePowerDegree p k then
        cyclotomicFixedArrayToArray n p k (cyclotomicFixedArrayMonomialUnit n p k count)
      else
        Array.ofFn fun j : Fin (primePowerDegree p k) =>
          -∑ i : Fin (p - 1),
              (previous.getD (count - primePowerDegree p k + primePowerStep p k * i.val)
                    (cyclotomicFixedArrayZeroRow n p k)).getD
                j.val 0
      previous.push row
termination_by count => count

/-- Table containing the single-pass reductions of every monomial used by multiplication. -/
def cyclotomicFixedArrayMonomialReduceTable (n : ℕ) {p k : ℕ} (hp : Nat.Prime p) :
    Array (Array (ZMod n)) :=
  @cyclotomicFixedArrayMonomialReduceTableAux n p k hp (2 * primePowerDegree p k)

/-- Materialized output of the fixed-array multiplication. -/
def cyclotomicFixedArrayMulByTableArray (n : ℕ) {p k : ℕ} (hp : Nat.Prime p)
    (a b : cyclotomicFixedArray n p k) : Array (ZMod n) :=
  let table := cyclotomicFixedArrayMonomialReduceTable n (p := p) (k := k) hp
  let convolution := Array.ofFn (cyclotomicFixedArrayConvolution n p k a b)
  Array.ofFn fun j : Fin (primePowerDegree p k) =>
    ∑ e : Fin (2 * primePowerDegree p k),
      (convolution.getD e.val 0) *
        ((table.getD e.val (cyclotomicFixedArrayZeroRow n p k)).getD j.val 0)

/-- Fixed-array multiplication constructs its reduction table and output coefficients once. -/
def cyclotomicFixedArrayMulByTable (n : ℕ) {p k : ℕ} (hp : Nat.Prime p)
    (a b : cyclotomicFixedArray n p k) : cyclotomicFixedArray n p k :=
  let result := cyclotomicFixedArrayMulByTableArray n hp a b
  fun j => result.getD j.val 0

/-- A materialized multiplication coefficient is the specified finite weighted sum. -/
theorem cyclotomicFixedArrayMulByTableArray_getD (n : ℕ) {p k : ℕ} (hp : Nat.Prime p)
    (a b : cyclotomicFixedArray n p k) (j : Fin (primePowerDegree p k)) :
    (cyclotomicFixedArrayMulByTableArray n hp a b).getD j.val 0 =
      ∑ e : Fin (2 * primePowerDegree p k),
        cyclotomicFixedArrayConvolution n p k a b e *
          (((cyclotomicFixedArrayMonomialReduceTable n (p := p) (k := k) hp).getD e.val
                (cyclotomicFixedArrayZeroRow n p k)).getD
            j.val 0) := by
  simp only [cyclotomicFixedArrayMulByTableArray, Array.getD_eq_getD_getElem?, Array.size_ofFn,
    Fin.is_lt, getElem?_pos, Array.getElem_ofFn, Option.getD_some]

/-- Slow reference multiplication: convolve, then recursively expand each monomial. -/
def cyclotomicFixedArrayMulByExpansionSpec (n : ℕ) {p k : ℕ} (hp : Nat.Prime p)
    (a b : cyclotomicFixedArray n p k) : cyclotomicFixedArray n p k := fun j =>
  ∑ e : Fin (2 * primePowerDegree p k),
    cyclotomicFixedArrayConvolution n p k a b e * cyclotomicFixedArrayMonomialReduce n hp e.val j

/-- Multiplication using a shared dynamic-programming table of reduced monomials. -/
def cyclotomicFixedArrayMulByExpansion (n : ℕ) {p k : ℕ} (hp : Nat.Prime p)
    (a b : cyclotomicFixedArray n p k) : cyclotomicFixedArray n p k :=
  cyclotomicFixedArrayMulByTable n hp a b

noncomputable section

/-- Polynomial represented by a fixed-size coefficient array. -/
def cyclotomicFixedArrayPolynomial (n p k : ℕ) (a : cyclotomicFixedArray n p k) :
    Polynomial (ZMod n) :=
  ∑ i : Fin (primePowerDegree p k), Polynomial.monomial i.val (a i)

/-- Coefficients of the represented polynomial equal the zero-extended array. -/
theorem cyclotomicFixedArrayPolynomial_coeff (n p k : ℕ) (a : cyclotomicFixedArray n p k) (d : ℕ) :
    (cyclotomicFixedArrayPolynomial n p k a).coeff d = cyclotomicFixedArrayCoeff n p k a d := by
  classical
  let f := fun i : Fin (primePowerDegree p k) => Polynomial.monomial i.val (a i)
  have hsum (s : Finset (Fin (primePowerDegree p k))) :
    (∑ i ∈ s, f i).coeff d = ∑ i ∈ s, if i.val = d then a i else 0 := by
    induction s using Finset.induction_on with
    | empty => simp only [f, Finset.sum_empty, Polynomial.coeff_zero]
    | @insert i s hi ih =>
      simp only [Finset.sum_insert hi, f, Polynomial.coeff_add, Polynomial.coeff_monomial, ih]
  have hcoeff :
    (cyclotomicFixedArrayPolynomial n p k a).coeff d =
      ∑ i : Fin (primePowerDegree p k), if i.val = d then a i else 0 := by
    simpa only [cyclotomicFixedArrayPolynomial, f] using hsum Finset.univ
  by_cases hd : d < primePowerDegree p k
  · rw [hcoeff]
    simp only [cyclotomicFixedArrayCoeff, hd, dite_eq_left]
    rw [Finset.sum_eq_single ⟨d, hd⟩]
    · simp only [ite_true]
    · intro i hi hne
      have hval : i.val ≠ d := fun h => hne (Fin.ext h)
      simp only [hval, ite_false]
    · intro hnot
      exact (hnot (Finset.mem_univ _)).elim
  · rw [hcoeff]
    simp only [cyclotomicFixedArrayCoeff, dite_eq_right hd]
    apply Finset.sum_eq_zero
    intro i hi
    have hval : i.val ≠ d := by
      intro h
      apply hd
      rw [← h]
      exact i.isLt
    simp only [hval, ite_false]

/-- The quotient element represented by a fixed coefficient array. -/
def cyclotomicFixedArrayClass (n p k : ℕ) (a : cyclotomicFixedArray n p k) :
    cyclotomicQuotient n p k :=
  AdjoinRoot.mk (primePowerCyclotomic p k (ZMod n)) (cyclotomicFixedArrayPolynomial n p k a)

/-- Polynomial representation preserves negation of coefficient arrays. -/
theorem cyclotomicFixedArrayPolynomial_neg (n p k : ℕ) (a : cyclotomicFixedArray n p k) :
    cyclotomicFixedArrayPolynomial n p k (-a) = -cyclotomicFixedArrayPolynomial n p k a := by
  ext d
  calc
    (cyclotomicFixedArrayPolynomial n p k (-a)).coeff d = cyclotomicFixedArrayCoeff n p k (-a) d :=
      cyclotomicFixedArrayPolynomial_coeff n p k (-a) d
    _ = -cyclotomicFixedArrayCoeff n p k a d := by
      by_cases hd : d < primePowerDegree p k <;>
        simp only [cyclotomicFixedArrayCoeff, hd, Pi.neg_apply, dite_true, dite_false, neg_zero]
    _ = -(cyclotomicFixedArrayPolynomial n p k a).coeff d := by
      rw [cyclotomicFixedArrayPolynomial_coeff]

/-- Polynomial representation preserves finite pointwise sums of coefficient arrays. -/
theorem cyclotomicFixedArrayPolynomial_sum {n p k q : ℕ} (a : Fin q → cyclotomicFixedArray n p k) :
    cyclotomicFixedArrayPolynomial n p k (∑ i, a i) =
      ∑ i, cyclotomicFixedArrayPolynomial n p k (a i) := by
  classical
  ext d
  rw [cyclotomicFixedArrayPolynomial_coeff]
  by_cases hd : d < primePowerDegree p k
  · simp only [cyclotomicFixedArrayCoeff, hd, Finset.sum_apply, dite_eq_left]
    have hsum (s : Finset (Fin q)) :
      (∑ i ∈ s, cyclotomicFixedArrayPolynomial n p k (a i)).coeff d =
        ∑ i ∈ s, cyclotomicFixedArrayCoeff n p k (a i) d := by
      induction s using Finset.induction_on with
      | empty => simp only [Finset.sum_empty, Polynomial.coeff_zero]
      | @insert i s hi
        ih =>
        rw [Finset.sum_insert hi, Finset.sum_insert hi, Polynomial.coeff_add, ih]
        rw [cyclotomicFixedArrayPolynomial_coeff]
    rw [hsum Finset.univ]
    simp only [cyclotomicFixedArrayCoeff, hd, dite_eq_left]
  · simp only [cyclotomicFixedArrayCoeff, dite_eq_right hd]
    have hsum (s : Finset (Fin q)) :
      (∑ i ∈ s, cyclotomicFixedArrayPolynomial n p k (a i)).coeff d =
        ∑ i ∈ s, cyclotomicFixedArrayCoeff n p k (a i) d := by
      induction s using Finset.induction_on with
      | empty => simp only [Finset.sum_empty, Polynomial.coeff_zero]
      | @insert i s hi
        ih =>
        rw [Finset.sum_insert hi, Finset.sum_insert hi, Polynomial.coeff_add, ih]
        rw [cyclotomicFixedArrayPolynomial_coeff]
    have hz := hsum Finset.univ
    rw [hz]
    simp only [cyclotomicFixedArrayCoeff, hd, dite_false, Finset.sum_const_zero]

/-- Polynomial representation preserves scalar multiplication of arrays. -/
theorem cyclotomicFixedArrayPolynomial_scale (n p k : ℕ) (c : ZMod n)
    (a : cyclotomicFixedArray n p k) :
    cyclotomicFixedArrayPolynomial n p k (cyclotomicFixedArrayScale n p k c a) =
      Polynomial.C c * cyclotomicFixedArrayPolynomial n p k a := by
  ext d
  calc
    (cyclotomicFixedArrayPolynomial n p k (cyclotomicFixedArrayScale n p k c a)).coeff d =
        cyclotomicFixedArrayCoeff n p k (cyclotomicFixedArrayScale n p k c a) d :=
      cyclotomicFixedArrayPolynomial_coeff n p k _ d
    _ = c * cyclotomicFixedArrayCoeff n p k a d := by
      by_cases hd : d < primePowerDegree p k
      · simp only [cyclotomicFixedArrayCoeff, cyclotomicFixedArrayScale, hd, dite_eq_left]
      · simp only [cyclotomicFixedArrayCoeff, cyclotomicFixedArrayScale, hd, dite_false, mul_zero]
    _ = (Polynomial.C c * cyclotomicFixedArrayPolynomial n p k a).coeff d := by
      rw [Polynomial.coeff_C_mul, cyclotomicFixedArrayPolynomial_coeff]

/-- The quotient interpretation preserves finite sums of arrays. -/
theorem cyclotomicFixedArrayClass_sum {n p k q : ℕ} (a : Fin q → cyclotomicFixedArray n p k) :
    cyclotomicFixedArrayClass n p k (∑ i, a i) = ∑ i, cyclotomicFixedArrayClass n p k (a i) := by
  simp only [cyclotomicFixedArrayClass, cyclotomicFixedArrayPolynomial_sum, map_sum]

/-- The quotient interpretation preserves scalar multiplication of arrays. -/
theorem cyclotomicFixedArrayClass_scale (n p k : ℕ) (c : ZMod n) (a : cyclotomicFixedArray n p k) :
    cyclotomicFixedArrayClass n p k (cyclotomicFixedArrayScale n p k c a) =
      AdjoinRoot.of (primePowerCyclotomic p k (ZMod n)) c * cyclotomicFixedArrayClass n p k a := by
  simp only [cyclotomicFixedArrayClass, cyclotomicFixedArrayPolynomial_scale, AdjoinRoot.mk_C,
    map_mul]

/-- The executable convolution computes every coefficient of the unreduced product. -/
theorem cyclotomicFixedArrayConvolution_coeff (n p k : ℕ) (a b : cyclotomicFixedArray n p k)
    (e : Fin (2 * primePowerDegree p k)) :
    cyclotomicFixedArrayConvolution n p k a b e =
      (cyclotomicFixedArrayPolynomial n p k a * cyclotomicFixedArrayPolynomial n p k b).coeff
        e.val := by
  rw [Polynomial.coeff_mul]
  simp only [cyclotomicFixedArrayConvolution]
  apply Finset.sum_congr rfl
  intro ij hij
  rw [← cyclotomicFixedArrayPolynomial_coeff n p k a ij.1, ←
    cyclotomicFixedArrayPolynomial_coeff n p k b ij.2]

/-- The quotient coefficient equivalence with its index converted to the explicit degree. -/
def cyclotomicFixedCoefficientEquiv (n p k : ℕ) (hn : 1 < n) (hp : Nat.Prime p) :
    cyclotomicQuotient n p k ≃ cyclotomicFixedArray n p k := by
  letI : Nontrivial (ZMod n) := ZMod.nontrivial_iff.mpr hn.ne'
  let hdeg := primePowerCyclotomic_natDegree (p := p) (k := k) hp (ZMod n)
  exact
    (cyclotomicCoefficientEquiv n p k hp).trans
      (Equiv.piCongrLeft (fun _ : Fin (primePowerDegree p k) => ZMod n)
        (Equiv.cast (congrArg Fin hdeg)))

/-- Encoding and decoding a fixed-size coefficient array returns the original array. -/
theorem cyclotomicFixedCoefficientEquiv_encode_decode (n p k : ℕ) (hn : 1 < n) (hp : Nat.Prime p)
    (a : cyclotomicFixedArray n p k) :
    cyclotomicFixedCoefficientEquiv n p k hn hp
        ((cyclotomicFixedCoefficientEquiv n p k hn hp).symm a) =
      a := by
  exact (cyclotomicFixedCoefficientEquiv n p k hn hp).apply_symm_apply a

/-- Decoding the fixed-size coefficient representation recovers its quotient element. -/
theorem cyclotomicFixedCoefficientEquiv_decode_encode (n p k : ℕ) (hn : 1 < n) (hp : Nat.Prime p)
    (x : cyclotomicQuotient n p k) :
    (cyclotomicFixedCoefficientEquiv n p k hn hp).symm
        (cyclotomicFixedCoefficientEquiv n p k hn hp x) =
      x := by
  exact (cyclotomicFixedCoefficientEquiv n p k hn hp).symm_apply_apply x

/-- Coefficients are the canonical monic-remainder coefficients of a quotient element. -/
theorem cyclotomicCoefficientEquiv_apply (n p k : ℕ) (hp : Nat.Prime p)
    (x : cyclotomicQuotient n p k) (i : Fin (primePowerCyclotomic p k (ZMod n)).natDegree) :
    cyclotomicCoefficientEquiv n p k hp x i =
      ((AdjoinRoot.modByMonicHom (primePowerCyclotomic_monic hp (ZMod n))) x).coeff i.val := by
  exact AdjoinRoot.powerBasisAux'_repr_apply_to_fun (primePowerCyclotomic_monic hp (ZMod n)) x i

/-- Reference array multiplication, transported through the certified quotient equivalence. -/
def cyclotomicArrayMul (n p k : ℕ) (hp : Nat.Prime p)
    (a b : Fin (primePowerCyclotomic p k (ZMod n)).natDegree → ZMod n) :=
  cyclotomicCoefficientEquiv n p k hp
    ((cyclotomicCoefficientEquiv n p k hp).symm a * (cyclotomicCoefficientEquiv n p k hp).symm b)

/-- Decoding reference array multiplication agrees with multiplication in the quotient. -/
theorem cyclotomicArrayMul_decode (n p k : ℕ) (hp : Nat.Prime p)
    (a b : Fin (primePowerCyclotomic p k (ZMod n)).natDegree → ZMod n) :
    (cyclotomicCoefficientEquiv n p k hp).symm (cyclotomicArrayMul n p k hp a b) =
      (cyclotomicCoefficientEquiv n p k hp).symm a *
        (cyclotomicCoefficientEquiv n p k hp).symm b := by
  exact (cyclotomicCoefficientEquiv n p k hp).symm_apply_apply _

/-- Each output entry is the canonical monic-remainder coefficient after quotient multiplication. -/
theorem cyclotomicArrayMul_coeff (n p k : ℕ) (hp : Nat.Prime p)
    (a b : Fin (primePowerCyclotomic p k (ZMod n)).natDegree → ZMod n)
    (i : Fin (primePowerCyclotomic p k (ZMod n)).natDegree) :
    cyclotomicArrayMul n p k hp a b i =
      ((AdjoinRoot.modByMonicHom (primePowerCyclotomic_monic hp (ZMod n)))
            ((cyclotomicCoefficientEquiv n p k hp).symm a *
              (cyclotomicCoefficientEquiv n p k hp).symm b)).coeff
        i.val := by
  exact cyclotomicCoefficientEquiv_apply n p k hp _ i

/-- Bounded-degree polynomial represented by an input coefficient array. -/
def cyclotomicArrayPolynomial (n p k : ℕ)
    (a : Fin (primePowerCyclotomic p k (ZMod n)).natDegree → ZMod n) :=
  ∑ i : Fin (primePowerCyclotomic p k (ZMod n)).natDegree, Polynomial.monomial i.val (a i)

/-- Decoding an array gives the quotient class of its bounded-degree polynomial. -/
theorem cyclotomicCoefficientEquiv_symm_eq_mk (n p k : ℕ) (hp : Nat.Prime p)
    (a : Fin (primePowerCyclotomic p k (ZMod n)).natDegree → ZMod n) :
    (cyclotomicCoefficientEquiv n p k hp).symm a =
      AdjoinRoot.mk (primePowerCyclotomic p k (ZMod n)) (cyclotomicArrayPolynomial n p k a) := by
  change
    (AdjoinRoot.powerBasisAux' (primePowerCyclotomic_monic hp (ZMod n))).repr.symm
        (Finsupp.equivFunOnFinite.symm a) =
      _
  rw [AdjoinRoot.powerBasisAux'_repr_symm_apply]
  congr 1

/-- Specification that multiplies represented polynomials and reduces by the monic relation. -/
def cyclotomicArrayMulRemainderSpec (n p k : ℕ)
    (a b : Fin (primePowerCyclotomic p k (ZMod n)).natDegree → ZMod n) :
    Fin (primePowerCyclotomic p k (ZMod n)).natDegree → ZMod n := fun i =>
  (Polynomial.modByMonic (cyclotomicArrayPolynomial n p k a * cyclotomicArrayPolynomial n p k b)
        (primePowerCyclotomic p k (ZMod n))).coeff
    i.val

/-- The monic-remainder specification agrees with quotient-reference multiplication. -/
theorem cyclotomicArrayMulRemainderSpec_eq_reference (n p k : ℕ) (hp : Nat.Prime p)
    (a b : Fin (primePowerCyclotomic p k (ZMod n)).natDegree → ZMod n) :
    cyclotomicArrayMulRemainderSpec n p k a b = cyclotomicArrayMul n p k hp a b := by
  funext i
  rw [cyclotomicArrayMul_coeff, cyclotomicCoefficientEquiv_symm_eq_mk,
    cyclotomicCoefficientEquiv_symm_eq_mk, ← map_mul (AdjoinRoot.mk _)]
  rw [AdjoinRoot.modByMonicHom_mk]
  rfl

/-- Reference array exponentiation, transported through the quotient equivalence. -/
def cyclotomicArrayPow (n p k : ℕ) (hp : Nat.Prime p)
    (a : Fin (primePowerCyclotomic p k (ZMod n)).natDegree → ZMod n) (e : ℕ) :=
  cyclotomicCoefficientEquiv n p k hp ((cyclotomicCoefficientEquiv n p k hp).symm a ^ e)

/-- Decoding array exponentiation agrees with exponentiation in the quotient. -/
theorem cyclotomicArrayPow_decode (n p k : ℕ) (hp : Nat.Prime p)
    (a : Fin (primePowerCyclotomic p k (ZMod n)).natDegree → ZMod n) (e : ℕ) :
    (cyclotomicCoefficientEquiv n p k hp).symm (cyclotomicArrayPow n p k hp a e) =
      (cyclotomicCoefficientEquiv n p k hp).symm a ^ e := by
  exact (cyclotomicCoefficientEquiv n p k hp).symm_apply_apply _

/-- Array exponentiation starts at the coefficient representation of one. -/
theorem cyclotomicArrayPow_zero (n p k : ℕ) (hp : Nat.Prime p)
    (a : Fin (primePowerCyclotomic p k (ZMod n)).natDegree → ZMod n) :
    cyclotomicArrayPow n p k hp a 0 = cyclotomicCoefficientEquiv n p k hp 1 := by
  simp only [cyclotomicArrayPow, pow_zero]

/-- One further array power is reference multiplication by the base array. -/
theorem cyclotomicArrayPow_succ (n p k : ℕ) (hp : Nat.Prime p)
    (a : Fin (primePowerCyclotomic p k (ZMod n)).natDegree → ZMod n) (e : ℕ) :
    cyclotomicArrayPow n p k hp a (e + 1) =
      cyclotomicArrayMul n p k hp (cyclotomicArrayPow n p k hp a e) a := by
  simp only [cyclotomicArrayPow, cyclotomicArrayMul, pow_succ,
    cyclotomicCoefficientEquiv_decode_encode]

/-- The quotient's canonical root satisfies the explicit prime-power cyclotomic relation. -/
theorem cyclotomicRoot_relation (n p k : ℕ) :
    Polynomial.eval₂ (AdjoinRoot.of (primePowerCyclotomic p k (ZMod n))) (cyclotomicRoot n p k)
        (primePowerCyclotomic p k (ZMod n)) =
      0 := by
  exact AdjoinRoot.eval₂_root _

/-- The defining geometric sum expresses the top block power as the negative lower block. -/
theorem cyclotomicRoot_highBlock_relation (n : ℕ) {p k : ℕ} (hp : Nat.Prime p) :
    cyclotomicRoot n p k ^ (primePowerStep p k * (p - 1)) =
      -∑ i ∈ Finset.range (p - 1), cyclotomicRoot n p k ^ (primePowerStep p k * i) := by
  have hsum : ∑ i ∈ Finset.range p, (cyclotomicRoot n p k ^ p ^ k) ^ i = 0 := by
    have h := cyclotomicRoot_relation n p k
    change
      Polynomial.eval₂ (AdjoinRoot.of (primePowerCyclotomic p k (ZMod n)))
          (AdjoinRoot.root (primePowerCyclotomic p k (ZMod n)))
          (primePowerCyclotomic p k (ZMod n)) =
        0 at h
    rw [primePowerCyclotomic, Polynomial.eval₂_finsetSum] at h
    simp only [Polynomial.eval₂_pow, Polynomial.eval₂_X] at h
    exact h
  have hpEq : (p - 1) + 1 = p := Nat.sub_add_cancel hp.one_le
  have hsum' : ∑ i ∈ Finset.range ((p - 1) + 1), (cyclotomicRoot n p k ^ p ^ k) ^ i = 0 := by
    rw [hpEq]
    exact hsum
  rw [Finset.sum_range_succ_comm] at hsum'
  have hblock :
    cyclotomicRoot n p k ^ (p ^ k * (p - 1)) +
        ∑ i ∈ Finset.range (p - 1), cyclotomicRoot n p k ^ (p ^ k * i) =
      0 := by
    simp only [← pow_mul] at hsum'
    exact hsum'
  exact eq_neg_of_add_eq_zero_left hblock

/-- Each exponent at or above the defining degree reduces to the lower block relation. -/
theorem cyclotomicRoot_pow_topBlock_add (n : ℕ) {p k : ℕ} (hp : Nat.Prime p) (e : ℕ) :
    cyclotomicRoot n p k ^ (primePowerDegree p k + e) =
      -∑ i ∈ Finset.range (p - 1), cyclotomicRoot n p k ^ (e + primePowerStep p k * i) := by
  have hdegree : primePowerDegree p k = primePowerStep p k * (p - 1) := by
    simp only [primePowerDegree, primePowerStep, Nat.mul_comm]
  rw [hdegree, pow_add, cyclotomicRoot_highBlock_relation n hp, neg_mul, Finset.sum_mul]
  apply congrArg Neg.neg
  apply Finset.sum_congr rfl
  intro i hi
  calc
    cyclotomicRoot n p k ^ (primePowerStep p k * i) * cyclotomicRoot n p k ^ e =
        cyclotomicRoot n p k ^ (primePowerStep p k * i + e) :=
      by rw [← pow_add]
    _ = cyclotomicRoot n p k ^ (e + primePowerStep p k * i) := by rw [Nat.add_comm]

/-- Monomial reduction preserves the represented quotient power. -/
theorem cyclotomicFixedArrayMonomialReduce_correct (n : ℕ) {p k : ℕ} (hp : Nat.Prime p) (e : ℕ) :
    cyclotomicFixedArrayClass n p k (cyclotomicFixedArrayMonomialReduce n hp e) =
      cyclotomicRoot n p k ^ e := by
  classical
    induction e using Nat.strong_induction_on with
  | h e ih =>
    rw [cyclotomicFixedArrayMonomialReduce]
    by_cases he : e < primePowerDegree p k
    · simp only [dite_eq_left he]
      have hpoly :
        cyclotomicFixedArrayPolynomial n p k
            (fun j : Fin (primePowerDegree p k) => if j.val = e then 1 else 0) =
          Polynomial.X ^ e := by
        apply Polynomial.ext
        intro d
        rw [cyclotomicFixedArrayPolynomial_coeff]
        by_cases hde : d = e
        · subst d
          simp only [cyclotomicFixedArrayCoeff, he, dite_eq_left, ite_eq_left,
            Polynomial.coeff_X_pow_self]
        · by_cases hbound : d < primePowerDegree p k
          · simp only [cyclotomicFixedArrayCoeff, hde, hbound, dite_eq_left, ite_false,
              Polynomial.coeff_X_pow]
          · simp only [cyclotomicFixedArrayCoeff, hde, hbound, dite_false, ite_false,
              Polynomial.coeff_X_pow]
      have hclass := congrArg (AdjoinRoot.mk (primePowerCyclotomic p k (ZMod n))) hpoly
      simpa only [cyclotomicFixedArrayClass, cyclotomicQuotient, cyclotomicRoot, map_pow,
        AdjoinRoot.mk_X] using hclass
    · simp only [dite_eq_right he]
      have hmle : primePowerDegree p k ≤ e := Nat.le_of_not_gt he
      have hsum :
        cyclotomicFixedArrayClass n p k
            (-∑ i : Fin (p - 1),
                cyclotomicFixedArrayMonomialReduce n hp
                  (e - primePowerDegree p k + primePowerStep p k * i.val)) =
          -∑ i : Fin (p - 1),
              cyclotomicFixedArrayClass n p k
                (cyclotomicFixedArrayMonomialReduce n hp
                  (e - primePowerDegree p k + primePowerStep p k * i.val)) := by
        simp only [cyclotomicFixedArrayClass, cyclotomicFixedArrayPolynomial_neg,
          cyclotomicFixedArrayPolynomial_sum, map_neg, map_sum]
      rw [hsum]
      have hterms :
        ∀ i : Fin (p - 1),
          cyclotomicFixedArrayClass n p k
              (cyclotomicFixedArrayMonomialReduce n hp
                (e - primePowerDegree p k + primePowerStep p k * i.val)) =
            cyclotomicRoot n p k ^ (e - primePowerDegree p k + primePowerStep p k * i.val) := by
        intro i
        apply ih
        have hdpos : 0 < p ^ k := Nat.pow_pos hp.pos
        have hdeg : primePowerDegree p k = (p - 1) * p ^ k := rfl
        have hstep : primePowerStep p k = p ^ k := rfl
        have hi : i.val < p - 1 := i.isLt
        have hblock := Nat.mul_lt_mul_of_pos_right hi hdpos
        have hblock' : p ^ k * i.val < (p - 1) * p ^ k := by simpa only [Nat.mul_comm] using hblock
        have he' : (p - 1) * p ^ k ≤ e := by
          rw [← hdeg]
          exact hmle
        rw [hstep, hdeg]
        calc
          e - (p - 1) * p ^ k + p ^ k * i.val < e - (p - 1) * p ^ k + (p - 1) * p ^ k :=
            Nat.add_lt_add_left hblock' _
          _ = e := Nat.sub_add_cancel he'
      have hpow := cyclotomicRoot_pow_topBlock_add n (p := p) (k := k) hp (e - primePowerDegree p k)
      rw [Nat.add_sub_of_le hmle] at hpow
      have hsumEq :
        (∑ i : Fin (p - 1),
            cyclotomicRoot n p k ^ (e - primePowerDegree p k + primePowerStep p k * i.val)) =
          ∑ i ∈ Finset.range (p - 1),
            cyclotomicRoot n p k ^ (e - primePowerDegree p k + primePowerStep p k * i) := by
        exact
          Fin.sum_univ_eq_sum_range
            (fun i => cyclotomicRoot n p k ^ (e - primePowerDegree p k + primePowerStep p k * i))
            (p - 1)
      calc
        -∑ i : Fin (p - 1),
                cyclotomicFixedArrayClass n p k
                  (cyclotomicFixedArrayMonomialReduce n hp
                    (e - primePowerDegree p k + primePowerStep p k * i.val)) =
            -∑ i : Fin (p - 1),
                cyclotomicRoot n p k ^ (e - primePowerDegree p k + primePowerStep p k * i.val) :=
          by
          congr 1
          apply Finset.sum_congr rfl
          intro i hi
          exact hterms i
        _ = cyclotomicRoot n p k ^ e := by
          rw [hsumEq]
          exact hpow.symm

/-- The table prefix contains exactly one row for every exponent below its bound. -/
theorem cyclotomicFixedArrayMonomialReduceTableAux_size (n : ℕ) {p k : ℕ} (hp : Nat.Prime p)
    (count : ℕ) : (@cyclotomicFixedArrayMonomialReduceTableAux n p k hp count).size = count := by
  induction count with
  | zero => simp only [cyclotomicFixedArrayMonomialReduceTableAux, Array.size_empty]
  | succ count ih => simp only [cyclotomicFixedArrayMonomialReduceTableAux, Array.size_push, ih]

/-- Each table row agrees with the recursively specified reduction for its exponent. -/
theorem cyclotomicFixedArrayMonomialReduceTableAux_getD (n : ℕ) {p k : ℕ} (hp : Nat.Prime p)
    (count exponent : ℕ) (he : exponent < count) (j : Fin (primePowerDegree p k)) :
    ((@cyclotomicFixedArrayMonomialReduceTableAux n p k hp count).getD exponent
            (cyclotomicFixedArrayZeroRow n p k)).getD
        j.val 0 =
      cyclotomicFixedArrayMonomialReduce n (p := p) (k := k) hp exponent j := by
  revert exponent
  induction count with
  | zero =>
    intro exponent he
    exact (Nat.not_lt_zero exponent he).elim
  | succ count ih =>
    intro exponent he
    by_cases hlow : exponent < count
    · have hprev := ih exponent hlow
      let previous := @cyclotomicFixedArrayMonomialReduceTableAux n p k hp count
      let row :=
        if count < primePowerDegree p k then
          cyclotomicFixedArrayToArray n p k (cyclotomicFixedArrayMonomialUnit n p k count)
        else
          Array.ofFn fun j : Fin (primePowerDegree p k) =>
            -∑ i : Fin (p - 1),
                (previous.getD (count - primePowerDegree p k + primePowerStep p k * i.val)
                      (cyclotomicFixedArrayZeroRow n p k)).getD
                  j.val 0
      have hsize : previous.size = count := by
        simpa only [previous] using cyclotomicFixedArrayMonomialReduceTableAux_size n hp count
      have hlt : exponent < previous.size := by
        rw [hsize]
        exact hlow
      have hlookup :
        (previous.push row).getD exponent (cyclotomicFixedArrayZeroRow n p k) =
          previous.getD exponent (cyclotomicFixedArrayZeroRow n p k) := by
        rw [Array.getD_eq_getD_getElem?]
        rw [Array.getElem?_push_lt hlt]
        simp only [Option.getD_some]
        exact Array.getElem_eq_getD (h := hlt) (cyclotomicFixedArrayZeroRow n p k)
      rw [cyclotomicFixedArrayMonomialReduceTableAux]
      change
        ((previous.push row).getD exponent (cyclotomicFixedArrayZeroRow n p k)).getD j.val 0 = _
      rw [hlookup]
      exact hprev
    · have heq : exponent = count := by
        exact Nat.le_antisymm (Nat.le_of_lt_succ he) (Nat.le_of_not_lt hlow)
      subst exponent
      let previous := @cyclotomicFixedArrayMonomialReduceTableAux n p k hp count
      let row :=
        if count < primePowerDegree p k then
          cyclotomicFixedArrayToArray n p k (cyclotomicFixedArrayMonomialUnit n p k count)
        else
          Array.ofFn fun j : Fin (primePowerDegree p k) =>
            -∑ i : Fin (p - 1),
                (previous.getD (count - primePowerDegree p k + primePowerStep p k * i.val)
                      (cyclotomicFixedArrayZeroRow n p k)).getD
                  j.val 0
      have hsize : previous.size = count := by
        simpa only [previous] using cyclotomicFixedArrayMonomialReduceTableAux_size n hp count
      have hlookup : (previous.push row).getD count (cyclotomicFixedArrayZeroRow n p k) = row := by
        rw [Array.getD_eq_getD_getElem?]
        rw [show count = previous.size by exact hsize.symm]
        rw [Array.getElem?_push_size]
        simp only [Option.getD_some]
      rw [cyclotomicFixedArrayMonomialReduceTableAux]
      change ((previous.push row).getD count (cyclotomicFixedArrayZeroRow n p k)).getD j.val 0 = _
      rw [hlookup]
      by_cases hsmall : count < primePowerDegree p k
      · dsimp only [row]
        rw [ite_eq_left hsmall]
        rw [cyclotomicFixedArrayMonomialReduce]
        simp only [dite_eq_left hsmall]
        simp only [cyclotomicFixedArrayToArray, Array.getD_eq_getD_getElem?, Array.size_ofFn,
          Fin.is_lt, getElem?_pos, Array.getElem_ofFn, Option.getD_some,
          cyclotomicFixedArrayMonomialUnit]
      · dsimp only [row]
        rw [ite_eq_right hsmall]
        rw [cyclotomicFixedArrayMonomialReduce]
        simp only [dite_eq_right hsmall]
        simp only [Array.getD_eq_getD_getElem?, Array.size_ofFn, Fin.is_lt, getElem?_pos,
          Array.getElem_ofFn, Option.getD_some, Pi.neg_apply, Finset.sum_apply, neg_inj]
        congr 1
        funext i
        have hdpos : 0 < p ^ k := Nat.pow_pos hp.pos
        have hindex : i.val < p - 1 := i.isLt
        have hblock : i.val * p ^ k < (p - 1) * p ^ k := Nat.mul_lt_mul_of_pos_right hindex hdpos
        have hblock' : p ^ k * i.val < (p - 1) * p ^ k := by simpa only [Nat.mul_comm] using hblock
        have hdeg : primePowerDegree p k = (p - 1) * p ^ k := rfl
        have hstep : primePowerStep p k = p ^ k := rfl
        have htarget : count - primePowerDegree p k + primePowerStep p k * i.val < count := by
          have hle : primePowerDegree p k ≤ count := Nat.le_of_not_gt hsmall
          rw [hstep, hdeg]
          calc
            count - (p - 1) * p ^ k + p ^ k * i.val < count - (p - 1) * p ^ k + (p - 1) * p ^ k :=
              Nat.add_lt_add_left hblock' _
            _ = count := Nat.sub_add_cancel hle
        rw [← Array.getD_eq_getD_getElem?]
        rw [← Array.getD_eq_getD_getElem?]
        exact ih (count - primePowerDegree p k + primePowerStep p k * i.val) htarget

/-- Dynamic-programming multiplication agrees with the recursive expansion specification. -/
theorem cyclotomicFixedArrayMulByTable_eq_expansion (n : ℕ) {p k : ℕ} (hp : Nat.Prime p)
    (a b : cyclotomicFixedArray n p k) :
    cyclotomicFixedArrayMulByTable n hp a b = cyclotomicFixedArrayMulByExpansionSpec n hp a b := by
  funext j
  change (cyclotomicFixedArrayMulByTableArray n hp a b).getD j.val 0 = _
  rw [cyclotomicFixedArrayMulByTableArray_getD]
  change
    _ =
      ∑ e : Fin (2 * primePowerDegree p k),
        cyclotomicFixedArrayConvolution n p k a b e *
          cyclotomicFixedArrayMonomialReduce n hp e.val j
  apply Finset.sum_congr rfl
  intro e he
  rw [cyclotomicFixedArrayMonomialReduceTable]
  rw [cyclotomicFixedArrayMonomialReduceTableAux_getD n hp (2 * primePowerDegree p k) e.val e.isLt
      j]

/-- The expansion multiplier represents the corresponding finite sum of root powers. -/
theorem cyclotomicFixedArrayMulByExpansion_class (n : ℕ) {p k : ℕ} (hp : Nat.Prime p)
    (a b : cyclotomicFixedArray n p k) :
    cyclotomicFixedArrayClass n p k (cyclotomicFixedArrayMulByExpansion n hp a b) =
      ∑ e : Fin (2 * primePowerDegree p k),
        AdjoinRoot.of (primePowerCyclotomic p k (ZMod n))
            (cyclotomicFixedArrayConvolution n p k a b e) *
          cyclotomicRoot n p k ^ e.val := by
  rw [cyclotomicFixedArrayMulByExpansion, cyclotomicFixedArrayMulByTable_eq_expansion]
  have hmul :
    cyclotomicFixedArrayMulByExpansionSpec n hp a b =
      ∑ e : Fin (2 * primePowerDegree p k),
        cyclotomicFixedArrayScale n p k (cyclotomicFixedArrayConvolution n p k a b e)
          (cyclotomicFixedArrayMonomialReduce n hp e.val) := by
    funext j
    simp only [cyclotomicFixedArrayMulByExpansionSpec, cyclotomicFixedArrayScale, Finset.sum_apply]
  rw [hmul, cyclotomicFixedArrayClass_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [cyclotomicFixedArrayClass_scale, cyclotomicFixedArrayMonomialReduce_correct]

/-- The polynomial represented by a fixed array has degree below the basis length. -/
theorem cyclotomicFixedArrayPolynomial_natDegree_lt (n p k : ℕ) (hp : Nat.Prime p)
    (a : cyclotomicFixedArray n p k) :
    (cyclotomicFixedArrayPolynomial n p k a).natDegree < primePowerDegree p k := by
  have hmpos : 0 < primePowerDegree p k := by
    rw [primePowerDegree]
    exact Nat.mul_pos (Nat.sub_pos_of_lt hp.one_lt) (Nat.pow_pos hp.pos)
  have hle : (cyclotomicFixedArrayPolynomial n p k a).natDegree ≤ primePowerDegree p k - 1 :=
    Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
      (by
        intro d hd
        rw [cyclotomicFixedArrayPolynomial_coeff]
        have hdegree : primePowerDegree p k ≤ d := by
          have hsucc : primePowerDegree p k - 1 + 1 ≤ d := Nat.succ_le_of_lt hd
          rw [Nat.sub_add_cancel (Nat.succ_le_iff.mpr hmpos)] at hsucc
          exact hsucc
        simp only [cyclotomicFixedArrayCoeff, Nat.not_lt.mpr hdegree, dite_false])
  exact Nat.lt_of_le_pred hmpos hle

/-- Expansion multiplication represents multiplication in the cyclotomic quotient. -/
theorem cyclotomicFixedArrayMulByExpansion_class_eq_mul (n : ℕ) {p k : ℕ} (hp : Nat.Prime p)
    (a b : cyclotomicFixedArray n p k) :
    cyclotomicFixedArrayClass n p k (cyclotomicFixedArrayMulByExpansion n hp a b) =
      cyclotomicFixedArrayClass n p k a * cyclotomicFixedArrayClass n p k b := by
  have hmpos : 0 < primePowerDegree p k := by
    rw [primePowerDegree]
    exact Nat.mul_pos (Nat.sub_pos_of_lt hp.one_lt) (Nat.pow_pos hp.pos)
  have hprodDegree :
    (cyclotomicFixedArrayPolynomial n p k a * cyclotomicFixedArrayPolynomial n p k b).natDegree <
      2 * primePowerDegree p k := by
    calc
      _ ≤
          (cyclotomicFixedArrayPolynomial n p k a).natDegree +
            (cyclotomicFixedArrayPolynomial n p k b).natDegree :=
        Polynomial.natDegree_mul_le
      _ < primePowerDegree p k + primePowerDegree p k :=
        Nat.add_lt_add (cyclotomicFixedArrayPolynomial_natDegree_lt n p k hp a)
          (cyclotomicFixedArrayPolynomial_natDegree_lt n p k hp b)
      _ = 2 * primePowerDegree p k := (Nat.two_mul _).symm
  have hdecomp :=
    Polynomial.as_sum_range_C_mul_X_pow'
      (cyclotomicFixedArrayPolynomial n p k a * cyclotomicFixedArrayPolynomial n p k b) hprodDegree
  have hcoeff :
    ∀ e : Fin (2 * primePowerDegree p k),
      cyclotomicFixedArrayConvolution n p k a b e =
        (cyclotomicFixedArrayPolynomial n p k a * cyclotomicFixedArrayPolynomial n p k b).coeff
          e.val :=
    cyclotomicFixedArrayConvolution_coeff n p k a b
  rw [cyclotomicFixedArrayMulByExpansion_class]
  have hsum :
    (∑ e : Fin (2 * primePowerDegree p k),
        Polynomial.C (cyclotomicFixedArrayConvolution n p k a b e) * Polynomial.X ^ e.val) =
      cyclotomicFixedArrayPolynomial n p k a * cyclotomicFixedArrayPolynomial n p k b := by
    let f : ℕ → Polynomial (ZMod n) := fun e =>
      if he : e < 2 * primePowerDegree p k then
        Polynomial.C (cyclotomicFixedArrayConvolution n p k a b ⟨e, he⟩) * Polynomial.X ^ e
      else 0
    have hrange :
      (∑ e ∈ Finset.range (2 * primePowerDegree p k), f e) =
        ∑ e ∈ Finset.range (2 * primePowerDegree p k),
          Polynomial.C
              ((cyclotomicFixedArrayPolynomial n p k a *
                    cyclotomicFixedArrayPolynomial n p k b).coeff
                e) *
            Polynomial.X ^ e := by
      apply Finset.sum_congr rfl
      intro e he
      have hlt := Finset.mem_range.mp he
      simp only [f, dite_eq_left hlt]
      rw [hcoeff ⟨e, hlt⟩]
    calc
      _ = ∑ e : Fin (2 * primePowerDegree p k), f e.val := by
        apply Finset.sum_congr rfl
        intro e he
        simp only [f, e.isLt, dite_eq_left]
      _ = ∑ e ∈ Finset.range (2 * primePowerDegree p k), f e := Fin.sum_univ_eq_sum_range f _
      _ =
          ∑ e ∈ Finset.range (2 * primePowerDegree p k),
            Polynomial.C
                ((cyclotomicFixedArrayPolynomial n p k a *
                      cyclotomicFixedArrayPolynomial n p k b).coeff
                  e) *
              Polynomial.X ^ e :=
        hrange
      _ = cyclotomicFixedArrayPolynomial n p k a * cyclotomicFixedArrayPolynomial n p k b :=
        hdecomp.symm
  have hmap := congrArg (AdjoinRoot.mk (primePowerCyclotomic p k (ZMod n))) hsum
  simp only [map_sum, map_mul, map_pow, AdjoinRoot.mk_C, AdjoinRoot.mk_X] at hmap
  simpa only [cyclotomicFixedArrayClass, cyclotomicQuotient, cyclotomicRoot] using hmap

/-- Coefficient array representing the multiplicative identity. -/
def cyclotomicFixedArrayOne (n p k : ℕ) : cyclotomicFixedArray n p k := fun j =>
  if j.val = 0 then 1 else 0

/-- Materialized coefficient-array powers computed by repeated multiplication. -/
def cyclotomicFixedArrayPowByMulArray (n : ℕ) {p k : ℕ} (hp : Nat.Prime p)
    (a : cyclotomicFixedArray n p k) : ℕ → Array (ZMod n)
  | 0 => Array.ofFn (cyclotomicFixedArrayOne n p k)
  | e + 1 =>
      let previous := cyclotomicFixedArrayPowByMulArray n hp a e
      let previousFn := fun j : Fin (primePowerDegree p k) => previous.getD j.val 0
      cyclotomicFixedArrayMulByTableArray n hp previousFn a
termination_by e => e

/-- View a materialized coefficient array in the fixed-size function interface. -/
def cyclotomicFixedArrayOfArray (n p k : ℕ) (a : Array (ZMod n)) : cyclotomicFixedArray n p k :=
  fun j => a.getD j.val 0

/-- Decoding a function-backed array recovers the original coefficient array. -/
theorem cyclotomicFixedArrayOfArray_ofFn (n p k : ℕ) (a : cyclotomicFixedArray n p k) :
    cyclotomicFixedArrayOfArray n p k (Array.ofFn a) = a := by
  funext j
  simp only [cyclotomicFixedArrayOfArray, Array.getD_eq_getD_getElem?, Array.size_ofFn, Fin.is_lt,
    getElem?_pos, Array.getElem_ofFn, Option.getD_some]

/-- Decoding a materialized table product agrees with the function interface. -/
theorem cyclotomicFixedArrayMulByTableArray_asFunction (n : ℕ) {p k : ℕ} (hp : Nat.Prime p)
    (a b : cyclotomicFixedArray n p k) :
    cyclotomicFixedArrayOfArray n p k (cyclotomicFixedArrayMulByTableArray n hp a b) =
      cyclotomicFixedArrayMulByTable n hp a b := by
  rfl

/-- Materialized square of a fixed coefficient array using the shared reduction table. -/
def cyclotomicFixedArraySquareArray (n : ℕ) {p k : ℕ} (hp : Nat.Prime p)
    (a : cyclotomicFixedArray n p k) : Array (ZMod n) :=
  cyclotomicFixedArrayMulByTableArray n hp a a

/-- Decode the materialized square into the fixed-size coefficient interface. -/
def cyclotomicFixedArraySquare (n : ℕ) {p k : ℕ} (hp : Nat.Prime p)
    (a : cyclotomicFixedArray n p k) : cyclotomicFixedArray n p k :=
  cyclotomicFixedArrayOfArray n p k (cyclotomicFixedArraySquareArray n hp a)

/-- The optimized array square represents the square in the cyclotomic quotient.
This connects the concrete coefficient operation to the abstract ring power used by APR-CL. -/
theorem cyclotomicFixedArraySquare_class (n : ℕ) {p k : ℕ} (hp : Nat.Prime p)
    (a : cyclotomicFixedArray n p k) :
    cyclotomicFixedArrayClass n p k (cyclotomicFixedArraySquare n hp a) =
      cyclotomicFixedArrayClass n p k a ^ 2 := by
  rw [cyclotomicFixedArraySquare]
  change
    cyclotomicFixedArrayClass n p k
        (cyclotomicFixedArrayOfArray n p k (cyclotomicFixedArrayMulByTableArray n hp a a)) =
      _
  rw [cyclotomicFixedArrayMulByTableArray_asFunction]
  change cyclotomicFixedArrayClass n p k (cyclotomicFixedArrayMulByExpansion n hp a a) = _
  rw [cyclotomicFixedArrayMulByExpansion_class_eq_mul]
  exact (pow_two _).symm

/-- A materialized multiplication decodes to the quotient-ring product. -/
theorem cyclotomicFixedArrayMulByTableArray_class (n : ℕ) {p k : ℕ} (hp : Nat.Prime p)
    (a b : cyclotomicFixedArray n p k) :
    cyclotomicFixedArrayClass n p k
        (cyclotomicFixedArrayOfArray n p k (cyclotomicFixedArrayMulByTableArray n hp a b)) =
      cyclotomicFixedArrayClass n p k a * cyclotomicFixedArrayClass n p k b := by
  rw [cyclotomicFixedArrayMulByTableArray_asFunction]
  change cyclotomicFixedArrayClass n p k (cyclotomicFixedArrayMulByExpansion n hp a b) = _
  exact cyclotomicFixedArrayMulByExpansion_class_eq_mul n hp a b

/-- The coefficient array of a square decodes to the quotient-ring square. -/
theorem cyclotomicFixedArraySquareArray_class (n : ℕ) {p k : ℕ} (hp : Nat.Prime p)
    (a : cyclotomicFixedArray n p k) :
    cyclotomicFixedArrayClass n p k
        (cyclotomicFixedArrayOfArray n p k (cyclotomicFixedArraySquareArray n hp a)) =
      cyclotomicFixedArrayClass n p k a ^ 2 :=
  cyclotomicFixedArraySquare_class n hp a

/-- One binary exponentiation step: square the preceding array, then apply the odd digit. -/
def cyclotomicFixedArrayPowBySquaringStep (n : ℕ) {p k : ℕ} (hp : Nat.Prime p)
    (a : cyclotomicFixedArray n p k) (odd : Bool) (previous : Array (ZMod n)) : Array (ZMod n) :=
  let previousFn := cyclotomicFixedArrayOfArray n p k previous
  let squared := cyclotomicFixedArraySquareArray n hp previousFn
  if odd then cyclotomicFixedArrayMulByTableArray n hp (cyclotomicFixedArrayOfArray n p k squared) a
  else squared

/-- The binary step decodes to squaring, with one extra factor for an odd digit. -/
theorem cyclotomicFixedArrayPowBySquaringStep_class (n : ℕ) {p k : ℕ} (hp : Nat.Prime p)
    (a : cyclotomicFixedArray n p k) (odd : Bool) (previous : Array (ZMod n)) :
    cyclotomicFixedArrayClass n p k
        (cyclotomicFixedArrayOfArray n p k
          (cyclotomicFixedArrayPowBySquaringStep n hp a odd previous)) =
      if odd then
        (cyclotomicFixedArrayClass n p k (cyclotomicFixedArrayOfArray n p k previous)) ^ 2 *
          cyclotomicFixedArrayClass n p k a
      else (cyclotomicFixedArrayClass n p k (cyclotomicFixedArrayOfArray n p k previous)) ^ 2 := by
  cases odd <;>
    simp only [cyclotomicFixedArrayPowBySquaringStep, Bool.false_eq_true, ite_false, ite_true,
      cyclotomicFixedArraySquareArray_class, cyclotomicFixedArrayMulByTableArray_class]

/-- Materialized powers computed from the binary digits of the exponent. -/
def cyclotomicFixedArrayPowBySquaringArray (n : ℕ) {p k : ℕ} (hp : Nat.Prime p)
    (a : cyclotomicFixedArray n p k) (e : ℕ) : Array (ZMod n) :=
  Nat.binaryRecFromOne (Array.ofFn (cyclotomicFixedArrayOne n p k)) (Array.ofFn a)
    (fun b _ _ previous => cyclotomicFixedArrayPowBySquaringStep n hp a b previous) e

/-- Repeated multiplication computes fixed-array powers, materializing every intermediate power.
-/
def cyclotomicFixedArrayPowByMul (n : ℕ) {p k : ℕ} (hp : Nat.Prime p)
    (a : cyclotomicFixedArray n p k) (e : ℕ) : cyclotomicFixedArray n p k :=
  cyclotomicFixedArrayOfArray n p k (cyclotomicFixedArrayPowByMulArray n hp a e)

/-- The identity coefficient array decodes to the multiplicative identity. -/
theorem cyclotomicFixedArrayOne_class (n : ℕ) {p k : ℕ} (hp : Nat.Prime p) :
    cyclotomicFixedArrayClass n p k (cyclotomicFixedArrayOne n p k) = 1 := by
  have hmpos : 0 < primePowerDegree p k := by
    rw [primePowerDegree]
    exact Nat.mul_pos (Nat.sub_pos_of_lt hp.one_lt) (Nat.pow_pos hp.pos)
  have hpoly : cyclotomicFixedArrayPolynomial n p k (cyclotomicFixedArrayOne n p k) = 1 := by
    ext d
    rw [cyclotomicFixedArrayPolynomial_coeff, Polynomial.coeff_one]
    by_cases hd : d = 0
    · subst d
      simp only [cyclotomicFixedArrayCoeff, cyclotomicFixedArrayOne, hmpos, dite_eq_left,
        ite_eq_left]
    · by_cases hbound : d < primePowerDegree p k
      · simp only [cyclotomicFixedArrayCoeff, cyclotomicFixedArrayOne, hd, hbound, dite_eq_left,
          ite_false]
      · simp only [cyclotomicFixedArrayCoeff, cyclotomicFixedArrayOne, hd, hbound, dite_false,
          ite_false]
  rw [cyclotomicFixedArrayClass, hpoly]
  exact map_one (AdjoinRoot.mk (primePowerCyclotomic p k (ZMod n)))

/-- Multiply a finite ordered list of fixed coefficient arrays by the executable expansion
multiplier, starting from the coefficient representation of one. -/
def cyclotomicFixedArrayProductList (n : ℕ) {p k : ℕ} (hp : Nat.Prime p)
    (xs : List (cyclotomicFixedArray n p k)) : cyclotomicFixedArray n p k :=
  xs.foldl (fun a b ↦ cyclotomicFixedArrayMulByExpansion n hp a b) (cyclotomicFixedArrayOne n p k)

/-- The quotient image of a left-to-right fixed-array product is the corresponding product of
the quotient images. This lets finite APR-CL Jacobi products use the executable array backend. -/
theorem cyclotomicFixedArrayProductList_class (n : ℕ) {p k : ℕ} (hp : Nat.Prime p)
    (xs : List (cyclotomicFixedArray n p k)) :
    cyclotomicFixedArrayClass n p k (cyclotomicFixedArrayProductList n hp xs) =
      (xs.map (cyclotomicFixedArrayClass n p k)).prod := by
  unfold cyclotomicFixedArrayProductList
  have hfold :
    ∀ (ys : List (cyclotomicFixedArray n p k)) (initial : cyclotomicFixedArray n p k),
      cyclotomicFixedArrayClass n p k
          (ys.foldl (fun a b ↦ cyclotomicFixedArrayMulByExpansion n hp a b) initial) =
        cyclotomicFixedArrayClass n p k initial *
          (ys.map (cyclotomicFixedArrayClass n p k)).prod := by
    intro ys
    induction ys with
    | nil =>
      intro initial
      simp only [List.foldl_nil, List.map_nil, List.prod_nil, mul_one]
    | cons x ys ih =>
      intro initial
      simp only [List.foldl_cons, List.map_cons, List.prod_cons]
      rw [ih]
      rw [cyclotomicFixedArrayMulByExpansion_class_eq_mul n hp]
      rw [mul_assoc]
  rw [hfold]
  rw [cyclotomicFixedArrayOne_class n hp, one_mul]

/-- Decoding an iterated coefficient-array power gives the corresponding quotient power. -/
theorem cyclotomicFixedArrayPowByMul_class (n : ℕ) {p k : ℕ} (hp : Nat.Prime p)
    (a : cyclotomicFixedArray n p k) (e : ℕ) :
    cyclotomicFixedArrayClass n p k (cyclotomicFixedArrayPowByMul n hp a e) =
      cyclotomicFixedArrayClass n p k a ^ e := by
  induction e with
  | zero =>
    rw [cyclotomicFixedArrayPowByMul, cyclotomicFixedArrayPowByMulArray,
      cyclotomicFixedArrayOfArray_ofFn, cyclotomicFixedArrayOne_class n hp, pow_zero]
  | succ e ih =>
    simp only [cyclotomicFixedArrayPowByMul, cyclotomicFixedArrayPowByMulArray]
    have hprev :
      (fun j : Fin (primePowerDegree p k) =>
          (cyclotomicFixedArrayPowByMulArray n hp a e).getD j.val 0) =
        cyclotomicFixedArrayPowByMul n hp a e :=
      rfl
    rw [hprev, cyclotomicFixedArrayMulByTableArray_asFunction]
    change
      cyclotomicFixedArrayClass n p k
          (cyclotomicFixedArrayMulByExpansion n hp (cyclotomicFixedArrayPowByMul n hp a e) a) =
        _
    rw [cyclotomicFixedArrayMulByExpansion_class_eq_mul n hp, ih, pow_succ]

/-- Binary-array exponentiation represents the corresponding quotient-ring power. -/
theorem cyclotomicFixedArrayPowBySquaringArray_class (n : ℕ) {p k : ℕ} (hp : Nat.Prime p)
    (a : cyclotomicFixedArray n p k) (e : ℕ) :
    cyclotomicFixedArrayClass n p k
        (cyclotomicFixedArrayOfArray n p k (cyclotomicFixedArrayPowBySquaringArray n hp a e)) =
      cyclotomicFixedArrayClass n p k a ^ e := by
  induction e using Nat.binaryRecFromOne with
  | zero =>
    rw [cyclotomicFixedArrayPowBySquaringArray, Nat.binaryRecFromOne_zero]
    rw [cyclotomicFixedArrayOfArray_ofFn, cyclotomicFixedArrayOne_class n hp, pow_zero]
  | one =>
    rw [cyclotomicFixedArrayPowBySquaringArray, Nat.binaryRecFromOne_one]
    rw [cyclotomicFixedArrayOfArray_ofFn]
    exact (pow_one _).symm
  | bit b m hm
    ih =>
    rw [cyclotomicFixedArrayPowBySquaringArray, Nat.binaryRecFromOne_eq b m hm]
    have hstep :=
      cyclotomicFixedArrayPowBySquaringStep_class n hp a b
        (Nat.binaryRecFromOne (Array.ofFn (cyclotomicFixedArrayOne n p k)) (Array.ofFn a)
          (fun b _ _ previous => cyclotomicFixedArrayPowBySquaringStep n hp a b previous) m)
    change _ = cyclotomicFixedArrayClass n p k a ^ Nat.bit b m
    rw [hstep]
    change
      (if b = true then
          (cyclotomicFixedArrayClass n p k
                (cyclotomicFixedArrayOfArray n p k
                  (cyclotomicFixedArrayPowBySquaringArray n hp a m))) ^
              2 *
            cyclotomicFixedArrayClass n p k a
        else
          (cyclotomicFixedArrayClass n p k
              (cyclotomicFixedArrayOfArray n p k
                (cyclotomicFixedArrayPowBySquaringArray n hp a m))) ^
            2) =
        _
    rw [ih]
    cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true]
    · rw [Nat.bit_false_apply]
      calc
        _ = cyclotomicFixedArrayClass n p k a ^ (m * 2) := (pow_mul _ _ _).symm
        _ = cyclotomicFixedArrayClass n p k a ^ (2 * m) := by rw [Nat.mul_comm]
    · rw [Nat.bit_true_apply]
      calc
        _ = cyclotomicFixedArrayClass n p k a ^ (m * 2) * cyclotomicFixedArrayClass n p k a := by
          rw [← pow_mul]
        _ = cyclotomicFixedArrayClass n p k a ^ (m * 2 + 1) := by rw [pow_succ]
        _ = cyclotomicFixedArrayClass n p k a ^ (2 * m + 1) := by rw [Nat.mul_comm]

/-- Function-interface view of the materialized binary exponentiation result. -/
def cyclotomicFixedArrayPowBySquaring (n : ℕ) {p k : ℕ} (hp : Nat.Prime p)
    (a : cyclotomicFixedArray n p k) (e : ℕ) : cyclotomicFixedArray n p k :=
  cyclotomicFixedArrayOfArray n p k (cyclotomicFixedArrayPowBySquaringArray n hp a e)

/-- The binary exponentiation result represents the corresponding quotient power. -/
theorem cyclotomicFixedArrayPowBySquaring_class (n : ℕ) {p k : ℕ} (hp : Nat.Prime p)
    (a : cyclotomicFixedArray n p k) (e : ℕ) :
    cyclotomicFixedArrayClass n p k (cyclotomicFixedArrayPowBySquaring n hp a e) =
      cyclotomicFixedArrayClass n p k a ^ e :=
  cyclotomicFixedArrayPowBySquaringArray_class n hp a e

/-- Exponentiate each array in a finite ordered family by binary powering, then multiply the
results with the executable expansion backend. This is the array implementation of a weighted
finite product. -/
def cyclotomicFixedArrayWeightedProductList (n : ℕ) {p k : ℕ} (hp : Nat.Prime p) {α : Type*}
    (xs : List α) (term : α → cyclotomicFixedArray n p k) (weight : α → ℕ) :
    cyclotomicFixedArray n p k :=
  cyclotomicFixedArrayProductList n hp
    (xs.map (fun x => cyclotomicFixedArrayPowBySquaring n hp (term x) (weight x)))

/-- Decode the executable weighted array product to the finite product of corresponding quotient
powers. This is the finite-product interface for APR-CL weighted updates. -/
theorem cyclotomicFixedArrayWeightedProductList_class (n : ℕ) {p k : ℕ} (hp : Nat.Prime p)
    {α : Type*} (xs : List α) (term : α → cyclotomicFixedArray n p k) (weight : α → ℕ) :
    cyclotomicFixedArrayClass n p k (cyclotomicFixedArrayWeightedProductList n hp xs term weight) =
      (xs.map (fun x => cyclotomicFixedArrayClass n p k (term x) ^ weight x)).prod := by
  unfold cyclotomicFixedArrayWeightedProductList
  rw [cyclotomicFixedArrayProductList_class]
  rw [List.map_map]
  apply congrArg List.prod
  apply List.map_congr_left
  intro x _
  exact cyclotomicFixedArrayPowBySquaring_class n hp (term x) (weight x)

/-- Fixed-array representative of the canonical cyclotomic root. -/
def cyclotomicFixedArrayRoot (n : ℕ) {p k : ℕ} (hp : Nat.Prime p) : cyclotomicFixedArray n p k :=
  cyclotomicFixedArrayMonomialReduce n hp 1

/-- The fixed-array root decodes to the canonical quotient root. -/
theorem cyclotomicFixedArrayRoot_class (n : ℕ) {p k : ℕ} (hp : Nat.Prime p) :
    cyclotomicFixedArrayClass n p k (cyclotomicFixedArrayRoot n hp) = cyclotomicRoot n p k := by
  simpa only [cyclotomicFixedArrayRoot, pow_one] using
    (cyclotomicFixedArrayMonomialReduce_correct n (p := p) (k := k) hp 1)

/-- The canonical root has order dividing the selected prime-power index. -/
theorem cyclotomicRoot_pow_index_eq_one (n : ℕ) {p k : ℕ} (hp : Nat.Prime p) :
    cyclotomicRoot n p k ^ primePowerIndex p k = 1 := by
  let f := primePowerCyclotomic p k (ZMod n)
  have hpoly : f * (Polynomial.X ^ p ^ k - 1) = Polynomial.X ^ p ^ (k + 1) - 1 := by
    change primePowerCyclotomic p k (ZMod n) * _ = _
    rw [primePowerCyclotomic_eq_cyclotomic hp]
    exact @Polynomial.cyclotomic_prime_pow_mul_X_pow_sub_one (ZMod n) inferInstance p k (Fact.mk hp)
  have heval := congrArg (Polynomial.eval₂ (AdjoinRoot.of f) (cyclotomicRoot n p k)) hpoly
  have hroot : Polynomial.eval₂ (AdjoinRoot.of f) (cyclotomicRoot n p k) f = 0 :=
    AdjoinRoot.eval₂_root f
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_one, hroot, zero_mul] at heval
  exact sub_eq_zero.mp heval.symm

/-- The canonical prime-power root is a unit, with inverse given by its penultimate power.
This packages the order-dividing-period theorem for use as a multiplicative character value. -/
noncomputable def cyclotomicRootUnit (n : ℕ) {p k : ℕ} (hp : Nat.Prime p) :
    (cyclotomicQuotient n p k)ˣ :=
  Units.mkOfMulEqOne (cyclotomicRoot n p k) (cyclotomicRoot n p k ^ (primePowerIndex p k - 1))
    (by
      have hindex : 0 < primePowerIndex p k := Nat.pow_pos hp.pos
      calc
        cyclotomicRoot n p k * cyclotomicRoot n p k ^ (primePowerIndex p k - 1) =
            cyclotomicRoot n p k ^ 1 * cyclotomicRoot n p k ^ (primePowerIndex p k - 1) :=
          by rw [pow_one]
        _ = cyclotomicRoot n p k ^ (1 + (primePowerIndex p k - 1)) := by rw [← pow_add]
        _ = cyclotomicRoot n p k ^ (primePowerIndex p k - 1 + 1) := by rw [Nat.add_comm]
        _ = cyclotomicRoot n p k ^ primePowerIndex p k := by
          rw [Nat.sub_add_cancel (n := primePowerIndex p k) (m := 1) (Nat.succ_le_iff.mpr hindex)]
        _ = 1 := cyclotomicRoot_pow_index_eq_one n hp)

/-- Coercing the canonical root unit to the quotient ring returns the canonical root. -/
theorem cyclotomicRootUnit_val (n : ℕ) {p k : ℕ} (hp : Nat.Prime p) :
    (cyclotomicRootUnit n (p := p) (k := k) hp : cyclotomicQuotient n p k) =
      cyclotomicRoot n p k := by
  rfl

/-- Powers with exponents equal modulo a period agree when the period power is one. -/
private theorem power_mod_period_eq {S : Type*} [Monoid S] (x : S) (period e : ℕ)
    (hperiod : x ^ period = 1) : x ^ (e % period) = x ^ e := by
  calc
    x ^ (e % period) = x ^ (e % period) * 1 := by rw [mul_one]
    _ = x ^ (e % period) * (x ^ period) ^ (e / period) := by rw [hperiod, one_pow]
    _ = x ^ (e % period + period * (e / period)) := by rw [← pow_mul, ← pow_add]
    _ = x ^ e := by rw [Nat.mod_add_div]

/-- Substitute the `u`-th power of the canonical root for `X` in a represented polynomial.
Each exponent is reduced modulo the root period before coefficient reduction, avoiding repeated
recursive expansion of large exponents. -/
def cyclotomicFixedArraySubstitutePower (n : ℕ) {p k : ℕ} (hp : Nat.Prime p)
    (a : cyclotomicFixedArray n p k) (u : ℕ) : cyclotomicFixedArray n p k :=
  ∑ i : Fin (primePowerDegree p k),
    cyclotomicFixedArrayScale n p k (a i)
      (cyclotomicFixedArrayMonomialReduce n hp (i.val * u % primePowerIndex p k))

/-- Power substitution is additive on coefficient arrays. This linearity is unconditional;
well-definedness on the quotient still requires the cyclotomic root relation. -/
theorem cyclotomicFixedArraySubstitutePower_add (n : ℕ) {p k : ℕ} (hp : Nat.Prime p)
    (a b : cyclotomicFixedArray n p k) (u : ℕ) :
    cyclotomicFixedArraySubstitutePower n hp (cyclotomicFixedArrayAdd n p k a b) u =
      cyclotomicFixedArrayAdd n p k (cyclotomicFixedArraySubstitutePower n hp a u)
        (cyclotomicFixedArraySubstitutePower n hp b u) := by
  funext j
  unfold cyclotomicFixedArraySubstitutePower cyclotomicFixedArrayAdd
  simp only [Finset.sum_apply, cyclotomicFixedArrayScale]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [add_mul]

/-- Power substitution commutes with scalar multiplication of coefficient arrays.
Together with additivity, this gives the coefficient-level linearity needed for the
quotient homomorphism construction. -/
theorem cyclotomicFixedArraySubstitutePower_scale (n : ℕ) {p k : ℕ} (hp : Nat.Prime p)
    (a : cyclotomicFixedArray n p k) (c : ZMod n) (u : ℕ) :
    cyclotomicFixedArraySubstitutePower n hp (cyclotomicFixedArrayScale n p k c a) u =
      cyclotomicFixedArrayScale n p k c (cyclotomicFixedArraySubstitutePower n hp a u) := by
  funext j
  unfold cyclotomicFixedArraySubstitutePower cyclotomicFixedArrayScale
  simp only [Finset.sum_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The substitution represents evaluation of the coefficient polynomial at `root ^ u`.
This specification is valid for every exponent; the automorphism property needs extra hypotheses.
-/
theorem cyclotomicFixedArraySubstitutePower_class (n : ℕ) {p k : ℕ} (hp : Nat.Prime p)
    (a : cyclotomicFixedArray n p k) (u : ℕ) :
    cyclotomicFixedArrayClass n p k (cyclotomicFixedArraySubstitutePower n hp a u) =
      ∑ i : Fin (primePowerDegree p k),
        AdjoinRoot.of (primePowerCyclotomic p k (ZMod n)) (a i) *
          cyclotomicRoot n p k ^ (i.val * u) := by
  rw [cyclotomicFixedArraySubstitutePower, cyclotomicFixedArrayClass_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [cyclotomicFixedArrayClass_scale, cyclotomicFixedArrayMonomialReduce_correct]
  exact
    congrArg (fun x => AdjoinRoot.of (primePowerCyclotomic p k (ZMod n)) (a i) * x)
      (by
        calc
          cyclotomicRoot n p k ^ (i.val * u % primePowerIndex p k) =
              cyclotomicRoot n p k ^ (i.val * u) :=
            power_mod_period_eq (cyclotomicRoot n p k) (primePowerIndex p k) (i.val * u)
              (cyclotomicRoot_pow_index_eq_one n hp))

/-- The coefficient substitution is polynomial evaluation at the powered root. -/
theorem cyclotomicFixedArraySubstitutePower_eq_eval₂ (n : ℕ) {p k : ℕ} (hp : Nat.Prime p)
    (a : cyclotomicFixedArray n p k) (u : ℕ) :
    cyclotomicFixedArrayClass n p k (cyclotomicFixedArraySubstitutePower n hp a u) =
      Polynomial.eval₂ (AdjoinRoot.of (primePowerCyclotomic p k (ZMod n)))
        (cyclotomicRoot n p k ^ u) (cyclotomicFixedArrayPolynomial n p k a) := by
  rw [cyclotomicFixedArraySubstitutePower_class]
  change
    (∑ i : Fin (primePowerDegree p k),
        AdjoinRoot.of (primePowerCyclotomic p k (ZMod n)) (a i) *
          cyclotomicRoot n p k ^ (i.val * u)) =
      (Polynomial.eval₂RingHom (AdjoinRoot.of (primePowerCyclotomic p k (ZMod n)))
          (cyclotomicRoot n p k ^ u))
        (∑ i : Fin (primePowerDegree p k), Polynomial.monomial i.val (a i))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  change
    _ =
      Polynomial.eval₂ (AdjoinRoot.of (primePowerCyclotomic p k (ZMod n)))
        (cyclotomicRoot n p k ^ u) (Polynomial.monomial i.val (a i))
  rw [Polynomial.eval₂_monomial]
  congr 1
  rw [Nat.mul_comm i.val u, pow_mul]

/-- A represented fixed-array polynomial is already reduced modulo the monic relation. -/
theorem cyclotomicFixedArrayPolynomial_modByMonic (n : ℕ) (hn : 1 < n) {p k : ℕ} (hp : Nat.Prime p)
    (a : cyclotomicFixedArray n p k) :
    Polynomial.modByMonic (cyclotomicFixedArrayPolynomial n p k a)
        (primePowerCyclotomic p k (ZMod n)) =
      cyclotomicFixedArrayPolynomial n p k a := by
  let : Nontrivial (ZMod n) := ZMod.nontrivial_iff.mpr hn.ne'
  apply (Polynomial.modByMonic_eq_self_iff (primePowerCyclotomic_monic hp (ZMod n))).mpr
  have hlt := cyclotomicFixedArrayPolynomial_natDegree_lt n p k hp a
  have hq := primePowerCyclotomic_natDegree (p := p) (k := k) hp (ZMod n)
  have hqne : primePowerCyclotomic p k (ZMod n) ≠ 0 :=
    (primePowerCyclotomic_monic hp (ZMod n)).ne_zero
  have hmpos : 0 < primePowerDegree p k := by
    rw [primePowerDegree]
    exact Nat.mul_pos (Nat.sub_pos_of_lt hp.one_lt) (Nat.pow_pos hp.pos)
  by_cases hne : cyclotomicFixedArrayPolynomial n p k a ≠ 0
  · rw [Polynomial.degree_eq_natDegree hne, Polynomial.degree_eq_natDegree hqne, hq]
    exact_mod_cast hlt
  · rw [not_ne_iff.mp hne]
    rw [Polynomial.degree_eq_natDegree hqne, hq]
    rw [Polynomial.degree_zero]
    exact WithBot.bot_lt_coe _

/-- Distinct fixed coefficient arrays represent distinct quotient elements for `n > 1`. -/
theorem cyclotomicFixedArrayClass_injective (n : ℕ) (hn : 1 < n) {p k : ℕ} (hp : Nat.Prime p) :
    Function.Injective (cyclotomicFixedArrayClass n p k) := by
  intro a b hab
  have hrem := congrArg (AdjoinRoot.modByMonicHom (primePowerCyclotomic_monic hp (ZMod n))) hab
  simp only [cyclotomicFixedArrayClass, AdjoinRoot.modByMonicHom_mk] at hrem
  rw [cyclotomicFixedArrayPolynomial_modByMonic n hn hp,
    cyclotomicFixedArrayPolynomial_modByMonic n hn hp] at hrem
  funext j
  have hcoeff := congrArg (fun f : Polynomial (ZMod n) => f.coeff j.val) hrem
  rw [cyclotomicFixedArrayPolynomial_coeff, cyclotomicFixedArrayPolynomial_coeff] at hcoeff
  simpa only [cyclotomicFixedArrayCoeff, j.isLt, dite_eq_left, ite_eq_left] using hcoeff

/-- Binary exponentiation agrees coefficientwise with the repeated-multiplication reference. -/
theorem cyclotomicFixedArrayPowBySquaring_eq_powByMul (n : ℕ) (hn : 1 < n) {p k : ℕ}
    (hp : Nat.Prime p) (a : cyclotomicFixedArray n p k) (e : ℕ) :
    cyclotomicFixedArrayPowBySquaring n hp a e = cyclotomicFixedArrayPowByMul n hp a e := by
  apply cyclotomicFixedArrayClass_injective n hn hp
  rw [cyclotomicFixedArrayPowBySquaring_class, cyclotomicFixedArrayPowByMul_class]

/-- The dedicated materialized square agrees with exponent two in the generic power API.
Injectivity transfers the quotient-ring square specification back to coefficients. -/
theorem cyclotomicFixedArraySquare_eq_pow_two (n : ℕ) (hn : 1 < n) {p k : ℕ} (hp : Nat.Prime p)
    (a : cyclotomicFixedArray n p k) :
    cyclotomicFixedArraySquare n hp a = cyclotomicFixedArrayPowByMul n hp a 2 := by
  apply cyclotomicFixedArrayClass_injective n hn hp
  rw [cyclotomicFixedArraySquare_class, cyclotomicFixedArrayPowByMul_class]

/-- Array-power equality is equivalent to equality of the corresponding quotient powers. -/
theorem cyclotomicFixedArrayPowByMul_root_eq_iff (n : ℕ) (hn : 1 < n) {p k : ℕ} (hp : Nat.Prime p)
    (a : cyclotomicFixedArray n p k) (e : ℕ) :
    cyclotomicFixedArrayPowByMul n hp (cyclotomicFixedArrayRoot n hp) e = a ↔
      cyclotomicRoot n p k ^ e = cyclotomicFixedArrayClass n p k a := by
  constructor
  · intro h
    have hc := congrArg (cyclotomicFixedArrayClass n p k) h
    rw [cyclotomicFixedArrayPowByMul_class, cyclotomicFixedArrayRoot_class] at hc
    exact hc
  · intro h
    apply cyclotomicFixedArrayClass_injective n hn hp
    rw [cyclotomicFixedArrayPowByMul_class, cyclotomicFixedArrayRoot_class]
    exact h

/-- Equality with a reduced monomial detects the corresponding root power when `1 < n`.
Injectivity of the coefficient representation transfers monomial correctness to the search. -/
theorem cyclotomicFixedArrayMonomialReduce_eq_iff (n : ℕ) (hn : 1 < n) {p k : ℕ} (hp : Nat.Prime p)
    (a : cyclotomicFixedArray n p k) (e : ℕ) :
    cyclotomicFixedArrayMonomialReduce n hp e = a ↔
      cyclotomicRoot n p k ^ e = cyclotomicFixedArrayClass n p k a := by
  rw [← cyclotomicFixedArrayMonomialReduce_correct n hp e]
  exact (cyclotomicFixedArrayClass_injective n hn hp).eq_iff.symm

/-- Search for the least root exponent by comparing reduced monomials with `a`.
The search interval bounds monomial reduction to one recursive level; no general
array multiplication, repeated powering, or multiplication reduction table is needed. -/
def cyclotomicFixedArrayRootExponent (n : ℕ) {p k : ℕ} (hp : Nat.Prime p)
    (a : cyclotomicFixedArray n p k) : Option ℕ :=
  (List.range (primePowerIndex p k)).find?
    (fun e =>
      decide (∀ j : Fin (primePowerDegree p k), cyclotomicFixedArrayMonomialReduce n hp e j = a j))

/-- Expansion multiplication has the monic-remainder coefficients of the input product. -/
theorem cyclotomicFixedArrayMulByExpansion_eq_remainder (n : ℕ) (hn : 1 < n) {p k : ℕ}
    (hp : Nat.Prime p) (a b : cyclotomicFixedArray n p k) :
    cyclotomicFixedArrayMulByExpansion n hp a b = fun i =>
      (Polynomial.modByMonic
            (cyclotomicFixedArrayPolynomial n p k a * cyclotomicFixedArrayPolynomial n p k b)
            (primePowerCyclotomic p k (ZMod n))).coeff
        i.val := by
  let f := primePowerCyclotomic p k (ZMod n)
  have : Nontrivial (ZMod n) := ZMod.nontrivial_iff.mpr hn.ne'
  have hclass := cyclotomicFixedArrayMulByExpansion_class_eq_mul n hp a b
  have hmk :
    (AdjoinRoot.mk f) (cyclotomicFixedArrayPolynomial n p k a) *
        (AdjoinRoot.mk f) (cyclotomicFixedArrayPolynomial n p k b) =
      (AdjoinRoot.mk f)
        (cyclotomicFixedArrayPolynomial n p k a * cyclotomicFixedArrayPolynomial n p k b) :=
    map_mul (AdjoinRoot.mk f) _ _
  simp only [cyclotomicFixedArrayClass] at hclass
  rw [hmk] at hclass
  have hrem := congrArg (AdjoinRoot.modByMonicHom (primePowerCyclotomic_monic hp (ZMod n))) hclass
  rw [AdjoinRoot.modByMonicHom_mk, AdjoinRoot.modByMonicHom_mk] at hrem
  rw [cyclotomicFixedArrayPolynomial_modByMonic n hn hp] at hrem
  funext i
  have hi := congrArg (fun q : Polynomial (ZMod n) => q.coeff i.val) hrem
  simpa only [cyclotomicFixedArrayPolynomial_coeff, cyclotomicFixedArrayCoeff, i.isLt,
    dite_true] using hi

/-- The double geometric sum converts the prime-length cyclotomic relation into
the unit multiple `-p` over any commutative ring. -/
private theorem geometric_sum_double_identity {S : Type*} [CommRing S] (x : S) (m : ℕ) :
    (∑ i ∈ Finset.range m, x ^ i) - (m : S) =
      (x - 1) * ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range i, x ^ j := by
  induction m with
  | zero => simp only [Finset.sum_range_zero, Nat.cast_zero, sub_zero, mul_zero]
  | succ m ih =>
    calc
      (∑ i ∈ Finset.range (m + 1), x ^ i) - ((m + 1 : ℕ) : S) =
          ((∑ i ∈ Finset.range m, x ^ i) - (m : S)) + (x ^ m - 1) :=
        by
        simp only [Finset.sum_range_succ, Nat.cast_succ]
        ring
      _ =
          (x - 1) * (∑ i ∈ Finset.range m, ∑ j ∈ Finset.range i, x ^ j) +
            (x - 1) * (∑ j ∈ Finset.range m, x ^ j) :=
        by rw [ih, mul_geom_sum]
      _ = (x - 1) * ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range i, x ^ j := by
        simp only [Finset.sum_range_succ]
        rw [mul_add]

/-- A vanishing geometric sum of length `p` makes `x - 1` a unit whenever
the scalar `p` is a unit. This argument does not require a domain. -/
private theorem isUnit_sub_one_of_geometric_sum_zero {S : Type*} [CommRing S] {p : ℕ}
    (hp : IsUnit (p : S)) {x : S} (hsum : (∑ i ∈ Finset.range p, x ^ i) = 0) : IsUnit (x - 1) := by
  have h := geometric_sum_double_identity x p
  rw [hsum, zero_sub] at h
  have hprod : IsUnit ((x - 1) * ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range i, x ^ j) := by
    rw [← h]
    exact hp.neg
  exact (IsUnit.mul_iff.mp hprod).1

/-- If `x ^ p = 1` and `x - 1` is a unit, then any exponent coprime to `p`
also has unit difference. -/
private theorem isUnit_power_sub_one_of_period {S : Type*} [CommRing S] (x : S) (p u v t : ℕ)
    (hperiod : x ^ p = 1) (hunit : IsUnit (x - 1)) (hprod : u * v = p * t + 1) :
    IsUnit (x ^ u - 1) := by
  have hinverse : (x ^ u) ^ v = x := by
    rw [← pow_mul, hprod, pow_add, pow_mul, hperiod, one_pow, pow_one, one_mul]
  have hgeom := mul_geom_sum (x ^ u) v
  rw [hinverse] at hgeom
  have hmul : IsUnit ((x ^ u - 1) * ∑ i ∈ Finset.range v, (x ^ u) ^ i) := by
    rw [hgeom]
    exact hunit
  exact (IsUnit.mul_iff.mp hmul).1

/-- The canonical prime-power root has unit difference after raising it to `p^k`,
provided `p` is coprime to the coefficient modulus. -/
theorem cyclotomicRoot_power_step_sub_one_isUnit (n p k : ℕ) (hcp : Nat.Coprime p n) :
    IsUnit (cyclotomicRoot n p k ^ p ^ k - 1) := by
  let f := primePowerCyclotomic p k (ZMod n)
  have hpunit : IsUnit (p : ZMod n) := (ZMod.isUnit_iff_coprime p n).2 hcp
  have hpun : IsUnit (p : cyclotomicQuotient n p k) := by
    simpa only [map_natCast] using hpunit.map (AdjoinRoot.of f)
  have hroot := AdjoinRoot.eval₂_root f
  have hsum : (∑ i ∈ Finset.range p, (cyclotomicRoot n p k ^ p ^ k) ^ i) = 0 := by
    change
      Polynomial.eval₂ (AdjoinRoot.of (∑ i ∈ Finset.range p, (Polynomial.X ^ p ^ k) ^ i))
          (AdjoinRoot.root (∑ i ∈ Finset.range p, (Polynomial.X ^ p ^ k) ^ i))
          (∑ i ∈ Finset.range p, (Polynomial.X ^ p ^ k) ^ i) =
        0 at hroot
    rw [Polynomial.eval₂_finsetSum] at hroot
    simp only [Polynomial.eval₂_pow, Polynomial.eval₂_X] at hroot
    exact hroot
  exact isUnit_sub_one_of_geometric_sum_zero hpun hsum

/-- If `u` is coprime to `p`, then the denominator required by the power
substitution is a unit. The inverse exponent modulo `p` expresses the powered
root as a power of the canonical unit-difference root. -/
theorem cyclotomicRoot_power_substitution_denominator_isUnit (n : ℕ) {p k u : ℕ} (hp : Nat.Prime p)
    (hcp : Nat.Coprime p n) (hup : Nat.Coprime u p) :
    IsUnit ((cyclotomicRoot n p k ^ u) ^ (p ^ k) - 1) := by
  obtain ⟨v, _, hmod⟩ := Nat.exists_mul_mod_eq_one_of_coprime hup hp.one_lt
  let t := u * v / p
  have hprod : u * v = p * t + 1 := by
    calc
      u * v = u * v % p + p * (u * v / p) := (Nat.mod_add_div (u * v) p).symm
      _ = 1 + p * (u * v / p) := by rw [hmod]
      _ = p * (u * v / p) + 1 := Nat.add_comm _ _
  have hperiod : (cyclotomicRoot n p k ^ p ^ k) ^ p = 1 := by
    rw [← pow_mul, ← Nat.pow_succ]
    exact cyclotomicRoot_pow_index_eq_one n hp
  have hunit :=
    isUnit_power_sub_one_of_period (cyclotomicRoot n p k ^ p ^ k) p u v t hperiod
      (cyclotomicRoot_power_step_sub_one_isUnit n p k hcp) hprod
  simpa only [← pow_mul, Nat.mul_comm] using hunit

/-- The explicit prime-power cyclotomic polynomial vanishes at `x` when `x` has
the required prime-power period and the preceding power minus one is a unit.
The unit condition permits cancellation in the geometric-sum identity over rings
that may have zero divisors. -/
theorem primePowerCyclotomic_eval_eq_zero_of_unit {R S : Type*} [CommRing R] [CommRing S] (p k : ℕ)
    (f : R →+* S) (x : S) (hpow : x ^ (p ^ k * p) = 1) (hunit : IsUnit (x ^ (p ^ k) - 1)) :
    Polynomial.eval₂ f x (primePowerCyclotomic p k R) = 0 := by
  rw [primePowerCyclotomic, Polynomial.eval₂_finsetSum]
  simp only [Polynomial.eval₂_pow, Polynomial.eval₂_X]
  have hgeom := mul_geom_sum (x ^ p ^ k) p
  have hsum : (x ^ p ^ k - 1) * ∑ i ∈ Finset.range p, (x ^ p ^ k) ^ i = 0 := by
    calc
      _ = (x ^ p ^ k) ^ p - 1 := hgeom
      _ = x ^ (p ^ k * p) - 1 := by rw [pow_mul]
      _ = 0 := by
        rw [hpow]
        exact sub_self 1
  have hsum' : (∑ i ∈ Finset.range p, (x ^ p ^ k) ^ i) * (x ^ p ^ k - 1) = 0 := by
    rw [mul_comm]
    exact hsum
  have hc : (∑ i ∈ Finset.range p, (x ^ p ^ k) ^ i) * (x ^ p ^ k - 1) = 0 * (x ^ p ^ k - 1) := by
    rw [zero_mul]
    exact hsum'
  exact (hunit.mul_left_inj).mp hc

/-- Substituting a power of the quotient root preserves the defining relation
whenever the corresponding geometric denominator is a unit. -/
theorem cyclotomicRoot_power_substitution_relation_of_unit (n : ℕ) {p k : ℕ} (hp : Nat.Prime p)
    (u : ℕ) (hunit : IsUnit ((cyclotomicRoot n p k ^ u) ^ (p ^ k) - 1)) :
    Polynomial.eval₂ (AdjoinRoot.of (primePowerCyclotomic p k (ZMod n))) (cyclotomicRoot n p k ^ u)
        (primePowerCyclotomic p k (ZMod n)) =
      0 := by
  apply
    primePowerCyclotomic_eval_eq_zero_of_unit p k
      (AdjoinRoot.of (primePowerCyclotomic p k (ZMod n))) (cyclotomicRoot n p k ^ u) ?_ hunit
  have hindex : p ^ k * p = primePowerIndex p k := by simp only [primePowerIndex, Nat.pow_succ]
  rw [← pow_mul]
  rw [Nat.mul_comm u (p ^ k * p)]
  rw [pow_mul]
  rw [hindex, cyclotomicRoot_pow_index_eq_one n hp, one_pow]

/-- Ring homomorphism induced by substituting the `u`-th power of the canonical root.
Its explicit unit hypothesis is the relation-preservation condition over a possibly
non-domain coefficient quotient. -/
def cyclotomicRootPowerSubstitutionHom (n : ℕ) {p k : ℕ} (hp : Nat.Prime p) (u : ℕ)
    (hunit : IsUnit ((cyclotomicRoot n p k ^ u) ^ (p ^ k) - 1)) :
    cyclotomicQuotient n p k →+* cyclotomicQuotient n p k :=
  AdjoinRoot.lift (AdjoinRoot.of (primePowerCyclotomic p k (ZMod n))) (cyclotomicRoot n p k ^ u)
    (cyclotomicRoot_power_substitution_relation_of_unit n hp u hunit)

/-- The induced quotient homomorphism realizes the coefficient-array power substitution. -/
theorem cyclotomicRootPowerSubstitutionHom_class (n : ℕ) {p k : ℕ} (hp : Nat.Prime p) (u : ℕ)
    (hunit : IsUnit ((cyclotomicRoot n p k ^ u) ^ (p ^ k) - 1)) (a : cyclotomicFixedArray n p k) :
    cyclotomicRootPowerSubstitutionHom n hp u hunit (cyclotomicFixedArrayClass n p k a) =
      cyclotomicFixedArrayClass n p k (cyclotomicFixedArraySubstitutePower n hp a u) := by
  change
    (AdjoinRoot.lift (AdjoinRoot.of (primePowerCyclotomic p k (ZMod n))) (cyclotomicRoot n p k ^ u)
          (cyclotomicRoot_power_substitution_relation_of_unit n hp u hunit))
        ((AdjoinRoot.mk (primePowerCyclotomic p k (ZMod n)))
          (cyclotomicFixedArrayPolynomial n p k a)) =
      _
  rw [AdjoinRoot.lift_mk]
  rw [← cyclotomicFixedArraySubstitutePower_eq_eval₂]

/-- Power-substitution homomorphism when coprimality with the coefficient modulus
proves the defining-relation denominator is a unit. -/
def cyclotomicRootPowerSubstitutionHom_of_coprime (n : ℕ) {p k u : ℕ} (hp : Nat.Prime p)
    (hpn : Nat.Coprime p n) (hup : Nat.Coprime u p) :
    cyclotomicQuotient n p k →+* cyclotomicQuotient n p k :=
  cyclotomicRootPowerSubstitutionHom n hp u
    (cyclotomicRoot_power_substitution_denominator_isUnit n hp hpn hup)

/-- The coprimality-derived homomorphism acts on coefficient arrays by the
period-reduced executable substitution. -/
theorem cyclotomicRootPowerSubstitutionHom_of_coprime_class (n : ℕ) {p k u : ℕ} (hp : Nat.Prime p)
    (hpn : Nat.Coprime p n) (hup : Nat.Coprime u p) (a : cyclotomicFixedArray n p k) :
    cyclotomicRootPowerSubstitutionHom_of_coprime n hp hpn hup (cyclotomicFixedArrayClass n p k a) =
      cyclotomicFixedArrayClass n p k (cyclotomicFixedArraySubstitutePower n hp a u) := by
  exact
    cyclotomicRootPowerSubstitutionHom_class n hp u
      (cyclotomicRoot_power_substitution_denominator_isUnit n hp hpn hup) a

/-- Two conditional power substitutions compose to the identity when their exponents
multiply to one modulo the root period. This gives the inverse law before proving the
APR-CL arithmetic hypotheses that supply the required denominator units. -/
theorem cyclotomicRootPowerSubstitutionHom_comp_eq_id (n : ℕ) {p k : ℕ} (hp : Nat.Prime p)
    (u v t : ℕ) (hu : IsUnit ((cyclotomicRoot n p k ^ u) ^ (p ^ k) - 1))
    (hv : IsUnit ((cyclotomicRoot n p k ^ v) ^ (p ^ k) - 1))
    (hprod : u * v = primePowerIndex p k * t + 1) :
    (cyclotomicRootPowerSubstitutionHom n hp u hu).comp
        (cyclotomicRootPowerSubstitutionHom n hp v hv) =
      RingHom.id (cyclotomicQuotient n p k) := by
  apply AdjoinRoot.ringHom_ext
  · ext a
    simp only [RingHom.comp_apply, cyclotomicRootPowerSubstitutionHom, AdjoinRoot.lift_of,
      RingHom.id_apply]
  · change
      (AdjoinRoot.lift (AdjoinRoot.of (primePowerCyclotomic p k (ZMod n)))
            (cyclotomicRoot n p k ^ u)
            (cyclotomicRoot_power_substitution_relation_of_unit n hp u hu))
          ((AdjoinRoot.lift (AdjoinRoot.of (primePowerCyclotomic p k (ZMod n)))
              (cyclotomicRoot n p k ^ v)
              (cyclotomicRoot_power_substitution_relation_of_unit n hp v hv))
            (AdjoinRoot.root (primePowerCyclotomic p k (ZMod n)))) =
        AdjoinRoot.root (primePowerCyclotomic p k (ZMod n))
    rw [AdjoinRoot.lift_root (cyclotomicRoot_power_substitution_relation_of_unit n hp v hv)]
    rw [map_pow]
    change
      (AdjoinRoot.lift (AdjoinRoot.of (primePowerCyclotomic p k (ZMod n)))
            (cyclotomicRoot n p k ^ u)
            (cyclotomicRoot_power_substitution_relation_of_unit n hp u hu)
            (AdjoinRoot.root (primePowerCyclotomic p k (ZMod n)))) ^
          v =
        AdjoinRoot.root (primePowerCyclotomic p k (ZMod n))
    rw [AdjoinRoot.lift_root (cyclotomicRoot_power_substitution_relation_of_unit n hp u hu)]
    rw [← pow_mul]
    rw [hprod, pow_add, pow_mul, cyclotomicRoot_pow_index_eq_one n hp]
    simp only [one_pow, one_mul, pow_one]
    rfl

/-- Exponents inverse modulo the prime-power period induce two-sided inverse
quotient homomorphisms, provided both substitutions preserve the defining relation. -/
theorem cyclotomicRootPowerSubstitutionHom_inverse_laws (n : ℕ) {p k : ℕ} (hp : Nat.Prime p)
    (u v t : ℕ) (hu : IsUnit ((cyclotomicRoot n p k ^ u) ^ (p ^ k) - 1))
    (hv : IsUnit ((cyclotomicRoot n p k ^ v) ^ (p ^ k) - 1))
    (hprod : u * v = primePowerIndex p k * t + 1) :
    (cyclotomicRootPowerSubstitutionHom n hp u hu).comp
          (cyclotomicRootPowerSubstitutionHom n hp v hv) =
        RingHom.id (cyclotomicQuotient n p k) ∧
      (cyclotomicRootPowerSubstitutionHom n hp v hv).comp
          (cyclotomicRootPowerSubstitutionHom n hp u hu) =
        RingHom.id (cyclotomicQuotient n p k) := by
  constructor
  · exact cyclotomicRootPowerSubstitutionHom_comp_eq_id n hp u v t hu hv hprod
  · apply cyclotomicRootPowerSubstitutionHom_comp_eq_id n hp v u t hv hu
    calc
      v * u = u * v := Nat.mul_comm v u
      _ = primePowerIndex p k * t + 1 := hprod

/-- A power exponent coprime to a period has a natural-number inverse exponent
whose product is one modulo that period. -/
theorem exists_inverse_exponent_mod_period {u period : ℕ} (hperiod : 1 < period)
    (hcop : Nat.Coprime u period) : ∃ v t, u * v = period * t + 1 := by
  obtain ⟨v, _, hmod⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hperiod
  refine ⟨v, u * v / period, ?_⟩
  calc
    u * v = u * v % period + period * (u * v / period) := (Nat.mod_add_div (u * v) period).symm
    _ = 1 + period * (u * v / period) := by rw [hmod]
    _ = period * (u * v / period) + 1 := Nat.add_comm _ _

/-- The exponent `u` has an inverse modulo the root period `p^(k+1)` whenever
it is coprime to that period. -/
theorem exists_inverse_exponent_mod_primePowerIndex {p k u : ℕ} (hp : Nat.Prime p)
    (hcop : Nat.Coprime u (primePowerIndex p k)) : ∃ v t, u * v = primePowerIndex p k * t + 1 := by
  apply exists_inverse_exponent_mod_period ?_ hcop
  change 1 < p ^ (k + 1)
  exact Nat.one_lt_pow (Nat.succ_ne_zero k) hp.one_lt

/-- An exponent inverse modulo the prime-power root period is coprime to its
underlying prime. -/
private theorem inverse_exponent_coprime_to_prime {p k u v t : ℕ} (hp : Nat.Prime p)
    (hprod : u * v = primePowerIndex p k * t + 1) : Nat.Coprime v p := by
  apply Nat.Coprime.symm
  apply hp.coprime_iff_not_dvd.mpr
  intro hv
  have hdiv : p ∣ u * v := dvd_mul_of_dvd_right hv u
  rw [hprod] at hdiv
  have hpPower : p ∣ primePowerIndex p k := by
    rw [primePowerIndex]
    exact dvd_pow_self p (Nat.succ_ne_zero k)
  have hdivone : p ∣ 1 := by
    have hdiv' : p ∣ t * primePowerIndex p k + 1 := by simpa only [Nat.mul_comm] using hdiv
    exact (Nat.dvd_add_right (dvd_mul_of_dvd_right hpPower t)).mp hdiv'
  have hple : p ≤ 1 := Nat.le_of_dvd (by decide) hdivone
  exact (Nat.not_le_of_lt hp.one_lt) hple

/-- Ring equivalence induced by mutually inverse power substitutions when their
denominators are units and their exponents multiply to one modulo the root period. -/
def cyclotomicRootPowerSubstitutionEquiv (n : ℕ) {p k : ℕ} (hp : Nat.Prime p) (u v t : ℕ)
    (hu : IsUnit ((cyclotomicRoot n p k ^ u) ^ (p ^ k) - 1))
    (hv : IsUnit ((cyclotomicRoot n p k ^ v) ^ (p ^ k) - 1))
    (hprod : u * v = primePowerIndex p k * t + 1) :
    cyclotomicQuotient n p k ≃+* cyclotomicQuotient n p k :=
  RingEquiv.ofRingHom (cyclotomicRootPowerSubstitutionHom n hp u hu)
    (cyclotomicRootPowerSubstitutionHom n hp v hv)
    (cyclotomicRootPowerSubstitutionHom_comp_eq_id n hp u v t hu hv hprod)
    (cyclotomicRootPowerSubstitutionHom_inverse_laws n hp u v t hu hv hprod).2

/-- The power-substitution equivalence sends the canonical root to the selected power.
This identifies its action on the algebra generator, not only on coefficient-array classes.
-/
theorem cyclotomicRootPowerSubstitutionEquiv_map_root (n : ℕ) {p k : ℕ} (hp : Nat.Prime p)
    (u v t : ℕ) (hu : IsUnit ((cyclotomicRoot n p k ^ u) ^ (p ^ k) - 1))
    (hv : IsUnit ((cyclotomicRoot n p k ^ v) ^ (p ^ k) - 1))
    (hprod : u * v = primePowerIndex p k * t + 1) :
    cyclotomicRootPowerSubstitutionEquiv n hp u v t hu hv hprod (cyclotomicRoot n p k) =
      cyclotomicRoot n p k ^ u := by
  change
    cyclotomicRootPowerSubstitutionHom n hp u hu
        (AdjoinRoot.root (primePowerCyclotomic p k (ZMod n))) =
      _
  rw [cyclotomicRootPowerSubstitutionHom,
    AdjoinRoot.lift_root (cyclotomicRoot_power_substitution_relation_of_unit n hp u hu)]

/-- Construct the power-substitution ring equivalence from the arithmetic input
conditions. Coprimality of `p` and `n` makes the base denominator a unit, while
coprimality of `u` with the root period supplies mutually inverse exponents. -/
noncomputable def cyclotomicRootPowerSubstitutionEquiv_of_coprime (n : ℕ) {p k u : ℕ}
    (hp : Nat.Prime p) (hpn : Nat.Coprime p n) (hcop : Nat.Coprime u (primePowerIndex p k)) :
    cyclotomicQuotient n p k ≃+* cyclotomicQuotient n p k := by
  let hinverse := exists_inverse_exponent_mod_primePowerIndex hp hcop
  let v := Classical.choose hinverse
  let t := Classical.choose (Classical.choose_spec hinverse)
  have hprod := Classical.choose_spec (Classical.choose_spec hinverse)
  have hpdiv : p ∣ primePowerIndex p k := by
    rw [primePowerIndex]
    exact dvd_pow_self p (Nat.succ_ne_zero k)
  have hcopu : Nat.Coprime u p := Nat.Coprime.of_dvd_right hpdiv hcop
  have hcopv : Nat.Coprime v p := inverse_exponent_coprime_to_prime hp hprod
  exact
    cyclotomicRootPowerSubstitutionEquiv n hp u v t
      (cyclotomicRoot_power_substitution_denominator_isUnit n hp hpn hcopu)
      (cyclotomicRoot_power_substitution_denominator_isUnit n hp hpn hcopv) hprod

/-- The automatically constructed coprime power equivalence sends the canonical root
to the chosen exponent power. -/
theorem cyclotomicRootPowerSubstitutionEquiv_of_coprime_map_root (n : ℕ) {p k u : ℕ}
    (hp : Nat.Prime p) (hpn : Nat.Coprime p n) (hcop : Nat.Coprime u (primePowerIndex p k)) :
    cyclotomicRootPowerSubstitutionEquiv_of_coprime n hp hpn hcop (cyclotomicRoot n p k) =
      cyclotomicRoot n p k ^ u := by
  have hpdiv : p ∣ primePowerIndex p k := by
    rw [primePowerIndex]
    exact dvd_pow_self p (Nat.succ_ne_zero k)
  change
    cyclotomicRootPowerSubstitutionHom n hp u
        (cyclotomicRoot_power_substitution_denominator_isUnit n hp hpn
          (Nat.Coprime.of_dvd_right hpdiv hcop))
        (AdjoinRoot.root (primePowerCyclotomic p k (ZMod n))) =
      _
  rw [cyclotomicRootPowerSubstitutionHom,
    AdjoinRoot.lift_root
      (cyclotomicRoot_power_substitution_relation_of_unit n hp u
        (cyclotomicRoot_power_substitution_denominator_isUnit n hp hpn
          (Nat.Coprime.of_dvd_right hpdiv hcop)))]

/-- The ring equivalence acts on fixed-array representatives by the executable
coefficient-level power substitution. -/
theorem cyclotomicRootPowerSubstitutionEquiv_class (n : ℕ) {p k : ℕ} (hp : Nat.Prime p) (u v t : ℕ)
    (hu : IsUnit ((cyclotomicRoot n p k ^ u) ^ (p ^ k) - 1))
    (hv : IsUnit ((cyclotomicRoot n p k ^ v) ^ (p ^ k) - 1))
    (hprod : u * v = primePowerIndex p k * t + 1) (a : cyclotomicFixedArray n p k) :
    cyclotomicRootPowerSubstitutionEquiv n hp u v t hu hv hprod
        (cyclotomicFixedArrayClass n p k a) =
      cyclotomicFixedArrayClass n p k (cyclotomicFixedArraySubstitutePower n hp a u) := by
  exact cyclotomicRootPowerSubstitutionHom_class n hp u hu a

/-- The automatically constructed coprime-exponent equivalence acts on coefficient
arrays by the period-reduced power substitution. -/
theorem cyclotomicRootPowerSubstitutionEquiv_of_coprime_class (n : ℕ) {p k u : ℕ} (hp : Nat.Prime p)
    (hpn : Nat.Coprime p n) (hcop : Nat.Coprime u (primePowerIndex p k))
    (a : cyclotomicFixedArray n p k) :
    cyclotomicRootPowerSubstitutionEquiv_of_coprime n hp hpn hcop
        (cyclotomicFixedArrayClass n p k a) =
      cyclotomicFixedArrayClass n p k (cyclotomicFixedArraySubstitutePower n hp a u) := by
  let hinverse := exists_inverse_exponent_mod_primePowerIndex hp hcop
  let v := Classical.choose hinverse
  let t := Classical.choose (Classical.choose_spec hinverse)
  have hprod := Classical.choose_spec (Classical.choose_spec hinverse)
  have hpdiv : p ∣ primePowerIndex p k := by
    rw [primePowerIndex]
    exact dvd_pow_self p (Nat.succ_ne_zero k)
  have hcopu : Nat.Coprime u p := Nat.Coprime.of_dvd_right hpdiv hcop
  have hcopv : Nat.Coprime v p := inverse_exponent_coprime_to_prime hp hprod
  change
    cyclotomicRootPowerSubstitutionEquiv n hp u v t
        (cyclotomicRoot_power_substitution_denominator_isUnit n hp hpn hcopu)
        (cyclotomicRoot_power_substitution_denominator_isUnit n hp hpn hcopv) hprod
        (cyclotomicFixedArrayClass n p k a) =
      _
  exact
    cyclotomicRootPowerSubstitutionEquiv_class n hp u v t
      (cyclotomicRoot_power_substitution_denominator_isUnit n hp hpn hcopu)
      (cyclotomicRoot_power_substitution_denominator_isUnit n hp hpn hcopv) hprod a

/-- A unit modulo the full APR-CL modulus induces the cyclotomic power
equivalence for every auxiliary prime block. -/
theorem cyclotomicRootPowerSubstitutionEquiv_class_of_modulus_coprime (n t q k u : ℕ) (ht : t ≠ 0)
    (hq : q ∈ auxiliaryPrimes t) (hn : Nat.Coprime n (modulus t)) (hu : Nat.Coprime u (modulus t))
    (a : cyclotomicFixedArray n q k) :
    cyclotomicRootPowerSubstitutionEquiv_of_coprime n
        ((mem_auxiliaryPrimes_iff_prime_sub_dvd ht).mp hq |>.1)
        (auxiliaryPrime_coprime_left_of_modulus hq hn)
        (by
          have hqu : Nat.Coprime u q := Nat.Coprime.of_dvd_right (auxiliaryPrime_dvd_modulus hq) hu
          rw [primePowerIndex]
          exact hqu.pow_right (k + 1))
        (cyclotomicFixedArrayClass n q k a) =
      cyclotomicFixedArrayClass n q k
        (cyclotomicFixedArraySubstitutePower n
          ((mem_auxiliaryPrimes_iff_prime_sub_dvd ht).mp hq |>.1) a u) := by
  have hqprime : Nat.Prime q := (mem_auxiliaryPrimes_iff_prime_sub_dvd ht).mp hq |>.1
  have hqn : Nat.Coprime q n := auxiliaryPrime_coprime_left_of_modulus hq hn
  have hqu : Nat.Coprime u q := Nat.Coprime.of_dvd_right (auxiliaryPrime_dvd_modulus hq) hu
  have hperiod : Nat.Coprime u (primePowerIndex q k) := by
    rw [primePowerIndex]
    exact hqu.pow_right (k + 1)
  exact cyclotomicRootPowerSubstitutionEquiv_of_coprime_class n hqprime hqn hperiod a

/-- The input residue acts by a cyclotomic power equivalence on every auxiliary-prime block.
The full-modulus coprimality hypothesis supplies both the quotient characteristic condition and
the invertibility of the input exponent modulo each prime-power period.
-/
theorem cyclotomicRootPowerSubstitutionEquiv_class_of_input_unit (n t q k : ℕ) (ht : t ≠ 0)
    (hq : q ∈ auxiliaryPrimes t) (hn : Nat.Coprime n (modulus t)) (a : cyclotomicFixedArray n q k) :
    cyclotomicRootPowerSubstitutionEquiv_of_coprime n
        ((mem_auxiliaryPrimes_iff_prime_sub_dvd ht).mp hq |>.1)
        (auxiliaryPrime_coprime_left_of_modulus hq hn)
        (by
          have hqn : Nat.Coprime q n := auxiliaryPrime_coprime_left_of_modulus hq hn
          rw [primePowerIndex]
          exact hqn.symm.pow_right (k + 1))
        (cyclotomicFixedArrayClass n q k a) =
      cyclotomicFixedArrayClass n q k
        (cyclotomicFixedArraySubstitutePower n
          ((mem_auxiliaryPrimes_iff_prime_sub_dvd ht).mp hq |>.1) a n) := by
  exact cyclotomicRootPowerSubstitutionEquiv_class_of_modulus_coprime n t q k n ht hq hn hn a

/-- Every prime-factor coefficient ring of an input unit modulo the APR-CL modulus
inherits the input-power equivalence on each auxiliary-prime cyclotomic block.
This exposes the algebraic action needed when proving a prime-factor orbit condition.
-/
theorem cyclotomicRootPowerSubstitutionEquiv_class_of_prime_factor (n ℓ t q k : ℕ) (ht : t ≠ 0)
    (hq : q ∈ auxiliaryPrimes t) (hℓn : ℓ ∣ n) (hn : Nat.Coprime n (modulus t))
    (a : cyclotomicFixedArray ℓ q k) :
    cyclotomicRootPowerSubstitutionEquiv_of_coprime ℓ
        ((mem_auxiliaryPrimes_iff_prime_sub_dvd ht).mp hq |>.1)
        (auxiliaryPrime_coprime_left_of_modulus hq (Nat.Coprime.of_dvd_left hℓn hn))
        (by
          have hnq : Nat.Coprime q n := auxiliaryPrime_coprime_left_of_modulus hq hn
          rw [primePowerIndex]
          exact hnq.symm.pow_right (k + 1))
        (cyclotomicFixedArrayClass ℓ q k a) =
      cyclotomicFixedArrayClass ℓ q k
        (cyclotomicFixedArraySubstitutePower ℓ
          ((mem_auxiliaryPrimes_iff_prime_sub_dvd ht).mp hq |>.1) a n) := by
  have hℓM : Nat.Coprime ℓ (modulus t) := Nat.Coprime.of_dvd_left hℓn hn
  exact cyclotomicRootPowerSubstitutionEquiv_class_of_modulus_coprime ℓ t q k n ht hq hℓM hn a

/-- On the coefficient ring of a prime divisor of the input, the induced APR-CL
equivalence sends the canonical cyclotomic root to its `n`-th power.
-/
theorem cyclotomicRootPowerSubstitutionEquiv_map_root_of_prime_factor (n ℓ t q k : ℕ) (ht : t ≠ 0)
    (hq : q ∈ auxiliaryPrimes t) (hℓn : ℓ ∣ n) (hn : Nat.Coprime n (modulus t)) :
    cyclotomicRootPowerSubstitutionEquiv_of_coprime ℓ
        ((mem_auxiliaryPrimes_iff_prime_sub_dvd ht).mp hq |>.1)
        (auxiliaryPrime_coprime_left_of_modulus hq (Nat.Coprime.of_dvd_left hℓn hn))
        (by
          have hnq : Nat.Coprime q n := auxiliaryPrime_coprime_left_of_modulus hq hn
          rw [primePowerIndex]
          exact hnq.symm.pow_right (k + 1))
        (cyclotomicRoot ℓ q k) =
      cyclotomicRoot ℓ q k ^ n := by
  have hℓM : Nat.Coprime ℓ (modulus t) := Nat.Coprime.of_dvd_left hℓn hn
  have hqℓ : Nat.Coprime q ℓ := auxiliaryPrime_coprime_left_of_modulus hq hℓM
  have hnq : Nat.Coprime q n := auxiliaryPrime_coprime_left_of_modulus hq hn
  have hperiod : Nat.Coprime n (primePowerIndex q k) := by
    rw [primePowerIndex]
    exact hnq.symm.pow_right (k + 1)
  exact
    cyclotomicRootPowerSubstitutionEquiv_of_coprime_map_root ℓ
      ((mem_auxiliaryPrimes_iff_prime_sub_dvd ht).mp hq |>.1) hqℓ hperiod

/-- The fixed-array root returns to the array unit after its prime-power period.
This connects the abstract quotient-root period to the executable coefficient-array power API.
-/
theorem cyclotomicFixedArrayRoot_pow_index_eq_one (n : ℕ) (hn : 1 < n) {p k : ℕ}
    (hp : Nat.Prime p) :
    cyclotomicFixedArrayPowByMul n hp (cyclotomicFixedArrayRoot n hp) (primePowerIndex p k) =
      cyclotomicFixedArrayOne n p k := by
  apply (cyclotomicFixedArrayClass_injective n hn hp)
  rw [cyclotomicFixedArrayPowByMul_class n hp (cyclotomicFixedArrayRoot n hp) (primePowerIndex p k)]
  rw [cyclotomicFixedArrayRoot_class n hp]
  rw [cyclotomicRoot_pow_index_eq_one n hp]
  rw [cyclotomicFixedArrayOne_class n hp]

/-- The optimized squaring implementation has the same certified prime-power root period. -/
theorem cyclotomicFixedArrayRoot_pow_index_eq_one_squaring (n : ℕ) (hn : 1 < n) {p k : ℕ}
    (hp : Nat.Prime p) :
    cyclotomicFixedArrayPowBySquaring n hp (cyclotomicFixedArrayRoot n hp) (primePowerIndex p k) =
      cyclotomicFixedArrayOne n p k := by
  rw [cyclotomicFixedArrayPowBySquaring_eq_powByMul n hn hp]
  exact cyclotomicFixedArrayRoot_pow_index_eq_one n hn hp

/-- Search the complete exponent interval for a power of the canonical root equal to `S`. -/
def rootExponent (n p k : ℕ) (S : cyclotomicQuotient n p k) : Option ℕ :=
  (List.range (primePowerIndex p k)).find? (fun h => decide (cyclotomicRoot n p k ^ h = S))

private theorem list_find?_congr {α : Type*} (l : List α) (p q : α → Bool)
    (h : ∀ x ∈ l, p x = q x) : List.find? p l = List.find? q l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [List.find?_cons, List.find?_cons]
    rw [h x (List.mem_cons_self)]
    split
    · rfl
    · apply ih
      intro y hy
      exact h y (List.mem_cons_of_mem x hy)

/-- The executable fixed-array search agrees with the quotient-reference search. -/
theorem cyclotomicFixedArrayRootExponent_eq_rootExponent (n : ℕ) (hn : 1 < n) {p k : ℕ}
    (hp : Nat.Prime p) (a : cyclotomicFixedArray n p k) :
    cyclotomicFixedArrayRootExponent n hp a =
      rootExponent n p k (cyclotomicFixedArrayClass n p k a) := by
  unfold cyclotomicFixedArrayRootExponent rootExponent
  apply list_find?_congr
  intro e _he
  exact
    Bool.decide_congr
      (funext_iff.symm.trans (cyclotomicFixedArrayMonomialReduce_eq_iff n hn hp a e))

/-- A successful root-exponent search returns the least matching exponent in the full range. -/
theorem rootExponent_eq_some_iff (n p k : ℕ) (S : cyclotomicQuotient n p k) (h : ℕ) :
    rootExponent n p k S = some h ↔
      h < primePowerIndex p k ∧
        cyclotomicRoot n p k ^ h = S ∧ ∀ j, j < h → cyclotomicRoot n p k ^ j ≠ S := by
  rw [rootExponent, List.find?_range_eq_some]
  constructor
  · rintro ⟨heq, hlt, hprior⟩
    refine ⟨List.mem_range.mp hlt, of_decide_eq_true heq, ?_⟩
    intro j hj
    have hfalse : decide (cyclotomicRoot n p k ^ j = S) = false :=
      Eq.mp (Bool.not_eq_true_eq_eq_false _) (hprior j hj)
    exact decide_eq_false_iff_not.mp hfalse
  · rintro ⟨hlt, heq, hprior⟩
    refine ⟨decide_eq_true_eq.mpr heq, List.mem_range.mpr hlt, ?_⟩
    intro j hj
    have hfalse : decide (cyclotomicRoot n p k ^ j = S) = false :=
      decide_eq_false_iff_not.mpr (hprior j hj)
    exact Eq.mpr (Bool.not_eq_true_eq_eq_false _) hfalse

/-- A failed root-exponent search means that none of the specified powers matches `S`. -/
theorem rootExponent_eq_none_iff (n p k : ℕ) (S : cyclotomicQuotient n p k) :
    rootExponent n p k S = none ↔ ∀ h, h < primePowerIndex p k → cyclotomicRoot n p k ^ h ≠ S := by
  simp only [rootExponent, List.find?_range_eq_none, Bool.not_eq_true_eq_eq_false,
    decide_eq_false_iff_not]

/-- A successful fixed-array root search returns the least exponent whose reduced
monomial is the requested coefficient array. This exposes the executable search contract. -/
theorem cyclotomicFixedArrayRootExponent_eq_some_iff (n : ℕ) (hn : 1 < n) {p k : ℕ}
    (hp : Nat.Prime p) (a : cyclotomicFixedArray n p k) (h : ℕ) :
    cyclotomicFixedArrayRootExponent n hp a = some h ↔
      h < primePowerIndex p k ∧
        cyclotomicFixedArrayMonomialReduce n hp h = a ∧
        ∀ j, j < h → cyclotomicFixedArrayMonomialReduce n hp j ≠ a := by
  rw [cyclotomicFixedArrayRootExponent_eq_rootExponent n hn hp a]
  rw [rootExponent_eq_some_iff]
  constructor
  · rintro ⟨hlt, hpow, hprior⟩
    refine ⟨hlt, (cyclotomicFixedArrayMonomialReduce_eq_iff n hn hp a h).mpr hpow, ?_⟩
    intro j hj harray
    apply hprior j hj
    exact (cyclotomicFixedArrayMonomialReduce_eq_iff n hn hp a j).mp harray
  · rintro ⟨hlt, harray, hprior⟩
    refine ⟨hlt, (cyclotomicFixedArrayMonomialReduce_eq_iff n hn hp a h).mp harray, ?_⟩
    intro j hj hroot
    apply hprior j hj
    exact (cyclotomicFixedArrayMonomialReduce_eq_iff n hn hp a j).mpr hroot

/-- A failed fixed-array root search means no reduced monomial in its finite range
equals the requested coefficient array. This makes the `none` branch explicit. -/
theorem cyclotomicFixedArrayRootExponent_eq_none_iff (n : ℕ) (hn : 1 < n) {p k : ℕ}
    (hp : Nat.Prime p) (a : cyclotomicFixedArray n p k) :
    cyclotomicFixedArrayRootExponent n hp a = none ↔
      ∀ e, e < primePowerIndex p k → cyclotomicFixedArrayMonomialReduce n hp e ≠ a := by
  rw [cyclotomicFixedArrayRootExponent_eq_rootExponent n hn hp a]
  rw [rootExponent_eq_none_iff]
  constructor
  · intro h e heq harray
    apply h e heq
    exact (cyclotomicFixedArrayMonomialReduce_eq_iff n hn hp a e).mp harray
  · intro h e heq hroot
    apply h e heq
    exact (cyclotomicFixedArrayMonomialReduce_eq_iff n hn hp a e).mpr hroot

end

end PseudoPrime.PrimeTest.APRCL
