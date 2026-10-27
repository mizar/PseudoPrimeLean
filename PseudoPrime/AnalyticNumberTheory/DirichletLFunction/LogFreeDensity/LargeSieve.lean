/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.SquarefreeReciprocalSums
public import PseudoPrime.Analysis.FiniteGramBounds
public import PseudoPrime.Analysis.FiniteSeparatedSetBounds
public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.NumberTheory.DirichletCharacter.Bounds
public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.ZeroCounting

/-! # Character orthogonality for finite bilinear sums -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity

/--
Inputs: a positive modulus `r` and an integer frequency `n`.

Definition: the Ramanujan sum `c_r(n)`, written as the sum of the standard additive character
over the units modulo `r`.

Output: a complex number encoding the additive frequencies coprime to `r`.

Role: supplies the finite additive-character factor in Selberg's weighted large-sieve identity.
-/
noncomputable def ramanujanSum (r n : ℕ) [NeZero r] : ℂ :=
  ∑ u : (ZMod r)ˣ, ZMod.stdAddChar ((n : ZMod r) * (u : ZMod r))

/--
Inputs: a positive modulus `r`, a frequency `n`, and a natural multiple `k`.

Claim: adding a multiple of `r` to a frequency leaves the Ramanujan sum unchanged.

Proof: the frequency is reduced modulo `r` inside each standard additive character.

Role: makes the periodicity of the finite additive-frequency weight explicit.
-/
theorem ramanujanSum_add_modulus_multiple (r n k : ℕ) [NeZero r] :
    ramanujanSum r (n + k * r) = ramanujanSum r n := by
  classical
  unfold ramanujanSum
  apply Finset.sum_congr rfl
  intro u hu
  simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, add_zero]

/--
Inputs: a positive modulus `r`.

Claim: the zero-frequency Ramanujan sum is the totient of the modulus.

Proof: every unit contributes the additive-character value at zero, and the number of units
modulo `r` is `Nat.totient r`.

Role: fixes the normalization of `ramanujanSum` used in the finite character decomposition.
-/
theorem ramanujanSum_zero (r : ℕ) [NeZero r] : ramanujanSum r 0 = (Nat.totient r : ℂ) := by
  classical
  simp only [ramanujanSum, Nat.cast_zero, zero_mul, AddChar.map_zero_eq_one, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  rw [← ZMod.card_units_eq_totient]
  ring

/--
Inputs: a positive modulus `r` and a frequency `n`.

Claim: the norm of the Ramanujan sum is at most `Nat.totient r`.

Proof: apply the triangle inequality and use that each standard additive-character value has norm
one; the number of terms is `Nat.totient r`.

Role: controls the size of the Ramanujan weight in Selberg's finite character transform.
-/
theorem norm_ramanujanSum_le_totient (r n : ℕ) [NeZero r] :
    ‖ramanujanSum r n‖ ≤ (Nat.totient r : ℝ) := by
  classical
    calc
    ‖ramanujanSum r n‖ ≤ ∑ u : (ZMod r)ˣ, ‖ZMod.stdAddChar ((n : ZMod r) * (u : ZMod r))‖ :=
      norm_sum_le _ _
    _ = ∑ _u : (ZMod r)ˣ, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [ZMod.stdAddChar_apply, Circle.norm_coe]
    _ = (Nat.totient r : ℝ) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      rw [← ZMod.card_units_eq_totient]

/--
Inputs: a positive modulus `r`, frequencies `n,m`, and a proof that `m` is a unit modulo `r`.

Claim: multiplying a frequency by a unit modulo `r` leaves its Ramanujan sum unchanged.

Proof: reindex the finite sum over units by left multiplication by the unit represented by `m`.

Role: absorbs unit factors that arise in the Chinese-remainder decomposition of additive characters.
-/
theorem ramanujanSum_mul_unit (r n m : ℕ) [NeZero r] (hm : IsUnit (m : ZMod r)) :
    ramanujanSum r (n * m) = ramanujanSum r n := by
  classical
  unfold ramanujanSum
  rw [Nat.cast_mul]
  calc
    (∑ u : (ZMod r)ˣ, ZMod.stdAddChar ((n : ZMod r) * (m : ZMod r) * (u : ZMod r))) =
        ∑ u : (ZMod r)ˣ, ZMod.stdAddChar ((n : ZMod r) * ((hm.unit * u : (ZMod r)ˣ) : ZMod r)) :=
      by
      apply Finset.sum_congr rfl
      intro u hu
      congr 1
      simp only [Units.val_mul, IsUnit.unit_spec]
      ring
    _ = ∑ u : (ZMod r)ˣ, ZMod.stdAddChar ((n : ZMod r) * (u : ZMod r)) := by
      exact
        Fintype.sum_equiv (Equiv.mulLeft hm.unit) _ _
          (fun u => by simp only [Equiv.coe_mulLeft, Units.val_mul])

/--
Inputs: a positive modulus `r`, a frequency `n`, and a proof that `n` is coprime to `r`.

Claim: the Ramanujan sum at `n` equals its value at frequency one.

Proof: coprimality makes `n` a unit modulo `r`, so apply `ramanujanSum_mul_unit`.

Role: makes the Ramanujan coefficient constant on integers sifted away from the prime factors of
its modulus.
-/
theorem ramanujanSum_eq_one_of_coprime {r n : ℕ} [NeZero r] (h : Nat.Coprime n r) :
    ramanujanSum r n = ramanujanSum r 1 := by
  have hm : IsUnit (n : ZMod r) := (ZMod.isUnit_iff_coprime n r).2 h
  calc
    ramanujanSum r n = ramanujanSum r (1 * n) := by simp only [one_mul]
    _ = ramanujanSum r 1 := ramanujanSum_mul_unit r 1 n hm

/--
Inputs: a prime modulus `p` and the standard additive character modulo `p`.

Claim: the Ramanujan sum at frequency one is `-1`.

Proof: the standard additive character sums to zero over `ZMod p`; removing its zero term leaves
the sum over nonzero residues, which is the sum over units.

Role: supplies the prime factor in the squarefree Ramanujan norm calculation.
-/
theorem ramanujanSum_prime_one {p : ℕ} [NeZero p] [Fact p.Prime] : ramanujanSum p 1 = -1 := by
  classical
  have hchar : ZMod.stdAddChar ≠ (1 : AddChar (ZMod p) ℂ) := by
    intro h
    have hval := congrArg (fun ψ : AddChar (ZMod p) ℂ => ψ (1 : ZMod p)) h
    have hone : ZMod.stdAddChar (1 : ZMod p) = 1 := by simpa only [AddChar.one_apply] using hval
    have hzero : ZMod.stdAddChar (0 : ZMod p) = ZMod.stdAddChar (1 : ZMod p) := by
      simp only [AddChar.map_zero_eq_one, hone]
    have h01 := ZMod.injective_stdAddChar hzero
    exact one_ne_zero h01.symm
  have htotal : (∑ x : ZMod p, ZMod.stdAddChar x) = 0 := AddChar.sum_eq_zero_of_ne_one hchar
  have hnonzero :
    (∑ x : { x : ZMod p // x ≠ 0 }, ZMod.stdAddChar x.1) =
      ∑ x ∈ Finset.univ.erase (0 : ZMod p), ZMod.stdAddChar x := by
    symm
    exact
      Finset.sum_subtype (Finset.univ.erase (0 : ZMod p))
        (by
          intro x; simp only [Finset.mem_erase, Finset.mem_univ, and_true])
        (fun x : ZMod p => ZMod.stdAddChar x)
  have hzero : (0 : ZMod p) ∈ Finset.univ := Finset.mem_univ _
  have hsumErase := Finset.sum_erase_add (Finset.univ : Finset (ZMod p)) ZMod.stdAddChar hzero
  have hunitSum : (∑ u : (ZMod p)ˣ, ZMod.stdAddChar (u : ZMod p)) = -1 := by
    calc
      _ = ∑ x : { x : ZMod p // x ≠ 0 }, ZMod.stdAddChar x.1 :=
        Fintype.sum_equiv unitsEquivNeZero (fun u : (ZMod p)ˣ => ZMod.stdAddChar (u : ZMod p))
          (fun x : { x : ZMod p // x ≠ 0 } => ZMod.stdAddChar x.1) (fun _ => rfl)
      _ = ∑ x ∈ Finset.univ.erase (0 : ZMod p), ZMod.stdAddChar x := hnonzero
      _ = -ZMod.stdAddChar 0 := by
        rw [htotal] at hsumErase
        exact add_eq_zero_iff_eq_neg.mp hsumErase
      _ = -1 := by simp only [AddChar.map_zero_eq_one]
  simpa only [ramanujanSum, Nat.cast_one, one_mul] using hunitSum

/--
Inputs: coprime positive moduli `q` and `r`, and a complex-valued function on units modulo `q*r`.

Claim: its sum over units modulo `q*r` equals the iterated sum over pairs of units modulo `q` and
`r`, transported through the Chinese-remainder equivalence.

Proof: map units through `ZMod.chineseRemainder`, use `MulEquiv.prodUnits`, and reindex the finite
sums by the resulting equivalence.

Role: provides the finite-domain decomposition needed to factor the character-weighted additive
sum in Selberg's Theorem 7A.
-/
theorem sum_units_zmod_mul_coprime {q r : ℕ} [NeZero q] [NeZero r] (h : Nat.Coprime q r)
    (f : (ZMod (q * r))ˣ → ℂ) :
    (∑ u : (ZMod (q * r))ˣ, f u) =
      ∑ a : (ZMod q)ˣ,
        ∑ b : (ZMod r)ˣ,
          f
            (((Units.mapEquiv (ZMod.chineseRemainder h).toMulEquiv).trans MulEquiv.prodUnits).symm
              (a, b)) := by
  classical
  let e : (ZMod (q * r))ˣ ≃* (ZMod q)ˣ × (ZMod r)ˣ :=
    (Units.mapEquiv (ZMod.chineseRemainder h).toMulEquiv).trans MulEquiv.prodUnits
  calc
    (∑ u : (ZMod (q * r))ˣ, f u) = ∑ p : (ZMod q)ˣ × (ZMod r)ˣ, f (e.symm p) := by
      symm
      exact Fintype.sum_equiv e.symm _ _ (fun p => rfl)
    _ = ∑ a : (ZMod q)ˣ, ∑ b : (ZMod r)ˣ, f (e.symm (a, b)) := by simp only [Fintype.sum_prod_type]

/--
Inputs: coprime positive moduli `q,r` and residues `a,b` modulo those moduli.

Claim: the inverse Chinese-remainder image of `(a,b)` is represented modulo `q*r` by the usual
integer CRT expression, using the inverses of `r` modulo `q` and `q` modulo `r`.

Proof: apply the Chinese-remainder equivalence and check the two components with the unit inverse
identities.

Role: gives an explicit representative for splitting standard additive characters after CRT
reindexing.
-/
theorem chineseRemainder_symm_apply_nat {q r : ℕ} [NeZero q] [NeZero r] (h : Nat.Coprime q r)
    (a : ZMod q) (b : ZMod r) :
    (ZMod.chineseRemainder h).symm (a, b) =
      ((r * (((ZMod.isUnit_iff_coprime r q).2 h.symm).unit⁻¹ * a).val +
            q * (((ZMod.isUnit_iff_coprime q r).2 h).unit⁻¹ * b).val :
          ℕ) :
        ZMod (q * r)) := by
  let e : ZMod (q * r) ≃+* ZMod q × ZMod r := ZMod.chineseRemainder h
  apply e.injective
  rw [RingEquiv.apply_symm_apply]
  symm
  apply Prod.ext
  · change
      ((ZMod.castHom
              (show q.lcm r ∣ q * r by
                exact Nat.lcm_dvd_iff.mpr ⟨dvd_mul_right q r, dvd_mul_left r q⟩)
              (ZMod q × ZMod r))
            _).1 =
        a
    rw [ZMod.castHom_apply, Prod.fst_zmod_cast, ZMod.cast_natCast (dvd_mul_right q r)]
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, ZMod.natCast_self, zero_mul, add_zero]
    rw [ZMod.natCast_zmod_val]
    have hu : (r : ZMod q) * (↑(((ZMod.isUnit_iff_coprime r q).2 h.symm).unit⁻¹) : ZMod q) = 1 := by
      calc
        (r : ZMod q) * (↑(((ZMod.isUnit_iff_coprime r q).2 h.symm).unit⁻¹) : ZMod q) =
            ↑((ZMod.isUnit_iff_coprime r q).2 h.symm).unit *
              ↑(((ZMod.isUnit_iff_coprime r q).2 h.symm).unit⁻¹) :=
          by rw [(ZMod.isUnit_iff_coprime r q).2 h.symm |>.unit_spec]
        _ = 1 := Units.val_inv _
    calc
      (r : ZMod q) *
            (((((ZMod.isUnit_iff_coprime r q).2 h.symm).unit⁻¹ : (ZMod q)ˣ) : ZMod q) * a) =
          ((r : ZMod q) *
              ((((ZMod.isUnit_iff_coprime r q).2 h.symm).unit⁻¹ : (ZMod q)ˣ) : ZMod q)) *
            a :=
        by ring
      _ = a := by rw [hu, one_mul]
  · change
      ((ZMod.castHom
              (show q.lcm r ∣ q * r by
                exact Nat.lcm_dvd_iff.mpr ⟨dvd_mul_right q r, dvd_mul_left r q⟩)
              (ZMod q × ZMod r))
            _).2 =
        b
    rw [ZMod.castHom_apply, Prod.snd_zmod_cast, ZMod.cast_natCast (dvd_mul_left r q)]
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, ZMod.natCast_self, zero_mul, zero_add]
    rw [ZMod.natCast_zmod_val]
    have hu : (q : ZMod r) * (↑(((ZMod.isUnit_iff_coprime q r).2 h).unit⁻¹) : ZMod r) = 1 := by
      calc
        (q : ZMod r) * (↑(((ZMod.isUnit_iff_coprime q r).2 h).unit⁻¹) : ZMod r) =
            ↑((ZMod.isUnit_iff_coprime q r).2 h).unit *
              ↑(((ZMod.isUnit_iff_coprime q r).2 h).unit⁻¹) :=
          by rw [(ZMod.isUnit_iff_coprime q r).2 h |>.unit_spec]
        _ = 1 := Units.val_inv _
    calc
      (q : ZMod r) * (((((ZMod.isUnit_iff_coprime q r).2 h).unit⁻¹ : (ZMod r)ˣ) : ZMod r) * b) =
          ((q : ZMod r) * ((((ZMod.isUnit_iff_coprime q r).2 h).unit⁻¹ : (ZMod r)ˣ) : ZMod r)) *
            b :=
        by ring
      _ = b := by rw [hu, one_mul]

/--
Inputs: a nonempty residue modulus, a finite set of unit residues, and two complex functions.

Claim: summing the product of their finite character transforms over all Dirichlet characters
equals the totient of the modulus times their pointwise inner product on the residue set.

Proof: expand both finite sums, exchange their order with the character sum, and apply character
orthogonality to the two unit residues.

Role: provides the exact finite-modulus orthogonality identity used in mean-square arguments.
-/
theorem dirichletCharacter_bilinear_orthogonality {q : ℕ} [NeZero q] (S : Finset (ZMod q))
    (hS : ∀ a ∈ S, IsUnit a) (f g : ZMod q → ℂ) :
    (∑ χ : DirichletCharacter ℂ q, (∑ a ∈ S, f a * χ a⁻¹) * (∑ b ∈ S, g b * χ b)) =
      (Nat.totient q : ℂ) * ∑ a ∈ S, f a * g a := by
  classical
    calc
    _ = ∑ χ : DirichletCharacter ℂ q, ∑ a ∈ S, ∑ b ∈ S, f a * g b * (χ a⁻¹ * χ b) := by
      apply Finset.sum_congr rfl
      intro χ hχ
      rw [Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      ring
    _ = ∑ a ∈ S, ∑ b ∈ S, f a * g b * ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * χ b := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b hb
      rw [← Finset.mul_sum]
    _ = (Nat.totient q : ℂ) * ∑ a ∈ S, f a * g a := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      calc
        _ = ∑ b ∈ S, if a = b then f a * g b * (Nat.totient q : ℂ) else 0 := by
          apply Finset.sum_congr rfl
          intro b hb
          rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ (hS a ha) b]
          by_cases hab : a = b
          · simp only [ite_eq_left hab]
          · simp only [ite_eq_right hab, mul_zero]
        _ = (Nat.totient q : ℂ) * (f a * g a) := by
          rw [Finset.sum_ite_eq, ite_eq_left ha]
          ring

/--
Inputs: a Dirichlet character and a unit residue modulo its modulus.

Claim: the character value at the inverse residue is the complex conjugate of its value at the
residue.

Proof: a character has norm one on units, and multiplicativity identifies its inverse value with
the multiplicative inverse.

Role: converts the bilinear character orthogonality identity into a sum of squared norms.
-/
theorem dirichletCharacter_inv_eq_star {q : ℕ} (χ : DirichletCharacter ℂ q) {a : ZMod q}
    (ha : IsUnit a) : χ (a⁻¹) = star (χ a) := by
  have hnorm : ‖χ a‖ = 1 := by
    rw [← ha.unit_spec]
    exact DirichletCharacter.unit_norm_eq_one χ ha.unit
  have hnonzero : χ a ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hnorm
    exact one_ne_zero hnorm.symm
  have hcancel : a * a⁻¹ = 1 := by
    rw [mul_comm]
    exact (ZMod.inv_mul_eq_one_of_isUnit ha a).2 rfl
  have hmul : χ a * χ (a⁻¹) = 1 := by
    calc
      χ a * χ (a⁻¹) = χ (a * a⁻¹) := (map_mul χ a _).symm
      _ = χ 1 := congrArg χ hcancel
      _ = 1 := map_one χ
  have hstar : χ a * star (χ a) = 1 := by
    calc
      χ a * star (χ a) = (Complex.normSq (χ a) : ℂ) := Complex.mul_conj _
      _ = 1 := by
        rw [Complex.normSq_eq_norm_sq, hnorm]
        exact congrArg (fun x : ℝ => (x : ℂ)) (show (1 : ℝ) ^ 2 = 1 by norm_num only)
  exact mul_left_cancel₀ hnonzero (hmul.trans hstar.symm)

/--
Inputs: a finite set of unit residues and a complex-valued function on the residue ring.

Claim: the sum over Dirichlet characters of the squared transform norm equals the totient times
the sum of the pointwise squared norms.

Proof: rewrite one transform as the conjugate transform using `dirichletCharacter_inv_eq_star`,
then apply finite bilinear character orthogonality.

Role: supplies exact fixed-modulus Parseval orthogonality for later large-sieve estimates.
-/
theorem dirichletCharacter_parseval {q : ℕ} [NeZero q] (S : Finset (ZMod q))
    (hS : ∀ a ∈ S, IsUnit a) (f : ZMod q → ℂ) :
    (∑ χ : DirichletCharacter ℂ q, star (∑ a ∈ S, f a * χ a) * (∑ a ∈ S, f a * χ a)) =
      (Nat.totient q : ℂ) * ∑ a ∈ S, star (f a) * f a := by
  classical
  have hbil := dirichletCharacter_bilinear_orthogonality S hS (fun a => star (f a)) f
  have hfirst (χ : DirichletCharacter ℂ q) :
    (∑ a ∈ S, star (f a) * χ (a⁻¹)) = star (∑ a ∈ S, f a * χ a) := by
    calc
      _ = ∑ a ∈ S, star (f a * χ a) := by
        apply Finset.sum_congr rfl
        intro a ha
        calc
          star (f a) * χ (a⁻¹) = star (f a) * star (χ a) :=
            congrArg (fun z : ℂ => star (f a) * z) (dirichletCharacter_inv_eq_star χ (hS a ha))
          _ = star (f a * χ a) := by rw [star_mul, mul_comm]
      _ = star (∑ a ∈ S, f a * χ a) := (map_sum (starRingEnd ℂ) (fun a => f a * χ a) S).symm
  calc
    _ = ∑ χ : DirichletCharacter ℂ q, (∑ a ∈ S, star (f a) * χ (a⁻¹)) * (∑ a ∈ S, f a * χ a) := by
      apply Finset.sum_congr rfl
      intro χ hχ
      rw [hfirst]
    _ = (Nat.totient q : ℂ) * ∑ a ∈ S, star (f a) * f a := hbil

/--
Inputs: a complex-valued function on `ZMod q`, for a positive modulus `q`.

Claim: the sum of squared norms of its discrete Fourier transform equals `q` times the sum of
squared norms of the original function.

Proof: expand both transforms, exchange the finite sums, and use orthogonality of the standard
additive character of `ZMod q`.

Role: provides the additive Plancherel identity used to transfer primitive Dirichlet character
means to additive Fourier means.
-/
theorem zmod_dft_parseval {q : ℕ} [NeZero q] (f : ZMod q → ℂ) :
    (∑ k : ZMod q, Complex.normSq (ZMod.dft f k)) = q * ∑ x : ZMod q, Complex.normSq (f x) := by
  have hcharSum (t : ZMod q) :
    (∑ k : ZMod q, ZMod.stdAddChar (t * k)) = if t = 0 then (q : ℂ) else 0 := by
    by_cases ht : t = 0
    · subst t
      simp only [zero_mul, AddChar.map_zero_eq_one, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, mul_one, ZMod.card, ite_true]
    · have hne : ZMod.stdAddChar.mulShift t ≠ 1 := by
        intro h
        have hv := congrArg (fun ψ : AddChar (ZMod q) ℂ => ψ 1) h
        simp only [AddChar.mulShift_apply, mul_one, AddChar.one_apply] at hv
        exact ht (ZMod.injective_stdAddChar (by simpa using hv))
      calc
        _ = 0 := AddChar.sum_eq_zero_of_ne_one hne
        _ = if t = 0 then (q : ℂ) else 0 := by simp only [ite_eq_right ht]
  have hterm (k : ZMod q) :
    ZMod.dft f k * star (ZMod.dft f k) =
      ∑ x : ZMod q, ∑ y : ZMod q, f x * star (f y) * ZMod.stdAddChar ((y - x) * k) := by
    have hdft : ZMod.dft f k = ∑ x : ZMod q, ZMod.stdAddChar (-(x * k)) * f x := by
      rw [ZMod.dft_apply]
      simp only [smul_eq_mul]
    have hstar : star (ZMod.dft f k) = ∑ y : ZMod q, star (f y) * ZMod.stdAddChar (y * k) := by
      calc
        star (ZMod.dft f k) = star (∑ y : ZMod q, ZMod.stdAddChar (-(y * k)) * f y) := by
          exact congrArg star (ZMod.dft_apply f k)
        _ = ∑ y : ZMod q, star (ZMod.stdAddChar (-(y * k)) * f y) :=
          map_sum (starRingEnd ℂ) (fun y : ZMod q => ZMod.stdAddChar (-(y * k)) * f y) Finset.univ
        _ = ∑ y : ZMod q, star (f y) * ZMod.stdAddChar (y * k) := by
          apply Finset.sum_congr rfl
          intro y hy
          rw [star_mul]
          have hneg := AddChar.map_neg_eq_conj (ZMod.stdAddChar) (y * k)
          have hneg' := congrArg star hneg
          simp only [starRingEnd_apply, star_star] at hneg'
          rw [hneg']
    have hstarSum :
      star (∑ x : ZMod q, ZMod.stdAddChar (-(x * k)) * f x) =
        ∑ y : ZMod q, star (f y) * ZMod.stdAddChar (y * k) := by
      calc
        _ = star (ZMod.dft f k) := (congrArg star hdft).symm
        _ = _ := hstar
    rw [hdft, hstarSum, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro y hy
    calc
      ZMod.stdAddChar (-(x * k)) * f x * (star (f y) * ZMod.stdAddChar (y * k)) =
          f x * star (f y) * (ZMod.stdAddChar (-(x * k)) * ZMod.stdAddChar (y * k)) :=
        by ring
      _ = f x * star (f y) * ZMod.stdAddChar (-(x * k) + y * k) := by rw [← AddChar.map_add_eq_mul]
      _ = f x * star (f y) * ZMod.stdAddChar ((y - x) * k) := by
        congr 1
        ring_nf
  have hcomplex :
    (∑ k : ZMod q, ZMod.dft f k * star (ZMod.dft f k)) =
      (q : ℂ) * ∑ x : ZMod q, f x * star (f x) := by
    calc
      _ =
          ∑ k : ZMod q,
            ∑ x : ZMod q, ∑ y : ZMod q, f x * star (f y) * ZMod.stdAddChar ((y - x) * k) :=
        by
        apply Finset.sum_congr rfl
        intro k hk
        exact hterm k
      _ =
          ∑ x : ZMod q,
            ∑ y : ZMod q, f x * star (f y) * ∑ k : ZMod q, ZMod.stdAddChar ((y - x) * k) :=
        by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro x hx
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro y hy
        rw [← Finset.mul_sum]
      _ = ∑ x : ZMod q, ∑ y : ZMod q, f x * star (f y) * (if y - x = 0 then (q : ℂ) else 0) := by
        apply Finset.sum_congr rfl
        intro x hx
        apply Finset.sum_congr rfl
        intro y hy
        rw [hcharSum]
      _ = (q : ℂ) * ∑ x : ZMod q, f x * star (f x) := by
        simp only [sub_eq_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, mul_ite, mul_zero]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        ring
  have hsumNorm :
    (∑ k : ZMod q, (Complex.normSq (ZMod.dft f k) : ℂ)) =
      (q : ℂ) * ∑ x : ZMod q, (Complex.normSq (f x) : ℂ) := by
    calc
      _ = ∑ k : ZMod q, ZMod.dft f k * star (ZMod.dft f k) := by
        apply Finset.sum_congr rfl
        intro k hk
        exact (Complex.mul_conj _).symm
      _ = _ := hcomplex
      _ = _ := by
        congr 1
        apply Finset.sum_congr rfl
        intro x hx
        exact Complex.mul_conj (f x)
  exact_mod_cast hsumNorm

/--
Inputs: a Dirichlet character modulo a positive integer.

Claim: the sum of the squared absolute values of the character over all residues equals the
modulus totient.

Proof: nonunits contribute zero, while every unit has character norm one; the units are counted
by `ZMod.card_units_eq_totient`.

Role: supplies the character-side mass needed to normalize primitive Fourier transforms.
-/
theorem dirichletCharacter_normSq_sum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    (∑ x : ZMod q, Complex.normSq (χ x)) = Nat.totient q := by
  classical
  let U : Finset (ZMod q) := Finset.univ.image (fun u : (ZMod q)ˣ => (u : ZMod q))
  have hsub : U ⊆ Finset.univ := Finset.subset_univ _
  have hout (x : ZMod q) (hx : x ∈ Finset.univ) (hxU : x ∉ U) : Complex.normSq (χ x) = 0 := by
    have hnot : ¬IsUnit x := by
      intro hu
      have hmem : x ∈ U := by
        simpa only [U, Finset.mem_image, Finset.mem_univ, true_and] using
          (show ∃ u : (ZMod q)ˣ, (u : ZMod q) = x from ⟨hu.unit, hu.unit_spec⟩)
      exact hxU hmem
    rw [MulChar.map_nonunit χ hnot]
    simp only [Complex.normSq_zero]
  have hsum :
    (∑ x ∈ U, Complex.normSq (χ x)) = ∑ x ∈ (Finset.univ : Finset (ZMod q)), Complex.normSq (χ x) :=
    Finset.sum_subset hsub hout
  have hsumUnits :
    (∑ x ∈ U, Complex.normSq (χ x)) = ∑ u : (ZMod q)ˣ, Complex.normSq (χ (u : ZMod q)) := by
    change (∑ x ∈ Finset.univ.image (fun u : (ZMod q)ˣ => (u : ZMod q)), Complex.normSq (χ x)) = _
    exact
      Finset.sum_image (f := fun x : ZMod q => Complex.normSq (χ x)) (g := fun u : (ZMod q)ˣ =>
        (u : ZMod q))
        (by
          intro a ha b hb hab
          exact Units.val_injective hab)
  have hunit (u : (ZMod q)ˣ) : Complex.normSq (χ (u : ZMod q)) = 1 := by
    rw [Complex.normSq_eq_norm_sq, DirichletCharacter.unit_norm_eq_one χ u]
    norm_num only
  rw [← hsum, hsumUnits]
  calc
    _ = ∑ u : (ZMod q)ˣ, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro u hu
      exact hunit u
    _ = Nat.totient q := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
        ZMod.card_units_eq_totient]

/--
Inputs: a primitive Dirichlet character modulo an integer greater than one.

Claim: the squared absolute value of its Gauss sum for the standard additive character equals
the modulus.

Proof: apply additive Plancherel to the character, rewrite its Fourier transform by the
primitive-character formula, and cancel the positive totient using the character norm sum.

Role: gives the exact Gauss-sum normalization used in cross-modulus mean-square estimates.
-/
theorem primitive_gaussSum_normSq_eq_modulus {q : ℕ} [NeZero q] (hq : 1 < q)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) :
    Complex.normSq (gaussSum χ ZMod.stdAddChar) = q := by
  have hparseval := zmod_dft_parseval (fun x : ZMod q => χ x)
  have hformula (k : ZMod q) :
    Complex.normSq (ZMod.dft (fun x : ZMod q => χ x) k) =
      Complex.normSq (χ⁻¹ (-k)) * Complex.normSq (gaussSum χ ZMod.stdAddChar) := by
    rw [hχ.fourierTransform_eq_inv_mul_gaussSum k, Complex.normSq_mul]
  have hsumformula :
    (∑ k : ZMod q, Complex.normSq (ZMod.dft (fun x : ZMod q => χ x) k)) =
      (∑ k : ZMod q, Complex.normSq (χ⁻¹ (-k))) * Complex.normSq (gaussSum χ ZMod.stdAddChar) := by
    calc
      _ = ∑ k : ZMod q, (Complex.normSq (χ⁻¹ (-k)) * Complex.normSq (gaussSum χ ZMod.stdAddChar)) :=
        by
        apply Finset.sum_congr rfl
        intro k hk
        exact hformula k
      _ = _ := by rw [Finset.sum_mul]
  have hcharsum : (∑ k : ZMod q, Complex.normSq (χ⁻¹ (-k))) = Nat.totient q := by
    calc
      _ = ∑ k : ZMod q, Complex.normSq (χ⁻¹ k) := by
        exact
          Fintype.sum_equiv (Equiv.neg (ZMod q)) (fun k : ZMod q => Complex.normSq (χ⁻¹ (-k)))
            (fun k : ZMod q => Complex.normSq (χ⁻¹ k))
            (by
              intro k
              simp only [Equiv.neg_apply])
      _ = Nat.totient q := dirichletCharacter_normSq_sum χ⁻¹
  have hchiNorm := dirichletCharacter_normSq_sum χ
  have hpos : 0 < q := lt_trans Nat.zero_lt_one hq
  have htot : Nat.totient q ≠ 0 := Nat.ne_of_gt (Nat.totient_pos.mpr hpos)
  have hmain := hsumformula.symm.trans hparseval
  rw [hcharsum, hchiNorm] at hmain
  have htotR : (↑(Nat.totient q) : ℝ) ≠ 0 := by exact_mod_cast htot
  have hmain' :
    (↑(Nat.totient q) : ℝ) * Complex.normSq (gaussSum χ ZMod.stdAddChar) =
      (↑(Nat.totient q) : ℝ) * (↑q : ℝ) := by
    calc
      _ = (↑q : ℝ) * ↑(Nat.totient q) := hmain
      _ = _ := by ring
  exact mul_left_cancel₀ htotR hmain'

/--
Inputs: a primitive Dirichlet character modulo a positive integer and a natural-number index.

Claim: multiplying the character value by the Gauss sum of its inverse gives the additive Fourier
sum of the inverse character at that index.

Proof: apply the primitive Fourier-transform formula at the negative index, expand the discrete
Fourier transform, and remove nonunit residues where the character vanishes.

Role: converts primitive Dirichlet polynomial sums into sums over reduced additive frequencies.
-/
theorem primitive_character_fourier_inversion {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (n : ℕ) :
    gaussSum χ⁻¹ ZMod.stdAddChar * χ (n : ZMod q) =
      ∑ x ∈ (Finset.univ.filter (fun x : ZMod q => IsUnit x)),
        ZMod.stdAddChar (x * (n : ZMod q)) * χ⁻¹ x := by
  classical
  have hprimInv : χ⁻¹.IsPrimitive := by
    rw [DirichletCharacter.isPrimitive_def] at hχ ⊢
    rw [DirichletCharacter.conductor_inv]
    exact hχ
  let U : Finset (ZMod q) := Finset.univ.filter (fun x => IsUnit x)
  have hsub : U ⊆ Finset.univ := Finset.subset_univ _
  have hout (x : ZMod q) (hx : x ∈ Finset.univ) (hxU : x ∉ U) :
    ZMod.stdAddChar (x * (n : ZMod q)) * χ⁻¹ x = 0 := by
    have hnot : ¬IsUnit x := by
      intro hu
      exact hxU (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩)
    rw [MulChar.map_nonunit χ⁻¹ hnot]
    simp only [mul_zero]
  have hsum :
    (∑ x : ZMod q, ZMod.stdAddChar (x * (n : ZMod q)) * χ⁻¹ x) =
      ∑ x ∈ U, ZMod.stdAddChar (x * (n : ZMod q)) * χ⁻¹ x :=
    (Finset.sum_subset hsub hout).symm
  have hdft :
    ZMod.dft (fun x : ZMod q => χ⁻¹ x) (-(n : ZMod q)) =
      ∑ x : ZMod q, ZMod.stdAddChar (x * (n : ZMod q)) * χ⁻¹ x := by
    rw [ZMod.dft_apply]
    simp only [smul_eq_mul]
    apply Finset.sum_congr rfl
    intro x hx
    congr 1
    congr 1
    ring
  have hfour := hprimInv.fourierTransform_eq_inv_mul_gaussSum (-(n : ZMod q))
  simp only [inv_inv, neg_neg] at hfour
  rw [hdft, hsum] at hfour
  calc
    gaussSum χ⁻¹ ZMod.stdAddChar * χ (n : ZMod q) = χ (n : ZMod q) * gaussSum χ⁻¹ ZMod.stdAddChar :=
      mul_comm _ _
    _ = _ := hfour.symm

/--
Inputs: a primitive Dirichlet character, a finite set of natural-number indices, and complex
coefficients.

Claim: the Dirichlet polynomial multiplied by the inverse character's Gauss sum is the additive
Fourier polynomial over unit residues, weighted by the inverse character.

Proof: apply `primitive_character_fourier_inversion` termwise, exchange the two finite sums, and
factor the character value out of the inner sum.

Role: reduces a primitive-character mean square to additive exponential sums over reduced
fractions, the input needed for the large-sieve spacing estimate.
-/
theorem primitive_character_polynomial_additive_transform {q : ℕ} [NeZero q] (S : Finset ℕ)
    (a : ℕ → ℂ) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) :
    gaussSum χ⁻¹ ZMod.stdAddChar * (∑ n ∈ S, a n * χ (n : ZMod q)) =
      ∑ x ∈ (Finset.univ.filter (fun x : ZMod q => IsUnit x)),
        χ⁻¹ x * (∑ n ∈ S, a n * ZMod.stdAddChar (x * (n : ZMod q))) := by
  classical
  let U : Finset (ZMod q) := Finset.univ.filter (fun x => IsUnit x)
  calc
    _ = ∑ n ∈ S, gaussSum χ⁻¹ ZMod.stdAddChar * (a n * χ (n : ZMod q)) := by rw [Finset.mul_sum]
    _ = ∑ n ∈ S, a n * (gaussSum χ⁻¹ ZMod.stdAddChar * χ (n : ZMod q)) := by
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _ = ∑ n ∈ S, a n * (∑ x ∈ U, ZMod.stdAddChar (x * (n : ZMod q)) * χ⁻¹ x) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [primitive_character_fourier_inversion χ hχ n]
    _ = ∑ n ∈ S, ∑ x ∈ U, a n * (ZMod.stdAddChar (x * (n : ZMod q)) * χ⁻¹ x) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.mul_sum]
    _ = ∑ x ∈ U, ∑ n ∈ S, a n * (ZMod.stdAddChar (x * (n : ZMod q)) * χ⁻¹ x) := by
      rw [Finset.sum_comm]
    _ = ∑ x ∈ U, χ⁻¹ x * (∑ n ∈ S, a n * ZMod.stdAddChar (x * (n : ZMod q))) := by
      apply Finset.sum_congr rfl
      intro x hx
      calc
        _ = ∑ n ∈ S, χ⁻¹ x * (a n * ZMod.stdAddChar (x * (n : ZMod q))) := by
          apply Finset.sum_congr rfl
          intro n hn
          ring
        _ = _ := by rw [← Finset.mul_sum]

/--
Input: a modulus whose character type has finitely many elements.

Definition: the finite set of Dirichlet characters modulo the given modulus whose conductor is
the modulus itself.

Role: indexes primitive-character mean-square estimates without introducing an additional
unproved predicate or a computability assumption.
-/
noncomputable def primitiveDirichletCharacterSet (q : ℕ) : Finset (DirichletCharacter ℂ q) := by
  classical exact Finset.univ.filter (fun χ => χ.IsPrimitive)

/--
Inputs: a modulus greater than one, a finite Dirichlet polynomial, and its complex coefficients.

Claim: the modulus times the primitive-character mean square is bounded by the totient times the
mean square of the additive Fourier polynomial over reduced residue frequencies.

Proof: the primitive Fourier identity and exact Gauss-sum norm convert each primitive character
sum to an additive sum. Fixed-modulus Parseval bounds the primitive subset by the sum over all
characters.

Role: reduces the required cross-modulus large sieve estimate to the additive large sieve for
fractions with reduced numerator and denominator.
-/
theorem primitive_character_mean_square_additive_le {q : ℕ} [NeZero q] (hq : 1 < q) (S : Finset ℕ)
    (a : ℕ → ℂ) :
    (q : ℝ) *
        (∑ χ ∈ primitiveDirichletCharacterSet q, Complex.normSq (∑ n ∈ S, a n * χ (n : ZMod q))) ≤
      (Nat.totient q : ℝ) *
        ∑ x ∈ (Finset.univ.filter (fun x : ZMod q => IsUnit x)),
          Complex.normSq (∑ n ∈ S, a n * ZMod.stdAddChar (x * (n : ZMod q))) := by
  classical
  let U : Finset (ZMod q) := Finset.univ.filter (fun x => IsUnit x)
  let P : Finset (DirichletCharacter ℂ q) := primitiveDirichletCharacterSet q
  let f : ZMod q → ℂ := fun x => ∑ n ∈ S, a n * ZMod.stdAddChar (x * (n : ZMod q))
  let D : DirichletCharacter ℂ q → ℂ := fun χ => ∑ x ∈ U, χ⁻¹ x * f x
  have hU : ∀ x ∈ U, IsUnit x := by
    intro x hx
    exact (Finset.mem_filter.mp hx).2
  have hnorm (z : ℂ) : (Complex.normSq z : ℂ) = star z * z := by
    rw [← Complex.mul_conj z]
    exact mul_comm _ _
  have hparseval := dirichletCharacter_parseval U hU f
  have hfull :
    (∑ χ : DirichletCharacter ℂ q, Complex.normSq (D χ)) =
      Nat.totient q * ∑ x ∈ U, Complex.normSq (f x) := by
    calc
      _ = ∑ χ : DirichletCharacter ℂ q, Complex.normSq (∑ x ∈ U, f x * χ x) := by
        exact
          Fintype.sum_equiv (Equiv.inv (DirichletCharacter ℂ q)) (fun χ => Complex.normSq (D χ))
            (fun χ => Complex.normSq (∑ x ∈ U, f x * χ x))
            (by
              intro χ
              unfold D
              congr 1
              apply Finset.sum_congr rfl
              intro x hx
              rw [Equiv.inv_apply]
              ring)
      _ = _ := by
        have hC :
          ((∑ χ : DirichletCharacter ℂ q, Complex.normSq (∑ x ∈ U, f x * χ x) : ℝ) : ℂ) =
            (Nat.totient q : ℂ) * ∑ x ∈ U, star (f x) * f x := by
          calc
            _ = ∑ χ : DirichletCharacter ℂ q, star (∑ x ∈ U, f x * χ x) * (∑ x ∈ U, f x * χ x) := by
              rw [Complex.ofReal_sum]
              apply Finset.sum_congr rfl
              intro χ hχ
              exact hnorm _
            _ = _ := hparseval
        have hC' :
          ((Nat.totient q * ∑ x ∈ U, Complex.normSq (f x) : ℝ) : ℂ) =
            (Nat.totient q : ℂ) * ∑ x ∈ U, star (f x) * f x := by
          rw [Complex.ofReal_mul, Complex.ofReal_sum]
          congr 1
          apply Finset.sum_congr rfl
          intro x hx
          exact hnorm (f x)
        exact_mod_cast hC.trans hC'.symm
  have hpoint (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) :
    (q : ℝ) * Complex.normSq (∑ n ∈ S, a n * χ (n : ZMod q)) = Complex.normSq (D χ) := by
    have hprimInv : χ⁻¹.IsPrimitive := by
      rw [DirichletCharacter.isPrimitive_def] at hχ ⊢
      rw [DirichletCharacter.conductor_inv]
      exact hχ
    have htau := primitive_gaussSum_normSq_eq_modulus hq χ⁻¹ hprimInv
    have htransform := primitive_character_polynomial_additive_transform S a χ hχ
    have hnormTransform := congrArg Complex.normSq htransform
    rw [Complex.normSq_mul, htau] at hnormTransform
    simpa only [D, f, U] using hnormTransform
  have hsumP :
    (q : ℝ) * ∑ χ ∈ P, Complex.normSq (∑ n ∈ S, a n * χ (n : ZMod q)) =
      ∑ χ ∈ P, Complex.normSq (D χ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro χ hχ
    have hprimitive : χ.IsPrimitive := by
      simpa only [P, primitiveDirichletCharacterSet, Finset.mem_filter, Finset.mem_univ,
        true_and] using hχ
    exact hpoint χ hprimitive
  have hPsub : P ⊆ Finset.univ := Finset.subset_univ _
  have hPbound :
    (∑ χ ∈ P, Complex.normSq (D χ)) ≤ ∑ χ : DirichletCharacter ℂ q, Complex.normSq (D χ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hPsub
      (by
        intro χ hχ hχP
        exact Complex.normSq_nonneg (D χ))
  calc
    _ = ∑ χ ∈ P, Complex.normSq (D χ) := hsumP
    _ ≤ _ := hPbound
    _ = _ := hfull

/--
Inputs: a modulus `q` greater than one, a Ramanujan-sum modulus `r`, a finite polynomial index
set, and complex coefficients.

Claim: the primitive-character mean square with coefficients weighted by the Ramanujan sum
`ramanujanSum r n` is bounded by the corresponding reduced additive-frequency mean square.

Proof: apply the fixed-modulus character-to-additive estimate to the coefficient function
`n ↦ a n * ramanujanSum r n`.

Role: supplies the fixed-modulus weighted estimate used in the character decomposition of
Selberg's Theorem 7A.
-/
theorem primitive_character_ramanujan_weighted_mean_square_additive_le {q r : ℕ} [NeZero q]
    [NeZero r] (hq : 1 < q) (S : Finset ℕ) (a : ℕ → ℂ) :
    (q : ℝ) *
        (∑ χ ∈ primitiveDirichletCharacterSet q,
          Complex.normSq (∑ n ∈ S, (a n * ramanujanSum r n) * χ (n : ZMod q))) ≤
      (Nat.totient q : ℝ) *
        ∑ x ∈ (Finset.univ.filter (fun x : ZMod q => IsUnit x)),
          Complex.normSq
            (∑ n ∈ S, (a n * ramanujanSum r n) * ZMod.stdAddChar (x * (n : ZMod q))) := by
  exact primitive_character_mean_square_additive_le hq S (fun n => a n * ramanujanSum r n)

/--
Inputs: a modulus greater than one, a finite set of indices, and complex coefficients.

Definition: the sum of squared norms of the corresponding Dirichlet polynomial over primitive
characters modulo the modulus. The proof argument records positivity so the residue ring has its
finite type structure.

Role: packages one modulus' primitive-character mean square for finite family estimates.
-/
noncomputable def primitiveCharacterPolynomialMeanSquare (q : ℕ) (_hq : 1 < q) (S : Finset ℕ)
    (a : ℕ → ℂ) : ℝ := by
  classical
  letI : NeZero q := ⟨Nat.ne_of_gt (lt_trans Nat.zero_lt_one _hq)⟩
  exact ∑ χ ∈ primitiveDirichletCharacterSet q, Complex.normSq (∑ n ∈ S, a n * χ (n : ZMod q))

/--
Inputs: a modulus greater than one, a finite polynomial index set, complex coefficients, and a
constant complex multiplier.

Claim: multiplying every coefficient by the same constant scales the primitive-character mean
square by the squared norm of that constant.

Proof: factor the constant out of each finite character sum and use multiplicativity of
`Complex.normSq`.

Role: removes constant Ramanujan weights from mean squares on a pre-sifted support.
-/
theorem primitiveCharacterPolynomialMeanSquare_mul_const {q : ℕ} (hq : 1 < q) (S : Finset ℕ)
    (a : ℕ → ℂ) (c : ℂ) :
    primitiveCharacterPolynomialMeanSquare q hq S (fun n => a n * c) =
      Complex.normSq c * primitiveCharacterPolynomialMeanSquare q hq S a := by
  classical
  simp only [primitiveCharacterPolynomialMeanSquare]
  calc
    (∑ χ ∈ primitiveDirichletCharacterSet q, Complex.normSq (∑ n ∈ S, a n * c * χ (n : ZMod q))) =
        ∑ χ ∈ primitiveDirichletCharacterSet q,
          Complex.normSq (c * ∑ n ∈ S, a n * χ (n : ZMod q)) :=
      by
      apply Finset.sum_congr rfl
      intro χ hχ
      apply congrArg Complex.normSq
      calc
        _ = ∑ n ∈ S, c * (a n * χ (n : ZMod q)) := by
          apply Finset.sum_congr rfl
          intro n hn
          ring
        _ = _ := (Finset.mul_sum S (fun n => a n * χ (n : ZMod q)) c).symm
    _ =
        ∑ χ ∈ primitiveDirichletCharacterSet q,
          Complex.normSq c * Complex.normSq (∑ n ∈ S, a n * χ (n : ZMod q)) :=
      by
      apply Finset.sum_congr rfl
      intro χ hχ
      rw [Complex.normSq_mul]
    _ =
        Complex.normSq c *
          ∑ χ ∈ primitiveDirichletCharacterSet q, Complex.normSq (∑ n ∈ S, a n * χ (n : ZMod q)) :=
      by rw [Finset.mul_sum]

/--
Inputs: a modulus greater than one, a finite set of indices, and complex coefficients.

Definition: the sum of squared norms of the corresponding additive Fourier polynomial over unit
residues modulo the modulus.

Role: packages one modulus' reduced-frequency contribution to the additive large sieve.
-/
noncomputable def reducedAdditivePolynomialMeanSquare (q : ℕ) (_hq : 1 < q) (S : Finset ℕ)
    (a : ℕ → ℂ) : ℝ := by
  classical
  letI : NeZero q := ⟨Nat.ne_of_gt (lt_trans Nat.zero_lt_one _hq)⟩
  exact
    ∑ x ∈ (Finset.univ.filter (fun x : ZMod q => IsUnit x)),
      Complex.normSq (∑ n ∈ S, a n * ZMod.stdAddChar (x * (n : ZMod q)))

/--
Inputs: a positive modulus.

Definition: the finite set of unit residues modulo the modulus.

Output: the reduced additive frequencies used in the mean-square sum.

Role: provides the finite index type for the vector-valued form of the additive large sieve.
-/
def reducedUnitFrequencySet (q : ℕ) [NeZero q] : Finset (ZMod q) :=
  Finset.univ.filter (fun x => IsUnit x)

/--
Inputs: a nonzero modulus, a finite set of polynomial indices, and a residue frequency.

Definition: the vector on the index set whose coordinate at `n` is the conjugate standard
additive character at `x * n`.

Output: a Euclidean-space vector representing one reduced additive frequency.

Role: its inner products give the cross-frequency kernels, and its inner product with the
coefficient vector gives the corresponding additive Fourier polynomial.
-/
noncomputable def reducedUnitFrequencyVector {q : ℕ} [NeZero q] (S : Finset ℕ) (x : ZMod q) :
    EuclideanSpace ℂ (↥S) :=
  WithLp.toLp 2 (fun n : ↥S => star (ZMod.stdAddChar (x * (n.val : ZMod q))))

/--
Inputs: a rational frequency and a natural index.

Definition: the complex exponential `exp(2π i α n)` at that frequency and index.

Output: the corresponding point on the unit circle.

Role: represents reduced additive frequencies uniformly across different moduli.
-/
noncomputable def rationalAdditiveCharacter (α : ℚ) (n : ℕ) : ℂ :=
  Complex.exp (Complex.I * ((2 * Real.pi * (α : ℝ) * n : ℝ) : ℂ))

/--
Inputs: two rational frequencies and a natural index.

Claim: the cross product of their rational additive characters is the exponential at the
difference frequency.

Proof: conjugate the second exponential, combine the exponentials, and normalize the real casts.

Role: converts Gram entries of rational-frequency vectors into the Fourier kernels used in the
separated-frequency estimate.
-/
theorem rationalAdditiveCharacter_cross_eq_exp_difference (α β : ℚ) (n : ℕ) :
    rationalAdditiveCharacter α n * star (rationalAdditiveCharacter β n) =
      Complex.exp (Complex.I * ((2 * Real.pi * ((α : ℝ) - β) * n : ℝ) : ℂ)) := by
  rw [rationalAdditiveCharacter, rationalAdditiveCharacter]
  rw [show
      star (Complex.exp (Complex.I * ((2 * Real.pi * (β : ℝ) * n : ℝ) : ℂ))) =
        (starRingEnd ℂ) (Complex.exp (Complex.I * ((2 * Real.pi * (β : ℝ) * n : ℝ) : ℂ)))
      by rfl]
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  push_cast
  simp only [map_mul, map_natCast, map_ofNat, map_ratCast, Complex.conj_ofReal, Complex.conj_I]
  ring_nf

/--
Inputs: a finite set of rational frequencies, a finite index set, and complex coefficients.

Definition: the sum of squared norms of the exponential polynomials over the selected
frequencies.

Output: a finite rational-frequency mean square.

Role: is the additive large-sieve quantity for a family of reduced fractions with varying
denominators.
-/
noncomputable def rationalAdditivePolynomialMeanSquare (F : Finset ℚ) (S : Finset ℕ) (a : ℕ → ℂ) :
    ℝ :=
  ∑ α ∈ F, Complex.normSq (∑ n ∈ S, a n * rationalAdditiveCharacter α n)

/--
Inputs: a rational frequency and two natural indices.

Claim: the additive character at a sum is the product of its values at the summands.

Proof: combine the two complex exponentials and normalize the real casts.

Role: factors the phase introduced by translating a finite exponential polynomial.
-/
theorem rationalAdditiveCharacter_add (α : ℚ) (m n : ℕ) :
    rationalAdditiveCharacter α (m + n) =
      rationalAdditiveCharacter α m * rationalAdditiveCharacter α n := by
  rw [rationalAdditiveCharacter, rationalAdditiveCharacter, rationalAdditiveCharacter]
  rw [Nat.cast_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/--
Inputs: a rational frequency and a natural index.

Claim: every rational additive-character value has squared norm one.

Proof: its exponent is purely imaginary, so the complex exponential has norm one.

Role: shows that translating a polynomial changes its value only by a unit phase.
-/
theorem rationalAdditiveCharacter_normSq (α : ℚ) (n : ℕ) :
    Complex.normSq (rationalAdditiveCharacter α n) = 1 := by
  rw [Complex.normSq_eq_norm_sq, rationalAdditiveCharacter]
  rw [Complex.norm_exp_I_mul_ofReal]
  norm_num only [one_pow]

/--
Inputs: a finite index set, complex coefficients, a natural shift, and a rational frequency.

Claim: translating every index by `c` multiplies the exponential polynomial by the phase at `c`.

Proof: reindex the image sum and use the additive law for `rationalAdditiveCharacter`.

Role: transfers polynomial estimates between coefficient intervals without changing their shape.
-/
theorem rationalAdditivePolynomial_shift_eq_phase_mul (S : Finset ℕ) (a : ℕ → ℂ) (c : ℕ) (α : ℚ) :
    (∑ m ∈ S.image (fun n => n + c), a (m - c) * rationalAdditiveCharacter α m) =
      (∑ n ∈ S, a n * rationalAdditiveCharacter α n) * rationalAdditiveCharacter α c := by
  rw [Finset.sum_image]
  · rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro n hn
    change
      a ((n + c) - c) * rationalAdditiveCharacter α (n + c) =
        (a n * rationalAdditiveCharacter α n) * rationalAdditiveCharacter α c
    rw [Nat.add_sub_cancel_right]
    rw [rationalAdditiveCharacter_add]
    exact (mul_assoc (a n) (rationalAdditiveCharacter α n) (rationalAdditiveCharacter α c)).symm
  · intro x hx y hy hxy
    exact Nat.add_right_cancel hxy

/--
Inputs: a finite index set, complex coefficients, and a natural shift.

Claim: shifting indices and pulling coefficients back by truncated subtraction preserves the
coefficient norm-square sum.

Proof: reindex the image sum by the injective translation and simplify `(n + c) - c`.

Role: keeps the coefficient side of a finite large-sieve estimate unchanged under translation.
-/
theorem sum_normSq_coefficients_shift_eq (S : Finset ℕ) (a : ℕ → ℂ) (c : ℕ) :
    (∑ m ∈ S.image (fun n => n + c), ‖a (m - c)‖ ^ 2) = ∑ n ∈ S, ‖a n‖ ^ 2 := by
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro n hn
    rw [Nat.add_sub_cancel_right]
  · intro x hx y hy hxy
    exact Nat.add_right_cancel hxy

/--
Inputs: finite rational frequencies and natural-indexed coefficients with finite support `S`.

Claim: the mean square is invariant under translating `S` and pulling coefficients back.

Proof: each polynomial acquires a unit-modulus phase, so `Complex.normSq` is unchanged.

Role: moves arbitrary finite support into the central interval required by the triangular-window
large-sieve estimate.
-/
theorem rationalAdditivePolynomialMeanSquare_shift_eq (F : Finset ℚ) (S : Finset ℕ) (a : ℕ → ℂ)
    (c : ℕ) :
    rationalAdditivePolynomialMeanSquare F (S.image (fun n => n + c)) (fun m => a (m - c)) =
      rationalAdditivePolynomialMeanSquare F S a := by
  unfold rationalAdditivePolynomialMeanSquare
  apply Finset.sum_congr rfl
  intro α hα
  rw [rationalAdditivePolynomial_shift_eq_phase_mul, Complex.normSq_mul,
    rationalAdditiveCharacter_normSq, mul_one]

/--
Inputs: a finite polynomial index set and a rational frequency.

Definition: the Euclidean-space vector of conjugate exponential values on that index set.

Output: a vector whose pairing with a coefficient vector gives the frequency's exponential
polynomial.

Role: applies Gram-row estimates uniformly to rational frequencies from different moduli.
-/
noncomputable def rationalFrequencyVector (S : Finset ℕ) (α : ℚ) : EuclideanSpace ℂ (↥S) :=
  WithLp.toLp 2 (fun n : ↥S => star (rationalAdditiveCharacter α n.val))

/--
Inputs: a finite index set and two rational frequencies.

Claim: the inner product of the conjugate exponential vectors equals their finite cross kernel.

Proof: expand the Euclidean-space inner product by coordinates.

Role: expresses the family Gram matrix directly in terms of rational-frequency correlations.
-/
theorem rationalFrequencyVector_inner_eq_cross_sum (S : Finset ℕ) (α β : ℚ) :
    inner ℂ (rationalFrequencyVector S α) (rationalFrequencyVector S β) =
      ∑ n ∈ S, rationalAdditiveCharacter α n * star (rationalAdditiveCharacter β n) := by
  rw [PiLp.inner_apply]
  simp only [rationalFrequencyVector, WithLp.ofLp_toLp, RCLike.inner_apply', starRingEnd_apply,
    star_star]
  rw [Finset.sum_subtype S (fun _ => Iff.rfl)]

/--
Inputs: a coefficient interval length, a positive taper length, and an extended index.

Definition: the number of shifts in an interval of length `L` whose translated index lies in the
interval of length `N + L`, normalized by `L`.

Output: a real weight in `[0, 1]` on the extension interval and zero outside it.

Role: its Fourier sum factors into two finite geometric sums, which provides the decay needed for
the separated-frequency Gram row bound.
-/
noncomputable def triangleOverlapWindowWeight (N L n : ℕ) : ℝ :=
  if n < N + 2 * L - 1 then
    (((Finset.range L).filter (fun j => L ≤ n + j + 1 ∧ n + j + 1 < N + 2 * L)).card : ℝ) / L
  else 0

/--
Inputs: an interval length, a positive taper length, and an extended index.

Definition: the square root of `triangleOverlapWindowWeight`, used as the coordinate amplitude
of a frequency vector.

Role: squaring this amplitude recovers the overlap weight in the Fourier Gram kernel.
-/
noncomputable def triangleOverlapWindow (N L n : ℕ) : ℝ :=
  Real.sqrt (triangleOverlapWindowWeight N L n)

/--
Inputs: a positive taper length and an index in the central coefficient interval.

Claim: the overlap weight and its square-root window both equal one on that interval.

Proof: both overlaps in the defining minimum are at least `L`, so the minimum is `L`.

Role: ensures that the extended frequency vectors reproduce the original polynomial.
-/
theorem triangleOverlapWindow_eq_one {N L n : ℕ} (hL : 0 < L) (hnlo : L - 1 ≤ n)
    (hnhi : n ≤ N + L - 1) :
    triangleOverlapWindowWeight N L n = 1 ∧ triangleOverlapWindow N L n = 1 := by
  have hncond : n < N + 2 * L - 1 := by omega
  have hLcast : (L : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hL
  have hfilter :
    (Finset.range L).filter (fun j => L ≤ n + j + 1 ∧ n + j + 1 < N + 2 * L) = Finset.range L := by
    apply Finset.filter_eq_self.mpr
    intro j hj
    have hjL : j < L := Finset.mem_range.mp hj
    constructor <;> omega
  constructor
  · rw [triangleOverlapWindowWeight, ite_eq_left hncond, hfilter, Finset.card_range]
    exact div_self hLcast
  · rw [triangleOverlapWindow, triangleOverlapWindowWeight, ite_eq_left hncond, hfilter,
      Finset.card_range, div_self hLcast, Real.sqrt_one]

/--
Inputs: an interval length, a taper length, and an extended index.

Claim: the overlap weight is nonnegative, including outside its finite support.

Proof: on the support it is a quotient of nonnegative natural casts by a nonnegative cast; outside
the support it is zero.

Role: permits squaring the square-root window to recover the overlap weight exactly.
-/
theorem triangleOverlapWindowWeight_nonneg (N L n : ℕ) : 0 ≤ triangleOverlapWindowWeight N L n := by
  rw [triangleOverlapWindowWeight]
  by_cases hn : n < N + 2 * L - 1
  · rw [ite_eq_left hn]
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · rw [ite_eq_right hn]

/--
Inputs: an interval length, a taper length, and an extended index.

Claim: the squared window amplitude equals the overlap weight at every index.

Proof: apply the real square-root identity to the nonnegative overlap weight.

Role: identifies the Gram kernel of the windowed frequencies with the finite overlap convolution.
-/
theorem triangleOverlapWindow_sq_eq_weight (N L n : ℕ) :
    triangleOverlapWindow N L n ^ 2 = triangleOverlapWindowWeight N L n := by
  rw [triangleOverlapWindow]
  exact Real.sq_sqrt (triangleOverlapWindowWeight_nonneg N L n)

/--
Inputs: an interval length, a taper length, and an index beyond the extension interval.

Claim: the square-root window vanishes outside its finite support.

Proof: the defining overlap weight is zero there, and the real square root of zero is zero.

Role: identifies the finite index set needed for the extended frequency vectors.
-/
theorem triangleOverlapWindow_eq_zero_of_le {N L n : ℕ} (hn : N + 2 * L - 1 ≤ n) :
    triangleOverlapWindow N L n = 0 := by
  have hnot : ¬n < N + 2 * L - 1 := Nat.not_lt.mpr hn
  rw [triangleOverlapWindow, triangleOverlapWindowWeight, ite_eq_right hnot, Real.sqrt_zero]

/--
Inputs: an interval length, a positive taper length, and an index.

Claim: the normalized overlap weight is at most one.

Proof: the overlap count is bounded by the shorter interval length `L`; outside its support the
weight is zero.

Role: bounds diagonal entries of the extended frequency Gram matrix.
-/
theorem triangleOverlapWindowWeight_le_one {N L n : ℕ} (hL : 0 < L) :
    triangleOverlapWindowWeight N L n ≤ 1 := by
  rw [triangleOverlapWindowWeight]
  by_cases hn : n < N + 2 * L - 1
  · rw [ite_eq_left hn]
    have hcard :
      ((Finset.range L).filter (fun j => L ≤ n + j + 1 ∧ n + j + 1 < N + 2 * L)).card ≤ L := by
      calc
        _ ≤ (Finset.range L).card := Finset.card_filter_le _ _
        _ = L := by rw [Finset.card_range]
    have hcardR :
      (((Finset.range L).filter (fun j => L ≤ n + j + 1 ∧ n + j + 1 < N + 2 * L)).card : ℝ) ≤
        (L : ℝ) := by
      exact_mod_cast hcard
    have hLR : (0 : ℝ) < L := by exact_mod_cast hL
    rw [div_le_iff₀ hLR]
    simpa only [one_mul] using hcardR
  · rw [ite_eq_right hn]
    exact zero_le_one

/--
Inputs: an interval length, a positive taper length, and an index.

Claim: the square-root window amplitude is at most one.

Proof: use monotonicity of the real square root and the overlap weight bound.

Role: provides a pointwise bound for the extended frequency vectors.
-/
theorem triangleOverlapWindow_le_one {N L n : ℕ} (hL : 0 < L) :
    triangleOverlapWindow N L n ≤ 1 := by
  rw [triangleOverlapWindow, ← Real.sqrt_one]
  exact Real.sqrt_le_sqrt (triangleOverlapWindowWeight_le_one hL)

/--
Inputs: an interval length, a taper length, and a complex ratio.

Claim: the finite Fourier sum of the overlap weights equals the normalized sum over all valid
overlap pairs.

Proof: write each filtered cardinality as a sum of indicator values, then collect the terms by
their first index.

Role: is the first step in factoring the window kernel into two geometric sums.
-/
theorem triangleOverlapWindowWeight_fourier_eq_pair_sum (N L : ℕ) (z : ℂ) :
    ∑ n ∈ Finset.range (N + 2 * L - 1), (triangleOverlapWindowWeight N L n : ℂ) * z ^ n =
      (L : ℂ)⁻¹ *
        ∑ n ∈ Finset.range (N + 2 * L - 1),
          ∑ j ∈ Finset.range L, if L ≤ n + j + 1 ∧ n + j + 1 < N + 2 * L then z ^ n else 0 := by
  classical
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hnlt : n < N + 2 * L - 1 := Finset.mem_range.mp hn
  rw [triangleOverlapWindowWeight, ite_eq_left hnlt]
  rw [Complex.ofReal_div, Complex.ofReal_natCast, Finset.natCast_card_filter (R := ℂ)]
  have hsum :
    (∑ j ∈ Finset.range L, if L ≤ n + j + 1 ∧ n + j + 1 < N + 2 * L then (1 : ℂ) else 0) * z ^ n =
      ∑ j ∈ Finset.range L, if L ≤ n + j + 1 ∧ n + j + 1 < N + 2 * L then z ^ n else 0 := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hp : L ≤ n + j + 1 ∧ n + j + 1 < N + 2 * L
    · simp only [ite_eq_left hp, one_mul]
    · simp only [ite_eq_right hp, zero_mul]
  calc
    (∑ j ∈ Finset.range L, if L ≤ n + j + 1 ∧ n + j + 1 < N + 2 * L then (1 : ℂ) else 0) / ↑L *
          z ^ n =
        (↑L)⁻¹ *
          ((∑ j ∈ Finset.range L, if L ≤ n + j + 1 ∧ n + j + 1 < N + 2 * L then (1 : ℂ) else 0) *
            z ^ n) :=
      by ring
    _ = _ := congrArg ((↑L)⁻¹ * ·) hsum

/--
Inputs: an interval length, a taper length, and a complex ratio.

Claim: the overlap-pair Fourier sum factors into two finite geometric sums.

Proof: reindex each valid pair by its translated interval coordinate, then separate the two
coordinates in the product of finite sums.

Role: gives the explicit Fourier kernel needed to bound the extended Gram rows.
-/
theorem triangleOverlapWindow_pair_sum_eq_geometric_product (N L : ℕ) (z : ℂ) :
    ∑ n ∈ Finset.range (N + 2 * L - 1),
        ∑ j ∈ Finset.range L, (if L ≤ n + j + 1 ∧ n + j + 1 < N + 2 * L then z ^ n else 0) =
      (∑ i ∈ Finset.range (N + L), z ^ i) * ∑ j ∈ Finset.range L, z ^ (L - 1 - j) := by
  classical
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Finset.sum_filter]
  rw [Finset.sum_mul (Finset.range (N + L)) (fun i => z ^ i) (z ^ (L - 1 - j))]
  refine
    Finset.sum_bij' (i := fun n _ => n + j + 1 - L) (j := fun i _ => i + (L - 1 - j)) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn
    have hsplit := Nat.sub_add_cancel hn.2.1
    simp only [Finset.mem_range]
    omega
  · intro i hi
    have hjlt : j < L := Finset.mem_range.mp hj
    simp only [Finset.mem_range] at hi
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn
    have hsplit := Nat.sub_add_cancel hn.2.1
    have hjlt : j < L := Finset.mem_range.mp hj
    have hjle : j ≤ L - 1 := by omega
    have hshift := Nat.sub_add_cancel hjle
    omega
  · intro i hi
    have hjlt : j < L := Finset.mem_range.mp hj
    have hilt : i < N + L := Finset.mem_range.mp hi
    omega
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn
    have hsplit := Nat.sub_add_cancel hn.2.1
    have hjlt : j < L := Finset.mem_range.mp hj
    have hjle : j ≤ L - 1 := by omega
    have hshift := Nat.sub_add_cancel hjle
    rw [← pow_add]
    congr 1
    omega

/--
Inputs: an interval length, a taper length, and a complex ratio.

Claim: the Fourier transform of the normalized overlap weights is a product of two geometric sums.

Proof: apply the overlap-pair expansion and its finite reindexing factorization.

Role: expresses the concrete window Gram kernel in a form suitable for frequency separation.
-/
theorem triangleOverlapWindowWeight_fourier_eq_geometric_product (N L : ℕ) (z : ℂ) :
    ∑ n ∈ Finset.range (N + 2 * L - 1), (triangleOverlapWindowWeight N L n : ℂ) * z ^ n =
      (L : ℂ)⁻¹ * (∑ i ∈ Finset.range (N + L), z ^ i) * ∑ j ∈ Finset.range L, z ^ (L - 1 - j) := by
  rw [triangleOverlapWindowWeight_fourier_eq_pair_sum,
    triangleOverlapWindow_pair_sum_eq_geometric_product]
  ring

/--
Inputs: a coefficient interval length, a positive taper length, and the finite extension interval.

Claim: the total overlap weight on the extension interval is `N + L`.

Proof: evaluate the Fourier factorization at frequency one; the two geometric sums count their
respective intervals, and the normalization cancels the taper length.

Role: gives the diagonal entry of each windowed Gram row.
-/
theorem triangleOverlapWindowWeight_sum_eq (N L : ℕ) (hL : 0 < L) :
    ∑ n ∈ Finset.range (N + 2 * L - 1), triangleOverlapWindowWeight N L n = N + L := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_sum, Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_natCast]
  calc
    ∑ n ∈ Finset.range (N + 2 * L - 1), (triangleOverlapWindowWeight N L n : ℂ) =
        ∑ n ∈ Finset.range (N + 2 * L - 1), (triangleOverlapWindowWeight N L n : ℂ) * (1 : ℂ) ^ n :=
      by
      apply Finset.sum_congr rfl
      intro n hn
      simp only [one_pow, mul_one]
    _ = ((N + L : ℕ) : ℂ) := by
      rw [triangleOverlapWindowWeight_fourier_eq_geometric_product]
      simp only [one_pow, Finset.sum_const, nsmul_eq_mul, Finset.card_range]
      field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt hL)]
    _ = (N : ℂ) + (L : ℂ) := by rw [Nat.cast_add]

/--
Inputs: a finite index set, a real-valued window, and a rational frequency.

Definition: the conjugate rational exponential vector multiplied coordinatewise by the window.

Output: a vector whose Gram kernel is the Fourier sum of the squared window.

Role: supplies the extended test vectors used in the separated-frequency large sieve.
-/
noncomputable def rationalWindowFrequencyVector (T : Finset ℕ) (w : ℕ → ℝ) (α : ℚ) :
    EuclideanSpace ℂ (↥T) :=
  WithLp.toLp 2 (fun n : ↥T => star (rationalAdditiveCharacter α n.val) * (w n.val : ℂ))

/--
Inputs: a finite coefficient set, a finite extended index set containing it, and complex
coefficients.

Definition: the coefficient vector on the extended index set, set to zero outside the original
coefficient set.

Role: tests windowed rational-frequency vectors while preserving the original coefficient norm.
-/
noncomputable def rationalWindowCoefficientVector (S T : Finset ℕ) (a : ℕ → ℂ) :
    EuclideanSpace ℂ (↥T) :=
  WithLp.toLp 2 (fun n : ↥T => if n.val ∈ S then a n.val else 0)

/--
Inputs: a coefficient set contained in an extended index set, a real-valued window equal to one
on the coefficient set, a rational frequency, and complex coefficients.

Claim: the inner product of the windowed frequency vector with the extended coefficient vector
equals the original rational exponential polynomial.

Proof: expand by coordinates; the window is one on the coefficient support and the coefficient
vector vanishes outside it.

Role: realizes the original polynomial as a sample of the smoothed, extended frequency family.
-/
theorem rationalWindowFrequencyVector_inner_eq_polynomial (S T : Finset ℕ) (hST : S ⊆ T) (w : ℕ → ℝ)
    (hw : ∀ n ∈ S, w n = 1) (α : ℚ) (a : ℕ → ℂ) :
    inner ℂ (rationalWindowFrequencyVector T w α) (rationalWindowCoefficientVector S T a) =
      ∑ n ∈ S, a n * rationalAdditiveCharacter α n := by
  rw [PiLp.inner_apply]
  simp only [rationalWindowFrequencyVector, rationalWindowCoefficientVector, WithLp.ofLp_toLp,
    RCLike.inner_apply', starRingEnd_apply, star_mul, star_star]
  rw [Finset.sum_coe_sort T
      (fun n : ℕ => star (w n : ℂ) * rationalAdditiveCharacter α n * if n ∈ S then a n else 0)]
  calc
    (∑ n ∈ T, star (w n : ℂ) * rationalAdditiveCharacter α n * if n ∈ S then a n else 0) =
        ∑ n ∈ T, if n ∈ S then a n * rationalAdditiveCharacter α n else 0 :=
      by
      apply Finset.sum_congr rfl
      intro n hn
      by_cases hs : n ∈ S
      · rw [ite_eq_left hs, ite_eq_left hs]
        rw [show star (w n : ℂ) = (w n : ℂ) by rw [RCLike.star_def, Complex.conj_ofReal]]
        rw [hw n hs]
        simp only [Complex.ofReal_one, one_mul]
        exact mul_comm _ _
      · rw [ite_eq_right hs, ite_eq_right hs]
        simp only [mul_zero]
    _ = ∑ n ∈ S, a n * rationalAdditiveCharacter α n := by
      calc
        _ = ∑ n ∈ S, if n ∈ S then a n * rationalAdditiveCharacter α n else 0 :=
          (Finset.sum_subset hST
              (by
                intro n hn hnot
                rw [ite_eq_right hnot])).symm
        _ = _ := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [ite_eq_left hn]

/--
Inputs: finite coefficient and extended index sets, a positive taper length, coefficient support
inside the flat part of the overlap window, a rational frequency, and complex coefficients.

Claim: the overlap-window frequency vector paired with the zero-extended coefficients gives the
original rational exponential polynomial.

Proof: the overlap window equals one throughout the coefficient support, so the general window
inner-product identity applies.

Role: instantiates the abstract extension interface with the explicit finite overlap window.
-/
theorem rationalTriangleOverlapFrequencyVector_inner_eq_polynomial (S T : Finset ℕ) (hST : S ⊆ T)
    (N L : ℕ) (hL : 0 < L) (hcentral : ∀ n ∈ S, L - 1 ≤ n ∧ n ≤ N + L - 1) (α : ℚ) (a : ℕ → ℂ) :
    inner ℂ (rationalWindowFrequencyVector T (triangleOverlapWindow N L) α)
        (rationalWindowCoefficientVector S T a) =
      ∑ n ∈ S, a n * rationalAdditiveCharacter α n := by
  exact
    rationalWindowFrequencyVector_inner_eq_polynomial S T hST (triangleOverlapWindow N L)
      (fun n hn => (triangleOverlapWindow_eq_one hL (hcentral n hn).1 (hcentral n hn).2).2) α a

/--
Inputs: a finite index set, two rational frequencies, and a real-valued window.

Claim: the inner product of the windowed frequency vectors equals the Fourier sum weighted by
the square of the window.

Proof: expand the Euclidean-space inner product by coordinates and simplify the conjugates.

Role: converts row bounds for smoothed frequencies into the Gram-row hypothesis of the
large-sieve estimate.
-/
theorem rationalWindowFrequencyVector_inner_eq_weighted_cross_sum (T : Finset ℕ) (w : ℕ → ℝ)
    (α β : ℚ) :
    inner ℂ (rationalWindowFrequencyVector T w α) (rationalWindowFrequencyVector T w β) =
      ∑ n ∈ T,
        (w n : ℂ) ^ 2 * rationalAdditiveCharacter α n * star (rationalAdditiveCharacter β n) := by
  rw [PiLp.inner_apply]
  simp only [rationalWindowFrequencyVector, WithLp.ofLp_toLp, RCLike.inner_apply',
    starRingEnd_apply, star_mul, star_star]
  rw [Finset.sum_subtype T (fun _ => Iff.rfl)]
  apply Finset.sum_congr rfl
  intro n hn
  rw [show star (w n : ℂ) = (w n : ℂ) by
      rw [RCLike.star_def]
      exact Complex.conj_ofReal (w n)]
  ring_nf

/--
Inputs: a finite index set, a real-valued window, and two rational frequencies.

Claim: the windowed Gram inner product is the Fourier sum of the squared window at their
difference frequency.

Proof: expand the cross sum, combine the rational exponentials, and use the natural-power law
for `Complex.exp`.

Role: converts the vector Gram row into the Fourier kernel estimated by the separated-frequency
argument.
-/
theorem rationalWindowFrequencyVector_inner_eq_fourier_difference (T : Finset ℕ) (w : ℕ → ℝ)
    (α β : ℚ) :
    inner ℂ (rationalWindowFrequencyVector T w α) (rationalWindowFrequencyVector T w β) =
      ∑ n ∈ T,
        (w n : ℂ) ^ 2 * Complex.exp (Complex.I * ((2 * Real.pi * ((α : ℝ) - β) : ℝ) : ℂ)) ^ n := by
  rw [rationalWindowFrequencyVector_inner_eq_weighted_cross_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [mul_assoc, rationalAdditiveCharacter_cross_eq_exp_difference]
  congr 1
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/--
Inputs: an interval length, taper length, finite index set, and two rational frequencies.

Claim: the Gram inner product for the triangle window is the Fourier sum of its overlap weight
at the difference frequency.

Proof: expand the windowed Gram product and use that the triangle window squared is the overlap
weight.

Role: identifies the rational-frequency Gram kernel with the kernel bounded by the separated
frequency row estimate.
-/
theorem rationalTriangleOverlapFrequencyVector_inner_eq_weight_fourier (N L : ℕ) (T : Finset ℕ)
    (α β : ℚ) :
    inner ℂ (rationalWindowFrequencyVector T (triangleOverlapWindow N L) α)
        (rationalWindowFrequencyVector T (triangleOverlapWindow N L) β) =
      ∑ n ∈ T,
        (triangleOverlapWindowWeight N L n : ℂ) *
          Complex.exp (Complex.I * ((2 * Real.pi * ((α : ℝ) - β) : ℝ) : ℂ)) ^ n := by
  rw [rationalWindowFrequencyVector_inner_eq_fourier_difference]
  apply Finset.sum_congr rfl
  intro n hn
  rw [← Complex.ofReal_pow, triangleOverlapWindow_sq_eq_weight]

/--
Inputs: finite coefficient and extended index sets with inclusion, and complex coefficients.

Claim: extending the coefficient vector by zero preserves its squared Euclidean norm.

Proof: expand the norm coordinatewise, remove the zero coordinates outside the coefficient set,
and use that the coefficient set is contained in the extended set.

Role: supplies the norm identity needed to apply the abstract Gram-row estimate to windowed
frequencies.
-/
theorem rationalWindowCoefficientVector_norm_sq_eq (S T : Finset ℕ) (hST : S ⊆ T) (a : ℕ → ℂ) :
    ‖rationalWindowCoefficientVector S T a‖ ^ 2 = ∑ n ∈ S, ‖a n‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  dsimp only [rationalWindowCoefficientVector]
  rw [Finset.sum_coe_sort T (fun n : ℕ => ‖if n ∈ S then a n else 0‖ ^ 2)]
  calc
    (∑ n ∈ T, ‖if n ∈ S then a n else 0‖ ^ 2) = ∑ n ∈ T, if n ∈ S then ‖a n‖ ^ 2 else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      by_cases hs : n ∈ S
      · rw [ite_eq_left hs, ite_eq_left hs]
      · rw [ite_eq_right hs, ite_eq_right hs]
        rw [norm_zero]
        norm_num only
    _ = ∑ n ∈ S, ‖a n‖ ^ 2 := by
      calc
        _ = ∑ n ∈ S, if n ∈ S then ‖a n‖ ^ 2 else 0 :=
          (Finset.sum_subset hST
              (by
                intro n hn hnot
                rw [ite_eq_right hnot])).symm
        _ = _ := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [ite_eq_left hn]

/--
Inputs: a nonzero modulus, a finite polynomial index set, and two residue frequencies.

Claim: the inner product of their conjugate-character vectors is the finite cross-frequency
kernel over the polynomial indices.

Proof: expand the Euclidean-space inner product by coordinates and simplify the conjugates.

Role: converts Gram row bounds for the frequency vectors into bounds on additive character
correlation sums.
-/
theorem reducedUnitFrequencyVector_inner_eq_cross_sum {q : ℕ} [NeZero q] (S : Finset ℕ)
    (x y : ZMod q) :
    inner ℂ (reducedUnitFrequencyVector S x) (reducedUnitFrequencyVector S y) =
      ∑ n ∈ S, ZMod.stdAddChar (x * (n : ZMod q)) * star (ZMod.stdAddChar (y * (n : ZMod q))) := by
  rw [PiLp.inner_apply]
  simp only [reducedUnitFrequencyVector, WithLp.ofLp_toLp, RCLike.inner_apply', starRingEnd_apply,
    star_star]
  rw [Finset.sum_subtype S (fun _ => Iff.rfl)]

/--
Inputs: a modulus greater than one, a finite polynomial index set, and complex coefficients.

Claim: the reduced additive mean square equals the sum over unit frequencies of the associated
Gram sums, with one term for every ordered pair of polynomial indices.

Proof: express the complex norm square as a conjugate product, distribute both finite sums, and
use symmetry of the two index sums.

Role: exposes the diagonal and cross-frequency contributions needed to aggregate the additive
mean squares across a family of moduli.
-/
theorem reducedAdditivePolynomialMeanSquare_gram {q : ℕ} [NeZero q] (hq : 1 < q) (S : Finset ℕ)
    (a : ℕ → ℂ) :
    ((reducedAdditivePolynomialMeanSquare q hq S a : ℝ) : ℂ) =
      ∑ x ∈ (Finset.univ.filter (fun x : ZMod q => IsUnit x)),
        ∑ n ∈ S,
          ∑ m ∈ S,
            star (a n * ZMod.stdAddChar (x * (n : ZMod q))) *
              (a m * ZMod.stdAddChar (x * (m : ZMod q))) := by
  classical
  rw [reducedAdditivePolynomialMeanSquare, Complex.ofReal_sum]
  have hnorm (z : ℂ) : (Complex.normSq z : ℂ) = star z * z := by
    rw [← Complex.mul_conj z]
    exact mul_comm _ _
  apply Finset.sum_congr rfl
  intro x hx
  rw [hnorm]
  simp only [star_sum, Finset.sum_mul, Finset.mul_sum, star_mul]
  rw [Finset.sum_comm]

/--
Inputs: a modulus greater than one, a finite polynomial index set, and complex coefficients.

Claim: the reduced additive mean square is the polynomial's Gram sum over ordered pairs of
indices, with each pair weighted by its summed cross-frequency kernel.

Proof: start from `reducedAdditivePolynomialMeanSquare_gram`, interchange the finite sums, swap
the two polynomial indices, and factor their coefficients from the frequency sum.

Role: exposes the exact cross-kernel form used to seek a collective bound across denominators.
-/
theorem reducedAdditivePolynomialMeanSquare_kernel {q : ℕ} [NeZero q] (hq : 1 < q) (S : Finset ℕ)
    (a : ℕ → ℂ) :
    ((reducedAdditivePolynomialMeanSquare q hq S a : ℝ) : ℂ) =
      ∑ n ∈ S,
        ∑ m ∈ S,
          a n * star (a m) *
            ∑ x ∈ (Finset.univ.filter (fun x : ZMod q => IsUnit x)),
              ZMod.stdAddChar (x * (n : ZMod q)) * star (ZMod.stdAddChar (x * (m : ZMod q))) := by
  classical
  rw [reducedAdditivePolynomialMeanSquare_gram]
  calc
    _ =
        ∑ n ∈ S,
          ∑ m ∈ S,
            ∑ x ∈ (Finset.univ.filter (fun x : ZMod q => IsUnit x)),
              star (a n * ZMod.stdAddChar (x * (n : ZMod q))) *
                (a m * ZMod.stdAddChar (x * (m : ZMod q))) :=
      by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.sum_comm]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro m hm
      calc
        _ =
            ∑ x ∈ (Finset.univ.filter (fun x : ZMod q => IsUnit x)),
              a n * star (a m) *
                (ZMod.stdAddChar (x * (n : ZMod q)) * star (ZMod.stdAddChar (x * (m : ZMod q)))) :=
          by
          apply Finset.sum_congr rfl
          intro x hx
          rw [star_mul]
          ring_nf
        _ = _ := by rw [Finset.mul_sum]

/--
Inputs: a modulus with its nonzero instance and an additive frequency modulo that modulus.

Claim: the diagonal cross-frequency kernel over unit residues is the Euler totient of the
modulus, independently of the frequency.

Proof: each additive character has norm one, so each diagonal summand is one; identify the units
with the filtered residue subtype and count them by `ZMod.card_units_eq_totient`.

Role: gives the exact diagonal contribution in the Gram expansion of the reduced additive mean
square.
-/
theorem additive_unit_frequency_selfKernel_eq_totient {q : ℕ} [NeZero q] (k : ZMod q) :
    (∑ x ∈ (Finset.univ.filter (fun x : ZMod q => IsUnit x)),
        ZMod.stdAddChar (x * k) * star (ZMod.stdAddChar (x * k))) =
      (Nat.totient q : ℂ) := by
  classical
  let U : Finset (ZMod q) := Finset.univ.filter (fun x => IsUnit x)
  have hU : ∀ x, x ∈ U ↔ IsUnit x := by
    intro x
    simp only [U, Finset.mem_filter, Finset.mem_univ, true_and]
  have hnorm (z : ℂ) : (Complex.normSq z : ℂ) = star z * z := by
    rw [← Complex.mul_conj z]
    exact mul_comm _ _
  have hphase (x : ZMod q) : ZMod.stdAddChar (x * k) * star (ZMod.stdAddChar (x * k)) = 1 := by
    calc
      _ = star (ZMod.stdAddChar (x * k)) * ZMod.stdAddChar (x * k) := mul_comm _ _
      _ = Complex.normSq (ZMod.stdAddChar (x * k)) := (hnorm _).symm
      _ = 1 := by
        rw [Complex.normSq_eq_norm_sq, ZMod.stdAddChar_apply, Circle.norm_coe]
        norm_num only [Complex.ofReal_one]
  calc
    _ = ∑ x ∈ U, (1 : ℂ) := by
      apply Finset.sum_congr rfl
      intro x hx
      exact hphase x
    _ = ∑ u : (ZMod q)ˣ, (1 : ℂ) := by
      let e : (ZMod q)ˣ ≃ { x : ZMod q // x ∈ U } :=
        { toFun := fun u => ⟨u, (hU u).2 u.isUnit⟩
          invFun := fun x => ((hU x.1).1 x.2).unit
          left_inv := fun u => by
            apply Units.ext
            rfl
          right_inv := fun x => by
            apply Subtype.ext
            exact IsUnit.unit_spec ((hU x.1).1 x.2) }
      calc
        _ = ∑ x : { x : ZMod q // x ∈ U }, (1 : ℂ) :=
          Finset.sum_subtype U (fun _ => Iff.rfl) (fun _ => (1 : ℂ))
        _ = _ := (Fintype.sum_equiv e (fun _ => (1 : ℂ)) (fun _ => (1 : ℂ)) (fun _ => rfl)).symm
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      rw [← ZMod.card_units_eq_totient]

/--
Inputs: a modulus with its nonzero instance, a finite set of polynomial indices, and complex
coefficients.

Claim: the diagonal terms in the kernel expansion sum to the totient of the modulus times the
coefficient norm-square sum.

Proof: replace each diagonal unit-frequency kernel by `Nat.totient q`, then factor this constant
out of the finite sum.

Role: isolates the exact diagonal contribution before estimating the off-diagonal correlations.
-/
theorem reducedAdditivePolynomialMeanSquare_diagonal {q : ℕ} [NeZero q] (S : Finset ℕ) (a : ℕ → ℂ) :
    (∑ n ∈ S,
        a n * star (a n) *
          ∑ x ∈ (Finset.univ.filter (fun x : ZMod q => IsUnit x)),
            ZMod.stdAddChar (x * (n : ZMod q)) * star (ZMod.stdAddChar (x * (n : ZMod q)))) =
      (Nat.totient q : ℂ) * ∑ n ∈ S, a n * star (a n) := by
  classical
    calc
    _ = ∑ n ∈ S, (a n * star (a n) * (Nat.totient q : ℂ)) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [additive_unit_frequency_selfKernel_eq_totient]
    _ = _ := by
      rw [← Finset.sum_mul]
      exact mul_comm _ _

/--
Inputs: a finite set of rational frequencies, a finite polynomial index set, complex
coefficients, and a uniform Gram row bound.

Claim: the rational additive mean square is bounded by the row bound times the coefficient
norm-square sum.

Proof: represent each rational frequency by its conjugate-character vector and apply the dual
Gram-row estimate to the coefficient vector.

Role: provides the common-frequency-family interface needed to combine additive frequencies
coming from different moduli.
-/
theorem rationalAdditivePolynomialMeanSquare_le_of_innerProduct_representation {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] (F : Finset ℚ) (S : Finset ℕ) (a : ℕ → ℂ)
    (φ : { α : ℚ // α ∈ F } → E) (x : E) (R : ℝ) (hR : 0 ≤ R)
    (hrow : ∀ α, ∑ β, ‖inner ℂ (φ α) (φ β)‖ ≤ R)
    (heval : ∀ α, inner ℂ (φ α) x = ∑ n ∈ S, a n * rationalAdditiveCharacter α.val n)
    (hnorm : ‖x‖ ^ 2 = ∑ n ∈ S, ‖a n‖ ^ 2) :
    rationalAdditivePolynomialMeanSquare F S a ≤ R * ∑ n ∈ S, ‖a n‖ ^ 2 := by
  classical
  have hBessel : (∑ α : { α : ℚ // α ∈ F }, ‖inner ℂ (φ α) x‖ ^ 2) ≤ R * ‖x‖ ^ 2 := by
    exact
      PseudoPrime.Analysis.FiniteGramBounds.sum_inner_product_norm_sq_le_of_gram_row_bound φ R hR
        hrow x
  have hmean :
    rationalAdditivePolynomialMeanSquare F S a =
      ∑ α : { α : ℚ // α ∈ F }, ‖inner ℂ (φ α) x‖ ^ 2 := by
    rw [rationalAdditivePolynomialMeanSquare, Finset.sum_subtype F (fun _ => Iff.rfl)]
    apply Finset.sum_congr rfl
    intro α hα
    rw [← heval α, Complex.normSq_eq_norm_sq]
  calc
    rationalAdditivePolynomialMeanSquare F S a = ∑ α : { α : ℚ // α ∈ F }, ‖inner ℂ (φ α) x‖ ^ 2 :=
      hmean
    _ ≤ R * ‖x‖ ^ 2 := hBessel
    _ = R * ∑ n ∈ S, ‖a n‖ ^ 2 := by rw [hnorm]

/--
Inputs: a finite set of rational frequencies, a finite polynomial index set, complex
coefficients, and a uniform Gram row bound.

Claim: the rational additive mean square is bounded by the row bound times the coefficient
norm-square sum.

Proof: represent each rational frequency by its conjugate-character vector and apply the dual
Gram-row estimate to the coefficient vector.

Role: provides the common-frequency-family interface needed to combine additive frequencies
coming from different moduli.
-/
theorem rationalAdditivePolynomialMeanSquare_le_of_gram_row_bound (F : Finset ℚ) (S : Finset ℕ)
    (a : ℕ → ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hrow :
      ∀ α : { α : ℚ // α ∈ F },
        ∑ β : { α : ℚ // α ∈ F },
            ‖∑ n ∈ S,
                rationalAdditiveCharacter α.val n * star (rationalAdditiveCharacter β.val n)‖ ≤
          R) :
    rationalAdditivePolynomialMeanSquare F S a ≤ R * ∑ n ∈ S, ‖a n‖ ^ 2 := by
  classical
  let I := { α : ℚ // α ∈ F }
  let φ : I → EuclideanSpace ℂ (↥S) := fun α => rationalFrequencyVector S α.val
  let b : EuclideanSpace ℂ (↥S) := WithLp.toLp 2 (fun n : ↥S => a n.val)
  have hrowVec : ∀ α : I, (∑ β : I, ‖inner ℂ (φ α) (φ β)‖) ≤ R := by
    intro α
    calc
      (∑ β : I, ‖inner ℂ (φ α) (φ β)‖) =
          ∑ β : I,
            ‖∑ n ∈ S,
                rationalAdditiveCharacter α.val n * star (rationalAdditiveCharacter β.val n)‖ :=
        by
        apply Finset.sum_congr rfl
        intro β hβ
        rw [show φ α = rationalFrequencyVector S α.val by rfl,
          show φ β = rationalFrequencyVector S β.val by rfl,
          rationalFrequencyVector_inner_eq_cross_sum]
      _ ≤ R := hrow α
  have heval (α : I) : inner ℂ (φ α) b = ∑ n ∈ S, a n * rationalAdditiveCharacter α.val n := by
    rw [PiLp.inner_apply]
    simp only [φ, rationalFrequencyVector, b, WithLp.ofLp_toLp, RCLike.inner_apply',
      starRingEnd_apply, star_star]
    rw [Finset.sum_subtype S (fun _ => Iff.rfl)]
    apply Finset.sum_congr rfl
    intro n hn
    exact mul_comm _ _
  have hbNorm : ‖b‖ ^ 2 = ∑ n ∈ S, ‖a n‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    dsimp only [b]
    exact Finset.sum_coe_sort S (fun n => ‖a n‖ ^ 2)
  exact
    rationalAdditivePolynomialMeanSquare_le_of_innerProduct_representation F S a φ b R hR hrowVec
      heval hbNorm

/--
Inputs: finite rational frequencies, coefficient and extended index sets, a window equal to one
on the coefficient set, and a uniform Gram row bound for the windowed frequency vectors.

Claim: the rational additive mean square is bounded by the Gram row bound times the coefficient
norm-square sum.

Proof: represent the polynomial by the windowed vectors and the zero-extended coefficient vector,
then apply the abstract inner-product estimate.

Role: connects a smooth extension of the coefficient interval to the rational large-sieve mean
square.
-/
theorem rationalAdditivePolynomialMeanSquare_le_of_window_gram_row_bound (F : Finset ℚ)
    (S T : Finset ℕ) (hST : S ⊆ T) (w : ℕ → ℝ) (hw : ∀ n ∈ S, w n = 1) (a : ℕ → ℂ) (R : ℝ)
    (hR : 0 ≤ R)
    (hrow :
      ∀ α : { α : ℚ // α ∈ F },
        ∑ β : { α : ℚ // α ∈ F },
            ‖inner ℂ (rationalWindowFrequencyVector T w α.val)
                (rationalWindowFrequencyVector T w β.val)‖ ≤
          R) :
    rationalAdditivePolynomialMeanSquare F S a ≤ R * ∑ n ∈ S, ‖a n‖ ^ 2 := by
  classical
  let I := { α : ℚ // α ∈ F }
  let φ : I → EuclideanSpace ℂ (↥T) := fun α => rationalWindowFrequencyVector T w α.val
  let x : EuclideanSpace ℂ (↥T) := rationalWindowCoefficientVector S T a
  have heval (α : I) : inner ℂ (φ α) x = ∑ n ∈ S, a n * rationalAdditiveCharacter α.val n := by
    rw [show φ α = rationalWindowFrequencyVector T w α.val by rfl,
      show x = rationalWindowCoefficientVector S T a by rfl,
      rationalWindowFrequencyVector_inner_eq_polynomial S T hST w hw α.val a]
  have hnorm : ‖x‖ ^ 2 = ∑ n ∈ S, ‖a n‖ ^ 2 := by
    rw [show x = rationalWindowCoefficientVector S T a by rfl,
      rationalWindowCoefficientVector_norm_sq_eq S T hST a]
  exact
    rationalAdditivePolynomialMeanSquare_le_of_innerProduct_representation F S a φ x R hR hrow heval
      hnorm

/--
Inputs: a modulus greater than one, a finite polynomial index set, complex coefficients, and a
uniform Gram row bound for the reduced unit frequencies.

Claim: the reduced additive mean square is bounded by the row bound times the coefficient
norm-square sum.

Proof: represent each reduced frequency by its conjugate character vector and apply the dual
Gram-row estimate to the coefficient vector.

Role: turns the abstract row-sum estimate into the additive large-sieve inequality for one
modulus.
-/
theorem reducedAdditivePolynomialMeanSquare_le_of_gram_row_bound {q : ℕ} [NeZero q] (hq : 1 < q)
    (S : Finset ℕ) (a : ℕ → ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hrow :
      ∀ x : { x : ZMod q // x ∈ reducedUnitFrequencySet q },
        ∑ y : { x : ZMod q // x ∈ reducedUnitFrequencySet q },
            ‖∑ n ∈ S,
                ZMod.stdAddChar (x.val * (n : ZMod q)) *
                  star (ZMod.stdAddChar (y.val * (n : ZMod q)))‖ ≤
          R) :
    reducedAdditivePolynomialMeanSquare q hq S a ≤ R * ∑ n ∈ S, ‖a n‖ ^ 2 := by
  classical
  let U := reducedUnitFrequencySet q
  let I := { x : ZMod q // x ∈ U }
  let φ : I → EuclideanSpace ℂ (↥S) := fun x => reducedUnitFrequencyVector S x.val
  let b : EuclideanSpace ℂ (↥S) := WithLp.toLp 2 (fun n : ↥S => a n.val)
  have hrowVec : ∀ x : I, (∑ y : I, ‖inner ℂ (φ x) (φ y)‖) ≤ R := by
    intro x
    calc
      (∑ y : I, ‖inner ℂ (φ x) (φ y)‖) =
          ∑ y : I,
            ‖∑ n ∈ S,
                ZMod.stdAddChar (x.val * (n : ZMod q)) *
                  star (ZMod.stdAddChar (y.val * (n : ZMod q)))‖ :=
        by
        apply Finset.sum_congr rfl
        intro y hy
        rw [show φ x = reducedUnitFrequencyVector S x.val by rfl,
          show φ y = reducedUnitFrequencyVector S y.val by rfl,
          reducedUnitFrequencyVector_inner_eq_cross_sum]
      _ ≤ R := hrow x
  have hBessel : (∑ x : I, ‖inner ℂ (φ x) b‖ ^ 2) ≤ R * ‖b‖ ^ 2 := by
    exact
      PseudoPrime.Analysis.FiniteGramBounds.sum_inner_product_norm_sq_le_of_gram_row_bound φ R hR
        hrowVec b
  have heval (x : I) : inner ℂ (φ x) b = ∑ n ∈ S, a n * ZMod.stdAddChar (x.val * (n : ZMod q)) := by
    rw [PiLp.inner_apply]
    simp only [φ, reducedUnitFrequencyVector, b, WithLp.ofLp_toLp, RCLike.inner_apply',
      starRingEnd_apply, star_star]
    rw [Finset.sum_subtype S (fun _ => Iff.rfl)]
    apply Finset.sum_congr rfl
    intro n hn
    exact mul_comm _ _
  have hbNorm : ‖b‖ ^ 2 = ∑ n ∈ S, ‖a n‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    dsimp only [b]
    exact Finset.sum_coe_sort S (fun n => ‖a n‖ ^ 2)
  have hmean : reducedAdditivePolynomialMeanSquare q hq S a = ∑ x : I, ‖inner ℂ (φ x) b‖ ^ 2 := by
    rw [reducedAdditivePolynomialMeanSquare]
    change (∑ x ∈ U, Complex.normSq (∑ n ∈ S, a n * ZMod.stdAddChar (x * (n : ZMod q)))) = _
    rw [Finset.sum_subtype U (fun _ => Iff.rfl)]
    apply Finset.sum_congr rfl
    intro x hx
    rw [← heval x, Complex.normSq_eq_norm_sq]
  calc
    reducedAdditivePolynomialMeanSquare q hq S a = ∑ x : I, ‖inner ℂ (φ x) b‖ ^ 2 := hmean
    _ ≤ R * ‖b‖ ^ 2 := hBessel
    _ = R * ∑ n ∈ S, ‖a n‖ ^ 2 := by rw [hbNorm]

/--
Inputs: positive denominators and two unequal cross-products of natural numerators.

Claim: the corresponding rational frequencies are separated by at least the reciprocal of the
product of their denominators.

Proof: clear denominators, use that a nonzero integer has absolute value at least one, and divide
by the positive denominator product.

Role: supplies the elementary spacing estimate for distinct reduced fractions in the additive
large-sieve argument.
-/
theorem rational_frequency_separation {q r x y : ℕ} (hq : 0 < q) (hr : 0 < r)
    (hxy : x * r ≠ y * q) : (1 : ℚ) / ((q : ℚ) * r) ≤ |(x : ℚ) / q - (y : ℚ) / r| := by
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  have hr0 : (r : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
  have hxyZ : (x : ℤ) * r ≠ (y : ℤ) * q := by exact_mod_cast hxy
  have hdiffZ : (x : ℤ) * r - (y : ℤ) * q ≠ 0 := sub_ne_zero.mpr hxyZ
  have hdiff : (1 : ℚ) ≤ |(x : ℚ) * r - (y : ℚ) * q| := by exact_mod_cast Int.one_le_abs hdiffZ
  have hmul : ((x : ℚ) / q - (y : ℚ) / r) * ((q : ℚ) * r) = (x : ℚ) * r - (y : ℚ) * q := by
    field_simp [hq0, hr0]
  have hqr : 0 < (q : ℚ) * r := mul_pos (by exact_mod_cast hq) (by exact_mod_cast hr)
  have hprod : (1 : ℚ) ≤ |(x : ℚ) / q - (y : ℚ) / r| * ((q : ℚ) * r) := by
    calc
      _ ≤ |(x : ℚ) * r - (y : ℚ) * q| := hdiff
      _ = |(x : ℚ) / q - (y : ℚ) / r| * ((q : ℚ) * r) := by rw [← abs_of_pos hqr, ← abs_mul, hmul]
  rw [div_le_iff₀ hqr]
  exact hprod

/--
Inputs: positive denominators, reduced natural-number numerators, and equality of the resulting
rational numbers.

Claim: two reduced representations have equal denominators and equal numerators.

Proof: clear denominators, use coprimality to show each denominator divides the other, then cancel
the common positive denominator.

Role: identifies reduced rational frequencies uniquely when combining additive sums across moduli.
-/
theorem rational_reduced_fraction_unique {q r x y : ℕ} (hq : 0 < q) (hr : 0 < r)
    (hx : Nat.Coprime x q) (hy : Nat.Coprime y r) (hxy : (x : ℚ) / q = (y : ℚ) / r) :
    q = r ∧ x = y := by
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  have hr0 : (r : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
  have hcross : x * r = y * q := by
    have h := (div_eq_div_iff hq0 hr0).mp hxy
    exact_mod_cast h
  have hqdiv : q ∣ r := by
    apply hx.symm.dvd_of_dvd_mul_left
    exact ⟨y, by simpa only [Nat.mul_comm] using hcross⟩
  have hrdiv : r ∣ q := by
    apply hy.symm.dvd_of_dvd_mul_left
    exact ⟨x, by simpa only [Nat.mul_comm] using hcross.symm⟩
  have hqr : q = r := Nat.dvd_antisymm hqdiv hrdiv
  subst r
  have hmul : x * q = y * q := hcross
  exact ⟨rfl, Nat.mul_right_cancel hq hmul⟩

/--
Inputs: positive denominators, numerators strictly between zero and their denominators, and
distinct cross-products.

Claim: the two fractions remain separated after identifying zero with one modulo the integers.

Proof: bound both the direct distance and its complement using nonzero integer cross-product
differences; the numerator in the complementary gap is also a positive integer.

Role: gives the circular spacing needed for an additive large sieve on reduced fractions.
-/
theorem rational_frequency_separation_circular {q r x y : ℕ} (hq : 0 < q) (hr : 0 < r) (hx : 0 < x)
    (hxq : x < q) (hy : 0 < y) (hyr : y < r) (hxy : x * r ≠ y * q) :
    min |(x : ℚ) / q - (y : ℚ) / r| (1 - |(x : ℚ) / q - (y : ℚ) / r|) ≥ 1 / ((q : ℚ) * r) := by
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  have hr0 : (r : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
  have hcrossZ : (x : ℤ) * r ≠ (y : ℤ) * q := by exact_mod_cast hxy
  have hdiffZ : (x : ℤ) * r - (y : ℤ) * q ≠ 0 := sub_ne_zero.mpr hcrossZ
  have hdiff : (1 : ℚ) ≤ |(x : ℚ) * r - (y : ℚ) * q| := by exact_mod_cast Int.one_le_abs hdiffZ
  have hmul : ((x : ℚ) / q - (y : ℚ) / r) * ((q : ℚ) * r) = (x : ℚ) * r - (y : ℚ) * q := by
    field_simp [hq0, hr0]
  have hqr : 0 < (q : ℚ) * r := mul_pos (by exact_mod_cast hq) (by exact_mod_cast hr)
  have hdirect : 1 / ((q : ℚ) * r) ≤ |(x : ℚ) / q - (y : ℚ) / r| := by
    have hprod : 1 ≤ |(x : ℚ) / q - (y : ℚ) / r| * ((q : ℚ) * r) := by
      calc
        _ ≤ |(x : ℚ) * r - (y : ℚ) * q| := hdiff
        _ = |(x : ℚ) / q - (y : ℚ) / r| * ((q : ℚ) * r) := by rw [← abs_of_pos hqr, ← abs_mul, hmul]
    rw [div_le_iff₀ hqr]
    exact hprod
  have hqz : (0 : ℤ) < q := by exact_mod_cast hq
  have hrz : (0 : ℤ) < r := by exact_mod_cast hr
  have hxz : (0 : ℤ) < x := by exact_mod_cast hx
  have hyz : (0 : ℤ) < y := by exact_mod_cast hy
  have hxqz : (x : ℤ) < q := by exact_mod_cast hxq
  have hyrz : (y : ℤ) < r := by exact_mod_cast hyr
  have hcrossBound : |(x : ℤ) * r - (y : ℤ) * q| < (q : ℤ) * r := by
    rw [abs_lt]
    constructor
    · nlinarith only [hxz, hxqz, hyz, hyrz, hqz, hrz]
    · nlinarith only [hxz, hxqz, hyz, hyrz, hqz, hrz]
  have hgapZ : 1 ≤ (q : ℤ) * r - |(x : ℤ) * r - (y : ℤ) * q| :=
    Int.add_one_le_iff.mpr (sub_pos.mpr hcrossBound)
  have hgap : (1 : ℚ) ≤ (q : ℚ) * r - |(x : ℚ) * r - (y : ℚ) * q| := by exact_mod_cast hgapZ
  have hcomp : 1 / ((q : ℚ) * r) ≤ 1 - |(x : ℚ) / q - (y : ℚ) / r| := by
    rw [div_le_iff₀ hqr]
    have hmulabs : |(x : ℚ) / q - (y : ℚ) / r| * ((q : ℚ) * r) = |(x : ℚ) * r - (y : ℚ) * q| := by
      rw [← abs_of_pos hqr, ← abs_mul, hmul]
    calc
      _ ≤ (q : ℚ) * r - |(x : ℚ) * r - (y : ℚ) * q| := hgap
      _ = (1 - |(x : ℚ) / q - (y : ℚ) / r|) * ((q : ℚ) * r) := by
        rw [← hmulabs]
        ring
  exact le_min hdirect hcomp

/--
Definition: represent the difference `β - α` in the centered unit interval by adding or subtracting
one when it lies outside `[-1/2, 1/2]`.

Inputs: two real representatives in `[0, 1)`.

Role: gives a signed coordinate for placing frequencies into positive and negative distance
shells.
-/
noncomputable def signedCircularDifference (α β : ℝ) : ℝ :=
  if β - α < -1 / 2 then β - α + 1 else if β - α ≤ 1 / 2 then β - α else β - α - 1

/--
Definition: record the integer shift used to move `β - α` into the centered unit interval.

Inputs: two real representatives.

Output: `1` for the lower branch, `0` for the middle branch, and `-1` for the upper branch.

Role: makes the signed difference's branch change explicit for proving uniqueness of its
representative.
-/
noncomputable def signedCircularShift (α β : ℝ) : ℤ :=
  if β - α < -1 / 2 then 1 else if β - α ≤ 1 / 2 then 0 else -1

/--
Inputs: two real representatives.

Claim: the signed difference is the ordinary difference plus its integer branch shift.

Proof: unfold both piecewise definitions and check each of their three branches.

Role: converts equality of signed differences into equality up to an integer shift.
-/
theorem signedCircularDifference_eq_difference_add_shift (α β : ℝ) :
    signedCircularDifference α β = (β - α) + (signedCircularShift α β : ℝ) := by
  unfold signedCircularDifference signedCircularShift
  split_ifs with hlow hhigh
  · norm_num only [Int.cast_one]
  · rw [Int.cast_zero, add_zero]
  · ring

/--
Inputs: a complex exponent and an integer multiple of the exponential period.

Claim: adding the integer period `2πi` does not change the complex exponential.

Proof: apply the integer-period form of `Complex.exp_periodic`.

Role: justifies replacing rational frequency differences by signed circular representatives.
-/
theorem complexExp_add_integer_period (z : ℂ) (k : ℤ) :
    Complex.exp (z + (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) = Complex.exp z := by
  have h := (Complex.exp_periodic.int_mul k).sub_eq (z + (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))
  simpa only [add_sub_cancel_right] using h.symm

/--
Inputs: a real frequency, an integer shift, and a natural index.

Claim: shifting a real frequency by an integer leaves its additive exponential unchanged.

Proof: the exponent change is the integer multiple `(k * n)` of the period `2πi`.

Role: transfers a character evaluated at a rational difference to its signed representative.
-/
theorem complexExp_real_frequency_int_shift (x : ℝ) (k : ℤ) (n : ℕ) :
    Complex.exp (Complex.I * ((2 * Real.pi * (x + (k : ℝ)) * n : ℝ) : ℂ)) =
      Complex.exp (Complex.I * ((2 * Real.pi * x * n : ℝ) : ℂ)) := by
  have harg :
    Complex.I * ((2 * Real.pi * (x + (k : ℝ)) * n : ℝ) : ℂ) =
      Complex.I * ((2 * Real.pi * x * n : ℝ) : ℂ) +
        ((k * n : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [harg]
  exact complexExp_add_integer_period _ _

/--
Inputs: a real frequency.

Claim: the complex exponential at its negative frequency is the conjugate at its positive
frequency.

Proof: conjugate the purely imaginary exponent and normalize the real negation.

Role: shows that the Fourier kernel norm is unchanged when the signed coordinate changes sign.
-/
theorem complexExp_real_frequency_neg (x : ℝ) :
    star (Complex.exp (Complex.I * ((2 * Real.pi * x : ℝ) : ℂ))) =
      Complex.exp (Complex.I * ((2 * Real.pi * (-x) : ℝ) : ℂ)) := by
  rw [show
      star (Complex.exp (Complex.I * ((2 * Real.pi * x : ℝ) : ℂ))) =
        (starRingEnd ℂ) (Complex.exp (Complex.I * ((2 * Real.pi * x : ℝ) : ℂ)))
      by rfl]
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

/--
Inputs: a finite index set, real coefficients, and a real frequency.

Claim: the Fourier sum at the negative frequency is the conjugate of the sum at the positive
frequency.

Proof: conjugation preserves real coefficients and distributes over finite sums and powers.

Role: transfers a row estimate proved for signed coordinates to the opposite Gram orientation.
-/
theorem realWeightedFourierSum_neg_eq_star (T : Finset ℕ) (w : ℕ → ℝ) (x : ℝ) :
    (∑ n ∈ T, (w n : ℂ) * Complex.exp (Complex.I * ((2 * Real.pi * (-x) : ℝ) : ℂ)) ^ n) =
      star (∑ n ∈ T, (w n : ℂ) * Complex.exp (Complex.I * ((2 * Real.pi * x : ℝ) : ℂ)) ^ n) := by
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [show
      star ((w n : ℂ) * Complex.exp (Complex.I * ((2 * Real.pi * x : ℝ) : ℂ)) ^ n) =
        (starRingEnd ℂ) ((w n : ℂ) * Complex.exp (Complex.I * ((2 * Real.pi * x : ℝ) : ℂ)) ^ n)
      by rfl]
  simp only [map_mul, Complex.conj_ofReal, map_pow]
  rw [show
      (starRingEnd ℂ) (Complex.exp (Complex.I * ((2 * Real.pi * x : ℝ) : ℂ))) =
        star (Complex.exp (Complex.I * ((2 * Real.pi * x : ℝ) : ℂ)))
      by rfl]
  rw [← complexExp_real_frequency_neg]

/--
Inputs: a finite index set, real coefficients, and a real frequency.

Claim: the norms of the Fourier sums at opposite frequencies are equal.

Proof: use conjugacy of the sums and invariance of the complex norm under conjugation.

Role: removes the orientation difference between a Gram cross term and its signed coordinate.
-/
theorem realWeightedFourierSum_norm_neg_eq (T : Finset ℕ) (w : ℕ → ℝ) (x : ℝ) :
    ‖∑ n ∈ T, (w n : ℂ) * Complex.exp (Complex.I * ((2 * Real.pi * (-x) : ℝ) : ℂ)) ^ n‖ =
      ‖∑ n ∈ T, (w n : ℂ) * Complex.exp (Complex.I * ((2 * Real.pi * x : ℝ) : ℂ)) ^ n‖ := by
  rw [realWeightedFourierSum_neg_eq_star]
  exact norm_star _

/--
Inputs: two rational frequencies and a natural index.

Claim: their character cross product can be evaluated at the negative signed circular difference.

Proof: express the signed difference as the ordinary difference plus an integer and apply
exponential periodicity.

Role: aligns rational-frequency Gram entries with the centered frequency coordinates in the
large-sieve row estimate.
-/
theorem rationalAdditiveCharacter_cross_eq_signed (α β : ℚ) (n : ℕ) :
    rationalAdditiveCharacter α n * star (rationalAdditiveCharacter β n) =
      Complex.exp
        (Complex.I *
          ((2 * Real.pi * (-signedCircularDifference (α : ℝ) (β : ℝ)) * n : ℝ) : ℂ)) := by
  rw [rationalAdditiveCharacter_cross_eq_exp_difference]
  have hshift := signedCircularDifference_eq_difference_add_shift (α : ℝ) (β : ℝ)
  have hdiff :
    (α : ℝ) - β =
      -signedCircularDifference (α : ℝ) (β : ℝ) + (signedCircularShift (α : ℝ) (β : ℝ) : ℝ) := by
    rw [hshift]
    ring
  rw [hdiff]
  exact
    complexExp_real_frequency_int_shift (-signedCircularDifference (α : ℝ) (β : ℝ))
      (signedCircularShift (α : ℝ) (β : ℝ)) n

/--
Inputs: a real representative.

Claim: its signed circular difference from itself is zero.

Proof: the middle branch of the centered representative definition applies to the zero difference.

Role: identifies the base frequency as the origin of its signed-coordinate family.
-/
theorem signedCircularDifference_self (α : ℝ) : signedCircularDifference α α = 0 := by
  unfold signedCircularDifference
  norm_num only [sub_self]
  simp only [ite_false, ite_true]

/--
Inputs: two real representatives.

Claim: the branch shift is one of `-1`, `0`, or `1`.

Proof: simplify the integer-valued branches of the definition.

Role: bounds the shift difference when proving injectivity on representatives in `[0, 1)`.
-/
theorem signedCircularShift_bounds (α β : ℝ) :
    -1 ≤ signedCircularShift α β ∧ signedCircularShift α β ≤ 1 := by
  unfold signedCircularShift
  split_ifs with hlow hhigh
  · norm_num only
    trivial
  · norm_num only
    trivial
  · norm_num only
    trivial

/--
Inputs: two real representatives in `[0, 1)`.

Claim: their signed circular difference lies in `[-1/2, 1/2]`.

Proof: split according to whether the ordinary difference is below, inside, or above the centered
unit interval, then use the representative bounds.

Role: provides the bounded coordinate range needed for the shell partition.
-/
theorem signedCircularDifference_bounds {α β : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) :
    -1 / 2 ≤ signedCircularDifference α β ∧ signedCircularDifference α β ≤ 1 / 2 := by
  unfold signedCircularDifference
  split_ifs with hlow hhigh
  · constructor <;> linarith only [hα0, hα1, hβ0, hβ1, hlow]
  · constructor <;> linarith only [hα0, hα1, hβ0, hβ1, hlow, hhigh]
  · constructor <;> linarith only [hα0, hα1, hβ0, hβ1, hlow, hhigh]

/--
Inputs: two real representatives in `[0, 1)`.

Claim: the signed difference has the same circular distance as the ordinary difference.

Proof: in the lower and upper branches, adding or subtracting one swaps the two entries of the
minimum; in the middle branch the difference is unchanged.

Role: transfers rational-frequency separation to the signed coordinate used by the shells.
-/
theorem signedCircularDifference_circularDistance {α β : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    min |signedCircularDifference α β| (1 - |signedCircularDifference α β|) =
      min |β - α| (1 - |β - α|) := by
  have hdlo : -1 < β - α := by linarith only [hα1, hβ0]
  have hdhi : β - α < 1 := by linarith only [hβ1, hα0]
  unfold signedCircularDifference
  split_ifs with hlow hhigh
  · have hneg : β - α < 0 := by linarith only [hlow]
    have hpos : 0 < β - α + 1 := by linarith only [hdlo]
    rw [abs_of_pos hpos, abs_of_neg hneg]
    rw [show 1 - (β - α + 1) = -(β - α) by ring, show 1 - (-(β - α)) = β - α + 1 by ring]
    exact min_comm _ _
  · rfl
  · have hpos : 0 < β - α := by linarith only [hhigh]
    have hneg : β - α - 1 < 0 := by linarith only [hdhi]
    rw [abs_of_neg hneg, abs_of_pos hpos]
    rw [show -(β - α - 1) = 1 - (β - α) by ring, show 1 - (1 - (β - α)) = β - α by ring]
    exact min_comm _ _

/--
Inputs: two real numbers in `[-1, 1]` whose difference is an integer translate.

Claim: adding an integer does not change their circular distance.

Proof: the integer shift is between `-2` and `2`; check the five possibilities, where adjacent
representatives exchange the two entries of the minimum and extreme representatives both have
zero circular distance.

Role: transfers circular separation between original frequencies to their signed coordinates.
-/
theorem circularDistance_eq_of_integer_translate {d e : ℝ} (k : ℤ) (hd : |d| ≤ 1) (he : |e| ≤ 1)
    (h : e = d + (k : ℝ)) : min |e| (1 - |e|) = min |d| (1 - |d|) := by
  have hdlo : -1 ≤ d := (abs_le.mp hd).1
  have hdhi : d ≤ 1 := (abs_le.mp hd).2
  have helo : -1 ≤ e := (abs_le.mp he).1
  have hehi : e ≤ 1 := (abs_le.mp he).2
  have hkR : (k : ℝ) = e - d := by linarith only [h]
  have hkloR : (-2 : ℝ) ≤ (k : ℝ) := by
    rw [hkR]; linarith only [hdhi, helo]
  have hkhiR : (k : ℝ) ≤ 2 := by
    rw [hkR]; linarith only [hdlo, hehi]
  have hklo : (-2 : ℤ) ≤ k := by exact_mod_cast hkloR
  have hkhi : k ≤ 2 := by exact_mod_cast hkhiR
  interval_cases k
  · norm_num only [Int.cast_neg] at h
    have hdval : d = 1 := by linarith only [hdhi, helo, h]
    rw [hdval] at h ⊢
    rw [h]
    norm_num only
  · norm_num only [Int.cast_neg] at h
    have hdnonneg : 0 ≤ d := by linarith only [helo, h]
    have henonpos : e ≤ 0 := by linarith only [hdhi, h]
    rw [abs_of_nonneg hdnonneg, abs_of_nonpos henonpos, h]
    rw [show -(d + -1) = 1 - d by ring, show 1 - (1 - d) = d by ring]
    exact min_comm _ _
  · rw [Int.cast_zero, add_zero] at h
    rw [h]
  · norm_num only [Int.cast_ofNat] at h
    have hdnonpos : d ≤ 0 := by linarith only [h, hehi]
    have henonneg : 0 ≤ e := by linarith only [hdlo, h]
    rw [abs_of_nonpos hdnonpos, abs_of_nonneg henonneg, h]
    rw [show 1 - (d + 1) = -d by ring, show 1 - (-d) = d + 1 by ring]
    exact min_comm _ _
  · norm_num only [Int.cast_ofNat] at h
    have hdval : d = -1 := by linarith only [hdlo, hehi, h]
    rw [hdval] at h ⊢
    rw [h]
    norm_num only

/--
Inputs: three real representatives in `[0, 1)`, with a common base frequency.

Claim: subtracting the same base and choosing centered representatives preserves the circular
distance between the other two frequencies.

Proof: express both signed differences using their integer branch shifts and apply
`circularDistance_eq_of_integer_translate`.

Role: establishes pairwise separation for the finite family of signed coordinates.
-/
theorem signedCircularDifference_pairwiseDistance {α β γ : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    min |signedCircularDifference α β - signedCircularDifference α γ|
        (1 - |signedCircularDifference α β - signedCircularDifference α γ|) =
      min |β - γ| (1 - |β - γ|) := by
  have hβcoord := signedCircularDifference_bounds hα0 hα1 hβ0 hβ1
  have hγcoord := signedCircularDifference_bounds hα0 hα1 hγ0 hγ1
  have hdiff :
    signedCircularDifference α β - signedCircularDifference α γ =
      (β - γ) + (signedCircularShift α β - signedCircularShift α γ : ℝ) := by
    rw [signedCircularDifference_eq_difference_add_shift α β,
      signedCircularDifference_eq_difference_add_shift α γ]
    ring
  have hdiff' :
    signedCircularDifference α β - signedCircularDifference α γ =
      (β - γ) + ((signedCircularShift α β - signedCircularShift α γ : ℤ) : ℝ) := by
    calc
      _ = (β - γ) + ((signedCircularShift α β : ℤ) - signedCircularShift α γ) := hdiff
      _ = _ := by rw [Int.cast_sub]
  have hβγ : |β - γ| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith only [hβ0, hβ1, hγ0, hγ1]
  have hsigned : |signedCircularDifference α β - signedCircularDifference α γ| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith only [hβcoord.1, hβcoord.2, hγcoord.1, hγcoord.2]
  exact
    circularDistance_eq_of_integer_translate (signedCircularShift α β - signedCircularShift α γ) hβγ
      hsigned hdiff'

/--
Inputs: two representatives `β` and `γ` in `[0, 1)`, with a common base `α`.

Claim: equal signed circular differences imply equal representatives.

Proof: express each difference using its integer shift; the difference of the shifts lies between
`-2` and `2`, while `β - γ` lies strictly between `-1` and `1`, forcing the shifts to agree.

Role: permits counting the finite image of frequencies in signed distance shells without losing
elements to collisions.
-/
theorem signedCircularDifference_injective {α β γ : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (h : signedCircularDifference α β = signedCircularDifference α γ) : β = γ := by
  let kb := signedCircularShift α β
  let kg := signedCircularShift α γ
  have hkb := signedCircularShift_bounds α β
  have hkg := signedCircularShift_bounds α γ
  have hshift : β - γ = (kg - kb : ℤ) := by
    dsimp only [kb, kg]
    rw [signedCircularDifference_eq_difference_add_shift α β,
      signedCircularDifference_eq_difference_add_shift α γ] at h
    exact_mod_cast
      (by linarith only [h] : (β - γ : ℝ) = (signedCircularShift α γ : ℝ) - signedCircularShift α β)
  let k : ℤ := kg - kb
  have hklo : -2 ≤ k := by
    dsimp only [k]
    linarith only [hkg.1, hkb.2]
  have hkhi : k ≤ 2 := by
    dsimp only [k]
    linarith only [hkg.2, hkb.1]
  have hβγlo : -1 < β - γ := by linarith only [hβ0, hγ1]
  have hβγhi : β - γ < 1 := by linarith only [hβ1, hγ0]
  have hshift' : β - γ = (k : ℝ) := by simpa only [k] using hshift
  interval_cases k <;> norm_num only [Int.cast_ofNat, Int.cast_neg] at hshift' <;>
    linarith only [hβγlo, hβγhi, hshift']

/--
Type: index a reduced rational frequency by a denominator `q` with `1 < q ≤ Q` and a numerator
`x` coprime to `q`, with `0 ≤ x < q`.

Invariant: `Fin (Q + 1)` bounds the denominator, and the second subtype enforces reducedness.

Role: provides a finite index type for all reduced frequencies used in the denominator-bounded
additive large sieve.
-/
abbrev ReducedUnitFrequencyIndex (Q : ℕ) :=
  Σ q : { q : Fin (Q + 1) // 1 < q.val }, { x : Fin q.val // Nat.Coprime x.val q.val }

/--
Definition: the finite set of all reduced frequency indices with denominator at most `Q`.

Inputs: a natural denominator cutoff.

Output: every index in `ReducedUnitFrequencyIndex Q`.

Role: supplies the complete finite frequency family for Gram row estimates.
-/
noncomputable def reducedUnitFrequencyIndexSet (Q : ℕ) : Finset (ReducedUnitFrequencyIndex Q) :=
  Finset.univ

/--
Definition: map a reduced frequency index to its rational value, viewed as a real number.

Inputs: a frequency index whose denominator is greater than one.

Output: the ratio of its canonical numerator and denominator.

Role: supplies real coordinates for circular separation and the signed shell partition.
-/
noncomputable def reducedUnitFrequencyCoordinate {Q : ℕ} (f : ReducedUnitFrequencyIndex Q) : ℝ :=
  (f.2.1.val : ℝ) / f.1.1.val

/--
Definition: the reduced rational frequency represented by an indexed numerator and denominator.

Inputs: a member of `ReducedUnitFrequencyIndex Q`.

Output: the numerator divided by the denominator in `ℚ`.

Role: provides the exact rational frequency used by `rationalAdditiveCharacter`.
-/
noncomputable def reducedUnitFrequencyRational {Q : ℕ} (f : ReducedUnitFrequencyIndex Q) : ℚ :=
  (f.2.1.val : ℚ) / f.1.1.val

/--
Claim: casting the rational frequency to `ℝ` gives its real coordinate.

Proof: cast the numerator and denominator through rational division.

Role: transfers real-coordinate separation results to the rational-frequency index family.
-/
theorem reducedUnitFrequencyRational_cast {Q : ℕ} (f : ReducedUnitFrequencyIndex Q) :
    (reducedUnitFrequencyRational f : ℝ) = reducedUnitFrequencyCoordinate f := by
  simp only [reducedUnitFrequencyRational, reducedUnitFrequencyCoordinate, Rat.cast_div,
    Rat.cast_natCast]

/--
Inputs: an index from `ReducedUnitFrequencyIndex Q`.

Claim: its real frequency coordinate lies in `[0, 1)`.

Proof: the numerator is a natural number below the positive denominator; divide by that
denominator in the real numbers.

Role: provides the representative bounds required by the signed-coordinate lemmas.
-/
theorem reducedUnitFrequencyCoordinate_bounds {Q : ℕ} (f : ReducedUnitFrequencyIndex Q) :
    0 ≤ reducedUnitFrequencyCoordinate f ∧ reducedUnitFrequencyCoordinate f < 1 := by
  obtain ⟨⟨q, hq⟩, ⟨x, hx⟩⟩ := f
  dsimp only [reducedUnitFrequencyCoordinate]
  have hqpos : 0 < (q.val : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hq
  have hxnonneg : 0 ≤ (x.val : ℝ) := by exact_mod_cast Nat.zero_le x.val
  have hxlt : (x.val : ℝ) < q.val := by exact_mod_cast x.is_lt
  exact ⟨div_nonneg hxnonneg hqpos.le, (div_lt_one hqpos).2 hxlt⟩

/--
Inputs: two indices from `ReducedUnitFrequencyIndex Q` with equal real coordinates.

Claim: the indices are equal.

Proof: cast the coordinate equality to a rational equality, apply uniqueness of reduced
fractions, then use extensionality of the denominator and numerator subtypes.

Role: ensures that passing from the finite index family to its rational-coordinate image loses no
frequencies.
-/
theorem reducedUnitFrequencyCoordinate_injective {Q : ℕ} :
    Function.Injective (reducedUnitFrequencyCoordinate (Q := Q)) := by
  intro f g hfg
  obtain ⟨⟨q, hq⟩, ⟨x, hx⟩⟩ := f
  obtain ⟨⟨r, hr⟩, ⟨y, hy⟩⟩ := g
  change (x.val : ℝ) / q.val = (y.val : ℝ) / r.val at hfg
  have hq0 : (q.val : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt hq))
  have hr0 : (r.val : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt hr))
  have hcrossR := (div_eq_div_iff hq0 hr0).mp hfg
  have hcross : x.val * r.val = y.val * q.val := by exact_mod_cast hcrossR
  have hq0Q : (q.val : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt hq))
  have hr0Q : (r.val : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt hr))
  have hcrossQ : (x.val : ℚ) * r.val = (y.val : ℚ) * q.val := by exact_mod_cast hcross
  have hrat := (div_eq_div_iff hq0Q hr0Q).2 hcrossQ
  obtain ⟨hqr, hxy⟩ :=
    rational_reduced_fraction_unique (Nat.zero_lt_of_lt hq) (Nat.zero_lt_of_lt hr) hx hy hrat
  have hqrFin : q = r := Fin.ext hqr
  subst r
  have hxyFin : x = y := Fin.ext hxy
  subst y
  rfl

/--
Claim: distinct indices define distinct rational frequencies.

Proof: cast a rational-frequency equality to `ℝ` and use injectivity of the real coordinate.

Role: allows finite sums over indexed frequencies to be transported to their rational image.
-/
theorem reducedUnitFrequencyRational_injective {Q : ℕ} :
    Function.Injective (reducedUnitFrequencyRational (Q := Q)) := by
  intro f g h
  apply reducedUnitFrequencyCoordinate_injective
  calc
    reducedUnitFrequencyCoordinate f = (reducedUnitFrequencyRational f : ℝ) :=
      (reducedUnitFrequencyRational_cast f).symm
    _ = (reducedUnitFrequencyRational g : ℝ) := congrArg Rat.cast h
    _ = reducedUnitFrequencyCoordinate g := reducedUnitFrequencyRational_cast g

/--
Definition: locate a reduced frequency relative to a fixed base in the centered circular
coordinate.

Inputs: a real base frequency and a reduced frequency index.

Output: its signed circular difference from the base.

Role: assigns each finite frequency index to a signed distance shell.
-/
noncomputable def reducedUnitFrequencySignedCoordinate {Q : ℕ} (α : ℝ)
    (f : ReducedUnitFrequencyIndex Q) : ℝ :=
  signedCircularDifference α (reducedUnitFrequencyCoordinate f)

/--
Inputs: a denominator cutoff, two indexed reduced frequencies, and an interval length.

Claim: the triangle-window Gram entry has the same norm as its Fourier kernel at the signed
circular coordinate.

Proof: rewrite the character cross product by exponential periodicity, then use conjugate symmetry
to change the negative signed coordinate to the positive one.

Role: transfers the real signed-coordinate row bound to the rational windowed frequency vectors.
-/
theorem reducedUnitFrequencyWindowGramTerm_norm_eq_signed_kernel_norm {Q : ℕ}
    (f₀ f : ReducedUnitFrequencyIndex Q) (N : ℕ) :
    ‖inner ℂ
          (rationalWindowFrequencyVector (Finset.range (N + 2 * (Q * Q) - 1))
            (triangleOverlapWindow N (Q * Q)) (reducedUnitFrequencyRational f₀))
          (rationalWindowFrequencyVector (Finset.range (N + 2 * (Q * Q) - 1))
            (triangleOverlapWindow N (Q * Q)) (reducedUnitFrequencyRational f))‖ =
      ‖∑ n ∈ Finset.range (N + 2 * (Q * Q) - 1),
          (triangleOverlapWindowWeight N (Q * Q) n : ℂ) *
            Complex.exp
                (Complex.I *
                  ((2 * Real.pi *
                        reducedUnitFrequencySignedCoordinate (reducedUnitFrequencyCoordinate f₀) f :
                      ℝ) :
                    ℂ)) ^
              n‖ := by
  have hsum :
    inner ℂ
        (rationalWindowFrequencyVector (Finset.range (N + 2 * (Q * Q) - 1))
          (triangleOverlapWindow N (Q * Q)) (reducedUnitFrequencyRational f₀))
        (rationalWindowFrequencyVector (Finset.range (N + 2 * (Q * Q) - 1))
          (triangleOverlapWindow N (Q * Q)) (reducedUnitFrequencyRational f)) =
      ∑ n ∈ Finset.range (N + 2 * (Q * Q) - 1),
        (triangleOverlapWindowWeight N (Q * Q) n : ℂ) *
          Complex.exp
              (Complex.I *
                ((2 * Real.pi *
                      (-reducedUnitFrequencySignedCoordinate (reducedUnitFrequencyCoordinate f₀)
                          f) :
                    ℝ) :
                  ℂ)) ^
            n := by
    rw [rationalWindowFrequencyVector_inner_eq_weighted_cross_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [mul_assoc, ← Complex.ofReal_pow, triangleOverlapWindow_sq_eq_weight]
    rw [rationalAdditiveCharacter_cross_eq_signed]
    rw [reducedUnitFrequencyRational_cast f₀, reducedUnitFrequencyRational_cast f]
    rw [reducedUnitFrequencySignedCoordinate]
    congr 1
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring_nf
  calc
    _ =
        ‖∑ n ∈ Finset.range (N + 2 * (Q * Q) - 1),
            (triangleOverlapWindowWeight N (Q * Q) n : ℂ) *
              Complex.exp
                  (Complex.I *
                    ((2 * Real.pi *
                          (-reducedUnitFrequencySignedCoordinate (reducedUnitFrequencyCoordinate f₀)
                              f) :
                        ℝ) :
                      ℂ)) ^
                n‖ :=
      congrArg norm hsum
    _ = _ :=
      realWeightedFourierSum_norm_neg_eq (Finset.range (N + 2 * (Q * Q) - 1))
        (triangleOverlapWindowWeight N (Q * Q))
        (reducedUnitFrequencySignedCoordinate (reducedUnitFrequencyCoordinate f₀) f)

/--
Inputs: two distinct indices from `ReducedUnitFrequencyIndex Q` and a base in `[0, 1)`.

Claim: their signed coordinates have circular distance at least `1 / Q^2`.

Proof: distinct reduced indices give distinct rational frequencies; apply the rational spacing
bound and transfer it to the pair of signed coordinates.

Role: establishes the separation hypothesis for the full finite signed-frequency family.
-/
theorem reducedUnitFrequencySignedCoordinate_pairwiseSeparation {Q : ℕ} (α : ℝ) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (f g : ReducedUnitFrequencyIndex Q) (hfg : f ≠ g) :
    1 / ((Q : ℝ) * Q) ≤
      min |reducedUnitFrequencySignedCoordinate α f - reducedUnitFrequencySignedCoordinate α g|
        (1 -
          |reducedUnitFrequencySignedCoordinate α f -
              reducedUnitFrequencySignedCoordinate α g|) := by
  have hxrange := reducedUnitFrequencyCoordinate_bounds f
  have hyrange := reducedUnitFrequencyCoordinate_bounds g
  have hpair :=
    signedCircularDifference_pairwiseDistance hα0 hα1 hxrange.1 hxrange.2 hyrange.1 hyrange.2
  rw [show
      reducedUnitFrequencySignedCoordinate α f =
        signedCircularDifference α (reducedUnitFrequencyCoordinate f)
      by rfl,
    show
      reducedUnitFrequencySignedCoordinate α g =
        signedCircularDifference α (reducedUnitFrequencyCoordinate g)
      by rfl,
    hpair]
  have hcoordNe : reducedUnitFrequencyCoordinate f ≠ reducedUnitFrequencyCoordinate g := by
    intro hcoord
    exact hfg (reducedUnitFrequencyCoordinate_injective hcoord)
  obtain ⟨⟨q, hq⟩, ⟨x, hx⟩⟩ := f
  obtain ⟨⟨r, hr⟩, ⟨y, hy⟩⟩ := g
  change (x.val : ℝ) / q.val ≠ (y.val : ℝ) / r.val at hcoordNe
  have hratNe : (x.val : ℚ) / q.val ≠ (y.val : ℚ) / r.val := by
    intro hrat
    apply hcoordNe
    have hcast := congrArg (fun z : ℚ => (z : ℝ)) hrat
    simpa only [Rat.cast_div, Rat.cast_natCast] using hcast
  have hq0 : (q.val : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt hq))
  have hr0 : (r.val : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt hr))
  have hcross : x.val * r.val ≠ y.val * q.val := by
    intro hcross
    apply hratNe
    exact (div_eq_div_iff hq0 hr0).2 (by exact_mod_cast hcross)
  have hxne : x.val ≠ 0 := by
    intro hxzero
    have hcop : Nat.Coprime 0 q.val := by simpa only [hxzero] using hx
    have hqone : q.val = 1 := (Nat.coprime_zero_left q.val).mp hcop
    exact (Nat.ne_of_gt hq) hqone
  have hyne : y.val ≠ 0 := by
    intro hyzero
    have hcop : Nat.Coprime 0 r.val := by simpa only [hyzero] using hy
    have hrone : r.val = 1 := (Nat.coprime_zero_left r.val).mp hcop
    exact (Nat.ne_of_gt hr) hrone
  have hqQ : q.val ≤ Q := Nat.lt_succ_iff.mp q.is_lt
  have hrQ : r.val ≤ Q := Nat.lt_succ_iff.mp r.is_lt
  have hqpos := Nat.zero_lt_of_lt hq
  have hrpos := Nat.zero_lt_of_lt hr
  have hspacingqr :=
    rational_frequency_separation_circular hqpos hrpos (Nat.pos_of_ne_zero hxne) x.is_lt
      (Nat.pos_of_ne_zero hyne) y.is_lt hcross
  have hQpos : 0 < (Q : ℚ) * Q := by
    have hQ : 0 < Q := hqpos.trans_le hqQ
    exact mul_pos (by exact_mod_cast hQ) (by exact_mod_cast hQ)
  have hqrpos : 0 < (q.val : ℚ) * r.val :=
    mul_pos (by exact_mod_cast hqpos) (by exact_mod_cast hrpos)
  have hprod : (q.val : ℚ) * r.val ≤ (Q : ℚ) * Q := by exact_mod_cast Nat.mul_le_mul hqQ hrQ
  have hscale : 1 / ((Q : ℚ) * Q) ≤ 1 / ((q.val : ℚ) * r.val) := by
    apply (div_le_div_iff₀ hQpos hqrpos).2
    simpa only [one_mul] using hprod
  have hspacingQ := le_trans hscale hspacingqr
  have hspacingR :
    1 / ((Q : ℝ) * Q) ≤
      min |(x.val : ℝ) / q.val - (y.val : ℝ) / r.val|
        (1 - |(x.val : ℝ) / q.val - (y.val : ℝ) / r.val|) := by
    simpa only [Rat.cast_div, Rat.cast_mul, Rat.cast_one, Rat.cast_min, Rat.cast_abs, Rat.cast_sub,
      Rat.cast_natCast] using (Rat.cast_le (K := ℝ)).2 hspacingQ
  exact hspacingR

/--
Definition: the finite set of signed circular coordinates of every reduced frequency with
denominator at most `Q`, measured from a fixed base frequency.

Inputs: a denominator cutoff and a real base frequency.

Output: the image of `reducedUnitFrequencyIndexSet Q` under the signed-coordinate map.

Role: provides the finite point set to partition into circular-distance shells.
-/
noncomputable def reducedUnitFrequencySignedCoordinates {Q : ℕ} (α : ℝ) : Finset ℝ :=
  (reducedUnitFrequencyIndexSet Q).image (reducedUnitFrequencySignedCoordinate α)

/--
Inputs: a reduced frequency index.

Claim: when measured from its own coordinate, the index contributes zero to the signed-coordinate
family.

Proof: the index belongs to the complete finite index set and its signed difference from itself is
zero.

Role: supplies the origin against which every off-diagonal frequency in a Gram row is separated.
-/
theorem reducedUnitFrequencySignedCoordinates_zero_mem {Q : ℕ} (f : ReducedUnitFrequencyIndex Q) :
    0 ∈ reducedUnitFrequencySignedCoordinates (Q := Q) (reducedUnitFrequencyCoordinate f) := by
  apply Finset.mem_image.mpr
  refine ⟨f, Finset.mem_univ _, ?_⟩
  exact signedCircularDifference_self (reducedUnitFrequencyCoordinate f)

/--
Inputs: two distinct values in the signed-coordinate set for cutoff `Q`, and a base in `[0, 1)`.

Claim: the values have circular distance at least `1 / Q^2`.

Proof: lift the two image memberships to frequency indices and apply their pairwise separation.

Role: supplies the spacing bound needed to count the points in each shell.
-/
theorem reducedUnitFrequencySignedCoordinates_separated {Q : ℕ} (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (u v : ℝ) (hu : u ∈ reducedUnitFrequencySignedCoordinates (Q := Q) α)
    (hv : v ∈ reducedUnitFrequencySignedCoordinates (Q := Q) α) (huv : u ≠ v) :
    1 / ((Q : ℝ) * Q) ≤ min |u - v| (1 - |u - v|) := by
  classical
  obtain ⟨f, hf, hfu⟩ := Finset.mem_image.mp hu
  obtain ⟨g, hg, hgv⟩ := Finset.mem_image.mp hv
  have hfg : f ≠ g := by
    intro hfg
    apply huv
    calc
      u = reducedUnitFrequencySignedCoordinate α f := hfu.symm
      _ = reducedUnitFrequencySignedCoordinate α g := by rw [hfg]
      _ = v := hgv
  rw [← hfu, ← hgv]
  exact reducedUnitFrequencySignedCoordinate_pairwiseSeparation α hα0 hα1 f g hfg

/--
Inputs: a member of a signed-coordinate family and a base in `[0, 1)`.

Claim: the member lies in the centered interval `[-1/2, 1/2]`.

Proof: lift membership through the finite image and apply the signed-difference range bound.

Role: ensures that the shell radius controls both sides of the circular distance.
-/
theorem reducedUnitFrequencySignedCoordinates_mem_bounds {Q : ℕ} (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (x : ℝ) (hx : x ∈ reducedUnitFrequencySignedCoordinates (Q := Q) α) :
    -(1 / 2 : ℝ) ≤ x ∧ x ≤ 1 / 2 := by
  obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp hx
  have h :=
    signedCircularDifference_bounds hα0 hα1 (reducedUnitFrequencyCoordinate_bounds f).1
      (reducedUnitFrequencyCoordinate_bounds f).2
  simpa only [reducedUnitFrequencySignedCoordinate] using
    (show
      -(1 / 2 : ℝ) ≤ signedCircularDifference α (reducedUnitFrequencyCoordinate f) ∧
        signedCircularDifference α (reducedUnitFrequencyCoordinate f) ≤ 1 / 2
      from ⟨by linarith only [h.1], h.2⟩)

/--
Inputs: a positive denominator cutoff and a member of its centered signed-frequency family.

Claim: the floor shell index at width `1 / Q²` is at most `Q²`.

Proof: the centered representative has absolute value at most one, so dividing by the shell width
gives a value at most `Q²`; apply the natural-floor bound.

Role: gives a finite range containing every shell needed for the reduced-frequency Gram row.
-/
theorem reducedUnitFrequencySignedCoordinates_floor_shell_index_le {Q : ℕ} (hQ : 0 < Q) (α : ℝ)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (x : ℝ)
    (hx : x ∈ reducedUnitFrequencySignedCoordinates (Q := Q) α) :
    ⌊|x| / (1 / ((Q : ℝ) * Q))⌋₊ ≤ Q * Q := by
  have hQR : 0 < (Q : ℝ) := by exact_mod_cast hQ
  have hQsq : 0 < (Q : ℝ) * Q := mul_pos hQR hQR
  have hδ : 0 < 1 / ((Q : ℝ) * Q) := div_pos (by norm_num only) hQsq
  have hproduct : ((Q * Q : ℕ) : ℝ) * (1 / ((Q : ℝ) * Q)) = 1 := by
    rw [Nat.cast_mul, one_div]
    exact mul_inv_cancel₀ (ne_of_gt hQsq)
  have hcenter := reducedUnitFrequencySignedCoordinates_mem_bounds α hα0 hα1 x hx
  have habs : |x| ≤ 1 := by
    rw [abs_le]
    exact ⟨by linarith only [hcenter.1], by linarith only [hcenter.2]⟩
  have hratio : |x| / (1 / ((Q : ℝ) * Q)) ≤ ((Q * Q : ℕ) : ℝ) := by
    apply (div_le_iff₀ hδ).2
    rw [hproduct]
    exact habs
  exact Nat.floor_le_of_le hratio

/--
Inputs: a base frequency index and a nonzero member of its signed-coordinate family.

Claim: the member is separated from zero by the circular spacing `1 / Q²`.

Proof: zero is the signed coordinate of the base index; apply pairwise separation to zero and the
given member.

Role: supplies the base spacing needed to bound every off-diagonal term in a Gram row.
-/
theorem reducedUnitFrequencySignedCoordinates_separated_from_zero {Q : ℕ}
    (f₀ : ReducedUnitFrequencyIndex Q) (x : ℝ)
    (hx : x ∈ reducedUnitFrequencySignedCoordinates (Q := Q) (reducedUnitFrequencyCoordinate f₀))
    (hx0 : x ≠ 0) : 1 / ((Q : ℝ) * Q) ≤ min |x| (1 - |x|) := by
  have hf₀ := reducedUnitFrequencyCoordinate_bounds f₀
  simpa only [zero_sub, abs_neg] using
    reducedUnitFrequencySignedCoordinates_separated (Q := Q) (reducedUnitFrequencyCoordinate f₀)
      hf₀.1 hf₀.2 0 x (reducedUnitFrequencySignedCoordinates_zero_mem f₀) hx (Ne.symm hx0)

/--
Inputs: a signed-coordinate family for cutoff `Q` covered by two half-open intervals of width
`1 / Q^2`, and a base in `[0, 1)`.

Claim: at most two distinct signed coordinates lie in the cover.

Proof: use the pairwise circular spacing of the family and the generic two-interval counting
lemma.

Role: bounds the population of an individual positive-and-negative distance shell.
-/
theorem reducedUnitFrequencySignedCoordinates_card_le_two_of_two_intervals {Q : ℕ} (α a b : ℝ)
    (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hcover :
      ∀ x ∈ reducedUnitFrequencySignedCoordinates (Q := Q) α,
        (a ≤ x ∧ x < a + 1 / ((Q : ℝ) * Q)) ∨ (b ≤ x ∧ x < b + 1 / ((Q : ℝ) * Q))) :
    (reducedUnitFrequencySignedCoordinates (Q := Q) α).card ≤ 2 := by
  apply
    PseudoPrime.Analysis.FiniteSeparatedSetBounds.finset_card_le_two_of_circular_separation
      (reducedUnitFrequencySignedCoordinates (Q := Q) α) a b (1 / ((Q : ℝ) * Q))
  · intro x hx y hy hxy
    exact reducedUnitFrequencySignedCoordinates_separated (Q := Q) α hα0 hα1 x y hx hy hxy
  · exact hcover

/--
Definition: retain the points of `S` in the positive interval `[kδ, (k+1)δ)` or its negative
counterpart `(-(k+1)δ, -kδ]`.

Inputs: a finite set of real points, a shell width, and a natural shell index.

Role: partitions signed circular coordinates into positive and negative distance shells.
-/
noncomputable def signedDistanceShell (S : Finset ℝ) (δ : ℝ) (k : ℕ) : Finset ℝ :=
  S.filter
    (fun x =>
      ((k : ℝ) * δ ≤ x ∧ x < ((k : ℝ) + 1) * δ) ∨ (-(((k : ℝ) + 1) * δ) < x ∧ x ≤ -((k : ℝ) * δ)))

/--
Inputs: a finite set whose distinct points have circular distance at least `δ`, a positive shell
width, and a natural shell index.

Claim: the signed distance shell contains at most two points.

Proof: its positive and negative parts occupy two half-open intervals of width `δ`; apply the
two-interval cardinal bound.

Role: controls the number of reduced frequencies contributing to each shell.
-/
theorem signedDistanceShell_card_le_two (S : Finset ℝ) (δ : ℝ) (k : ℕ)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ min |x - y| (1 - |x - y|)) :
    (signedDistanceShell S δ k).card ≤ 2 := by
  apply
    PseudoPrime.Analysis.FiniteSeparatedSetBounds.finset_card_le_two_of_mixed_interval_cover
      (signedDistanceShell S δ k) ((k : ℝ) * δ) (-(((k : ℝ) + 1) * δ)) δ
  · intro x hx y hy hxy
    exact
      le_trans (hsep x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1 hxy)
        (min_le_left _ _)
  · intro x hx
    rcases Finset.mem_filter.mp hx with ⟨_, hshell⟩
    rcases hshell with hpos | hneg
    · refine Or.inl ⟨hpos.1, ?_⟩
      calc
        x < ((k : ℝ) + 1) * δ := hpos.2
        _ = (k : ℝ) * δ + δ := by ring
    · refine Or.inr ⟨hneg.1, ?_⟩
      calc
        x ≤ -((k : ℝ) * δ) := hneg.2
        _ = -(((k : ℝ) + 1) * δ) + δ := by ring

/--
Inputs: a signed-coordinate family of reduced frequencies, a base in `[0, 1)`, and a shell index.

Claim: at most two reduced frequencies lie in each positive-and-negative shell of width `1 / Q²`.

Proof: every pair of distinct signed coordinates is separated by at least `1 / Q²`; apply the
generic signed-shell cardinal bound.

Role: provides the shell population bound used in the reduced-frequency Gram row estimate.
-/
theorem reducedUnitFrequencySignedCoordinates_shell_card_le_two {Q : ℕ} (α : ℝ) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (k : ℕ) :
    (signedDistanceShell (reducedUnitFrequencySignedCoordinates (Q := Q) α) (1 / ((Q : ℝ) * Q))
          k).card ≤
      2 := by
  apply signedDistanceShell_card_le_two
  intro x hx y hy hxy
  exact reducedUnitFrequencySignedCoordinates_separated (Q := Q) α hα0 hα1 x y hx hy hxy

/--
Inputs: a point in a signed distance shell of positive width `δ` and a shell index `k`.

Claim: the point's absolute value is at least `k * δ`.

Proof: use the lower endpoint of the positive interval or negate the upper endpoint of the
negative interval.

Role: converts shell membership into a lower bound on the phase distance for the kernel estimate.
-/
theorem signedDistanceShell_abs_ge {S : Finset ℝ} {δ : ℝ} {k : ℕ} {x : ℝ} (hδ : 0 < δ)
    (hx : x ∈ signedDistanceShell S δ k) : (k : ℝ) * δ ≤ |x| := by
  have hk : 0 ≤ (k : ℝ) * δ := mul_nonneg (by exact_mod_cast Nat.zero_le k) hδ.le
  rcases Finset.mem_filter.mp hx with ⟨_, hshell⟩
  rcases hshell with hpos | hneg
  · calc
      (k : ℝ) * δ ≤ x := hpos.1
      _ = |x| := (abs_of_nonneg (le_trans hk hpos.1)).symm
  · have hxnonpos : x ≤ 0 := le_trans hneg.2 (neg_nonpos.mpr hk)
    calc
      (k : ℝ) * δ ≤ -x := by simpa only [neg_neg] using neg_le_neg hneg.2
      _ = |x| := (abs_of_nonpos hxnonpos).symm

/--
Inputs: a point in a signed distance shell of positive width `δ` and a shell index `k`.

Claim: the point's absolute value is strictly less than `(k + 1) * δ`.

Proof: use the upper endpoint of the positive interval or negate the open lower endpoint of the
negative interval.

Role: identifies the exact floor index of every shell member.
-/
theorem signedDistanceShell_abs_lt_succ {S : Finset ℝ} {δ : ℝ} {k : ℕ} {x : ℝ} (hδ : 0 < δ)
    (hx : x ∈ signedDistanceShell S δ k) : |x| < ((k : ℝ) + 1) * δ := by
  have hk : 0 ≤ (k : ℝ) * δ := mul_nonneg (by exact_mod_cast Nat.zero_le k) hδ.le
  rcases Finset.mem_filter.mp hx with ⟨_, hshell⟩
  rcases hshell with hpos | hneg
  · have hxnonneg : 0 ≤ x := le_trans hk hpos.1
    rw [abs_of_nonneg hxnonneg]
    exact hpos.2
  · have hxnonpos : x ≤ 0 := le_trans hneg.2 (neg_nonpos.mpr hk)
    rw [abs_of_nonpos hxnonpos]
    linarith only [hneg.1]

/--
Inputs: a point of a finite real set and a positive shell width.

Claim: the point belongs to the shell indexed by the natural floor of its absolute value divided
by the shell width.

Proof: take the natural floor of its absolute value divided by the shell width and split by sign.

Role: partitions every finite signed-coordinate family into the shells used by the kernel sum.
-/
theorem mem_signedDistanceShell_floor_of_mem {S : Finset ℝ} {δ x : ℝ} (hδ : 0 < δ) (hx : x ∈ S) :
    x ∈ signedDistanceShell S δ ⌊|x| / δ⌋₊ := by
  let k : ℕ := ⌊|x| / δ⌋₊
  change x ∈ signedDistanceShell S δ k
  have habsdiv : 0 ≤ |x| / δ := div_nonneg (abs_nonneg x) hδ.le
  have hfloor_le : (k : ℝ) ≤ |x| / δ := by
    dsimp only [k]
    exact Nat.floor_le habsdiv
  have hdiv_lt_floor_succ : |x| / δ < (k : ℝ) + 1 := by
    dsimp only [k]
    exact Nat.lt_floor_add_one _
  have hlower : (k : ℝ) * δ ≤ |x| := (le_div_iff₀ hδ).mp hfloor_le
  have hupper : |x| < ((k : ℝ) + 1) * δ := (div_lt_iff₀ hδ).mp hdiv_lt_floor_succ
  refine Finset.mem_filter.mpr ⟨hx, ?_⟩
  by_cases hxneg : x < 0
  · rw [abs_of_neg hxneg] at hupper hlower
    exact Or.inr ⟨by linarith only [hupper], by linarith only [hlower]⟩
  · have hxnonneg : 0 ≤ x := le_of_not_gt hxneg
    rw [abs_of_nonneg hxnonneg] at hupper hlower
    exact Or.inl ⟨hlower, hupper⟩

/--
Inputs: a positive shell width, a natural shell index, and a point.

Claim: shell membership is equivalent to membership in `S` and equality of the shell index with
the floor of `|x| / δ`.

Proof: the shell gives matching lower and upper bounds for `|x|`; the natural-floor characterization
then identifies the index. The reverse direction is the floor-indexed membership theorem.

Role: proves that different shell indices have disjoint point sets, enabling finite shell summation.
-/
theorem signedDistanceShell_mem_iff_floor_eq {S : Finset ℝ} {δ x : ℝ} {k : ℕ} (hδ : 0 < δ) :
    x ∈ signedDistanceShell S δ k ↔ x ∈ S ∧ ⌊|x| / δ⌋₊ = k := by
  constructor
  · intro hx
    refine ⟨(Finset.mem_filter.mp hx).1, ?_⟩
    have hratio0 : 0 ≤ |x| / δ := div_nonneg (abs_nonneg x) hδ.le
    apply (Nat.floor_eq_iff hratio0).2
    constructor
    · exact (le_div_iff₀ hδ).2 (signedDistanceShell_abs_ge hδ hx)
    · exact (div_lt_iff₀ hδ).2 (signedDistanceShell_abs_lt_succ hδ hx)
  · rintro ⟨hxS, hfloor⟩
    rw [← hfloor]
    exact mem_signedDistanceShell_floor_of_mem hδ hxS

/--
Inputs: a positive shell width and two distinct shell indices.

Claim: the corresponding signed distance shells are disjoint.

Proof: each shell member's floor index is unique, so membership in both forces the indices equal.

Role: permits summing over the finite family of shells without overcounting coordinates.
-/
theorem signedDistanceShell_disjoint_of_ne {S : Finset ℝ} {δ : ℝ} (hδ : 0 < δ) {k l : ℕ}
    (hkl : k ≠ l) : Disjoint (signedDistanceShell S δ k) (signedDistanceShell S δ l) := by
  apply Finset.disjoint_left.mpr
  intro x hxk hxl
  have hfloor_k := (signedDistanceShell_mem_iff_floor_eq hδ).mp hxk
  have hfloor_l := (signedDistanceShell_mem_iff_floor_eq hδ).mp hxl
  exact hkl (hfloor_k.2.symm.trans hfloor_l.2)

/--
Inputs: a finite real set, a positive shell width, a finite shell-index set containing every floor
index, and an additive weight.

Claim: summing the weight over all shells in the index set equals summing it once over the original
set.

Proof: identify each shell with the fiber of the floor-index map and apply finite fiberwise
summation.

Role: collects the per-shell kernel bounds into a bound for a full Gram row.
-/
theorem sum_signedDistanceShells_eq_sum {S : Finset ℝ} {δ : ℝ} {K : Finset ℕ} (hδ : 0 < δ)
    (hindex : ∀ x ∈ S, ⌊|x| / δ⌋₊ ∈ K) {β : Type} [AddCommMonoid β] (f : ℝ → β) :
    ∑ k ∈ K, ∑ x ∈ signedDistanceShell S δ k, f x = ∑ x ∈ S, f x := by
  classical
  have hshell_filter (k : ℕ) : signedDistanceShell S δ k = S.filter (fun x => ⌊|x| / δ⌋₊ = k) := by
    ext x
    rw [signedDistanceShell_mem_iff_floor_eq hδ]
    simp only [Finset.mem_filter]
  calc
    ∑ k ∈ K, ∑ x ∈ signedDistanceShell S δ k, f x =
        ∑ k ∈ K, ∑ x ∈ S.filter (fun x => ⌊|x| / δ⌋₊ = k), f x :=
      by
      apply Finset.sum_congr rfl
      intro k hk
      rw [hshell_filter k]
    _ = ∑ x ∈ S, f x := Finset.sum_fiberwise_of_maps_to hindex f

/--
Inputs: a separated finite real set, a finite shell-index set containing every floor index, and a
nonnegative bound for the summand on each shell.

Claim: the sum over the set is at most twice the sum of the shell bounds.

Proof: decompose the sum by floor-index fibers, use the at-most-two-point shell bound, and apply the
pointwise bound within each shell.

Role: reduces the Gram row estimate to an explicit finite sum of radial kernel envelopes.
-/
theorem sum_le_two_shell_bounds {S : Finset ℝ} {δ : ℝ} {K : Finset ℕ} (hδ : 0 < δ)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ min |x - y| (1 - |x - y|))
    (hindex : ∀ x ∈ S, ⌊|x| / δ⌋₊ ∈ K) (f : ℝ → ℝ) (B : ℕ → ℝ) (hB : ∀ k ∈ K, 0 ≤ B k)
    (hbound : ∀ k ∈ K, ∀ x ∈ signedDistanceShell S δ k, f x ≤ B k) :
    ∑ x ∈ S, f x ≤ ∑ k ∈ K, 2 * B k := by
  rw [← sum_signedDistanceShells_eq_sum hδ hindex f]
  apply Finset.sum_le_sum
  intro k hk
  calc
    ∑ x ∈ signedDistanceShell S δ k, f x ≤ ∑ x ∈ signedDistanceShell S δ k, B k := by
      apply Finset.sum_le_sum
      intro x hx
      exact hbound k hk x hx
    _ = ((signedDistanceShell S δ k).card : ℝ) * B k := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 * B k := by
      exact
        mul_le_mul_of_nonneg_right (by exact_mod_cast signedDistanceShell_card_le_two S δ k hsep)
          (hB k hk)

/--
Inputs: a positive denominator cutoff, a base in `[0, 1)`, and a signed coordinate in the reduced
frequency family.

Claim: the coordinate belongs to a shell whose index lies below `Q² + 1`.

Proof: use its floor shell index, bound that index by `Q²` from the centered-coordinate range, and
embed it in the finite range.

Role: supplies the finite shell index set for summing the reduced-frequency Gram row.
-/
theorem reducedUnitFrequencySignedCoordinates_mem_finite_shell {Q : ℕ} (hQ : 0 < Q) (α : ℝ)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (x : ℝ)
    (hx : x ∈ reducedUnitFrequencySignedCoordinates (Q := Q) α) :
    ∃ k ∈ Finset.range (Q * Q + 1),
      x ∈
        signedDistanceShell (reducedUnitFrequencySignedCoordinates (Q := Q) α) (1 / ((Q : ℝ) * Q))
          k := by
  let k : ℕ := ⌊|x| / (1 / ((Q : ℝ) * Q))⌋₊
  have hQR : 0 < (Q : ℝ) := by exact_mod_cast hQ
  have hQsq : 0 < (Q : ℝ) * Q := mul_pos hQR hQR
  have hδ : 0 < 1 / ((Q : ℝ) * Q) := div_pos (by norm_num only) hQsq
  have hkbound := reducedUnitFrequencySignedCoordinates_floor_shell_index_le hQ α hα0 hα1 x hx
  refine ⟨k, Finset.mem_range.mpr (Nat.lt_succ_of_le hkbound), ?_⟩
  simpa only [k] using mem_signedDistanceShell_floor_of_mem hδ hx

/--
Inputs: two fractions with positive denominators bounded by a common positive natural cutoff,
strictly interior numerators, and distinct cross-products.

Claim: their circular distance is at least the reciprocal square of the cutoff.

Proof: compare the product of the denominators with the square of the cutoff, then apply
`rational_frequency_separation_circular`.

Role: states the uniform spacing parameter used by the additive large sieve for denominators up
to a fixed bound.
-/
theorem rational_frequency_separation_circular_of_le {q r Q x y : ℕ} (hq : 0 < q) (hr : 0 < r)
    (hx : 0 < x) (hxq : x < q) (hy : 0 < y) (hyr : y < r) (hxy : x * r ≠ y * q) (hqQ : q ≤ Q)
    (hrQ : r ≤ Q) :
    1 / ((Q : ℚ) * Q) ≤ min |(x : ℚ) / q - (y : ℚ) / r| (1 - |(x : ℚ) / q - (y : ℚ) / r|) := by
  have hQR : 0 < (Q : ℚ) * Q := by
    have hQ : 0 < Q := hq.trans_le hqQ
    exact mul_pos (by exact_mod_cast hQ) (by exact_mod_cast hQ)
  have hqr : 0 < (q : ℚ) * r := mul_pos (by exact_mod_cast hq) (by exact_mod_cast hr)
  have hprod : (q : ℚ) * r ≤ (Q : ℚ) * Q := by exact_mod_cast Nat.mul_le_mul hqQ hrQ
  have hscale : 1 / ((Q : ℚ) * Q) ≤ 1 / ((q : ℚ) * r) := by
    apply (div_le_div_iff₀ hQR hqr).2
    simpa only [one_mul] using hprod
  exact le_trans hscale (rational_frequency_separation_circular hq hr hx hxq hy hyr hxy)

/--
Inputs: a nontrivial `ZMod q`, a unit residue, and a modulus greater than one.

Claim: the canonical natural representative of the unit residue lies strictly between zero and
the modulus.

Proof: the unit property makes its representative coprime to the modulus, so it cannot be zero
when the modulus exceeds one; the upper bound is `ZMod.val_lt`.

Role: places reduced additive frequencies in the open unit interval.
-/
theorem zmod_unit_value_bounds {q : ℕ} [NeZero q] (hq : 1 < q) (x : ZMod q) (hx : IsUnit x) :
    0 < x.val ∧ x.val < q := by
  have hx' : IsUnit ((x.val : ℕ) : ZMod q) := by simpa only [ZMod.natCast_zmod_val] using hx
  have hcop : Nat.Coprime x.val q := (ZMod.isUnit_iff_coprime x.val q).mp hx'
  have hval : x.val ≠ 0 := by
    intro h
    have hc : Nat.Coprime 0 q := by simpa only [h] using hcop
    have hqone : q = 1 := (Nat.coprime_zero_left q).mp hc
    exact (Nat.ne_of_gt hq) hqone
  exact ⟨Nat.pos_of_ne_zero hval, ZMod.val_lt x⟩

/--
Inputs: a residue modulo a positive natural modulus and a proof that it is a unit.

Claim: its canonical natural representative is coprime to the modulus.

Proof: rewrite the residue as the natural cast of its canonical representative and apply the
unit characterization for `ZMod`.

Role: supplies the reducedness hypothesis needed for uniqueness of rational frequencies.
-/
theorem zmod_unit_value_coprime {q : ℕ} [NeZero q] (x : ZMod q) (hx : IsUnit x) :
    Nat.Coprime x.val q := by
  have hx' : IsUnit ((x.val : ℕ) : ZMod q) := by simpa only [ZMod.natCast_zmod_val] using hx
  exact (ZMod.isUnit_iff_coprime x.val q).mp hx'

/--
Inputs: unit residues modulo two positive natural moduli.

Claim: equality of their canonical rational frequencies is equivalent to equality of both
denominators and canonical numerators.

Proof: unit representatives are coprime to their moduli, so apply uniqueness of reduced rational
representations; the reverse implication follows by substitution.

Role: identifies the frequency index with its reduced fraction, allowing pairwise spacing to be
used across the family of moduli.
-/
theorem reducedUnitFrequency_eq_iff {q r : ℕ} [NeZero q] [NeZero r] (x : ZMod q) (hx : IsUnit x)
    (y : ZMod r) (hy : IsUnit y) : (x.val : ℚ) / q = (y.val : ℚ) / r ↔ q = r ∧ x.val = y.val := by
  constructor
  · intro h
    exact
      rational_reduced_fraction_unique (NeZero.pos q) (NeZero.pos r) (zmod_unit_value_coprime x hx)
        (zmod_unit_value_coprime y hy) h
  · rintro ⟨rfl, hxy⟩
    simp only [hxy]

/--
Inputs: unit residues modulo two moduli bounded by `Q`, with distinct rational frequencies.

Claim: their circular distance is at least `1 / Q^2`.

Proof: unit representatives are strictly between zero and their moduli; distinct frequencies
have unequal cross-products, so apply the denominator-uniform circular spacing estimate.

Role: transfers the rational spacing result to the reduced residue frequencies used in the
primitive-character mean-square reduction.
-/
theorem reducedUnitFrequency_circularSeparation {q r Q : ℕ} [NeZero q] [NeZero r] (hq : 1 < q)
    (hr : 1 < r) (hqQ : q ≤ Q) (hrQ : r ≤ Q) (x : ZMod q) (hx : IsUnit x) (y : ZMod r)
    (hy : IsUnit y) (hfrac : (x.val : ℚ) / q ≠ (y.val : ℚ) / r) :
    1 / ((Q : ℚ) * Q) ≤
      min |(x.val : ℚ) / q - (y.val : ℚ) / r| (1 - |(x.val : ℚ) / q - (y.val : ℚ) / r|) := by
  have hqpos : 0 < q := Nat.zero_lt_of_lt hq
  have hrpos : 0 < r := Nat.zero_lt_of_lt hr
  obtain ⟨hxpos, hxq⟩ := zmod_unit_value_bounds hq x hx
  obtain ⟨hypos, hyr⟩ := zmod_unit_value_bounds hr y hy
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hqpos.ne'
  have hr0 : (r : ℚ) ≠ 0 := by exact_mod_cast hrpos.ne'
  have hcross : x.val * r ≠ y.val * q := by
    intro h
    have h' : (x.val : ℚ) * r = (y.val : ℚ) * q := by exact_mod_cast h
    apply hfrac
    exact (div_eq_div_iff hq0 hr0).2 h'
  exact rational_frequency_separation_circular_of_le hqpos hrpos hxpos hxq hypos hyr hcross hqQ hrQ

/--
Inputs: distinct reduced unit frequencies with denominators at most `Q`.

Claim: their signed circular differences are separated by at least `1 / Q^2` in circular
distance.

Proof: transfer the rational frequency spacing to real representatives, then use preservation of
circular distance by `signedCircularDifference`.

Role: supplies the separation hypothesis for counting finite signed-frequency shells.
-/
theorem reducedUnitFrequency_signedCircularSeparation {q r Q : ℕ} [NeZero q] [NeZero r] (hq : 1 < q)
    (hr : 1 < r) (hqQ : q ≤ Q) (hrQ : r ≤ Q) (x : ZMod q) (hx : IsUnit x) (y : ZMod r)
    (hy : IsUnit y) (hfrac : (x.val : ℚ) / q ≠ (y.val : ℚ) / r) :
    1 / ((Q : ℝ) * Q) ≤
      min |signedCircularDifference ((x.val : ℝ) / q) ((y.val : ℝ) / r)|
        (1 - |signedCircularDifference ((x.val : ℝ) / q) ((y.val : ℝ) / r)|) := by
  have hsep := reducedUnitFrequency_circularSeparation hq hr hqQ hrQ x hx y hy hfrac
  have hsepR :
    1 / ((Q : ℝ) * Q) ≤
      min |(x.val : ℝ) / q - (y.val : ℝ) / r| (1 - |(x.val : ℝ) / q - (y.val : ℝ) / r|) := by
    simpa only [Rat.cast_div, Rat.cast_mul, Rat.cast_one, Rat.cast_min, Rat.cast_abs, Rat.cast_sub,
      Rat.cast_natCast] using (Rat.cast_le (K := ℝ)).2 hsep
  have hsepR' :
    1 / ((Q : ℝ) * Q) ≤
      min |(y.val : ℝ) / r - (x.val : ℝ) / q| (1 - |(y.val : ℝ) / r - (x.val : ℝ) / q|) := by
    simpa only [abs_sub_comm] using hsepR
  obtain ⟨hx0, hx1⟩ := zmod_unit_value_bounds hq x hx
  obtain ⟨hy0, hy1⟩ := zmod_unit_value_bounds hr y hy
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hq)
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hr)
  have hα0 : 0 ≤ (x.val : ℝ) / q := div_nonneg (by exact_mod_cast hx0.le) hqpos.le
  have hα1 : (x.val : ℝ) / q < 1 := (div_lt_one hqpos).2 (by exact_mod_cast hx1)
  have hβ0 : 0 ≤ (y.val : ℝ) / r := div_nonneg (by exact_mod_cast hy0.le) hrpos.le
  have hβ1 : (y.val : ℝ) / r < 1 := (div_lt_one hrpos).2 (by exact_mod_cast hy1)
  rw [signedCircularDifference_circularDistance hα0 hα1 hβ0 hβ1]
  exact hsepR'

/--
Inputs: a complex ratio and a natural taper length.

Claim: reversing the exponents in a finite geometric sum leaves the sum unchanged.

Proof: reindex the interval by the involution `j ↦ L - 1 - j`.

Role: transfers the geometric-sum norm bound to the reversed factor in the overlap kernel.
-/
theorem reverse_geometric_sum_eq {z : ℂ} (L : ℕ) :
    ∑ j ∈ Finset.range L, z ^ (L - 1 - j) = ∑ i ∈ Finset.range L, z ^ i := by
  classical
  refine Finset.sum_bij' (i := fun j _ => L - 1 - j) (j := fun i _ => L - 1 - i) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    have hjlt : j < L := Finset.mem_range.mp hj
    simp only [Finset.mem_range]
    omega
  · intro i hi
    have hilt : i < L := Finset.mem_range.mp hi
    simp only [Finset.mem_range]
    omega
  · intro j hj
    have hjlt : j < L := Finset.mem_range.mp hj
    omega
  · intro i hi
    have hilt : i < L := Finset.mem_range.mp hi
    omega
  · intro j hj
    rfl

/--
Inputs: a complex number on the unit circle, distinct from one, and a natural interval length.

Claim: the geometric exponential sum over that interval has norm at most twice the reciprocal
distance from the ratio to one.

Proof: telescope the geometric sum, take norms, use unit norm for every power, and divide by the
nonzero denominator.

Role: bounds the off-diagonal kernel that appears when squaring finite exponential sums in a
large-sieve estimate.
-/
theorem unit_circle_geometric_sum_norm_le {z : ℂ} (hz : ‖z‖ = 1) (hneq : z ≠ 1) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, z ^ n‖ ≤ 2 / ‖1 - z‖ := by
  have hgeom : (1 - z) * ∑ n ∈ Finset.range N, z ^ n = 1 - z ^ N := by
    induction N with
    | zero => simp only [Finset.sum_range_zero, mul_zero, pow_zero, sub_self]
    | succ N ih =>
      rw [Finset.sum_range_succ, pow_succ]
      rw [mul_add, ih]
      ring
  have hden : 1 - z ≠ 0 := sub_ne_zero.mpr hneq.symm
  have hden0 : ‖1 - z‖ ≠ 0 := norm_ne_zero_iff.mpr hden
  have hpow : ‖z ^ N‖ = 1 := by rw [norm_pow, hz, one_pow]
  have hnum : ‖1 - z ^ N‖ ≤ 2 := by
    calc
      ‖1 - z ^ N‖ ≤ ‖1‖ + ‖z ^ N‖ := norm_sub_le _ _
      _ = 2 := by
        rw [norm_one, hpow]; ring
  have hnorm : ‖1 - z‖ * ‖∑ n ∈ Finset.range N, z ^ n‖ = ‖1 - z ^ N‖ := by rw [← norm_mul, hgeom]
  have hnorm' : ‖∑ n ∈ Finset.range N, z ^ n‖ * ‖1 - z‖ = ‖1 - z ^ N‖ := by
    simpa only [mul_comm] using hnorm
  have hdivide : ‖∑ n ∈ Finset.range N, z ^ n‖ = ‖1 - z ^ N‖ / ‖1 - z‖ :=
    (eq_div_iff hden0).2 hnorm'
  rw [hdivide]
  exact div_le_div_of_nonneg_right hnum (norm_nonneg _)

/--
Inputs: a complex number on the unit circle, distinct from one, and a natural interval length.

Claim: the geometric sum is bounded both by its length and by twice the reciprocal phase distance.

Proof: use the triangle inequality for the length bound and the telescoping estimate for decay.

Role: supplies both regimes needed for the tapered Gram-kernel estimate.
-/
theorem unit_circle_geometric_sum_norm_le_min {z : ℂ} (hz : ‖z‖ = 1) (hneq : z ≠ 1) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, z ^ n‖ ≤ min (N : ℝ) (2 / ‖1 - z‖) := by
  apply le_min
  · calc
      ‖∑ n ∈ Finset.range N, z ^ n‖ ≤ ∑ n ∈ Finset.range N, ‖z ^ n‖ := norm_sum_le _ _
      _ = N := by
        simp only [norm_pow, hz, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          mul_one]
  · exact unit_circle_geometric_sum_norm_le hz hneq N

/--
Inputs: a unit-circle ratio distinct from one and a natural taper length.

Claim: the reversed geometric sum has the same length-and-decay bound as the forward sum.

Proof: reindex its terms in reverse order and apply `unit_circle_geometric_sum_norm_le_min`.

Role: bounds the second geometric factor in the overlap Fourier kernel.
-/
theorem reverse_unit_circle_geometric_sum_norm_le_min {z : ℂ} (hz : ‖z‖ = 1) (hneq : z ≠ 1)
    (L : ℕ) : ‖∑ j ∈ Finset.range L, z ^ (L - 1 - j)‖ ≤ min (L : ℝ) (2 / ‖1 - z‖) := by
  rw [reverse_geometric_sum_eq]
  exact unit_circle_geometric_sum_norm_le_min hz hneq L

/--
Inputs: an interval length, taper length, and unit-circle ratio distinct from one.

Claim: the overlap Fourier kernel is bounded by the product of the two geometric-sum envelopes,
divided by the taper length through the complex inverse factor.

Proof: factor the kernel, apply the length-and-decay bounds to both geometric sums, and use norm
multiplicativity.

Role: is the pointwise off-diagonal estimate used in summing separated-frequency Gram rows.
-/
theorem triangleOverlapWindowWeight_fourier_norm_le (N L : ℕ) (z : ℂ) (hz : ‖z‖ = 1)
    (hneq : z ≠ 1) :
    ‖∑ n ∈ Finset.range (N + 2 * L - 1), (triangleOverlapWindowWeight N L n : ℂ) * z ^ n‖ ≤
      ‖(L : ℂ)⁻¹‖ * min ((N + L : ℕ) : ℝ) (2 / ‖1 - z‖) * min (L : ℝ) (2 / ‖1 - z‖) := by
  rw [triangleOverlapWindowWeight_fourier_eq_geometric_product]
  rw [norm_mul, norm_mul]
  have hfirst := unit_circle_geometric_sum_norm_le_min hz hneq (N + L)
  have hsecond := reverse_unit_circle_geometric_sum_norm_le_min hz hneq L
  have hminNonneg : 0 ≤ min ((N + L : ℕ) : ℝ) (2 / ‖1 - z‖) := le_trans (norm_nonneg _) hfirst
  calc
    ‖(L : ℂ)⁻¹‖ * ‖∑ i ∈ Finset.range (N + L), z ^ i‖ * ‖∑ j ∈ Finset.range L, z ^ (L - 1 - j)‖ ≤
        (‖(L : ℂ)⁻¹‖ * min ((N + L : ℕ) : ℝ) (2 / ‖1 - z‖)) *
          ‖∑ j ∈ Finset.range L, z ^ (L - 1 - j)‖ :=
      by
      exact
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfirst (norm_nonneg _))
          (norm_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_left hsecond (mul_nonneg (norm_nonneg _) hminNonneg)

/--
Inputs: a nonzero natural modulus and a residue in its `ZMod` ring.

Claim: the standard additive character equals the complex exponential at the residue's canonical
rational frequency.

Proof: unfold the character as the coercion of `ZMod.toCircle` and use its explicit formula.

Role: connects finite additive Fourier sums to the rational frequencies used in the spacing
estimates.
-/
theorem zmod_stdAddChar_exp_val {q : ℕ} [NeZero q] (x : ZMod q) :
    ZMod.stdAddChar x = Complex.exp (2 * Real.pi * Complex.I * (x.val : ℂ) / q) := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]

/--
Inputs: a residue modulo a nonzero natural modulus and a natural exponent.

Claim: evaluating the standard additive character at the residue multiplied by the exponent is
the corresponding power of its value at the residue.

Proof: rewrite natural scalar multiplication as multiplication in `ZMod` and apply the additive
character's `nsmul`-to-power identity.

Role: expresses each additive Fourier polynomial as a polynomial in its frequency phase.
-/
theorem zmod_stdAddChar_mul_nat_eq_pow {q : ℕ} [NeZero q] (x : ZMod q) (n : ℕ) :
    ZMod.stdAddChar (x * (n : ZMod q)) = (ZMod.stdAddChar x) ^ n := by
  calc
    _ = ZMod.stdAddChar (n • x) := by
      congr 1
      rw [nsmul_eq_mul]
      ring
    _ = _ := AddChar.map_nsmul_eq_pow _ _ _

/--
Inputs: a nonzero modulus, a residue, and a natural polynomial index.

Claim: the standard additive character at the residue times the index equals the rational
exponential at the residue's canonical fraction.

Proof: rewrite the additive character as a natural power, use its explicit exponential formula,
and combine the exponent into the rational-frequency definition.

Role: allows reduced residue frequencies from different moduli to share the rational-frequency
large-sieve interface.
-/
theorem zmod_stdAddChar_mul_nat_eq_rationalAdditiveCharacter {q : ℕ} [NeZero q] (x : ZMod q)
    (n : ℕ) :
    ZMod.stdAddChar (x * (n : ZMod q)) = rationalAdditiveCharacter ((x.val : ℚ) / q) n := by
  rw [zmod_stdAddChar_mul_nat_eq_pow, zmod_stdAddChar_exp_val]
  rw [rationalAdditiveCharacter, ← Complex.exp_nat_mul]
  congr 1
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
  push_cast
  field_simp [hq]

/--
Inputs: a nonzero modulus and two residues in its unit-frequency set.

Claim: equal rational frequencies have equal residues.

Proof: use uniqueness of reduced fractions and injectivity of the canonical `ZMod` value.

Role: proves injectivity when a modulus' unit frequencies are reindexed by rational numbers.
-/
theorem reducedUnitFrequency_rational_injective {q : ℕ} [NeZero q] :
    Set.InjOn (fun x : ZMod q => (x.val : ℚ) / q)
      (↑(reducedUnitFrequencySet q) : Set (ZMod q)) := by
  intro x hx y hy hxy
  have hxunit : IsUnit x := (Finset.mem_filter.mp hx).2
  have hyunit : IsUnit y := (Finset.mem_filter.mp hy).2
  exact ZMod.val_injective q ((reducedUnitFrequency_eq_iff x hxunit y hyunit).mp hxy).2

/--
Inputs: a nonzero modulus, a residue frequency, a finite index set, and complex coefficients.

Claim: the additive Fourier polynomial at the residue equals the rational exponential polynomial
at its canonical fraction.

Proof: rewrite each character value by `zmod_stdAddChar_mul_nat_eq_rationalAdditiveCharacter`.

Role: transfers the polynomial evaluation before reindexing a modulus' mean square.
-/
theorem reducedUnitFrequency_polynomial_eq_rational {q : ℕ} [NeZero q] (x : ZMod q) (S : Finset ℕ)
    (a : ℕ → ℂ) :
    (∑ n ∈ S, a n * ZMod.stdAddChar (x * (n : ZMod q))) =
      ∑ n ∈ S, a n * rationalAdditiveCharacter ((x.val : ℚ) / q) n := by
  apply Finset.sum_congr rfl
  intro n hn
  exact congrArg (fun z : ℂ => a n * z) (zmod_stdAddChar_mul_nat_eq_rationalAdditiveCharacter x n)

/--
Inputs: a modulus greater than one, a finite polynomial index set, and complex coefficients.

Claim: the reduced additive mean square modulo the modulus equals the rational-frequency mean
square over the image of its unit residues.

Proof: identify each unit residue with its reduced rational frequency, use uniqueness of reduced
fractions to reindex the finite sum injectively, and rewrite each character by the preceding
exponential identity.

Role: transfers one modulus' additive contribution into the common rational-frequency family.
-/
theorem reducedAdditivePolynomialMeanSquare_eq_rational {q : ℕ} [NeZero q] (hq : 1 < q)
    (S : Finset ℕ) (a : ℕ → ℂ) :
    reducedAdditivePolynomialMeanSquare q hq S a =
      rationalAdditivePolynomialMeanSquare
        ((reducedUnitFrequencySet q).image (fun x => (x.val : ℚ) / q)) S a := by
  classical
  let U := reducedUnitFrequencySet q
  let f : ZMod q → ℚ := fun x => (x.val : ℚ) / q
  have hInjective : Set.InjOn f (↑U : Set (ZMod q)) := reducedUnitFrequency_rational_injective
  rw [reducedAdditivePolynomialMeanSquare, rationalAdditivePolynomialMeanSquare]
  change
    (∑ x ∈ U, Complex.normSq (∑ n ∈ S, a n * ZMod.stdAddChar (x * (n : ZMod q)))) =
      ∑ α ∈ U.image f, Complex.normSq (∑ n ∈ S, a n * rationalAdditiveCharacter α n)
  calc
    (∑ x ∈ U, Complex.normSq (∑ n ∈ S, a n * ZMod.stdAddChar (x * (n : ZMod q)))) =
        ∑ x ∈ U, Complex.normSq (∑ n ∈ S, a n * rationalAdditiveCharacter (f x) n) :=
      by
      apply Finset.sum_congr rfl
      intro x hx
      apply congrArg Complex.normSq
      exact reducedUnitFrequency_polynomial_eq_rational x S a
    _ = ∑ α ∈ U.image f, Complex.normSq (∑ n ∈ S, a n * rationalAdditiveCharacter α n) :=
      (Finset.sum_image (s := U) (g := f) (f := fun α : ℚ =>
          Complex.normSq (∑ n ∈ S, a n * rationalAdditiveCharacter α n)) hInjective).symm

/--
Inputs: positive natural moduli `q,r` and a natural frequency `n`.

Claim: the standard additive character modulo `q*r` at `r*n` equals the standard additive
character modulo `q` at `n`.

Proof: rewrite both values by the exponential formula for integer representatives and cancel the
nonzero factor `r` in the phase denominator.

Role: identifies the additive phase of the `r`-multiple component in the CRT decomposition.
-/
theorem zmod_stdAddChar_mul_factor_eq {q r : ℕ} [NeZero q] [NeZero r] (n : ℕ) :
    ZMod.stdAddChar ((r * n : ℕ) : ZMod (q * r)) = ZMod.stdAddChar (n : ZMod q) := by
  rw [show ((r * n : ℕ) : ZMod (q * r)) = ((r * n : ℤ) : ZMod (q * r)) by
      simp only [Nat.cast_mul, Int.cast_mul, Int.cast_natCast]]
  rw [show (n : ZMod q) = (n : ℤ) by simp only [Int.cast_natCast]]
  rw [ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  have hr : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne r)
  have hq : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hqr : (q : ℂ) * r ≠ 0 := mul_ne_zero hq hr
  apply (div_eq_div_iff hqr hq).2
  ring

/--
Inputs: positive natural moduli `q,r` and a natural frequency `n`.

Claim: the standard additive character modulo `q*r` at `q*n` equals the standard additive
character modulo `r` at `n`.

Proof: rewrite both values by the exponential formula for integer representatives and cancel the
nonzero factor `q` in the phase denominator.

Role: identifies the additive phase of the `q`-multiple component in the CRT decomposition.
-/
theorem zmod_stdAddChar_mul_left_factor_eq {q r : ℕ} [NeZero q] [NeZero r] (n : ℕ) :
    ZMod.stdAddChar ((q * n : ℕ) : ZMod (q * r)) = ZMod.stdAddChar (n : ZMod r) := by
  rw [show ((q * n : ℕ) : ZMod (q * r)) = ((q * n : ℤ) : ZMod (q * r)) by
      simp only [Nat.cast_mul, Int.cast_mul, Int.cast_natCast]]
  rw [show (n : ZMod r) = (n : ℤ) by simp only [Int.cast_natCast]]
  rw [ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  have hr : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne r)
  have hq : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hqr : (q : ℂ) * r ≠ 0 := mul_ne_zero hq hr
  apply (div_eq_div_iff hqr hr).2
  ring

/--
Inputs: positive natural moduli `q,r` and natural frequencies `a,b`.

Claim: the standard additive character modulo `q*r` at `r*a + q*b` factors as the product of the
standard characters modulo `q` and `r` at `a` and `b`.

Proof: use additivity of the standard character and the two modulus-factor identities.

Role: factors each term after reindexing the units modulo `q*r` by the Chinese-remainder theorem.
-/
theorem zmod_stdAddChar_add_factor_eq {q r : ℕ} [NeZero q] [NeZero r] (a b : ℕ) :
    ZMod.stdAddChar ((r * a + q * b : ℕ) : ZMod (q * r)) =
      ZMod.stdAddChar (a : ZMod q) * ZMod.stdAddChar (b : ZMod r) := by
  rw [Nat.cast_add, AddChar.map_add_eq_mul, zmod_stdAddChar_mul_factor_eq,
    zmod_stdAddChar_mul_left_factor_eq]

/--
Inputs: coprime positive moduli `q,r`, residues `a,b`, and a natural frequency `n`.

Claim: the standard additive character modulo `q*r`, evaluated at `n` times the CRT lift of
`(a,b)`, factors into the standard characters modulo `q` and `r` at the corresponding inverse-
twisted residues.

Proof: use the explicit CRT representative and split its additive character into the two modulus
components.

Role: factors each additive phase after reindexing a unit sum by the Chinese-remainder equivalence.
-/
theorem stdAddChar_mul_chineseRemainder_symm {q r : ℕ} [NeZero q] [NeZero r] (h : Nat.Coprime q r)
    (a : ZMod q) (b : ZMod r) (n : ℕ) :
    let A : ℕ := (((ZMod.isUnit_iff_coprime r q).2 h.symm).unit⁻¹ * a).val
    let B : ℕ := (((ZMod.isUnit_iff_coprime q r).2 h).unit⁻¹ * b).val
    ZMod.stdAddChar ((n : ZMod (q * r)) * ((ZMod.chineseRemainder h).symm (a, b))) =
      ZMod.stdAddChar ((n * A : ℕ) : ZMod q) * ZMod.stdAddChar ((n * B : ℕ) : ZMod r) := by
  dsimp only
  rw [chineseRemainder_symm_apply_nat]
  let A : ℕ := (((ZMod.isUnit_iff_coprime r q).2 h.symm).unit⁻¹ * a).val
  let B : ℕ := (((ZMod.isUnit_iff_coprime q r).2 h).unit⁻¹ * b).val
  have hmul :
    (n : ZMod (q * r)) * ((r * A + q * B : ℕ) : ZMod (q * r)) =
      ((r * (n * A) + q * (n * B) : ℕ) : ZMod (q * r)) := by
    push_cast
    ring
  rw [hmul, zmod_stdAddChar_add_factor_eq]

/--
Inputs: a positive modulus `q`, a frequency `n`, and a unit `u` modulo `q`.

Claim: multiplying each unit in the additive-character sum by `u` leaves the sum unchanged.

Proof: reindex the finite sum by the equivalence given by left multiplication by `u`.

Role: removes the inverse twists introduced by the explicit CRT representative.
-/
theorem sum_stdAddChar_mul_unit_eq_ramanujanSum {q : ℕ} [NeZero q] (n : ℕ) (u : (ZMod q)ˣ) :
    (∑ a : (ZMod q)ˣ, ZMod.stdAddChar ((n : ZMod q) * ((u * a : (ZMod q)ˣ) : ZMod q))) =
      ramanujanSum q n := by
  classical
  unfold ramanujanSum
  exact Fintype.sum_equiv (Equiv.mulLeft u) _ _ (fun a => rfl)

/--
Inputs: coprime positive moduli `q,r` and a natural frequency `n`.

Claim: the Ramanujan sum modulo `q*r` is the product of the Ramanujan sums modulo `q` and `r`.

Proof: reindex units by the CRT equivalence, factor each additive phase into its two components,
then remove the inverse twists by finite-sum reindexing.

Role: supplies the multiplicative normalization for Ramanujan weights in the finite character
decomposition.
-/
theorem ramanujanSum_mul_coprime {q r : ℕ} [NeZero q] [NeZero r] (h : Nat.Coprime q r) (n : ℕ) :
    ramanujanSum (q * r) n = ramanujanSum q n * ramanujanSum r n := by
  classical
  let ur : (ZMod q)ˣ := (ZMod.isUnit_iff_coprime r q).2 h.symm |>.unit
  let uq : (ZMod r)ˣ := (ZMod.isUnit_iff_coprime q r).2 h |>.unit
  let e : (ZMod (q * r))ˣ ≃* (ZMod q)ˣ × (ZMod r)ˣ :=
    (Units.mapEquiv (ZMod.chineseRemainder h).toMulEquiv).trans MulEquiv.prodUnits
  have hq :
    (∑ a : (ZMod q)ˣ, ZMod.stdAddChar ((n * (ur⁻¹ * (a : ZMod q)).val : ℕ) : ZMod q)) =
      ramanujanSum q n := by
    calc
      _ = ∑ a : (ZMod q)ˣ, ZMod.stdAddChar ((n : ZMod q) * ((ur⁻¹ * a : (ZMod q)ˣ) : ZMod q)) := by
        apply Finset.sum_congr rfl
        intro a ha
        simp only [Nat.cast_mul, ZMod.natCast_zmod_val, Units.val_mul]
      _ = ramanujanSum q n := sum_stdAddChar_mul_unit_eq_ramanujanSum n ur⁻¹
  have hr :
    (∑ b : (ZMod r)ˣ, ZMod.stdAddChar ((n * (uq⁻¹ * (b : ZMod r)).val : ℕ) : ZMod r)) =
      ramanujanSum r n := by
    calc
      _ = ∑ b : (ZMod r)ˣ, ZMod.stdAddChar ((n : ZMod r) * ((uq⁻¹ * b : (ZMod r)ˣ) : ZMod r)) := by
        apply Finset.sum_congr rfl
        intro b hb
        simp only [Nat.cast_mul, ZMod.natCast_zmod_val, Units.val_mul]
      _ = ramanujanSum r n := sum_stdAddChar_mul_unit_eq_ramanujanSum n uq⁻¹
  calc
    ramanujanSum (q * r) n =
        ∑ a : (ZMod q)ˣ,
          ∑ b : (ZMod r)ˣ, ZMod.stdAddChar ((n : ZMod (q * r)) * (e.symm (a, b) : ZMod (q * r))) :=
      by
      unfold ramanujanSum
      rw [sum_units_zmod_mul_coprime h]
    _ =
        ∑ a : (ZMod q)ˣ,
          ∑ b : (ZMod r)ˣ,
            ZMod.stdAddChar ((n * (ur⁻¹ * (a : ZMod q)).val : ℕ) : ZMod q) *
              ZMod.stdAddChar ((n * (uq⁻¹ * (b : ZMod r)).val : ℕ) : ZMod r) :=
      by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      change ZMod.stdAddChar ((n : ZMod (q * r)) * ((ZMod.chineseRemainder h).symm (a, b))) = _
      exact stdAddChar_mul_chineseRemainder_symm h a b n
    _ = ramanujanSum q n * ramanujanSum r n := by rw [← Finset.sum_mul_sum, hq, hr]

/--
Inputs: a positive squarefree modulus `r`.

Claim: the squared norm of the Ramanujan sum at frequency one is one.

Proof: factor `r` into a prime and a smaller squarefree quotient, use coprime multiplicativity,
and induct on `r`; the prime factor contributes `-1`.

Role: shows that the constant Ramanujan coefficient on a pre-sifted support has unit squared norm.
-/
theorem ramanujanSum_one_normSq_eq_one (r : ℕ) (hr : 0 < r) (hsq : Squarefree r) :
    ‖@ramanujanSum r 1 ⟨Nat.ne_of_gt hr⟩‖ ^ 2 = 1 := by
  revert hr hsq
  induction r using Nat.strong_induction_on with
  | h r ih =>
    intro hr hsq
    by_cases hrOne : r = 1
    · subst r
      have hsum : ramanujanSum 1 1 = 1 := by
        calc
          ramanujanSum 1 1 = ramanujanSum 1 (0 + 1 * 1) := by norm_num only
          _ = ramanujanSum 1 0 := ramanujanSum_add_modulus_multiple 1 0 1
          _ = 1 := by
            rw [ramanujanSum_zero]; norm_num only [Nat.totient_one]
      rw [hsum]
      norm_num only [norm_one]
    · obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hrOne
      let m := r / p
      have hfactor : p * m = r := by
        dsimp only [m]
        exact Nat.mul_div_cancel' hpdvd
      have hm : 0 < m := by
        dsimp only [m]
        exact Nat.div_pos (Nat.le_of_dvd hr hpdvd) hp.pos
      have hmsq : Squarefree m := by
        apply Squarefree.squarefree_of_dvd (show m ∣ r from ⟨p, by rw [Nat.mul_comm, hfactor]⟩)
        exact hsq
      have hsqpm : Squarefree (p * m) := hfactor ▸ hsq
      have hcop : Nat.Coprime p m := Nat.coprime_of_squarefree_mul hsqpm
      have hlt : m < r := by
        dsimp only [m]
        exact Nat.div_lt_self hr hp.one_lt
      have hih := ih m hlt hm hmsq
      have hpNe : NeZero p := ⟨hp.ne_zero⟩
      have hpFact : Fact p.Prime := ⟨hp⟩
      have hprime : @ramanujanSum p 1 hpNe = -1 := ramanujanSum_prime_one
      have hmNe : NeZero m := ⟨Nat.ne_of_gt hm⟩
      have hmul := @ramanujanSum_mul_coprime p m hpNe hmNe hcop 1
      have hfactorSum : @ramanujanSum r 1 ⟨Nat.ne_of_gt hr⟩ = -@ramanujanSum m 1 hmNe := by
        calc
          _ = @ramanujanSum (p * m) 1 ⟨Nat.ne_of_gt (Nat.mul_pos hp.pos hm)⟩ := by
            congr 1
            exact hfactor.symm
          _ = _ := by
            rw [hmul, hprime]; ring
      rw [hfactorSum, norm_neg]
      exact hih

/--
Inputs: a character modulus greater than one, a positive squarefree Ramanujan modulus coprime to
every index in a finite polynomial, and complex coefficients.

Claim: inserting the Ramanujan weight into the primitive-character mean square leaves that mean
square unchanged.

Proof: coprimality makes the weight constant on the index set, and the squarefree norm lemma shows
that this constant has squared norm one.

Role: identifies each squarefree term in the reciprocal-totient lower bound with the same
unweighted primitive-character mean square.
-/
theorem primitiveCharacterPolynomialMeanSquare_eq_of_squarefree_ramanujan {q r : ℕ} [NeZero r]
    (hq : 1 < q) (S : Finset ℕ) (a : ℕ → ℂ) (hr : 0 < r) (hsq : Squarefree r)
    (hcop : ∀ n ∈ S, Nat.Coprime n r) :
    primitiveCharacterPolynomialMeanSquare q hq S (fun n => a n * ramanujanSum r n) =
      primitiveCharacterPolynomialMeanSquare q hq S a := by
  have hnorm : Complex.normSq (ramanujanSum r 1) = 1 := by
    rw [Complex.normSq_eq_norm_sq]
    exact ramanujanSum_one_normSq_eq_one r hr hsq
  have hsum :
    primitiveCharacterPolynomialMeanSquare q hq S (fun n => a n * ramanujanSum r n) =
      primitiveCharacterPolynomialMeanSquare q hq S (fun n => a n * ramanujanSum r 1) := by
    classical
    unfold primitiveCharacterPolynomialMeanSquare
    apply Finset.sum_congr rfl
    intro χ hχ
    apply congrArg Complex.normSq
    apply Finset.sum_congr rfl
    intro n hn
    change a n * ramanujanSum r n * χ (n : ZMod q) = a n * ramanujanSum r 1 * χ (n : ZMod q)
    rw [ramanujanSum_eq_one_of_coprime (hcop n hn)]
  calc
    _ = _ := hsum
    _ = _ := primitiveCharacterPolynomialMeanSquare_mul_const hq S a (ramanujanSum r 1)
    _ = _ := by
      rw [hnorm]; simp only [one_mul]

/--
Inputs: coprime positive moduli `q,r`, characters at those moduli, and units `a,b`.

Claim: the product of the level-raised characters at the CRT unit corresponding to `(a,b)` is
`χ a * ψ b`.

Proof: identify the CRT inverse image with the inverse image of the pair of underlying residues,
then evaluate each raised character through its modulus cast.

Role: separates the multiplicative character factor in the CRT factorization of unit Gauss sums.
-/
theorem changeLevel_mul_apply_crt_units {q r : ℕ} [NeZero q] [NeZero r] (h : Nat.Coprime q r)
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) (a : (ZMod q)ˣ) (b : (ZMod r)ˣ) :
    (DirichletCharacter.changeLevel (Nat.dvd_mul_right q r) χ *
          DirichletCharacter.changeLevel (Nat.dvd_mul_left r q) ψ)
        (((Units.mapEquiv (ZMod.chineseRemainder h).toMulEquiv).trans MulEquiv.prodUnits).symm
          (a, b)) =
      χ (a : ZMod q) * ψ (b : ZMod r) := by
  let e : (ZMod (q * r))ˣ ≃* (ZMod q)ˣ × (ZMod r)ˣ :=
    (Units.mapEquiv (ZMod.chineseRemainder h).toMulEquiv).trans MulEquiv.prodUnits
  let u : (ZMod (q * r))ˣ := e.symm (a, b)
  have huval : (u : ZMod (q * r)) = (ZMod.chineseRemainder h).symm ((a : ZMod q), (b : ZMod r)) :=
    rfl
  have hcrt : (ZMod.chineseRemainder h) (u : ZMod (q * r)) = ((a : ZMod q), (b : ZMod r)) := by
    rw [huval]
    exact RingEquiv.apply_symm_apply _ _
  have hq : ((u : ZMod (q * r)).cast : ZMod q) = (a : ZMod q) := by
    have hp := congrArg Prod.fst hcrt
    change ((u : ZMod (q * r)).cast : ZMod q × ZMod r).1 = (a : ZMod q) at hp
    simpa only [Prod.fst_zmod_cast] using hp
  have hr : ((u : ZMod (q * r)).cast : ZMod r) = (b : ZMod r) := by
    have hp := congrArg Prod.snd hcrt
    change ((u : ZMod (q * r)).cast : ZMod q × ZMod r).2 = (b : ZMod r) at hp
    simpa only [Prod.snd_zmod_cast] using hp
  have hχ := DirichletCharacter.changeLevel_eq_cast_of_dvd χ (Nat.dvd_mul_right q r) u
  have hψ := DirichletCharacter.changeLevel_eq_cast_of_dvd ψ (Nat.dvd_mul_left r q) u
  rw [MulChar.mul_apply, hχ, hψ, hq, hr]

/--
Inputs: a positive modulus `q`, a Dirichlet character modulo `q`, and a natural frequency `n`.

Definition: the Gauss sum over unit residues, with additive phase given by the natural product
`n * a.val`, reduced modulo `q`.

Role: provides the finite unit-group form of the Gauss sum used in CRT factorization.
-/
noncomputable def unitGaussSum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  ∑ a : (ZMod q)ˣ, χ (a : ZMod q) * ZMod.stdAddChar ((n * (a : ZMod q).val : ℕ) : ZMod q)

/--
Inputs: a nonzero modulus `q`, a Dirichlet character modulo `q`, and a natural frequency `n`.

Claim: the unit-restricted Gauss sum equals the ordinary Gauss sum with the additive character
shifted by `n`.

Proof: reindex units as the subtype of unit residues, split the full residue sum into units and
nonunits, and use that a Dirichlet character vanishes on nonunits.

Role: lets CRT factorizations of unit sums feed directly into the standard Gauss sum API.
-/
theorem unitGaussSum_eq_gaussSum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (n : ℕ) :
    unitGaussSum χ n = gaussSum χ (ZMod.stdAddChar.mulShift (n : ZMod q)) := by
  classical
  let f : ZMod q → ℂ := fun a => χ a * ZMod.stdAddChar ((n : ZMod q) * a)
  let e : (ZMod q)ˣ ≃ { a : ZMod q // IsUnit a } :=
    { toFun := fun u => ⟨u, u.isUnit⟩
      invFun := fun a => a.2.unit
      left_inv := fun u => by
        apply Units.ext; rfl
      right_inv := fun a => by
        apply Subtype.ext; rfl }
  calc
    unitGaussSum χ n = ∑ a : { a : ZMod q // IsUnit a }, f a := by
      unfold unitGaussSum
      exact
        Fintype.sum_equiv e _ _
          (fun u => by
            change
              χ (u : ZMod q) * ZMod.stdAddChar ((n * (u : ZMod q).val : ℕ) : ZMod q) =
                χ (u : ZMod q) * ZMod.stdAddChar ((n : ZMod q) * (u : ZMod q))
            simp only [Nat.cast_mul, ZMod.natCast_zmod_val])
    _ = ∑ a : ZMod q, f a := by
      rw [← Fintype.sum_subtype_add_sum_subtype (fun a : ZMod q => IsUnit a) f]
      have hzero : (∑ a : { a : ZMod q // ¬IsUnit a }, f a) = 0 := by
        apply Finset.sum_eq_zero
        intro a ha
        simp only [f, MulChar.map_nonunit χ a.property, zero_mul]
      rw [hzero, add_zero]

/--
Inputs: a positive modulus `r` and a natural frequency `n`.

Claim: the Gauss sum of the principal character modulo `r`, shifted by frequency `n`, equals the
Ramanujan sum `ramanujanSum r n`.

Proof: rewrite the Gauss sum as its sum over units; the principal character is one on each unit,
leaving exactly the defining additive-character sum.

Role: identifies the second CRT Gauss factor in Selberg's Theorem 7A with its Ramanujan weight.
-/
theorem gaussSum_one_eq_ramanujanSum {r : ℕ} [NeZero r] (n : ℕ) :
    gaussSum (1 : DirichletCharacter ℂ r) (ZMod.stdAddChar.mulShift (n : ZMod r)) =
      ramanujanSum r n := by
  rw [← unitGaussSum_eq_gaussSum]
  unfold unitGaussSum ramanujanSum
  apply Finset.sum_congr rfl
  intro u hu
  simp only [MulChar.one_apply u.isUnit, one_mul, Nat.cast_mul, ZMod.natCast_zmod_val]

/--
Inputs: coprime positive moduli `q,r`, Dirichlet characters modulo each modulus, and a natural
frequency `n`.

Claim: the unit Gauss sum for the product of the two level-raised characters modulo `q*r` equals
the product of the component unit Gauss sums, multiplied by the character values at the opposite
moduli.

Proof: reindex the units modulo `q*r` through CRT, factor the additive phase, then reindex each
component by multiplication by the inverse of the opposite modulus.

Role: is the CRT Gauss-sum factorization needed to pass the weighted character expression in
Selberg's Theorem 7A to separate moduli.
-/
theorem unitGaussSum_changeLevel_mul_crt {q r : ℕ} [NeZero q] [NeZero r] (h : Nat.Coprime q r)
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) (n : ℕ) :
    unitGaussSum
        (DirichletCharacter.changeLevel (Nat.dvd_mul_right q r) χ *
          DirichletCharacter.changeLevel (Nat.dvd_mul_left r q) ψ)
        n =
      (χ (((ZMod.isUnit_iff_coprime r q).2 h.symm).unit : ZMod q) * unitGaussSum χ n) *
        (ψ (((ZMod.isUnit_iff_coprime q r).2 h).unit : ZMod r) * unitGaussSum ψ n) := by
  classical
  let ur : (ZMod q)ˣ := (ZMod.isUnit_iff_coprime r q).2 h.symm |>.unit
  let uq : (ZMod r)ˣ := (ZMod.isUnit_iff_coprime q r).2 h |>.unit
  let e : (ZMod (q * r))ˣ ≃* (ZMod q)ˣ × (ZMod r)ˣ :=
    (Units.mapEquiv (ZMod.chineseRemainder h).toMulEquiv).trans MulEquiv.prodUnits
  have hq :
    (∑ a : (ZMod q)ˣ,
        χ (a : ZMod q) *
          ZMod.stdAddChar ((n * (((ur⁻¹ : (ZMod q)ˣ) : ZMod q) * (a : ZMod q)).val : ℕ) : ZMod q)) =
      χ (ur : ZMod q) * unitGaussSum χ n := by
    calc
      _ =
          ∑ a : (ZMod q)ˣ,
            χ ((ur * a : (ZMod q)ˣ) : ZMod q) *
              ZMod.stdAddChar ((n * (a : ZMod q).val : ℕ) : ZMod q) :=
        by
        exact
          Fintype.sum_equiv (Equiv.mulLeft ur⁻¹) _ _
            (fun a => by simp only [Equiv.coe_mulLeft, mul_inv_cancel_left, Units.val_mul])
      _ = χ (ur : ZMod q) * unitGaussSum χ n := by
        rw [unitGaussSum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a ha
        rw [Units.val_mul, map_mul]
        simp only [mul_assoc, Nat.cast_mul, ZMod.natCast_zmod_val]
  have hr :
    (∑ b : (ZMod r)ˣ,
        ψ (b : ZMod r) *
          ZMod.stdAddChar ((n * (((uq⁻¹ : (ZMod r)ˣ) : ZMod r) * (b : ZMod r)).val : ℕ) : ZMod r)) =
      ψ (uq : ZMod r) * unitGaussSum ψ n := by
    calc
      _ =
          ∑ b : (ZMod r)ˣ,
            ψ ((uq * b : (ZMod r)ˣ) : ZMod r) *
              ZMod.stdAddChar ((n * (b : ZMod r).val : ℕ) : ZMod r) :=
        by
        exact
          Fintype.sum_equiv (Equiv.mulLeft uq⁻¹) _ _
            (fun b => by simp only [Equiv.coe_mulLeft, mul_inv_cancel_left, Units.val_mul])
      _ = ψ (uq : ZMod r) * unitGaussSum ψ n := by
        rw [unitGaussSum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b hb
        rw [Units.val_mul, map_mul]
        simp only [mul_assoc, Nat.cast_mul, ZMod.natCast_zmod_val]
  calc
    unitGaussSum
          (DirichletCharacter.changeLevel (Nat.dvd_mul_right q r) χ *
            DirichletCharacter.changeLevel (Nat.dvd_mul_left r q) ψ)
          n =
        ∑ a : (ZMod q)ˣ,
          ∑ b : (ZMod r)ˣ,
            χ (a : ZMod q) * ZMod.stdAddChar ((n * (ur⁻¹ * (a : ZMod q)).val : ℕ) : ZMod q) *
              (ψ (b : ZMod r) * ZMod.stdAddChar ((n * (uq⁻¹ * (b : ZMod r)).val : ℕ) : ZMod r)) :=
      by
      unfold unitGaussSum
      rw [sum_units_zmod_mul_coprime h]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      rw [changeLevel_mul_apply_crt_units h χ ψ a b]
      simp only [Nat.cast_mul, ZMod.natCast_zmod_val]
      have huval : (e.symm (a, b) : ZMod (q * r)) = (ZMod.chineseRemainder h).symm (a, b) := rfl
      rw [huval]
      change
        χ (a : ZMod q) * ψ (b : ZMod r) *
            ZMod.stdAddChar ((n : ZMod (q * r)) * ((ZMod.chineseRemainder h).symm (a, b))) =
          χ (a : ZMod q) *
            ZMod.stdAddChar ((n : ZMod q) * (((ur⁻¹ : (ZMod q)ˣ) : ZMod q) * (a : ZMod q))) *
            (ψ (b : ZMod r) *
              ZMod.stdAddChar ((n : ZMod r) * (((uq⁻¹ : (ZMod r)ˣ) : ZMod r) * (b : ZMod r))))
      rw [stdAddChar_mul_chineseRemainder_symm h (a : ZMod q) (b : ZMod r) n]
      simp only [Nat.cast_mul, ZMod.natCast_zmod_val]
      rw [show
          (n : ZMod q) * (((ur⁻¹ : (ZMod q)ˣ) : ZMod q) * (a : ZMod q)) =
            (n : ZMod q) * (a : ZMod q) * ((ur⁻¹ : (ZMod q)ˣ) : ZMod q)
          by ring]
      rw [show
          (n : ZMod r) * (((uq⁻¹ : (ZMod r)ˣ) : ZMod r) * (b : ZMod r)) =
            (n : ZMod r) * (b : ZMod r) * ((uq⁻¹ : (ZMod r)ˣ) : ZMod r)
          by ring]
      ring
    _ =
        (∑ a : (ZMod q)ˣ,
            χ (a : ZMod q) *
              ZMod.stdAddChar
                ((n * (((ur⁻¹ : (ZMod q)ˣ) : ZMod q) * (a : ZMod q)).val : ℕ) : ZMod q)) *
          (∑ b : (ZMod r)ˣ,
            ψ (b : ZMod r) *
              ZMod.stdAddChar
                ((n * (((uq⁻¹ : (ZMod r)ˣ) : ZMod r) * (b : ZMod r)).val : ℕ) : ZMod r)) :=
      by rw [← Fintype.sum_mul_sum]
    _ = _ := by rw [hq, hr]

/--
Inputs: coprime positive moduli `q,r`, Dirichlet characters modulo each modulus, and a natural
frequency `n`.

Claim: the Gauss sum of the product of the level-raised characters factors into Gauss sums at
`q` and `r`, with the corresponding opposite-modulus character factors.

Proof: rewrite each ordinary Gauss sum as its unit-restricted form and apply the CRT factorization.

Role: gives the standard Gauss-sum interface for the weighted character estimates used in
Selberg's Theorem 7A.
-/
theorem gaussSum_changeLevel_mul_crt {q r : ℕ} [NeZero q] [NeZero r] (h : Nat.Coprime q r)
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) (n : ℕ) :
    gaussSum
        (DirichletCharacter.changeLevel (Nat.dvd_mul_right q r) χ *
          DirichletCharacter.changeLevel (Nat.dvd_mul_left r q) ψ)
        (ZMod.stdAddChar.mulShift (n : ZMod (q * r))) =
      (χ (((ZMod.isUnit_iff_coprime r q).2 h.symm).unit : ZMod q) *
          gaussSum χ (ZMod.stdAddChar.mulShift (n : ZMod q))) *
        (ψ (((ZMod.isUnit_iff_coprime q r).2 h).unit : ZMod r) *
          gaussSum ψ (ZMod.stdAddChar.mulShift (n : ZMod r))) := by
  rw [← unitGaussSum_eq_gaussSum, unitGaussSum_changeLevel_mul_crt h χ ψ n,
    unitGaussSum_eq_gaussSum, unitGaussSum_eq_gaussSum]

/--
Inputs: coprime positive moduli `q,r`, a Dirichlet character modulo `q`, and a natural frequency.

Claim: the Gauss sum modulo `q*r` of the product of the raised character and the raised principal
character is the component Gauss sum modulo `q` times `ramanujanSum r n`, with the CRT unit factor.

Proof: specialize `gaussSum_changeLevel_mul_crt` to the principal character modulo `r` and rewrite
its shifted Gauss sum using `gaussSum_one_eq_ramanujanSum`.

Role: gives the explicit Ramanujan-weighted Gauss identity required to turn primitive-character
sums into the weighted family in Selberg's Theorem 7A.
-/
theorem gaussSum_changeLevel_mul_principal_crt {q r : ℕ} [NeZero q] [NeZero r] (h : Nat.Coprime q r)
    (χ : DirichletCharacter ℂ q) (n : ℕ) :
    gaussSum
        (DirichletCharacter.changeLevel (Nat.dvd_mul_right q r) χ *
          DirichletCharacter.changeLevel (Nat.dvd_mul_left r q) (1 : DirichletCharacter ℂ r))
        (ZMod.stdAddChar.mulShift (n : ZMod (q * r))) =
      (χ (((ZMod.isUnit_iff_coprime r q).2 h.symm).unit : ZMod q) *
          gaussSum χ (ZMod.stdAddChar.mulShift (n : ZMod q))) *
        ramanujanSum r n := by
  have hu : IsUnit (q : ZMod r) := (ZMod.isUnit_iff_coprime q r).2 h
  have htriv : (1 : DirichletCharacter ℂ r) (hu.unit : ZMod r) = 1 :=
    MulChar.one_apply hu.unit.isUnit
  rw [gaussSum_changeLevel_mul_crt h χ (1 : DirichletCharacter ℂ r) n, gaussSum_one_eq_ramanujanSum,
    htriv, one_mul]

/--
Inputs: coprime positive moduli `q,r`, a primitive character modulo `q`, and a natural frequency.

Claim: the unit Gauss sum modulo `q*r` of the raised inverse character times the raised principal
character equals `χ(n) * ramanujanSum r n`, multiplied by `χ⁻¹(r) * gaussSum χ⁻¹`.

Proof: factor the unit Gauss sum through CRT, identify the principal-character factor with the
Ramanujan sum, and apply the primitive Gauss-sum shift identity to `χ⁻¹`.

Role: supplies the frequency-by-frequency identity used to transform Ramanujan-weighted
primitive-character polynomials into additive sums modulo `q*r`.
-/
theorem unitGaussSum_changeLevel_mul_principal_of_primitive {q r : ℕ} [NeZero q] [NeZero r]
    (h : Nat.Coprime q r) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (n : ℕ) :
    unitGaussSum
        (DirichletCharacter.changeLevel (Nat.dvd_mul_right q r) χ⁻¹ *
          DirichletCharacter.changeLevel (Nat.dvd_mul_left r q) (1 : DirichletCharacter ℂ r))
        n =
      (χ⁻¹ (r : ZMod q) * gaussSum χ⁻¹ ZMod.stdAddChar) * (χ (n : ZMod q) * ramanujanSum r n) := by
  have hχinv : χ⁻¹.IsPrimitive := by
    rw [DirichletCharacter.isPrimitive_def] at hχ ⊢
    rw [DirichletCharacter.conductor_inv]
    exact hχ
  have huq : IsUnit (q : ZMod r) := (ZMod.isUnit_iff_coprime q r).2 h
  have htriv : (1 : DirichletCharacter ℂ r) (huq.unit : ZMod r) = 1 :=
    MulChar.one_apply huq.unit.isUnit
  have hur : IsUnit (r : ZMod q) := (ZMod.isUnit_iff_coprime r q).2 h.symm
  have hurval : (hur.unit : ZMod q) = (r : ZMod q) := hur.unit_spec
  rw [unitGaussSum_changeLevel_mul_crt h χ⁻¹ (1 : DirichletCharacter ℂ r) n,
    unitGaussSum_eq_gaussSum, unitGaussSum_eq_gaussSum, gaussSum_one_eq_ramanujanSum, htriv,
    one_mul, gaussSum_mulShift_of_isPrimitive ZMod.stdAddChar hχinv (n : ZMod q), inv_inv, hurval]
  ring

/--
Inputs: coprime positive moduli `q,r`, a primitive character modulo `q`, a finite index set, and
complex coefficients.

Claim: the Ramanujan-weighted primitive-character polynomial, multiplied by its Gauss normalization,
equals the additive Fourier polynomial over unit residues modulo `q*r`, weighted by the raised
inverse character.

Proof: apply `unitGaussSum_changeLevel_mul_principal_of_primitive` termwise, expand the unit Gauss
sums, exchange the finite sums, and factor the character value out of each inner polynomial.

Role: gives the polynomial form of Selberg's Theorem 7A for one coprime modulus pair.
-/
theorem primitive_ramanujan_weighted_polynomial_additive_transform {q r : ℕ} [NeZero q] [NeZero r]
    (h : Nat.Coprime q r) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (S : Finset ℕ)
    (a : ℕ → ℂ) :
    (χ⁻¹ (r : ZMod q) * gaussSum χ⁻¹ ZMod.stdAddChar) *
        (∑ n ∈ S, a n * (χ (n : ZMod q) * ramanujanSum r n)) =
      ∑ b : (ZMod (q * r))ˣ,
        (DirichletCharacter.changeLevel (Nat.dvd_mul_right q r) χ⁻¹ *
              DirichletCharacter.changeLevel (Nat.dvd_mul_left r q) (1 : DirichletCharacter ℂ r))
            (b : ZMod (q * r)) *
          (∑ n ∈ S, a n * ZMod.stdAddChar ((n * (b : ZMod (q * r)).val : ℕ) : ZMod (q * r))) := by
  let χr :=
    DirichletCharacter.changeLevel (Nat.dvd_mul_right q r) χ⁻¹ *
      DirichletCharacter.changeLevel (Nat.dvd_mul_left r q) (1 : DirichletCharacter ℂ r)
  calc
    _ =
        ∑ n ∈ S,
          a n *
            ((χ⁻¹ (r : ZMod q) * gaussSum χ⁻¹ ZMod.stdAddChar) *
              (χ (n : ZMod q) * ramanujanSum r n)) :=
      by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _ = ∑ n ∈ S, a n * unitGaussSum χr n := by
      apply Finset.sum_congr rfl
      intro n hn
      dsimp [χr]
      rw [unitGaussSum_changeLevel_mul_principal_of_primitive h χ hχ n]
    _ =
        ∑ n ∈ S,
          a n *
            ∑ b : (ZMod (q * r))ˣ,
              χr (b : ZMod (q * r)) *
                ZMod.stdAddChar ((n * (b : ZMod (q * r)).val : ℕ) : ZMod (q * r)) :=
      by
      apply Finset.sum_congr rfl
      intro n hn
      rw [unitGaussSum]
    _ =
        ∑ n ∈ S,
          ∑ b : (ZMod (q * r))ˣ,
            a n *
              (χr (b : ZMod (q * r)) *
                ZMod.stdAddChar ((n * (b : ZMod (q * r)).val : ℕ) : ZMod (q * r))) :=
      by
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.mul_sum]
    _ =
        ∑ b : (ZMod (q * r))ˣ,
          ∑ n ∈ S,
            a n *
              (χr (b : ZMod (q * r)) *
                ZMod.stdAddChar ((n * (b : ZMod (q * r)).val : ℕ) : ZMod (q * r))) :=
      by rw [Finset.sum_comm]
    _ =
        ∑ b : (ZMod (q * r))ˣ,
          χr (b : ZMod (q * r)) *
            (∑ n ∈ S, a n * ZMod.stdAddChar ((n * (b : ZMod (q * r)).val : ℕ) : ZMod (q * r))) :=
      by
      apply Finset.sum_congr rfl
      intro b hb
      calc
        _ =
            ∑ n ∈ S,
              χr (b : ZMod (q * r)) *
                (a n * ZMod.stdAddChar ((n * (b : ZMod (q * r)).val : ℕ) : ZMod (q * r))) :=
          by
          apply Finset.sum_congr rfl
          intro n hn
          ring
        _ = _ := by rw [← Finset.mul_sum]

/--
Inputs: a modulus `q` greater than one, a positive coprime modulus `r`, a primitive character
modulo `q`, a finite index set, and complex coefficients.

Claim: `q` times the squared norm of the Ramanujan-weighted character polynomial equals the
squared norm of its additive transform over units modulo `q*r`.

Proof: take squared norms in `primitive_ramanujan_weighted_polynomial_additive_transform`; the
normalizing factor has squared norm `q` by the primitive Gauss-sum norm identity and unit norm.

Role: gives the exact fixed-character identity needed to sum Selberg's Theorem 7A over primitive
characters.
-/
theorem primitive_ramanujan_weighted_polynomial_normSq_eq {q r : ℕ} [NeZero q] [NeZero r]
    (hq : 1 < q) (h : Nat.Coprime q r) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (S : Finset ℕ) (a : ℕ → ℂ) :
    (q : ℝ) * Complex.normSq (∑ n ∈ S, a n * (χ (n : ZMod q) * ramanujanSum r n)) =
      Complex.normSq
        (∑ b : (ZMod (q * r))ˣ,
          (DirichletCharacter.changeLevel (Nat.dvd_mul_right q r) χ⁻¹ *
                DirichletCharacter.changeLevel (Nat.dvd_mul_left r q) (1 : DirichletCharacter ℂ r))
              (b : ZMod (q * r)) *
            (∑ n ∈ S,
              a n * ZMod.stdAddChar ((n * (b : ZMod (q * r)).val : ℕ) : ZMod (q * r)))) := by
  have hχinv : χ⁻¹.IsPrimitive := by
    rw [DirichletCharacter.isPrimitive_def] at hχ ⊢
    rw [DirichletCharacter.conductor_inv]
    exact hχ
  have hur : IsUnit (r : ZMod q) := (ZMod.isUnit_iff_coprime r q).2 h.symm
  have hurval : (hur.unit : ZMod q) = (r : ZMod q) := hur.unit_spec
  have hchar : Complex.normSq (χ⁻¹ (r : ZMod q)) = 1 := by
    rw [← hurval, Complex.normSq_eq_norm_sq, DirichletCharacter.unit_norm_eq_one χ⁻¹ hur.unit]
    norm_num only
  have hgauss := primitive_gaussSum_normSq_eq_modulus hq χ⁻¹ hχinv
  have hconstant : Complex.normSq (χ⁻¹ (r : ZMod q) * gaussSum χ⁻¹ ZMod.stdAddChar) = q := by
    rw [Complex.normSq_mul, hchar, hgauss]
    norm_num only [one_mul]
  have htransform := primitive_ramanujan_weighted_polynomial_additive_transform h χ hχ S a
  calc
    _ =
        Complex.normSq (χ⁻¹ (r : ZMod q) * gaussSum χ⁻¹ ZMod.stdAddChar) *
          Complex.normSq (∑ n ∈ S, a n * (χ (n : ZMod q) * ramanujanSum r n)) :=
      by rw [hconstant]
    _ = _ := by
      rw [← Complex.normSq_mul]
      exact congrArg Complex.normSq htransform

/--
Inputs: two moduli dividing a positive common level, and primitive Dirichlet characters at those
moduli.

Claim: if the characters become equal after lifting to the common level, then their moduli agree.

Proof: conductor invariance under level change identifies both primitive conductors with the
respective original moduli.

Role: proves disjointness of lifted primitive-character images from distinct conductors.
-/
theorem primitive_level_lifts_equal_imply_moduli_eq {q q' h : ℕ} [NeZero h] (hq : q ∣ h)
    (hq' : q' ∣ h) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (ψ : DirichletCharacter ℂ q')
    (hψ : ψ.IsPrimitive)
    (heq : DirichletCharacter.changeLevel hq χ = DirichletCharacter.changeLevel hq' ψ) :
    q = q' := by
  have hcond := congrArg (fun ξ : DirichletCharacter ℂ h => ξ.conductor) heq
  rw [DirichletCharacter.conductor_changeLevel, hχ, DirichletCharacter.conductor_changeLevel,
    hψ] at hcond
  exact hcond

/--
Inputs: two primitive characters whose inverse characters are lifted to a common positive level.

Claim: equality of the lifted inverse characters forces equality of their original moduli.

Proof: inversion preserves the conductor, so the preceding conductor argument applies to both
inverse characters.

Role: separates the product-modulus character images used by the Ramanujan-weighted Parseval
identity.
-/
theorem primitive_inverse_level_lifts_equal_imply_moduli_eq {q q' h : ℕ} [NeZero h] (hq : q ∣ h)
    (hq' : q' ∣ h) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (ψ : DirichletCharacter ℂ q')
    (hψ : ψ.IsPrimitive)
    (heq : DirichletCharacter.changeLevel hq χ⁻¹ = DirichletCharacter.changeLevel hq' ψ⁻¹) :
    q = q' := by
  have hχinv : χ⁻¹.IsPrimitive := by
    rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]
    exact hχ
  have hψinv : ψ⁻¹.IsPrimitive := by
    rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]
    exact hψ
  exact primitive_level_lifts_equal_imply_moduli_eq hq hq' χ⁻¹ hχinv ψ⁻¹ hψinv heq

/--
Inputs: distinct moduli dividing a positive common level.

Claim: the images of their primitive characters under level raising are disjoint.

Proof: any common image character would have both moduli as its conductor, by primitivity and
conductor invariance under level raising.

Role: ensures that Parseval counts each lifted primitive character only once at a fixed product
modulus.
-/
theorem primitive_levelLift_images_disjoint_of_ne {h q q' : ℕ} [NeZero h]
    [DecidableEq (DirichletCharacter ℂ h)] (hq : q ∣ h) (hq' : q' ∣ h) (hne : q ≠ q') :
    Disjoint
      ((primitiveDirichletCharacterSet q).image (fun χ => DirichletCharacter.changeLevel hq χ⁻¹))
      ((primitiveDirichletCharacterSet q').image
        (fun χ => DirichletCharacter.changeLevel hq' χ⁻¹)) := by
  classical
  apply Finset.disjoint_left.mpr
  intro ψ hψ hψ'
  rcases Finset.mem_image.mp hψ with ⟨χ, hχ, hχψ⟩
  rcases Finset.mem_image.mp hψ' with ⟨χ', hχ', hχ'ψ⟩
  have hχprim : χ.IsPrimitive := by
    simpa only [primitiveDirichletCharacterSet, Finset.mem_filter, Finset.mem_univ, true_and] using
      hχ
  have hχ'prim : χ'.IsPrimitive := by
    simpa only [primitiveDirichletCharacterSet, Finset.mem_filter, Finset.mem_univ, true_and] using
      hχ'
  have hlift : DirichletCharacter.changeLevel hq χ⁻¹ = DirichletCharacter.changeLevel hq' χ'⁻¹ :=
    hχψ.trans hχ'ψ.symm
  have hmod := primitive_inverse_level_lifts_equal_imply_moduli_eq hq hq' χ hχprim χ' hχ'prim hlift
  exact hne hmod

/--
Inputs: a modulus `q`, a positive common level `h`, and a divisibility witness `q ∣ h`.

Definition: the finite image of primitive characters modulo `q` under level raising to `h`, with
characters inverted as in the Ramanujan-weighted additive transform.

Role: packages the conductor-indexed image sets used in collective Parseval estimates.
-/
noncomputable def primitiveCharacterLevelLiftImage {q h : ℕ} [NeZero h]
    [DecidableEq (DirichletCharacter ℂ h)] (hq : q ∣ h) : Finset (DirichletCharacter ℂ h) :=
  (primitiveDirichletCharacterSet q).image (fun χ => DirichletCharacter.changeLevel hq χ⁻¹)

/--
Inputs: a finite set of moduli dividing a positive common level.

Claim: their primitive-character level-lift images are pairwise disjoint.

Proof: distinct moduli give disjoint images by `primitive_levelLift_images_disjoint_of_ne`.

Role: allows the image sums for all selected conductors to be joined before applying Parseval.
-/
theorem primitiveCharacterLevelLiftImages_pairwiseDisjoint {h : ℕ} [NeZero h]
    [DecidableEq (DirichletCharacter ℂ h)] (Q : Finset ℕ) (hQ : ∀ q, q ∣ h) :
    (Q : Set ℕ).PairwiseDisjoint
      (fun q => (primitiveCharacterLevelLiftImage (hQ q) : Set (DirichletCharacter ℂ h))) := by
  rw [Set.pairwiseDisjoint_iff]
  intro q hq q' hq' hinter
  by_contra hne
  rcases hinter with ⟨ψ, hψ⟩
  rw [Set.mem_inter_iff] at hψ
  rcases hψ with ⟨hψq, hψq'⟩
  have hd := primitive_levelLift_images_disjoint_of_ne (hQ q) (hQ q') hne
  change ψ ∈ primitiveCharacterLevelLiftImage (hQ q) at hψq
  change ψ ∈ primitiveCharacterLevelLiftImage (hQ q') at hψq'
  exact (Finset.disjoint_left.mp hd hψq) hψq'

/--
Inputs: a finite set of moduli dividing a positive common level and a real-valued weight on its
Dirichlet characters.

Claim: summing over the union of the primitive-character lift images equals the sum of their
individual image sums.

Proof: apply the finite disjoint-union sum identity to the pairwise-disjoint image theorem above.

Role: collects all primitive-conductor contributions before one application of Parseval.
-/
theorem sum_primitiveCharacterLevelLiftImage_biUnion {h : ℕ} [NeZero h]
    [DecidableEq (DirichletCharacter ℂ h)] (Q : Finset ℕ) (hQ : ∀ q, q ∣ h)
    (f : DirichletCharacter ℂ h → ℝ) :
    (∑ ψ ∈ Q.biUnion fun q => primitiveCharacterLevelLiftImage (hQ q), f ψ) =
      ∑ q ∈ Q, ∑ ψ ∈ primitiveCharacterLevelLiftImage (hQ q), f ψ := by
  exact
    Finset.sum_biUnion
      (Finset.pairwiseDisjoint_coe.mp
        (primitiveCharacterLevelLiftImages_pairwiseDisjoint (h := h) Q hQ))

/--
Inputs: a finite set of moduli dividing a positive common level and a complex-valued function on
its Dirichlet characters.

Claim: the sum of squared norms over all primitive-character lift images is bounded by the sum over
all characters at the common level.

Proof: join the pairwise-disjoint images, then enlarge their union to the full character set.

Role: supplies the one-Parseval upper bound after conductor-indexed images have been aggregated.
-/
theorem sum_primitiveCharacterLevelLiftImage_normSq_le_all {h : ℕ} [NeZero h]
    [DecidableEq (DirichletCharacter ℂ h)] (Q : Finset ℕ) (hQ : ∀ q, q ∣ h)
    (f : DirichletCharacter ℂ h → ℂ) :
    (∑ q ∈ Q, ∑ ψ ∈ primitiveCharacterLevelLiftImage (hQ q), Complex.normSq (f ψ)) ≤
      ∑ ψ : DirichletCharacter ℂ h, Complex.normSq (f ψ) := by
  rw [← sum_primitiveCharacterLevelLiftImage_biUnion (h := h) Q hQ (fun ψ => Complex.normSq (f ψ))]
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
  intro ψ hψ hψnot
  exact Complex.normSq_nonneg (f ψ)

/--
Inputs: a finite set of moduli dividing a positive common level and a complex-valued function on
its Dirichlet characters.

Claim: the sum over the attached primitive-character lift images is bounded by the sum over all
characters at the common level.

Proof: the attached images are pairwise disjoint by conductor uniqueness, so their union is a
subset of the full character set.

Role: supports collective Parseval when divisibility is known only for members of the finite set.
-/
theorem sum_primitiveCharacterLevelLiftImage_normSq_le_all_attached {h : ℕ} [NeZero h]
    [DecidableEq (DirichletCharacter ℂ h)] (Q : Finset ℕ) (hQ : ∀ q, q ∈ Q → q ∣ h)
    (f : DirichletCharacter ℂ h → ℂ) :
    (∑ q ∈ Q.attach,
        ∑ ψ ∈ primitiveCharacterLevelLiftImage (hQ q.val q.property), Complex.normSq (f ψ)) ≤
      ∑ ψ : DirichletCharacter ℂ h, Complex.normSq (f ψ) := by
  classical
  have hdisjoint :
    (Q.attach : Set { q : ℕ // q ∈ Q }).PairwiseDisjoint
      (fun q =>
        (primitiveCharacterLevelLiftImage (hQ q.val q.property) :
          Set (DirichletCharacter ℂ h))) := by
    rw [Set.pairwiseDisjoint_iff]
    intro q hq q' hq' hinter
    by_contra hne
    have hval : q.val ≠ q'.val := by
      intro heq
      apply hne
      exact Subtype.ext heq
    rcases hinter with ⟨ψ, hψ⟩
    rw [Set.mem_inter_iff] at hψ
    rcases hψ with ⟨hψq, hψq'⟩
    have hd :=
      primitive_levelLift_images_disjoint_of_ne (hQ q.val q.property) (hQ q'.val q'.property) hval
    change ψ ∈ primitiveCharacterLevelLiftImage (hQ q.val q.property) at hψq
    change ψ ∈ primitiveCharacterLevelLiftImage (hQ q'.val q'.property) at hψq'
    exact (Finset.disjoint_left.mp hd hψq) hψq'
  rw [← Finset.sum_biUnion (Finset.pairwiseDisjoint_coe.mp hdisjoint)]
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
  intro ψ hψ hψnot
  exact Complex.normSq_nonneg (f ψ)

/--
Inputs: positive moduli `q,r` and a primitive Dirichlet character modulo `q`.

Claim: the character on the product modulus used in the Ramanujan-weighted additive transform has
conductor `q`.

Proof: the lifted trivial character modulo `r` is trivial at level `q*r`; conductor invariance
under level change then reduces the claim to primitivity of the original character.

Role: distinguishes the images arising from different primitive conductors when aggregating
Parseval over a fixed product modulus.
-/
theorem primitive_ramanujan_weighted_levelLift_conductor_eq {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) :
    (DirichletCharacter.changeLevel (Nat.dvd_mul_right q r) χ⁻¹ *
          DirichletCharacter.changeLevel (Nat.dvd_mul_left r q)
            (1 : DirichletCharacter ℂ r)).conductor =
      q := by
  rw [DirichletCharacter.changeLevel_one, mul_one, DirichletCharacter.conductor_changeLevel,
    DirichletCharacter.conductor_inv]
  exact hχ

/--
Inputs: coprime moduli `q,r`, a finite polynomial, and coefficients in `ℂ`.

Claim: after lifting each primitive character modulo `q` to the product modulus, the sum of the
Ramanujan-weighted character mean squares equals the additive-polynomial norm-square sum over the
image of those lifted characters.

Proof: use the fixed-character norm identity, prove that the lift is injective by cancellation
and injectivity of change of level, and reindex the finite sum by the image.

Role: isolates the primitive-character contribution before bounding it by Parseval over all
characters modulo `q*r`.
-/
theorem primitive_ramanujan_weighted_polynomial_image_normSq_eq {q r : ℕ} [NeZero q] [NeZero r]
    [DecidableEq (DirichletCharacter ℂ (q * r))] (hq : 1 < q) (h : Nat.Coprime q r) (S : Finset ℕ)
    (a : ℕ → ℂ) :
    let F : DirichletCharacter ℂ q → DirichletCharacter ℂ (q * r) := fun χ =>
      DirichletCharacter.changeLevel (Nat.dvd_mul_right q r) χ⁻¹ *
        DirichletCharacter.changeLevel (Nat.dvd_mul_left r q) (1 : DirichletCharacter ℂ r)
    let A : DirichletCharacter ℂ (q * r) → ℂ := fun ψ =>
      ∑ b : (ZMod (q * r))ˣ,
        ψ b * (∑ n ∈ S, a n * ZMod.stdAddChar ((n * (b : ZMod (q * r)).val : ℕ) : ZMod (q * r)))
    (q : ℝ) *
        ∑ χ ∈ primitiveDirichletCharacterSet q,
          Complex.normSq (∑ n ∈ S, a n * (χ (n : ZMod q) * ramanujanSum r n)) =
      ∑ ψ ∈ (primitiveDirichletCharacterSet q).image F, Complex.normSq (A ψ) := by
  classical
  let F : DirichletCharacter ℂ q → DirichletCharacter ℂ (q * r) := fun χ =>
    DirichletCharacter.changeLevel (Nat.dvd_mul_right q r) χ⁻¹ *
      DirichletCharacter.changeLevel (Nat.dvd_mul_left r q) (1 : DirichletCharacter ℂ r)
  let A : DirichletCharacter ℂ (q * r) → ℂ := fun ψ =>
    ∑ b : (ZMod (q * r))ˣ,
      ψ b * (∑ n ∈ S, a n * ZMod.stdAddChar ((n * (b : ZMod (q * r)).val : ℕ) : ZMod (q * r)))
  have hF : Function.Injective F := by
    intro χ ψ hχψ
    have hcancel :
      DirichletCharacter.changeLevel (Nat.dvd_mul_right q r) χ⁻¹ =
        DirichletCharacter.changeLevel (Nat.dvd_mul_right q r) ψ⁻¹ := by
      exact mul_right_cancel hχψ
    have hinv : χ⁻¹ = ψ⁻¹ :=
      DirichletCharacter.changeLevel_injective (Nat.dvd_mul_right q r) hcancel
    exact inv_injective hinv
  rw [Finset.mul_sum]
  calc
    _ = ∑ χ ∈ primitiveDirichletCharacterSet q, Complex.normSq (A (F χ)) := by
      apply Finset.sum_congr rfl
      intro χ hχ
      have hprim : χ.IsPrimitive := by
        simpa only [primitiveDirichletCharacterSet, Finset.mem_filter, Finset.mem_univ,
          true_and] using hχ
      exact primitive_ramanujan_weighted_polynomial_normSq_eq hq h χ hprim S a
    _ = ∑ ψ ∈ (primitiveDirichletCharacterSet q).image F, Complex.normSq (A ψ) := by
      symm
      exact Finset.sum_image hF.injOn

/--
Inputs: coprime positive moduli `q,r` with `q > 1`, a finite polynomial, and complex
coefficients.

Claim: the Ramanujan-weighted primitive-character mean square equals the additive-transform
norm-square sum over the primitive-character level-lift image modulo `q*r`.

Proof: simplify the lift of the trivial character modulo `r` in
`primitive_ramanujan_weighted_polynomial_image_normSq_eq`.

Role: identifies the pair-indexed Ramanujan contribution with the conductor-indexed image used by
the collective Parseval estimate.
-/
theorem primitive_ramanujan_weighted_polynomial_levelLiftImage_normSq_eq {q r : ℕ} [NeZero q]
    [NeZero r] [DecidableEq (DirichletCharacter ℂ (q * r))] (hq : 1 < q) (h : Nat.Coprime q r)
    (S : Finset ℕ) (a : ℕ → ℂ) :
    (q : ℝ) *
        ∑ χ ∈ primitiveDirichletCharacterSet q,
          Complex.normSq (∑ n ∈ S, a n * (χ (n : ZMod q) * ramanujanSum r n)) =
      ∑ ψ ∈ primitiveCharacterLevelLiftImage (Nat.dvd_mul_right q r),
        Complex.normSq
          (∑ b : (ZMod (q * r))ˣ,
            ψ b * (∑ n ∈ S, a n * ZMod.stdAddChar ((b : ZMod (q * r)) * (n : ZMod (q * r))))) := by
  classical
  have hphase (b : (ZMod (q * r))ˣ) (n : ℕ) :
    ZMod.stdAddChar ((n * (b : ZMod (q * r)).val : ℕ) : ZMod (q * r)) =
      ZMod.stdAddChar ((b : ZMod (q * r)) * (n : ZMod (q * r))) := by
    apply congrArg ZMod.stdAddChar
    rw [Nat.cast_mul, ZMod.natCast_zmod_val]
    exact mul_comm _ _
  have hpoly (ψ : DirichletCharacter ℂ (q * r)) :
    (∑ b : (ZMod (q * r))ˣ,
        ψ b * ∑ n ∈ S, a n * ZMod.stdAddChar ((n * (b : ZMod (q * r)).val : ℕ) : ZMod (q * r))) =
      ∑ b : (ZMod (q * r))ˣ,
        ψ b * ∑ n ∈ S, a n * ZMod.stdAddChar ((b : ZMod (q * r)) * (n : ZMod (q * r))) := by
    simp only [hphase]
  have hbase :
    (q : ℝ) *
        ∑ χ ∈ primitiveDirichletCharacterSet q,
          Complex.normSq (∑ n ∈ S, a n * (χ (n : ZMod q) * ramanujanSum r n)) =
      ∑ ψ ∈ primitiveCharacterLevelLiftImage (Nat.dvd_mul_right q r),
        Complex.normSq
          (∑ b : (ZMod (q * r))ˣ,
            ψ b *
              ∑ n ∈ S,
                a n * ZMod.stdAddChar ((n * (b : ZMod (q * r)).val : ℕ) : ZMod (q * r))) := by
    simpa only [primitiveCharacterLevelLiftImage, DirichletCharacter.changeLevel_one, mul_one] using
      primitive_ramanujan_weighted_polynomial_image_normSq_eq hq h S a
  calc
    _ =
        ∑ ψ ∈ primitiveCharacterLevelLiftImage (Nat.dvd_mul_right q r),
          Complex.normSq
            (∑ b : (ZMod (q * r))ˣ,
              ψ b *
                ∑ n ∈ S, a n * ZMod.stdAddChar ((n * (b : ZMod (q * r)).val : ℕ) : ZMod (q * r))) :=
      hbase
    _ = _ := by
      apply Finset.sum_congr rfl
      intro ψ hψ
      exact congrArg Complex.normSq (hpoly ψ)

/--
Inputs: coprime positive moduli `q,r`, a common level `h = q*r`, and a finite polynomial.

Claim: the Ramanujan-weighted primitive-character mean square at `q` equals the additive-transform
norm-square sum over its primitive level-lift image at `h`.

Proof: transport the fixed-product identity along the supplied equality `q*r = h`.

Role: gives a uniform-level form of the pair identity for finite families with fixed product.
-/
theorem primitive_ramanujan_weighted_commonLevelImage_normSq_eq {q r h : ℕ} [NeZero q] [NeZero r]
    [NeZero h] [DecidableEq (DirichletCharacter ℂ h)] (hqr : q * r = h) (hqdiv : q ∣ h) (hq : 1 < q)
    (hcop : Nat.Coprime q r) (S : Finset ℕ) (a : ℕ → ℂ) :
    (q : ℝ) *
        ∑ χ ∈ primitiveDirichletCharacterSet q,
          Complex.normSq (∑ n ∈ S, a n * (χ (n : ZMod q) * ramanujanSum r n)) =
      ∑ ψ ∈ primitiveCharacterLevelLiftImage hqdiv,
        Complex.normSq
          (∑ b : (ZMod h)ˣ,
            ψ b * ∑ n ∈ S, a n * ZMod.stdAddChar ((b : ZMod h) * (n : ZMod h))) := by
  classical
  subst h
  exact primitive_ramanujan_weighted_polynomial_levelLiftImage_normSq_eq hq hcop S a

/--
Inputs: a finite set of residues consisting exactly of the units modulo `q`, a Dirichlet
character modulo `q`, and a complex-valued function on residues.

Claim: summing the character-weighted function over unit elements agrees with summing over the
finite set of unit residues.

Proof: construct the equivalence between units and the subtype of residues in the finite set,
then reindex the finite sum.

Role: converts sums over the unit group into the finite-set form used by character Parseval.
-/
theorem dirichletCharacter_units_sum_eq_finset {q : ℕ} [NeZero q] (S : Finset (ZMod q))
    (hS : ∀ x, x ∈ S ↔ IsUnit x) (χ : DirichletCharacter ℂ q) (f : ZMod q → ℂ) :
    (∑ u : (ZMod q)ˣ, χ u * f u) = ∑ x ∈ S, f x * χ x := by
  classical
  let e : (ZMod q)ˣ ≃ { x : ZMod q // x ∈ S } :=
    { toFun := fun u => ⟨u, (hS u).2 u.isUnit⟩
      invFun := fun x => ((hS x.1).1 x.2).unit
      left_inv := fun u => by
        apply Units.ext
        rfl
      right_inv := fun x => by
        apply Subtype.ext
        exact IsUnit.unit_spec ((hS x.1).1 x.2) }
  calc
    _ = ∑ x : { x : ZMod q // x ∈ S }, χ x.1 * f x.1 := by
      exact Fintype.sum_equiv e _ _ (fun u => rfl)
    _ = ∑ x ∈ S, χ x * f x := by
      exact (Finset.sum_subtype S (fun _ => Iff.rfl) (fun x : ZMod q => χ x * f x)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x hx
      exact mul_comm _ _

/--
Inputs: a positive modulus, a finite set consisting exactly of unit residues, and a complex
function on those residues.

Claim: the sum of squared norms of the character-weighted unit sums equals the totient times the
sum of squared norms of the function on the finite set.

Proof: reindex unit sums over the finite set, apply `dirichletCharacter_parseval`, and convert
the resulting complex identity to real norms.

Role: supplies Parseval for the unit-group polynomial used in the lifted-character estimate.
-/
theorem dirichletCharacter_units_polynomial_parseval {q : ℕ} [NeZero q] (S : Finset (ZMod q))
    (hS : ∀ x, x ∈ S ↔ IsUnit x) (f : ZMod q → ℂ) :
    (∑ χ : DirichletCharacter ℂ q, Complex.normSq (∑ u : (ZMod q)ˣ, χ u * f u)) =
      (Nat.totient q : ℝ) * ∑ x ∈ S, Complex.normSq (f x) := by
  classical
  have hnorm (z : ℂ) : (Complex.normSq z : ℂ) = star z * z := by
    rw [← Complex.mul_conj z]
    exact mul_comm _ _
  have htrans (χ : DirichletCharacter ℂ q) : (∑ u : (ZMod q)ˣ, χ u * f u) = ∑ x ∈ S, f x * χ x :=
    dirichletCharacter_units_sum_eq_finset S hS χ f
  have hS' : ∀ x ∈ S, IsUnit x := by
    intro x hx
    exact (hS x).1 hx
  have hparseval := dirichletCharacter_parseval S hS' f
  have hC :
    ((∑ χ : DirichletCharacter ℂ q, Complex.normSq (∑ u : (ZMod q)ˣ, χ u * f u) : ℝ) : ℂ) =
      (Nat.totient q : ℂ) * ∑ x ∈ S, star (f x) * f x := by
    calc
      _ = ∑ χ : DirichletCharacter ℂ q, star (∑ x ∈ S, f x * χ x) * (∑ x ∈ S, f x * χ x) := by
        rw [Complex.ofReal_sum]
        apply Finset.sum_congr rfl
        intro χ hχ
        rw [htrans χ]
        exact hnorm _
      _ = _ := hparseval
  have hC' :
    ((Nat.totient q * ∑ x ∈ S, Complex.normSq (f x) : ℝ) : ℂ) =
      (Nat.totient q : ℂ) * ∑ x ∈ S, star (f x) * f x := by
    rw [Complex.ofReal_mul, Complex.ofReal_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro x hx
    exact hnorm (f x)
  exact_mod_cast hC.trans hC'.symm

/--
Inputs: a positive common level, a finite set of its divisors, a finite polynomial, and complex
coefficients.

Claim: the sum of squared additive-transform norms over all primitive-character lift images is
bounded by one totient-weighted reduced additive mean square at the common level.

Proof: combine the image-union bound with unit-group character Parseval and the definition of the
reduced additive mean square.

Role: provides the fixed-product-modulus collective Parseval estimate for the pre-sifted large
sieve.
-/
theorem sum_primitiveCharacterLevelLiftImage_additiveParseval_le {h : ℕ} [NeZero h] (hh : 1 < h)
    [DecidableEq (DirichletCharacter ℂ h)] (Q : Finset ℕ) (hQ : ∀ q, q ∣ h) (S : Finset ℕ)
    (a : ℕ → ℂ) :
    (∑ q ∈ Q,
        ∑ ψ ∈ primitiveCharacterLevelLiftImage (hQ q),
          Complex.normSq
            (∑ b : (ZMod h)ˣ,
              ψ b * (∑ n ∈ S, a n * ZMod.stdAddChar ((b : ZMod h) * (n : ZMod h))))) ≤
      (Nat.totient h : ℝ) * reducedAdditivePolynomialMeanSquare h hh S a := by
  classical
  let U : Finset (ZMod h) := Finset.univ.filter fun x => IsUnit x
  let f : ZMod h → ℂ := fun x => ∑ n ∈ S, a n * ZMod.stdAddChar (x * (n : ZMod h))
  let A : DirichletCharacter ℂ h → ℂ := fun ψ => ∑ b : (ZMod h)ˣ, ψ b * f b
  have hU : ∀ x, x ∈ U ↔ IsUnit x := by
    intro x
    simp only [U, Finset.mem_filter, Finset.mem_univ, true_and]
  have hparseval := dirichletCharacter_units_polynomial_parseval U hU f
  have hred : reducedAdditivePolynomialMeanSquare h hh S a = ∑ x ∈ U, Complex.normSq (f x) := by rfl
  calc
    _ ≤ ∑ ψ : DirichletCharacter ℂ h, Complex.normSq (A ψ) := by
      simpa only [A, f] using sum_primitiveCharacterLevelLiftImage_normSq_le_all (h := h) Q hQ A
    _ = _ := by rw [hred, hparseval]

/--
Inputs: a positive common level, a finite set of its divisors with membership-indexed
divisibility proofs, a finite polynomial, and complex coefficients.

Claim: the attached sum of squared additive-transform norms over primitive-character lift images
is bounded by one totient-weighted reduced additive mean square at the common level.

Proof: apply the attached disjoint-image bound and unit-group character Parseval.

Role: supplies the one-Parseval estimate for selected conductor families at a fixed product level.
-/
theorem sum_primitiveCharacterLevelLiftImage_additiveParseval_le_attached {h : ℕ} [NeZero h]
    (hh : 1 < h) [DecidableEq (DirichletCharacter ℂ h)] (Q : Finset ℕ) (hQ : ∀ q, q ∈ Q → q ∣ h)
    (S : Finset ℕ) (a : ℕ → ℂ) :
    (∑ q ∈ Q.attach,
        ∑ ψ ∈ primitiveCharacterLevelLiftImage (hQ q.val q.property),
          Complex.normSq
            (∑ b : (ZMod h)ˣ,
              ψ b * (∑ n ∈ S, a n * ZMod.stdAddChar ((b : ZMod h) * (n : ZMod h))))) ≤
      (Nat.totient h : ℝ) * reducedAdditivePolynomialMeanSquare h hh S a := by
  classical
  let U : Finset (ZMod h) := Finset.univ.filter fun x => IsUnit x
  let f : ZMod h → ℂ := fun x => ∑ n ∈ S, a n * ZMod.stdAddChar (x * (n : ZMod h))
  let A : DirichletCharacter ℂ h → ℂ := fun ψ => ∑ b : (ZMod h)ˣ, ψ b * f b
  have hU : ∀ x, x ∈ U ↔ IsUnit x := by
    intro x
    simp only [U, Finset.mem_filter, Finset.mem_univ, true_and]
  have hparseval := dirichletCharacter_units_polynomial_parseval U hU f
  have hred : reducedAdditivePolynomialMeanSquare h hh S a = ∑ x ∈ U, Complex.normSq (f x) := by rfl
  calc
    _ ≤ ∑ ψ : DirichletCharacter ℂ h, Complex.normSq (A ψ) := by
      simpa only [A, f] using
        sum_primitiveCharacterLevelLiftImage_normSq_le_all_attached (h := h) Q hQ A
    _ = _ := by rw [hred, hparseval]

/--
Inputs: a positive common level `h`, a finite family of divisors, a positive complementary
modulus for each family member with product `h`, pairwise coprimality, and a finite polynomial.

Claim: the sum of the modulus-weighted Ramanujan-primitive mean squares over the family is bounded
by one totient-weighted reduced additive mean square at level `h`.

Proof: identify each pair contribution with its level-lift image, use conductor disjointness, and
apply Parseval once over the characters modulo `h`.

Role: removes repeated full-character Parseval sums from fixed-product families.
-/
theorem primitive_ramanujan_weighted_fixedProduct_family_parseval_le {h : ℕ} [NeZero h] (hh : 1 < h)
    (Q : Finset ℕ) (r : ℕ → ℕ) (hQ : ∀ q, q ∈ Q → q ∣ h) (hprod : ∀ q, q ∈ Q → q * r q = h)
    (hq : ∀ q, q ∈ Q → 1 < q) (hr : ∀ q, q ∈ Q → 0 < r q) (hcop : ∀ q, q ∈ Q → Nat.Coprime q (r q))
    (S : Finset ℕ) (a : ℕ → ℂ) :
    (∑ q ∈ Q.attach,
        (q.val : ℝ) *
          primitiveCharacterPolynomialMeanSquare q.val (hq q.val q.property) S
            (fun n => a n * @ramanujanSum (r q.val) n ⟨Nat.ne_of_gt (hr q.val q.property)⟩)) ≤
      (Nat.totient h : ℝ) * reducedAdditivePolynomialMeanSquare h hh S a := by
  classical
  let A : DirichletCharacter ℂ h → ℂ := fun ψ =>
    ∑ b : (ZMod h)ˣ, ψ b * ∑ n ∈ S, a n * ZMod.stdAddChar ((b : ZMod h) * (n : ZMod h))
  calc
    _ =
        ∑ q ∈ Q.attach,
          ∑ ψ ∈ primitiveCharacterLevelLiftImage (hQ q.val q.property), Complex.normSq (A ψ) :=
      by
      apply Finset.sum_congr rfl
      intro q hqQ
      have hqpos : 1 < q.val := hq q.val q.property
      have hterm :=
        @primitive_ramanujan_weighted_commonLevelImage_normSq_eq q.val (r q.val) h
          ⟨Nat.ne_of_gt (lt_trans Nat.zero_lt_one hqpos)⟩ ⟨Nat.ne_of_gt (hr q.val q.property)⟩
          inferInstance inferInstance (hprod q.val q.property) (hQ q.val q.property) hqpos
          (hcop q.val q.property) S a
      simpa only [primitiveCharacterPolynomialMeanSquare, A, mul_assoc, mul_comm,
        mul_left_comm] using hterm
    _ ≤ _ := by
      simpa only [A] using
        sum_primitiveCharacterLevelLiftImage_additiveParseval_le_attached (h := h) hh Q hQ S a

/--
Inputs: the fixed-product family from
`primitive_ramanujan_weighted_fixedProduct_family_parseval_le`.

Claim: after dividing by `φ(h)`, its normalized Ramanujan-primitive mean-square sum is bounded by
the reduced additive mean square at level `h`.

Proof: divide the collective bound by the positive totient of `h`.

Role: gives the exact fixed-product input for summing the reduced additive large sieve over levels.
-/
theorem primitive_ramanujan_weighted_fixedProduct_family_normalized_le {h : ℕ} [NeZero h]
    (hh : 1 < h) (Q : Finset ℕ) (r : ℕ → ℕ) (hQ : ∀ q, q ∈ Q → q ∣ h)
    (hprod : ∀ q, q ∈ Q → q * r q = h) (hq : ∀ q, q ∈ Q → 1 < q) (hr : ∀ q, q ∈ Q → 0 < r q)
    (hcop : ∀ q, q ∈ Q → Nat.Coprime q (r q)) (S : Finset ℕ) (a : ℕ → ℂ) :
    (∑ q ∈ Q.attach,
        (q.val : ℝ) / (Nat.totient h : ℝ) *
          primitiveCharacterPolynomialMeanSquare q.val (hq q.val q.property) S
            (fun n => a n * @ramanujanSum (r q.val) n ⟨Nat.ne_of_gt (hr q.val q.property)⟩)) ≤
      reducedAdditivePolynomialMeanSquare h hh S a := by
  classical
  have hφ : 0 < (Nat.totient h : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (lt_trans Nat.zero_lt_one hh)
  have hsum :
    (∑ q ∈ Q.attach,
          (q.val : ℝ) *
            primitiveCharacterPolynomialMeanSquare q.val (hq q.val q.property) S
              (fun n => a n * @ramanujanSum (r q.val) n ⟨Nat.ne_of_gt (hr q.val q.property)⟩)) /
        (Nat.totient h : ℝ) =
      ∑ q ∈ Q.attach,
        ((q.val : ℝ) *
            primitiveCharacterPolynomialMeanSquare q.val (hq q.val q.property) S
              (fun n => a n * @ramanujanSum (r q.val) n ⟨Nat.ne_of_gt (hr q.val q.property)⟩)) /
          (Nat.totient h : ℝ) := by
    rw [Finset.sum_div]
  calc
    _ =
        ∑ q ∈ Q.attach,
          ((q.val : ℝ) *
              primitiveCharacterPolynomialMeanSquare q.val (hq q.val q.property) S
                (fun n => a n * @ramanujanSum (r q.val) n ⟨Nat.ne_of_gt (hr q.val q.property)⟩)) /
            (Nat.totient h : ℝ) :=
      by
      apply Finset.sum_congr rfl
      intro q hqQ
      rw [div_mul_eq_mul_div]
    _ = _ := hsum.symm
    _ ≤ _ := by
      apply (div_le_iff₀ hφ).2
      calc
        _ ≤ (Nat.totient h : ℝ) * reducedAdditivePolynomialMeanSquare h hh S a :=
          primitive_ramanujan_weighted_fixedProduct_family_parseval_le hh Q r hQ hprod hq hr hcop S
            a
        _ = reducedAdditivePolynomialMeanSquare h hh S a * (Nat.totient h : ℝ) := mul_comm _ _

/--
Inputs: coprime positive moduli `q,r`, a finite polynomial, and its complex coefficients.

Claim: `q` times the Ramanujan-weighted primitive-character mean square modulo `q` is bounded by
the totient of `q*r` times the additive-polynomial mean square over unit residues modulo `q*r`.

Proof: identify the primitive-character sum with the image sum of its injective level lift,
enlarge that image to all characters modulo `q*r`, and apply unit-group Parseval.

Role: transfers the fixed-pair weighted character estimate to the additive side before the
collective large-sieve bound.
-/
theorem primitive_ramanujan_weighted_polynomial_parseval_le {q r : ℕ} [NeZero q] [NeZero r]
    (hq : 1 < q) (h : Nat.Coprime q r) (S : Finset ℕ) (a : ℕ → ℂ) :
    let U : Finset (ZMod (q * r)) := Finset.univ.filter (fun x => IsUnit x)
    let f : ZMod (q * r) → ℂ := fun x =>
      ∑ n ∈ S, a n * ZMod.stdAddChar ((n * x.val : ℕ) : ZMod (q * r))
    (q : ℝ) *
        ∑ χ ∈ primitiveDirichletCharacterSet q,
          Complex.normSq (∑ n ∈ S, a n * (χ (n : ZMod q) * ramanujanSum r n)) ≤
      (Nat.totient (q * r) : ℝ) * ∑ x ∈ U, Complex.normSq (f x) := by
  classical
  let F : DirichletCharacter ℂ q → DirichletCharacter ℂ (q * r) := fun χ =>
    DirichletCharacter.changeLevel (Nat.dvd_mul_right q r) χ⁻¹ *
      DirichletCharacter.changeLevel (Nat.dvd_mul_left r q) (1 : DirichletCharacter ℂ r)
  let A : DirichletCharacter ℂ (q * r) → ℂ := fun ψ =>
    ∑ b : (ZMod (q * r))ˣ,
      ψ b * (∑ n ∈ S, a n * ZMod.stdAddChar ((n * (b : ZMod (q * r)).val : ℕ) : ZMod (q * r)))
  let U : Finset (ZMod (q * r)) := Finset.univ.filter (fun x => IsUnit x)
  let f : ZMod (q * r) → ℂ := fun x =>
    ∑ n ∈ S, a n * ZMod.stdAddChar ((n * x.val : ℕ) : ZMod (q * r))
  have hU : ∀ x, x ∈ U ↔ IsUnit x := by
    intro x
    simp only [U, Finset.mem_filter, Finset.mem_univ, true_and]
  have himage := primitive_ramanujan_weighted_polynomial_image_normSq_eq hq h S a
  have hparseval := dirichletCharacter_units_polynomial_parseval U hU f
  have hsubset : (primitiveDirichletCharacterSet q).image F ⊆ Finset.univ := Finset.subset_univ _
  have hbound :
    (∑ ψ ∈ (primitiveDirichletCharacterSet q).image F, Complex.normSq (A ψ)) ≤
      ∑ ψ : DirichletCharacter ℂ (q * r), Complex.normSq (A ψ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (by
        intro ψ hψ hψnot
        exact Complex.normSq_nonneg (A ψ))
  calc
    _ = ∑ ψ ∈ (primitiveDirichletCharacterSet q).image F, Complex.normSq (A ψ) := himage
    _ ≤ _ := hbound
    _ = _ := hparseval

/--
Inputs: coprime moduli `q,r` with `q > 1` and `q*r > 1`, a finite polynomial, and complex
coefficients.

Claim: the Ramanujan-weighted primitive-character mean square modulo `q`, multiplied by `q`, is
bounded by the reduced additive mean square modulo `q*r`, multiplied by its totient.

Proof: rewrite the primitive-character polynomial using the weighted coefficient function, match
the additive phases through `ZMod.natCast_zmod_val`, and apply
`primitive_ramanujan_weighted_polynomial_parseval_le`.

Role: expresses the fixed-pair estimate through the existing reduced additive mean-square API.
-/
theorem primitive_ramanujan_weighted_polynomial_reducedMeanSquare_le {q r : ℕ} [NeZero q] [NeZero r]
    (hq : 1 < q) (hqr : 1 < q * r) (h : Nat.Coprime q r) (S : Finset ℕ) (a : ℕ → ℂ) :
    (q : ℝ) * primitiveCharacterPolynomialMeanSquare q hq S (fun n => a n * ramanujanSum r n) ≤
      (Nat.totient (q * r) : ℝ) * reducedAdditivePolynomialMeanSquare (q * r) hqr S a := by
  classical
  let U : Finset (ZMod (q * r)) := Finset.univ.filter (fun x => IsUnit x)
  let f : ZMod (q * r) → ℂ := fun x =>
    ∑ n ∈ S, a n * ZMod.stdAddChar ((n * x.val : ℕ) : ZMod (q * r))
  have hphase (x : ZMod (q * r)) (n : ℕ) :
    ZMod.stdAddChar ((n * x.val : ℕ) : ZMod (q * r)) =
      ZMod.stdAddChar (x * (n : ZMod (q * r))) := by
    congr 1
    rw [Nat.cast_mul, ZMod.natCast_zmod_val]
    exact mul_comm _ _
  have hpoly (x : ZMod (q * r)) :
    f x = ∑ n ∈ S, a n * ZMod.stdAddChar (x * (n : ZMod (q * r))) := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [hphase]
  have hleft :
    (q : ℝ) * primitiveCharacterPolynomialMeanSquare q hq S (fun n => a n * ramanujanSum r n) =
      (q : ℝ) *
        ∑ χ ∈ primitiveDirichletCharacterSet q,
          Complex.normSq (∑ n ∈ S, a n * (χ (n : ZMod q) * ramanujanSum r n)) := by
    simp only [primitiveCharacterPolynomialMeanSquare]
    congr 1
    apply Finset.sum_congr rfl
    intro χ hχ
    apply congrArg Complex.normSq
    apply Finset.sum_congr rfl
    intro n hn
    ring
  have hright :
    (Nat.totient (q * r) : ℝ) * reducedAdditivePolynomialMeanSquare (q * r) hqr S a =
      (Nat.totient (q * r) : ℝ) * ∑ x ∈ U, Complex.normSq (f x) := by
    rw [reducedAdditivePolynomialMeanSquare]
    congr 1
    apply Finset.sum_congr rfl
    intro x hx
    exact congrArg Complex.normSq (hpoly x).symm
  calc
    _ =
        (q : ℝ) *
          ∑ χ ∈ primitiveDirichletCharacterSet q,
            Complex.normSq (∑ n ∈ S, a n * (χ (n : ZMod q) * ramanujanSum r n)) :=
      hleft
    _ ≤ (Nat.totient (q * r) : ℝ) * ∑ x ∈ U, Complex.normSq (f x) :=
      primitive_ramanujan_weighted_polynomial_parseval_le hq h S a
    _ = _ := hright.symm

/--
Inputs: a finite family of moduli `q > 1`, a positive fixed modulus `r` coprime to every member,
and a finite polynomial with complex coefficients.

Claim: the sum over `q` of the `q`-weighted Ramanujan-twisted primitive-character mean squares is
bounded by the corresponding sum of totient-weighted reduced additive mean squares modulo `q*r`.

Proof: derive `q*r > 1` for every family member and sum
`primitive_ramanujan_weighted_polynomial_reducedMeanSquare_le` termwise.

Role: provides the fixed-`r` family estimate with product moduli, extending the existing
fixed-modulus family bounds toward the `q*r` range in Selberg's Theorem 7A.
-/
theorem primitive_ramanujan_weighted_family_reducedMeanSquare_le (Q : Finset ℕ)
    (hQ : ∀ q ∈ Q, 1 < q) (r : ℕ) [NeZero r] (hcop : ∀ q ∈ Q, Nat.Coprime q r) (S : Finset ℕ)
    (a : ℕ → ℂ) :
    (∑ q ∈ Q.attach,
        (q.val : ℝ) *
          primitiveCharacterPolynomialMeanSquare q.val (hQ q.val q.property) S
            (fun n => a n * ramanujanSum r n)) ≤
      ∑ q ∈ Q.attach,
        (Nat.totient (q.val * r) : ℝ) *
          reducedAdditivePolynomialMeanSquare (q.val * r)
            (by
              have hq : 1 < q.val := hQ q.val q.property
              exact
                lt_of_lt_of_le hq (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero (NeZero.ne r))))
            S a := by
  classical
  apply Finset.sum_le_sum
  intro q hqQ
  have hq : 1 < q.val := hQ q.val q.property
  have hqr : 1 < q.val * r :=
    lt_of_lt_of_le hq (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero (NeZero.ne r)))
  exact
    @primitive_ramanujan_weighted_polynomial_reducedMeanSquare_le q.val r
      ⟨Nat.ne_of_gt (lt_trans Nat.zero_lt_one hq)⟩ inferInstance hq hqr (hcop q.val q.property) S a

/--
Inputs: a finite family of pairs of natural moduli whose first components exceed one, whose
second components are positive, and whose components are pairwise coprime; also a finite
polynomial with complex coefficients.

Claim: summing the Ramanujan-weighted primitive-character estimate over the pair family is
bounded by the corresponding sum of reduced additive mean squares modulo each product modulus.

Proof: apply `primitive_ramanujan_weighted_polynomial_reducedMeanSquare_le` to each attached pair.

Role: handles finite families cut by product-modulus conditions such as `q * r ≤ Q`, without
requiring the second modulus to be fixed across the family.
-/
theorem primitive_ramanujan_weighted_pair_family_reducedMeanSquare_le (P : Finset (ℕ × ℕ))
    (hPq : ∀ p ∈ P, 1 < p.1) (hPr : ∀ p ∈ P, 0 < p.2) (hPcop : ∀ p ∈ P, Nat.Coprime p.1 p.2)
    (S : Finset ℕ) (a : ℕ → ℂ) :
    (∑ p ∈ P.attach,
        (p.val.1 : ℝ) *
          primitiveCharacterPolynomialMeanSquare p.val.1 (hPq p.val p.property) S
            (fun n => a n * @ramanujanSum p.val.2 n ⟨Nat.ne_of_gt (hPr p.val p.property)⟩)) ≤
      ∑ p ∈ P.attach,
        (Nat.totient (p.val.1 * p.val.2) : ℝ) *
          reducedAdditivePolynomialMeanSquare (p.val.1 * p.val.2)
            (by
              have hq := hPq p.val p.property
              exact lt_of_lt_of_le hq (Nat.le_mul_of_pos_right _ (hPr p.val p.property)))
            S a := by
  classical
  apply Finset.sum_le_sum
  intro p hp
  have hq : 1 < p.val.1 := hPq p.val p.property
  have hr : 0 < p.val.2 := hPr p.val p.property
  have hqr : 1 < p.val.1 * p.val.2 := lt_of_lt_of_le hq (Nat.le_mul_of_pos_right _ hr)
  exact
    @primitive_ramanujan_weighted_polynomial_reducedMeanSquare_le p.val.1 p.val.2
      ⟨Nat.ne_of_gt (lt_trans Nat.zero_lt_one hq)⟩ ⟨Nat.ne_of_gt hr⟩ hq hqr (hPcop p.val p.property)
      S a

/--
Inputs: residues modulo two nonzero natural moduli.

Claim: the product of one standard additive phase and the conjugate of the other equals the
exponential of the difference of their canonical rational frequencies.

Proof: use the explicit standard-character formula, conjugation of the complex exponential, and
the addition law for `Complex.exp`.

Role: identifies cross-modulus additive correlations with the geometric kernels bounded by the
large-sieve spacing estimates.
-/
theorem zmod_stdAddChar_phase_ratio {q r : ℕ} [NeZero q] [NeZero r] (x : ZMod q) (y : ZMod r) :
    ZMod.stdAddChar x * star (ZMod.stdAddChar y) =
      Complex.exp (Complex.I * ((2 * Real.pi * ((x.val : ℝ) / q - (y.val : ℝ) / r) : ℝ) : ℂ)) := by
  rw [zmod_stdAddChar_exp_val, zmod_stdAddChar_exp_val]
  rw [show
      star (Complex.exp (2 * Real.pi * Complex.I * (y.val : ℂ) / r)) =
        (starRingEnd ℂ) (Complex.exp (2 * Real.pi * Complex.I * (y.val : ℂ) / r))
      by rfl]
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  push_cast
  simp only [map_div₀, map_mul, map_natCast, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  ring_nf

/--
Inputs: a real phase in `[-1, 1]`.

Claim: the absolute sine of its multiple by `π` is at least twice the distance of the phase to
the nearest integer.

Proof: use the linear lower bound for sine on `[0, π/2]`, reducing phases above `1/2` by
`sin (π - x) = sin x` and negative phases by oddness.

Role: converts circular separation of rational frequencies into a lower bound for the complex
distance between their exponential phases.
-/
theorem abs_sin_pi_mul_ge_circular {d : ℝ} (hd : |d| ≤ 1) :
    2 * min |d| (1 - |d|) ≤ |Real.sin (Real.pi * d)| := by
  have ha : 0 ≤ |d| := abs_nonneg d
  have hs : |Real.sin (Real.pi * d)| = |Real.sin (Real.pi * |d|)| := by
    by_cases h : 0 ≤ d
    · rw [abs_of_nonneg h]
    · have h' : d < 0 := lt_of_not_ge h
      rw [abs_of_neg h', show Real.pi * d = -(Real.pi * (-d)) by ring, Real.sin_neg, abs_neg]
  rw [hs]
  by_cases hh : |d| ≤ 1 / 2
  · rw [min_eq_left (by linarith only [hh] : |d| ≤ 1 - |d|)]
    have hsin :=
      Real.mul_abs_le_abs_sin (x := Real.pi * |d|)
        (by
          rw [abs_of_nonneg (mul_nonneg Real.pi_nonneg ha)]
          nlinarith only [Real.pi_pos, hh])
    have habs : |Real.pi * (|d|)| = Real.pi * |d| := abs_of_nonneg (mul_nonneg Real.pi_nonneg ha)
    have hsimple : 2 / Real.pi * (Real.pi * |d|) = 2 * |d| := by field_simp [Real.pi_ne_zero]
    rw [habs, hsimple] at hsin
    exact hsin
  · have hh' : 1 / 2 < |d| := lt_of_not_ge hh
    have hb : 0 ≤ 1 - |d| := by linarith only [hd]
    rw [min_eq_right (by linarith only [hh'] : 1 - |d| ≤ |d|)]
    have hsin :=
      Real.mul_abs_le_abs_sin (x := Real.pi * (1 - |d|))
        (by
          rw [abs_of_nonneg (mul_nonneg Real.pi_nonneg hb)]
          nlinarith only [Real.pi_pos, hh', hb])
    have heq : Real.sin (Real.pi * |d|) = Real.sin (Real.pi * (1 - |d|)) := by
      rw [show Real.pi * |d| = Real.pi - Real.pi * (1 - |d|) by ring, Real.sin_pi_sub]
    rw [heq]
    have habs : |Real.pi * (1 - |d|)| = Real.pi * (1 - |d|) :=
      abs_of_nonneg (mul_nonneg Real.pi_nonneg hb)
    have hsimple : 2 / Real.pi * (Real.pi * (1 - |d|)) = 2 * (1 - |d|) := by
      field_simp [Real.pi_ne_zero]
    rw [habs, hsimple] at hsin
    exact hsin

/--
Inputs: a real phase in `[-1, 1]` and a lower bound for its circular distance to an integer.

Claim: the corresponding complex exponential is separated from one by at least four times that
distance lower bound.

Proof: express the chord length through `2 |sin (π d)|` and apply
`abs_sin_pi_mul_ge_circular`.

Role: turns the reduced-fraction spacing theorem into a denominator bound for the finite
geometric-sum kernel.
-/
theorem complex_exp_distance_ge_of_circular_separation {d ε : ℝ} (hd : |d| ≤ 1)
    (hsep : ε ≤ min |d| (1 - |d|)) :
    4 * ε ≤ ‖1 - Complex.exp (Complex.I * ((2 * Real.pi * d : ℝ) : ℂ))‖ := by
  have hsin := abs_sin_pi_mul_ge_circular hd
  have hmul : 4 * ε ≤ 2 * |Real.sin (Real.pi * d)| := by
    calc
      4 * ε ≤ 4 * min |d| (1 - |d|) := mul_le_mul_of_nonneg_left hsep (by norm_num only)
      _ = 2 * (2 * min |d| (1 - |d|)) := by ring
      _ ≤ 2 * |Real.sin (Real.pi * d)| := mul_le_mul_of_nonneg_left hsin (by norm_num only)
  have hnorm :
    ‖Complex.exp (Complex.I * ((2 * Real.pi * d : ℝ) : ℂ)) - 1‖ = 2 * |Real.sin (Real.pi * d)| := by
    rw [Complex.norm_exp_I_mul_ofReal_sub_one]
    rw [show (2 * Real.pi * d : ℝ) / 2 = Real.pi * d by ring, Real.norm_eq_abs, abs_mul,
      abs_of_pos (by norm_num only : (0 : ℝ) < 2)]
  calc
    4 * ε ≤ 2 * |Real.sin (Real.pi * d)| := hmul
    _ = ‖Complex.exp (Complex.I * ((2 * Real.pi * d : ℝ) : ℂ)) - 1‖ := hnorm.symm
    _ = ‖1 - Complex.exp (Complex.I * ((2 * Real.pi * d : ℝ) : ℂ))‖ := by rw [norm_sub_rev]

/--
Inputs: a phase difference in `[-1, 1]`, a positive lower bound for its circular distance to an
integer, and the interval and taper lengths.

Claim: the overlap Fourier kernel decays according to that circular-distance lower bound.

Proof: the sine chord estimate gives phase separation at least `4 * ε`; insert this into the two
geometric-sum bounds in `triangleOverlapWindowWeight_fourier_norm_le`.

Role: supplies a distance-sensitive kernel estimate for summing the separated-frequency shells.
-/
theorem triangleOverlapWindowWeight_fourier_norm_le_of_circular_separation (N L : ℕ) (d ε : ℝ)
    (hd : |d| ≤ 1) (hε : 0 < ε) (hsep : ε ≤ min |d| (1 - |d|)) :
    ‖∑ n ∈ Finset.range (N + 2 * L - 1),
          (triangleOverlapWindowWeight N L n : ℂ) *
            Complex.exp (Complex.I * ((2 * Real.pi * d : ℝ) : ℂ)) ^ n‖ ≤
      ‖(L : ℂ)⁻¹‖ * min ((N + L : ℕ) : ℝ) (1 / (2 * ε)) * min (L : ℝ) (1 / (2 * ε)) := by
  let z : ℂ := Complex.exp (Complex.I * ((2 * Real.pi * d : ℝ) : ℂ))
  have hphase := complex_exp_distance_ge_of_circular_separation hd hsep
  have hden : 0 < ‖1 - z‖ := by
    have hpos : 0 < 4 * ε := mul_pos (by norm_num only) hε
    exact lt_of_lt_of_le hpos (by simpa only [z] using hphase)
  have hz : ‖z‖ = 1 := by
    dsimp only [z]
    exact Complex.norm_exp_I_mul_ofReal _
  have hzne : z ≠ 1 := by
    intro heq
    have hz0 : ‖1 - z‖ = 0 := by rw [heq, sub_self, norm_zero]
    exact (ne_of_gt hden) hz0
  have hscale : 2 / ‖1 - z‖ ≤ 1 / (2 * ε) := by
    apply (div_le_div_iff₀ hden (mul_pos (by norm_num only : (0 : ℝ) < 2) hε)).2
    nlinarith only [hphase]
  have hfirst := unit_circle_geometric_sum_norm_le_min hz hzne (N + L)
  have hsecond := reverse_unit_circle_geometric_sum_norm_le_min hz hzne L
  have hfirst' := min_le_min_left ((N + L : ℕ) : ℝ) hscale
  have hsecond' := min_le_min_left (L : ℝ) hscale
  have hfirstNonneg : 0 ≤ min ((N + L : ℕ) : ℝ) (2 / ‖1 - z‖) := le_trans (norm_nonneg _) hfirst
  calc
    _ ≤ ‖(L : ℂ)⁻¹‖ * min ((N + L : ℕ) : ℝ) (2 / ‖1 - z‖) * min (L : ℝ) (2 / ‖1 - z‖) :=
      triangleOverlapWindowWeight_fourier_norm_le N L z hz hzne
    _ ≤ _ := by
      calc
        _ ≤ (‖(L : ℂ)⁻¹‖ * min ((N + L : ℕ) : ℝ) (1 / (2 * ε))) * min (L : ℝ) (2 / ‖1 - z‖) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfirst' (norm_nonneg _))
            (le_trans (norm_nonneg _) hsecond)
        _ ≤ _ :=
          mul_le_mul_of_nonneg_left hsecond'
            (mul_nonneg (norm_nonneg _) (le_trans hfirstNonneg hfirst'))

/--
Inputs: a signed coordinate in a positive-width distance shell, with a separate circular-distance
lower bound, together with the interval and taper lengths.

Claim: the overlap Fourier kernel is bounded using the larger of the spacing and the shell's
inner radius as its phase separation.

Proof: the shell gives the radial lower bound, the circular separation gives the base spacing, and
the centered coordinate range bounds the complementary circular distance.

Role: turns the shell population estimate into a summable kernel estimate for the Gram row.
-/
theorem triangleOverlapWindowWeight_fourier_norm_le_of_signed_shell (N L : ℕ) (S : Finset ℝ)
    (δ d : ℝ) (k : ℕ) (hδ : 0 < δ) (hd : -(1 / 2 : ℝ) ≤ d ∧ d ≤ 1 / 2)
    (hbase : δ ≤ min |d| (1 - |d|)) (hshell : d ∈ signedDistanceShell S δ k) :
    ‖∑ n ∈ Finset.range (N + 2 * L - 1),
          (triangleOverlapWindowWeight N L n : ℂ) *
            Complex.exp (Complex.I * ((2 * Real.pi * d : ℝ) : ℂ)) ^ n‖ ≤
      ‖(L : ℂ)⁻¹‖ * min ((N + L : ℕ) : ℝ) (1 / (2 * max δ ((k : ℝ) * δ))) *
        min (L : ℝ) (1 / (2 * max δ ((k : ℝ) * δ))) := by
  have hεpos : 0 < max δ ((k : ℝ) * δ) := lt_of_lt_of_le hδ (le_max_left _ _)
  have habs : |d| ≤ 1 / 2 := abs_le.mpr hd
  have hεlower : max δ ((k : ℝ) * δ) ≤ |d| :=
    max_le (le_trans hbase (min_le_left _ _)) (signedDistanceShell_abs_ge hδ hshell)
  have hεupper : max δ ((k : ℝ) * δ) ≤ 1 - |d| := by
    have hcomp : |d| ≤ 1 - |d| := by linarith only [habs]
    exact le_trans hεlower hcomp
  have hεsep : max δ ((k : ℝ) * δ) ≤ min |d| (1 - |d|) := le_min hεlower hεupper
  have hdabs : |d| ≤ 1 := by exact le_trans habs (by norm_num only)
  exact
    triangleOverlapWindowWeight_fourier_norm_le_of_circular_separation N L d (max δ ((k : ℝ) * δ))
      hdabs hεpos hεsep

/--
Inputs: a base reduced frequency, a nonzero member of its signed-coordinate family, a shell index,
and positive interval and taper lengths.

Claim: the member's overlap Fourier kernel is bounded by the spacing and shell-radius envelope.

Proof: use pairwise frequency separation from the origin, the centered-coordinate range, and the
generic shell kernel estimate.

Role: gives the off-diagonal kernel estimate for an individual reduced-frequency Gram row entry.
-/
theorem reducedUnitFrequencySignedCoordinates_shell_kernel_bound {Q : ℕ}
    (f₀ : ReducedUnitFrequencyIndex Q) (x : ℝ) (k : ℕ) (hQ : 0 < Q)
    (hx : x ∈ reducedUnitFrequencySignedCoordinates (Q := Q) (reducedUnitFrequencyCoordinate f₀))
    (hx0 : x ≠ 0)
    (hshell :
      x ∈
        signedDistanceShell
          (reducedUnitFrequencySignedCoordinates (Q := Q) (reducedUnitFrequencyCoordinate f₀))
          (1 / ((Q : ℝ) * Q)) k)
    (N L : ℕ) :
    ‖∑ n ∈ Finset.range (N + 2 * L - 1),
          (triangleOverlapWindowWeight N L n : ℂ) *
            Complex.exp (Complex.I * ((2 * Real.pi * x : ℝ) : ℂ)) ^ n‖ ≤
      ‖(L : ℂ)⁻¹‖ *
        min ((N + L : ℕ) : ℝ) (1 / (2 * max (1 / ((Q : ℝ) * Q)) ((k : ℝ) * (1 / ((Q : ℝ) * Q))))) *
        min (L : ℝ) (1 / (2 * max (1 / ((Q : ℝ) * Q)) ((k : ℝ) * (1 / ((Q : ℝ) * Q))))) := by
  have hQR : 0 < (Q : ℝ) := by exact_mod_cast hQ
  have hQsq : 0 < (Q : ℝ) * Q := mul_pos hQR hQR
  have hδ : 0 < 1 / ((Q : ℝ) * Q) := div_pos (by norm_num only) hQsq
  have hbase := reducedUnitFrequencySignedCoordinates_separated_from_zero f₀ x hx hx0
  have hcenter :=
    reducedUnitFrequencySignedCoordinates_mem_bounds (reducedUnitFrequencyCoordinate f₀)
      (reducedUnitFrequencyCoordinate_bounds f₀).1 (reducedUnitFrequencyCoordinate_bounds f₀).2 x hx
  exact
    triangleOverlapWindowWeight_fourier_norm_le_of_signed_shell N L _ (1 / ((Q : ℝ) * Q)) x k hδ
      hcenter hbase hshell

/--
Inputs: a natural upper cutoff for positive integer indices.

Claim: the sum of reciprocal squares over indices from one through the cutoff is at most two.

Proof: identify the interval with `Ioo 0 (n + 1)` and apply the telescoping reciprocal-square
estimate from mathlib.

Role: bounds the total contribution of the nonzero frequency shells by an absolute multiple of
`Q^2`.
-/
theorem reciprocal_square_sum_Ico_le_two (n : ℕ) :
    ∑ k ∈ Finset.Ico 1 (n + 1), ((k : ℝ) ^ 2)⁻¹ ≤ 2 := by
  have hset : Finset.Ico 1 (n + 1) = Finset.Ioo 0 (n + 1) := by
    ext k
    simp only [Finset.mem_Ico, Finset.mem_Ioo]
    omega
  rw [hset]
  simpa only [Nat.cast_zero, zero_add, div_one] using (sum_Ioo_inv_sq_le (α := ℝ) 0 (n + 1))

/--
Inputs: a finite shell cutoff, a positive scale `M`, and a nonnegative interval length `N`.

Claim: the sum of the zero-shell contribution and the inverse-square tails is at most `N + 2M`.

Proof: bound the zero shell by `N + M`, each positive shell by `M / (2 k^2)`, and apply the
reciprocal-square estimate to the remaining finite sum.

Role: evaluates the explicit radial envelope in the separated-frequency Gram-row estimate.
-/
theorem radial_overlap_envelope_sum_le (m : ℕ) {M N : ℝ} (hM : 0 < M) (hN : 0 ≤ N) :
    ∑ k ∈ Finset.range (m + 1),
        2 * (M⁻¹ * min (N + M) (M / (2 * max 1 (k : ℝ))) * min M (M / (2 * max 1 (k : ℝ)))) ≤
      N + 2 * M := by
  let B : ℕ → ℝ := fun k =>
    2 * (M⁻¹ * min (N + M) (M / (2 * max 1 (k : ℝ))) * min M (M / (2 * max 1 (k : ℝ))))
  have hset : Finset.range (m + 1) = insert 0 (Finset.Ico 1 (m + 1)) := by
    ext k
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]
    omega
  have hzero : B 0 ≤ N + M := by
    dsimp only [B]
    simp only [Nat.cast_zero]
    have hmax : max 1 (0 : ℝ) = 1 := max_eq_left (by norm_num only : (0 : ℝ) ≤ 1)
    rw [hmax]
    have hA0 : 0 ≤ min (N + M) (M / 2) :=
      le_min (add_nonneg hN hM.le) (div_nonneg hM.le (by norm_num only))
    have hB0 : 0 ≤ min M (M / 2) := le_min hM.le (div_nonneg hM.le (by norm_num only))
    have hA : min (N + M) (M / 2) ≤ N + M := min_le_left _ _
    have hB : min M (M / 2) ≤ M / 2 := min_le_right _ _
    have hprod := mul_le_mul hA hB hB0 (add_nonneg hN hM.le)
    calc
      _ = (2 * M⁻¹) * (min (N + M) (M / 2) * min M (M / 2)) := by ring_nf
      _ ≤ (2 * M⁻¹) * ((N + M) * (M / 2)) :=
        mul_le_mul_of_nonneg_left hprod (mul_nonneg (by norm_num only) (inv_nonneg.mpr hM.le))
      _ = N + M := by field_simp [ne_of_gt hM]
  have htail : ∀ k ∈ Finset.Ico 1 (m + 1), B k ≤ M / (2 * (k : ℝ) ^ 2) := by
    intro k hk
    dsimp only [B]
    have hkpos : 0 < k := (Finset.mem_Ico.mp hk).1
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hkpos
    have hmax : max 1 (k : ℝ) = k := max_eq_right hk1
    rw [hmax]
    have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hkpos)
    have hr : 0 < M / (2 * (k : ℝ)) :=
      div_pos hM (mul_pos (by norm_num only) (by exact_mod_cast hkpos))
    have hA0 : 0 ≤ min (N + M) (M / (2 * (k : ℝ))) := le_min (add_nonneg hN hM.le) hr.le
    have hB0 : 0 ≤ min M (M / (2 * (k : ℝ))) := le_min hM.le hr.le
    have hA : min (N + M) (M / (2 * (k : ℝ))) ≤ M / (2 * (k : ℝ)) := min_le_right _ _
    have hB : min M (M / (2 * (k : ℝ))) ≤ M / (2 * (k : ℝ)) := min_le_right _ _
    have hprod := mul_le_mul hA hB hB0 hr.le
    calc
      _ = (2 * M⁻¹) * (min (N + M) (M / (2 * (k : ℝ))) * min M (M / (2 * (k : ℝ)))) := by ring_nf
      _ ≤ (2 * M⁻¹) * ((M / (2 * (k : ℝ))) * (M / (2 * (k : ℝ)))) :=
        mul_le_mul_of_nonneg_left hprod (mul_nonneg (by norm_num only) (inv_nonneg.mpr hM.le))
      _ = M / (2 * (k : ℝ) ^ 2) := by field_simp [ne_of_gt hM, hkR]
  have hinterval : Finset.Ico 1 (m + 1) = Finset.Ioo 0 (m + 1) := by
    ext k
    simp only [Finset.mem_Ico, Finset.mem_Ioo]
    omega
  have hsum : ∑ k ∈ Finset.Ico 1 (m + 1), M / (2 * (k : ℝ) ^ 2) ≤ M := by
    rw [hinterval]
    calc
      _ = (M / 2) * ∑ k ∈ Finset.Ioo 0 (m + 1), ((k : ℝ) ^ 2)⁻¹ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        have hkpos : 0 < k := (Finset.mem_Ioo.mp hk).1
        have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hkpos)
        field_simp [hkR]
      _ ≤ (M / 2) * 2 := by
        apply mul_le_mul_of_nonneg_left _ (div_nonneg hM.le (by norm_num only))
        simpa only [Nat.cast_zero, zero_add, div_one] using (sum_Ioo_inv_sq_le (α := ℝ) 0 (m + 1))
      _ = M := by ring
  rw [hset,
    Finset.sum_insert
      (by
        intro hz
        simp only [Finset.mem_Ico] at hz
        omega)]
  change B 0 + ∑ k ∈ Finset.Ico 1 (m + 1), B k ≤ N + 2 * M
  calc
    _ ≤ (N + M) + ∑ k ∈ Finset.Ico 1 (m + 1), M / (2 * (k : ℝ) ^ 2) :=
      add_le_add hzero (Finset.sum_le_sum htail)
    _ ≤ (N + M) + M := add_le_add (le_refl _) hsum
    _ = N + 2 * M := by ring

/--
Inputs: a positive cutoff, a base reduced frequency, and the interval and taper lengths.

Claim: the sum of all off-diagonal overlap-kernel norms in the row is bounded by the finite sum of
twice the radial shell envelopes.

Proof: remove the base point, use reduced-frequency separation and the finite shell range, then
apply the general shell-summation bound and the individual kernel estimate.

Role: supplies the radial finite-sum estimate needed for the additive large-sieve Gram row.
-/
theorem reducedUnitFrequencySignedCoordinates_offdiag_kernel_row_le {Q : ℕ} (hQ : 0 < Q)
    (f₀ : ReducedUnitFrequencyIndex Q) (N L : ℕ) :
    ∑
        x ∈
          (reducedUnitFrequencySignedCoordinates (Q := Q)
                (reducedUnitFrequencyCoordinate f₀)).filter
            (fun x => x ≠ 0),
        ‖∑ n ∈ Finset.range (N + 2 * L - 1),
            (triangleOverlapWindowWeight N L n : ℂ) *
              Complex.exp (Complex.I * ((2 * Real.pi * x : ℝ) : ℂ)) ^ n‖ ≤
      ∑ k ∈ Finset.range (Q * Q + 1),
        2 *
          (‖(L : ℂ)⁻¹‖ *
            min ((N + L : ℕ) : ℝ)
              (1 / (2 * max (1 / ((Q : ℝ) * Q)) ((k : ℝ) * (1 / ((Q : ℝ) * Q))))) *
            min (L : ℝ) (1 / (2 * max (1 / ((Q : ℝ) * Q)) ((k : ℝ) * (1 / ((Q : ℝ) * Q)))))) := by
  classical
  let α := reducedUnitFrequencyCoordinate f₀
  let T := reducedUnitFrequencySignedCoordinates (Q := Q) α
  let S := T.filter (fun x => x ≠ 0)
  let δ := 1 / ((Q : ℝ) * Q)
  let K := Finset.range (Q * Q + 1)
  have hα := reducedUnitFrequencyCoordinate_bounds f₀
  have hQR : 0 < (Q : ℝ) := by exact_mod_cast hQ
  have hQsq : 0 < (Q : ℝ) * Q := mul_pos hQR hQR
  have hδ : 0 < δ := by
    dsimp only [δ]
    exact div_pos (by norm_num only) hQsq
  have hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ min |x - y| (1 - |x - y|) := by
    intro x hx y hy hxy
    have hxT := (Finset.mem_filter.mp hx).1
    have hyT := (Finset.mem_filter.mp hy).1
    exact reducedUnitFrequencySignedCoordinates_separated α hα.1 hα.2 x y hxT hyT hxy
  have hindex : ∀ x ∈ S, ⌊|x| / δ⌋₊ ∈ K := by
    intro x hx
    have hxT := (Finset.mem_filter.mp hx).1
    have hk := reducedUnitFrequencySignedCoordinates_floor_shell_index_le hQ α hα.1 hα.2 x hxT
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hk)
  let f : ℝ → ℝ := fun x =>
    ‖∑ n ∈ Finset.range (N + 2 * L - 1),
        (triangleOverlapWindowWeight N L n : ℂ) *
          Complex.exp (Complex.I * ((2 * Real.pi * x : ℝ) : ℂ)) ^ n‖
  let B : ℕ → ℝ := fun k =>
    ‖(L : ℂ)⁻¹‖ * min ((N + L : ℕ) : ℝ) (1 / (2 * max δ ((k : ℝ) * δ))) *
      min (L : ℝ) (1 / (2 * max δ ((k : ℝ) * δ)))
  have hB : ∀ k ∈ K, 0 ≤ B k := by
    intro k hk
    dsimp only [B]
    have hr : 0 < max δ ((k : ℝ) * δ) := lt_of_lt_of_le hδ (le_max_left _ _)
    have hinv : 0 ≤ 1 / (2 * max δ ((k : ℝ) * δ)) :=
      le_of_lt (div_pos (by norm_num only) (mul_pos (by norm_num only) hr))
    have hfirst : 0 ≤ min ((N + L : ℕ) : ℝ) (1 / (2 * max δ ((k : ℝ) * δ))) :=
      le_min (Nat.cast_nonneg _) hinv
    have hsecond : 0 ≤ min (L : ℝ) (1 / (2 * max δ ((k : ℝ) * δ))) :=
      le_min (Nat.cast_nonneg _) hinv
    exact mul_nonneg (mul_nonneg (norm_nonneg _) hfirst) hsecond
  have hbound : ∀ k ∈ K, ∀ x ∈ signedDistanceShell S δ k, f x ≤ B k := by
    intro k hk x hx
    rcases Finset.mem_filter.mp hx with ⟨hxS, hshell⟩
    have hxST : x ∈ T.filter (fun x => x ≠ 0) := by simpa only [S] using hxS
    rcases Finset.mem_filter.mp hxST with ⟨hxT, hx0⟩
    have hfull : x ∈ signedDistanceShell T δ k := by exact Finset.mem_filter.mpr ⟨hxT, hshell⟩
    exact
      reducedUnitFrequencySignedCoordinates_shell_kernel_bound f₀ x k hQ hxT hx0
        (by simpa only [T, α, δ] using hfull) N L
  have hsum := sum_le_two_shell_bounds hδ hsep hindex f B hB hbound
  simpa only [f, B, S, K, T, α, δ] using hsum

/--
Inputs: a positive denominator cutoff, a base reduced frequency, and an interval length `N`.

Claim: with taper length `Q^2`, the off-diagonal overlap-kernel row is at most `N + 2 Q^2`.

Proof: apply the finite-shell row estimate and evaluate its radial envelope using
`radial_overlap_envelope_sum_le`.

Role: provides the uniform Gram-row bound needed by the windowed additive large sieve.
-/
theorem reducedUnitFrequencySignedCoordinates_offdiag_kernel_row_le_square {Q : ℕ} (hQ : 0 < Q)
    (f₀ : ReducedUnitFrequencyIndex Q) (N : ℕ) :
    ∑
        x ∈
          (reducedUnitFrequencySignedCoordinates (Q := Q)
                (reducedUnitFrequencyCoordinate f₀)).filter
            (fun x => x ≠ 0),
        ‖∑ n ∈ Finset.range (N + 2 * (Q * Q) - 1),
            (triangleOverlapWindowWeight N (Q * Q) n : ℂ) *
              Complex.exp (Complex.I * ((2 * Real.pi * x : ℝ) : ℂ)) ^ n‖ ≤
      (N : ℝ) + 2 * ((Q * Q : ℕ) : ℝ) := by
  classical
  let m : ℕ := Q * Q
  let M : ℝ := (m : ℝ)
  let δ : ℝ := 1 / ((Q : ℝ) * Q)
  have hMpos : 0 < M := by
    dsimp only [M, m]
    exact_mod_cast Nat.mul_pos hQ hQ
  have hcast : M = (Q : ℝ) * Q := by
    dsimp only [M, m]
    simp only [Nat.cast_mul]
  have hδeq : δ = 1 / M := by
    dsimp only [δ]
    rw [← hcast]
  have hδpos : 0 < δ := by
    rw [hδeq]; exact div_pos (by norm_num only) hMpos
  have hnorm : ‖((Q : ℂ) * Q)⁻¹‖ = M⁻¹ := by
    calc
      ‖((Q : ℂ) * Q)⁻¹‖ = ((Q : ℝ) * Q)⁻¹ := by rw [norm_inv, norm_mul, Complex.norm_natCast]
      _ = M⁻¹ := by rw [← hcast]
  have hmax (k : ℕ) : max δ ((k : ℝ) * δ) = δ * max 1 (k : ℝ) := by
    calc
      max δ ((k : ℝ) * δ) = max (1 * δ) ((k : ℝ) * δ) := by rw [one_mul]
      _ = max 1 (k : ℝ) * δ := (max_mul_of_nonneg 1 (k : ℝ) hδpos.le).symm
      _ = δ * max 1 (k : ℝ) := by ring
  have hrec (k : ℕ) : 1 / (2 * max δ ((k : ℝ) * δ)) = M / (2 * max 1 (k : ℝ)) := by
    rw [hmax k, hδeq]
    have hmaxpos : 0 < max 1 (k : ℝ) := lt_of_lt_of_le (by norm_num only) (le_max_left _ _)
    field_simp [ne_of_gt hMpos, ne_of_gt hmaxpos]
  calc
    _ ≤
        ∑ k ∈ Finset.range (m + 1),
          2 *
            (M⁻¹ * min ((N : ℝ) + M) (M / (2 * max 1 (k : ℝ))) * min M (M / (2 * max 1 (k : ℝ)))) :=
      by
      simpa only [hnorm, hrec, δ, Nat.cast_add, Nat.cast_mul, M, m] using
        (reducedUnitFrequencySignedCoordinates_offdiag_kernel_row_le hQ f₀ N m)
    _ ≤ (N : ℝ) + 2 * M := radial_overlap_envelope_sum_le m hMpos (Nat.cast_nonneg N)
    _ = (N : ℝ) + 2 * ((Q * Q : ℕ) : ℝ) := by simp only [M, m]

/--
Inputs: a positive denominator cutoff, a base reduced frequency, and an interval length `N`.

Claim: the full row over signed reduced frequencies, including its diagonal entry, is at most
`2N + 3Q^2` when the taper length is `Q^2`.

Proof: split off the zero coordinate, evaluate its overlap weight sum as `N + Q^2`, and apply the
off-diagonal estimate `N + 2Q^2` to the remaining coordinates.

Role: gives the complete uniform Gram-row bound for the finite reduced-frequency family.
-/
theorem reducedUnitFrequencySignedCoordinates_full_kernel_row_le_square {Q : ℕ} (hQ : 0 < Q)
    (f₀ : ReducedUnitFrequencyIndex Q) (N : ℕ) :
    ∑ x ∈ reducedUnitFrequencySignedCoordinates (Q := Q) (reducedUnitFrequencyCoordinate f₀),
        ‖∑ n ∈ Finset.range (N + 2 * (Q * Q) - 1),
            (triangleOverlapWindowWeight N (Q * Q) n : ℂ) *
              Complex.exp (Complex.I * ((2 * Real.pi * x : ℝ) : ℂ)) ^ n‖ ≤
      2 * (N : ℝ) + 3 * ((Q * Q : ℕ) : ℝ) := by
  classical
  let α := reducedUnitFrequencyCoordinate f₀
  let T := reducedUnitFrequencySignedCoordinates (Q := Q) α
  let m : ℕ := Q * Q
  let M : ℝ := (m : ℝ)
  let f : ℝ → ℝ := fun x =>
    ‖∑ n ∈ Finset.range (N + 2 * m - 1),
        (triangleOverlapWindowWeight N m n : ℂ) *
          Complex.exp (Complex.I * ((2 * Real.pi * x : ℝ) : ℂ)) ^ n‖
  have hzero : 0 ∈ T := by exact reducedUnitFrequencySignedCoordinates_zero_mem f₀
  have hfilter : T.filter (fun x => ¬x ≠ 0) = {0} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨_, hnot⟩
      exact Classical.not_not.mp hnot
    · intro hx
      subst x
      exact ⟨hzero, fun h => h rfl⟩
  have hdiagComplex :
    ∑ n ∈ Finset.range (N + 2 * m - 1),
        (triangleOverlapWindowWeight N m n : ℂ) *
          Complex.exp (Complex.I * ((2 * Real.pi * (0 : ℝ) : ℝ) : ℂ)) ^ n =
      ((N + m : ℕ) : ℂ) := by
    calc
      _ = ∑ n ∈ Finset.range (N + 2 * m - 1), (triangleOverlapWindowWeight N m n : ℂ) := by
        apply Finset.sum_congr rfl
        intro n hn
        simp only [mul_zero, Complex.ofReal_zero, Complex.exp_zero, one_pow, mul_one]
      _ = ((∑ n ∈ Finset.range (N + 2 * m - 1), triangleOverlapWindowWeight N m n : ℝ) : ℂ) := by
        rw [← Complex.ofReal_sum]
      _ = ((N + m : ℕ) : ℂ) := by
        rw [triangleOverlapWindowWeight_sum_eq N m
            (by
              dsimp only [m]
              exact Nat.mul_pos hQ hQ),
          Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_natCast]
        simp only [Nat.cast_add]
  have hdiag : f 0 = (N : ℝ) + M := by
    dsimp only [f]
    calc
      _ = ‖((N + m : ℕ) : ℂ)‖ := congrArg norm hdiagComplex
      _ = (N : ℝ) + M := by
        rw [Complex.norm_natCast]
        simp only [Nat.cast_add, M, m]
  have hdiagSum : ∑ x ∈ T.filter (fun x => ¬x ≠ 0), f x = f 0 := by
    rw [hfilter]
    simp only [Finset.sum_singleton]
  have hdecomp :
    (∑ x ∈ T.filter (fun x => x ≠ 0), f x) + (∑ x ∈ T.filter (fun x => ¬x ≠ 0), f x) =
      ∑ x ∈ T, f x :=
    Finset.sum_filter_add_sum_filter_not T (fun x => x ≠ 0) f
  have hOff : ∑ x ∈ T.filter (fun x => x ≠ 0), f x ≤ (N : ℝ) + 2 * M := by
    simpa only [f, T, α, m, M] using
      (reducedUnitFrequencySignedCoordinates_offdiag_kernel_row_le_square hQ f₀ N)
  calc
    _ = (∑ x ∈ T.filter (fun x => x ≠ 0), f x) + f 0 := by rw [← hdecomp, hdiagSum]
    _ ≤ ((N : ℝ) + 2 * M) + ((N : ℝ) + M) := add_le_add hOff (le_of_eq hdiag)
    _ = 2 * (N : ℝ) + 3 * M := by ring
    _ = 2 * (N : ℝ) + 3 * ((Q * Q : ℕ) : ℝ) := by simp only [M, m]

/--
Inputs: a positive denominator cutoff, a base reduced frequency, and an interval length.

Claim: the Gram row over all reduced rational frequencies through `Q` is at most `2N + 3Q²` for
the triangle window of length `Q²`.

Proof: reindex the rational vector Gram entries by their injective signed-coordinate image and
apply the real Fourier-kernel row bound.

Role: supplies the concrete Gram-row hypothesis for the one-modulus additive large sieve.
-/
theorem reducedUnitFrequencyRationalWindowGramRow_le_square {Q : ℕ} (hQ : 0 < Q)
    (f₀ : ReducedUnitFrequencyIndex Q) (N : ℕ) :
    ∑ f ∈ reducedUnitFrequencyIndexSet Q,
        ‖inner ℂ
            (rationalWindowFrequencyVector (Finset.range (N + 2 * (Q * Q) - 1))
              (triangleOverlapWindow N (Q * Q)) (reducedUnitFrequencyRational f₀))
            (rationalWindowFrequencyVector (Finset.range (N + 2 * (Q * Q) - 1))
              (triangleOverlapWindow N (Q * Q)) (reducedUnitFrequencyRational f))‖ ≤
      2 * (N : ℝ) + 3 * ((Q * Q : ℕ) : ℝ) := by
  classical
  let α := reducedUnitFrequencyCoordinate f₀
  let U := reducedUnitFrequencyIndexSet Q
  let φ : ReducedUnitFrequencyIndex Q → ℝ := fun f => reducedUnitFrequencySignedCoordinate α f
  let K : ℝ → ℝ := fun x =>
    ‖∑ n ∈ Finset.range (N + 2 * (Q * Q) - 1),
        (triangleOverlapWindowWeight N (Q * Q) n : ℂ) *
          Complex.exp (Complex.I * ((2 * Real.pi * x : ℝ) : ℂ)) ^ n‖
  have hφ : Function.Injective φ := by
    intro f g hfg
    dsimp only [φ] at hfg
    apply reducedUnitFrequencyCoordinate_injective
    exact
      signedCircularDifference_injective (reducedUnitFrequencyCoordinate_bounds f).1
        (reducedUnitFrequencyCoordinate_bounds f).2 (reducedUnitFrequencyCoordinate_bounds g).1
        (reducedUnitFrequencyCoordinate_bounds g).2 hfg
  have hsum :
    (∑ f ∈ U,
        ‖inner ℂ
            (rationalWindowFrequencyVector (Finset.range (N + 2 * (Q * Q) - 1))
              (triangleOverlapWindow N (Q * Q)) (reducedUnitFrequencyRational f₀))
            (rationalWindowFrequencyVector (Finset.range (N + 2 * (Q * Q) - 1))
              (triangleOverlapWindow N (Q * Q)) (reducedUnitFrequencyRational f))‖) =
      ∑ x ∈ reducedUnitFrequencySignedCoordinates (Q := Q) α, K x := by
    calc
      _ = ∑ f ∈ U, K (φ f) := by
        apply Finset.sum_congr rfl
        intro f hf
        simpa only [K, φ, α] using
          reducedUnitFrequencyWindowGramTerm_norm_eq_signed_kernel_norm f₀ f N
      _ = _ := (Finset.sum_image (s := U) (g := φ) (f := K) hφ.injOn).symm
  rw [hsum]
  simpa only [K, α] using (reducedUnitFrequencySignedCoordinates_full_kernel_row_le_square hQ f₀ N)

/--
Definition: the finite set of all reduced rational frequencies with denominator at most `Q`.

Inputs: a natural denominator cutoff.

Output: the rational-coordinate image of `reducedUnitFrequencyIndexSet Q`.

Role: provides the common frequency set for the denominator-bounded additive large sieve.
-/
noncomputable def reducedUnitFrequencyRationalSet (Q : ℕ) : Finset ℚ :=
  (reducedUnitFrequencyIndexSet Q).image reducedUnitFrequencyRational

/--
Inputs: a positive denominator cutoff, an interval length, and a frequency in the reduced
rational set.

Claim: the windowed Gram row over all reduced rational frequencies is at most `2N + 3Q²`.

Proof: reindex the subtype sum by the injective rational-coordinate map and apply the signed-row
bound.

Role: supplies the uniform Gram-row condition for the rational additive large-sieve estimate.
-/
theorem reducedUnitFrequencyRationalSet_window_gram_row_le_square {Q : ℕ} (hQ : 0 < Q) (N : ℕ) :
    ∀ α : { α : ℚ // α ∈ reducedUnitFrequencyRationalSet Q },
      ∑ β : { α : ℚ // α ∈ reducedUnitFrequencyRationalSet Q },
          ‖inner ℂ
              (rationalWindowFrequencyVector (Finset.range (N + 2 * (Q * Q) - 1))
                (triangleOverlapWindow N (Q * Q)) α.val)
              (rationalWindowFrequencyVector (Finset.range (N + 2 * (Q * Q) - 1))
                (triangleOverlapWindow N (Q * Q)) β.val)‖ ≤
        2 * (N : ℝ) + 3 * ((Q * Q : ℕ) : ℝ) := by
  classical
  intro α
  let U := reducedUnitFrequencyIndexSet Q
  let F := reducedUnitFrequencyRationalSet Q
  obtain ⟨f₀, hf₀, hα⟩ := Finset.mem_image.mp α.property
  let G : ℚ → ℝ := fun β =>
    ‖inner ℂ
        (rationalWindowFrequencyVector (Finset.range (N + 2 * (Q * Q) - 1))
          (triangleOverlapWindow N (Q * Q)) (reducedUnitFrequencyRational f₀))
        (rationalWindowFrequencyVector (Finset.range (N + 2 * (Q * Q) - 1))
          (triangleOverlapWindow N (Q * Q)) β)‖
  have hInjective : Function.Injective (reducedUnitFrequencyRational (Q := Q)) :=
    reducedUnitFrequencyRational_injective
  have hsum :
    (∑ β : { β : ℚ // β ∈ F },
        ‖inner ℂ
            (rationalWindowFrequencyVector (Finset.range (N + 2 * (Q * Q) - 1))
              (triangleOverlapWindow N (Q * Q)) α.val)
            (rationalWindowFrequencyVector (Finset.range (N + 2 * (Q * Q) - 1))
              (triangleOverlapWindow N (Q * Q)) β.val)‖) =
      ∑ f ∈ U, G (reducedUnitFrequencyRational f) := by
    calc
      _ = ∑ β ∈ F, G β := by
        rw [Finset.sum_subtype F (fun _ => Iff.rfl)]
        apply Finset.sum_congr rfl
        intro β hβ
        dsimp only [G]
        rw [hα]
      _ = _ := by
        simpa only [F, reducedUnitFrequencyRationalSet] using
          (Finset.sum_image (s := U) (g := reducedUnitFrequencyRational) (f := G) hInjective.injOn)
  rw [hsum]
  simpa only [G] using (reducedUnitFrequencyRationalWindowGramRow_le_square hQ f₀ N)

/--
Inputs: a positive denominator cutoff, an interval length, a coefficient set inside the flat
part of the triangle window, and complex coefficients.

Claim: the rational additive mean square over denominators at most `Q` is at most the row bound
`2N + 3Q²` times the coefficient norm-square sum.

Proof: represent the polynomial by triangle-window frequency vectors and apply the windowed
Gram-row estimate.

Role: connects the completed reduced-frequency row bound to the additive large-sieve interface.
-/
theorem reducedUnitFrequencyRationalSet_mean_square_le_window_row {Q : ℕ} (hQ : 0 < Q) (N : ℕ)
    (S : Finset ℕ) (hST : S ⊆ Finset.range (N + 2 * (Q * Q) - 1))
    (hcentral : ∀ n ∈ S, Q * Q - 1 ≤ n ∧ n ≤ N + Q * Q - 1) (a : ℕ → ℂ) :
    rationalAdditivePolynomialMeanSquare (reducedUnitFrequencyRationalSet Q) S a ≤
      (2 * (N : ℝ) + 3 * ((Q * Q : ℕ) : ℝ)) * ∑ n ∈ S, ‖a n‖ ^ 2 := by
  have hR : 0 ≤ 2 * (N : ℝ) + 3 * ((Q * Q : ℕ) : ℝ) :=
    add_nonneg (mul_nonneg (by norm_num only) (Nat.cast_nonneg N))
      (mul_nonneg (by norm_num only) (Nat.cast_nonneg (Q * Q)))
  exact
    rationalAdditivePolynomialMeanSquare_le_of_window_gram_row_bound
      (reducedUnitFrequencyRationalSet Q) S (Finset.range (N + 2 * (Q * Q) - 1)) hST
      (triangleOverlapWindow N (Q * Q))
      (fun n hn =>
        (triangleOverlapWindow_eq_one (Nat.mul_pos hQ hQ) (hcentral n hn).1 (hcentral n hn).2).2)
      a (2 * (N : ℝ) + 3 * ((Q * Q : ℕ) : ℝ)) hR
      (reducedUnitFrequencyRationalSet_window_gram_row_le_square hQ N)

/--
Inputs: a positive denominator cutoff, an interval length, a finite support inside `[0,N)`, and
complex coefficients.

Claim: the reduced rational-frequency mean square on arbitrary support in `[0,N)` is bounded by
the same triangular-window row estimate as central support.

Proof: translate support by `Q²`, apply the central-window estimate, and use phase and coefficient
norm invariance under translation.

Role: supplies the usual finite-support interface needed by the unconditional large sieve.
-/
theorem reducedUnitFrequencyRationalSet_mean_square_le_window_row_of_range {Q : ℕ} (hQ : 0 < Q)
    (N : ℕ) (S : Finset ℕ) (hSN : S ⊆ Finset.range N) (a : ℕ → ℂ) :
    rationalAdditivePolynomialMeanSquare (reducedUnitFrequencyRationalSet Q) S a ≤
      (2 * (N : ℝ) + 3 * ((Q * Q : ℕ) : ℝ)) * ∑ n ∈ S, ‖a n‖ ^ 2 := by
  let c : ℕ := Q * Q
  let T : Finset ℕ := S.image (fun n => n + c)
  let b : ℕ → ℂ := fun m => a (m - c)
  have hc : 0 < c := by
    dsimp [c]
    exact Nat.mul_pos hQ hQ
  have hTN : T ⊆ Finset.range (N + 2 * (Q * Q) - 1) := by
    intro m hm
    rcases Finset.mem_image.mp hm with ⟨n, hn, rfl⟩
    have hnN : n < N := Finset.mem_range.mp (hSN hn)
    dsimp [T, c]
    simp only [Finset.mem_range]
    have hcc : c < 2 * c := by
      calc
        c < c + c := Nat.lt_add_of_pos_right hc
        _ = 2 * c := (two_mul c).symm
    have hbound : N + c ≤ N + 2 * c - 1 := Nat.le_sub_one_of_lt (Nat.add_lt_add_left hcc N)
    exact lt_of_lt_of_le (Nat.add_lt_add_right hnN c) (by simpa [c] using hbound)
  have hcentral : ∀ m ∈ T, Q * Q - 1 ≤ m ∧ m ≤ N + Q * Q - 1 := by
    intro m hm
    rcases Finset.mem_image.mp hm with ⟨n, hn, rfl⟩
    have hnN : n < N := Finset.mem_range.mp (hSN hn)
    dsimp [T, c]
    constructor
    · exact le_trans (Nat.sub_le _ _) (Nat.le_add_left _ _)
    · exact Nat.le_sub_one_of_lt (Nat.add_lt_add_right hnN (Q * Q))
  calc
    rationalAdditivePolynomialMeanSquare (reducedUnitFrequencyRationalSet Q) S a =
        rationalAdditivePolynomialMeanSquare (reducedUnitFrequencyRationalSet Q) T b :=
      by
      dsimp [T, b]
      exact
        (rationalAdditivePolynomialMeanSquare_shift_eq (reducedUnitFrequencyRationalSet Q) S a
            c).symm
    _ ≤ (2 * (N : ℝ) + 3 * ((Q * Q : ℕ) : ℝ)) * ∑ m ∈ T, ‖b m‖ ^ 2 := by
      dsimp [T, b]
      exact
        reducedUnitFrequencyRationalSet_mean_square_le_window_row hQ N T hTN hcentral
          (fun m => a (m - c))
    _ = (2 * (N : ℝ) + 3 * ((Q * Q : ℕ) : ℝ)) * ∑ n ∈ S, ‖a n‖ ^ 2 := by
      rw [sum_normSq_coefficients_shift_eq]

/--
Inputs: a positive denominator cutoff, a finite coefficient support contained in the interval
`[M, M + N)`, and complex coefficients.

Claim: the reduced rational-frequency mean square is bounded in terms of the interval length `N`,
independently of the interval's starting point `M`.

Proof: translate only the additive support to `[0, N)`, apply the range estimate, and use the
translation invariance of the additive mean square and coefficient energy.

Role: gives the support interval interface used by the pre-sifted hybrid large sieve.
-/
theorem reducedUnitFrequencyRationalSet_mean_square_le_of_support_Ico {Q : ℕ} (hQ : 0 < Q) (M N : ℕ)
    (S : Finset ℕ) (hS : S ⊆ Finset.Ico M (M + N)) (a : ℕ → ℂ) :
    rationalAdditivePolynomialMeanSquare (reducedUnitFrequencyRationalSet Q) S a ≤
      (2 * (N : ℝ) + 3 * ((Q * Q : ℕ) : ℝ)) * ∑ n ∈ S, ‖a n‖ ^ 2 := by
  let T : Finset ℕ := S.image (fun n => n - M)
  let b : ℕ → ℂ := fun m => a (m + M)
  have hTN : T ⊆ Finset.range N := by
    intro m hm
    rcases Finset.mem_image.mp hm with ⟨n, hn, rfl⟩
    have hnI := Finset.mem_Ico.mp (hS hn)
    simp only [Finset.mem_range]
    exact (Nat.sub_lt_iff_lt_add hnI.1).2 (by simpa only [Nat.add_comm] using hnI.2)
  have hTimage : T.image (fun n => n + M) = S := by
    ext n
    dsimp only [T]
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨m, ⟨k, hk, rfl⟩, rfl⟩
      have hkI := Finset.mem_Ico.mp (hS hk)
      simpa only [Nat.sub_add_cancel hkI.1] using hk
    · intro hn
      refine ⟨n - M, ?_, Nat.sub_add_cancel (Finset.mem_Ico.mp (hS hn)).1⟩
      exact ⟨n, hn, rfl⟩
  have hcoef : ∀ n ∈ S, b (n - M) = a n := by
    intro n hn
    have hnI := Finset.mem_Ico.mp (hS hn)
    dsimp [b]
    rw [Nat.sub_add_cancel hnI.1]
  have hmean :
    rationalAdditivePolynomialMeanSquare (reducedUnitFrequencyRationalSet Q) S a =
      rationalAdditivePolynomialMeanSquare (reducedUnitFrequencyRationalSet Q) T b := by
    calc
      rationalAdditivePolynomialMeanSquare (reducedUnitFrequencyRationalSet Q) S a =
          rationalAdditivePolynomialMeanSquare (reducedUnitFrequencyRationalSet Q) S
            (fun m => b (m - M)) :=
        by
        unfold rationalAdditivePolynomialMeanSquare
        apply Finset.sum_congr rfl
        intro α hα
        congr 1
        apply Finset.sum_congr rfl
        intro n hn
        change a n * rationalAdditiveCharacter α n = b (n - M) * rationalAdditiveCharacter α n
        rw [hcoef n hn]
      _ =
          rationalAdditivePolynomialMeanSquare (reducedUnitFrequencyRationalSet Q)
            (T.image (fun n => n + M)) (fun m => b (m - M)) :=
        by rw [hTimage]
      _ = rationalAdditivePolynomialMeanSquare (reducedUnitFrequencyRationalSet Q) T b :=
        rationalAdditivePolynomialMeanSquare_shift_eq (reducedUnitFrequencyRationalSet Q) T b M
  have henergy : (∑ m ∈ T, ‖b m‖ ^ 2) = ∑ n ∈ S, ‖a n‖ ^ 2 := by
    calc
      (∑ m ∈ T, ‖b m‖ ^ 2) = ∑ m ∈ T.image (fun n => n + M), ‖b (m - M)‖ ^ 2 :=
        (sum_normSq_coefficients_shift_eq T b M).symm
      _ = ∑ n ∈ S, ‖a n‖ ^ 2 := by
        rw [hTimage]
        apply Finset.sum_congr rfl
        intro n hn
        rw [hcoef n hn]
  calc
    rationalAdditivePolynomialMeanSquare (reducedUnitFrequencyRationalSet Q) S a =
        rationalAdditivePolynomialMeanSquare (reducedUnitFrequencyRationalSet Q) T b :=
      hmean
    _ ≤ (2 * (N : ℝ) + 3 * ((Q * Q : ℕ) : ℝ)) * ∑ m ∈ T, ‖b m‖ ^ 2 :=
      reducedUnitFrequencyRationalSet_mean_square_le_window_row_of_range hQ N T hTN b
    _ = (2 * (N : ℝ) + 3 * ((Q * Q : ℕ) : ℝ)) * ∑ n ∈ S, ‖a n‖ ^ 2 := by rw [henergy]

set_option linter.style.haveILetI false

/--
Inputs: a finite family of product levels, a finite divisor family and complementary-modulus
function at each level, a modulus cutoff, and a finite polynomial.

Claim: the normalized Ramanujan-primitive mean squares over all these product levels are bounded
by the rational additive mean square over reduced frequencies up to the cutoff.

Proof: apply the fixed-product Parseval estimate at each level, identify its reduced additive
mean square with the rational-frequency layer, use disjointness of layers with distinct reduced
denominators, and include these layers in the full reduced-frequency set.

Role: separates the support-independent frequency comparison from the range large-sieve bound.
-/
theorem primitive_ramanujan_weighted_fixedProduct_levels_le_rationalMeanSquare (H : Finset ℕ)
    (hH : ∀ h, h ∈ H → 1 < h) (Q : ℕ → Finset ℕ) (r : ℕ → ℕ → ℕ)
    (hQ : ∀ h, h ∈ H → ∀ q, q ∈ Q h → q ∣ h) (hprod : ∀ h, h ∈ H → ∀ q, q ∈ Q h → q * r h q = h)
    (hq : ∀ h, h ∈ H → ∀ q, q ∈ Q h → 1 < q) (hr : ∀ h, h ∈ H → ∀ q, q ∈ Q h → 0 < r h q)
    (hcop : ∀ h, h ∈ H → ∀ q, q ∈ Q h → Nat.Coprime q (r h q)) (Qmax : ℕ)
    (hHmax : ∀ h, h ∈ H → h ≤ Qmax) (S : Finset ℕ) (a : ℕ → ℂ) :
    (∑ h ∈ H.attach,
        ∑ q ∈ (Q h.val).attach,
          (q.val : ℝ) / (Nat.totient h.val : ℝ) *
            primitiveCharacterPolynomialMeanSquare q.val (hq h.val h.property q.val q.property) S
              (fun n =>
                a n *
                  @ramanujanSum (r h.val q.val) n
                    ⟨Nat.ne_of_gt (hr h.val h.property q.val q.property)⟩)) ≤
      rationalAdditivePolynomialMeanSquare (reducedUnitFrequencyRationalSet Qmax) S a := by
  classical
  let F : { h // h ∈ H } → Finset ℚ := fun h => by
    letI : NeZero h.val := ⟨Nat.ne_of_gt (lt_trans Nat.zero_lt_one (hH h.val h.property))⟩
    exact (reducedUnitFrequencySet h.val).image (fun x => (x.val : ℚ) / h.val)
  have hdisj : Set.PairwiseDisjoint (H.attach : Set { h // h ∈ H }) F := by
    intro h₁ hh₁ h₂ hh₂ hne
    letI : NeZero h₁.val := ⟨Nat.ne_of_gt (lt_trans Nat.zero_lt_one (hH h₁.val h₁.property))⟩
    letI : NeZero h₂.val := ⟨Nat.ne_of_gt (lt_trans Nat.zero_lt_one (hH h₂.val h₂.property))⟩
    change
      Disjoint ((reducedUnitFrequencySet h₁.val).image _) ((reducedUnitFrequencySet h₂.val).image _)
    apply Finset.disjoint_left.mpr
    intro α hα₁ hα₂
    rcases Finset.mem_image.mp hα₁ with ⟨x, hx, hαx⟩
    rcases Finset.mem_image.mp hα₂ with ⟨y, hy, hαy⟩
    have hxunit : IsUnit x := (Finset.mem_filter.mp hx).2
    have hyunit : IsUnit y := (Finset.mem_filter.mp hy).2
    have hxcast : IsUnit ((x.val : ℕ) : ZMod h₁.val) := by
      rw [ZMod.natCast_zmod_val]
      exact hxunit
    have hycast : IsUnit ((y.val : ℕ) : ZMod h₂.val) := by
      rw [ZMod.natCast_zmod_val]
      exact hyunit
    have hxcop : Nat.Coprime x.val h₁.val := (ZMod.isUnit_iff_coprime x.val h₁.val).mp hxcast
    have hycop : Nat.Coprime y.val h₂.val := (ZMod.isUnit_iff_coprime y.val h₂.val).mp hycast
    have hfrac : (x.val : ℚ) / h₁.val = (y.val : ℚ) / h₂.val := hαx.trans hαy.symm
    have hden :=
      (rational_reduced_fraction_unique (Nat.zero_lt_of_lt (hH h₁.val h₁.property))
          (Nat.zero_lt_of_lt (hH h₂.val h₂.property)) hxcop hycop hfrac).1
    exact hne (Subtype.ext hden)
  have hmean :
    (∑ h ∈ H.attach,
        ∑ q ∈ (Q h.val).attach,
          (q.val : ℝ) / (Nat.totient h.val : ℝ) *
            primitiveCharacterPolynomialMeanSquare q.val (hq h.val h.property q.val q.property) S
              (fun n =>
                a n *
                  @ramanujanSum (r h.val q.val) n
                    ⟨Nat.ne_of_gt (hr h.val h.property q.val q.property)⟩)) ≤
      ∑ h ∈ H.attach, reducedAdditivePolynomialMeanSquare h.val (hH h.val h.property) S a := by
    apply Finset.sum_le_sum
    intro h hh
    letI : NeZero h.val := ⟨Nat.ne_of_gt (lt_trans Nat.zero_lt_one (hH h.val h.property))⟩
    exact
      primitive_ramanujan_weighted_fixedProduct_family_normalized_le (hH h.val h.property) (Q h.val)
        (r h.val) (hQ h.val h.property) (hprod h.val h.property) (hq h.val h.property)
        (hr h.val h.property) (hcop h.val h.property) S a
  have hEq :
    (∑ h ∈ H.attach, reducedAdditivePolynomialMeanSquare h.val (hH h.val h.property) S a) =
      ∑ h ∈ H.attach, rationalAdditivePolynomialMeanSquare (F h) S a := by
    apply Finset.sum_congr rfl
    intro h hh
    letI : NeZero h.val := ⟨Nat.ne_of_gt (lt_trans Nat.zero_lt_one (hH h.val h.property))⟩
    exact reducedAdditivePolynomialMeanSquare_eq_rational (hH h.val h.property) S a
  have hsubset : H.attach.biUnion F ⊆ reducedUnitFrequencyRationalSet Qmax := by
    intro α hα
    rcases Finset.mem_biUnion.mp hα with ⟨h, hh, hα⟩
    letI : NeZero h.val := ⟨Nat.ne_of_gt (lt_trans Nat.zero_lt_one (hH h.val h.property))⟩
    change α ∈ (reducedUnitFrequencySet h.val).image _ at hα
    rcases Finset.mem_image.mp hα with ⟨x, hx, rfl⟩
    have hxunit : IsUnit x := (Finset.mem_filter.mp hx).2
    have hxcast : IsUnit ((x.val : ℕ) : ZMod h.val) := by
      rw [ZMod.natCast_zmod_val]
      exact hxunit
    have hcop : Nat.Coprime x.val h.val := (ZMod.isUnit_iff_coprime x.val h.val).mp hxcast
    have hhmax := hHmax h.val h.property
    let f : ReducedUnitFrequencyIndex Qmax :=
      ⟨⟨⟨h.val, Nat.lt_succ_of_le hhmax⟩, by simpa using hH h.val h.property⟩,
        ⟨⟨x.val, ZMod.val_lt x⟩, hcop⟩⟩
    apply Finset.mem_image.mpr
    refine ⟨f, Finset.mem_univ _, ?_⟩
    dsimp [reducedUnitFrequencyRational, f]
  calc
    _ ≤ ∑ h ∈ H.attach, reducedAdditivePolynomialMeanSquare h.val (hH h.val h.property) S a := hmean
    _ = rationalAdditivePolynomialMeanSquare (H.attach.biUnion F) S a := by
      rw [hEq]
      unfold rationalAdditivePolynomialMeanSquare
      rw [Finset.sum_biUnion hdisj]
    _ ≤ rationalAdditivePolynomialMeanSquare (reducedUnitFrequencyRationalSet Qmax) S a := by
      unfold rationalAdditivePolynomialMeanSquare
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro α hα hnot
      exact Complex.normSq_nonneg _

/--
Inputs: the fixed-product family parameters, a modulus cutoff, and a coefficient support in
`range N`.

Claim: the normalized Ramanujan-primitive mean squares are bounded by the additive large-sieve
majorant `(2N + 3 Qmax²)` times the coefficient energy.

Proof: use the support-independent rational-frequency comparison, then apply the range version of
the additive large sieve.

Role: preserves the range-supported API for callers that need an explicit numerical bound.
-/
theorem primitive_ramanujan_weighted_fixedProduct_levels_le_additive_large_sieve (H : Finset ℕ)
    (hH : ∀ h, h ∈ H → 1 < h) (Q : ℕ → Finset ℕ) (r : ℕ → ℕ → ℕ)
    (hQ : ∀ h, h ∈ H → ∀ q, q ∈ Q h → q ∣ h) (hprod : ∀ h, h ∈ H → ∀ q, q ∈ Q h → q * r h q = h)
    (hq : ∀ h, h ∈ H → ∀ q, q ∈ Q h → 1 < q) (hr : ∀ h, h ∈ H → ∀ q, q ∈ Q h → 0 < r h q)
    (hcop : ∀ h, h ∈ H → ∀ q, q ∈ Q h → Nat.Coprime q (r h q)) (Qmax : ℕ) (hQmaxPos : 0 < Qmax)
    (hHmax : ∀ h, h ∈ H → h ≤ Qmax) (N : ℕ) (S : Finset ℕ) (hSN : S ⊆ Finset.range N) (a : ℕ → ℂ) :
    (∑ h ∈ H.attach,
        ∑ q ∈ (Q h.val).attach,
          (q.val : ℝ) / (Nat.totient h.val : ℝ) *
            primitiveCharacterPolynomialMeanSquare q.val (hq h.val h.property q.val q.property) S
              (fun n =>
                a n *
                  @ramanujanSum (r h.val q.val) n
                    ⟨Nat.ne_of_gt (hr h.val h.property q.val q.property)⟩)) ≤
      (2 * (N : ℝ) + 3 * ((Qmax * Qmax : ℕ) : ℝ)) * ∑ n ∈ S, ‖a n‖ ^ 2 := by
  calc
    _ ≤ rationalAdditivePolynomialMeanSquare (reducedUnitFrequencyRationalSet Qmax) S a :=
      primitive_ramanujan_weighted_fixedProduct_levels_le_rationalMeanSquare H hH Q r hQ hprod hq hr
        hcop Qmax hHmax S a
    _ ≤ (2 * (N : ℝ) + 3 * ((Qmax * Qmax : ℕ) : ℝ)) * ∑ n ∈ S, ‖a n‖ ^ 2 :=
      reducedUnitFrequencyRationalSet_mean_square_le_window_row_of_range hQmaxPos N S hSN a

set_option linter.style.haveILetI true

/-!
The next lemma records the finite reindexing from pairs to product levels. For a fixed product
`h`, the first moduli are obtained from the pairs with product `h`; the second modulus is then
uniquely recovered as `h / q`.
-/

/--
Inputs: a finite family of modulus pairs with positive first components, and a real-valued weight
on product and first-modulus coordinates.

Claim: summing that weight over the product-level first-modulus families equals summing it once
over the original pair family.

Proof: identify the union of the level-indexed `(h,q)` images with the image of the pair family
under `(q,r) ↦ (q*r,q)`. Distinct product levels give disjoint image sets, and the map is
injective because the first modulus is positive.

Role: justifies regrouping an arbitrary pair family before applying the fixed-product estimate.
-/
theorem sum_productLevel_pairFamily_eq {P : Finset (ℕ × ℕ)} (hPq : ∀ p, p ∈ P → 0 < p.1)
    (f : ℕ × ℕ → ℝ) :
    (∑ h ∈ (P.image fun p => p.1 * p.2).attach,
        ∑ q ∈ ((P.filter fun p => p.1 * p.2 = h.val).image Prod.fst).attach, f (h.val, q.val)) =
      ∑ p ∈ P.attach, f (p.val.1 * p.val.2, p.val.1) := by
  classical
  let H : Finset ℕ := P.image fun p => p.1 * p.2
  let Q : ℕ → Finset ℕ := fun h => (P.filter fun p => p.1 * p.2 = h).image Prod.fst
  let F : { h // h ∈ H } → Finset (ℕ × ℕ) := fun h => (Q h.val).image fun q => (h.val, q)
  have hdisj : Set.PairwiseDisjoint (H.attach : Set { h // h ∈ H }) F := by
    intro h hh k hk hne
    apply Finset.disjoint_left.mpr
    intro z hz1 hz2
    rcases Finset.mem_image.mp hz1 with ⟨q, hq, rfl⟩
    rcases Finset.mem_image.mp hz2 with ⟨q', hq', hpair⟩
    exact hne (Subtype.ext (congrArg Prod.fst hpair).symm)
  have hinner :
    (∑ h ∈ H.attach, ∑ q ∈ (Q h.val).attach, f (h.val, q.val)) =
      ∑ h ∈ H.attach, ∑ z ∈ F h, f z := by
    apply Finset.sum_congr rfl
    intro h hh
    calc
      _ = ∑ q ∈ Q h.val, f (h.val, q) := Finset.sum_attach (Q h.val) (fun q => f (h.val, q))
      _ = ∑ z ∈ F h, f z := by
        dsimp only [F]
        symm
        apply Finset.sum_image
        intro q hq q' hq' heq
        exact congrArg Prod.snd heq
  have hunion : (∑ h ∈ H.attach, ∑ z ∈ F h, f z) = ∑ z ∈ H.attach.biUnion F, f z := by
    rw [Finset.sum_biUnion hdisj]
  have hset : H.attach.biUnion F = P.image (fun p => (p.1 * p.2, p.1)) := by
    ext z
    constructor
    · intro hz
      rcases Finset.mem_biUnion.mp hz with ⟨h, hh, hz⟩
      rcases Finset.mem_image.mp hz with ⟨q, hq, rfl⟩
      rcases Finset.mem_image.mp hq with ⟨p, hp, hq⟩
      have hpP : p ∈ P := (Finset.mem_filter.mp hp).1
      have hpProd : p.1 * p.2 = h.val := (Finset.mem_filter.mp hp).2
      apply Finset.mem_image.mpr
      refine ⟨p, hpP, ?_⟩
      exact Prod.ext hpProd hq
    · intro hz
      rcases Finset.mem_image.mp hz with ⟨p, hp, rfl⟩
      have hh : p.1 * p.2 ∈ H := Finset.mem_image.mpr ⟨p, hp, rfl⟩
      have hq : p.1 ∈ Q (p.1 * p.2) := by
        apply Finset.mem_image.mpr
        refine ⟨p, Finset.mem_filter.mpr ⟨hp, rfl⟩, rfl⟩
      apply Finset.mem_biUnion.mpr
      refine ⟨⟨p.1 * p.2, hh⟩, Finset.mem_attach H _, ?_⟩
      apply Finset.mem_image.mpr
      exact ⟨p.1, hq, rfl⟩
  have himage :
    (∑ z ∈ P.image (fun p => (p.1 * p.2, p.1)), f z) =
      ∑ p ∈ P.attach, f (p.val.1 * p.val.2, p.val.1) := by
    rw [Finset.sum_image]
    · exact (Finset.sum_attach P (fun p => f (p.1 * p.2, p.1))).symm
    · intro p hp q hq heq
      have hpProd := congrArg Prod.fst heq
      have hpFirst := congrArg Prod.snd heq
      change p.1 * p.2 = q.1 * q.2 at hpProd
      change p.1 = q.1 at hpFirst
      have hpSecond : p.2 = q.2 := by
        rw [hpFirst] at hpProd
        exact Nat.mul_left_cancel (hPq q hq) hpProd
      exact Prod.ext hpFirst hpSecond
  calc
    _ = ∑ h ∈ H.attach, ∑ z ∈ F h, f z := hinner
    _ = ∑ z ∈ H.attach.biUnion F, f z := hunion
    _ = ∑ z ∈ P.image (fun p => (p.1 * p.2, p.1)), f z := by rw [hset]
    _ = _ := himage

/--
Inputs: a finite family of modulus pairs with first modulus greater than one, positive second
modulus, pairwise coprime components, a product cutoff, and a finite polynomial.

Claim: the normalized Ramanujan-primitive mean squares over the pair family are bounded by the
rational additive mean square over reduced frequencies up to the product cutoff.

Proof: group the pairs by their product, recover the complementary modulus as the product divided
by the first modulus, apply the fixed-product Parseval estimate on each level, and include the
disjoint rational-frequency layers in the common reduced-frequency set.

Role: separates the support-independent frequency comparison from the range large-sieve bound.
-/
theorem primitive_ramanujan_weighted_pair_family_le_rationalMeanSquare (P : Finset (ℕ × ℕ))
    (hPq : ∀ p, p ∈ P → 1 < p.1) (hPr : ∀ p, p ∈ P → 0 < p.2)
    (hPcop : ∀ p, p ∈ P → Nat.Coprime p.1 p.2) (Qmax : ℕ) (hPmax : ∀ p, p ∈ P → p.1 * p.2 ≤ Qmax)
    (S : Finset ℕ) (a : ℕ → ℂ) :
    (∑ p ∈ P.attach,
        (p.val.1 : ℝ) / (Nat.totient (p.val.1 * p.val.2) : ℝ) *
          primitiveCharacterPolynomialMeanSquare p.val.1 (hPq p.val p.property) S
            (fun n => a n * @ramanujanSum p.val.2 n ⟨Nat.ne_of_gt (hPr p.val p.property)⟩)) ≤
      rationalAdditivePolynomialMeanSquare (reducedUnitFrequencyRationalSet Qmax) S a := by
  classical
  let H : Finset ℕ := P.image fun p => p.1 * p.2
  let Q : ℕ → Finset ℕ := fun h => (P.filter fun p => p.1 * p.2 = h).image Prod.fst
  let r : ℕ → ℕ → ℕ := fun h q => h / q
  have hH : ∀ h, h ∈ H → 1 < h := by
    intro h hh
    rcases Finset.mem_image.mp hh with ⟨p, hp, rfl⟩
    exact lt_of_lt_of_le (hPq p hp) (Nat.le_mul_of_pos_right _ (hPr p hp))
  have hHmax : ∀ h, h ∈ H → h ≤ Qmax := by
    intro h hh
    rcases Finset.mem_image.mp hh with ⟨p, hp, rfl⟩
    exact hPmax p hp
  have hQ : ∀ h, h ∈ H → ∀ q, q ∈ Q h → q ∣ h := by
    intro h hh q hq
    rcases Finset.mem_image.mp hq with ⟨p, hp, hfirst⟩
    have hpP : p ∈ P := (Finset.mem_filter.mp hp).1
    have hprod : p.1 * p.2 = h := (Finset.mem_filter.mp hp).2
    rw [← hfirst, ← hprod]
    exact ⟨p.2, rfl⟩
  have hprod : ∀ h, h ∈ H → ∀ q, q ∈ Q h → q * r h q = h := by
    intro h hh q hq
    exact Nat.mul_div_cancel' (hQ h hh q hq)
  have hq : ∀ h, h ∈ H → ∀ q, q ∈ Q h → 1 < q := by
    intro h hh q hq
    rcases Finset.mem_image.mp hq with ⟨p, hp, hfirst⟩
    exact hfirst ▸ hPq p (Finset.mem_filter.mp hp).1
  have hr : ∀ h, h ∈ H → ∀ q, q ∈ Q h → 0 < r h q := by
    intro h hh q hq
    rcases Finset.mem_image.mp hq with ⟨p, hp, hfirst⟩
    have hpP : p ∈ P := (Finset.mem_filter.mp hp).1
    have hdiv : h / q = p.2 := by
      calc
        h / q = (p.1 * p.2) / p.1 := by rw [(Finset.mem_filter.mp hp).2, hfirst]
        _ = p.2 := Nat.mul_div_cancel_left p.2 (Nat.zero_lt_of_lt (hPq p hpP))
    rw [show r h q = h / q by rfl, hdiv]
    exact hPr p hpP
  have hcop : ∀ h, h ∈ H → ∀ q, q ∈ Q h → Nat.Coprime q (r h q) := by
    intro h hh q hq
    rcases Finset.mem_image.mp hq with ⟨p, hp, hfirst⟩
    have hpP : p ∈ P := (Finset.mem_filter.mp hp).1
    have hdiv : h / q = p.2 := by
      calc
        h / q = (p.1 * p.2) / p.1 := by rw [(Finset.mem_filter.mp hp).2, hfirst]
        _ = p.2 := Nat.mul_div_cancel_left p.2 (Nat.zero_lt_of_lt (hPq p hpP))
    rw [show r h q = h / q by rfl, hdiv, ← hfirst]
    exact hPcop p hpP
  let f : ℕ × ℕ → ℝ := fun z =>
    if hqz : 1 < z.2 then
      if hrz : 0 < z.1 / z.2 then
        (z.2 : ℝ) / (Nat.totient z.1 : ℝ) *
          primitiveCharacterPolynomialMeanSquare z.2 hqz S
            (fun n => a n * @ramanujanSum (z.1 / z.2) n ⟨Nat.ne_of_gt hrz⟩)
      else 0
    else 0
  have hpair :
    (∑ p ∈ P.attach,
        (p.val.1 : ℝ) / (Nat.totient (p.val.1 * p.val.2) : ℝ) *
          primitiveCharacterPolynomialMeanSquare p.val.1 (hPq p.val p.property) S
            (fun n => a n * @ramanujanSum p.val.2 n ⟨Nat.ne_of_gt (hPr p.val p.property)⟩)) =
      ∑ p ∈ P.attach, f (p.val.1 * p.val.2, p.val.1) := by
    apply Finset.sum_congr rfl
    intro p hp
    have hdiv : p.val.1 * p.val.2 / p.val.1 = p.val.2 :=
      Nat.mul_div_cancel_left p.val.2 (Nat.zero_lt_of_lt (hPq p.val p.property))
    dsimp only [f]
    rw [dite_eq_left (hPq p.val p.property)]
    rw [dite_eq_left
        (by
          rw [hdiv]; exact hPr p.val p.property)]
    simp only [hdiv]
  have hgroup :
    (∑ h ∈ H.attach, ∑ q ∈ (Q h.val).attach, f (h.val, q.val)) =
      ∑ p ∈ P.attach, f (p.val.1 * p.val.2, p.val.1) := by
    simpa only [H, Q] using
      (sum_productLevel_pairFamily_eq (P := P) (fun p hp => Nat.zero_lt_of_lt (hPq p hp)) f)
  have hlevel :
    (∑ h ∈ H.attach, ∑ q ∈ (Q h.val).attach, f (h.val, q.val)) =
      ∑ h ∈ H.attach,
        ∑ q ∈ (Q h.val).attach,
          (q.val : ℝ) / (Nat.totient h.val : ℝ) *
            primitiveCharacterPolynomialMeanSquare q.val (hq h.val h.property q.val q.property) S
              (fun n =>
                a n *
                  @ramanujanSum (r h.val q.val) n
                    ⟨Nat.ne_of_gt (hr h.val h.property q.val q.property)⟩) := by
    apply Finset.sum_congr rfl
    intro h hh
    apply Finset.sum_congr rfl
    intro q hq'
    have hqval := hq h.val h.property q.val q.property
    have hrval := hr h.val h.property q.val q.property
    dsimp only [f]
    rw [dite_eq_left hqval, dite_eq_left hrval]
  have hbase :=
    primitive_ramanujan_weighted_fixedProduct_levels_le_rationalMeanSquare H hH Q r hQ hprod hq hr
      hcop Qmax hHmax S a
  calc
    _ = ∑ p ∈ P.attach, f (p.val.1 * p.val.2, p.val.1) := hpair
    _ = ∑ h ∈ H.attach, ∑ q ∈ (Q h.val).attach, f (h.val, q.val) := hgroup.symm
    _ =
        ∑ h ∈ H.attach,
          ∑ q ∈ (Q h.val).attach,
            (q.val : ℝ) / (Nat.totient h.val : ℝ) *
              primitiveCharacterPolynomialMeanSquare q.val (hq h.val h.property q.val q.property) S
                (fun n =>
                  a n *
                    @ramanujanSum (r h.val q.val) n
                      ⟨Nat.ne_of_gt (hr h.val h.property q.val q.property)⟩) :=
      hlevel
    _ ≤ _ := hbase

/--
Inputs: a finite family of modulus pairs with first modulus greater than one, positive second
modulus, pairwise coprime components, a product cutoff, and a finite polynomial.

Claim: the normalized Ramanujan-primitive mean squares over the pair family are bounded by one
additive large-sieve estimate, with no factor for the number of pairs or product levels.

Proof: group the pairs by their product, recover the complementary modulus as the product divided
by the first modulus, apply the fixed-product Parseval estimate on each level, and use the
pair-family reindexing and common rational-frequency large sieve once.

Role: supplies the arbitrary finite-pair form of the pre-sifted Selberg large-sieve bound.
-/
theorem primitive_ramanujan_weighted_pair_family_le_additive_large_sieve (P : Finset (ℕ × ℕ))
    (hPq : ∀ p, p ∈ P → 1 < p.1) (hPr : ∀ p, p ∈ P → 0 < p.2)
    (hPcop : ∀ p, p ∈ P → Nat.Coprime p.1 p.2) (Qmax : ℕ) (hQmaxPos : 0 < Qmax)
    (hPmax : ∀ p, p ∈ P → p.1 * p.2 ≤ Qmax) (N : ℕ) (S : Finset ℕ) (hSN : S ⊆ Finset.range N)
    (a : ℕ → ℂ) :
    (∑ p ∈ P.attach,
        (p.val.1 : ℝ) / (Nat.totient (p.val.1 * p.val.2) : ℝ) *
          primitiveCharacterPolynomialMeanSquare p.val.1 (hPq p.val p.property) S
            (fun n => a n * @ramanujanSum p.val.2 n ⟨Nat.ne_of_gt (hPr p.val p.property)⟩)) ≤
      (2 * (N : ℝ) + 3 * ((Qmax * Qmax : ℕ) : ℝ)) * ∑ n ∈ S, ‖a n‖ ^ 2 := by
  calc
    _ ≤ rationalAdditivePolynomialMeanSquare (reducedUnitFrequencyRationalSet Qmax) S a :=
      primitive_ramanujan_weighted_pair_family_le_rationalMeanSquare P hPq hPr hPcop Qmax hPmax S a
    _ ≤ (2 * (N : ℝ) + 3 * ((Qmax * Qmax : ℕ) : ℝ)) * ∑ n ∈ S, ‖a n‖ ^ 2 :=
      reducedUnitFrequencyRationalSet_mean_square_le_window_row_of_range hQmaxPos N S hSN a

/--
Inputs: distinct reduced unit frequencies modulo two moduli bounded by `Q`.

Claim: the complex exponential phases are separated by at least `4 / Q^2`.

Proof: represent the frequencies by their canonical rational numbers, use their circular
separation, and apply the sine lower bound for the chord between unit-circle points.

Role: bounds the denominator of every off-diagonal geometric kernel in the reduced-frequency
large-sieve sum.
-/
theorem reducedUnitFrequency_complexPhase_distance {q r Q : ℕ} [NeZero q] [NeZero r] (hq : 1 < q)
    (hr : 1 < r) (hqQ : q ≤ Q) (hrQ : r ≤ Q) (x : ZMod q) (hx : IsUnit x) (y : ZMod r)
    (hy : IsUnit y) (hfrac : (x.val : ℚ) / q ≠ (y.val : ℚ) / r) :
    4 / ((Q : ℝ) * Q) ≤
      ‖1 -
          Complex.exp
            (Complex.I * ((2 * Real.pi * ((x.val : ℝ) / q - (y.val : ℝ) / r) : ℝ) : ℂ))‖ := by
  have hqpos : 0 < q := Nat.zero_lt_of_lt hq
  have hrpos : 0 < r := Nat.zero_lt_of_lt hr
  obtain ⟨hxpos, hxq⟩ := zmod_unit_value_bounds hq x hx
  obtain ⟨hypos, hyr⟩ := zmod_unit_value_bounds hr y hy
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hqpos
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hrpos
  have hxposR : 0 < (x.val : ℝ) / q := div_pos (by exact_mod_cast hxpos) hqR
  have hyposR : 0 < (y.val : ℝ) / r := div_pos (by exact_mod_cast hypos) hrR
  have hxltR : (x.val : ℝ) / q < 1 := by
    rw [div_lt_iff₀ hqR]
    simpa only [one_mul] using (show (x.val : ℝ) < q by exact_mod_cast hxq)
  have hyltR : (y.val : ℝ) / r < 1 := by
    rw [div_lt_iff₀ hrR]
    simpa only [one_mul] using (show (y.val : ℝ) < r by exact_mod_cast hyr)
  let d : ℝ := (x.val : ℝ) / q - (y.val : ℝ) / r
  have hd : |d| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> dsimp [d] <;> linarith only [hxposR, hyposR, hxltR, hyltR]
  have hsepQ := reducedUnitFrequency_circularSeparation hq hr hqQ hrQ x hx y hy hfrac
  have hsep : 1 / ((Q : ℝ) * Q) ≤ min |d| (1 - |d|) := by
    dsimp [d]
    simpa only [Rat.cast_div, Rat.cast_mul, Rat.cast_one, Rat.cast_abs, Rat.cast_min, Rat.cast_sub,
      Rat.cast_natCast] using (Rat.cast_le (K := ℝ)).2 hsepQ
  have h := complex_exp_distance_ge_of_circular_separation hd hsep
  calc
    4 / ((Q : ℝ) * Q) = 4 * (1 / ((Q : ℝ) * Q)) := by ring
    _ ≤ ‖1 - Complex.exp (Complex.I * ((2 * Real.pi * d : ℝ) : ℂ))‖ := h
    _ = _ := by dsimp [d]

/--
Inputs: two reduced unit frequencies, a positive lower bound for their circular distance, and
the interval and taper lengths.

Claim: their overlap kernel is bounded in terms of that actual distance lower bound.

Proof: the canonical representatives lie in the unit interval, so their difference has absolute
value at most one; apply the distance-sensitive phase-kernel estimate.

Role: preserves the decay by frequency shell needed for the large-sieve Gram row sum.
-/
theorem reducedUnitFrequency_overlapKernel_norm_le_of_circular_separation {q r : ℕ} [NeZero q]
    [NeZero r] (hq : 1 < q) (hr : 1 < r) (x : ZMod q) (hx : IsUnit x) (y : ZMod r) (hy : IsUnit y)
    (ε : ℝ) (hε : 0 < ε)
    (hsep : ε ≤ min |(x.val : ℝ) / q - (y.val : ℝ) / r| (1 - |(x.val : ℝ) / q - (y.val : ℝ) / r|))
    (N L : ℕ) :
    ‖∑ n ∈ Finset.range (N + 2 * L - 1),
          (triangleOverlapWindowWeight N L n : ℂ) *
            Complex.exp
                (Complex.I * ((2 * Real.pi * ((x.val : ℝ) / q - (y.val : ℝ) / r) : ℝ) : ℂ)) ^
              n‖ ≤
      ‖(L : ℂ)⁻¹‖ * min ((N + L : ℕ) : ℝ) (1 / (2 * ε)) * min (L : ℝ) (1 / (2 * ε)) := by
  let d : ℝ := (x.val : ℝ) / q - (y.val : ℝ) / r
  have hxpos := zmod_unit_value_bounds hq x hx
  have hypos := zmod_unit_value_bounds hr y hy
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hq)
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hr)
  have hxlower : 0 ≤ (x.val : ℝ) / q := div_nonneg (by exact_mod_cast hxpos.1.le) hqpos.le
  have hxupper : (x.val : ℝ) / q ≤ 1 := (div_le_one hqpos).2 (by exact_mod_cast hxpos.2.le)
  have hylower : 0 ≤ (y.val : ℝ) / r := div_nonneg (by exact_mod_cast hypos.1.le) hrpos.le
  have hyupper : (y.val : ℝ) / r ≤ 1 := (div_le_one hrpos).2 (by exact_mod_cast hypos.2.le)
  have hd : |d| ≤ 1 := by
    dsimp only [d]
    rw [abs_le]
    constructor <;> linarith only [hxlower, hxupper, hylower, hyupper]
  have hsep' : ε ≤ min |d| (1 - |d|) := by simpa only [d] using hsep
  simpa only [d] using
    triangleOverlapWindowWeight_fourier_norm_le_of_circular_separation N L d ε hd hε hsep'

/--
Inputs: distinct reduced unit frequencies with denominators at most `Q`, an interval length, and
a taper length.

Claim: their overlap Fourier kernel is bounded by the two geometric envelopes with phase distance
replaced by the common lower bound `4 / Q^2`.

Proof: use circular frequency separation to bound the phase denominator, then apply the overlap
kernel estimate and monotonicity of each minimum.

Role: gives a denominator-only off-diagonal bound for the tapered Gram matrix.
-/
theorem reducedUnitFrequency_overlapKernel_norm_le {q r Q : ℕ} [NeZero q] [NeZero r] (hq : 1 < q)
    (hr : 1 < r) (hqQ : q ≤ Q) (hrQ : r ≤ Q) (x : ZMod q) (hx : IsUnit x) (y : ZMod r)
    (hy : IsUnit y) (hfrac : (x.val : ℚ) / q ≠ (y.val : ℚ) / r) (N L : ℕ) :
    ‖∑ n ∈ Finset.range (N + 2 * L - 1),
          (triangleOverlapWindowWeight N L n : ℂ) *
            Complex.exp
                (Complex.I * ((2 * Real.pi * ((x.val : ℝ) / q - (y.val : ℝ) / r) : ℝ) : ℂ)) ^
              n‖ ≤
      ‖(L : ℂ)⁻¹‖ * min ((N + L : ℕ) : ℝ) (((Q : ℝ) * Q) / 2) *
        min (L : ℝ) (((Q : ℝ) * Q) / 2) := by
  classical
  let z : ℂ :=
    Complex.exp (Complex.I * ((2 * Real.pi * ((x.val : ℝ) / q - (y.val : ℝ) / r) : ℝ) : ℂ))
  have hQpos : 0 < (Q : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hq).trans_le hqQ
  have hphase := reducedUnitFrequency_complexPhase_distance hq hr hqQ hrQ x hx y hy hfrac
  have hden : 0 < ‖1 - z‖ := by
    have hpos : 0 < 4 / ((Q : ℝ) * Q) := div_pos (by norm_num only) (mul_pos hQpos hQpos)
    have h := lt_of_lt_of_le hpos hphase
    simpa only [z] using h
  have hz : ‖z‖ = 1 := by
    dsimp only [z]
    exact Complex.norm_exp_I_mul_ofReal _
  have hzne : z ≠ 1 := by
    intro heq
    have hz0 : ‖1 - z‖ = 0 := by rw [heq, sub_self, norm_zero]
    exact (ne_of_gt hden) hz0
  have hmul : 4 ≤ ((Q : ℝ) * Q) * ‖1 - z‖ := by
    calc
      4 = ((Q : ℝ) * Q) * (4 / ((Q : ℝ) * Q)) := by field_simp [ne_of_gt (mul_pos hQpos hQpos)]
      _ ≤ ((Q : ℝ) * Q) * ‖1 - z‖ := mul_le_mul_of_nonneg_left hphase (mul_nonneg hQpos.le hQpos.le)
  have hscale : 2 / ‖1 - z‖ ≤ ((Q : ℝ) * Q) / 2 := by
    apply (div_le_div_iff₀ hden (by norm_num only : (0 : ℝ) < 2)).2
    nlinarith only [hmul]
  have hfirst := unit_circle_geometric_sum_norm_le_min hz hzne (N + L)
  have hsecond := reverse_unit_circle_geometric_sum_norm_le_min hz hzne L
  have hfirst' := min_le_min_left ((N + L : ℕ) : ℝ) hscale
  have hsecond' := min_le_min_left (L : ℝ) hscale
  have hfirstNonneg : 0 ≤ min ((N + L : ℕ) : ℝ) (2 / ‖1 - z‖) := le_trans (norm_nonneg _) hfirst
  have hsecondNonneg : 0 ≤ min (L : ℝ) (2 / ‖1 - z‖) := le_trans (norm_nonneg _) hsecond
  have hfirstBound :
    min ((N + L : ℕ) : ℝ) (2 / ‖1 - z‖) ≤ min ((N + L : ℕ) : ℝ) (((Q : ℝ) * Q) / 2) := hfirst'
  have hsecondBound : min (L : ℝ) (2 / ‖1 - z‖) ≤ min (L : ℝ) (((Q : ℝ) * Q) / 2) := hsecond'
  have hkernel := triangleOverlapWindowWeight_fourier_norm_le N L z hz hzne
  calc
    ‖∑ n ∈ Finset.range (N + 2 * L - 1), (triangleOverlapWindowWeight N L n : ℂ) * z ^ n‖ ≤
        ‖(L : ℂ)⁻¹‖ * min ((N + L : ℕ) : ℝ) (2 / ‖1 - z‖) * min (L : ℝ) (2 / ‖1 - z‖) :=
      hkernel
    _ ≤ ‖(L : ℂ)⁻¹‖ * min ((N + L : ℕ) : ℝ) (((Q : ℝ) * Q) / 2) * min (L : ℝ) (((Q : ℝ) * Q) / 2) :=
      by
      calc
        _ ≤ (‖(L : ℂ)⁻¹‖ * min ((N + L : ℕ) : ℝ) (((Q : ℝ) * Q) / 2)) * min (L : ℝ) (2 / ‖1 - z‖) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfirstBound (norm_nonneg _))
            hsecondNonneg
        _ ≤ _ :=
          mul_le_mul_of_nonneg_left hsecondBound
            (mul_nonneg (norm_nonneg _) (le_trans hfirstNonneg hfirstBound))
    _ = _ := by rfl

/--
Inputs: two distinct reduced unit frequencies with denominators at most `Q`, and a finite
interval length.

Claim: the geometric sum of the ratio of their complex exponential phases has norm at most
`Q^2 / 2`.

Proof: apply the unit-circle geometric-sum estimate and the `4 / Q^2` lower bound for the phase
denominator.

Role: gives a uniform off-diagonal kernel bound for the additive large sieve.
-/
theorem reducedUnitFrequency_geometricSum_norm_le {q r Q : ℕ} [NeZero q] [NeZero r] (hq : 1 < q)
    (hr : 1 < r) (hqQ : q ≤ Q) (hrQ : r ≤ Q) (x : ZMod q) (hx : IsUnit x) (y : ZMod r)
    (hy : IsUnit y) (hfrac : (x.val : ℚ) / q ≠ (y.val : ℚ) / r) (N : ℕ) :
    ‖∑ n ∈ Finset.range N,
          Complex.exp (Complex.I * ((2 * Real.pi * ((x.val : ℝ) / q - (y.val : ℝ) / r) : ℝ) : ℂ)) ^
            n‖ ≤
      ((Q : ℝ) * Q) / 2 := by
  let z : ℂ :=
    Complex.exp (Complex.I * ((2 * Real.pi * ((x.val : ℝ) / q - (y.val : ℝ) / r) : ℝ) : ℂ))
  have hQpos : 0 < (Q : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hq).trans_le hqQ
  have hphase := reducedUnitFrequency_complexPhase_distance hq hr hqQ hrQ x hx y hy hfrac
  have hden : 0 < ‖1 - z‖ := by
    have hpos : 0 < 4 / ((Q : ℝ) * Q) := div_pos (by norm_num only) (mul_pos hQpos hQpos)
    have h := lt_of_lt_of_le hpos hphase
    simpa only [z] using h
  have hz : ‖z‖ = 1 := by
    dsimp [z]
    exact Complex.norm_exp_I_mul_ofReal _
  have hzne : z ≠ 1 := by
    intro heq
    have hz0 : ‖1 - z‖ = 0 := by rw [heq, sub_self, norm_zero]
    exact (ne_of_gt hden) hz0
  have hgeom := unit_circle_geometric_sum_norm_le hz hzne N
  have hmul : 4 ≤ ((Q : ℝ) * Q) * ‖1 - z‖ := by
    calc
      4 = ((Q : ℝ) * Q) * (4 / ((Q : ℝ) * Q)) := by field_simp [ne_of_gt (mul_pos hQpos hQpos)]
      _ ≤ ((Q : ℝ) * Q) * ‖1 - z‖ := mul_le_mul_of_nonneg_left hphase (mul_nonneg hQpos.le hQpos.le)
  have hscale : 2 / ‖1 - z‖ ≤ ((Q : ℝ) * Q) / 2 := by
    apply (div_le_div_iff₀ hden (by norm_num only : (0 : ℝ) < 2)).2
    nlinarith only [hmul]
  simpa only [z] using le_trans hgeom hscale

/--
Inputs: two distinct reduced unit frequencies with denominators at most `Q`, and a finite
interval length.

Claim: the cross-correlation of their standard additive-character powers has norm at most
`Q^2 / 2`.

Proof: combine powers into the ratio of the two unit-circle phases, identify that ratio with the
exponential of the rational frequency difference, and apply the geometric-kernel bound.

Role: supplies the off-diagonal correlation estimate for the finite additive large sieve.
-/
theorem reducedUnitFrequency_stdAddChar_crossSum_norm_le {q r Q : ℕ} [NeZero q] [NeZero r]
    (hq : 1 < q) (hr : 1 < r) (hqQ : q ≤ Q) (hrQ : r ≤ Q) (x : ZMod q) (hx : IsUnit x) (y : ZMod r)
    (hy : IsUnit y) (hfrac : (x.val : ℚ) / q ≠ (y.val : ℚ) / r) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, (ZMod.stdAddChar x) ^ n * star ((ZMod.stdAddChar y) ^ n)‖ ≤
      ((Q : ℝ) * Q) / 2 := by
  have hsum :
    (∑ n ∈ Finset.range N, (ZMod.stdAddChar x) ^ n * star ((ZMod.stdAddChar y) ^ n)) =
      ∑ n ∈ Finset.range N, (ZMod.stdAddChar x * star (ZMod.stdAddChar y)) ^ n := by
    apply Finset.sum_congr rfl
    intro n hn
    have hstar : star (ZMod.stdAddChar y ^ n) = (star (ZMod.stdAddChar y)) ^ n :=
      map_pow (starRingEnd ℂ) _ _
    rw [hstar, ← mul_pow]
  rw [hsum, zmod_stdAddChar_phase_ratio]
  exact reducedUnitFrequency_geometricSum_norm_le hq hr hqQ hrQ x hx y hy hfrac N

/--
Inputs: a modulus greater than one, a finite polynomial index set, and complex coefficients.

Claim: after weighting the primitive-character mean square by `q / φ(q)`, it is bounded by the
unweighted reduced additive-frequency mean square.

Proof: divide the fixed-modulus Gauss-sum and Parseval inequality by the positive totient.

Role: matches the standard additive large sieve, whose sum over reduced frequencies has no
additional totient weight.
-/
theorem primitive_character_mean_square_scaled_additive_le {q : ℕ} [NeZero q] (hq : 1 < q)
    (S : Finset ℕ) (a : ℕ → ℂ) :
    (q : ℝ) / (Nat.totient q : ℝ) * primitiveCharacterPolynomialMeanSquare q hq S a ≤
      reducedAdditivePolynomialMeanSquare q hq S a := by
  have h := primitive_character_mean_square_additive_le hq S a
  have hφ : 0 < (Nat.totient q : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (lt_trans Nat.zero_lt_one hq)
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hφ).2
  calc
    (q : ℝ) * primitiveCharacterPolynomialMeanSquare q hq S a ≤
        (Nat.totient q : ℝ) * reducedAdditivePolynomialMeanSquare q hq S a :=
      h
    _ = reducedAdditivePolynomialMeanSquare q hq S a * Nat.totient q := by ring

/--
Inputs: a finite set of moduli greater than one, a finite polynomial index set, and complex
coefficients.

Claim: the sum of primitive-character mean squares weighted by `q / φ(q)` is bounded by the
unweighted sum of reduced additive-frequency mean squares.

Proof: apply the normalized fixed-modulus inequality at each modulus in the attached finite set.

Role: reduces the family large-sieve target to the classical additive large sieve with its
standard unweighted frequency sum.
-/
theorem primitiveCharacterFamilyMeanSquare_scaled_additive_le (Q : Finset ℕ) (hQ : ∀ q ∈ Q, 1 < q)
    (S : Finset ℕ) (a : ℕ → ℂ) :
    (∑ q ∈ Q.attach,
        (q.val : ℝ) / (Nat.totient q.val : ℝ) *
          primitiveCharacterPolynomialMeanSquare q.val (hQ q.val q.property) S a) ≤
      ∑ q ∈ Q.attach, reducedAdditivePolynomialMeanSquare q.val (hQ q.val q.property) S a := by
  classical
  apply Finset.sum_le_sum
  intro q hqQ
  have hq : 1 < q.val := hQ q.val q.property
  have hnz : NeZero q.val := ⟨Nat.ne_of_gt (lt_trans Nat.zero_lt_one hq)⟩
  simpa only [primitiveCharacterPolynomialMeanSquare, reducedAdditivePolynomialMeanSquare] using
    (@primitive_character_mean_square_scaled_additive_le q.val hnz hq S a)

/--
Inputs: a modulus greater than one, a finite polynomial index set, and complex coefficients.

Claim: the primitive-character polynomial mean square is nonnegative.

Proof: each summand is the squared norm of a complex number.

Role: permits removal of the factor `q / φ(q)`, which is at least one, from the family estimate.
-/
theorem primitiveCharacterPolynomialMeanSquare_nonneg {q : ℕ} (hq : 1 < q) (S : Finset ℕ)
    (a : ℕ → ℂ) : 0 ≤ primitiveCharacterPolynomialMeanSquare q hq S a := by
  classical
  unfold primitiveCharacterPolynomialMeanSquare
  apply Finset.sum_nonneg
  intro χ hχ
  exact Complex.normSq_nonneg _

/--
Inputs: an integer support bounded away from zero, a positive cutoff `Z`, and a proof that every
prime divisor of each supported integer exceeds `Z`.

Claim: every positive modulus at most `Z` is coprime to each supported integer.

Proof: a common divisor would contain a prime dividing both numbers; that prime is at most the
modulus and therefore at most `Z`, contradicting the support condition.

Role: turns the least-prime-factor restriction in the pre-sifted large sieve into the coprimality
condition required by the Ramanujan coefficient lemmas.
-/
theorem Nat.coprime_of_prime_factors_gt {n r Z : ℕ} (hr : 0 < r) (hrZ : r ≤ Z)
    (hprime : ∀ p, Nat.Prime p → p ∣ n → Z < p) : Nat.Coprime n r := by
  by_contra hnot
  obtain ⟨p, hp, hpn, hpr⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnot
  have hpZ : Z < p := hprime p hp hpn
  have hprle : p ≤ r := Nat.le_of_dvd hr hpr
  exact Nat.not_le_of_gt hpZ (le_trans hprle hrZ)

open PseudoPrime.AnalyticNumberTheory.Arithmetic in
/--
Inputs: `q ≤ Z`, a finite coefficient support whose prime divisors exceed `Z`, and the
primitive-character mean square modulo `q`.

Claim: summing the squarefree Ramanujan-weighted mean squares over `r ≤ Z/q` gives at least
`(log (Z/q) / 2)` times the unweighted mean square.

Proof: on the support, each squarefree Ramanujan weight is constant with squared norm one. Factor
`φ(q*r)` by coprimality and apply the squarefree reciprocal-totient lower bound.

Role: supplies the arithmetic `log (Z/q)` gain needed to pass from the pair-family estimate to a
pre-sifted large-sieve bound.
-/
theorem primitiveCharacterPolynomialMeanSquare_preSifted_weighted_lower (q Z : ℕ) (hq : 0 < q)
    (hZ : q ≤ Z) (hq1 : 1 < q) (S : Finset ℕ) (a : ℕ → ℂ)
    (hprime : ∀ n ∈ S, ∀ p, Nat.Prime p → p ∣ n → Z < p) :
    Real.log ((Z : ℝ) / (q : ℝ)) / 2 * primitiveCharacterPolynomialMeanSquare q hq1 S a ≤
      ∑
        r ∈
          ((Finset.range (Z / q + 1)).filter
              (fun r : ℕ => 0 < r ∧ Squarefree r ∧ Nat.Coprime r q)).attach,
        (q : ℝ) / (Nat.totient (q * r.val) : ℝ) *
          primitiveCharacterPolynomialMeanSquare q hq1 S
            (fun n =>
              a n *
                @ramanujanSum r.val n ⟨Nat.ne_of_gt ((Finset.mem_filter.mp r.property).2.1)⟩) := by
  classical
  let R := (Finset.range (Z / q + 1)).filter (fun r : ℕ => 0 < r ∧ Squarefree r ∧ Nat.Coprime r q)
  have hrecip := squarefree_coprime_reciprocal_totient_sum_ge_log_ratio_div_two Z q hq hZ
  have hMnonneg : 0 ≤ primitiveCharacterPolynomialMeanSquare q hq1 S a :=
    primitiveCharacterPolynomialMeanSquare_nonneg hq1 S a
  have hsumAttach :
    (∑ r ∈ R.attach, 1 / (Nat.totient r.val : ℝ)) = ∑ r ∈ R, 1 / (Nat.totient r : ℝ) :=
    Finset.sum_attach R (fun r => 1 / (Nat.totient r : ℝ))
  have hrecipAttach :
    Real.log ((Z : ℝ) / (q : ℝ)) / 2 ≤
      (q : ℝ) / (Nat.totient q : ℝ) * ∑ r ∈ R.attach, 1 / (Nat.totient r.val : ℝ) := by
    rw [hsumAttach]
    exact hrecip
  have hweighted :
    (∑ r ∈ R.attach,
        (q : ℝ) / (Nat.totient (q * r.val) : ℝ) *
          primitiveCharacterPolynomialMeanSquare q hq1 S
            (fun n =>
              a n * @ramanujanSum r.val n ⟨Nat.ne_of_gt ((Finset.mem_filter.mp r.property).2.1)⟩)) =
      ((q : ℝ) / (Nat.totient q : ℝ) * ∑ r ∈ R.attach, 1 / (Nat.totient r.val : ℝ)) *
        primitiveCharacterPolynomialMeanSquare q hq1 S a := by
    calc
      _ =
          ∑ r ∈ R.attach,
            ((q : ℝ) / (Nat.totient q : ℝ)) * (1 / (Nat.totient r.val : ℝ)) *
              primitiveCharacterPolynomialMeanSquare q hq1 S a :=
        by
        apply Finset.sum_congr rfl
        intro r hrR
        have hrprop := Finset.mem_filter.mp r.property
        have hrpos : 0 < r.val := hrprop.2.1
        have hrsq : Squarefree r.val := hrprop.2.2.1
        have hrq : Nat.Coprime r.val q := hrprop.2.2.2
        have hqr : Nat.Coprime q r.val := hrq.symm
        have hrNe : NeZero r.val := ⟨Nat.ne_of_gt hrpos⟩
        have hrZdiv : r.val ≤ Z / q := Nat.le_of_lt_succ (Finset.mem_range.mp hrprop.1)
        have hrZ : r.val ≤ Z := le_trans hrZdiv (Nat.div_le_self Z q)
        have hrMean :=
          @primitiveCharacterPolynomialMeanSquare_eq_of_squarefree_ramanujan q r.val hrNe hq1 S a
            hrpos hrsq (fun n hn => Nat.coprime_of_prime_factors_gt hrpos hrZ (hprime n hn))
        have hphiQ : 0 < Nat.totient q := Nat.totient_pos.mpr hq
        have hphiR : 0 < Nat.totient r.val := Nat.totient_pos.mpr hrpos
        rw [hrMean]
        rw [show (Nat.totient (q * r.val) : ℝ) = (Nat.totient q : ℝ) * (Nat.totient r.val : ℝ) by
            exact_mod_cast Nat.totient_mul hqr]
        field_simp [ne_of_gt (show (Nat.totient q : ℝ) > 0 by exact_mod_cast hphiQ),
          ne_of_gt (show (Nat.totient r.val : ℝ) > 0 by exact_mod_cast hphiR)]
      _ = _ := by
        calc
          (∑ r ∈ R.attach,
                ((q : ℝ) / (Nat.totient q : ℝ)) * (1 / (Nat.totient r.val : ℝ)) *
                  primitiveCharacterPolynomialMeanSquare q hq1 S a) =
              (∑ r ∈ R.attach, ((q : ℝ) / (Nat.totient q : ℝ)) * (1 / (Nat.totient r.val : ℝ))) *
                primitiveCharacterPolynomialMeanSquare q hq1 S a :=
            (Finset.sum_mul R.attach
                (fun r => ((q : ℝ) / (Nat.totient q : ℝ)) * (1 / (Nat.totient r.val : ℝ)))
                (primitiveCharacterPolynomialMeanSquare q hq1 S a)).symm
          _ = _ := by rw [Finset.mul_sum]
  calc
    _ = (Real.log ((Z : ℝ) / (q : ℝ)) / 2) * primitiveCharacterPolynomialMeanSquare q hq1 S a := by
      ring
    _ ≤
        ((q : ℝ) / (Nat.totient q : ℝ) * ∑ r ∈ R.attach, 1 / (Nat.totient r.val : ℝ)) *
          primitiveCharacterPolynomialMeanSquare q hq1 S a :=
      mul_le_mul_of_nonneg_right hrecipAttach hMnonneg
    _ = _ := hweighted.symm

/--
Inputs: a finite set of moduli greater than one, a finite polynomial index set, and complex
coefficients.

Claim: the unweighted sum of primitive-character mean squares is bounded by the unweighted sum of
reduced additive-frequency mean squares.

Proof: nonnegativity allows the pointwise factor `q / φ(q) ≥ 1`, followed by the normalized
fixed-modulus family estimate.

Role: gives the direct input required by the standard additive large-sieve inequality.
-/
theorem primitiveCharacterFamilyMeanSquare_unweighted_additive_le (Q : Finset ℕ)
    (hQ : ∀ q ∈ Q, 1 < q) (S : Finset ℕ) (a : ℕ → ℂ) :
    (∑ q ∈ Q.attach, primitiveCharacterPolynomialMeanSquare q.val (hQ q.val q.property) S a) ≤
      ∑ q ∈ Q.attach, reducedAdditivePolynomialMeanSquare q.val (hQ q.val q.property) S a := by
  calc
    _ ≤
        ∑ q ∈ Q.attach,
          (q.val : ℝ) / (Nat.totient q.val : ℝ) *
            primitiveCharacterPolynomialMeanSquare q.val (hQ q.val q.property) S a :=
      by
      apply Finset.sum_le_sum
      intro q hqQ
      have hq : 1 < q.val := hQ q.val q.property
      have hratio : (1 : ℝ) ≤ (q.val : ℝ) / (Nat.totient q.val : ℝ) := by
        have hφ : 0 < (Nat.totient q.val : ℝ) := by
          exact_mod_cast Nat.totient_pos.mpr (lt_trans Nat.zero_lt_one hq)
        rw [le_div_iff₀ hφ]
        simpa only [one_mul] using
          (show (Nat.totient q.val : ℝ) ≤ (q.val : ℝ) by exact_mod_cast (Nat.totient_le q.val))
      simpa only [one_mul] using
        (mul_le_mul_of_nonneg_right hratio (primitiveCharacterPolynomialMeanSquare_nonneg hq S a))
    _ ≤ ∑ q ∈ Q.attach, reducedAdditivePolynomialMeanSquare q.val (hQ q.val q.property) S a :=
      primitiveCharacterFamilyMeanSquare_scaled_additive_le Q hQ S a

/--
Inputs: a finite set of moduli greater than one, a finite set of polynomial indices, and complex
coefficients.

Claim: the sum of the modulus-weighted primitive-character mean squares is bounded by the sum of
the totient-weighted additive Fourier mean squares over reduced residues.

Proof: apply `primitive_character_mean_square_additive_le` separately at each modulus in the
attached finite set.

Role: makes the remaining analytic task explicit: bound the combined reduced additive sums by the
classical additive large sieve.
-/
theorem primitiveCharacterFamilyMeanSquare_additive_le (Q : Finset ℕ) (hQ : ∀ q ∈ Q, 1 < q)
    (S : Finset ℕ) (a : ℕ → ℂ) :
    (∑ q ∈ Q.attach,
        (q.val : ℝ) * primitiveCharacterPolynomialMeanSquare q.val (hQ q.val q.property) S a) ≤
      ∑ q ∈ Q.attach,
        (Nat.totient q.val : ℝ) *
          reducedAdditivePolynomialMeanSquare q.val (hQ q.val q.property) S a := by
  classical
  apply Finset.sum_le_sum
  intro q hqQ
  have hq : 1 < q.val := hQ q.val q.property
  have hnz : NeZero q.val := ⟨Nat.ne_of_gt (lt_trans Nat.zero_lt_one hq)⟩
  simpa only [primitiveCharacterPolynomialMeanSquare, reducedAdditivePolynomialMeanSquare] using
    (@primitive_character_mean_square_additive_le q.val hnz hq S a)

/--
Inputs: a finite family of moduli greater than one, a Ramanujan-sum modulus, a finite polynomial
index set, and complex coefficients.

Claim: the family sum of modulus-weighted primitive-character mean squares with coefficients
`a n * ramanujanSum r n` is bounded by the corresponding totient-weighted reduced additive
Fourier sums.

Proof: apply `primitiveCharacterFamilyMeanSquare_additive_le` to the Ramanujan-weighted
coefficient function.

Role: gives the fixed-Ramanujan-weight family estimate needed before summing the coprime modulus
pairs in Selberg's Theorem 7A.
-/
theorem primitiveCharacterRamanujanWeightedFamilyMeanSquare_additive_le (Q : Finset ℕ)
    (hQ : ∀ q ∈ Q, 1 < q) (r : ℕ) [NeZero r] (S : Finset ℕ) (a : ℕ → ℂ) :
    (∑ q ∈ Q.attach,
        (q.val : ℝ) *
          primitiveCharacterPolynomialMeanSquare q.val (hQ q.val q.property) S
            (fun n => a n * ramanujanSum r n)) ≤
      ∑ q ∈ Q.attach,
        (Nat.totient q.val : ℝ) *
          reducedAdditivePolynomialMeanSquare q.val (hQ q.val q.property) S
            (fun n => a n * ramanujanSum r n) := by
  exact primitiveCharacterFamilyMeanSquare_additive_le Q hQ S (fun n => a n * ramanujanSum r n)

/--
Inputs: a positive modulus, a finite set of natural-number indices, and complex coefficients.

Claim: the squared norms of the associated Dirichlet polynomials, summed over all characters
modulo the fixed modulus, equal the totient times the squared norms of their residue-class sums
on the unit group.

Proof: group the polynomial by residue classes, discard nonunits where every character vanishes,
and apply the fixed-modulus character Parseval identity.

Role: provides an exact mean-square formula that can be combined with estimates for the residue
class sums when building a cross-modulus large sieve bound.
-/
theorem dirichletCharacter_polynomial_mean_square {q : ℕ} [NeZero q] (S : Finset ℕ) (a : ℕ → ℂ) :
    (∑ χ : DirichletCharacter ℂ q,
        star (∑ n ∈ S, a n * χ (n : ZMod q)) * (∑ n ∈ S, a n * χ (n : ZMod q))) =
      (Nat.totient q : ℂ) *
        ∑ x ∈ (Finset.univ.filter (fun x : ZMod q => IsUnit x)),
          star (∑ n ∈ S with ((n : ℕ) : ZMod q) = x, a n) *
            (∑ n ∈ S with ((n : ℕ) : ZMod q) = x, a n) := by
  classical
  let U : Finset (ZMod q) := Finset.univ.filter (fun x => IsUnit x)
  let f : ZMod q → ℂ := fun x => ∑ n ∈ S with ((n : ℕ) : ZMod q) = x, a n
  have htrans (χ : DirichletCharacter ℂ q) :
    (∑ n ∈ S, a n * χ (n : ZMod q)) = ∑ x ∈ U, f x * χ x := by
    have hfiber :
      (∑ n ∈ S, a n * χ (n : ZMod q)) =
        ∑ x : ZMod q, ∑ n ∈ S with ((n : ℕ) : ZMod q) = x, a n * χ (n : ZMod q) := by
      simpa only [Finset.sum_filter, Finset.mem_univ, ite_true] using
        (Finset.sum_fiberwise_eq_sum_filter S Finset.univ (fun n => (n : ZMod q))
            (fun n => a n * χ (n : ZMod q))).symm
    rw [hfiber]
    have hres :
      (∑ x : ZMod q, ∑ n ∈ S with ((n : ℕ) : ZMod q) = x, a n * χ (n : ZMod q)) =
        ∑ x : ZMod q, f x * χ x := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_filter]
      unfold f
      rw [Finset.sum_filter, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro n hn
      by_cases hnx : (n : ZMod q) = x
      · rw [ite_eq_left hnx, ite_eq_left hnx, hnx]
      · rw [ite_eq_right hnx, ite_eq_right hnx, zero_mul]
    rw [hres]
    have hsub : U ⊆ Finset.univ := Finset.subset_univ _
    have hout (x : ZMod q) (hx : x ∈ Finset.univ) (hxU : x ∉ U) : f x * χ x = 0 := by
      have hnot : ¬IsUnit x := by
        intro hu
        exact hxU (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩)
      rw [MulChar.map_nonunit χ hnot]
      simp only [mul_zero]
    rw [← Finset.sum_subset hsub hout]
  have hS : ∀ x ∈ U, IsUnit x := by
    intro x hx
    exact (Finset.mem_filter.mp hx).2
  calc
    _ = ∑ χ : DirichletCharacter ℂ q, star (∑ x ∈ U, f x * χ x) * (∑ x ∈ U, f x * χ x) := by
      apply Finset.sum_congr rfl
      intro χ hχ
      rw [htrans χ]
    _ = (Nat.totient q : ℂ) * ∑ x ∈ U, star (f x) * f x := dirichletCharacter_parseval U hS f

/-
Inputs: a modulus `q ≤ Q` greater than one, and a polynomial supported on a finite set.

Claim: the reduced additive mean square for modulus `q` is bounded by the common mean square
over all reduced rational frequencies with denominator at most `Q`.

Proof: identify each unit residue modulo `q` with its reduced rational frequency, embed that
frequency in the common denominator-bounded set, and use nonnegativity of every squared norm.

Role: provides the finite-family interface needed to combine the fixed-modulus character estimate
with the cross-modulus additive large sieve.
-/
theorem reducedAdditivePolynomialMeanSquare_le_rationalSet {Q q : ℕ} [NeZero q] (hq : 1 < q)
    (hqQ : q ≤ Q) (S : Finset ℕ) (a : ℕ → ℂ) :
    reducedAdditivePolynomialMeanSquare q hq S a ≤
      rationalAdditivePolynomialMeanSquare (reducedUnitFrequencyRationalSet Q) S a := by
  rw [reducedAdditivePolynomialMeanSquare_eq_rational hq S a]
  unfold rationalAdditivePolynomialMeanSquare
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro α hα
    rcases Finset.mem_image.mp hα with ⟨x, hx, rfl⟩
    have hxunit : IsUnit x := by
      change x ∈ Finset.univ.filter (fun y : ZMod q => IsUnit y) at hx
      exact (Finset.mem_filter.mp hx).2
    have hcast : IsUnit ((x.val : ℕ) : ZMod q) := by
      rw [ZMod.natCast_zmod_val]
      exact hxunit
    have hcop : x.val.Coprime q := (ZMod.isUnit_iff_coprime x.val q).mp hcast
    let f : ReducedUnitFrequencyIndex Q :=
      ⟨⟨⟨q, by omega⟩, by simpa using hq⟩, ⟨⟨x.val, ZMod.val_lt x⟩, hcop⟩⟩
    apply Finset.mem_image.mpr
    refine ⟨f, Finset.mem_univ _, ?_⟩
    rfl
  · intro α hα hnot
    exact Complex.normSq_nonneg _

/--
Inputs: a finite family of moduli greater than one and at most `Qmax`, a finite polynomial support
inside `[0,N)`, and complex coefficients.

Claim: the sum of primitive-character polynomial mean squares over the modulus family is at most
the family cardinality times `(2N + 3 Qmax²)` times the coefficient norm-square sum.

Proof: apply the fixed-modulus character-to-additive estimate, embed every reduced frequency into
the common denominator-bounded set, then use the finite additive large-sieve bound.

Role: supplies an explicit cross-modulus mean-square estimate for later zero detection.
-/
theorem primitiveCharacterFamilyMeanSquare_le_additive_large_sieve (Q : Finset ℕ)
    (hQ : ∀ q ∈ Q, 1 < q) (Qmax : ℕ) (hQpos : 0 < Qmax) (hQmax : ∀ q ∈ Q, q ≤ Qmax) (N : ℕ)
    (S : Finset ℕ) (hSN : S ⊆ Finset.range N) (a : ℕ → ℂ) :
    (∑ q ∈ Q.attach, primitiveCharacterPolynomialMeanSquare q.val (hQ q.val q.property) S a) ≤
      (Q.card : ℝ) * (2 * (N : ℝ) + 3 * ((Qmax * Qmax : ℕ) : ℝ)) * ∑ n ∈ S, ‖a n‖ ^ 2 := by
  have hcommon := primitiveCharacterFamilyMeanSquare_unweighted_additive_le Q hQ S a
  have hstep :
    (∑ q ∈ Q.attach, reducedAdditivePolynomialMeanSquare q.val (hQ q.val q.property) S a) ≤
      (Q.card : ℝ) *
        rationalAdditivePolynomialMeanSquare (reducedUnitFrequencyRationalSet Qmax) S a := by
    calc
      _ ≤
          ∑ q ∈ Q.attach,
            rationalAdditivePolynomialMeanSquare (reducedUnitFrequencyRationalSet Qmax) S a :=
        by
        apply Finset.sum_le_sum
        intro q hq
        have hqbig : 1 < q.val := hQ q.val q.property
        exact
          @reducedAdditivePolynomialMeanSquare_le_rationalSet Qmax q.val
            ⟨Nat.ne_of_gt (lt_trans Nat.zero_lt_one hqbig)⟩ hqbig (hQmax q.val q.property) S a
      _ = _ := by simp only [Finset.sum_const, Finset.card_attach, nsmul_eq_mul]
  have hlarge := reducedUnitFrequencyRationalSet_mean_square_le_window_row_of_range hQpos N S hSN a
  calc
    _ ≤ ∑ q ∈ Q.attach, reducedAdditivePolynomialMeanSquare q.val (hQ q.val q.property) S a :=
      hcommon
    _ ≤
        (Q.card : ℝ) *
          rationalAdditivePolynomialMeanSquare (reducedUnitFrequencyRationalSet Qmax) S a :=
      hstep
    _ ≤ (Q.card : ℝ) * ((2 * (N : ℝ) + 3 * ((Qmax * Qmax : ℕ) : ℝ)) * ∑ n ∈ S, ‖a n‖ ^ 2) := by
      exact mul_le_mul_of_nonneg_left hlarge (by positivity)
    _ = _ := by ring

set_option linter.style.haveILetI false

/--
Inputs: a finite family of moduli greater than one and at most `Qmax`, a finite polynomial
support inside `[0,N)`, and complex coefficients.

Claim: the sum of primitive-character polynomial mean squares over the family is at most
`(2N + 3 Qmax²)` times the coefficient norm-square sum, with no factor for the number of moduli.

Proof: reindex each modulus' reduced additive frequencies by reduced rational fractions. Distinct
moduli give disjoint fraction sets, so their union is counted once before applying the common
additive large-sieve estimate.

Role: removes the extraneous modulus-count factor from the family mean-square bound.
-/
theorem primitiveCharacterFamilyMeanSquare_le_additive_large_sieve_without_modulus_factor
    (Q : Finset ℕ) (hQ : ∀ q ∈ Q, 1 < q) (Qmax : ℕ) (hQpos : 0 < Qmax) (hQmax : ∀ q ∈ Q, q ≤ Qmax)
    (N : ℕ) (S : Finset ℕ) (hSN : S ⊆ Finset.range N) (a : ℕ → ℂ) :
    (∑ q ∈ Q.attach, primitiveCharacterPolynomialMeanSquare q.val (hQ q.val q.property) S a) ≤
      (2 * (N : ℝ) + 3 * ((Qmax * Qmax : ℕ) : ℝ)) * ∑ n ∈ S, ‖a n‖ ^ 2 := by
  classical
  let F : { q // q ∈ Q } → Finset ℚ := fun q => by
    letI : NeZero q.val := ⟨Nat.ne_of_gt (lt_trans Nat.zero_lt_one (hQ q.val q.property))⟩
    exact (reducedUnitFrequencySet q.val).image (fun x => (x.val : ℚ) / q.val)
  have hdisj : Set.PairwiseDisjoint (Q.attach : Set { q // q ∈ Q }) F := by
    intro q hq r hr hne
    letI : NeZero q.val := ⟨Nat.ne_of_gt (lt_trans Nat.zero_lt_one (hQ q.val q.property))⟩
    letI : NeZero r.val := ⟨Nat.ne_of_gt (lt_trans Nat.zero_lt_one (hQ r.val r.property))⟩
    change
      Disjoint ((reducedUnitFrequencySet q.val).image _) ((reducedUnitFrequencySet r.val).image _)
    apply Finset.disjoint_left.mpr
    intro α hαq hαr
    rcases Finset.mem_image.mp hαq with ⟨x, hx, hαx⟩
    rcases Finset.mem_image.mp hαr with ⟨y, hy, hαy⟩
    have hxunit : IsUnit x := (Finset.mem_filter.mp hx).2
    have hyunit : IsUnit y := (Finset.mem_filter.mp hy).2
    have hxcast : IsUnit ((x.val : ℕ) : ZMod q.val) := by
      rw [ZMod.natCast_zmod_val]
      exact hxunit
    have hycast : IsUnit ((y.val : ℕ) : ZMod r.val) := by
      rw [ZMod.natCast_zmod_val]
      exact hyunit
    have hxcop : Nat.Coprime x.val q.val := (ZMod.isUnit_iff_coprime x.val q.val).mp hxcast
    have hycop : Nat.Coprime y.val r.val := (ZMod.isUnit_iff_coprime y.val r.val).mp hycast
    have hfrac : (x.val : ℚ) / q.val = (y.val : ℚ) / r.val := hαx.trans hαy.symm
    have hden :=
      (rational_reduced_fraction_unique (Nat.zero_lt_of_lt (hQ q.val q.property))
          (Nat.zero_lt_of_lt (hQ r.val r.property)) hxcop hycop hfrac).1
    exact hne (Subtype.ext hden)
  have hmean := primitiveCharacterFamilyMeanSquare_unweighted_additive_le Q hQ S a
  have hEq :
    (∑ q ∈ Q.attach, reducedAdditivePolynomialMeanSquare q.val (hQ q.val q.property) S a) =
      ∑ q ∈ Q.attach, rationalAdditivePolynomialMeanSquare (F q) S a := by
    apply Finset.sum_congr rfl
    intro q hq
    letI : NeZero q.val := ⟨Nat.ne_of_gt (lt_trans Nat.zero_lt_one (hQ q.val q.property))⟩
    exact reducedAdditivePolynomialMeanSquare_eq_rational (hQ q.val q.property) S a
  have hsubset : Q.attach.biUnion F ⊆ reducedUnitFrequencyRationalSet Qmax := by
    intro α hα
    rcases Finset.mem_biUnion.mp hα with ⟨q, hq, hα⟩
    letI : NeZero q.val := ⟨Nat.ne_of_gt (lt_trans Nat.zero_lt_one (hQ q.val q.property))⟩
    change α ∈ (reducedUnitFrequencySet q.val).image _ at hα
    rcases Finset.mem_image.mp hα with ⟨x, hx, rfl⟩
    have hxunit : IsUnit x := (Finset.mem_filter.mp hx).2
    have hxcast : IsUnit ((x.val : ℕ) : ZMod q.val) := by
      rw [ZMod.natCast_zmod_val]
      exact hxunit
    have hcop : Nat.Coprime x.val q.val := (ZMod.isUnit_iff_coprime x.val q.val).mp hxcast
    have hqmax := hQmax q.val q.property
    let f : ReducedUnitFrequencyIndex Qmax :=
      ⟨⟨⟨q.val, Nat.lt_succ_of_le hqmax⟩, by simpa using hQ q.val q.property⟩,
        ⟨⟨x.val, ZMod.val_lt x⟩, hcop⟩⟩
    apply Finset.mem_image.mpr
    refine ⟨f, Finset.mem_univ _, ?_⟩
    dsimp [reducedUnitFrequencyRational, f]
  calc
    _ ≤ ∑ q ∈ Q.attach, reducedAdditivePolynomialMeanSquare q.val (hQ q.val q.property) S a := hmean
    _ = rationalAdditivePolynomialMeanSquare (Q.attach.biUnion F) S a := by
      rw [hEq]
      unfold rationalAdditivePolynomialMeanSquare
      rw [Finset.sum_biUnion hdisj]
    _ ≤ rationalAdditivePolynomialMeanSquare (reducedUnitFrequencyRationalSet Qmax) S a := by
      unfold rationalAdditivePolynomialMeanSquare
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro α hα hnot
      exact Complex.normSq_nonneg _
    _ ≤ (2 * (N : ℝ) + 3 * ((Qmax * Qmax : ℕ) : ℝ)) * ∑ n ∈ S, ‖a n‖ ^ 2 :=
      reducedUnitFrequencyRationalSet_mean_square_le_window_row_of_range hQpos N S hSN a

set_option linter.style.haveILetI true

/--
Inputs: a positive modulus cutoff, a finite Dirichlet polynomial supported in `[0,N)`, and its
complex coefficients.

Claim: summing the polynomial mean square over primitive characters of all moduli
`1 < q ≤ Qmax` is at most `(2N + 3 Qmax²)` times the coefficient norm-square sum.

Proof: specialize the family estimate without a modulus-count factor to `Finset.Ioc 1 Qmax`.

Role: supplies the all-moduli form of the stronger cross-modulus large-sieve bound.
-/
theorem primitiveCharacterFamilyMeanSquare_le_additive_large_sieve_Ioc (Qmax : ℕ) (hQmax : 0 < Qmax)
    (N : ℕ) (S : Finset ℕ) (hSN : S ⊆ Finset.range N) (a : ℕ → ℂ) :
    (∑ q ∈ (Finset.Ioc 1 Qmax).attach,
        primitiveCharacterPolynomialMeanSquare q.val
          (show 1 < q.val from (Finset.mem_Ioc.mp q.property).1) S a) ≤
      (2 * (N : ℝ) + 3 * ((Qmax * Qmax : ℕ) : ℝ)) * ∑ n ∈ S, ‖a n‖ ^ 2 := by
  exact
    primitiveCharacterFamilyMeanSquare_le_additive_large_sieve_without_modulus_factor
      (Finset.Ioc 1 Qmax)
      (by
        intro q hq
        exact (Finset.mem_Ioc.mp hq).1)
      Qmax hQmax
      (by
        intro q hq
        exact (Finset.mem_Ioc.mp hq).2)
      N S hSN a

/--
Inputs: a real threshold, a finite modulus range, a finite polynomial support, and its
coefficients.

Claim: the number of primitive characters for which the Dirichlet polynomial has squared norm
at least the threshold, multiplied by that threshold, is bounded by the additive large-sieve
majorant.

Proof: apply the finite Markov inequality at each modulus, sum over moduli, and use the existing
cross-modulus additive large-sieve estimate.

Role: converts a mean-square estimate into a count of characters with large polynomial values,
the counting form needed by a zero-detection argument.
-/
theorem primitiveCharacterLargeValueCount_mul_le_additive_large_sieve_Ioc (Qmax : ℕ)
    (hQmax : 0 < Qmax) (N : ℕ) (S : Finset ℕ) (hSN : S ⊆ Finset.range N) (a : ℕ → ℂ)
    (threshold : ℝ) :
    (∑ q ∈ (Finset.Ioc 1 Qmax).attach,
          (((primitiveDirichletCharacterSet q.val).filter
                (fun χ => threshold ≤ Complex.normSq (∑ n ∈ S, a n * χ (n : ZMod q.val)))).card :
            ℝ)) *
        threshold ≤
      (2 * (N : ℝ) + 3 * ((Qmax * Qmax : ℕ) : ℝ)) * ∑ n ∈ S, ‖a n‖ ^ 2 := by
  let U : Finset ℕ := Finset.Ioc 1 Qmax
  have hmarkov :
    (∑ q ∈ U.attach,
          (((primitiveDirichletCharacterSet q.val).filter
                (fun χ => threshold ≤ Complex.normSq (∑ n ∈ S, a n * χ (n : ZMod q.val)))).card :
            ℝ)) *
        threshold ≤
      ∑ q ∈ U.attach,
        primitiveCharacterPolynomialMeanSquare q.val
          (show 1 < q.val from (Finset.mem_Ioc.mp q.property).1) S a := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro q hq
    let P := primitiveDirichletCharacterSet q.val
    let V := P.filter (fun χ => threshold ≤ Complex.normSq (∑ n ∈ S, a n * χ (n : ZMod q.val)))
    have hconstant : (V.card : ℝ) * threshold = ∑ _χ ∈ V, threshold := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    have hselected :
      (∑ χ ∈ V, threshold) ≤ ∑ χ ∈ V, Complex.normSq (∑ n ∈ S, a n * χ (n : ZMod q.val)) := by
      apply Finset.sum_le_sum
      intro χ hχ
      exact (Finset.mem_filter.mp hχ).2
    have hsubset :
      (∑ χ ∈ V, Complex.normSq (∑ n ∈ S, a n * χ (n : ZMod q.val))) ≤
        ∑ χ ∈ P, Complex.normSq (∑ n ∈ S, a n * χ (n : ZMod q.val)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro χ hχ hχP
      exact Complex.normSq_nonneg _
    calc
      _ = (V.card : ℝ) * threshold := by rfl
      _ = ∑ _χ ∈ V, threshold := hconstant
      _ ≤ ∑ χ ∈ V, Complex.normSq (∑ n ∈ S, a n * χ (n : ZMod q.val)) := hselected
      _ ≤ ∑ χ ∈ P, Complex.normSq (∑ n ∈ S, a n * χ (n : ZMod q.val)) := hsubset
      _ =
          primitiveCharacterPolynomialMeanSquare q.val
            (show 1 < q.val from (Finset.mem_Ioc.mp q.property).1) S a :=
        by rfl
  calc
    _ =
        (∑ q ∈ U.attach,
            (((primitiveDirichletCharacterSet q.val).filter
                  (fun χ => threshold ≤ Complex.normSq (∑ n ∈ S, a n * χ (n : ZMod q.val)))).card :
              ℝ)) *
          threshold :=
      by rw [Finset.sum_mul]
    _ ≤ _ := hmarkov
    _ ≤ _ := by
      dsimp only [U]
      exact primitiveCharacterFamilyMeanSquare_le_additive_large_sieve_Ioc Qmax hQmax N S hSN a

/--
Inputs: `Qmax ≥ 2`, a dyadic interval `[N, 2N)`, and arbitrary complex coefficients.

Claim: when `Qmax² ≤ N`, the primitive-character mean square over all moduli up to `Qmax` is
bounded by `10.5 * Qmax * N` times the coefficient norm-square sum on that interval.

Proof: specialize the finite additive large sieve to support in `[N, 2N)`, then simplify its
length and modulus factors using the two scale hypotheses.

Role: gives the interval estimate used to average the differentiated Euler-series tail.
-/
theorem primitiveCharacterFamilyMeanSquare_le_dyadic_large_sieve (Qmax N : ℕ) (hQ : 2 ≤ Qmax)
    (hN : Qmax * Qmax ≤ N) (a : ℕ → ℂ) :
    (∑ q ∈ (Finset.Ioc 1 Qmax).attach,
        primitiveCharacterPolynomialMeanSquare q.val
          (show 1 < q.val from (Finset.mem_Ioc.mp q.property).1) (Finset.Ico N (2 * N)) a) ≤
      (21 / 2 : ℝ) * (Qmax : ℝ) * (N : ℝ) * ∑ n ∈ Finset.Ico N (2 * N), ‖a n‖ ^ 2 := by
  have hsupport : Finset.Ico N (2 * N) ⊆ Finset.range (2 * N) := by
    intro n hn
    exact Finset.mem_range.mpr (Finset.mem_Ico.mp hn).2
  have hQpos : 0 < Qmax := lt_of_lt_of_le (by norm_num only) hQ
  have hbase :=
    primitiveCharacterFamilyMeanSquare_le_additive_large_sieve_Ioc Qmax hQpos (2 * N)
      (Finset.Ico N (2 * N)) hsupport a
  have hQreal : (2 : ℝ) ≤ (Qmax : ℝ) := by exact_mod_cast hQ
  have hQreal1 : (1 : ℝ) ≤ (Qmax : ℝ) := le_trans (by norm_num only) hQreal
  have hN' : (Qmax : ℝ) * (Qmax : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hwindow : 2 * ((2 * N : ℕ) : ℝ) + 3 * ((Qmax * Qmax : ℕ) : ℝ) ≤ 7 * (N : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_mul]
    calc
      _ = 4 * (N : ℝ) + 3 * ((Qmax : ℝ) * (Qmax : ℝ)) := by ring
      _ ≤ 4 * (N : ℝ) + 3 * (N : ℝ) :=
        add_le_add (le_of_eq rfl)
          (mul_le_mul_of_nonneg_left hN' (show (0 : ℝ) ≤ 3 by norm_num only))
      _ = 7 * (N : ℝ) := by ring
  have hsum : 0 ≤ ∑ n ∈ Finset.Ico N (2 * N), ‖a n‖ ^ 2 := by
    apply Finset.sum_nonneg
    intro n hn
    exact sq_nonneg ‖a n‖
  have hNnonneg : 0 ≤ (N : ℝ) := Nat.cast_nonneg _
  have hQnonneg : 0 ≤ (Qmax : ℝ) := Nat.cast_nonneg _
  have hfactor :
    2 * ((2 * N : ℕ) : ℝ) + 3 * ((Qmax * Qmax : ℕ) : ℝ) ≤ (21 / 2 : ℝ) * (Qmax : ℝ) * (N : ℝ) := by
    calc
      _ ≤ 7 * (N : ℝ) := hwindow
      _ ≤ 7 * (Qmax : ℝ) * (N : ℝ) := by
        calc
          _ = (7 * 1) * (N : ℝ) := by ring
          _ ≤ (7 * (Qmax : ℝ)) * (N : ℝ) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hQreal1 (by norm_num only))
              hNnonneg
      _ ≤ (21 / 2 : ℝ) * (Qmax : ℝ) * (N : ℝ) := by
        exact
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (by norm_num only : (7 : ℝ) ≤ 21 / 2) hQnonneg) hNnonneg
  calc
    _ ≤
        (2 * ((2 * N : ℕ) : ℝ) + 3 * ((Qmax * Qmax : ℕ) : ℝ)) *
          ∑ n ∈ Finset.Ico N (2 * N), ‖a n‖ ^ 2 :=
      hbase
    _ ≤ (21 / 2 : ℝ) * (Qmax : ℝ) * (N : ℝ) * ∑ n ∈ Finset.Ico N (2 * N), ‖a n‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hfactor hsum

/--
Inputs: the hypotheses of `primitiveCharacterFamilyMeanSquare_le_dyadic_large_sieve`, a coefficient
sequence, and a real threshold.

Claim: the number of primitive characters whose dyadic polynomial has squared norm at least the
threshold, multiplied by the threshold, is bounded by the dyadic large-sieve factor times the
coefficient norm-square sum.

Proof: specialize the existing large-value estimate to `[N, 2N)`, then compare the scale factors
using `Qmax² ≤ N`.

Role: bounds the number of characters with a large derivative-series block at any fixed height.
-/
theorem primitiveCharacterLargeValueCount_mul_le_dyadic_large_sieve (Qmax N : ℕ) (hQ : 2 ≤ Qmax)
    (hN : Qmax * Qmax ≤ N) (a : ℕ → ℂ) (threshold : ℝ) :
    (∑ q ∈ (Finset.Ioc 1 Qmax).attach,
          (((primitiveDirichletCharacterSet q.val).filter
                (fun χ =>
                  threshold ≤
                    Complex.normSq (∑ n ∈ Finset.Ico N (2 * N), a n * χ (n : ZMod q.val)))).card :
            ℝ)) *
        threshold ≤
      (21 / 2 : ℝ) * (Qmax : ℝ) * (N : ℝ) * ∑ n ∈ Finset.Ico N (2 * N), ‖a n‖ ^ 2 := by
  have hsupport : Finset.Ico N (2 * N) ⊆ Finset.range (2 * N) := by
    intro n hn
    exact Finset.mem_range.mpr (Finset.mem_Ico.mp hn).2
  have hbase :=
    primitiveCharacterLargeValueCount_mul_le_additive_large_sieve_Ioc Qmax
      (Nat.lt_of_lt_of_le (by norm_num only) hQ) (2 * N) (Finset.Ico N (2 * N)) hsupport a threshold
  have hQreal : (2 : ℝ) ≤ (Qmax : ℝ) := by exact_mod_cast hQ
  have hQreal1 : (1 : ℝ) ≤ (Qmax : ℝ) := le_trans (by norm_num only) hQreal
  have hN' : (Qmax : ℝ) * (Qmax : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hwindow : 2 * ((2 * N : ℕ) : ℝ) + 3 * ((Qmax * Qmax : ℕ) : ℝ) ≤ 7 * (N : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_mul]
    calc
      _ = 4 * (N : ℝ) + 3 * ((Qmax : ℝ) * (Qmax : ℝ)) := by ring
      _ ≤ 4 * (N : ℝ) + 3 * (N : ℝ) :=
        add_le_add (le_of_eq rfl)
          (mul_le_mul_of_nonneg_left hN' (show (0 : ℝ) ≤ 3 by norm_num only))
      _ = 7 * (N : ℝ) := by ring
  have hsum : 0 ≤ ∑ n ∈ Finset.Ico N (2 * N), ‖a n‖ ^ 2 := by
    apply Finset.sum_nonneg
    intro n hn
    exact sq_nonneg ‖a n‖
  have hNnonneg : 0 ≤ (N : ℝ) := Nat.cast_nonneg _
  have hQnonneg : 0 ≤ (Qmax : ℝ) := Nat.cast_nonneg _
  have hfactor :
    2 * ((2 * N : ℕ) : ℝ) + 3 * ((Qmax * Qmax : ℕ) : ℝ) ≤ (21 / 2 : ℝ) * (Qmax : ℝ) * (N : ℝ) := by
    calc
      _ ≤ 7 * (N : ℝ) := hwindow
      _ ≤ 7 * (Qmax : ℝ) * (N : ℝ) := by
        calc
          _ = (7 * 1) * (N : ℝ) := by ring
          _ ≤ (7 * (Qmax : ℝ)) * (N : ℝ) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hQreal1 (by norm_num only))
              hNnonneg
      _ ≤ (21 / 2 : ℝ) * (Qmax : ℝ) * (N : ℝ) := by
        exact
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (by norm_num only : (7 : ℝ) ≤ 21 / 2) hQnonneg) hNnonneg
  calc
    _ ≤
        (2 * ((2 * N : ℕ) : ℝ) + 3 * ((Qmax * Qmax : ℕ) : ℝ)) *
          ∑ n ∈ Finset.Ico N (2 * N), ‖a n‖ ^ 2 :=
      hbase
    _ ≤ (21 / 2 : ℝ) * (Qmax : ℝ) * (N : ℝ) * ∑ n ∈ Finset.Ico N (2 * N), ‖a n‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hfactor hsum

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity
