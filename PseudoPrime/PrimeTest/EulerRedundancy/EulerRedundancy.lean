/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.MillerRabin.Decomposition
public import PseudoPrime.PrimeTest.BPSW.BFWSpec
public import PseudoPrime.PrimeTest.EulerJacobi.Spec

/-! # Conditional Euler redundancy after a base-2 Strong MR pass

Prove closure under powers and signs and connect the three-modulo-four branch
to the shared evaluator and the independent paper specification.
Signed even powers are also covered for every odd modulus greater than one.
The odd-exponent one-modulo-four branches are proved in EulerModEight and EulerBaseTwo.
-/

@[expose] public section

namespace PseudoPrime.PrimeTest.EulerRedundancy

/-- A modulus three modulo four is greater than one and both n and its half are odd.
The quotient equations provide the arithmetic facts used by the MR and Jacobi bridges. -/
theorem mod_four_data {n : ℕ} (hm : n % 4 = 3) : 1 < n ∧ Odd n ∧ Odd (n / 2) := by
  have hd := Nat.div_add_mod n 4
  have h2 := Nat.odd_mod_four_iff.mpr (Or.inr hm)
  have hh := Nat.div_add_mod n 2
  rw [hm] at hd
  rw [h2] at hh
  refine ⟨?_, Nat.odd_iff.mpr h2, ⟨n / 4, ?_⟩⟩
  · nlinarith only [hd, Nat.zero_le (n / 4)]
  · nlinarith only [hd, hh]

/-- For n three modulo four, the two-adic valuation of n-1 is exactly one.
Divisibility by four would contradict the given remainder; used to reduce the MR round. -/
theorem twoAdic_eq_one {n : ℕ} (hm : n % 4 = 3) : padicValNat 2 (n - 1) = 1 := by
  obtain ⟨hn, ho, _⟩ := mod_four_data hm
  have hs := (odd_sub_canonical_decomp hn ho).1
  apply Nat.le_antisymm _ hs
  apply Nat.le_of_not_gt
  intro h
  have hd : 4 ∣ n - 1 := (padicValNat_dvd_iff 2 (n - 1)).mpr (Or.inr h)
  obtain ⟨k, hk⟩ := hd
  have he : n = 4 * k + 1 := by rw [← Nat.sub_add_cancel (Nat.le_of_lt hn), hk]
  rw [he, Nat.add_mod, Nat.mul_mod] at hm
  norm_num only [Nat.reduceMod, Nat.zero_mul, Nat.zero_add] at hm

/-- A Strong MR pass for n three modulo four gives sign one or minus one at n/2.
The canonical decomposition has one factor of two, so only the initial MR exponent occurs. -/
theorem half_sign {n : ℕ} {x : ZMod n} (hm : n % 4 = 3) (h : StrongMillerRabinPass n x) :
    x ^ (n / 2) = 1 ∨ x ^ (n / 2) = -1 := by
  obtain ⟨hn, ho, _⟩ := mod_four_data hm
  have hs := twoAdic_eq_one hm
  have hd := (odd_sub_canonical_decomp hn ho).2.2
  rw [hs, pow_one] at hd
  have hn2 := Nat.div_add_mod n 2
  rw [Nat.odd_iff.mp ho] at hn2
  have hh : Nat.divMaxPow (n - 1) 2 = n / 2 := by
    have hnsub := Nat.sub_add_cancel (Nat.le_of_lt hn)
    nlinarith only [hd, hn2, hnsub]
  rcases h with h | ⟨j, hj, h⟩
  · exact Or.inl (hh ▸ h)
  · rw [hs] at hj
    have hj0 : j = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hj)
    simp only [hj0, pow_zero, one_mul, hh] at h
    exact Or.inr h

/-- Equal integer residues have equal Jacobi symbols for the same modulus.
Transport the residue equality to integer congruence for the half-power argument. -/
theorem jacobi_cast_eq (n : ℕ) (a b : ℤ) (h : (a : ZMod n) = (b : ZMod n)) :
    jacobiSym a n = jacobiSym b n := by
  exact jacobiSym.mod_left' ((ZMod.intCast_eq_intCast_iff a b n).mp h)

/-- Raising the numerator to an odd positive exponent preserves its Jacobi symbol.
The three possible symbol values prove the identity, including a nonunit numerator. -/
theorem jacobi_odd_pow (n : ℕ) (a : ℤ) (e : ℕ) (he : Odd e) :
    jacobiSym (a ^ e) n = jacobiSym a n := by
  rw [jacobiSym.pow_left]
  rcases jacobiSym.trichotomy a n with h | h | h
  · rw [h, zero_pow (Nat.ne_of_gt he.pos)]
  · rw [h, one_pow]
  · rw [h, he.neg_one_pow]

/-- A half-power sign determines Euler-Jacobi for a modulus three modulo four.
Apply the odd-power Jacobi identity and the Jacobi symbol of minus one to each sign. -/
theorem euler_of_half_sign {n : ℕ} (a : ℤ) (hm : n % 4 = 3)
    (hs : (a : ZMod n) ^ (n / 2) = 1 ∨ (a : ZMod n) ^ (n / 2) = -1) :
    IsEulerJacobiProbablePrimeInt n a := by
  have he := (mod_four_data hm).2.2
  rcases hs with hs | hs
  · have hj :=
      jacobi_cast_eq n (a ^ (n / 2)) 1 (by simpa only [Int.cast_pow, Int.cast_one] using hs)
    rw [jacobi_odd_pow n a (n / 2) he, jacobiSym.one_left] at hj
    change (a : ZMod n) ^ (n / 2) = (jacobiSym a n : ZMod n)
    rw [hj]
    simpa only [Int.cast_one, Int.cast_neg] using hs
  · have hj :=
      jacobi_cast_eq n (a ^ (n / 2)) (-1)
        (by simpa only [Int.cast_pow, Int.cast_neg, Int.cast_one] using hs)
    rw [jacobi_odd_pow n a (n / 2) he, jacobiSym.at_neg_one (mod_four_data hm).2.1,
      ZMod.χ₄_nat_three_mod_four hm] at hj
    change (a : ZMod n) ^ (n / 2) = (jacobiSym a n : ZMod n)
    rw [hj]
    simpa only [Int.cast_one, Int.cast_neg] using hs

/-- Strong MR implies Euler-Jacobi on the three-modulo-four branch.
The mathematical MR decomposition supplies the half-power sign for the integer base. -/
theorem euler_of_strong {n : ℕ} (a : ℕ) (hm : n % 4 = 3)
    (h : IsStrongMillerRabinProbablePrime n a) : IsEulerJacobiProbablePrimeInt n a := by
  apply euler_of_half_sign a hm
  simpa only [Int.cast_natCast] using half_sign hm (isStrongMillerRabinProbablePrime_iff_pass.mp h)

/-- Euler-Jacobi acceptance is closed under all natural powers of an integer base.
The power law for Jacobi and commutation of the two exponents prove the equation. -/
theorem euler_pow {n : ℕ} {a : ℤ} (h : IsEulerJacobiProbablePrimeInt n a) (k : ℕ) :
    IsEulerJacobiProbablePrimeInt n (a ^ k) := by
  change (a : ZMod n) ^ (n / 2) = _ at h
  simp only [IsEulerJacobiProbablePrimeInt, Int.cast_pow, jacobiSym.pow_left, Int.cast_pow]
  rw [← pow_mul, Nat.mul_comm, pow_mul, h]

/-- For an odd modulus, negating an accepted Euler-Jacobi base preserves acceptance.
The character of minus one equals its n/2 power; used for signed powers of two. -/
theorem euler_neg {n : ℕ} (hn : Odd n) {a : ℤ} (h : IsEulerJacobiProbablePrimeInt n a) :
    IsEulerJacobiProbablePrimeInt n (-a) := by
  change (a : ZMod n) ^ (n / 2) = _ at h
  simp only [IsEulerJacobiProbablePrimeInt, jacobiSym.neg a hn, Int.cast_mul, Int.cast_neg]
  rw [neg_pow, h, ZMod.χ₄_eq_neg_one_pow (Nat.odd_iff.mp hn), Int.cast_pow, Int.cast_neg,
    Int.cast_one]

/-- A passed base-2 Strong MR round supplies Euler for every signed power of two
when the modulus is three modulo four. Exponent zero is included. -/
theorem euler_signed_two_power {n : ℕ} (hm : n % 4 = 3) (h : IsStrongMillerRabinProbablePrime n 2)
    {Q : ℤ} (k : ℕ) (hQ : Q = (2 : ℤ) ^ k ∨ Q = -(2 : ℤ) ^ k) :
    IsEulerJacobiProbablePrimeInt n Q := by
  have hb : IsEulerJacobiProbablePrimeInt n (2 : ℤ) := euler_of_strong 2 hm h
  rcases hQ with hQ | hQ
  · exact hQ ▸ euler_pow hb k
  · exact hQ ▸ euler_neg (mod_four_data hm).2.1 (euler_pow hb k)

/-- For n congruent to 3 modulo 4, a passed base-two Strong MR round and Q = ±2^k
imply that the executable Euler-Jacobi test returns true, including k = 0.
Transport the signed-power Euler equation through the evaluator's acceptance equivalence.
This removes the Euler flag from the shared Lucas evaluator under these hypotheses. -/
theorem euler_signed_two_power_true {n : ℕ} (hm : n % 4 = 3)
    (h : IsStrongMillerRabinProbablePrime n 2) {Q : ℤ} (k : ℕ)
    (hQ : Q = (2 : ℤ) ^ k ∨ Q = -(2 : ℤ) ^ k) : eulerJacobiWithIntBase n Q = true := by
  exact eulerJacobiWithIntBase_eq_true_iff.mpr (euler_signed_two_power hm h k hQ)

/-- For n congruent to 3 modulo 4, assume a base-two Strong MR pass and param.Q = ±2^k.
The shared strengthened Lucas evaluator equals the conjunction of its Strong Lucas and
terminal V tests. The signed-power Euler theorem makes the third flag true; this equality
supplies the conditional omission contract without changing the evaluator definition. -/
theorem strengthened_without_euler {n : ℕ} (hm : n % 4 = 3)
    (h : IsStrongMillerRabinProbablePrime n 2) (param : LucasParams) (k : ℕ)
    (hQ : param.Q = (2 : ℤ) ^ k ∨ param.Q = -(2 : ℤ) ^ k) :
    strengthenedLucasSharedEulerValid n param =
      (strongLucasWithParams n param.D param.P param.Q &&
        lucasVWithParams n param.D param.P param.Q) := by
  rw [strengthenedLucasSharedEulerValid_eq, strengthenedLucasSharedEuler_eq,
    euler_signed_two_power_true hm h k hQ, Bool.and_true]

/-- The paper's multiplied Euler condition follows without cancelling Q.
The half-index Euler equation is multiplied by Q using oddness of n. -/
theorem multiplied_euler {n : ℕ} (hn : Odd n) {Q : ℤ} (h : IsEulerJacobiProbablePrimeInt n Q) :
    (Q : ZMod n) ^ ((n + 1) / 2) = (Q : ZMod n) * (jacobiSym Q n : ZMod n) := by
  change (Q : ZMod n) ^ (n / 2) = _ at h
  rw [lucasOdd_half_succ n hn, pow_succ, h, mul_comm]

/-- For n congruent to 3 modulo 4, a base-two Strong MR pass and param.Q = ±2^k make
BFWLucasConditions equivalent to the Strong Lucas condition and V_(n+1) = 2Q.
Multiply the implied half-index Euler equation by Q and simplify the conjunction.
This proves the same conditional omission for the independent BFW specification. -/
theorem bfw_without_euler {n : ℕ} (hm : n % 4 = 3) (h : IsStrongMillerRabinProbablePrime n 2)
    (param : LucasParams) (k : ℕ) (hQ : param.Q = (2 : ℤ) ^ k ∨ param.Q = -(2 : ℤ) ^ k) :
    BFWLucasConditions n param ↔
      IsStrongLucasProbablePrime n param ∧
        lucasVZMod n param.P param.Q (n + 1) = 2 * (param.Q : ZMod n) := by
  have he := multiplied_euler (mod_four_data hm).2.1 (euler_signed_two_power hm h k hQ)
  simp only [BFWLucasConditions, he, and_true]

/-- For n congruent to 3 modulo 4, assume a base-two Strong MR pass, a nonempty classical
stopping set, and Q = ±2^k for the selected Method A* parameters.
The selected BFW conditions reduce to Jacobi(D,n) = -1, Strong Lucas, and V_(n+1) = 2Q.
Apply the Lucas-condition equivalence at the first stop, preserving its discriminant and
parameters. This connects conditional Euler omission to the full selection specification. -/
theorem selected_without_euler {n : ℕ} (hm : n % 4 = 3) (h : IsStrongMillerRabinProbablePrime n 2)
    (hc : (FirstStopNeOneSet isClassicalCandidate n).Nonempty) (k : ℕ)
    (hQ : (BFWParams n hc).Q = (2 : ℤ) ^ k ∨ (BFWParams n hc).Q = -(2 : ℤ) ^ k) :
    BFWSelectedConditions n hc ↔
      jacobiSym (selfridgeD (firstStopNeOne isClassicalCandidate n hc)) n = -1 ∧
        IsStrongLucasProbablePrime n (BFWParams n hc) ∧
        lucasVZMod n (BFWParams n hc).P (BFWParams n hc).Q (n + 1) =
          2 * ((BFWParams n hc).Q : ZMod n) := by
  rw [BFWSelectedConditions, bfw_without_euler hm h (BFWParams n hc) k hQ]

/-- For odd n greater than one, twice the quotient n/2 equals n-1.
The division remainder and subtraction equations cancel their common added one.
This identifies the exponent used by the square-base Euler bridge. -/
theorem odd_twice_half {n : ℕ} (hn : 1 < n) (ho : Odd n) : 2 * (n / 2) = n - 1 := by
  have hd := Nat.div_add_mod n 2
  rw [Nat.odd_iff.mp ho] at hd
  exact Nat.add_right_cancel (hd.trans (Nat.sub_add_cancel (Nat.le_of_lt hn)).symm)

/-- A Fermat residue squared has half-index power one for odd n greater than one.
Combining the exponents gives n-1; used to derive Euler for the base four. -/
theorem square_half_pow {n : ℕ} (hn : 1 < n) (ho : Odd n) {x : ZMod n} (hf : x ^ (n - 1) = 1) :
    (x ^ 2) ^ (n / 2) = 1 := by rw [← pow_mul, odd_twice_half hn ho, hf]

/-- For an odd modulus greater than one, a base-two Strong MR pass gives Euler for four.
The Fermat equation and the Jacobi symbol of four identify both sides with one.
This supplies the even-exponent branch without a Jacobi sign-recovery theorem. -/
theorem euler_four_of_strong {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (h : IsStrongMillerRabinProbablePrime n 2) : IsEulerJacobiProbablePrimeInt n 4 := by
  have hf := strongMillerRabinPass_pow hn ho (isStrongMillerRabinProbablePrime_iff_pass.mp h)
  simp only [IsEulerJacobiProbablePrimeInt, Int.cast_ofNat, jacobiSym.at_four ho, Int.cast_one]
  have he := square_half_pow hn ho hf
  norm_num only at he
  exact he

/-- Even powers of two pass Euler after base-two Strong MR for every odd n greater than one.
Rewrite the even exponent as a power of four and use closure under powers. -/
theorem euler_even_two_power {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (h : IsStrongMillerRabinProbablePrime n 2) (k : ℕ) (hk : Even k) :
    IsEulerJacobiProbablePrimeInt n ((2 : ℤ) ^ k) := by
  obtain ⟨j, hj⟩ := hk
  have he : (2 : ℤ) ^ k = (4 : ℤ) ^ j := by
    rw [hj, ← two_mul, pow_mul]
    norm_num only
  rw [he]
  exact euler_pow (euler_four_of_strong hn ho h) j

/-- Signed even powers of two satisfy Euler under an odd-modulus base-two MR pass.
Exponent zero is included; negation preserves the Euler equation.
The result justifies conditional omission on the one-modulo-four branch as well. -/
theorem euler_signed_even_two_power {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (h : IsStrongMillerRabinProbablePrime n 2) {Q : ℤ} (k : ℕ) (hk : Even k)
    (hQ : Q = (2 : ℤ) ^ k ∨ Q = -(2 : ℤ) ^ k) : IsEulerJacobiProbablePrimeInt n Q := by
  have he := euler_even_two_power hn ho h k hk
  rcases hQ with hQ | hQ
  · exact hQ ▸ he
  · exact hQ ▸ euler_neg ho he

/-- For a signed even power of two, the strengthened evaluator reduces to Strong and V.
Oddness, n greater than one, and a passed base-two MR round imply the missing Euler flag.
This equality connects the arithmetic proof to the executable conditional evaluator. -/
theorem strengthened_without_euler_even {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (h : IsStrongMillerRabinProbablePrime n 2) (param : LucasParams) (k : ℕ) (hk : Even k)
    (hQ : param.Q = (2 : ℤ) ^ k ∨ param.Q = -(2 : ℤ) ^ k) :
    strengthenedLucasSharedEulerValid n param =
      (strongLucasWithParams n param.D param.P param.Q &&
        lucasVWithParams n param.D param.P param.Q) := by
  have he := eulerJacobiWithIntBase_eq_true_iff.mpr (euler_signed_even_two_power hn ho h k hk hQ)
  rw [strengthenedLucasSharedEulerValid_eq, strengthenedLucasSharedEuler_eq, he, Bool.and_true]

/-- The paper conditions reduce to Strong and terminal V for signed even powers of two.
For odd n greater than one, the base-two MR pass implies the multiplied Euler equation.
This supplies an independent paper-specification consumer of the even-exponent proof. -/
theorem bfw_without_euler_even {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (h : IsStrongMillerRabinProbablePrime n 2) (param : LucasParams) (k : ℕ) (hk : Even k)
    (hQ : param.Q = (2 : ℤ) ^ k ∨ param.Q = -(2 : ℤ) ^ k) :
    BFWLucasConditions n param ↔
      IsStrongLucasProbablePrime n param ∧
        lucasVZMod n param.P param.Q (n + 1) = 2 * (param.Q : ZMod n) := by
  have he := multiplied_euler ho (euler_signed_even_two_power hn ho h k hk hQ)
  simp only [BFWLucasConditions, he, and_true]

end PseudoPrime.PrimeTest.EulerRedundancy
