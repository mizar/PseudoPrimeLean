# Comparator challenges

Run the four-ninths criterion challenge from the project root with Lean 4.35's
built-in comparator on Linux with `bwrap` available:

```sh
lake comparator --config=ComparatorChallenges/PrimeMillerRabinFourNinthsCriterion.json
```

The challenge states the GRH-conditional criterion independently of the library proof. The
solution repeats the challenge declarations under the same names and applies the proof from
`PrimeTestBounds/MillerRabin/FourNinthsCriterion.lean`. Comparator checks the two modules in
separate environments; do not import the challenge into the solution. The challenge theorem's
`sorry` is a placeholder and is not part of the solution's proof.

The allowed axioms are `propext`, `Quot.sound`, and `Classical.choice`. GRH is an explicit
assumption in the statement, not an allowed axiom. The configuration contains no definition
holes: the definitions used in the statement are part of the fixed challenge.

The stronger base-nine logarithm criterion has a separate challenge and solution:

```sh
lake comparator --config=ComparatorChallenges/PrimeMillerRabinLogNineCriterion.json
```

Its solution uses the base-nine rejecting-prime bound and the four-ninths prime acceptance
result. The [base-nine slides](PrimeMillerRabinLogNineCriterion.md) display the theorem and GRH.

The two GRH-conditional odd-prime quadratic witness bounds use the same arrangement. Run both
comparisons together with:

```sh
lake comparator --config=ComparatorChallenges/PrimeQuadraticWitnessCriterion.json
```

The solution applies `exists_prime_ne_one_witness_of_grh` in `PseudoSquare/Bounds/PointwiseWitness.lean`
and `exists_negOneWitness_le_refined_elementary` in `PseudoSquare/Bounds/RefinedElementaryBounds.lean`.
The first bound concerns a Jacobi symbol different from one for positive odd nonsquares; the second
concerns a symbol equal to negative one for odd nonsquares at least three. Both use the same explicit
GRH assumption and permitted axioms as the Miller–Rabin challenge.
The [quadratic witness slides](PrimeQuadraticWitnessCriterion.md) show the statements and the
GRH definition used by the solution.

The extended LLS S1 subgroup bound and S2 nonprincipal-character bound are compared with:

```sh
lake comparator --config=ComparatorChallenges/LLSWitnessCriterion.json
```

The S1 statement fixes the original correction term and starts at modulus three. The S2 statement
starts at modulus five, allows character value zero, and does not require the witness to be coprime
to the modulus. The [LLS slides](LLSWitnessCriterion.md) display both statements and GRH.
