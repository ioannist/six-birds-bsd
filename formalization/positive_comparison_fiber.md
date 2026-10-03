# The exact information lost by the scalar comparison

This construction reviews source dependence inside the auxiliary rational
comparison layer. The paper's target remains the conditional BSD-to-Six-Birds
translation with supplied arithmetic premises. No premise is independently
proved as an elliptic-curve theorem here, and no paper statement is changed.

Use the existing `CoupledFactors.FactorData` carrier, with native coefficient
a, native local factor b, and prescribed coefficient s=Sha/torsionSquared
and Tamagawa product T. The retained native fixity premise is

    L = a R Omega b.

The scalar target is

    L = s R Omega T.

When R Omega is nonzero, the existing `scalarIffCombined` theorem equates
scalar BSD with a b = s T. The new construction classifies the entire
positive solution set and constructs its exact loss witness and repair.

## Classify every positive comparison fiber

Assume all eight rational fields of the native factor record are positive.
Under native fixity, `positiveComparisonFiber` proves

    scalar BSD iff there exists u > 0 with a = u s and b = T/u.

The forward construction sets u=a/s. Positivity makes s and a nonzero, and
the combined comparison gives b=T/u. Conversely, substitution returns
a b=s T, hence scalar BSD. `comparisonFiberParameterUnique` proves that the
retained a and s determine u uniquely. This does not force u=1: selecting
that normalization is additional information beyond the joint product.

The explicit family `positiveGauge u` fixes

    L = R = Omega = Sha = torsionSquared = T = 1,
    a = u, b = 1/u, for every positive rational u.

`positiveGaugeReturns` proves positivity, native fixity and scalar BSD for
every member. `positiveGaugePackageIffOne` proves that the full pair of
exact comparison statements b=T and a=s holds precisely when u=1.
Thus the earlier single compensating-factor example belongs to a fully
classified family, rather than standing alone as a numerical diagnostic.

## A genuine loss theorem on a declared lens

The declared lens retains L, R, Omega, Sha, torsionSquared, T and the joint
native product a b. It erases the two individual native factors a and b.
`positiveGaugeLensConstant` proves that every member of the positive family
has exactly the same seven retained values, all one.

`noFullPackageFromScalarLens` excludes every predicate on this lens that
would recover the conjunction of the two exact comparisons throughout the
family. The proof uses u=1 and u=2: their observations agree, but only the
first has the full comparison package. This is mathematical non-descent on
the declared rational carrier, not failure of a particular proposed reader.

The lens intentionally loses information. It is not the full normalized
GZ record, and the family is not asserted to consist of elliptic curves
with every remaining named arithmetic source frozen. It therefore proves
neither arithmetic ablation realizability nor necessity of the original
sources for the scalar conclusion.

## Retaining one comparison repairs this loss

Under native fixity and scalar BSD, assume R Omega, T and s are nonzero.
Then a b=s T gives

    b=T iff a=s.

`comparisonsEquivalentUnderScalar` proves this by lawful cancellation.
`fullPackageIffLocalUnderScalar` and
`fullPackageIffCoefficientUnderScalar` prove that either individual exact
comparison then recovers the full comparison package. No comparison
certificate is added to a record to assume this repair.

This does not contradict the earlier three-premise universal assembly
independence theorem. There, scalar BSD must be inferred from native
fixity and the two comparisons. Here scalar BSD is an additional retained
premise, so the two comparison directions cease to be independent. A larger
target alone does not automatically establish that both sources are needed.
It must have a precise observation interface and a surviving separation.

## Distinct self-review and scope

Zero-factor controls reject unrestricted cancellation: with T=0 the local
comparison may hold while the coefficient comparison fails; with s=0 the
reverse failure occurs. These controls lie outside the positive domain,
and prevent dropping the stated nonzero hypotheses.

Self-review checks the forward and reverse classification, the explicit
parameter construction, the retained observation tuple, the unchanged scalar
readout, both directions of the comparison repair, and the extra scalar
premise that distinguishes repair from universal assembly independence.
All statements are mechanized rational algebra. The native arithmetic
interpretations and source comparisons remain explicit conditional content
or separately documented research tasks. The accepted closure premise and
the main conditional landing are preserved.

Fresh `make verify-lean` and `make validate test public-audit` runs pass:
96 Lean build jobs, all 51 live manifest declarations, the unchanged
five-axiom manifest trust base, and all 26 unit tests. All ten new printed
declarations use only standard Lean axioms. The 29 theorem-alignment statuses
and actions and 40 supplementary assessments retain their previous values;
their Lean context hashes are refreshed. These checks cover the represented
conditional rational statements, not their arithmetic realization.
