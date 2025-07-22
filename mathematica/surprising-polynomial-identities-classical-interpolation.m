(* ::Package:: *)

BeginPackage["SurprisingPolynomialIdentitiesClassicalInterpolation`"]

A::usage="A[n, k] returns the real coefficient A of non-negative integers n, k such that n <= k."
OddPowerIdentity::usage="Validates odd power identity."
OddPowerIdentitySimplified::usage="Validates odd power identity expanded form."
PrintTriangleA::usage="PrintTriangleA[m] prints triangle of coefficients A for given non negative integer m."
BivariateSumT::usage="Defines bivariate sum T(m,n,k)."
RecurrenceForT::usage="Validates the recurrence for the bivariate sum T(m,n,k)."
OddPowerDecomposition::usage="Validates the identity Odd power decomposition."
OddPowerBinomialForm::usage="Validates the identity Odd power binomial form."

Begin["`Private`"]
Unprotect[Power];
Power[0|0., 0|0.] = 1;
Protect[Power];

A[n_, k_] := 0;
A[n_, k_] := (2k + 1) * Binomial[2k, k] * Sum[A[n, j] * Binomial[j, 2k + 1] * (-1)^(j - 1) / (j - k) * BernoulliB[2j - 2k], {j, 2k + 1, n}] /; 0 <= k < n;
A[n_, k_] := (2n + 1) * Binomial[2n, n] /; k == n;

OddPowerIdentity[n_, m_]:= Sum[Sum[A[m,r] * k^r * (n-k)^r, {k, 1, n}], {r, 0, m}];
OddPowerIdentitySimplified[n_, m_]:= Expand[Sum[Sum[A[m,r] * k^r * (n-k)^r, {k, 1, n}], {r, 0, m}]];
PrintTriangleA[m_]:= TableForm[Table[A[n, k], {n, 0, m}, {k, 0, n}], TableAlignments -> Left];
BivariateSumT[m_, n_, k_]:= Sum[A[m, r] * k^r (n-k)^r, {r, 0, m}];
RecurrenceForT[m_, n_, k_]:= Sum[(-1)^(t-1) * Binomial[m+1, t] * BivariateSumT[m, n-t, k], {t, 1, m+1}];
OddPowerDecomposition[n_, m_]:= Sum[Sum[(-1)^(t-1) * Binomial[m+1, t] * BivariateSumT[m, n-t, k], {t, 1, m+1}], {k, 1, n}];
OddPowerBinomialForm[m_, n_, a_] := Sum[A[m, r]* Sum[(k - a)^r * (n - a - k)^r, {k, a+1, n - a}], {r, 0, m}];

End[ ]

EndPackage[ ]



