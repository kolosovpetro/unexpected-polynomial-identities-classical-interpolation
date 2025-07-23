(* ::Package:: *)

BeginPackage["SurprisingPolynomialIdentitiesClassicalInterpolation`"]

A::usage="A[n, k] returns the real coefficient A of non-negative integers n, k such that n <= k."
OddPowerIdentity::usage="Validates odd power identity."
OddPowerIdentitySimplified::usage="Validates odd power identity expanded form."
PrintTriangleA::usage="PrintTriangleA[m] prints triangle of coefficients A for given non negative integer m."
BivariateSumT::usage="Defines bivariate sum T(m,n,k)."
BackwardRecurrenceForT::usage="Validates the backward recurrence for the bivariate sum T(m,n,k)."
ForwardRecurrenceForT::usage="Validates the forward recurrence for the bivariate sum T(m,n,k)."
CentralRecurrenceForT::usage="Validates the central recurrence for the bivariate sum T(m,n,k)."
OddPowerDecomposition::usage="Validates the identity Odd power decomposition."
OddPowerDecompositionMMinus1::usage="Validates the identity Odd power decomposition m-1."
OddPowerBinomialForm::usage="Validates the identity Odd power binomial form shifted."
OddPowerBinomialFormShifted::usage="Validates the identity Odd power binomial form."
TableFormBackwardRecurrenceForT::usage="Prints the backward recurrence for Tm in the form of triangle."
TableFormForwardRecurrenceForT::usage="Prints the forward recurrence for Tm in the form of triangle."
TableFormCentralRecurrenceForT::usage="Prints the central recurrence for Tm in the form of triangle."
TableFormBivariateSumT::usage="Prints Tm in the form of triangle."

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
BackwardRecurrenceForT[m_, n_, k_]:= Sum[(-1)^(t-1) * Binomial[m+1, t] * BivariateSumT[m, n-t, k], {t, 1, m+1}];
ForwardRecurrenceForT[m_, n_, k_]:= Sum[(-1)^(t+1) * Binomial[m+1, t] * BivariateSumT[m, n+t, k], {t, 1, m+1}];
CentralRecurrenceForT[m_, n_, k_]:= Sum[(-1)^(t+1) * Binomial[m+1, t] * BivariateSumT[m, n+(m/2)-t, k], {t, 1, m+1}];
OddPowerDecomposition[n_, m_]:= Sum[Sum[(-1)^(t-1) * Binomial[m+1, t] * BivariateSumT[m, n-t, k], {t, 1, m+1}], {k, 1, n}];
OddPowerDecompositionMMinus1[n_, m_]:= Sum[Sum[(-1)^(t-1) * Binomial[m, t] * BivariateSumT[m-1, n-t, k], {t, 1, m}], {k, 1, n}];
OddPowerBinomialForm[m_, n_, a_] := Sum[A[m, r]* Sum[(k - a)^r * (n - a - k)^r, {k, a+1, n - a}], {r, 0, m}];
OddPowerBinomialFormShifted[m_, n_, a_] := Sum[A[m, r]* Sum[(k - a)^r * (n - a - k)^r, {k, a, n - a - 1}], {r, 0, m}];
TableFormBackwardRecurrenceForT[m_, rows_]:= TableForm[Table[BackwardRecurrenceForT[m, n, k], {n, 0, rows}, {k, 0, n}], TableAlignments -> Left];
TableFormForwardRecurrenceForT[m_, rows_]:= TableForm[Table[ForwardRecurrenceForT[m, n, k], {n, 0, rows}, {k, 0, n}], TableAlignments -> Left];
TableFormCentralRecurrenceForT[m_, rows_]:= TableForm[Table[CentralRecurrenceForT[m, n, k], {n, -m/2, rows}, {k, 0, n+m/2}], TableAlignments -> Left];
TableFormBivariateSumT[m_, rows_]:=TableForm[Table[BivariateSumT[m, n, k], {n, 0, rows}, {k, 0, n}], TableAlignments -> Left];

End[ ]
EndPackage[ ]



