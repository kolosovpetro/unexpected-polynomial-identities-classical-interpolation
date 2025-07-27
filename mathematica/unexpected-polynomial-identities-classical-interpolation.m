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
OddPowerBackwardDecomposition::usage="Validates the identity Odd power backward decomposition."
OddPowerBackwardDecompositionShifted::usage="Validates the identity Odd power backward decomposition shifted."
OddPowerBackwardDecompositionMMinus1::usage="Validates the identity Odd power backward decomposition m-1."
OddPowerBackwardDecompositionMMinus1Shifted::usage="Validates the identity Odd power backward decomposition m-1 shifted."
OddPowerForwardDecomposition::usage="Validates the identity Odd power forward decomposition."
OddPowerForwardDecompositionMMinus1::usage="Validates the identity Odd power forward decomposition m-1."
OddPowerForwardDecompositionMMinus1Shifted::usage="Validates the identity Odd power forward decomposition m-1 shifted."
OddPowerForwardDecompositionShifted::usage="Validates the identity Odd power forward decomposition shifted."
OddPowerCentralDecomposition::usage="Validates the identity Odd power central decomposition."
TableFormBackwardRecurrenceForT::usage="Prints the backward recurrence for Tm in the form of triangle."
TableFormForwardRecurrenceForT::usage="Prints the forward recurrence for Tm in the form of triangle."
TableFormCentralRecurrenceForT::usage="Prints the central recurrence for Tm in the form of triangle."
TableFormBivariateSumT::usage="Prints Tm in the form of triangle."

BinomialForm::usage="Validates the identity Binomial form."
ShiftedBinomialForm::usage="Validates the identity Shifted binomial form."
CenteredBinomialForm::usage="Validates the identity Centered binomial form."
ShiftedCenteredBinomialForm::usage="Validates the identity Shifted centered binomial form."
NegatedBinomialForm::usage="Validates the identity Negated binomial form."
ShiftedNegatedBinomialForm::usage="Validates the identity Shifted negated binomial form."
CenteredNegatedBinomialForm::usage="Validates the identity Centered negated binomial form."
ShiftedCenteredNegatedBinomialForm::usage="Validates the identity Shifted centered negated binomial form."

Begin["`Private`"]
Unprotect[Power];
Power[0|0., 0|0.] = 1;
Protect[Power];

A[n_, k_] := 0;
A[n_, k_] := (2k + 1) * Binomial[2k, k] * Sum[A[n, j] * Binomial[j, 2k + 1] * (-1)^(j - 1) / (j - k) * BernoulliB[2j - 2k], {j, 2k + 1, n}] /; 0 <= k < n;
A[n_, k_] := (2n + 1) * Binomial[2n, n] /; k == n;

PrintTriangleA[m_]:= TableForm[Table[A[n, k], {n, 0, m}, {k, 0, n}], TableAlignments -> Left];

OddPowerIdentity[n_, m_]:= Sum[Sum[A[m,r] * k^r * (n-k)^r, {k, 1, n}], {r, 0, m}];
OddPowerIdentitySimplified[n_, m_]:= Expand[Sum[Sum[A[m,r] * k^r * (n-k)^r, {k, 1, n}], {r, 0, m}]];

BivariateSumT[m_, n_, k_]:= Sum[A[m, r] * k^r (n-k)^r, {r, 0, m}];
TableFormBivariateSumT[m_, rows_]:=TableForm[Table[BivariateSumT[m, n, k], {n, 0, rows}, {k, 0, n}], TableAlignments -> Left];

ForwardRecurrenceForT[m_, n_, k_]:= Sum[(-1)^(t+1) * Binomial[m+1, t] * BivariateSumT[m, n+t, k], {t, 1, m+1}];
OddPowerForwardDecomposition[n_, m_]:= Sum[Sum[(-1)^(t+1) * Binomial[m+1, t] * BivariateSumT[m, n+t, k], {t, 1, m+1}], {k, 1, n}];
OddPowerForwardDecompositionMMinus1[n_, m_]:= Sum[Sum[(-1)^(t+1) * Binomial[m, t] * BivariateSumT[m-1, n+t, k], {t, 1, m}], {k, 1, n}];
OddPowerForwardDecompositionMMinus1Shifted[n_, m_]:= Sum[Sum[(-1)^(t+1) * Binomial[m, t] * BivariateSumT[m-1, n+t, k], {t, 1, m}], {k, 0, n-1}];
OddPowerForwardDecompositionShifted[n_, m_]:= Sum[Sum[(-1)^(t+1) * Binomial[m+1, t] * BivariateSumT[m, n+t, k], {t, 1, m+1}], {k, 0, n-1}];
TableFormForwardRecurrenceForT[m_, rows_]:= TableForm[Table[ForwardRecurrenceForT[m, n, k], {n, 0, rows}, {k, 0, n}], TableAlignments -> Left];

BackwardRecurrenceForT[m_, n_, k_]:= Sum[(-1)^(t-1) * Binomial[m+1, t] * BivariateSumT[m, n-t, k], {t, 1, m+1}];
OddPowerBackwardDecomposition[n_, m_]:= Sum[Sum[(-1)^(t+1) * Binomial[m+1, t] * BivariateSumT[m, n-t, k], {t, 1, m+1}], {k, 1, n}];
OddPowerBackwardDecompositionShifted[n_, m_]:= Sum[Sum[(-1)^(t+1) * Binomial[m+1, t] * BivariateSumT[m, n-t, k], {t, 1, m+1}], {k, 0, n-1}];
OddPowerBackwardDecompositionMMinus1[n_, m_]:= Sum[Sum[(-1)^(t-1) * Binomial[m, t] * BivariateSumT[m-1, n-t, k], {t, 1, m}], {k, 1, n}];
OddPowerBackwardDecompositionMMinus1Shifted[n_, m_]:= Sum[Sum[(-1)^(t-1) * Binomial[m, t] * BivariateSumT[m-1, n-t, k], {t, 1, m}], {k, 0, n-1}];
TableFormBackwardRecurrenceForT[m_, rows_]:= TableForm[Table[BackwardRecurrenceForT[m, n, k], {n, 0, rows}, {k, 0, n}], TableAlignments -> Left];

CentralRecurrenceForT[m_, n_, k_]:= Sum[(-1)^(t+1) * Binomial[m+1, t] * BivariateSumT[m, n+(m/2)-t, k], {t, 1, m+1}];
TableFormCentralRecurrenceForT[m_, rows_]:= TableForm[Table[CentralRecurrenceForT[m, n, k], {n, -m/2, rows}, {k, 0, n+m/2}], TableAlignments -> Left];
OddPowerCentralDecomposition[n_, m_]:= Sum[Sum[(-1)^(t+1) * Binomial[m+1, t] * BivariateSumT[m, n+(m/2)-t, k], {t, 1, m+1}], {k, 1, n+(m/2)}];

BinomialForm[m_, n_, a_] := Sum[A[m, r]* Sum[(k + a)^r * (n + a - k)^r, {k, -a+1, n + a}], {r, 0, m}];
ShiftedBinomialForm[m_, n_, a_] := Sum[A[m, r]* Sum[(k + a)^r * (n + a - k)^r, {k, -a, n + a-1}], {r, 0, m}];
CenteredBinomialForm[m_, n_, a_] := Sum[A[m, r]* Sum[(k + a/2)^r * (n + a/2 - k)^r, {k, -a/2 + 1, n + a/2}], {r, 0, m}];
ShiftedCenteredBinomialForm[m_, n_, a_] := Sum[A[m, r]* Sum[(k + a/2)^r * (n + a/2 - k)^r, {k, -a/2, n + a/2 - 1}], {r, 0, m}];
NegatedBinomialForm[m_, n_, a_] := Sum[A[m, r]* Sum[(k - a)^r * (n - a - k)^r, {k, a+1, n - a}], {r, 0, m}];
ShiftedNegatedBinomialForm[m_, n_, a_] := Sum[A[m, r]* Sum[(k - a)^r * (n - a - k)^r, {k, a, n - a - 1}], {r, 0, m}];
CenteredNegatedBinomialForm[m_, n_, a_] := Sum[A[m, r]* Sum[(k - a/2)^r * (n - a/2 - k)^r, {k, a/2, n - a/2 - 1}], {r, 0, m}];
ShiftedCenteredNegatedBinomialForm[m_, n_, a_] := Sum[A[m, r]* Sum[(k - a/2)^r * (n - a/2 - k)^r, {k, a/2+1, n - a/2}], {r, 0, m}];

End[ ]
EndPackage[ ]



