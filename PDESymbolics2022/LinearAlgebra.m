(* Wolfram Language Package *)
(*BeginPackage["PDESymbolics2020`LinearAlgebra`"]*)
GenericLinearCombinationOperator::usage = 
"GenericLinearCombinationOperator[variables][list] operator form of GenericLinearCombination";

GaussianEliminationOperator::usage = 
"GaussianEliminationOperator[field][system] performs Gaussian elimination on the system with the given field.";

MatrixInverseOperator::usage = 
"MatrixInverseOperator[variables][matrix] Inverts matrix when possible";

LinearSystemSolveOperator::usage = 
"LinearSystemSolveOperator[variables] solves a linear system with respect to variables";

SolveUndeterminedCoefficientsOperator::usage = 
"SolveUndeterminedCoefficientsOperator[variables] Operator form of SolveUndeterminedCoefficients";

UndeterminedCoefficientsOperator::usage = 
"UndeterminedCoefficientsOperator[variables] extracts undertermined coefficients matrix and vector";

ImprovedHomogeneousSolveAlwaysOperator::usage = 
"ImprovedHomogeneousSolveAlwaysOperator[variables] Version of SolveAlways that attemps to split products, get rid of denominators and powers";

EqualToZeroOperator::usage = 
"EqualToZeroOperator[variables][expression] when applied to an expression, finds values of parameters for which the expression vanishes identically";

SolveAlwaysOperator::usage = 
"SolveAlwaysOperator[variables][] Like the built-in SolveAlways function, SolveAlwaysOperator when applied to an expression, finds values of parameters for which the expression vanishes identically";

MonomialDependenceOperator::usage = 
"MonomialDependenceOperator[variables][] operator form of monomial dependent that handles generic functions";

UndeterminedCoefficientsMatrixOperator::usage = 
"UndeterminedCoefficientsMatrixOperator[variables][expression] extracts undetermined coefficients matrix";

UndeterminedCoefficientsEquationOperator::usage = 
"UndeterminedCoefficientsEquationOperator[variables][expression] extracts undertermined coefficients matrix and vector";

CoeffsinExpression::usage = 
"";

Coeffs::usage = 
"";

DependentCoefficients::usage = 
"DependentCoefficients[expression, coefficients, parameters] For a given expression finds the coefficients that are linearly dependent from others";

UndeterminedCoefficientsMatrix::usage = 
"UCM[expression(s), coefficients, parameters] gives the factors-coefficients matrix of expression";

UCM::usage = 
"UCM[expression(s), coefficients, parameters], short name of UndeterminedCoefficientsMatrix";

UndeterminedCoefficientsFactors::usage = 
"gives the factors in the undetermined coefficients methods";

UndeterminedCoefficientsEquation::usage = 
"UCE[expression(s), coefficients, parameters], gives the matrix-vector coefficients of an expression";

UCE::usage = 
"UCE[expression(s), coefficients, parameters], short name of UndeterminedCoefficientsEquation";

ExtractCoefficient::usage = 
"ExtractCoefficient[monomial, parameters] Extracts the coefficient form a given monomial";

RecursiveRowBranchingGaussianElimination::usage = 
"RecursiveRowBranchingGaussianElimination[matrix, vector, generators, parameters] returns...
RecursiveRowBranchingGaussianElimination[matrix, vector, generators, parameters, conditions] returns...
RecursiveRowBranchingGaussianElimination[matrix, vector, generators, parameters, conditions, row, column] returns ...";

BranchingGaussianElimination::usage = 
"";

SolvableVariables::usage = 
"takes a matrix and a list of variables and gives the list of variables that can be solved";

UpperTriangularCleanUp::usage = 
"adssda";

Pivots::usage = 
"gives the pivots of a matrix (assumes the matrix has been gaussian eliminated";

IdM::usage = 
"gives the identity matrix of the size of its argument";

ZdM::usage = 
"gives the zero vector of the size of its argument";

BasisOperator::usage = 
"BasisOpereator[list] computes a basis, given a list of expressions";

MatrixKernelOperator::usage =
"MatrixKernelOperator[variables][matrix] returns the kernel of \
matrix of expressions of the variables.";

Numerizer::usage = 
"Numerizer[monomial, parameters] extracts the coefficient from monomial and returns factor-coefficient list";

ParametricRefineOperator::usage = 
"ParametricRefineOperator[variables][expression] Refines an expression depending on different values of the parameters";(*has unit tests*)

RegroupParametersOperator::usage = 
"RegroupParametersOperator[variables][] Groups an expression, tries to write expressions with parameters as coefficients."; 

removemultiples::usage = 
"internal function, here for debugging purposes.
removemultiples[??] returns..."

logicalcleaner::usage =  
"internal function, here for debugging purposes.
logicalcleaner[list] returns ";
Begin["`Private`"]
(* ######## mini-Function: Numerizer ########## *)
(**********************************************************************)
(* Usage: Numerizer[monomial, parameters] *)
(* Purpose: Separate coefficient from factor in monomial*)
(* Input: single term expression, i.e. Head!= Plus*)
(*list of parameters*)
(* Output:{factor, coefficient} list*)
(**********************************************************************)
Numerizer[monomial_, parameters_List] :=
    With[ {coefficient = ExtractCoefficient[Factor[monomial], parameters]},
        {Simplify[monomial/coefficient],coefficient}
    ]

(**** ****)
(* parametric refining expressions *)
(*TODO include functions such as KroneckerDelta in the generators in the variables
    Complement[xp//Variables, Lookup[variables, "pars",{}] still leaves the dependent variables in the list, but these are genFuns...
    *)
ParametricRefine[variables_Association][xp_] := 
With[ {xpp = RegroupParametersOperator[variables][xp]},
    	PiecewiseSimplifyOperator[variables][
        PiecewiseMap[xpp /. # &, 
        MonomialDependenceOperator[variables][
        If[ Head[xpp] === Plus,
            List @@ xpp,
            	{xpp}
        ]]]]
]
        
ParametricRefineOperator = KleisliListable[ParametricRefine]    

(* regroup parameters tries to write expressions with parameters as \
coefficients in a nicer way for example
1+a x +a^2 x becomes 1+(a +a^2) x *)
RegroupParameters[variables_Association][rawxp_] := 
 With[{xp = Expand@rawxp(*expanding a Plus may NOT lead to a Plus*)}, 
  If[Head[xp] === Plus, 
   Module[{monomiallist, numerizedmonomiallist, individualmonomials, 
     grouped}, 
    monomiallist = 
     Flatten[
      If[Head[#] === Plus, List @@ #, #] & /@ 
       Expand /@ 
        Factor /@ Select[List @@ xp, # =!= 0 && # =!= 0. &]];
    numerizedmonomiallist = 
     Numerizer[#, Lookup[variables, "pars", {}]] & /@ monomiallist;
    individualmonomials = 
     removemultiples@
      DeleteDuplicates[Simplify[numerizedmonomiallist[[All, 1]]]];
    grouped = 
     Function[
       mon, {mon, 
        Select[numerizedmonomiallist, 
         NumberQ[Simplify[First[#]/mon]] &]}] /@ individualmonomials;
    Total[#[[
         1]] ((Simplify /@ (#[[2, All, 1]]/#[[1]])) . #[[2, All, 
           2]]) & /@ grouped]],
   xp]]
   
RegroupParametersOperator = KleisliListable[RegroupParameters]

removemultiples[indmon_] :=
    removemultiples[{}, indmon];
removemultiples[processedmon_, {}] :=
    processedmon;
removemultiples[processedmon_, indmon_] :=
    With[ {fst = First[indmon]},
        If[ fst===0||fst===0.,
            removemultiples[Append[processedmon, fst], Rest[indmon]],
            If[ Or @@ (NumberQ /@ (processedmon/fst // Simplify)),
                removemultiples[processedmon, Rest[indmon]],
                removemultiples[Append[processedmon, fst], Rest[indmon]]
            ]
        ]
    ];

(* BASIS OPERATOR *)
Basis[variables_Association][MonList_] := 
Module[ {sortedList = Lookup[variables, "sortoperator", Sort][MonList], 
		coeffList, localvariables = variables, matrix, reducedmatrix, faux},
        coeffList = Table[Subscript[\[FormalA], i], {i, Length@sortedList}];
        AssociateTo[localvariables, {
        "pars" -> Lookup[localvariables, "pars", {}], 
        "coefficients" -> coeffList, 
        "refine" -> True, 
        "facts" -> Lookup[localvariables, "facts", True], 
        "generators" -> {}}];
        matrix = UndeterminedCoefficientsOperator[localvariables][coeffList.sortedList];
        reducedmatrix = GaussianEliminationOperator[localvariables][matrix];
        faux = (If[ # =!= $Failed,
                    sortedList[[#]],
                    $Failed
                ]) &;
        PiecewiseMap[faux,PiecewiseMap[Pivots[#["matrix"]] &, reducedmatrix] // PiecewiseExpand] // PiecewiseExpand // PiecewiseBeautify
    ]

BasisOperator = Kleisli[Basis]

(* ######## mini-Function: ExtractCoefficient########## *)
(**********************************************************************)
(* Usage: ExtractCoefficient[monomial, parameters]*)
(* Purpose: Extract the terms from a given monomial that either *)
(*dependent on parameters or constant *)
(* Input: single term expression, i.e. Head!= Plus*)
(*list of parameters*)
(* Output:extracted coefficient *)
(**********************************************************************)
ExtractCoefficient[monomial_, parameters_List] :=
    Which[
    Head@Expand[monomial]===Plus,
    Print@StringForm["ExtractCoefficient:ArgumentError:: check the first argument '``', it should be a monomial.", monomial],
    Head[monomial]===Times,Times@@Select[List@@monomial,NumericQ[#/.Thread[parameters->RandomReal[1,Length@parameters]]]&],
    NumericQ[monomial/.Thread[parameters->RandomReal[1,Length@parameters]]]&&monomial=!=0,
    monomial,
    True,
    1
    ]

(* ###### Function: UndeterminedCoefficientsMatrix ######## *)
(**********************************************************************)
(* Usage: UCM[expression(s), coefficients, parameters]*)
(* Purpose: Takes an expression and computes the factor-coefficient *)
(*matrix, so that the entries of the matrix either constants*)
(*or depending only on parameters *)
(* Input: single term expression(s), i.e. Head!= Plus *)
(*list of coefficients*)
(*list of parameters*)
(* Output:factor-coefficient matrix if Factor->False*)
(*{factors, matrix} list if Factor->True (Default)*)
(**********************************************************************)
Options[UndeterminedCoefficientsMatrix] = {Factors->True, SelfTest->False}; 

UCM = UndeterminedCoefficientsMatrix;

UndeterminedCoefficientsMatrix[expr_Piecewise,coeffs_, pars_, OptionsPattern[]] :=
    PiecewiseMap[UndeterminedCoefficientsMatrix[#,coeffs, pars, Factors->OptionValue[Factors]]&, expr]

UndeterminedCoefficientsMatrix[expList_List, coeffs_List, pars_List, OptionsPattern[]] :=
    If[ OptionValue[SelfTest],
        And@@(UndeterminedCoefficientsMatrix[#, coeffs, pars, SelfTest->True]&/@ expList),
        If[ OptionValue@Factors==False,
            Join@@(UndeterminedCoefficientsMatrix[#, coeffs, pars, Factors->False]& /@ expList),
            With[ {uuu = UndeterminedCoefficientsMatrix[#, coeffs, pars, Factors->True]& /@ expList},
                Join@@@Transpose[uuu]
            ]
        ]
    ]

UndeterminedCoefficientsMatrix[expr_, coeffs_List, pars_List:{}, OptionsPattern[]] :=
    Module[ { print, factors,showFactors, matrix,coeffsList,separatedCoeffsList,factorsToCoeffsMapping,factorsToCoeffsAssociation},
        print = DebugPrint[False, "[ucm]"];
        (*for a given expression 'expr' extracts the coefficients matrix based on given coefficients 'coeffs' and factors that appears in expr. So the columns of the resulting matrix corresponds to the given 'coeffs', while the rows corresponds to the factors from 'expr'*)
        showFactors = OptionValue[Factors];
         
        (*extract coefficients of the coefficients 'coeffs' in the expression*)
         (* coeffsList = ParallelMap[Coefficient[Expand@expr,#]&, coeffs,DistributedContexts->Automatic];*)
        coeffsList = Map[Coefficient[Expand@expr,#]&, coeffs];
        print["coeffsList = ", coeffsList];
        (*If the expression does not contain any coeffs then returns row of 0s and 1 as only factor. Without the code below UCM outputs both empty lists.[!]*)
        If[ AllTrue[coeffsList, PossibleZeroQ],
            Return[If[ showFactors,
                       {{1}, {coeffsList}},
                       {coeffsList}
                   ]]
        ];

        (*for each coefficient, transform a sum into a list, if no sum just turns into a list of a single element*)
        separatedCoeffsList = Map[If[ Head[#]===Plus,
                                      List@@#,
                                      {#}
                                  ]&, coeffsList];
        print["separatedCoeffsList = ", separatedCoeffsList];

        (*make a mapping from factors to their corresponding coefficient, by combining coefficients with the same factors*)
        factorsToCoeffsMapping = Map[#[[1,1]]->Total@#[[All,2]]&, Map[SplitBy[#, #[[1]]&]&,Map[Numerizer[#,pars]&, separatedCoeffsList, {2}(*, DistributedContexts->Automatic*)]],{2}];
        print["factorsToCoeffsMapping = ", factorsToCoeffsMapping];

        (*transform a map into association*)
        factorsToCoeffsAssociation = Select[Association/@factorsToCoeffsMapping,!Keys[#]===0&];
        factors = Select[Union@Map[Keys,Flatten@factorsToCoeffsMapping], !(#===0)&];
        matrix = Map[#/@factors&, factorsToCoeffsAssociation]/.Missing[___]->0;
        print["factorsToCoeffsAssociation = ", factorsToCoeffsAssociation];
        print["factors = ", factors];
        If[ matrix!={},
            matrix = Transpose@matrix
        ];
        If[ OptionValue[SelfTest],
            FullSimplify[factors.matrix.coeffs-expr==0],
            If[ showFactors,
                {factors, matrix},
                matrix
            ]
        ]
    ]

Coeffs[list_, coeffsSymbol_] :=
    Table[Subscript[coeffsSymbol, i], {i, 1 , Length[list]}]

CoeffsinExpression[expr_, coefficients_] :=
    Select[coefficients, !(Cases[expr, #, {0, Infinity}]==={})&]

(* operator form *)

UndeterminedCoefficientsMatrixOperator[variables_Association][expression_] :=
    With[ {ucm = UndeterminedCoefficientsMatrix[expression, variables["coefficients"], Lookup[variables,"pars",{}]]},
        If[ Head[ucm]===Piecewise,
            PiecewiseMap[Association[{"matrix"->#[[2]], "factors"->#[[1]]}]&,ucm],
            Association[{"matrix"->ucm[[2]],"factors"->ucm[[1]]}]
        ]
    ] 

UndeterminedCoefficientsFactors[expr_, coeffs_List, pars_List:{} ] :=
    Module[ {print, factors,coeffsList,separatedCoeffsList,factorsToCoeffsMapping,factorsToCoeffsAssociation,expr0, expr1},
        expr0 = expr/.Thread[coeffs->0];
        expr1 = expr+(\[FormalZ]-1)expr0;

        (*extract coefficients of the coefficients 'coeffs' in the expression*)
        coeffsList = Map[Coefficient[Expand@expr1,#]&,Append[coeffs,\[FormalZ]](*, DistributedContexts->Automatic*)];
        print["coeffsList = ", coeffsList];
        (*If the expression does not contain any coeffs then returns row of 0s and 1 as only factor. Without the code below outputs empty lists.[!]*)
        If[ AllTrue[coeffsList, PossibleZeroQ],
            Return[
             {{1}, {coeffsList}}]
        ];

        (*for each coefficient, transform a sum into a list, if no sum just turns into a list of a single element*)
        separatedCoeffsList = Map[If[ Head[#]===Plus,
                                      List@@#,
                                      {#}
                                  ]&, coeffsList];
        print["separatedCoeffsList = ", separatedCoeffsList];

        (*make a mapping from factors to their corresponding coefficient, by combining coefficients with the same factors*)
        factorsToCoeffsMapping = Map[#[[1,1]]->Total@#[[All,2]]&, Map[SplitBy[#, #[[1]]&]&,Map[Numerizer[#,pars]&, separatedCoeffsList, {2}(*, DistributedContexts->Automatic*)]],{2}];
        print["factorsToCoeffsMapping = ", factorsToCoeffsMapping];

        (*transform a map into association*)
        factorsToCoeffsAssociation = Select[Association/@factorsToCoeffsMapping,!Keys[#]===0&];
        factors = Select[Union@Map[Keys,Flatten@factorsToCoeffsMapping], !(#===0)&]
    ]

SolveUndeterminedCoefficients[variables_Association][xp_] := 
	Module[{xp0 = If[Head[xp] === List, xp, {xp}], uceinfo},
		uceinfo = UndeterminedCoefficientsOperator[variables][xp0];
        LinearSystemSolveOperator[Append[variables, "sign" -> -1]][
        PiecewiseMap[Append[#, "unknowns" -> variables["coefficients"]] &, uceinfo]]
    ]


SolveUndeterminedCoefficients[variables_Association][xp_Association] :=
    SolveUndeterminedCoefficients[
    Append[variables, "coefficients"->Lookup[xp, "coefficients",{}]]][xp["expression"]]

SolveUndeterminedCoefficientsOperator = Kleisli[SolveUndeterminedCoefficients]

(* ######Function: UndeterminedCoefficientsEquation ######## *)
(*************************************************************************)
Options[UndeterminedCoefficientsEquation] = {Factors->True};

(* if factors = true returns factors, matrix, vector; otherwise returns matrix, vector *)

UndeterminedCoefficientsEquation[$Failed,coeffs_, pars_, OptionsPattern[]] :=
    $Failed

UndeterminedCoefficientsEquation[expr_Piecewise,coeffs_, pars_, OptionsPattern[]] :=
    PiecewiseMap[UndeterminedCoefficientsEquation[#,coeffs, pars, Factors->OptionValue[Factors]]&, expr]

UndeterminedCoefficientsEquation[expr_, coeffs_, pars_, OptionsPattern[]] :=
    Module[ {print, expr0, undet,fact},
        print = DebugPrint[False, "[uce]"];
        fact = OptionValue[Factors];
        expr0 = expr/.Thread[coeffs->0];
        print["expr0 = ", expr0];
        print[expr+(\[FormalZ]-1) expr0//Expand];
        undet = UndeterminedCoefficientsMatrix[expr+(\[FormalZ]-1)expr0, Append[coeffs,\[FormalZ]], pars, Factors->True];
        print[undet];
        (* get the output *)
        print[undet[[2]][[;;,;;-2]]];
        print[undet[[2]][[;;,-1]]];
        print[fact];
        If[ fact,
            {undet[[1]], undet[[2]][[;;,;;-2]], undet[[2]][[;;,-1]]},
            { undet[[2]][[;;,;;-2]], undet[[2]][[;;,-1]]}
        ]
    ]

UCE = UndeterminedCoefficientsEquation;

(* ######mini-Function: DependentCoefficients ######## *)
(***********************************************************************)
(* Usage: DependentCoefficients[expression, coefficients, parameters]*)
(* Purpose: For a given expression finds the coefficients that are *)
(*linearly dependent from others *)
(* Input: single term expression, i.e. Head!= Plus *)
(*list of coefficients *)
(*list of parameters *)
(* Output:list of dependent coefficients *)
(***********************************************************************)
DependentCoefficients[exp_, coeffs_List, pars_List] :=
    If[ Expand@exp===0,
        {},
        With[ {print = DebugPrint[False, "[dep-coeffs]"], coefsinxp = CoeffsinExpression[Expand[exp], coeffs]},
            print["DependentCoefficients:exp = ", exp];
            print["DependentCoefficients:UCMatrix = ", UndeterminedCoefficientsMatrix[exp, coefsinxp, pars]];
            Complement[coefsinxp, coefsinxp[[#]]]&@Flatten[Position[#, Except[0, _?NumericQ], 1, 1] & /@ RowReduce@UndeterminedCoefficientsMatrix[exp, coefsinxp, pars, Factors->False]]
        ]
    ]

(* MONOMIAL DEPENDENCE FOR UCE/UCM *)
(*rulesclean::usage ="takes a list of rules, transforms into a system and solves it back, returning a list of rules.";*)

rulesclean = (Solve[And @@ (# /. Rule -> Equal)] // Flatten) &;
(*TODO implement a version with Kleisli*)
MonomialDependenceOperator[variables_Association][monomials_] :=
    Which[
    monomials === $Failed,
    $Failed,
    Head[monomials] === Piecewise,
    PiecewiseOperatorMap[MonomialDependenceOperator, variables, monomials],
    Head[monomials] === List,
    Module[ {generators, depVars, indVars, pars, localvariables, 
    zerosofmonomials, quotients, derivatives, zerosofderivatives, 
    constantmonomials},
     (* generic functions are handled here like dependent variables *)
        depVars = Join[Lookup[variables, "depVars", {}], Lookup[variables, "genFuns", {}]]; 

        (* generators are handled like independent variables *)(*TODO KroenckerDelta should be included here...*)
        indVars = Join[Lookup[variables, "indVars", {}], Lookup[variables, "generators", {}]];
        pars = Lookup[variables, "pars", {}];

        (* compute the generators from the expressions *)
        generators = DeleteDuplicates @ Join[Join @@ (DeleteDuplicates /@ 
        Cases[monomials, Derivative[__][#][__], {0, Infinity}] & /@ depVars), Join @@ (DeleteDuplicates /@ 
        Cases[monomials, #[__], {0, Infinity}] & /@ depVars), indVars];
        localvariables = Append[variables, "generators" -> generators];

        (* compute when the monomials are zero *)
        zerosofmonomials = EqualToZeroOperator[localvariables] /@ Flatten[monomials];

        (* compute when monomials are constant *)
        If[ Lookup[variables,"refineconstantmonomials",False],
            constantmonomials = EqualToZeroOperator[localvariables] /@ (Grad[#, generators] & /@ monomials),
            constantmonomials = {}
        ];

        (* compute quotients *)
        quotients = Select[ With[ {nonzeromonomials = Select[Flatten[monomials], # =!= 0 &]},
                                (Flatten[monomials]/#) & /@ nonzeromonomials
                            ] // Flatten // DeleteDuplicates, # =!= 1 &];
        derivatives = Grad[#, generators] & /@ quotients;
        zerosofderivatives = EqualToZeroOperator[localvariables] /@ derivatives;
        PiecewiseMap[rulesclean[DeleteDuplicates[Flatten[#]]] &, Piecewise[#, {}] & /@ 
        Select[ Join[zerosofmonomials, zerosofderivatives, constantmonomials], # =!= True && # =!= False &] // PiecewiseExpand]
    ]
    ]


UndeterminedCoefficientsEquationOperator[variables_Association][expression_] :=
    If[ Head[expression]===Piecewise,
        PiecewiseOperatorMap[UndeterminedCoefficientsEquationOperator,variables, expression],
        If[ Lookup[variables,"refine", True],
            Module[ {factors, mdep},
                factors = UndeterminedCoefficientsFactors[expression//Expand//RegroupParametersOperator[variables], variables["coefficients"], Lookup[variables,"pars",{}]];
                 
                mdep = MonomialDependenceOperator[variables][factors];
                PiecewiseMap[
                If[ #=!=$Failed,
                    UndeterminedCoefficientsEquationOperator[Append[variables, "refine"->False]][expression/.#//Simplify],
                    $Failed
                ]&,
                mdep]
            ],
            With[ {ucm = UndeterminedCoefficientsEquation[expression//Expand//RegroupParametersOperator[variables], variables["coefficients"], Lookup[variables,"pars",{}]]},
                If[ Head[ucm]===Piecewise,
                    PiecewiseMap[Association[{"matrix"->#[[2]],"vector"->#[[3]], "factors"->#[[1]]}]&,ucm],
                    Association[{"matrix"->ucm[[2]],"vector"->ucm[[3]], "factors"->ucm[[1]]}]
                ]
            ]
        ]
    ]

 
UndeterminedCoefficientsOperator = UndeterminedCoefficientsEquationOperator;

UndeterminedCoefficientsFactors[$Failed, coeffs_List, pars_List:{} ] :=
    $Failed

UndeterminedCoefficientsFactors[expr_Piecewise, coeffs_List, pars_List:{} ] :=
    PiecewiseMap[UndeterminedCoefficientsFactors[#, coeffs, pars]&, expr]

UndeterminedCoefficientsFactors[expr_List, coeffs_List, pars_List:{} ] :=
    Union@@(UndeterminedCoefficientsFactors[#, coeffs, pars]&/@expr)

UndeterminedCoefficientsFactors[expr_, coeffs_List, pars_List:{} ] :=
    Module[ {print, factors,coeffsList,separatedCoeffsList,factorsToCoeffsMapping,factorsToCoeffsAssociation,expr0, expr1},
        expr0 = expr/.Thread[coeffs->0];
        expr1 = expr+(\[FormalZ]-1)expr0;

         (*extract coefficients of the coefficients 'coeffs' in the expression*)
        coeffsList = Map[Coefficient[Expand@expr1,#]&,Append[coeffs,\[FormalZ]]];
        print["coeffsList = ", coeffsList];
        (*If the expression does not contain any coeffs then returns row of 0s and 1 as only factor. Without the code below outputs empty lists.[!]*)
        If[ AllTrue[coeffsList, PossibleZeroQ],
            Return[
             {{1}, {coeffsList}}]
        ];

        (*for each coefficient, transform a sum into a list, if no sum just turns into a list of a single element*)
        separatedCoeffsList = Map[If[ Head[#]===Plus,
                                      List@@#,
                                      {#}
                                  ]&, coeffsList];
        print["separatedCoeffsList = ", separatedCoeffsList];

        (*make a mapping from factors to their corresponding coefficient, by combining coefficients with the same factors*)
        factorsToCoeffsMapping = Map[#[[1,1]]->Total@#[[All,2]]&, Map[SplitBy[#, #[[1]]&]&,Map[Numerizer[#,pars]&, separatedCoeffsList, {2}(*, DistributedContexts->Automatic*)]],{2}];
        print["factorsToCoeffsMapping = ", factorsToCoeffsMapping];

        (*transform a map into association*)
        factorsToCoeffsAssociation = Select[Association/@factorsToCoeffsMapping,!Keys[#]===0&];
        factors = Select[Union@Map[Keys,Flatten@factorsToCoeffsMapping], !(#===0)&]
    ] 

(************************************************************************************************************)
(* ######big-Function: Gaussian Elimination Algorithm######## *)
(************************************************************************************************************)

(* ######mini-Function: EqualToZero ######## *)
(*************************************************************)

FA :=
    ForAll[#1, #2]&;
EE :=
    Exists[#1,#2]&;

(*TODO this implementation does not use facts explicitly, check ImprovedHomogeneousSolveAlwaysOperator.*)
ImprovedHomogeneousSolveAlwaysOperator[variables_Association][eqs0_] :=
    Which[
     eqs0 === $Failed, $Failed,
     Head[eqs0] === Piecewise, 
    PiecewiseOperatorMap[ImprovedHomogeneousSolveAlwaysOperator, variables, eqs0],
    True, Module[ {spa, spap, eqs, sol, dom, vrs, facts, localvariables},
     (* variables *)
              vrs = Lookup[variables, "generators", {}];

              (*If exponents are present and are not numeric, we work with reals otherwise complexes*)
              (*Domain can be set to reals or complexes*)
              dom = Lookup[variables, "domain", If[ FreeQ[eqs, Power[a___, z__?(! NumberQ[#] &)]],
                                                    dom = Complexes,
                                                    dom = Reals
                                                ]];

              (* "facts" are assumptions that should be added to the problem *)
              facts = Lookup[variables, "facts", True];

              (*transforms lists of equations in conjunctions*)
              eqs = (If[ Head[eqs0] === List,
                         And @@ eqs0,
                         eqs0
                     ] /. Equal[x___, 0] :> (With[ {ft = Factor[x]},
                                                 ft == 0
                                             ])) && facts;
              (*the code below replaces the original expression according to the rules:
              A/B=0 if A=0 and B is non-zero 
              products=0 are equivalent to factors=0 
              powers=0 are equivalent to argument=0 if exponent is positive or 1/argument=0 if negative*)
              spa = FixedPoint[# /. Equal[Power[xx_, yy_], 0] :> 
              ((xx == 0 && Reduce[FA[vrs, yy > 0], dom]) || (Factor[1/xx] == 0 && Reduce[FA[vrs, yy < 0], dom])) /. 
              (Equal[xx___, 0] :> (Numerator[xx] == 0 && 
              Reduce[EE[vrs, With[ {den = Denominator[xx]},
                                 If[ Head[den] === Power,
                                     First[den] != 0,
                                     den =!= 0
                                 ]
                             ]], dom])) /. 
              (Equal[Times[xx_, yy___], 0] :> Or @@ (# == 0 & /@ ({xx, yy} // Flatten))) &, eqs];
              localvariables = Append[variables, "coefficients" -> {}];
              spap = spa /. Equal[Plus[xx___], 0] :>
              If[ FreeQ[xx, Alternatives @@ vrs],
                  xx==0,
                  With[ {pre = ParametricRefineOperator[localvariables][xx]},
                      Module[ {aux},
                          aux =
                          PiecewiseMap[(And @@ (((# == 0) &) /@ #)) &,
                          PiecewiseMap[UndeterminedCoefficientsOperator[localvariables][#]["vector"] &, pre]];
                          If[ Head[#] === Piecewise,
                              Or @@ And @@@ (#[[1]]),
                              #
                          ] &[aux]
                      ]
                  ]
              ];

              (*the output is a list of replacement rules (like solve always) AND conditions*)
              sol = ({Flatten[ToRules /@ Select[#, Head[#] === Equal &]], And @@ #}) & /@ 
              (If[ Head[#] === And,
                   List @@ #,
                   {#}
               ] & /@ If[ Head[#] === Or,
                          List @@ #,
                          {#}
                      ] &
              [BooleanConvert[Reduce[FA[vrs, spap], dom]]])
          ]
    ]
 
(*TODO this implementation does not use facts explicitly, check ImprovedHomogeneousSolveAlwaysOperator.*)
(*EqualToZeroOperator[variables_Association][XP_] :=
     Which[
     XP === $Failed, $Failed,
     Head[XP] === Piecewise, 
    PiecewiseOperatorMap[EqualToZeroOperator, variables, XP],
    Head[XP] === List,
    Module[ {},(*maybe we can choose a different, non-branching, solve operator... (this is for Friedemann)*)
        If[ And @@ ((# === 0)||(#===0.) & /@ XP),
            True,
            If[ Cases[XP, _?(MemberQ[Lookup[variables, "pars", {}], #] &), {0, Infinity}] == {},
                False,(*is there an expression without parameters that is a non-trivial representation of zero?*)
                With[ {sol = ImprovedHomogeneousSolveAlwaysOperator[variables][#==0 & /@ XP]},
                    If[ sol === {{{}, False}},
                        False,
                        sol
                    ]
                ]
            ]
        ]
    ], 
    True, EqualToZeroOperator[variables][{XP}]
    ]*)

EqualToZero[variables_][XP_] := 
If[Head[XP]===List,
        If[ And @@ ((# === 0)||(#===0.) & /@ XP),
            True,
            If[ Cases[XP, _?(MemberQ[Lookup[variables, "pars", {}], #] &), {0, Infinity}] == {},
                False,(*is there an expression without parameters that is a non-trivial representation of zero?*)
                With[ {sol = ImprovedHomogeneousSolveAlwaysOperator[variables][#==0 & /@ XP]},
                    If[ sol === {{{}, False}},
                        False,
                        sol
                    ]
                ]
            ]
        ],
        EqualToZero[variables][{XP}]
];
   
EqualToZeroOperator = Kleisli[EqualToZero];
(**** SolveAlwaysOperator *****)


(* solvealways operator wraps up EqualToZero in the standard Mathematica 
convention - empty list of rules
means no solution, list of an empty list means anything is a solution and works like the solvealways
*)

SolveAlwaysOperator[variables_Association][xp_] :=
    Which[
    xp === $Failed,
    $Failed,
    Head[xp] === Piecewise,
    PiecewiseOperatorMap[SolveAlwaysOperator, variables, xp],
    True,
    Which[
    # === True, {{}},
    # === False, {},
    True,
    Piecewise[({{#[[1]]}, #[[2]]}) & /@ #, {}]
    ] &@EqualToZeroOperator[variables][xp]
    ]

(* ######mini-Function: logicalcleaner ######## *)
(* this function attempts to remove logical overlaps in branching *)
(*************************************************************)
logicalcleaner::usage =  
"logicalcleaner[list] returns ";
(*logicalcleaner = Function[lst, Simplify/@MapThread[And[!#1,#2]&, {FoldList[Or,False, lst][[;;-2]], lst}]]*)
logicalcleaner[lst_List] := Simplify/@MapThread[And[!#1,#2]&, {Most@FoldList[Or,False, lst], lst}];
(* ######mini-Function: CompareRows ######## *)
(*************************************************************)
CompareRows::usage =
"CompareRows[r1, r2] takes r1 is {r1[[1]], Integer, Matrix, Vector}, where r1[[1]] is either Boolean {Rule, Equation}, (same for r2). 
r1[[1]] = False implies that the pivot (from Gaussian Elimination) is never (as a function of parameters) zero,
r1[[1]] = {Rule, Equation} implies that the pivot is zero when Equation is satisfied.
r1[[1]] = True implies that the pivot is zero.
Returns True if r1 < r2 and False otherwise."
CompareRows[r1_, r2_] :=
(*TODO remove SimplifyCount from RecursiveRowBranchingGaussianElimination and put it here, compute only when needed*)
    Which[
     (*first is never zero, second can be zero *)
     
     r1[[1]] === False && r2[[1]] =!= False, 
     True, 
     
     (*first and second are never zero, but first is simpler *)
     
     r1[[1]] === False && r2[[1]] === False,
     If[ r1[[2]] < r2[[2]],
         True,
         False
     ],
     
     (* second is literally zero but first is not *)
     
     r1[[1]] =!= True && r2[[1]] === True,
     True, 
     
     (* first is literally zero *)
     
     r1[[1]] === True, 
     False, 
     
     (* now the remaing cases correspond to branching we need to select \
    shortest 
     and then among same length the simplest *)
     
     Length@r1[[1]] < Length@r2[[1]], 
     True, 
     
     Length@r1[[1]] > Length@r2[[1]], 
     False, 
     
     Length@r1[[1]] == Length@r2[[1]], 
     If[ r1[[2]] < r2[[2]],
         True,
         False
     ]
     ]

(* auxiliary functions, identity matrices and zero vectors *)

IdM[M_?ListQ] :=
    IdentityMatrix[Length[M]]

IdM[_] :=
    $Failed

ZdM[M_?ListQ] :=
    0&/@M

ZdM[_] :=
    $Failed

(* ###### Function: RecursiveRowBranchingGaussianElimination ######## *)
(************************************************************************************)
(* The Gaussian Elimination below takes in a matrix and a vector; the \
matrix and the vector have coefficients on the
field of rational functions on the generators; the parameters are \
free parameters - the gaussian elimination will branch according to 
the different parameter values *)
RecursiveRowBranchingGaussianElimination[matrix_, vector_, generators_, parameters_] :=
    RecursiveRowBranchingGaussianElimination[matrix, vector, generators, parameters, True]

RecursiveRowBranchingGaussianElimination[matrix_, vector_, generators_, parameters_, conditions_] :=
    RecursiveRowBranchingGaussianElimination[matrix, vector, generators, parameters, conditions, 1, 1]

RecursiveRowBranchingGaussianElimination[ matrix_, vector_, generators_, parameters_, conditions_, row_, column_] :=
    Module[ {localvariables,matrix1, matrix2, vector1, vector2, aux, cons, sortedrows, newmatrix2, newvector2, genericcase, specialcases,specialcasescleaned},
        If[ Length[matrix] != Length[vector],
            Print["Matrix-vector length mismatch"];
            Return[]
        ];
        If[ row > Length[matrix] || column > If[ Length[matrix]===0,
                                                 0,
                                                 Length@Transpose@matrix
                                             ],
            {{conditions, {matrix, vector}}},
            matrix1 = matrix[[1 ;; row - 1]];
            vector1 = vector[[1 ;; row - 1]];
            matrix2 = Simplify@matrix[[row ;;]]; 
            (* the simplify is really necessary *)
            vector2 = Simplify@vector[[row ;;]];

            (* TODO we are not keeping track of the domain for quantifier elimination *)
            localvariables = Association[{"pars" -> parameters, "generators" -> generators, "facts" -> conditions}];
            aux = MapThread[{ 
            EqualToZeroOperator[localvariables][#1[[column]]],
            Simplify`SimplifyCount[#1[[column]]],#1, #2} &, {matrix2, 
             vector2}];
             
             

            (* there are three cases - all elements are zero, some are non-
            zero and non-branching or all are branching *)

            (* case 1 - all elements of the column are zero - 
            do nothing *)
            If[ (*And @@ ( # === True & /@ Transpose[aux][[1]]), 
*) And @@ ( # === True & /@ First /@ aux), 
            
             (* All entries are zero, no elimination is possible, 
             hence we increment column by one but not the row *)
                RecursiveRowBranchingGaussianElimination[matrix, vector, 
                 generators, parameters, conditions, row, column + 1],

                (* case 2 and 3 - sort *)
                sortedrows = Sort[aux, CompareRows];
                newmatrix2 = sortedrows[[;; , 3]];
                newvector2 = sortedrows[[;; , 4]];

                (* handle the branching and non-branching cases as needed *)
                If[ First[sortedrows][[1]] === False, 
                 
                 (* proceed with standard elimination *)
                    cons = (First@newmatrix2)[[column]];
                    newmatrix2[[1]] = newmatrix2[[1]]/cons;
                    newvector2[[1]] = newvector2[[1]]/cons;
                    Do[
                     cons = newmatrix2[[j, column]];
                     newmatrix2[[j]] = newmatrix2[[j]] - cons newmatrix2[[1]];
                     newvector2[[j]] = newvector2[[j]] - cons newvector2[[1]],
                     {j, 2, Length@newmatrix2}
                     ];
                    RecursiveRowBranchingGaussianElimination[
                     Join[matrix1, newmatrix2],Join[vector1, newvector2], 
                     generators, parameters, conditions, row + 1, column + 1](******)
                    , 
                    (* otherwise we need to consider the branching algorithm *)

                    (* the branching considers the following:

                    1) there is the generic case
                    2) there are the special cases, which in principle could overlap
                    3) we need to do back substitution 
                    *)

                    (* first address the generic case *)
                    cons = (First@newmatrix2)[[column]];
                    newmatrix2[[1]] = newmatrix2[[1]]/cons;
                    newvector2[[1]] = newvector2[[1]]/cons;
                    Do[
                     cons = newmatrix2[[j, column]];
                     newmatrix2[[j]] = newmatrix2[[j]] - cons newmatrix2[[1]];
                     newvector2[[j]] = newvector2[[j]] - cons newvector2[[1]];,
                     {j, 2, Length@newmatrix2}
                     ];

                    (* need to compute the additional conditions for the generic \
                     case *)
                    genericcase =
                     RecursiveRowBranchingGaussianElimination[
                    Join[matrix1, newmatrix2], Join[vector1, newvector2], 
                    generators, parameters, 
                    Simplify[
                     conditions && 
                    And @@ Not /@ 
                    (sortedrows[[1, 1, ;;, 2]])], row + 1, 
                    column + 1];

                    (* then, 
                    for each of the special cases replacing and calling the function \
                     recursively without incrementing row or column *)

                    (* the quiet below is necessary because some denominators may be \
                     zero, this should be fixed - in any case is should not give any problem
                    because in this case the conditions should become false *)
                    specialcases = 
                    Quiet@Select[{Simplify[matrix /. #[[1]]], Simplify[vector /. #[[1]]], 
                     Simplify[
                    conditions&& # [[2]]] } & /@ 
                     sortedrows[[1, 1]], #[[3]] =!= False &];
                    If[ specialcases!={},
                        specialcasescleaned =
                         With[ {lc = logicalcleaner[specialcases[[All,3]]]},
                             Select[Append[(specialcases//Transpose)[[;;-2]], lc]//Transpose, #[[-1]]=!=False &]
                             
                            ],
                        specialcasescleaned = specialcases
                    ];
                    Join[genericcase, Join @@ (
                     RecursiveRowBranchingGaussianElimination[#[[1]], #[[2]], 
                    generators, parameters, #[[3]], row, column] & /@ specialcasescleaned)]
                ]
            ]
        ]
    ]

(* ###### mini-Function: GetSolvabilityConditions ######## *)
(*************************************************************************)
GetSolvabilityConditions[matrix_, vector_] :=
    With[ {zerovector = (0 & /@ Transpose@matrix)},
        And @@ (# == 0 & /@ Select[Transpose[{matrix, vector}], #[[1]] == zerovector &][[;; , 2]])
    ]

(* ###### mini-Function: ExtractAndRefineSolvability ######## *)
(* here we need to improve the handling of the case where solvealways does not work *)
(****************************************************************************)

ExtractAndRefineSolvability[subproblem_, generators_] :=
    Module[ {sc, solvabilityconditions, localvariables},
        sc = GetSolvabilityConditions @@ subproblem[[2]];
        localvariables = Association[{"generators" -> generators}];
        solvabilityconditions = ImprovedHomogeneousSolveAlwaysOperator[localvariables][sc];
        Select[Map[
        With[ {newc = 
        Simplify[subproblem[[1]] && #[[2]]]},
            If[ newc === False,
                $Failed,
                {newc, Simplify[subproblem[[2]] /. #[[1]]]}
            ]
        ] &, 
        solvabilityconditions], 
        # =!= $Failed &]
    ]
 
(* ###### mini-Function: GetNonZeroLines ######## *)
(****************************************************************)

zerolist = Function[list, And@@(((#===0)||(#===0.))&/@list)];

GetNonZeroLines[subproblem_] :=
    {subproblem[[1]], 
     If[ # === {},
         {},
         Transpose@#
     ] &@
    Select[ Transpose[subproblem[[2]]], !zerolist[#[[1]]] &]
    }

(* ###### mini-Function: UpperTriangularCleanUp ######## *)
(***********************************************************************)
UpperTriangularCleanUp[subproblem_] :=
    Module[ {cond, matrix, vector, column, cons},
        cond = subproblem[[1]];
        If[ subproblem[[2]] == {},
            subproblem,
            matrix = subproblem[[2]][[1]];
            vector = subproblem[[2]][[2]];
            If[ Length[vector] == 1,
                subproblem,
                Do[
                 column = First@First@Position[matrix[[j]], n_ /; n == 1];
                 Do[
                 cons = matrix[[k, column]];
                 matrix[[k]] = matrix[[k]] - matrix[[j]] cons;
                 vector[[k]] = vector[[k]] - vector[[j]] cons;
                 ,
                 {k, 1, j - 1}
                 ],
                 {j, Length[vector], 2, -1}];
                {cond, {matrix, vector}}
            ]
        ]
    ]

(* ######Function: BranchingGaussianElimination ######## *)
(***********************************************************************)

(* from this point on is the original branchinggaussianelimination *)
BranchingGaussianElimination[$Failed, vector_, generators_, parameters_,cond_] :=
    $Failed

BranchingGaussianElimination[matrix_, $Failed, generators_, parameters_,cond_] :=
    $Failed

BranchingGaussianElimination[matrix_, vector_, generators_, parameters_] :=
    BranchingGaussianElimination[matrix, vector, generators, parameters, True]

BranchingGaussianElimination[{},{}, generators_, parameters_, cond_] :=
    {{cond, {{}, {}}}}

Options[BranchingGaussianElimination] = {SelfTest->False}; 

BranchingGaussianElimination[matrix0_, vector0_, generators0_, parameters0_, conditions0_, OptionsPattern[]] :=
    Module[ {dom, eqs, spa, XX, utcl, rowreducedproblems, rowreducedproblemswithsolvabilityconds, vars, nvars, tlabels, itlabels,matrix, vector, generators, parameters, conditions},
     (* variables clean-up *)
        vars = Union[Variables[matrix0], Variables[vector0],parameters0, generators0];
        nvars = Unique["a"]&/@vars;
        tlabels = MapThread[Rule, {vars, nvars}];
        itlabels = MapThread[Rule, {nvars, vars}];
        matrix = matrix0/.tlabels;
        vector = vector0/.tlabels;
        generators = generators0/.tlabels;
        parameters = parameters0/.tlabels;
        conditions = conditions0/.tlabels;

        (* row reduce *)
        rowreducedproblems = 
         RecursiveRowBranchingGaussianElimination[matrix, vector, 
        generators, parameters, conditions];

        (* add solvability conditions and remove all the zero lines *)
        (* 
        note that if the equation becomes trivial because all lines of the \
        matrix are zero, the matrix-
        vector disappears and the output is just {condition, {}} *)
        rowreducedproblemswithsolvabilityconds =
         GetNonZeroLines /@ (Join @@ (ExtractAndRefineSolvability[#, generators] & /@ rowreducedproblems));
         
        (* clean upper triangular part for the cases where there exists a \
        solution - why is this not here??? *)
        utcl = (UpperTriangularCleanUp /@ rowreducedproblemswithsolvabilityconds);
        If[ OptionValue[SelfTest],
            XX = Unique["X"]&/@(matrix0[[1]]);
            eqs = Implies[Or@@(#[[1]]&&And@@Map[Factor[#]==0&, 
            If[ #[[2]]=={},
                True,
                #[[2,1]].XX- #[[2, 2]]
            ]]&/@utcl), conditions&&And@@Map[Factor[#]==0&, matrix.XX-vector]];
            spa = FixedPoint[#/. Equal[Power[xx_, yy_], 0]:>((xx==0&&Reduce[FA[generators, yy>0],Reals])||(Factor[1/xx]==0 && Reduce[FA[generators, yy<0],Reals]))/.(Equal[xx___, 0]:>(Numerator[xx]== 0&&Reduce[EE[generators,Denominator[xx]!= 0],Reals]))/.(Equal[Times[xx_,yy___], 0]:>Or@@(#==0&/@({xx,yy}//Flatten)))&, eqs];
            dom = And@@(#!=0&/@Cases[eqs, Power[x__, -1]:>x, {0, Infinity}]);
            Reduce[FA[generators, FA[Complement[Join[nvars, XX],generators],Implies[dom, spa]]], Reals]/.itlabels,
            utcl/.itlabels
        ]
    ]

(* Solvable variables takes a matrix in reduced form (after gaussian elimination)
and gives the list of variables that can be solved directly *)

Pivots[{}] :=
    {}

Pivots[matrix_] :=
    SolvableVariables[matrix, Range@Length@First@matrix]

Pivots[$Failed] :=
    $Failed

Pivots[matrix_Piecewise] :=
    PiecewiseMap[Pivots, matrix]

SolvableVariables[matrix_, variables_] :=
    (First@Select[Transpose[{#, variables}], Function[z, z[[1]]=!=0&&z[[1]]=!=0.]]&/@matrix)[[All,2]]

GaussianEliminationOperator[field_Association][system_] :=
     Which[
    system === $Failed, $Failed, 
    Head[system] === Piecewise,
    PiecewiseOperatorMap[GaussianEliminationOperator, field, system] // PiecewiseExpand,
    True, Module[ {expandedsys},
              expandedsys = PiecewiseExpandAssociation[system];
              Which[
              Head[expandedsys] === Piecewise,
              PiecewiseOperatorMap[GaussianEliminationOperator, field, expandedsys] // PiecewiseExpand,
              True, Module[ {matrix, vector, generators, parameters, cond, sol},
                        matrix = Lookup[system, "matrix"];
                        vector = Lookup[system, "vector", PiecewiseMap[ZdM, matrix]];
                        generators = Lookup[field, "generators", {}];
                        parameters = Lookup[field, "pars", {}];
                        cond = Lookup[field, "facts", True];
                        sol = BranchingGaussianElimination[matrix, vector, generators, parameters, cond];
                        If[ sol =!= $Failed,
                            Piecewise[{Association[
                            If[ #[[2]] === {},
                                {"matrix" -> {}, "vector" -> {}},
                                {"matrix" -> #[[2, 1]], "vector" -> #[[2, 2]]}
                            ]
                            ], #[[1]]} & /@ sol, $Failed
                            ],
                            $Failed
                        ]
                    ]
              ]
          ]
    ]

MatrixInverseOperator[field_Association][matrix_] :=
    Which[matrix === $Failed, $Failed,
    Head[matrix] === Piecewise, 
    PiecewiseOperatorMap[MatrixInverseOperator, field, matrix] // PiecewiseExpand,
     (* if the matrix is not square inversefails *)
     Quiet[matrix==={}||Length[matrix] =!= Length[Transpose[matrix]]], $Failed,
     True,
     With[ {l = Length[matrix]},
         PiecewiseMap[
         If[ Length[#["matrix"]]===l&&#["matrix"]=!=$Failed,
             #["vector"],
             $Failed
         ] &, 
         (GaussianEliminationOperator[field][Association[{"matrix" -> matrix,"vector"->(IdM@matrix)}]])
         ]
     ]
     ]

(* linear system solve solves a linear system by branching gaussian elimination with respect
to a list of variables *)

LinearSystemSolveOperator[field_Association][system_] :=
    Which[
    system === $Failed, $Failed,
    Head[system] === Piecewise, 
    PiecewiseOperatorMap[LinearSystemSolveOperator, field, system] // PiecewiseExpand,
    True,
    With[ {sol = GaussianEliminationOperator[field][system]},
        PiecewiseMap[
         If[ # === $Failed,
             $Failed,
             With[ {vrs = SolvableVariables[#["matrix"], system["unknowns"]]},
                 If[ #["matrix"] === {}||vrs==={},
                     {},
                     First@Solve[#["matrix"].system["unknowns"] ==Lookup[field,"sign",1]* #["vector"], 
                     vrs]
                 ]
             ]
         ]
        &, sol
         ]
    ]
    ]

GenericLinearCombinationOperator[variables_Association][MonList_] := 
    Which[
    MonList === $Failed, $Failed,
    Head[MonList] === Piecewise, PiecewiseOperatorMap[GenericLinearCombinationOperator, variables, MonList],
    True, 
    Module[ {A},
        A = Table[
        If[ Lookup[variables,"unique", False],
            Subscript[Lookup[variables, "coeff", \[FormalA]], Unique[]],
            Subscript[Lookup[variables, "coeff", \[FormalA]], i]
        ],{i, 1, Length[MonList]}];
        {MonList . A//RegroupParametersOperator[variables], A}
    ]
    ]

MatrixKernelOperator[variables_Association][xp_] :=
    Which[
    xp === $Failed,
    $Failed,
    Head[xp] === Piecewise,
    PiecewiseOperatorMap[MatrixKernelOperator, variables, xp],
    xp === {}||xp === {{}},
    Print["Warning: kernel of an empty matrix"];
    $Failed,
    True,
    Module[ {sol, vars, zero, zerov},
        vars = Unique["z"] & /@ First[xp];
        zero = 0 & /@ xp;
        zerov = 0 & /@ vars;
        sol = LinearSystemSolveOperator[variables][
        Association["matrix" -> xp, "vector" -> zero, "unknowns" -> vars]];
        PiecewiseMap[Select[Transpose[#], (# =!= zerov) &] &, PiecewiseMap[Grad[#, vars] &, PiecewiseReplace[vars, sol]]]
    ]
    ]

End[] (* End Private Context *)
(*EndPackage[]*)