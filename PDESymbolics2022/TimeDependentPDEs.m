(* Wolfram Language package *)
(*BeginPackage["PDESymbolics2020`TimeDependentPDEs`"]*)
TimeDerOperator::usage = 
"TimeDerOperator[<|\"depVars\" -> {u}, \"indVars\" -> {x}, \"timederivativeorder\" -> n, \"eqRhs\"-> {N[u][x]}|>] when applied to an expression, gives the n-th order time derivative of the integral of the expression where u_t[x] = N[u][x].
TimeDerOperator[<|\"depVars\" -> {u}, \"indVars\" -> {x}, \"timederivativeorder\" -> n, \"eqRhs\"-> {N[u][x]}, \"Beautify\" -> True|>] beautifies the result of the above";

FindConservedQuantityOperator::usage = 
"FindConservedQuantityOperator[<|\"depVars\" -> {u}, \"indVars\" -> {x}, \"timederivativeorder\" -> n, \"eqRhs\"-> {N[u[x]]}|>][<|\"degree\" -> p,\"derivatives\" -> q|>] finds a general quantity, built by monomials of degree at most p on the depVars and its derivatives of order at most q, whose n-th order time derivative along the solutions of u_t[x] = N[u][x] is zero";

FindConservedQuantityBasisOperator::usage = 
"FindConservedQuantityBasisOperator[<|\"depVars\" -> {u}, \"indVars\" -> {x}, \"timederivativeorder\" -> n, \"eqRhs\"-> {N[u[x]]}|>][<|\"degree\" -> p,\"derivatives\" -> q|>] finds a basis of quantities, built by monomials of degree at most p on the depVars and its derivatives of order at most q, whose n-th order time derivative along the solutions of u_t[x] = N[u][x] is zero";

FindIntegratingFactorOperator::usage = 
"FindIntegratingFactorOperator[variables][expression] finds integrating factors for expressions";

FindIntegratingFactorBasisOperator::usage = 
"FindIntegratingFactorBasisOperator[variables][expression] finds a basis of integrating factors for expressions";

ConservedQOperator::usage =
"ConservedQOperator[variables][expression] returns True if the quantity is conserved"

Begin["`Private`"]
TimeDerOperator[variables_Association][expression_Association] :=
    TimeDerOperator[
        Append[variables, 
            {
            "timederivativeorder"->Lookup[expression, "timederivativeorder", Lookup[variables,"timederivativeorder",1]],
            "eqRhs"->Lookup[expression, "eqRhs", Lookup[variables,"eqRhs",1]]
            }]
        ][Lookup[expression, "expression",0]];
            
TimeDerOperator[variables_Association][expression_] :=
    Which[ 
        expression === $Failed, $Failed,
        Head[expression] === Piecewise, PiecewiseOperatorMap[TimeDerOperator, variables, expression],
        Head[expression] === List, TimeDerOperator[variables] /@ expression //PiecewiseExpand//PiecewiseListClean,(*trying to fix list issue*) 
        True,
        If[ Lookup[variables, "Beautify", False],
            
              With[ {bo = 
                  If[ Lookup[variables, "VarDOperator", VarDOperator] === VarDOperator,
                      BeautifyOperator[variables][#]&, (*integrate by parts, then represent without predefined basis*)
                      RepresentModNullLagrangiansOperator[KeyDrop["basis"][variables]][#]&
                  (*just represent without predefined basis*)
                          ]
              },
                  Nest[(bo[Lookup[variables, "VarDOperator", VarDOperator][Append[variables,"order" -> 1]][#] . Lookup[variables, "eqRhs", {}]])&, expression, Lookup[variables, "timederivativeorder", 1] ]
              ],
              Nest[(Lookup[variables, "VarDOperator", VarDOperator][Append[variables,"order" -> 1]][#] . Lookup[variables, "eqRhs", {}])&, expression, Lookup[variables, "timederivativeorder", 1] ]
          ]
    ];

expand :=
    Expand[#] /. Power[x_, y_] :> Power[Expand[Power[x, -y]], -1] &;

FindConservedQuantityOperator[variables_Association][problem_] :=
    Which[
     xp === $Failed,
     $Failed,
     Head[xp] === Piecewise,
     PiecewiseOperatorMap[FindConservedQuantityOperator, variables, 
      xp],
     True,
     Module[ {monomials, basis, glc, conservationcondition, sol},
         monomials = MonomialsOperator[variables][problem];
         basis = BasisModNullLagrangiansOperator[variables][monomials];
         glc = GenericLinearCombinationOperator[variables][basis];
         conservationcondition = 
          PiecewiseMap[Expand@Simplify@expand[Lookup[variables, "VarDOperator",VarDOperator][variables][TimeDerOperator[
              Append[variables, 
             {
             "timederivativeorder"->Lookup[problem, "timederivativeorder", Lookup[variables,"timederivativeorder",1]],
             "eqRhs"->Lookup[problem, "eqRhs", Lookup[variables,"eqRhs",1]],
             "Beautify"->False
             }]
              ][#[[1]]]]]&,glc]//PiecewiseExpand;
       
         sol = PiecewiseMap[
         If[ #[[1]] === $Failed || #[[2]] === $Failed,
             $Failed,
             SolveUndeterminedCoefficientsOperator[
               Append[variables, "coefficients" -> #[[1, 2]]]][#[[2]]]
         ] &,
         PiecewiseExpand[{glc, conservationcondition}]];
         PiecewiseMap[First, PiecewiseReplace[glc, sol]]
         ]
     ];
   
 FindConservedQuantityBasisOperator[variables_Association][problem_] :=
     With[ {conservationlaws = FindConservedQuantityOperator[variables][problem]},
         PiecewiseMap[
          With[ {coefficients = DeleteDuplicates[Cases[#, Subscript[\[FormalA], _],{0,Infinity}]]},
              Map[Function[coeff, conservationlaws /. coeff -> 1] ,
                coefficients] /. (Function[c,Rule[c, 0]]  /@ coefficients)
          ] &
          ,
          conservationlaws]
     ];
   
FindIntegratingFactorOperator[variables_Association][problem_] :=
    Which[
     problem === $Failed,
     $Failed,
     Head[problem] === Piecewise,
     PiecewiseOperatorMap[
      FindIntegratingFactorOperator, variables, problem],
     True,
     Module[ {monomials, glc, integratingcondition, sol},
         monomials = 
          MonomialsOperator[variables][
           If[ Head[#] =!= List,
               Table[#, {j, 1, 
                 Length[problem["expression"]]}],
               #
           ] &[(Lookup[problem, 
              "monomials", Association[] & /@ problem["expression"]])]];
         glc = GenericLinearCombinationOperator[
              Append[variables, "unique" -> True]][#] & /@ monomials;
         integratingcondition =
          Expand[Lookup[variables, "VarDOperator", VarDOperator][variables][
            Lookup[problem, "expression", {0}].glc[[All, 1]]]];
         sol = SolveUndeterminedCoefficientsOperator[variables][
           Association["coefficients" -> Flatten[glc[[All, 2]]],
            "expression" -> integratingcondition]];
         PiecewiseReplace[glc[[All, 1]], sol] // 
     UniqueConstantsCleaner[\[FormalA]]
     ]];

FindIntegratingFactorBasisOperator[variables_Association][problem_] :=
    With[ {
    integratingfactors = 
     FindIntegratingFactorOperator[variables][problem]},
        PiecewiseMap[
         With[ {coefficients = 
             DeleteDuplicates[
              Cases[#, Subscript[\[FormalA], _], {0, Infinity}]]},
             Map[Function[coeff, integratingfactors /. coeff -> 1], 
               coefficients] /. (Function[c, Rule[c, 0]] /@ coefficients)
         ] &,
          integratingfactors]
    ];

ConservedQ::usage = 
"ConservedQ[f, RHSEq, DepVars_List, IndVars_List] checks if exp quantity is conserved";

  (*ConservedQ*)
ConservedQ[exp_, RHSEq_List, DepVars_List, IndVars_List] :=
    FullSimplify@VarD[TimeDer[exp, RHSEq, DepVars,IndVars],  
    	DepVars,IndVars] == 0;

ConservedQ[exp_, RHSEq_List, DepVars_List, IndVars_List , n_] :=
    FullSimplify@VarD[TimeDer[exp, RHSEq, DepVars,IndVars, n],  
    	DepVars,IndVars] == 0;
          
ConservedQOperator[variables_][expression_]:=
	Module[{},
		EqualToZeroOperator[variables]@TimeDerOperator[variables][expression]
	]

End[]
(*EndPackage[]*)