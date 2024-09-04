(* Wolfram Language Package *)
(*BeginPackage["PDESymbolics2020`VariationalCalculus`"]*) 

RepresentModNullLagrangiansOperator::usage = 
"RepresentModNullLagrangiansOperator[<|\"depVars\" -> {u}, \"indVars\" -> {x}|>] when applied to an expression,  represents the expression as a linear combination of a basis (for the expression) mod null Lagrangians.
RepresentModNullLagrangiansOperator[<|depVars -> {u}, indVars -> {x}, basis -> {f, g}|>] when applied to an expression, represents the expression as a linear combination of the given basis (for the expression) mod null Lagrangians.";

IntegralEquivalenceClassOperator::usage = 
"IntegralEquivalenceClassOperator[variables][expression] returns the integrand of an equivalent integral quantity"

BasisModNullLagrangiansOperator::usage = 
"BasisModNullLagrangiansOperator[<|\"depVars\" -> {u}, \"indVars\" -> {x}|>] when applied to a list of expressions, returns a basis for the list of expressions modulo null Lagrangians";

CleanNullLagrangiansOperator::usage = 
"CleanNullLagrangiansOperator[<|\"depVars\"->{m},\"indVars\"->{x}|>] when applied to a list of expressions, removes null Lagrangians from the list";

VarDOperator::usage = 
"VarDOperator[<|\"depVars\" -> {u}, \"indVars\" -> {t}|>][expression] gives the variational derivative of the expression with respect to depVars.
VarDOperator[<|\"depVars\" -> {u,v}, \"indVars\" -> {t}|>][expression] gives a list with de variational derivatives of the expression with respect to depVars.
VarDOperator[<|\"depVars\" -> {u}, \"indVars\" -> {x,y,z,t}|>][expression] gives the variational derivative of the expression with respect to depVars.
VarDOperator[<|\"depVars\" -> {u,v,w}, \"indVars\" -> {x,t}|>][expression] gives a list with de variational derivatives of the expression with respect to depVars.";
    
VariationalDOperator::usage = 
"VariationalDOperator[<|\"depVars\" -> {u}, \"indVars\" -> {t}|>][expression] gives the variational derivative of the expression with respect to depVars.
VariationalDOperator[<|\"depVars\" -> {u,v}, \"indVars\" -> {t}|>][expression] gives a list with de variational derivatives of the expression with respect to depVars.
VariationalDOperator[<|\"depVars\" -> {u}, \"indVars\" -> {x,y,z,t}|>][expression] gives the variational derivative of the expression with respect to depVars.
VariationalDOperator[<|\"depVars\" -> {u,v,w}, \"indVars\" -> {x,t}|>][expression] gives a list with de variational derivatives of the expression with respect to depVars
 ";

DVarDOperator::usage = 
"DVarDOperator[<|\"depVars\" -> {u}, \"indVars\" -> {n}|>][expression] gives the variational derivative of the expression with respect to depVars.
DVarDOperator[<|\"depVars\" -> {u,v}, \"indVars\" -> {n}|>][expression] gives a list with de variational derivatives of the expression with respect to depVars.
DVarDOperator[<|\"depVars\" -> {u}, \"indVars\" -> {n1,n2,n3,n4}|>][expression]	gives the variational derivative of the expression with respect to depVars.
DVarDOperator[<|\"depVars\" -> {u,v,w}, \"indVars\" -> {m,n}|>][expression] gives a list with de variational derivatives of the expression with respect to depVarsDVarDOperator is an operator form of Discrete Variational Derivative (DVarD).";

DisintegrateOperator::usage = 
"DisintegrateOperator[<|\"depVars\" -> {u}, \"indVars\" -> {x}|>][expresion] returns a linear combination, whose coefficients add up to 1, of the the terms given by EquivalentsByIBPOpoerator." 

UniqueConstantsCleaner::usage = "cleans up constant numberings";

EquivalentsByIntegrationByPartsOperator::usage = 
"EquivalentsByIntegrationByPartsOperator[variables][expression] gives a basis for all expressions that can be obtained by integration by parts - uses a more robust algorithm than EquivalentsByIBPOperator";

EquivalentsByIntegrationByPartsStepOperator::usage =
"each step of the integration by parts";

StencilOperator::usage = 
"StencilOperator[variables][expression] returns the stencil of a discrete expression";

DiscreteEquivalentsOperator::usage = 
"DiscreteEquivalentsOperator[variables][expression] The discrete version of  EquivalentsByIntegrationByPartsOperator";

FastEquivalentsByIntegrationByPartsOperator::usage = 
"Fast version of EquivalentsByIntegrationByPartsOperator, does not generate a basis"

Translations::usage = 
"Auxiliary function";

PartialDVarDOperator::usage = 
"Partial variational derivative for discrete problems";

KroneckerDeltaOperator::usage = 
"Kronecker delta at a point";

SubtractOneandSelect::usage = 
"SubtractOneandSelect[multiindex] returns a list of the multiindices of order one less together with the argument place and removed multiindex"

Begin["`Private`"] (* Begin Private Context *) 

(*TBD rewrite as operator and clean up *)

SolveVarProb[Lag_, DVars_List, IndpVars_List] :=
  With[{EL = 
     Map[# == 0 &, 
      VarD[Lag, #, IndpVars]&/@ DVars]},
   Module[{sol = DSolve[EL, DVars, IndpVars], fsol},
    If[sol === {},
     Print["There is no solution"],
     fsol = First@sol]]
   ];





(*PartialDVarDOperator[variables_Association][expression_] :=
    Which[
    	expression === $Failed,
    		$Failed,
        Head[expression] === Piecewise, 
            PiecewiseMap[PartialDVarDOperator[variables], expression],
        Head[expression] === List, 
    		Map[PartialDVarDOperator[variables], expression] // PiecewiseExpand // PiecewiseListClean,
    	Sort[variables["indVars"]] === Sort[variables["timeVars"]],
    		expression, 
        Lookup[variables, "order", 1] === 1,
        	Module[ {depVars = Lookup[variables, "depVars", {}], 
    			indVars = Lookup[variables, "indVars", {}], 
    			timeVars = Lookup[variables, "timeVars", {}]},
        		PartialDVarD[expression, #, indVars, timeVars] & /@ depVars
    		],
        Lookup[variables, "order", 1] > 1, 
    		Module[ {localexpression, 
    			depVars = Lookup[variables, "depVars", {}], 
    			indVars = Lookup[variables, "indVars", {}], 
    			timeVars = Lookup[variables, "timeVars", {}]},
        		localexpression = PartialDVarD[expression, #, indVars, timeVars] & /@ depVars;
        		PartialDVarDOperator[Append[variables, "order" -> (variables["order"] - 1)]][localexpression]
    		]
	]*)

PartialDVarDOperator[variables_Association][expression_] := 
  Module[{depVars, indVars, timeVars, order},
    {depVars, indVars, timeVars} = Lookup[variables, {"depVars", "indVars", "timeVars"}, {}];
    order = Lookup[variables, "order", 1];
    
    Which[
      (*expression === $Failed,
        $Failed,*)
      
      MatchQ[expression, _Piecewise],
        PiecewiseMap[PartialDVarDOperator[variables], expression],
      
      MatchQ[expression, _List],
        expression // Map[PartialDVarDOperator[variables]] // PiecewiseExpand // PiecewiseListClean,
      
      Sort[indVars] === Sort[timeVars],
        expression,
      
      order >= 1,
        With[{localExpression = Map[PartialDVarD[expression, #, indVars, timeVars] &, depVars]},
          If[order > 1,
            PartialDVarDOperator[Append[variables, "order" -> (order - 1)]][localExpression],
            localExpression
          ]
        ],
      
      True,
        $Failed  (* Default case to handle unexpected situations *)
    ]
  ]

KroneckerDeltaOperator[n_List] :=
    KroneckerDeltaOperator@@Select[n, #=!=0&]
KroneckerDeltaOperator[] :=
    1;
KroneckerDeltaOperator[n___][m___] :=
    KroneckerDelta @@ (List@n-List@m);

PartialDVarD[expression_, depVars_, indVars_List, timeVars_List] :=
    With[ {instances = 
       DeleteDuplicates[Cases[expression, depVars[___], {0, Infinity}]]}, 
         (*finds all the translations of depVars in expression*)
        Module[ {
           instancesargs,
           instancesargsclean, 
           instancesrules, 
           indVarsused = Select[indVars, MemberQ[timeVars, #] == False &]
           },
            instancesargs = 
            List @@@ instances /. (# -> 0 & /@ indVarsused);
            instancesargsclean = 
            instancesargs /. 
            Join[# + j_ :> Nothing & /@ timeVars, # :> Nothing & /@ 
              timeVars];
            instancesrules = 
            Thread /@ 
            Map[Rule[indVarsused, #] &, 
            indVarsused - # & /@ instancesargsclean];
            MapThread[((KroneckerDeltaOperator
              @((List @@ ((#1 /. #2) /. ((# -> 0 &) /@ 
                     indVarsused))))) (D[
               expression, #1] /. #2)) &, {instances, instancesrules}]
        ] // Total
    ]

$mrr :=
    Times[rest_., Power[Derivative[d__][u_][x__], p_.]] :> 
    Sequence @@ 
    Union@Flatten@
    Table[Expand[
    Derivative[
       Sequence @@ ReplacePart[#, m -> Part[#, m] - k] &@{d}][u][
     x]*D[Times[rest, 
      Power[Derivative[d][u][x], p - 1]], {{x}[[m]], k}]], {m, 
    Length@{d}}, {k, 0, {d}[[m]]}]

EquivalentsByIBP[monomial_, pars_: {}] :=
    Module[ {temp},
        temp = If[ Head@# === Plus,
                   List @@ #,
                   #
               ] & /@ 
          ReplaceList[monomial, $mrr];
        Union[First@Numerizer[#, pars] & /@ Append[Flatten@temp, monomial]]
    ]

FastEquivalentsByIntegrationByPartsOperator[variables_Association][problem_] :=
    Which[
     problem === $Failed,
     $Failed,
     Head[problem] === Piecewise,
     PiecewiseOperatorMap[FastEquivalentsByIntegrationByPartsOperator, 
      variables, problem],
     Head[problem] === List,
     FastEquivalentsByIntegrationByPartsOperator[variables] /@ problem//PiecewiseExpand//PiecewiseListClean,
     Head[problem] === Association,
     DeleteDuplicates@
      Flatten@Nest[
        FastEquivalentsByIntegrationByPartsOperator[variables], 
        problem["expression"], 
        Lookup[problem, "depth", Lookup[variables, "depth", 1]]],
     True,
     With[ {pex = problem // Expand},
         If[ Head[pex] === Plus,
             EquivalentsByIBP[#, Lookup[variables, "pars", {}]] & /@ (List @@ 
                 pex) // Flatten,
             EquivalentsByIBP[problem, Lookup[variables, "pars", {}]]
         ]
     ]
     ]

(*TODO document. This is an operator that does something...*)

SubtractOneandSelect[L_] :=
    Select[MapIndexed[{ReplacePart[L, #2[[1]] -> (L[[#2[[1]]]] - 1)], #2 // First, ReplacePart[(0 &) /@ L, #2[[1]] -> 1]} &, L], 
        AllTrue[#[[1]], (# >= 0 &)] &];

integratebyparts::usage = 
"integratebyparts[xp, var, arg, mindex1, argmindex, mindex2] returns the integrand ZZZ"

integratebyparts[xp_, variable_, arguments_, multiindex1_, argumentindex_, multiindex2_] :=
    -D[xp/((Derivative @@ (multiindex1 + multiindex2))[variable][Sequence @@ arguments]), 
        arguments[[argumentindex]]] (Derivative @@ multiindex1)[variable][Sequence @@ arguments] // Expand;

EquivalentsByIntegrationByPartsStepOperator[variables_Association][xp_] :=
    Which[
        xp === $Failed,
            $Failed,
        Head[xp] === Piecewise,
            PiecewiseOperatorMap[EquivalentsByIntegrationByPartsStepOperator, variables, xp],
        True,    
        With[ {xpp = RegroupParametersOperator[variables][xp]},
            Which[    
            Head[xpp] === Plus, 
                EquivalentsByIntegrationByPartsStepOperator[variables][List @@ xpp]//PiecewiseExpand,
            Head[xpp] === List,
                BasisOperator[variables] @ PiecewiseMap[Select[Flatten[#], ( # =!= $Failed &)] &, 
                    With[ {pexp = PiecewiseExpand[xpp]},
                        If[ Head[pexp] === Piecewise,
                            PiecewiseOperatorMap[EquivalentsByIntegrationByPartsStepOperator, variables, pexp],
                            Map[EquivalentsByIntegrationByPartsStepOperator[variables], pexp] // PiecewiseExpand
                        ]
                    ]
                  ],
            True,
                Module[ {ders, pders, depVars, indVars, derivativepattern, integratebypartsexpressions},
                     (* derivatives in the expression *)
                    depVars = variables["depVars"];
                    indVars = variables["indVars"];
                    derivativepattern = Alternatives @@ (Derivative[___][Alternatives @@ depVars][Sequence[___, #, ___]] & /@ indVars);
                    ders = DeleteDuplicates @ Flatten @ (Cases[xp, derivativepattern, {0, Infinity}] & /@ indVars);
                    pders = # /. Derivative[z : ___][v___][x___] :> {List @ z, v, List[x]} & /@ ders;
        
                    (* compute integrate by parts *)
                    integratebypartsexpressions = Flatten @ Map[
                        Module[ {transformedindices},
                            With[ {multiindex = #[[1]], variable = #[[2]], arguments = #[[3]]},
                                transformedindices = SubtractOneandSelect[multiindex];
                                Map[(integratebyparts[xpp, variable, arguments, #[[1]], #[[2]], #[[3]]] &), transformedindices]
                            ]
                        ] &, pders
                     ];
                     (* finally the result - the current expression with all its possible integration by parts *)
                    BasisOperator[variables][Prepend[integratebypartsexpressions, xpp]]
                ]
            ]
        ]
    ]
 
EquivalentsByIntegrationByPartsOperator[variables_Association][xp_] :=
    Which[
        xp === $Failed,
            $Failed,
        Head[xp] === Piecewise,
            PiecewiseOperatorMap[EquivalentsByIntegrationByPartsOperator, variables, xp],
        True, 
            FixedPoint[
                Module[ {},
                    EquivalentsByIntegrationByPartsStepOperator[variables][#]
                ]&,
                EquivalentsByIntegrationByPartsStepOperator[variables][xp], 
                Lookup[variables, "depth", 8],
                SameTest -> (PiecewiseMap[Length, #1] === PiecewiseMap[Length, #2] &)]
    ]


RepresentModNullLagrangiansOperator[variables_Association][expression_] :=
    Which[
     expression === $Failed,
     $Failed,
     Head[expression] === List,
     Map[RepresentModNullLagrangiansOperator[variables], expression] // 
    PiecewiseExpand // PiecewiseListClean,
     Head[expression] === Piecewise,
     PiecewiseOperatorMap[RepresentModNullLagrangiansOperator, 
      variables, expression], 
      And @@ ((# === 0 &) /@ 
        (Expand[Lookup[variables, "VarDOperator", VarDOperator][
           variables][
          expression]]// RegroupParametersOperator[variables])),(*Returns what it would when expression is a \
    null Lagrangian*)
     0,
     True,
     Module[ {generatorlist, basis, GLC, VDGLC, SOL, ESOL, 
       expandeexpression},
         expandeexpression = 
          Expand[expression] // RegroupParametersOperator[variables];
         generatorlist = 
          Lookup[variables, "basis", 
           If[ Head[expandeexpression] === Plus,
               List @@ expandeexpression,
               {expandeexpression}
           ]];
         basis = BasisModNullLagrangiansOperator[variables][generatorlist] // PiecewiseEliminateEqualitiesOperator[variables];
         (*GLC={linear combination,coefficients}*)
         GLC = GenericLinearCombinationOperator[Append[variables, "unique" -> True]][basis];
         VDGLC = PiecewiseMap[Association[
             "expression" -> 
              RegroupParametersOperator[variables]@(Expand@Simplify[ Lookup[variables, "VarDOperator", VarDOperator][
                variables][#[[1]] - expandeexpression]]),
             "coefficients" -> #[[2]]] &, GLC]//PiecewiseEliminateEqualitiesOperator[variables];
            
         (*below we need to use piecewiseoperator map*)
         SOL = PiecewiseOperatorMap[SolveUndeterminedCoefficientsOperator, 
           variables, VDGLC]//PiecewiseBeautify;
         (*use here piecewisereplace*)
         ESOL = PiecewiseExpand[{VDGLC, SOL}];
         PiecewiseMap[First, PiecewiseReplace[GLC, SOL]]
     ]
     ]

IntegralEquivalenceClassOperator[variables_Association][expression_] :=
    Which[
         expression === $Failed, 
             $Failed,
         Head[expression] === List, 
             Map[IntegralEquivalenceClassOperator[variables], expression] // PiecewiseExpand // PiecewiseListClean,
         Head[expression] === Piecewise, 
             PiecewiseOperatorMap[IntegralEquivalenceClassOperator, variables, expression],
         True, 
             Module[ {xpatzero, replacementrule, powerreplacementrule, 
             	wholevariables, powerderivativereplacementrule, 
             	derivativereplacementrule,
             	depvars = variables["depVars"]},
                 replacementrule = # :> Function[0]&  /@ depvars;
                 wholevariables = #[Sequence @@ variables["indVars"]] & /@ depvars;
                 derivativereplacementrule = Derivative[___][#][__] :> 0 & /@ depvars;
                 powerderivativereplacementrule = Power[Derivative[___][#][__], ___] :> 0 & /@ depvars;
                 powerreplacementrule = Power[#[__], ___] :> 0 & /@ depvars(*wholevariables*);
                 xpatzero = expression /. powerderivativereplacementrule;
                 xpatzero = xpatzero /. derivativereplacementrule;
                 xpatzero = xpatzero /. powerreplacementrule;
                 xpatzero = xpatzero /. replacementrule;
                 (*this is a fix for when the expression involves powers of u and/or its derivatives.*)
                 (*xpatzero = xpatzero/.Power[0,___]->0;*)
                 PiecewiseMap[If[xpatzero=!=$Failed, #+ xpatzero, $Failed]&, RepresentModNullLagrangiansOperator[variables][(expression - xpatzero)]] //PiecewiseExpand
             ]
    ]

(* ############## Operator:CleanNullLagrangiansOperator ############## *)
(***********************************************************************)
(* Usage:   CleanNullLagsOperator[variables][MonList]                  *)
(* Purpose: Takes a list of monomials and removes the ones that        *)
(*          have zero variational derivative,i.e.are null Lagrangians  *)
(* Input: variables = Association[{"indVars"\[Rule] ...{x},            *)
(*                                 "depVars"\[Rule] ...{u},            *)
(*                                 "VarDOperator"\[Rule] VarDOperator  *)
(*                                 }];                                 *)
(*        list of monomials                                            *)
(* Output: Cleaned list of monomials, without null Lagrangians         *)
(***********************************************************************)
CleanNullLagrangiansOperator[variables_Association][listofexpressions_] :=
    Which[listofexpressions === $Failed, $Failed,
        Head[listofexpressions] === Piecewise, 
            PiecewiseMap[CleanNullLagrangiansOperator[variables], listofexpressions],
        True, 
            Select[listofexpressions, Simplify[Lookup[variables, "VarDOperator", VarDOperator][variables][#] =!= {0}&]]
    ]

(* #################### Operator: VarDOperator ###################### *)
(**********************************************************************)
(* Usage:   VarDOperator[variables][expression]                       *)
(* Purpose: Takes an expressson and computes the variational          *)
(*          derivative(s) with respect to the variables association,  *)
(*          as VariationalD function does.                            *)
(* Input:   variables=Association[{    "depVars"\[Rule] {u,v,...},    *)
(*                                     "indVars"\[Rule]{x,y,...},     *)
(*                                   "order"\[Rule]                   *)
(*          expression                                                *)
(* Output:  Variational derivative(s) of the expression wrt to        *)
(*            depVars@indVars                                         *)
(**********************************************************************)
VarDOperator[variables_Association][expression_] :=
    Which[
        expression === $Failed, $Failed,
        Head[expression] === Piecewise, 
                PiecewiseMap[VarDOperator[variables], expression],
        Head[expression] === List, 
                VarDOperator[variables] /@ expression//PiecewiseExpand//PiecewiseListClean, (*using sugar to Map*)
        Lookup[variables, "order", 1] === 1,
                Module[ {depVars = Lookup[variables, "depVars", {}], indVars = Lookup[variables, "indVars", {}]},
                    (VarD[expression, #, indVars] &) /@ depVars
                ],
        Lookup[variables, "order", 1] > 1, 
                Module[ {localexpression, depVars = Lookup[variables, "depVars", {}], indVars = Lookup[variables, "indVars", {}]},
                    localexpression = (VarD[expression, #, indVars] &) /@ depVars;
                    VarDOperator[Append[variables, "order" -> (variables["order"] - 1)]] /@ localexpression
                ]
    ]



VarD[L_, DepVar_Symbol, IndVars_List] :=
    With[ {Dfuncs = DeleteDuplicates @ Cases[L, Derivative[__][DepVar][Sequence@@IndVars], {0, Infinity}]},
        D[L, DepVar @@ IndVars] + Total @ Map[
        		(-1)^(Total[
        			ReplaceAll[
        				Derivative[ders__][_][__]:>{ders}
        			][#]
        		])#/.{
        			DepVar->Function[#1, #2]& [IndVars, D[L, #]]
        		}&, Dfuncs
        		]
    ]

VarD::BadArgs = 
"Incorrect input of arguments";

VarD[___] :=
    "nothing"/;Message[VarD::BadArgs];

VariationalDOperator[variables_Association][expression_] :=
    Which[
        expression === $Failed, 
            $Failed, 
        Head[expression] === Piecewise, 
                PiecewiseMap[VariationalDOperator[variables], expression],
        Head[expression] === List, 
                Map[VariationalDOperator[variables],expression]//PiecewiseExpand//PiecewiseListClean, 
        Lookup[variables, "order", 1] === 1,
                Module[ {depVars = Lookup[variables, "depVars", {}], indVars = Lookup[variables, "indVars", {}]},
                    VariationalD[expression, (#@@indVars)&/@depVars, indVars]
                ],
        Lookup[variables, "order", 1] > 1, 
            Module[ {localexpression, depVars = Lookup[variables, "depVars", {}], indVars = Lookup[variables, "indVars", {}]},
                localexpression = VariationalD[expression, (#@@indVars)&/@depVars, indVars];
                VariationalDOperator[Append[variables, "order" -> (variables["order"] - 1)]]/@localexpression
            ]
    ]
    
(* #################### Operator: DVarDOperator ##################### *)
(**********************************************************************)
(* Usage:   DVarDOperator[variables][expression]                      *)
(* Purpose: Takes an expressson and computes the variational          *)
(*          derivative(s) with respect to the variables association,  *)
(*          as VariationalD function does.                            *)
(* Input:   variables=Association[{    "depVars" -> {u,v,...},              *)
(*                                  "indVars" ->{m,n,...},               *)
(*                                  "order" -> 2                         *)
(*          expression                                                *)
(* Output:  Variational derivative(s) of the expression wrt to        *)
(*            depVars@indVars                                         *)
(**********************************************************************)
DVarDOperator[variables_Association][expression_] :=
    Which[
        expression === $Failed, 
                $Failed,
        Head[expression] === Piecewise, 
                PiecewiseMap[DVarDOperator[variables], expression],
        Head[expression] === List, 
                Map[DVarDOperator[variables],expression]//PiecewiseExpand//PiecewiseListClean, 
        Lookup[variables, "order", 1] === 1,
                Module[ {depVars = Lookup[variables, "depVars", {}], indVars = Lookup[variables, "indVars", {}]},
                    DVarD[expression, #, indVars]&/@depVars
                ],
        Lookup[variables, "order", 1] > 1, 
            Module[ {localvariables = variables, localexpression, depVars = Lookup[variables, "depVars", {}], indVars = Lookup[variables, "indVars", {}]},
                localexpression = DVarD[expression, #, indVars]& /@ depVars;
                DVarDOperator[AssociateTo[localvariables, "order" -> (localvariables["order"] - 1)]] /@ localexpression
            ]
    ]


DVarD[expression_, depVars_, indVars_List] :=
    With[ {instances = DeleteDuplicates[Cases[expression, depVars[___], {0, Infinity}]]}, 
        (*finds all the translations of depVars in expression*)
        Module[ {instancesargs, instancesrules},
            instancesargs = List@@@instances/.(# -> 0 &/@indVars);
            instancesrules = Thread/@Map[Rule[indVars, #]&, indVars - #&/@instancesargs];
            MapThread[D[expression, #1]/.#2&, {instances, instancesrules}] // Total
        ]
    ];

BasisModNullLagrangiansOperator[variables_Association][MonList_] :=
    Which[
        MonList === $Failed, 
            $Failed,
          Head[MonList] === Piecewise, 
              PiecewiseOperatorMap[BasisModNullLagrangiansOperator, variables, MonList],
          Head[MonList] === List,
              Module[ {cleanedList = CleanNullLagrangiansOperator[variables][MonList], sortedList, varList, coeffList, localvariables = variables, matrix, reducedmatrix, faux},
                  sortedList = Lookup[variables, "sortoperator", Sort][cleanedList];
                  varList = Lookup[variables, "VarDOperator", VarDOperator][variables][sortedList]// RegroupParametersOperator[variables];
                  coeffList = Table[Subscript[\[FormalA], i], {i, Length@cleanedList}];
                  AssociateTo[localvariables, {"pars" -> Lookup[localvariables, "pars", {}], "coefficients" -> coeffList, "refine" -> True, "facts" -> Lookup[localvariables, "facts", True], "generators" -> {}}];
                  matrix = UndeterminedCoefficientsOperator[localvariables][coeffList.varList];
                  reducedmatrix = GaussianEliminationOperator[localvariables][matrix];
                  faux = (If[ # =!= $Failed,
                              sortedList[[#]],
                              $Failed
                          ]) &;
                  PiecewiseMap[faux, PiecewiseMap[Pivots[#["matrix"]] &, reducedmatrix] // PiecewiseExpand] // PiecewiseExpand // PiecewiseBeautify
              ]
    ]

UniqueConstantsCleaner[name_] :=
    With[ {T = DeleteDuplicates@Cases[#, Subscript[name, _], {0, Infinity}]},
        # /. MapIndexed[(#1 -> Subscript[name, #2 // First]) &, T]
    ] &;

DisintegrateOperator[variables_][ XP_] :=
    If[ Lookup[variables, "uniqueconstantsclean", True],
        UniqueConstantsCleaner[
         Lookup[variables, "coeff", \[FormalA]]],
        # &
    ]@
     Which[XP === $Failed,
      $Failed,
      Head[XP] === Piecewise,
      PiecewiseOperatorMap[DisintegrateOperator, 
       Append[variables, "uniqueconstantsclean" -> False], XP],
      Head[XP] === List,
      (DisintegrateOperator[Append[variables, {"unique" -> True, "uniqueconstantsclean" -> False}]] /@ XP)//PiecewiseExpand//PiecewiseListClean,
      True,(*XP is a scalar expression*)      
      Module[ {equivalents, glc, linearproblem, rules, 
        vardoperator = Lookup[variables, "VarDOperator", VarDOperator]
           },
          equivalents = Lookup[variables,"EquivalentsOperator", 0];
          If[ equivalents == 0,
              equivalents = If[ Lookup[variables, "VarDOperator",$Failed] === DVarDOperator,
                                DiscreteEquivalentsOperator[variables][XP],
                                FastEquivalentsByIntegrationByPartsOperator[variables][<|"expression" -> XP|>]
                            ]
          ];
           If[ Head[equivalents] === Piecewise,
               glc = 
                PiecewiseOperatorMap[GenericLinearCombinationOperator, 
                 Append[variables, "unique" -> True], 
                 Piecewise@PiecewiseLastCaseClean @  equivalents],
               glc = 
                GenericLinearCombinationOperator[
                  Append[variables, "unique" -> True]][equivalents]
           ];
          linearproblem = 
           PiecewiseMap[{#[[1]], 
              Append[variables, "coefficients" -> #[[2]]]} &, glc];
          rules = 
           PiecewiseMap[(SolveUndeterminedCoefficientsOperator[#[[2]]][
               vardoperator[variables][#[[1]] - XP]]) &, linearproblem];
          PiecewiseMap[First, PiecewiseReplace[glc, rules]]
      ]
      ]
   
(* given an expression computes the stencil on the dependent \
variables *)

StencilOperator[variables_Association][xp_] :=
    Which[
      xp === $Failed,
      $Failed,
      Head[xp] === Piecewise,
      PiecewiseOperatorMap[StencilOperator, variables, xp],
    Head[xp] === List,
    StencilOperator[variables][#] & /@ xp // PiecewiseExpand // 
   PiecewiseListClean,
      True,
      With[ {
          dv = Lookup[variables, "depVars", {}],
          iv = Lookup[variables, "indVars", {}]
          },
          DeleteDuplicates /@ ((# -> 
                           
              Cases[{xp}, #[z___] -> {z}, {0, Infinity}] & /@ 
                       dv) /. (Rule[#, 0] & /@ iv) // Association)
      ]
      ]
(* this is an auxiliary function used in DiscreteEquivalentsOperator*)

Translations[masterstencil_, stencil_] :=
    If[ stencil === Association[],
        {},
        Module[ {diff, sum, possibletranslations},
            diff :=
                Function[{a, b}, # - b & /@ a];
            sum :=
                Function[{a, b}, # + b & /@ a];
            possibletranslations = 
             Intersection @@ (diff[masterstencil[#], 
                  With[ {tstencil = stencil[#]},
                      First[tstencil]
                  ]] & /@ 
                Keys[stencil]);
            Select[
             possibletranslations, (And @@ (Function[key, 
                   ContainsAll[masterstencil[key], sum[stencil[key], #]]] /@ 
                  Keys[stencil])) &]
        ]
    ];


(* this is the discrete counterpart of \
EquivalentsByIntegrationByParts *)

DiscreteEquivalentsOperator[variables_][xp_] :=
    Which[
         xp === $Failed,
             $Failed,
         Head[xp] === Piecewise,
             PiecewiseOperatorMap[DiscreteEquivalentsOperator, variables, xp],
         Head[xp] === List,
             DiscreteEquivalentsOperator[variables] /@ xp//PiecewiseExpand//PiecewiseListClean,
         True,
             With[ {xxp = xp//Expand//RegroupParametersOperator[variables]},
                 If[ Head[xxp] =!= Plus,
                     {xxp},
                     With[ {
                           masterstencil = StencilOperator[variables][xp], 
                           xplist = List @@ xxp
                           },
                         MapThread[Function[{translationlist, xppart},
                         (xppart /. MapThread[
                           Rule[#1, #1 + #2] &, {variables["indVars"] , #}]) & /@ translationlist
                         ], {Translations[masterstencil, 
                         StencilOperator[variables][#]] & /@ xplist, xplist}
                         ] // Flatten // DeleteDuplicates // BasisOperator[variables]
                     ]
                 ]
             ]
     ]   
    
End[] (* End Private Context *)
(*EndPackage[]*)