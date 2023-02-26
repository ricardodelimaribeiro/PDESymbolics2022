(* Wolfram Language Package *)
(*BeginPackage["PDESymbolics2020`Beaultify`"]*)
IntegrateByPartsOperator::usage =  
"IntegrateByPartsOperator[<|\"depVars\" -> {u}, \"indVars\" -> {x}|>] when applied to an expression, symmetrizes the expression by integrating by parts with respect to indVars";

RemoveDersOperator::usage = 
"RemoveDersOperator[<|\"depVars\" -> {u,v}, \"indVars\" -> {x}, \"rdVars\" -> {v}|>] when applied to an expression, removes the derivatives from rdVars by integrating by parts.";

BeautifyOperator::usage = 
"BeautifyOperator[<|\"depVars\" -> {u}, \"indVars\" -> {x}|>] Chains together IntegrateByPartsOperator with RepresentModNullLagrangians, dropping the \"basis\" key from the  variables.";

Begin["`Private`"] (* Begin Private Context *) 
RemoveDers::usage = "Removes the derivative operator from certain dependent variables"
RemoveDersStep::usage = "RemoveDersStep is a step function for RemoveDers."
IntegrateByParts::usage = "IntegrateByParts[x][expresssion] keeps doing an integration by parts with respect to x till the stationary point";
IntegrateByPartsStep::usage = "IntegrateByPartsStep[x][expresssion] does an integration by parts with respect to x";

(* ##########         Function: IntegrateByParts          ########### *)
(**********************************************************************)
(* IntegrateByParts[x,y,...][expr]                                    *)
(* Purpose: Takes an expressson expr with independent variables x,y,..*)
(*          and tries to balance the number of derivatives            *)
(*          in summands by integration by parts                       *)
(* Input:   A sequence of independent variables                       *)
(*          An expression                                             *)
(* Output:  A transformed expression                                  *)
(**********************************************************************)
(*TODO use Kleisli*)
IntegrateByPartsOperator[variables_Association][expression_] :=
Which[
	expression === $Failed, 
		$Failed,
	Head[expression] === List, 
		Map[IntegrateByPartsOperator[variables], expression]//PiecewiseExpand//PiecewiseListClean,
	Head[expression] === Piecewise, 
		PiecewiseOperatorMap[IntegrateByPartsOperator,variables, expression],
	True, 
		(IntegrateByParts@@Lookup[variables, "intVars", Lookup[variables, "indVars", {}]])[expression]
]

IntegrateByPartsStep[exp_, indVar_Symbol, OptionsPattern[]] :=
Module[{print = DebugPrint[False, "[IBP]"], expr = Expand @ exp, maxDer, maxDerVar, Ders, varsToDers},
	print["expr = ", expr];
	Which[
		Head @ expr === Plus, 
			Total @ Map[IntegrateByPartsStep[#, indVar]&, List @@ expr],
		Head @ expr === Times, 
            varsToDers = Merge[Cases[expr, Derivative[d__][_][v__] :> AssociationThread[{v}->{d}], {0, Infinity}], Identity];
            If[ !MemberQ[Keys @ varsToDers, indVar],
                print @ "1. Calculation has stoped by Return command:no derivatives";
                Return @ expr
            ];
            If[ Position[Integrate[expr, indVar], Integrate] === {},
                print @ "2. Calculation has stoped by Return command:complete derivative";
                Return[0]
            ];
            Ders = varsToDers[indVar];
            print["varsToDers = ", varsToDers];
            print["Ders = ", Ders];
            maxDer = Max @ Ders;
            If[ MemberQ[Ders, maxDer - 1] || maxDer < 2,
                print @ "3. Calculation has stoped by Return command:maxDer";
                Return @ expr
            ];
            maxDerVar = Cases[expr, Derivative[d__][_][v__] /; AssociationThread[{v}->{d}][indVar] == maxDer, {0, Infinity}];
            print["maxDer, maxDerVar = ", maxDer, maxDerVar];
            print[{Length @ maxDerVar == 1, !MemberQ[Ders, maxDer - 1], Exponent[expr, First @ maxDerVar] === 1}];
            If[ Length @ maxDerVar == 1 && Exponent[expr, First @ maxDerVar] === 1,
                Simplify[-D[expr/First @ maxDerVar, indVar] Integrate[First @ maxDerVar, indVar]],
                exp
            ],
            Position[expr, indVar] != {} && Position[Integrate[expr, indVar], Integrate] === {},
            print["Complete derivative"];
            0,
		True,
            print["Nothing can do with it."];
            exp
	]
]

IntegrateByPartsStep[indVar_Symbol] :=
IntegrateByPartsStep[#, indVar]&

IntegrateByParts[indVar_] :=
FixedPoint[IntegrateByPartsStep[indVar], #]&;

IntegrateByParts[indVars___, OptionsPattern[]] :=
RightComposition[Sequence @@ (IntegrateByParts[#]& /@ {indVars})];


(* ##########            Function: RemoveDers              ########### *)
(***********************************************************************)
(* RemoveDers[expr, depVars, indVars]                                  *)
(* Purpose: Removes derivatives from depVars using integration by parts*)
(* Input:   An expression                                              *)
(*          list of dependent variables                                *)
(*          list of independent variables                              *)
(* Output:  expression containing no derivatives of depVars            *)
(***********************************************************************)
RemoveDersStep[exp_, depVar_, indVar_, OptionsPattern[]] :=
Module[ {print = DebugPrint[False, "[rm-ders]"], expr = Expand @ exp, depVarExpr, params}, 
	Which[
		Head @ expr === Plus,
        	print["expr = ", expr];
        	Total @ Map[RemoveDersStep[#, depVar, indVar]&, List @@ expr],
        Head @ expr === Times,
        	print["expr = ", expr];
        	params = DeleteDuplicates @ Cases[expr, depVar[Sequence[___,indVar,___]] | Derivative[___][depVar][Sequence[___,indVar,___]], {0, Infinity}]; 
        	print["params = ", params];
        	If[ params === {},
        		Return[expr]
        	];
        	depVarExpr = ExtractCoefficient[expr, params];
        	print["depVarExpr = ", depVarExpr];
        	If[ FreeQ[Integrate[depVarExpr, indVar], Integrate],
        		Simplify[-D[expr/depVarExpr, indVar]Integrate[depVarExpr, indVar]], expr],
        True,
        	expr
	]
]

Options[RemoveDers] = Options[RemoveDersStep];

(* Function form *)
RemoveDers[exp_, depVar_Symbol, indVar_Symbol, OptionsPattern[]] :=
FixedPoint[RemoveDersStep[#, depVar, indVar]&, exp];

(* Operator form *)
RemoveDers[depVar_Symbol, indVar_Symbol, OptionsPattern[]] :=
RemoveDers[#, depVar, indVar]&;

(* Operator form *)
RemoveDers[depVar_Symbol, indVars_List, OptionsPattern[]] :=
RightComposition[Sequence @@ (RemoveDers[depVar, #]& /@ indVars)];

(* Function form *)
RemoveDers[exp_, depVar_, indVars_List, OptionsPattern[]] :=
RemoveDers[depVar, indVars][exp];

(* Operator form *)
RemoveDers[depVars_List, indVars_List, OptionsPattern[]] :=
RightComposition[Sequence @@ (RemoveDers[#, indVars]& /@ depVars)];

(* Function form *)
RemoveDers[exp_, depVars_List, indVars_List, OptionsPattern[]] :=
RemoveDers[depVars, indVars][exp]

RemoveDersOperator[variables_Association][expression_] :=
	Which[
		expression === $Failed, 
			$Failed, 
		Head[expression] === Piecewise, 
			PiecewiseOperatorMap[RemoveDersOperator,variables, expression], 
		True, 
			RemoveDers[expression, Lookup[variables, "rdVars", {}], Lookup[variables, "indVars", {}]]
	]


BeautifyOperator[variables_Association][expression_] :=
Which[
	expression === $Failed, 
		$Failed,
	Head[expression] === List, 
		Map[BeautifyOperator[variables], expression]//PiecewiseExpand//PiecewiseListClean,
	Head[expression] === Piecewise, 
		PiecewiseOperatorMap[BeautifyOperator,variables, expression],
	True, 
    Module[ {},
    	If[Lookup[variables, "VarDOperator", VarDOperator]===VarDOperator, 
	   IntegralEquivalenceClassOperator[KeyDrop["basis"] @ variables][IntegrateByPartsOperator[variables][expression]],
	   IntegralEquivalenceClassOperator[KeyDrop["basis"] @ variables][expression]
    	]
     ]
]
End[] (* End Private Context *)

(*EndPackage[]*)