(* Wolfram Language Package *)
(* Exported symbols added here with SymbolName::usage *)  
(* piecewise expressions handling *)

(*BeginPackage["PDESymbolics2020`PiecewiseTools`"]*)
PiecewiseMap::usage = 
"PiecewiseMap[function, piecewiseExpression] Maps function through piecewiseExpression.";

PiecewiseOperatorMap::usage = (*just making a small change*)
"PiecewiseOperatorMap[operator, variables, piecewiseExpression] Maps operator[variables] through piecewiseExpression and updates facts in variables.";

PiecewiseSimplifyOperator::usage = 
"PiecewiseSimplifyOperator[variables][piecewiseExpression] Simplifies piecewiseExpression by replacing, if possible, the parameters (from variables)";

PiecewiseFullSimplifyOperator::usage = 
"PiecewiseFullSimplifyOperator[variables][piecewiseExpression] FullSimplifies piecewiseExpression by replacing, if possible, the parameters (from variables)";

PiecewiseEliminateEqualitiesOperator::usage = 
"PiecewiseEliminateEqualitiesOperator[variables][expression] replaces definite values of parameter cases in the expression"

PiecewiseEqualOperator::usage = 
"PiecewiseEqualOperator[variables][exp1, exp2] returns True if the expressions are (non-trivially) equal"

PiecewiseBeautify::usage = 
"PiecewiseBeautify[piecewiseExpression] Rewrites the conditions in piecewiseExpression in a disjoint way";

PiecewiseBeautifyOperator::usage =
"PiecewiseBeautifyOperator[<||>][piecewiseExpression] is the same as PiecewiseBeautify[piecewiseExpression]"

ConditionalPiecewiseMap::usage = 
"ConditionalPiecewiseMap[function, piecewiseExpression] Takes a function that depends on two variables, the second being the condition, and maps through a conditional expression";

PiecewiseExpandAssociation::usage = 
"PiecewiseExpandAssociation[association] takes the association with possible piecewise values and
expands it as piecewise expression"

PiecewiseReplace::usage = 
"PiecewiseReplace[expression,rules] Replaces a piecewise expression using a piecewise rule";

PiecewiseLastCaseClean::usage = 
"PiecewiseLastCaseClean[expression] adds the True case as a pair. Here for debugging/development purposes. ";

PiecewiseListClean::usage = 
"PiecewiseListClean[list] takes a list or piecewise list and if any of the elements is $Failed, returns $Failed";

PiecewiseAssociationClean::usage = "PiecewiseAssociationClean[Association] takes 
an association or piecewise associations and if any of the Values is $Failed,
returns $Failed";

Kleisli::usage = "Kleisli[Operator] lets Operator handle Piecewise and $Failed expressions";

KleisliListable::usage = "KleisliListable[Operator] lets Operator handle Piecewise and 
$Failed expressions for listable functions";

KleisliTest::usage = "KleisliTest operator to handle the specific structure of tests"

Begin["`Private`"] (* Begin Private Context *) 

PiecewiseAssociationClean[assoc_] :=
  PiecewiseMap[
    If[Head[#] =!= Association, #,
        If[
     Or @@ (KeyValueMap[Function[{key, value}, value === $Failed], #]),
     $Failed,
     #]
    ]
   &, assoc
  ]//PiecewiseBeautify;

PiecewiseListClean[list_] :=
 PiecewiseMap[
  If[Head[#] =!= List, #,
    If[Or @@ (Function[z,z === $Failed] /@ #), $Failed, #]] &, list];

PiecewiseReplace[xp_, rules_] :=
 PiecewiseBeautify@PiecewiseMap[If[#[[1]]===$Failed||#[[2]]===$Failed,$Failed, #[[1]] /. #[[2]]] &, PiecewiseExpand[{xp, rules//PiecewiseBeautify}]];

(*Inputs the the default value in the Piecewise list: Piecewise[{{val1,cond1},{val2,cond2}},val] -> {{val1,cond1},{val2,cond2},{val, "no conditions"}}
If no value is given, the default value is 0.*)
PiecewiseLastCaseClean[xp_Piecewise] :=
	Module[{pxp = PiecewiseExpand @ xp}, 
		Append[pxp[[1]], {pxp[[2]], True}]
	];

PiecewiseMap[F_, XPO_] := 
With[{XP=PiecewiseExpand[XPO]},
Which[
	XP === $Failed, 
	$Failed,
    Head[XP] === Piecewise, 
		With[ {G = PiecewiseLastCaseClean[XP]},
			Piecewise[{
				If[ #[[1]] =!= $Failed,
					F[#[[1]]],
					$Failed
				], #[[2]]} & /@ G, 
				$Failed 
			]
		] // PiecewiseExpand,
	True, 
		F[XP]
]];

PiecewiseOperatorMap[Operator_, variables_, XPO_] := 
 With[{XP = PiecewiseExpand[XPO]},
  Which[
   XP === $Failed,
   $Failed,
   Head[XP] === Piecewise,
   With[{G = PiecewiseLastCaseClean[XP]},
    With[{qq = Reduce /@ MapThread[Simplify[! #1 && #2] &,
          {FoldList[Or, False, G[[All, 2]]][[;; -2]], G[[All, 2]]}]},
      Module[{gg},
       gg = Transpose[{G[[All, 1]], qq}];
       Piecewise[{If[#[[1]] =!= $Failed, 
            Operator[
              Append[variables, 
               "facts" -> 
                Lookup[variables, "facts", 
                  True] && #[[2]]]][#[[1]]], $Failed], #[[2]]} & /@ 
         gg, $Failed]]] // PiecewiseExpand],
   True,
   Operator[variables][XP]]]



ConditionalPiecewiseMap[F_,XP_] :=
Which[
	XP === $Failed, 
		$Failed,		
	Head[XP]=!=Piecewise,
		F[XP,True],	
	True,
		Module[ {qq, pp = PiecewiseLastCaseClean[XP]},
			qq = Reduce/@MapThread[Simplify[!#1&&#2]&, {FoldList[Or,False, pp[[All,2]]][[;;-2]],pp[[All,2]]}];
			Piecewise[{
				If[ #[[1]]=!=$Failed,
					F[#[[1]], #[[2]]],
					$Failed
				], #[[2]]}&/@({pp[[All,1]], qq}//Transpose), $Failed
			]
        ] // PiecewiseExpand//PiecewiseBeautify
]

Clear[PiecewiseBeautify];
Options[PiecewiseBeautify]={"domain"->Complex};


PiecewiseBeautify[P_,OptionsPattern[]] :=
    Which[
        Head[P] === Piecewise,
        With[ {pp = PiecewiseLastCaseClean[P]},
            Module[ {qq},
                qq = Reduce[#,OptionValue["domain"]]&/@MapThread[Simplify[!#1&&#2]&, {FoldList[Or,False, pp[[All,2]]][[;;-2]],pp[[All,2]]}];
                Piecewise[Select[Transpose[{pp[[All,1]], qq}], #[[1]]=!=$Failed &], $Failed]
            ]
        ],
        True,
        P
    ]

PiecewiseBeautifyOperator[variables_][xp_] := PiecewiseBeautify[xp,"domain"->Lookup[variables,"domain",Complex]];

PiecewiseEliminateEqualitiesOperator[variables_Association][xp_] :=
 If[Lookup[variables, "eliminateequalities", True],
  If[Head[xp] =!= Piecewise,
   xp,
   Module[{xpb, xpbl, xpblbc, xpblbcand, xpblbcandeq, facts, domain},
    facts = Lookup[variables, "facts", True];
    domain = Lookup[variables, "domain", Reals];
    xpb = PiecewiseBeautify[xp(*,"domain"->(*domain*)(*Complex*)*)];
    If[Head[xpb] =!= Piecewise,
     xpb,
     xpbl = Select[ Append[{xpb[[2]], Not[Or @@ ( xpb[[1, All, 2]])]}][First[xpb]], #[[1]] =!= $Failed &];
     xpblbc = Select[{#[[1]], BooleanConvert[Reduce[facts && #[[2]]], domain]} & /@ xpbl, #[[2]] =!= False &];
     xpblbcand = Union @@ 
        	(Function[case, If[Head[case[[2]]] === Or, List @@ ({case[[1]], #} & /@ case[[2]]) , {case}]] /@ xpblbc);
     xpblbcandeq = {#[[1]] /. Quiet@First@Solve[
        	Which[
        		Head[#[[2]]] === Equal, #[[2]], 
        		Head[#[[2]]] =!= And, True,
        		True, Select[#[[2]], Head[#] === Equal &]
        	]
        ], #[[2]]} & /@ xpblbcand;
        Piecewise[xpblbcandeq, $Failed]
    ]
   ]
  ], xp
 ]



PiecewiseSimplifyOperator[variables_Association][xp_] := 
  If[Head[xp] =!= Piecewise, 
   Assuming[Lookup[variables, "facts", True], Simplify[xp]], 
   Module[{xpr, xprb, facts, xprbl, 
     simplify = Lookup[variables, "simplify", Simplify]}, 
    xpr = PiecewiseEliminateEqualitiesOperator[variables][xp];
    xprb = PiecewiseBeautify[xpr];
    facts = Lookup[variables, "facts", True];
    If[Head[xprb] =!= Piecewise,
     xprb, 
     xprbl = 
      Select[
       Append[{xprb[[2]], Not[Or @@ (xprb[[1, All, 2]])]}][
        First[xprb]] , #[[1]] =!= $Failed &];
     Piecewise[{If[Head[#[[1]]] === Association, 
          AssociationMap[
           Function[ZZZ, 
            Assuming[facts && #[[2]], simplify[ZZZ]]], #[[1]]], 
          Assuming[facts && #[[2]], simplify[#[[1]]]]], #[[2]]} & /@ 
       xprbl, $Failed]]]];
       
PiecewiseSimplify = PiecewiseSimplifyOperator[Association[]];


PiecewiseFullSimplifyOperator[variables_] := 
 PiecewiseSimplifyOperator[Append[variables, "simplify" -> FullSimplify]]
  
PiecewiseFullSimplify = PiecewiseFullSimplifyOperator[<||>];

PiecewiseExpandAssociation[association_Association] :=
  PiecewiseMap[Association, PiecewiseExpand@Normal@association]//PiecewiseAssociationClean;
  
PiecewiseExpandAssociation[association_Piecewise] :=
   PiecewiseMap[PiecewiseExpandAssociation, association]//PiecewiseBeautify;  

PiecewiseExpandAssociation[$Failed]=$Failed;

PiecewiseExpandAssociation[z_]=z;

PiecewiseEqualOperator[variables_Association][xp1_, xp2_] :=
 Module[{xp},
  xp = PiecewiseBeautify[PiecewiseExpand[PiecewiseExpandAssociation/@{xp1, xp2}]];
  If[Head[xp] =!= Piecewise,
   Simplify[Equal @@ xp] === True,
   Module[{facts, domain, xprbl},
    facts = Lookup[variables, "facts", True];
    domain = Lookup[variables, "domain", Reals];
    xprbl = Select[Append[{xp[[2]], Not[Or @@ ( xp[[1, All, 2]])]}][First[xp]], #[[1]] =!= $Failed &];
    Reduce[
      And @@ (Implies[#[[2]] && facts, #[[1, 1]] == #[[1, 2]]] & /@ 
         xprbl), domain] === True
    ]
   ]
  ];

Kleisli[Op_][variables_Association][xp_] :=
  Which[
   xp === $Failed,
   $Failed,
   Head[xp] === Piecewise,
   PiecewiseOperatorMap[Kleisli[Op], variables, xp] // PiecewiseExpand,
   True,
   Op[variables][xp]
   ];

KleisliListable[Op_][variables_Association][xp_] :=
  Which[
   xp === $Failed,
   $Failed,
   Head[xp] === Piecewise,
   PiecewiseOperatorMap[KleisliListable[Op], variables, xp] // PiecewiseExpand,
   Head[xp]===List, 
   Map[KleisliListable[Op][variables], xp]//PiecewiseExpand//PiecewiseListClean,
   True,
   Op[variables][xp]
   ];
   
KleisliTest[test_][variables_, expression_, output_] :=
  Which[
   Head[expression] === Piecewise,
   True,
   Head[expression] === $Failed,
   output === $Failed,
   True,
   test[variables, expression, output]
   ];   
   
End[] (* End Private Context *)
(*EndPackage[]*)