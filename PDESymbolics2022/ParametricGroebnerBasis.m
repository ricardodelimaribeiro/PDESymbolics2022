(* ::Package:: *)

(* Wolfram Language package *)
InferGeneratorsOperator::usage =
"InferGeneratorsOperator[variables][xplist] infers the generators of xplist.";

PiecewisePolynomialLCM::usage =
"PiecewisePolynomialLCM[f, g] gives the polynomial Least Common Multiple of f and g.";

LeadingTermOperator::usage =
"LeadingTermOperator[variables][xp] returns a Piecewise expression with the leading term depending on the parameters. ";

LeadingCoefficientOperator::usage = 
"LeadingCoefficientOperator[variables][xp] returns a Piecewise expression with the leading term depending on the parameters. ";

PiecewiseSPolynomialOperator::usage =
"PiecewiseSPolynomialOperator[variables][f, g] returns the S-polynomial for f and g. If one of them is a Piecewise expression, it takes care of the cases.";

PiecewiseDivision::usage =
"PiecewiseDivision[a,b] takes care of $Failed and division by zero."

AutoReduceOperator::usage =
"AutoReduceOperator[variables][polylist] returns the reduced (smallest set generating the same ideal) polylist.";

PiecewisePolynomialReduceRemainderOperator::usage =
"PiecewisePolynomialReduceRemainderOperator[variables][p, polylist] returns a Piecewise remainder for the redeuctions.";
(*Debuging*)
SPolynomialOperator::usage="";
Begin["`Private`"]
InferGeneratorsOperator[variables_][xplist_List] :=
  With[{glc = First@GenericLinearCombinationOperator[variables][xplist]},
   InferGeneratorsOperator[variables][glc]
   ];
InferGeneratorsOperator[variables_Association][xp_] := 
  With[{indvars = Lookup[variables, "indVars", {}], 
    depvars = LexicographicSort[Lookup[variables, "depVars", {}]]},
    Reverse@
    DeleteDuplicates@
     Flatten[
      Join[ 
         Cases[xp, # @@ indvars, {0, Infinity}],(*I don't know why, 
         but the code didn't work without the levelspec*)
         
         Cases[xp, Derivative[__][#] @@ indvars, {0, Infinity}]] & /@ 
       depvars]
   ];


PiecewisePolynomialLCM[f_, g_] :=
 Module[{PLCM},
 	PLCM[$Failed,_]=$Failed;
 	PLCM[_,$Failed]=$Failed;
  PiecewiseExpand[PLCM[f, g]] /. PLCM -> PolynomialLCM
  ];
   
NotPiecewise[xp_] := Head[xp] =!= Piecewise;

LeadingTerm[variables_Association][xp_?NotPiecewise] := 
  Module[{order, generators, MonList, rules,facts},
  	facts = Lookup[variables,"facts",True]; 
   order = Lookup[variables, "ordering", "Lexicographic"];
   generators = 
    Lookup[variables, "generators", 
     InferGeneratorsOperator[variables][xp]];
   rules = # -> 1 & /@ generators;
   MonList = Assuming[facts,MonomialList[xp, generators, order]];
   (*Print[MonList,rules];*)
   Piecewise[({#, (# /. rules) != 0} & /@ MonList)]//PiecewiseBeautify
   ];

LeadingTermOperator[vars_][xp_] := 
 KleisliListable[LeadingTerm][vars][xp] (*// PiecewiseBeautify*);
 
Clear[LeadingCoefficientOperator];
LeadingCoefficient[variables_Association][xp_?NotPiecewise] := 
  Module[{order, generators, MonList, rules, facts},
   facts = Lookup[variables, "facts", True];
   If[facts===False,$Failed,
   	Assuming[facts,
   order = Lookup[variables, "ordering", "Lexicographic"];
   generators = 
    Lookup[variables, "generators", 
     InferGeneratorsOperator[variables][xp]];
   rules = # -> 1 & /@ generators;
   MonList = MonomialList[xp, generators, order];
   MonList = Simplify/@(MonList /.rules); 
   (*Print["coeff list: ", MonList, " facts: ", facts];*)
    PiecewiseBeautify@Simplify@Piecewise[({#, (*Reduce[*)facts&&(# != 0)(*]*)} & /@ MonList),1] (*this was giving problems for a parametric leading coefficient (constant in the generators)*)
   ]
   ]
   ];

LeadingCoefficientOperator[vars_][xp_] := 
 KleisliListable[LeadingCoefficient][vars][xp](*//PiecewiseBeautify
*)
Division[a_?NotPiecewise,b_?NotPiecewise]:=
If[a === $Failed|| b === $Failed,
	$Failed,
	(*a b === 0,
	0,*)
	(*True,*)
	a/b
];

PiecewiseDivision[a_,b_]:= PiecewiseExpand[Division[a,b]];

(*SPolynomialOperator[variables_][f_List]:=
Module[{pairs},
	pairs=Subsets[f,{2}];
	Print[pairs];
	SPolynomialOperator[variables][pairs]
];*)
Clear[SPolynomialOperator];
SPolynomialOperator[variables_][f_?NotPiecewise,
	g_?NotPiecewise] :=
	Which[f === 0 || g === 0,
		0,
		f === $Failed || g === $Failed,
		$Failed,
		True,
		With[{facts = Lookup[variables, "facts", True],
			lf = LeadingTermOperator[variables][f],
			lg = LeadingTermOperator[variables][g]},
			If[Head[lf]===Piecewise||Head[lg]===Piecewise,
				Print["
				**********************************************************
				Piecewise Leading Term!!! Trying to S-Poly:
				**********************************************************
				", f," and ",g];
				Assuming[facts,
			Expand@(*PiecewiseEliminateEqualitiesOperator[variables]@*)PiecewiseBeautify@PiecewiseExpand[PiecewisePolynomialLCM[lf,lg](PiecewiseDivision[f,lf] - PiecewiseDivision[g,lg])](*//PiecewiseBeautify*)
			],
			Assuming[facts, Expand[ReleaseHold[PolynomialLCM[lf, lg] Hold[(f/lf - g/lg)]]]]
			]	
			]
		];
Clear[PiecewiseSPolynomialOperator];
PiecewiseSPolynomialOperator[variables_][f_, g_] := 
 FixedPoint[PiecewiseExpand, 
   SPolynomialOperator[variables][f, g]] // Expand;

PiecewiseSPolynomialOperator[variables_][f_Piecewise] :=
((*Print[piecewise];*)
PiecewiseOperatorMap[PiecewiseSPolynomialOperator,variables, f]);

PiecewiseSPolynomialOperator[variables_][f_List] :=
Which[Length[f]===2,
	(*Print[2];*)
	{PiecewiseSPolynomialOperator[variables]@@f},
	Length[f]>2,
	Module[{pairs},
		pairs = Subsets[f,{2}];
		PiecewiseSPolynomialOperator[variables]@@@pairs
		
	],
		True,
		Print["PSPO with a longer list of size: "Length[f]];
		$Failed
];


Clear[AutoReduceStepOperator];
AutoReduceStepOperator[variables_][polylist_] := 
  Kleisli[AutoReduceStep][variables][polylist];
AutoReduceStep[variables_][polylist_List] :=
  
  With[{ps = sort@polylist},
   (*Print[polylist];*)
   Module[{unrefined},
    unrefined = 
     DeleteCases[0]@
      Table[
       PiecewisePolynomialReduceRemainderOperator[variables][ps[[i]], 
        ps[[;; i - 1]]], {i, 1, Length@ps}];
    PiecewiseDivision[unrefined, 
     LeadingCoefficientOperator[variables]@unrefined]
    ]
   ];
Clear[AutoReduceOperator];
AutoReduceOperator[variables_][polylist_] := 
  FixedPoint[AutoReduceStepOperator[variables], polylist] ;

PPRRO[$Failed, _] = $Failed;
PiecewisePolynomialReduceRemainderOperator[variables_][f_, g_List] := 
  Module[{preliminary, generators}, 
   generators = 
    Lookup[variables, "generators", 
     InferGeneratorsOperator[variables][Append[f][g]]]; 
   preliminary = PiecewiseExpand[PPRRO[f, g]]; 
   preliminary /. 
    PPRRO -> 
     Function[{poly, polylist}, 
      Last[
       PolynomialReduce[poly, DeleteCases[0]@polylist, generators]]]
   ];
(*AutoReduceOperator[variables_][opolylist_] := 
 With[{generators = Lookup[variables, "generators", {}],facts = Lookup[variables,"facts",True]},
  Assuming[facts,(*DeleteDuplicates@*)FixedPoint[
   Function[polylist, 
   	Module[{normalPolylist},
   	normalPolylist=polylist;(*MapThread[PiecewiseDivision,{polylist,LeadingCoefficientOperator[variables]/@polylist}]//Expand;*)
    Print[polylist];(*,normalPolylist];*)
    Select[
     Function[
       poly, (Last@
         PolynomialReduce[poly, Select[normalPolylist, # =!= poly &], 
          generators])] /@ normalPolylist, # =!= 0 &]]], opolylist]]
  ]; *)
         
End[]
