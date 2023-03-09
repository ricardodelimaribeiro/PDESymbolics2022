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
"AutoReduceOperator[variables][polylist] returns the reduced polylist.";

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
  Module[{order, generators, MonList, rules}, 
   order = Lookup[variables, "ordering", "Lexicographic"];
   generators = 
    Lookup[variables, "generators", 
     InferGeneratorsOperator[variables][xp]];
   rules = # -> 1 & /@ generators;
   MonList = MonomialList[xp, generators, order];
   (*Print[MonList,rules];*)
   Piecewise[({#, (# /. rules) != 0} & /@ MonList)]//PiecewiseBeautify
   ];

LeadingTermOperator[vars_][xp_] := 
 KleisliListable[LeadingTerm][vars][xp] // PiecewiseBeautify;
 
Clear[LeadingCoefficientOperator];
LeadingCoefficient[variables_Association][xp_?NotPiecewise] := 
  Module[{order, generators, MonList, rules}, 
   order = Lookup[variables, "ordering", "Lexicographic"];
   generators = 
    Lookup[variables, "generators", 
     InferGeneratorsOperator[variables][xp]];
   rules = # -> 1 & /@ generators;
   MonList = MonomialList[xp, generators, order];
   Piecewise[({(# /. rules), (# /. rules) != 0} & /@ MonList),1]//PiecewiseBeautify
   ];

LeadingCoefficientOperator[vars_][xp_] := 
 KleisliListable[LeadingCoefficient][vars][xp] // PiecewiseBeautify

Division[a_?NotPiecewise,b_?NotPiecewise]:=
Which[a === $Failed|| b === $Failed,
	$Failed,
	a b === 0,
	0,
	True,
	a/b
];

PiecewiseDivision[a_,b_]:= PiecewiseExpand[Division[a,b]];

SPolynomialOperator[variables_][f_?NotPiecewise,
	g_?NotPiecewise] :=
	Which[f === 0 || g === 0,
		0,
		f === $Failed || g === $Failed,
		$Failed,
		True,
		With[{lf = LeadingTermOperator[variables][f],
			lg = LeadingTermOperator[variables][g]},
			
			Expand@PiecewiseEliminateEqualitiesOperator[variables]@PiecewiseExpand[PiecewisePolynomialLCM[lf,lg](PiecewiseDivision[f,lf] - PiecewiseDivision[g,lg])]//PiecewiseBeautify
			(*	PolynomialLCM[lf, lg] (f/lf - g/lg)*)
			]
		];

PiecewiseSPolynomialOperator[variables_][f_, g_] := 
 FixedPoint[PiecewiseExpand, 
   SPolynomialOperator[variables][f, g]] // Expand;

AutoReduceOperator[variables_][opolylist_] := 
 With[{generators = Lookup[variables, "generators", {}],facts = Lookup[variables,"facts",True]},
  Assuming[facts,DeleteDuplicates@FixedPoint[
   Function[polylist, 
    Select[
     Function[
       poly, (Last@
         PolynomialReduce[poly, Select[polylist, # =!= poly &], 
          generators])] /@ polylist, # =!= 0 &]], opolylist]]
          ]; 
         
End[]