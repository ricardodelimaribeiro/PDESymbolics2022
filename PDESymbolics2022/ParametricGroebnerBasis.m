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

PiecewiseApplyConditionOperator::usage =
"PiecewiseApplyConditionOperator[variables][px] Simplifies the expressions with conditions as Assumptions";

GrobOp::usage =
"GrobOp[variables][preGrobner] returns a piecewise expression with groebner basis for each set of conditions.";

(*Debuging*)
SPolynomialOperator::usage="";
Begin["`Private`"]
InferGeneratorsOperator[variables_][xplist_List] :=
  With[{glc = First@GenericLinearCombinationOperator[variables][xplist]},
   InferGeneratorsOperator[variables][glc]
   ];

InferGeneratorsOperator[variables_Association][xp_] := Kleisli[InferGenerators][variables][xp];
   
InferGenerators[variables_Association][xp_] := 
  With[{indvars = Lookup[variables, "indVars", {}], 
    depvars = LexicographicSort[Lookup[variables, "depVars", {}]]},
    Reverse@
    DeleteDuplicates@
     Flatten[
      Join[ 
         Cases[xp, # @@ indvars, {0, Infinity}],(*I don't know why, 
         but the code didn't work without the levelspec*)
         (*{# @@ indvars},*)
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
   Piecewise[({#, (# /. rules) != 0} & /@ MonList)]//PiecewiseBeautifyOperator[variables]
   ];

LeadingTermOperator[vars_][xp_] := 
 KleisliListable[LeadingTerm][vars][xp] (*// PiecewiseBeautify*);
 
Clear[LeadingCoefficientOperator];
LeadingCoefficient[variables_Association][xp_?NotPiecewise] := 
  Module[{order, generators, MonList, rules, facts},
   facts = Lookup[variables, "facts", True];
   If[facts===False,$Failed,
   	Assuming[facts,
   		(*Print["coeff facts:, "facts];*)
   order = Lookup[variables, "ordering", "Lexicographic"];
   generators = 
    Lookup[variables, "generators", 
     InferGeneratorsOperator[variables][xp]];
   rules = # -> 1 & /@ generators;
   MonList = MonomialList[xp, generators, order];
   MonList = Simplify/@(MonList /.rules); 
   (*Print["coeff list: ", MonList, " facts: ", facts];*)
    PiecewiseBeautify@(*Simplify@*)Piecewise[({#, (*Reduce[*)facts&&(# != 0)(*]*)} & /@ MonList),1] (*this was giving problems for a parametric leading coefficient (constant in the generators)*)
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
			Expand@PiecewiseApplyConditionOperator[variables]@PiecewiseBeautifyOperator[variables]@PiecewiseExpand[PiecewisePolynomialLCM[lf,lg](PiecewiseDivision[f,lf] - PiecewiseDivision[g,lg])]
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
  Module[{generators},
   generators = 
    Lookup[variables, "generators", 
     InferGeneratorsOperator[variables][polylist]];
   With[{ps = 
      ReverseSortBy[First[MonomialList[#, generators]] &]@polylist},
    Module[{unrefined},
     unrefined = 
      DeleteCases[0]@
       Table[
        PiecewisePolynomialReduceRemainderOperator[variables][ps[[i]],
          ps[[i + 1 ;;]]], {i, 1, Length@ps}];
     PiecewiseDivision[unrefined, 
      LeadingCoefficientOperator[variables]@unrefined]
     ]
    ]
   ];
   
Clear[AutoReduceOperator];
AutoReduceOperator[variables_][polylist_] := 
  FixedPoint[AutoReduceStepOperator[variables], polylist] //PiecewiseApplyConditionOperator[variables];


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
   
Clear[SplitOr];

SplitOr[xp_, cond_] := {xp, cond};

SplitOr[xp_, cond_Or] := Sequence @@ ({xp, #} & /@ cond);

   
PiecewiseApplyConditionOperator[variables_][px_] := px;

PiecewiseApplyConditionOperator[variables_][px_List] :=
  PiecewiseApplyConditionOperator[variables] /@ px;

PiecewiseApplyConditionOperator[variables_][px_Piecewise] :=
  Module[{facts, cleanList, newPx},
   facts = Lookup[variables, "facts", True];
   If[Reduce[facts] === False,
    $Failed,
    newPx = 
     SplitOr @@@ 
      PiecewiseLastCaseClean[
       px];(*need to split the Ors*)
    (*Print[newPx];*)
    
    cleanList = Function[dd,
       Assuming[dd[[2]], {Expand@Simplify[dd[[1]]], dd[[2]]}]] /@ 
      newPx;
    Piecewise[cleanList] // PiecewiseBeautifyOperator[variables]
    ]
   ];
   
Clear[GrobOp];

hasFailed[x_] := MemberQ[$Failed][x];

hasZero[x_] := MemberQ[0][x];

hasOne[x_] := MemberQ[1][x];

GrobOp[variables_][{x_List, y_List}] := GrobOp[variables][x, y];

GrobOp[variables_][{}] = {};

GrobOp[variables_][_, _?hasFailed] := (Print["checking..."]; $Failed);

GrobOp[variables_][_, $Failed] := (Print["checking... 2"]; $Failed);

GrobOp[variables_][_?hasFailed, _] := (Print[
    "checking... 3"]; $Failed);

GrobOp[variables_][$Failed, _] := (Print["checking... 4"]; $Failed);

GrobOp[variables_][$Failed] := $Failed;

GrobOp[variables_][x_?hasZero, y_] := 
  GrobOp[variables][DeleteCases[0][x], y];

GrobOp[variables_][x_, y_?hasZero] := 
  GrobOp[variables][x, DeleteCases[0][y]];

GrobOp[variables_][_, _?hasOne] := {1};

GrobOp[variables_][_?hasOne, _] := {1};

GrobOp[variables_][_?hasOne] := {1};

GrobOp[variables_][grobner_List, {}] := Module[{facts},
   facts = Simplify@Lookup[variables, "facts", True];
   If[facts===False,
   	$Failed,
(*   Print["final: facts: ", facts, "\tfinal: expanded: ", grobner];*)   AutoReduceOperator[variables][grobner]
   ]
   ];


GrobOp[variables_][preGrobner_List, sPolynomials_List] :=
  
  Module[{facts, fstSPoly, lc, newPreGrobner, reduced, newArgs, 
    newSPolynomials, generators(*,depVars,indVars,vars*)},
   facts = Simplify@Lookup[variables, "facts", True]
    (*Reduce[Lookup[variables, "facts", True], 
     Lookup[variables, "domain", Complex]]*);
   If[facts === False,
    $Failed,
    newPreGrobner = Simplify@preGrobner;
    
    fstSPoly = Simplify[First@sPolynomials];
   	
   	lc = LeadingCoefficientOperator[variables][fstSPoly];
    fstSPoly = (*PiecewiseEliminateEqualitiesOperator[variables]@*)
     PiecewiseDivision[fstSPoly, lc] // Expand;
    reduced = 
     PiecewisePolynomialReduceRemainderOperator[variables][fstSPoly, 
      newPreGrobner];
    lc = LeadingCoefficientOperator[variables][reduced];
    reduced = PiecewiseDivision[reduced, lc];
    
    generators = InferGeneratorsOperator[variables][reduced];
    reduced = 
     PiecewiseMap[Total@Simplify@MonomialList[#, generators] & , 
       reduced] // PiecewiseBeautifyOperator[variables];
    reduced = PiecewiseApplyConditionOperator[variables][reduced];
    Which[Head[reduced] === Piecewise,
     (*replace the first S-polynomial by the cases of the S-
     polynomial.*)
     newArgs = PiecewiseMap[ ({newPreGrobner,
           DeleteDuplicates[Prepend[#][Rest@sPolynomials]]} // 
          Expand) &
       , reduced],
     reduced === 0,
     (*this is the most effective choice!*)
     
     newArgs = {newPreGrobner, Rest[sPolynomials]},
     True,
     newSPolynomials = 
      PiecewiseSPolynomialOperator[variables][reduced, #] & /@ 
       newPreGrobner;
     (*Using Union to DeleteDuplicates! is there a better choice?*)
  
        newSPolynomials = 
      PiecewiseMap[Simplify[Expand@(*Full*)Simplify@#] &, 
       Union[Rest@sPolynomials, newSPolynomials] // PiecewiseExpand];
     newArgs = {Append[reduced][newPreGrobner], newSPolynomials} // 
        PiecewiseExpand // PiecewiseListClean
     ];
    newArgs = PiecewiseApplyConditionOperator[variables][newArgs];
    PiecewiseOperatorMap[GrobO, variables, newArgs]
    ]
   ];

GrobOp[variables_][preGrobner_List] :=
  Module[{lc, newPreGrobner, sPolynomials, newArgs, facts, 
    generators},
   facts = Lookup[variables, "facts", True];
   If[facts === False,
    $Failed,
    Assuming[facts,
    generators = 
     Lookup[variables, "generators", 
      InferGeneratorsOperator[variables][preGrobner]];
    lc = LeadingCoefficientOperator[variables] /@ preGrobner;
    newPreGrobner = 
     PiecewiseBeautifyOperator[variables] /@ 
      MapThread[PiecewiseDivision, {preGrobner, lc}];
    newPreGrobner = 
     PiecewiseApplyConditionOperator[variables] /@ newPreGrobner;
    sPolynomials = 
     PiecewiseSPolynomialOperator[variables][newPreGrobner];
    lc = LeadingCoefficientOperator[variables] /@ sPolynomials;
    sPolynomials = MapThread[PiecewiseDivision, {sPolynomials, lc}];
    sPolynomials = 
     PiecewiseApplyConditionOperator[variables]@sPolynomials;
    newArgs = {newPreGrobner, sPolynomials} // PiecewiseExpand // 
      PiecewiseApplyConditionOperator[variables];
    PiecewiseOperatorMap[GrobO, variables, newArgs] // 
     PiecewiseBeautifyOperator[variables]
    ]
    ]
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
