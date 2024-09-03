(* ::Package:: *)

(* Wolfram Language package *)
InferGeneratorsOperator::usage =
"InferGeneratorsOperator[variables][xplist] infers the generators of xplist. It works with \"continuous\" expressions.";

DiscreteInferGeneratorsOperator::usage = 
"DiscreteInferGeneratorsOperator[vars][xp] infers the generators of xp. It works with discrete expressions.";

PiecewisePolynomialLCM::usage =
"PiecewisePolynomialLCM[f, g] gives the polynomial Least Common Multiple of f and g.";

LeadingTermOperator::usage =
"LeadingTermOperator[variables][xp] returns a Piecewise expression with the leading term depending on the parameters. ";

LeadingCoefficientOperator::usage = 
"LeadingCoefficientOperator[variables][xp] returns a Piecewise expression with the leading term depending on the parameters. ";

PiecewiseSPolynomialOperator::usage =
"PiecewiseSPolynomialOperator[variables][f, g] returns the S-polynomial for f and g. If one of them is a Piecewise expression, it takes care of the cases.";

PiecewiseDivisionOperator::usage =
"PiecewiseDivisionOperator[a,b] takes care of $Failed and division by zero."

AutoReduceOperator::usage =
"AutoReduceOperator[variables][polylist] returns the reduced (smallest set generating the same ideal) polylist.";

PiecewisePolynomialRemainderOperator::usage =
"PiecewisePolynomialRemainderOperator[variables][p, polylist] returns a Piecewise remainder for the reductions.";

PiecewiseApplyConditionOperator::usage =
"PiecewiseApplyConditionOperator[variables][px] Simplifies the expressions with conditions as Assumptions";

ComprehensiveGroebnerSystemOperator::usage =
"ComprehensiveGroebnerSystemOperator[variables][preGrobner] returns a piecewise expression with groebner basis for each set of conditions.";

GrobOp::usage =
"GrobOp[variables][preGrobner] returns a piecewise expression with groebner basis for each set of conditions.";

GrobOpReduced::usage = "
GrobOpReduced[variables][preGrobner] returns a piecewise expression with reduced groebner basis for each set of conditions.";
(*backward compatibility*)
PiecewisePolynomialReduceRemainderOperator::usage =
"This is PiecewisePolynomialRemainderOperator"
(*Debuging*)
SPolynomialOperator::usage = "";

Division::usage = "";

NotPiecewise::usage = "";

MonicOperator::usage = "";

AllCasesOperator::usage = "";
Begin["`Private`"]

PiecewisePolynomialReduceRemainderOperator[variables] =
    PiecewisePolynomialRemainderOperator[variables]
    
    
InferGeneratorsOperator[variables_][xplist_List] :=
    With[ {glc = First@EchoLabel["InferGenerators: gLc"]@GenericLinearCombinationOperator[variables][EchoLabel["InferGenerators: input"]@xplist]},
        InferGeneratorsOperator[variables][glc]
    ]//QuietEcho;

InferGeneratorsOperator[variables_Association][xp_] :=
    Kleisli[InferGenerators][variables][xp];
   
InferGenerators[variables_Association][xp_] :=
    With[ {indvars = Lookup[variables, "indVars", {}], 
      depvars = LexicographicSort[Lookup[variables, "depVars", {}]]},
        DeleteDuplicates@
         Flatten[
          Reverse@Join[ 
             Cases[xp, # @@ indvars, {0, Infinity}],
             Cases[xp, Derivative[__][#] @@ indvars, {0, Infinity}]] & /@ 
           depvars]
    ];
    
DiscreteInferGeneratorsOperator[vars_][xp_] :=
    Module[ {generators, indvars, depvars},
        generators = PiecewiseExtractGeneratorsOperator[vars][xp];
        indvars = Lookup[variables, "indVars", {}];
        depvars = LexicographicSort[Lookup[variables, "depVars", {}]];
       (*TODO make this work for any number of independent variables, not just 2.*)
        SortBy[
         generators, {-Abs[#[[2]] /. indvars[[2]] -> 0], 
           Sign[#[[2]] /. 
             indvars[[2]] -> 0], -Abs[#[[1]] /.  indvars[[1]] -> 0], 
           Sign[#[[1]] /.  indvars[[1]] -> 0]} &]
    ]
 
 DiscreteInferGeneratorsOperator[variables_][xplist_List] :=
     With[ {glc = 
      First@GenericLinearCombinationOperator[variables][xplist]},
         DiscreteInferGeneratorsOperator[variables][glc]
     ];
     
(*TODO how is this behaving with the parameters?*)
PiecewisePolynomialLCM[f_, g_] :=
    Module[ {PLCM},
        PLCM[$Failed,_] = $Failed;
        PLCM[_,$Failed] = $Failed;
        PiecewiseExpand[PLCM[f, g]] /. PLCM -> PolynomialLCM
    ];
   
NotPiecewise[xp_] :=
    Head[xp] =!= Piecewise;

LeadingTerm[variables_Association][xp_?NotPiecewise] :=
    Module[ {order, generators, MonList, rules,facts},
        facts = Lookup[variables,"facts",True];
        order = Lookup[variables, "ordering", (*Degree*)Lexicographic];
        generators = 
         Lookup[variables, "generators", 
          InferGeneratorsOperator[variables][xp]];
        rules = # -> 1 & /@ generators;
        MonList = Assuming[facts,Simplify@MonomialList[xp, generators, order]];
        Assuming[facts,Simplify@Piecewise[({#, BooleanConvert(*@EchoLabel["LeadingTerm: will BollConv"]*)[facts&&((# /. rules) != 0)]} & /@ MonList)]]
    ];

LeadingTermOperator[vars_][xp_] :=
    KleisliListable[LeadingTerm][vars][xp](*// PiecewiseBeautify*);
 
Clear[LeadingCoefficientOperator];
LeadingCoefficient[variables_Association][xp_?NotPiecewise] :=
    Module[ {order, generators, MonList, rules, facts},
        facts = FullSimplify[EchoLabel["LeadingCoeff: facts"]@Lookup[variables, "facts", True]];
        If[ EchoLabel["LeadingCoeff: simplified facts"]@facts===False,
            $Failed,
            Assuming[facts,
            order = Lookup[variables, "ordering", (*Degree*)Lexicographic];
            generators = 
             Lookup[variables, "generators", 
              InferGeneratorsOperator[variables][xp]];
            rules = # -> 1 & /@ generators;
            MonList = Assuming[facts,Simplify@MonomialList[xp, generators, order]];
            MonList = EchoLabel["LeadingCoeff:MonList"]@(Simplify/@(MonList /.rules));
            Assuming[facts,Simplify@Piecewise[({#, BooleanConvert@EchoLabel["LeadingCoeff: will BollConv"][facts&&(# != 0)]} & /@ MonList),1]] 
            ]
        ]
    ];

LeadingCoefficientOperator[vars_][xp_] :=
    KleisliListable[LeadingCoefficient][vars][xp]//QuietEcho

Division[variables_][a_?NotPiecewise,b_?NotPiecewise] :=
    If[ a === $Failed|| b === $Failed,
        $Failed,
        If[ Head[a]===List,
            MapThread[Division[variables],{a,b}],
            Module[ {pars = Lookup[variables,"pars",{}],except = Variables[b],q,r,
                generators = Lookup[variables,"generators",InferGeneratorsOperator[variables][{a,b}]]},
                {{q},r} = PolynomialReduce[a,{b},Complement[pars,except]];
                EchoLabel["Division: total"]@Total[Simplify[MonomialList[q+r/b,generators]]]
            (*Module[ {pars = Lookup[variables,"pars",{}],except = Variables[b],q,r},
                {{q},r} = PolynomialReduce[a,{b},Complement[pars,except]];
                q+r/b*)
            ]
        ]
    ];

PiecewiseDivisionOperator[variables_][a_,b_] :=
    (*EchoLabel["PDO: division b4 beautify"]@*)
    EchoLabel["PDO: division expanded"][PiecewiseExpand@(*EchoLabel["PDO: unexpanded division"]@*)Division[variables][a,b]]//PiecewiseBeautifyOperator[variables];

Clear[SPolynomialOperator];
SPolynomialOperator[variables_][f_?NotPiecewise,
    g_?NotPiecewise] :=
    Which[f === 0 || g === 0,
        0,
        f === $Failed || g === $Failed,
        $Failed,
        True,
        With[ {facts = Lookup[variables, "facts", True],
            lf = LeadingTermOperator[variables][f],
            lg = LeadingTermOperator[variables][g]},
            If[ Head[lf]===Piecewise||Head[lg]===Piecewise,
                Print["
				**********************************************************
				Piecewise Leading Term!!! Trying to S-Poly:
				**********************************************************
				", f," and ",g," lf ",lf, " lg ",lg, " facts ",facts];
                Assuming[facts,
                Expand@PiecewiseApplyConditionOperator[variables]@PiecewiseBeautifyOperator[variables]@
                PiecewiseExpand[PiecewisePolynomialLCM[lf,lg](PiecewiseDivisionOperator[variables][f,lf] - PiecewiseDivisionOperator[variables][g,lg])]
                ],
                Assuming[facts, Expand[ReleaseHold[PolynomialLCM[lf, lg] Hold[(f/lf - g/lg)]]]]
            ]
        ]
        ];
        
Clear[PiecewiseSPolynomialOperator];
PiecewiseSPolynomialOperator[variables_][f_, g_] :=
    FixedPoint[PiecewiseExpand, 
      SPolynomialOperator[variables][f, g]] // Expand;
      
PiecewiseSPolynomialOperator[_][$Failed] = $Failed;

PiecewiseSPolynomialOperator[variables_][f_Piecewise] :=
    ((*Print[piecewise];*)
    PiecewiseOperatorMap[PiecewiseSPolynomialOperator,variables, f]);

PiecewiseSPolynomialOperator[variables_][f_List] :=
    Which[
        Length[f]===2,
        (*Print[2];*)
        {PiecewiseSPolynomialOperator[variables]@@f},
        Length[f]>2,
        Module[ {pairs},
            pairs = Subsets[f,{2}];
            PiecewiseSPolynomialOperator[variables]@@@pairs
        ],
            True,
            (*Print["PSPO with a list of size: ",Length[f], " and the list is: ",f];*)
            {0}
    ];


Clear[AutoReduceStepOperator];
AutoReduceStepOperator[variables_][polylist_] :=
    Kleisli[AutoReduceStep][variables][polylist];

AutoReduceStep[variables_][polylist_List] :=
    Module[ {generators},
        generators = 
         EchoLabel["AutoReduceStep: generators"]@Lookup[variables, "generators", 
          InferGeneratorsOperator[variables][EchoLabel["AutoReduceStep: input"]@polylist]];
        With[ {ps = 
           EchoLabel["AutoReduceStep: ps"]@ReverseSortBy[First[MonomialList[#, generators]] &]@polylist},
            Module[ {unrefined},
                unrefined = 
                  Table[
                   PiecewisePolynomialRemainderOperator[Append["generators"->generators]@variables][ps[[i]],
                     ps[[i + 1 ;;]]], {i, 1, Length@ps}];
                unrefined = DeleteCases[0]@EchoLabel["AutoReduceStep: unrefined"]@unrefined;
                PiecewiseDivisionOperator[variables][unrefined, 
                 LeadingCoefficientOperator[variables]@unrefined]
            ]
        ]
    ];
   
Clear[AutoReduceOperator];
AutoReduceOperator[variables_][polylist_] :=
    FixedPoint[AutoReduceStepOperator[variables], AllCasesOperator[variables]@polylist] //PiecewiseApplyConditionOperator[variables];


PPRRO[$Failed, _] = $Failed;
PiecewisePolynomialRemainderOperator[variables_][f_, g_Piecewise] :=
    PiecewiseMap[PiecewisePolynomialRemainderOperator[variables][f, #]&,g]

PiecewisePolynomialRemainderOperator[variables_][f_, g_List] :=
    Module[ {preliminary, generators},
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

SplitOr[xp_, cond_] :=
    {xp, cond};

SplitOr[xp_, cond_Or] :=
    Sequence @@ ({xp, #} & /@ cond);

   
PiecewiseApplyConditionOperator[variables_][px_] :=
    px;

PiecewiseApplyConditionOperator[variables_][px_List] :=
    PiecewiseApplyConditionOperator[variables] /@ px;

PiecewiseApplyConditionOperator[variables_][px_Piecewise] :=
    Module[ {facts, cleanList, newPx = EchoLabel["PACO: input"]@px, generators},
        facts = Lookup[variables, "facts", True];
        If[ Reduce[facts] === False,
            $Failed,
            newPx = EchoLabel["PACO: newPx"][
             SplitOr @@@ 
              PiecewiseLastCaseClean[
               (*EchoLabel["PACO: first beautify"]@*)PiecewiseBeautifyOperator[variables][px]]];
            generators = (*EchoLabel["PACO: generators"]@*) Lookup[variables, "generators", InferGeneratorsOperator[variables][Piecewise@newPx]];
            (*If[ AnyTrue[First@newPx,Head[#]===List&],
                (*Print["1"];*)
                cleanList = Function[dd,
                Assuming[dd[[2]], {(*EchoLabel["PACO: simplifyed this"]@*)
                    If[dd[[1]]===$Failed,{$Failed,dd[[2]]},{Total@Expand@Simplify@MonomialList[#,generators]&/@dd[[1,1]],dd[[1,2]]}], dd[[2]]}]] /@ newPx,
                (*Print["2"];*)
                cleanList = Function[dd,
                 Assuming[dd[[2]], {Total@Expand@Simplify@MonomialList[(*EchoLabel["PACO: simplifying that"]@*)dd[[1]],generators], dd[[2]]}]] /@ newPx
            ];*)
            If[ AnyTrue[First@newPx,Head[#]===List&],
                cleanList = Function[dd,
                (*Print["list: ",dd, facts];*)
                Assuming[dd[[2]], {Simplify[dd[[1]]], dd[[2]]}]] /@ newPx,
                cleanList = Function[dd,
                 (*Print["just piecewise: ",dd, facts];*)
                 Assuming[dd[[2]], {Total@Simplify@MonomialList[dd[[1]],generators], dd[[2]]}]] /@ newPx
            ];
            EchoLabel["PACO: output"][(*EchoLabel["PACO: before second beautify"]@*)(Piecewise[cleanList])//PiecewiseBeautifyOperator[variables]]
        ]
    ];
(*Clear[PiecewiseApplyConditionOperator];
PiecewiseApplyConditionOperator[variables_][px_] := px*)
 
   
Clear[GrobOp];

ComprehensiveGroebnerSystemOperator[variables_][ideal_] :=
    Kleisli[GrobOpReduced][variables][ideal]//PiecewiseBeautifyOperator[variables];

hasFailed[x_] :=
    MemberQ[$Failed][x];

hasZero[x_] :=
    MemberQ[0][x];

hasOne[x_] :=
    MemberQ[1][x];

GrobOp[variables_][{x_List, y_List}] :=
    GrobOp[variables][x, y];

GrobOp[variables_][{}] = {};

GrobOp[variables_][_, _?hasFailed] :=
    $Failed;

GrobOp[variables_][_, $Failed] :=
    $Failed;

GrobOp[variables_][_?hasFailed, _] :=
    $Failed;

GrobOp[variables_][$Failed, _] :=
    $Failed;

GrobOp[variables_][$Failed] :=
    $Failed;

GrobOp[variables_][x_?hasZero] :=
    GrobOp[variables][DeleteCases[0][x]];

GrobOp[variables_][x_?hasZero, y_] :=
    GrobOp[variables][DeleteCases[0][x], y];

GrobOp[variables_][x_, y_?hasZero] :=
    GrobOp[variables][x, DeleteCases[0][y]];

GrobOp[variables_][_, _?hasOne] :=
    {1};

GrobOp[variables_][_?hasOne, _] :=
    {1};

GrobOp[variables_][_?hasOne] :=
    {1};

GrobOp[variables_][grobner_List, {}] :=
    Module[ {facts},
        facts = Simplify@Lookup[variables, "facts", True];
        If[ facts===False,
            $Failed,
            grobner
        ]
    ];

GrobOpReduced[variables_][grobner_List] :=
    Module[ {facts},
        facts = Simplify@Lookup[variables, "facts", True];
        (*If[ facts===False,
            $Failed,
            AutoReduceOperator[variables][GrobOp[variables]@grobner] // PiecewiseExpand
        ]//PiecewiseApplyConditionOperator[variables]*)
        Which[ facts===False,
            $Failed,
            (*Lookup[variables,"pars",{}]==={}||*)FreeQQ[grobner,Lookup[variables,"pars",{}]],
            GroebnerBasis[Echo@grobner, Echo@Lookup[variables, "generators",{}], MonomialOrder->Echo@Lookup[variables, "ordering", (*Degree*)Lexicographic]],
            True,
            AutoReduceOperator[variables][GrobOp[variables]@grobner] // PiecewiseExpand //PiecewiseApplyConditionOperator[variables]
        ]
    ];

GrobOp[variables_][preGrobner_List, sPolynomials_List] :=
    Module[ {facts, fstSPoly, newPreGrobner = preGrobner, reduced, newArgs, 
      newSPolynomials},
      (*Print["in the second part"];*)
        facts = Reduce@Lookup[variables, "facts", True];
        If[ Reduce[facts] === False,
            $Failed,
            fstSPoly = First@sPolynomials;
            fstSPoly = EchoLabel["GrobOp2: monic S poly"]@MonicOperator[variables][fstSPoly];
            reduced = EchoLabel["GrobOp2: S poly reduced"]@PiecewisePolynomialRemainderOperator[variables][fstSPoly, newPreGrobner];
            reduced = EchoLabel["GrobOp2: monic S poly reduced"]@MonicOperator[variables][reduced];
            fstSPoly = Simplify[First@sPolynomials];
            (*lc = LeadingCoefficientOperator[variables][fstSPoly];*)
            (*fstSPoly = (*PiecewiseEliminateEqualitiesOperator[variables]@*)
             PiecewiseDivisionOperator[variables][fstSPoly, lc] // Expand;*)
            (*reduced = 
             PiecewisePolynomialRemainderOperator[variables][fstSPoly, 
              newPreGrobner];*)
            (*lc = LeadingCoefficientOperator[variables][reduced];*)
            (*reduced = PiecewiseDivisionOperator[variables][reduced, lc];*)
            (*generators = InferGeneratorsOperator[variables][reduced];
            reduced = 
             PiecewiseMap[Total@Simplify@MonomialList[#, generators] & , 
               reduced] // PiecewiseBeautifyOperator[variables];*)
            reduced = EchoLabel["GrobOp2: Apply! monic S poly reduced"]@PiecewiseApplyConditionOperator[variables][reduced];
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
            PiecewiseOperatorMap[GrobOp, variables, newArgs]
        ]
    ];

GrobOp[variables_][preGrobner_List] :=
    Module[ {newPreGrobner, sPolynomials, newArgs, facts ,newVariables, generators,reduce},
        facts = Reduce@Lookup[variables, "facts", True];
        reduce = Lookup[variables, "reduce", Resolve];
        If[ Lookup[variables,"VarDOperator",VarDOperator] === VarDOperator,
            generators = Lookup[variables, "generators", InferGeneratorsOperator[variables][preGrobner]],
            (*if "VarDOperator" is DVarDOperator*)
            generators = Lookup[variables, "generators", DiscreteInferGeneratorsOperator[variables][preGrobner]]
        ];
        newVariables = Append[{"facts"->facts,"reduce"->reduce,"generators"->generators}]@variables;
        If[ facts === False,
            $Failed,
            newPreGrobner = DeleteCases[0]@EchoLabel["simplified"]@Simplify[preGrobner,facts];
            newPreGrobner = EchoLabel["monic preGrobner"]@ MonicOperator[newVariables][newPreGrobner];
            sPolynomials = PiecewiseSPolynomialOperator[newVariables][newPreGrobner];
            newArgs = {newPreGrobner, sPolynomials} // PiecewiseExpand // PiecewiseApplyConditionOperator[newVariables];
            PiecewiseOperatorMap[GrobOp, newVariables, newArgs] //PiecewiseExpand// PiecewiseBeautifyOperator[newVariables]
        ]
    (*Which[ facts === False,
            $Failed,
            Lookup[variables,"pars",{}]==={},
            Print["not parametric"];
            Echo@GroebnerBasis[preGrobner, generators, MonomialOrder->Lookup[variables, "ordering", "Lexicographic"]],
            True,
            newPreGrobner = DeleteCases[0]@EchoLabel["simplified"]@Simplify[preGrobner,facts];
            newPreGrobner = EchoLabel["monic preGrobner"]@ MonicOperator[newVariables][newPreGrobner];
            sPolynomials = PiecewiseSPolynomialOperator[newVariables][newPreGrobner];
            newArgs = {newPreGrobner, sPolynomials} // PiecewiseExpand // PiecewiseApplyConditionOperator[newVariables];
            PiecewiseOperatorMap[GrobOp, newVariables, newArgs] //PiecewiseExpand// PiecewiseBeautifyOperator[newVariables]
        ]*)
    ];

AllCasesOperator[variables_][xp_] :=
    KleisliListable[AllCases][variables][xp] // PiecewiseApplyConditionOperator[variables];

AllCases[variables_][xp_] :=
    Module[ {generators,MonList,lt},
        generators = Lookup[variables,"generators",InferGeneratorsOperator[variables][xp]];
        MonList = (*EchoLabel["AllCases: MonList"]@*) MonomialList[xp,generators];
        lt = (*EchoLabel["AllCases: leading terms"]@*) (LeadingTermOperator[variables] /@ MonList);
        EchoLabel["AllCases: output"]@PiecewiseExpand@Total[lt]
    ]//QuietEcho;

MonicOperator[variables_][0] = 0;

MonicOperator[variables_][xp_] :=
    Module[ {allCases,lc, divided,generators},
        generators = Lookup[variables,"generators",InferGeneratorsOperator[variables][xp]];
        allCases = EchoLabel["Monic: ac"]@AllCasesOperator[variables][xp];
        lc = EchoLabel["Monic: lc"]@LeadingCoefficientOperator[variables][allCases];
        divided = (*EchoLabel["Monic: divided"]@*) PiecewiseDivisionOperator[variables][allCases,lc]//PiecewiseApplyConditionOperator[variables];
        (*divided=PiecewiseMap[Simplify@MonomialList[#, generators] &,divided];
        Print["divided: simplified: ",divided];*)
        (*Which[Head[divided]===Piecewise,
            divided = PiecewiseMap[Total/@ # &,divided];
            Print["piecewise divided: ", divided],
            DeleteDuplicates[Head /@ divided]==={List},
            divided = Total/@ divided;
            Print["list of lists: ", divided],
            True,
            divided = Total@divided
        ];*)
        (*Print["divided: simplified again: ",divided];*)
        EchoLabel["Monic: output"]@divided
    ](*//QuietEcho*);
           
End[]
