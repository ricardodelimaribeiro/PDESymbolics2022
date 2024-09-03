(* Wolfram Language Package *)
(*BeginPackage["PDESymbolics2020`Discrete`"]*)
RangeSchemeTranslationsOperator::usage =
"RangeSchemeTranslationsOperator[variables][masterstencil, stencil] returns all 
translations of stencil that belong to (default) or intersect (\"intersect\"-> True) the numerical hull (needs proper definition) of masterstencil";

DiscreteConservedQOperator::usage =
"DiscreteConservedQOperator[variables][expression] returns True if a quantity is conserved in time or False otherwise. It needs a righthandside (\"rhs\"->{...})
or a scheme (\"scheme\"->{...}) under which it can check conservation.";    

VariationalTimeDifferenceOperator::usage =
"VariationalTimeDifferenceOperator[variables][expression] builds the time difference of the expression and tries to reduce/simplify it
using the given righthandside or scheme. Then calculates the variational derivative of the reduced time difference (and tries to reduce this again if there is a scheme given).";

VariationalTimeDifference::usage = "debuging ..."

ReduceModSchemeOperator::usage = 
"ReduceModSchemeOperator[variables][expression] takes an expression and a scheme that is equal to zero and reduces the expression using the 
Groebner Basis of the scheme";

TimeDifferenceOperator::usage = 
"TimeDifferenceOperator[variables][expression] builds the time difference of the expression and reduces/simplifies it using the righthandside
or the scheme";

EliminationListOperator::usage =
"EliminationListOperator[variables][expression] is here for Unit Test reasons.";

TimeOrderedQOperator::usage = 
"TimeOrderedQOperator[variables][x, y] is here for Unit Test reasons.";

PiecewiseExtractGeneratorsOperator::usage =
   "PiecewiseExtractGeneratorsOperator[variables][expression] extracts all generators from a piecewise expression";

FindDiscreteConservedQuantityOperator::usage = 
    "FindDiscreteConservedQuantityOperator[variables][<||>] finds the discrete conserved quantities up to degree 2 for the given rhs";

FindDiscreteConservedQuantityBasisOperator::usage =
    "FindDiscreteConservedQuantityBasisOperator[variables][<|\"degree\"->degree,\"generators\"->generators|>] finds a monomial basis for conserved quantities made from the generators up to the total degree";


(* debug *)
(*TODO write usage for this function*)
VariableEliminationOperator::usage =
    "VariableEliminationOperator[variables}[] returns...";

ImplicitVariationalTimeDifferenceOperator::usage =
"ImplicitVariationalTimeDifferenceOperator for debugging";



Begin["`Private`"] (* Begin Private Context *) 

RangeSchemeTranslationsOperator[variables_Association][masterstencil_,stencil_] :=
    Which[ 
     masterstencil === $Failed || stencil === $Failed, 
     $Failed,
     Head[stencil] === Piecewise,
     PiecewiseOperatorMap[RangeSchemeTranslationsOperator, variables, 
      masterstencil, stencil],
     Head[stencil] === List,
     RangeSchemeTranslationsOperator[variables][masterstencil, #] & /@ 
        stencil // PiecewiseExpand // PiecewiseListClean, 
     True,
     Module[ {sten = EchoLabel["RangeSchemeTranslationsOperator: stencil"]@stencil, masten = EchoLabel["RangeSchemeTranslationsOperator: master stencil"]@masterstencil, stenkeys, mastenkeys, rangelist, stencillist, translist},
         stenkeys = EchoLabel["RangeSchemeTranslationsOperator: stenkeys"]@Select[sten, (# // Flatten) === {} &] // Keys;
         sten = EchoLabel["RangeSchemeTranslationsOperator: sten"]@KeyDrop[sten, stenkeys];
         mastenkeys = Select[masten, (# // Flatten) === {} &] // Keys;
         masten = EchoLabel["RangeSchemeTranslationsOperator: masten"]@KeyDrop[masten, mastenkeys];
         If[ sten === Association[] || masten === Association[] || !SubsetQ[Keys[masten], Keys[sten]],
          (*TODO include something here: it may be good to include translate by the stencil of the expression. 
          My understanding now is that we only need the 'elimination' orders if we don't have enough translations of the scheme.
          But is it a good tradeoff in terms of time? 
          GB of translations may take longer than looking for a 'good' GB in a differente variable order.
           *)
             {},
             rangelist =  EchoLabel["RangeSchemeTranslationsOperator: rangelist"][
              Association @@ 
               Map[# -> Transpose[{Min /@ Transpose[masten[#]], Max /@ Transpose[masten[#]]}] &, Keys[sten]]];
             stencillist = EchoLabel["RangeSchemeTranslationsOperator: stencillist"][
              Association @@ 
               Map[# -> Transpose[{Min /@ Transpose[sten[#]], Max /@ Transpose[sten[#]]}] &, Keys[sten]]];
             rangelist = EchoLabel["RangeSchemeTranslationsOperator: rangelist"]@(rangelist[#] & /@ Keys[sten]);
             stencillist = EchoLabel["RangeSchemeTranslationsOperator: stencillist"]@(stencillist[#] & /@ Keys[sten]);
             EchoLabel["RangeSchemeTranslationsOperator: translist"]@If[ Lookup[variables, "intersect", False],
                                                                         translist = 
                                                                          MapThread[
                                                                           MapThread[{#1[[1]] - #2[[2]], #1[[2]] - #2[[1]]} &, {#1, #2}] &, {rangelist, stencillist}],
                                                                         translist = (rangelist - Map[Reverse,stencillist,{2}])
                                                                     ];
             translist = EchoLabel["RangeSchemeTranslationsOperator: new translist"][Map[Table[k, {k, #[[1]], #[[2]], 1}] &, translist, {2}]];
             translist = MapThread[Intersection, translist] // Tuples
         ]
     ]
    ];
  
HeaderOperator[Op_][variables_Association][expression_] :=
    Which[
     expression === $Failed,
     $Failed,
     Head[expression] === Piecewise,
     PiecewiseOperatorMap[HeaderOperator[Op], variables, expression] // PiecewiseExpandAssociation,
     Head[expression] =!= Association,
     Module[ {exp},
         exp = Association["exp" -> expression];
         HeaderOperator[Op][variables][exp]
     ],
     True,(*Head[expression] === Association*)
     Module[ {var = variables, schexp},
         var = Append[var, expression];
         schexp = KeyTake[var, {"exp", "rhs", "scheme"}] // PiecewiseExpandAssociation;
         var = KeyDrop[var, {"exp", "rhs", "scheme"}] // PiecewiseExpandAssociation;
         (*var = var // PiecewiseExpandAssociation;*)
         schexp = PiecewiseAssociationOperator[ParametricRefineOperator][var,"exp",schexp];
         Which[
         PiecewiseMap[KeyExistsQ[#,"rhs"]&, schexp],
         schexp = PiecewiseAssociationOperator[ParametricRefineOperator][var,"rhs",schexp],
         PiecewiseMap[KeyExistsQ[#,"scheme"]&, schexp],
         schexp = PiecewiseAssociationOperator[ParametricRefineOperator][var,"scheme",schexp]
         ];
         Header[Op][var][schexp]
     ]
     ];

Header[Op_][variables_Association][schemeexpression_] :=
    Which[
     schemeexpression === $Failed,
     $Failed,
     Head[schemeexpression] === Piecewise,
     PiecewiseOperatorMap[Header[Op], variables, schemeexpression] // PiecewiseExpandAssociation,
     True,
     Module[ {var = variables, schexp = schemeexpression, exp},
     	exp = schexp["exp"];
         If[ Lookup[var, "listop", True] && Head[exp] === List,
             Op[var][Append[schexp, "exp" -> #]] & /@ exp // 
       PiecewiseExpand // PiecewiseListClean//PiecewiseBeautifyOperator[variables],
             Op[var][schexp]
         ]
     ]
     ];

DiscreteConservedQOperator[variables_Association][expression_] :=
    HeaderOperator[DiscreteConservedQ][(*Echo@*)Append[variables, "listop" -> False]][expression];

DiscreteConservedQ[variables_Association][schemeexpression_] :=
    If[ Head[schemeexpression["exp"]] === List,
        Module[ {schexp = schemeexpression, res},
            res = 
             DiscreteConservedQ[variables][Append[schexp, "exp" -> #]] & /@ 
                schexp["exp"] // PiecewiseExpand // PiecewiseListClean;
            PiecewiseMap[And @@ # &, (*EchoLabel["DiscreteConservedQ: res"]@*)res]
        ],
        Module[ {var = variables, schexp = schemeexpression, generators},
            schexp = 
             EchoLabel["DiscreteConservedQ: schexp"]@VariationalTimeDifferenceOperator[KeyDrop[var, "listop"]][
                 (*EchoLabel["DiscreteConservedQ: schexp: input to VariationalTimeDifferenceOperator"]@*)schexp];
            schexp = EchoLabel["DiscreteConservedQ: schexp[exp]"]@PiecewiseMap[Lookup["exp"], schexp];
            generators = PiecewiseExtractGeneratorsOperator[var][schexp];
            var = Append[var, "generators" -> generators];
            (*If[Lookup[var, "display result", False], Print[schexp]];*)
            EqualToZeroOperator[Echo@var][EchoLabel["DiscreteConservedQ: schexp"]@schexp]
        ]
    ];

PiecewiseExtractGeneratorsOperator[variables_Association][expression_] :=
    Which[
     Head[expression] === List,
     (PiecewiseExtractGeneratorsOperator[variables][#] & /@ 
        expression) // Flatten,
     Head[expression] === Piecewise,
     Module[ {xp},
      (*TODO use PiecewiseLastCaseClean and not [[1]]. Later, DeleteCases[$Failed].*)
         xp = (List @@ expression)[[1]];
         xp = First /@ xp // Flatten;
         PiecewiseExtractGeneratorsOperator[variables][xp]
     ],
     True,
     Module[ {exp = expression, list},
         list = Complement[exp // Variables // Flatten, Lookup[variables, "pars", {}]];
         If[ list === {},
          (*Why do we need a non-empty list of generators?*)
             list = {variables["depVars"][[1]] @@ variables["indVars"]},
             list
         ]
     ]
     ];

VariationalTimeDifferenceOperator[variables_Association][expression_] :=
    HeaderOperator[VariationalTimeDifference][variables][expression];

VariationalTimeDifference[variables_Association][
   expression_Association] :=
    Module[ {var = variables, exp = expression},
        exp["exp"] = EchoLabel["VariationalTimeDiff: refined input"]@ParametricRefineOperator[var][exp["exp"]];
        If[ ! KeyExistsQ[var, "sortoperator"],
            var = Append[var, "sortoperator" -> SortBy[Simplify`SimplifyCount]]
        ];
        Which[
         KeyExistsQ[exp, "rhs"],
         ExplicitVariationalTimeDifferenceOperator[var][exp],
         
         KeyExistsQ[exp, "scheme"],
         EchoLabel["VariationalTimeDiff: result of ImplicitVariationalTimeDifferenceOperator"]@ImplicitVariationalTimeDifferenceOperator[var][exp],
         
         True,
         ImplicitVariationalTimeDifferenceOperator[var][Append[exp, "scheme" -> {0}]]
         ]
    ];

ExplicitVariationalTimeDifferenceOperator[variables_Association][rhsexpression_] :=
    HeaderOperator[ExplicitVariationalTimeDifference][variables][rhsexpression];

ExplicitVariationalTimeDifference[variables_Association][
   rhsexpression_Association] :=
    Module[ {var = variables, rhsexp = rhsexpression},
        If[ ! KeyExistsQ[var, "VarDOperator"],
            var = Append[var, "VarDOperator" -> DVarDOperator]
        ];
        rhsexp = TimeDifferenceOperator[var][rhsexp];
        rhsexp = 
         PiecewiseAssociationOperator[ParametricRefineOperator][var, "exp", rhsexp];
        rhsexp = 
         PiecewiseAssociationOperator[IntegralEquivalenceClassOperator][var, "exp", rhsexp];
        rhsexp = 
         PiecewiseAssociationOperator[ParametricRefineOperator][var, "exp", rhsexp];
        rhsexp = 
         PiecewiseAssociationOperator[var["VarDOperator"]][var, "exp", rhsexp];
        rhsexp = 
         EchoLabel["ExplicitVariationalDifference: rhsexp"]@PiecewiseAssociationOperator[ParametricRefineOperator][var, "exp", rhsexp];
        rhsexp = EchoLabel["ExplicitVariationalDifference: rhsexp Append"]@(
            PiecewiseMap[Append["exp" -> #] & @
            EchoLabel["ExplicitVariationalDifference: rhsexp[exp]"]@PiecewiseMap[Part[Key["exp"]],rhsexp],rhsexp])
    ];

ImplicitVariationalTimeDifferenceOperator[variables_Association][schemeexpression_] :=
    HeaderOperator[ImplicitVariationalTimeDifference][variables][schemeexpression];

ImplicitVariationalTimeDifference[variables_Association][schemeexpression_Association] :=
    Module[ {schexp = (*EchoLabel["ImplicitVariationalTimeDirrerence: input"]@*) schemeexpression, var = variables,generators},
        If[ ! KeyExistsQ[var, "VarDOperator"] || var["VarDOperator"] === DVarDOperator,
            var = Append[var, "VarDOperator" -> PartialDVarDOperator]
        ];
        If[ ! KeyExistsQ[var, "timeVars"],
            var = Append[var, "timeVars" -> {Lookup[var, "indVars"] // Last}]
        ];
        schexp = EchoLabel["ImplicitVariationalTimeDifference: result of TimeDifferenceOperator"]@TimeDifferenceOperator[var][schexp];
        schexp = EchoLabel["ImplicitVariationalTimeDifference: result of ParametricRefineOperator"]@PiecewiseAssociationOperator[ParametricRefineOperator][Echo@var, "exp", schexp];
         (*(partial) variational derivative of the expression*)
        (*schexp = EchoLabel["ImplicitVariationalTimeDifference: result of 'DVarDOperator'"]@
        PiecewiseAssociationOperator[var["VarDOperator"]][
            Append["depVars"->Echo@Select[var["depVars"],Function[x,!FreeQ[x][schexp["exp"]]]]]@var, 
            "exp", schexp];*)
        schexp = PiecewiseAssociationOperator[var["VarDOperator"]][var, "exp", schexp];
   (*Added this TimeInstancesSmallestOperator to detect a zero in the vector of DVarDOperator when there are more than one variables. But I thin we can do better....
   Choose the variables depVars to be the ones present in the expression.
   We need the vector to the zero vector... so TimeInstances was not the correct approach.*)
   (*schexp = PiecewiseAssociationOperator[TimeInstancesSmallestOperator][var,"exp",schexp];*)
        generators = PiecewiseExtractGeneratorsOperator[var][PiecewiseMap[Lookup["exp"], schexp]];
        schexp = EchoLabel["ImplicitVariationalTimeDifference: result of ParametricRefineOperator"]@PiecewiseAssociationOperator[ParametricRefineOperator][Append[var, "generators"->generators], "exp", schexp];
        schexp = EchoLabel["ImplicitVariationalTimeDifference: result of ReduceModSchemeOperator"]@ReduceModSchemeOperator[Append[var, "reduce Beautify" -> False]][schexp];
        generators = PiecewiseExtractGeneratorsOperator[var][PiecewiseMap[Lookup["exp"], schexp]];
        PiecewiseAssociationOperator[ParametricRefineOperator][Append[var, "generators"->generators], "exp", schexp]
    ];

PiecewiseAssociationOperator[Op_][variables_, key_, schemeexpression_] :=
    Which[
     schemeexpression === $Failed,
     $Failed,
     Head[schemeexpression] === Piecewise,
     PiecewiseMap[PiecewiseAssociationOperator[Op][variables, key, #] &, 
        schemeexpression] // PiecewiseExpandAssociation,
     Head[schemeexpression] === List,
     PiecewiseAssociationOperator[Op][variables, key, #] & /@ schemeexpression//PiecewiseListClean,
     True,
     Module[ {schexp = schemeexpression},
         schexp = Association @@ KeyValueMap[
            Function[{ky, value}, If[ ky === key,
                                      ky -> Op[variables][value],
                                      ky -> value
                                  ]], schexp];
         schexp // PiecewiseExpandAssociation
     ]
     ];
   
PiecewiseAssociationFunction[Fun_][key_, schemeexpression_] :=
    Which[
     schemeexpression === $Failed,
     $Failed,
     Head[schemeexpression] === Piecewise,
     PiecewiseMap[PiecewiseAssociationFunction[Fun][key, #] &, 
        schemeexpression] // PiecewiseExpandAssociation,
     Head[schemeexpression] === List,
     PiecewiseAssociationFunction[Fun][key, #] & /@ schemeexpression,
     True,
     Module[ {schexp = schemeexpression},
         schexp = Association @@ KeyValueMap[
            Function[{ky, value}, If[ ky === key,
                                      key -> Fun[value],
                                      ky -> value
                                  ]], schexp];
         schexp // PiecewiseExpandAssociation
     ]
     ];

ReduceModSchemeOperator[variables_Association][expression_] :=
    HeaderOperator[ReduceModScheme][variables][expression];
  
ReduceModScheme[variables_Association][schemeexpression_Association] :=
    Module[ {var = variables, schexp = schemeexpression, reducelist},
        schexp["scheme"] = Lookup[schexp, "scheme", {0}];
        (*If[ ! KeyExistsQ[schexp, "scheme"],
            schexp = Append[schexp, "scheme" -> {0}]
        ];*)
        (*If[ !KeyExistsQ[var,"VarDOperator"],
            If[ KeyExistsQ[var,"timeVars"],
                var = Append[var,"VarDOperator"->PartialDVarDOperator],
                var = Append[var,"VarDOperator"->DVarDOperator]
            ];
        ];*)
        var["VarDOperator"] = Lookup[var,"VarDOperator",
            If[ KeyExistsQ[var,"timeVars"],
                PartialDVarDOperator,
                "VarDOperator"->DVarDOperator
            ]
            ];
        If[ Lookup[var, "reduce Beautify", True],
            If[ ! KeyExistsQ[var, "sortoperator"],
                var = Append[var, "sortoperator" -> SortBy[Simplify`SimplifyCount]]
            ];
            (*are we repeating this procedure??? it does not take a lot of time.*)
            schexp = EchoLabel["ReduceModScheme: result of IntegralEquivalenceClassOperator"]@PiecewiseAssociationOperator[IntegralEquivalenceClassOperator][var,"exp", schexp]
        (*the result is an association like schexp*)
        ];
        reducelist = EchoLabel["ReduceModScheme: result of ReductionOperator"]@ReductionOperator[var][schexp];
        If[ Lookup[var, "reduce Beautify", True],
            reducelist = EchoLabel["ReduceModScheme: result of IntegralEquivalenceClassOperator"]@PiecewiseAssociationOperator[IntegralEquivalenceClassOperator][var, "exp", reducelist]
        ];
        reducelist = EchoLabel["ReduceModScheme: List of 'reduced' expressions"]@
        PiecewiseMap[Association["exp"->(#["exp"]&/@#),"scheme"->(Lookup[#//First,"scheme"])]&,reducelist];
        PiecewiseAssociationOperator[TimeInstancesSmallestOperator][var,"exp",reducelist]
    ];

ReductionOperator[variables_Association][schemeexpression_] :=
    HeaderOperator[Reduction][variables][schemeexpression];

Reduction[variables_Association][schemeexpression_Association] :=
    Module[ {var = variables, schexp = (*EchoLabel["Reduction: scheme "]@*) schemeexpression, scheme, exp, masterstencil,
        stencil, transl, polylist, polyvars, gbscheme, normalred, eliminationlist, reducelist, expvars},
        exp = schexp["exp"];
        If[EqualToZeroOperator[var][ exp],
            Return[List[schexp,schexp],Module]
        ];
        scheme = schexp["scheme"];
        masterstencil = (*EchoLabel["Reduction: masterstencil "]@*) StencilOperator[var][exp];
        stencil = (*EchoLabel["Reduction: stencil "]@*) StencilOperator[var][scheme];
        
        (* this may be an alternative to the code below.
         translations = Flatten[Table[{i, j}, {i, 0, 0}, {j, -1, 0}], 1]
         {n -> n + #1, t -> t + #2} & @@@ translations
         Flatten[schemma /. %] // Expand
        *)
        transl = 
         EchoLabel["Reduction: RangeSchemeTranslationsOperator"][(*QuietEcho@*)RangeSchemeTranslationsOperator[var][masterstencil, #] & /@ stencil];
        If[ (transl//Flatten)==={},
            (*this is the no translations alternative:
            transl = Table[Table[0,Length@var["indVars"]], Length@scheme];*)
            transl = Table[{Table[0,Length@var["indVars"]],
                Append[-1]@Table[0,Length@var["indVars"]-1]},Length@scheme]
        ];
        g[nscheme_, trans_List] :=
            Map[MKF[var["indVars"], nscheme] @@ # &, 
             trans + Table[var["indVars"], Length[trans]]
            ];
        polylist = EchoLabel["Reduction: translations of the scheme"]@(DeleteDuplicates[MapThread[g, {scheme, transl}] // Flatten]);
        (*Print["Pause"];
        Pause[10];*)
        (*If[ polylist === {},
            polylist = scheme
        ];*)
        polyvars = Complement[Union[polylist // Variables // Flatten, exp // Variables // Flatten] // Flatten, 
          Lookup[var, "pars", {}]];
        polyvars = EchoLabel["Reduction: ordered variables from the translations of the scheme"]@Sort[polyvars, TimeOrderedQOperator[Append[variables,"elimOrder"->"explicit"]]];
    
        (*polyvars = Complement[
       polylist // Variables // Flatten,
       Lookup[var, "pars", {}]];*)
       (*polyvars = Sort[polyvars, TimeOrderedQOperator[Append[variables,"elimOrder"->"explicit"]]];*)
       (*polyvars = EchoLabel["Reduction: ordered variables from the translations of the scheme"]@ReverseSortBy[Simplify`SimplifyCount][polyvars];*)
       
       (*
       expvars = exp // Variables // Flatten;
       expvars = EchoLabel["Reduction: ordered variables from the expression"]@Sort[expvars, TimeOrderedQOperator[Append[variables,"elimOrder"->"explicit"]]];
       (*polyvars = EchoLabel["Reduction: ordered variables from the translations of the scheme"]@Join[Most@expvars,Complement[polyvars,expvars],{Last@expvars}];*)
       polyvars = EchoLabel["Reduction: ordered variables from the translations of the scheme"]@Join[expvars,Complement[polyvars,expvars]];
       *)
       (*
       polyvars = EchoLabel["Reduction: ordered variables from the translations of the scheme"]@Complement[
       polylist // Variables // Flatten,
       Lookup[var, "pars", {}]];
       *)
    (*from here *)
    
    (* Friedmann code *)
    (*
     scheme = 
      GroebnerBasis[polylist, polyvars, 
       CoefficientDomain -> RationalFunctions];
       
       *)
       
     (* DG code *)  
       (*
       Print["original scheme = ", scheme];
       Print["polylist = ",polylist];
       Print["polyvars = ",polyvars];
       *)
        gbscheme =(*EchoLabel["Reduction: gb of translations of scheme"]@*) QuietEcho@ComprehensiveGroebnerSystemOperator[Append[variables, "generators"->polyvars]][polylist];  
          
         (*
          Print["polyscheme = ", scheme]; 
          *)
          
        (* Friedmann code *)
       (*  
        normalred = 
         PolynomialReduce[exp, scheme, polyvars, 
           CoefficientDomain -> RationalFunctions] // Last;
           
            *)
          
        (* DG code *)
        normalred = (*EchoLabel["Reduction: normalred"]@*) PiecewisePolynomialRemainderOperator[Append[variables, "generators"->polyvars]][exp,gbscheme];
         
         (*
        Print["original scheme = ", scheme];
        Print["polylist = ",polylist];
        Print["polyvars = ",polyvars];
        Print["polyscheme = ", scheme]; 
        Print["normalred = ", normalred]; 
         *)
         
         
         (*Version without elimination, but we need to do something about the scheme*)
         
         (*EchoLabel["Reduction: reduced expression and scheme"]@List[Association["exp"->normalred,"scheme"->scheme]//PiecewiseExpandAssociation]*)
        normalred = EchoLabel["Reduction: reduced expression and gb of translations of scheme"]@Association["exp"->normalred,"scheme"->gbscheme]//PiecewiseExpandAssociation;
        (*maybe we don't want to do the following step (Ricard was inspired to finish early)
        normalred["exp"] = IntegralEquivalenceClassOperator[var][normalred["exp"]];*)
        Which[
            EqualToZeroOperator[var][normalred["exp"]],
            (*Print["2)End now!\nnormalred = ",normalred];*)
            Return[List[schexp,normalred],Module],
            
            (*
            normalred["exp"]=!=exp,
            Print["Would use variable elimination operator, but we stop here!\n",normalred["exp"]];
            Return[List[schexp,normalred],Module],
            *)
            (*var["ordering"]=!=DegreeReverseLexicographic,
            (*Print["Reduce again...!\nnormalred = ", normalred];*)
            Return[Reduction[Append["ordering"->DegreeReverseLexicographic]@var][schexp],Module],
            *)
            True,
            Print["Will use variable elimination operator.\nnormalred = ",normalred]
        ];
        (*TODO there is a chance that the algorithm could have stoped here: check if normalred["exp"]==0?????*)
        
        
        (* set up list of lists with elimination order, i.e. 
       order of variables in which they are eliminated , 
       default is permutations, 
       specify function that does that by function name*)

       (*TODO check if this commented code is really necessary. Elimination stuff is not well explained. 
       To Ricardo, it is not clear how a GB with elimination order is used.*)
        eliminationlist = EchoLabel["Reduction: EliminationListOperator"][
            Lookup[var, "EliminationListOperator", EliminationListOperator][
                Echo@Append[var, "scheme" -> polylist]][exp]]; (*list of lists*)
        reducelist = EchoLabel["Reduction: VariableEliminationOperator"][
            VariableEliminationOperator[Append[var,"elimOrder"->Lookup[var,"elimOrder","explicit"]]][#, 
                (*TODO Should we change the scheme?? After trying with the translations, the code crashed ... Append["scheme"->polylist]@*)schexp] & /@ eliminationlist];
        Append[reducelist, normalred] // PiecewiseExpand // PiecewiseListClean
    (* to here there are some picewise objects *)
   
    ];
    
(*These are Daniel Lichtblaum's functions as in https://mathematica.stackexchange.com/questions/184632/default-weight-matrix-for-eliminationorder *)
drlMatrix[n_] :=
    Prepend[Table[-KroneckerDelta[j + k - (n + 1)], {j, n - 1}, {k, n}],
      Table[1, {n}]];
elimMatrix[n1_, n2_] :=
    Module[ {row1, rest},
        row1 = Join[Table[1, {n1}], Table[0, {n2 - n1}]];
        rest = drlMatrix[n2];
        rest = Drop[rest, {-n1}];
        Prepend[rest, row1]
    ];

VariableEliminationOperator[variables_Association][
   eliminationlist_List, schemeexpression_] :=
    Which[
     schemeexpression === $Failed,
     $Failed,
     Head[schemeexpression] === Piecewise,
     PiecewiseMap[
        VariableEliminationOperator[variables][eliminationlist, #] &,schemeexpression] // PiecewiseExpand // PiecewiseListClean,
     Head[schemeexpression] === List,
     VariableEliminationOperator[variables][eliminationlist, #] & /@ 
        schemeexpression // PiecewiseExpand // PiecewiseListClean,
     True,
     Module[ {var = variables, schexp = schemeexpression, scheme, exp, elimlist = eliminationlist, elem, 
       Gbasis, polyvars, n1, n2, ordermatrix, expvars},
         scheme = schexp["scheme"];
         exp = schexp["exp"];
         (*If[ Length[elimlist] === 1 || elimlist === {},*)
         If[ Length[elimlist] <= 1,
             schexp,
             elem = EchoLabel["VariableEliminationOperator: element"][elimlist[[1]]];
             polyvars = EchoLabel["VariableEliminationOperator: polyvars"][scheme//Variables//Flatten];
             expvars = EchoLabel["VariableEliminationOperator: expvars"][exp//Variables//Flatten];
             If[ polyvars =!= {},
                 If[ MemberQ[polyvars,elem],
                     If[ "elimOrder"==="permutations",
                         (*TODO could we use Join instead of append and flatten?*)
                         polyvars = Sort[Union[expvars,polyvars], TimeOrderedQOperator[variables]],
                         (*When we take comlement, the variables of scheme not in the expression are ordered by Mathematica!*)
                         polyvars = EchoLabel["VariableEliminationOperator: EliminationListOperator with polyvars not in expvars appended"]@Join[EliminationListOperator[variables][Plus@@expvars]//First, Complement[polyvars,expvars]]
                     ];
                     n1 = EchoLabel["n1"]@Position[polyvars,elem]//First//First;
                     n2 = EchoLabel["n2"]@Length[polyvars];
                     ordermatrix = elimMatrix[n1,n2];
                     
                 (* from here *)    
                     (* Friedmann code *)
                 (*Gbasis = GroebnerBasis[scheme, polyvars, CoefficientDomain -> RationalFunctions, MonomialOrder -> ordermatrix];*)
                 (*exp = 
                  PolynomialReduce[exp, Gbasis, polyvars, CoefficientDomain -> RationalFunctions, MonomialOrder -> ordermatrix] // Last;*)
                     Gbasis = EchoLabel["VariableEliminationOperator: elimination groebner base"]@QuietEcho@ComprehensiveGroebnerSystemOperator[Append[{"ordering"-> ordermatrix,"generators"->polyvars}]@variables][scheme];
                     (*Gbasis=GroebnerBasis[scheme, polyvars, CoefficientDomain -> RationalFunctions, MonomialOrder -> ordermatrix]*);
                     schexp["exp"] = EchoLabel["VariableEliminationOperator: PiecewisePolynomialRemainderOperator"]@PiecewisePolynomialRemainderOperator[Append[variables, {"ordering"-> ordermatrix, "generators"->polyvars}]][exp, Gbasis];
                     If[ Lookup[Echo@var, "reduce Beautify", True],
                         schexp = EchoLabel["VariableEliminationOperator: IntegralEquivalenceClassOperator"]@PiecewiseAssociationOperator[IntegralEquivalenceClassOperator][var, "exp", schexp]
                     ];
                 ];
                 VariableEliminationOperator[var][Drop[elimlist, 1],schexp],
                 schexp
             ]
         ]
     (* up to here there are some picewise objects *)
        ]
     ];

TimeInstancesSmallestOperator[variables_Association][expression_] :=
    Which[
    expression === $Failed,
    $Failed,
    Head[expression] === Piecewise,
    PiecewiseOperatorMap[TimeInstancesSmallestOperator, variables, 
     expression],
    True,
    Module[ {var = variables, exp = (*EchoLabel["TimeInstancesSmallestOperator: input"]@*) expression, 
      t = variables["indVars"] // Last, varlist},
        varlist = 
         Complement[# // Variables, Lookup[var, "pars", {}]] & /@ exp;
        varlist = 
         varlist /. ((#[x___] :> Last[List @@ #[x]]) & /@ 
            var["depVars"]);
        varlist = varlist /. (KroneckerDeltaOperator[x___] :> x);
        varlist = DeleteDuplicates[#] & /@ varlist;
        varlist = Union[Cases[#, _ + t], Cases[#, t]] & /@ varlist;
        varlist = Length[#] & /@ varlist;
        f[exp, elem_] :=
            If[ elem === 0 && exp === 0,
                -1,
                elem
            ];
        varlist = f[exp, #] & /@ varlist;
        exp[[
         FirstPosition[varlist, TakeSmallest[varlist, 1] // First] // 
      First]]
    ]
    ];

(*
generates list of lists, where each list contains the variables of \
the expression in a given
row such that they can be eliminated according to that list
* permutations: gives list of lists with all permutations
* implicit: gives list with one list with the first element being the \
one with the lowest time (i.e. t < t+1) and the last one with the \
highest time. The same ordering applies to the other independent \
variables
 * explicit: gives list with one list with the first element being \
the one with the highest time (i.e. t+1 > t) and the last one with \
the lowest time. The same ordering applies to the other independent \
variables
Default is explicit order.
*)

EliminationListOperator[variables_Association][expression_] :=
    Which[
     expression === $Failed,
     $Failed,
     True,
     Module[ {polyvars, helpvars1, helpvars2, firstlist, secondlist, elimOrder},
         polyvars = Complement[expression // Variables // Flatten, Lookup[variables, "pars", {}]] // DeleteDuplicates;
         elimOrder = variables["elimOrder"];
         Which[
          elimOrder === "implicit",
          {Sort[polyvars, TimeOrderedQOperator[variables]]},
          
          elimOrder === "permutations",
          Permutations[polyvars],
          
          elimOrder === "explicitimplicit",
          (*TODO What if we have more explicit dependent variables?*)
          helpvars1 =  Select[polyvars, Head[#] == First[variables["depVars"]]&];
          firstlist = Sort[helpvars1, TimeOrderedQOperator[Append[variables, "elimOrder" -> "explicit"]]];
          helpvars2 = Complement[polyvars,helpvars1];
          secondlist = Sort[helpvars2, TimeOrderedQOperator[Append[variables, "elimOrder" -> "implicit"]]];
          {Join[firstlist,secondlist]},
          
          True,
          {Sort[polyvars, TimeOrderedQOperator[Append[variables, "elimOrder" -> "explicit"]]]}
          ]
     ]
     ];

(*TimeOrderedQ gives true if x>=y where x>=y means that all instances \
of independent variables started from the last one (the time \
variable) are the same and one of x is actually greater or equal \
(explicit) or less or equal (implicit) and false otherwise*)

TimeOrderedQOperator[variables_Association][x_, y_] :=
    Which[
     x === $Failed || y === $Failed,
     $Failed,
     True,
     Module[ {xlist, ylist, poslist, depvars, indvars},
         depvars = Lookup[variables,"depVars",{}];
         indvars = Lookup[variables,"indVars",{}];
         Which[
          (MemberQ[depvars, Head[x]] && MemberQ[depvars, Head[y]]) ||
           (!MemberQ[depvars, Head[x]] && !MemberQ[depvars, Head[y]]),
          xlist = Cases[x, _ + #, All] & /@ indvars;
          poslist = Position[(*Echo@*)xlist, {}] // Flatten;
          xlist[[poslist]] = Cases[x, #, All] & /@ (indvars[[(*Echo@*)poslist]]);
          poslist = Position[xlist, {}] // Flatten;
          xlist[[poslist]] = -Table[Infinity, Length[poslist]];
          ylist = Cases[y, _ + #, All] & /@ indvars;
          poslist = Position[ylist, {}] // Flatten;
          ylist[[poslist]] = Cases[y, #, All] & /@ (indvars[[poslist]]);
          poslist = Position[ylist, {}] // Flatten;
          ylist[[poslist]] = -Table[Infinity, Length[poslist]];
          xlist = xlist // Flatten;
          ylist = ylist // Flatten;
          TimeOrderOperator[variables][xlist, ylist],
          MemberQ[depvars, Head[x]],
          True,
          MemberQ[depvars, Head[y]],
          False
          ]
     ]
     ];

TimeOrderOperator[variables_Association][xlist_List, ylist_List] :=
    Module[ {},
        If[ Lookup[variables, "elimOrder", "explicit"] === "implicit",
            Oper[x_] :=
                Identity[x],
            Oper[x_] :=
                Not[x]
        ];
        Which[
         xlist === {},
         True,
         (xlist // Last) === (ylist // Last),
         TimeOrderOperator[variables][Drop[xlist, -1], Drop[ylist, -1]],
         OrderedQ[{xlist // Last, ylist // Last}],
         Oper[True],
         True,
         Oper[False]
         ]
    ];

TimeDifferenceOperator[variables_Association][expression_] :=
    HeaderOperator[TimeDifference][variables][expression]

TimeDifference[variables_Association][schemeexpression_Association] :=
    Module[ {schexp = (*Echo@*) schemeexpression, exp, var = variables, t},
    	exp = schexp["exp"];
        If[ EqualToZeroOperator[var][exp],
            Return[schexp, Module]
        ];
        If[ KeyExistsQ[schexp,"rhs"],
            If[ ! KeyExistsQ[var, "VarDOperator"],
                var = Append[var, "VarDOperator" -> DVarDOperator]
            ],
            If[ KeyExistsQ[var, "timeVars"],
                t = var["timeVars"] // Last,
                t = var["indVars"] // Last;
                var = Append[var, "timeVars" -> {t}]
            ];
            If[ ! KeyExistsQ[var, "VarDOperator"] || var["VarDOperator"] === DVarDOperator,
                var = Append[var, "VarDOperator" -> PartialDVarDOperator]
            ]
        ];
        If[ ! KeyExistsQ[var, "timederivativeorder"],
            var = Append[var, "timederivativeorder" -> 1]
        ];
        If[ KeyExistsQ[schexp, "rhs"],
            replacementrule = MapThread[#1 -> MKF[var["indVars"], #2] &, {var["depVars"], schexp["rhs"]}];
            schexp["exp"] = (exp /. replacementrule) - exp,
            
            If[ KeyExistsQ[var,"timedifference"],
                schexp["exp"] = var["timedifference"] @ exp,

                schexp["exp"] = (exp /. t :> t + 1) - exp
            ];
        ];
        var["timederivativeorder"] = var["timederivativeorder"] - 1;
        If[ var["timederivativeorder"] > 0,
            TimeDifferenceOperator[var][schexp],
            
            If[ KeyExistsQ[schexp, "scheme"],
                If[ Lookup[var, "Beautify", True],
                		schexp = EchoLabel["TimeDifference: result of IntegralEquivalenceClassOperator"]@PiecewiseAssociationOperator[IntegralEquivalenceClassOperator][var, "exp", schexp]
                ];
                schexp = EchoLabel["TimeDifference: result of ReduceModSchemeOperator"]@ReduceModSchemeOperator[var][schexp]
            ];
            If[ Lookup[var, "Beautify", True],
                schexp = EchoLabel["TimeDifference: result of IntegralEquivalenceClassOperator on time difference"]@PiecewiseAssociationOperator[IntegralEquivalenceClassOperator][var, "exp", schexp]
            ];
            PiecewiseAssociationFunction[Expand]["exp", schexp]
        ]
    ]
  
  
expand :=
    Expand[#] /. Power[x_, y_] :> Power[Expand[Power[x, -y]], -1] &;

FindDiscreteConservedQuantityOperator[variables_Association][problem_] :=
    Which[
    problem === $Failed,
    $Failed,
    Head[problem] === Piecewise, 
    PiecewiseOperatorMap[FindDiscreteConservedQuantityOperator, 
    variables, problem], True, 
    Module[ {monomials, basis, glc, conservationcondition, sol},
        monomials = MonomialsOperator[variables][problem];
        basis = BasisModNullLagrangiansOperator[variables][monomials](*/.{}->$Failed*);
        glc = GenericLinearCombinationOperator[variables][basis];
        conservationcondition = 
         PiecewiseMap[
          TimeDifferenceOperator[
             Append[
              variables, {"timederivativeorder" -> 
                Lookup[problem, "timederivativeorder", 
                 Lookup[variables, "timederivativeorder", 1]], 
               "rhs" -> 
                Lookup[problem, "rhs", Lookup[variables, "rhs", 1]], 
               "Beautify" -> False}]][#[[1]]] &, glc];
        conservationcondition = 
         PiecewiseMap[#["exp"] &, conservationcondition];
        conservationcondition = 
         PiecewiseMap[
          Lookup[variables, "VarDOperator", DVarDOperator][variables][#] +
            ReplaceAll[
              Map[# -> Function[0] &, variables["depVars"]]][#] &, 
          conservationcondition];
        conservationcondition = 
         PiecewiseMap[Expand@Simplify@expand@# &, conservationcondition];
        sol = 
         PiecewiseMap[
          If[ #[[1]] === $Failed || #[[2]] === $Failed,
              $Failed,
              SolveUndeterminedCoefficientsOperator[
                Append[variables, "coefficients" -> #[[1, 2]]]][#[[2]]]
          ] &, 
          PiecewiseExpand[{glc, conservationcondition}]];
        PiecewiseMap[First, PiecewiseReplace[glc, sol]]
    ]
    ];

FindDiscreteConservedQuantityBasisOperator[variables_Association][problem_] :=
    With[ {conservationlaws = 
    FindDiscreteConservedQuantityOperator[variables][
    problem]},
        PiecewiseMap[
          With[ {coefficients = 
              DeleteDuplicates[
               Cases[#, Subscript[\[FormalA], _], {0, Infinity}]]},
              Map[Function[coeff, conservationlaws /. coeff -> 1], 
                coefficients] /. (Function[c, Rule[c, 0]] /@ 
                 coefficients)
          ] &, conservationlaws] //PiecewiseExpand// PiecewiseBeautifyOperator[variables]
    ]; 
          
End[] (* End Private Context *)
(*EndPackage[]*)