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

VariationalTimeDifference::usage= "debuging ..."

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

VariableEliminationOperator::usaga ="";




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
   Module[
   	{sten = stencil, masten = masterstencil, stenkeys, mastenkeys, rangelist, stencillist, translist},
    stenkeys = Select[sten, (# // Flatten) === {} &] // Keys;
    sten = KeyDrop[sten, stenkeys];
    mastenkeys = Select[masten, (# // Flatten) === {} &] // Keys;
    masten = KeyDrop[masten, mastenkeys];
    If[ 
     sten === Association[] || masten === Association[] || !SubsetQ[Keys[masten], Keys[sten]],
     {},
     rangelist =  
      Association @@ 
       Map[# -> 
          Transpose[{Min /@ Transpose[masten[#]], 
            Max /@ Transpose[masten[#]]}] &, Keys[sten]];
     stencillist = 
      Association @@ 
       Map[# -> 
          Transpose[{Min /@ Transpose[sten[#]], 
            Max /@ Transpose[sten[#]]}] &, Keys[sten]]; 
     rangelist = rangelist[#] & /@ Keys[sten];
     stencillist = stencillist[#] & /@ Keys[sten];
     If[
      Lookup[variables, "intersect", False],
      translist = 
       MapThread[
        MapThread[{#1[[1]] - #2[[2]], #1[[2]] - #2[[
              1]]} &, {#1, #2}] &, {rangelist, stencillist}],
      translist = rangelist - stencillist
      ];
     translist = Map[Table[k, {k, #[[1]], #[[2]], 1}] &, translist, {2}];
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
   Module[
    {exp},
    exp = Association["exp" -> expression];
    HeaderOperator[Op][variables][exp]
    ],
   True,(*Head[expression] === Association*)
   Module[
    {var = variables, schexp},
    var = Append[var, expression];
    schexp = KeyTake[var, {"exp", "rhs", "scheme"}] // PiecewiseExpandAssociation;
    var = KeyDrop[var, {"exp", "rhs", "scheme"}] // PiecewiseExpandAssociation;
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
   Module[
    {var = variables, schexp = schemeexpression},
    If[
     Lookup[var, "listop", True] && Head[schexp["exp"]] === List,
     Op[var][Append[schexp, "exp" -> #]] & /@ schexp["exp"] // 
       PiecewiseExpand // PiecewiseListClean//PiecewiseBeautifyOperator[variables],
     Op[var][schexp]
     ]
    ]
   ];

DiscreteConservedQOperator[variables_Association][expression_] := HeaderOperator[DiscreteConservedQ][Append[variables, "listop" -> False]][expression];

DiscreteConservedQ[variables_Association][schemeexpression_] :=
  If[
   Head[schemeexpression["exp"]] === List,
   Module[
    {schexp = schemeexpression, res},
    res = 
     DiscreteConservedQ[variables][Append[schexp, "exp" -> #]] & /@ 
        schexp["exp"] // PiecewiseExpand // PiecewiseListClean;
    PiecewiseMap[And @@ # &, EchoLabel["DiscreteConservedQ: res"]@res]
    ],
   Module[
    {var = variables, schexp = schemeexpression, generators},
    schexp = 
     EchoLabel["DiscreteConservedQ: schexp"]@VariationalTimeDifferenceOperator[KeyDrop[var, "listop"]][
     	EchoLabel["DiscreteConservedQ: schexp: input to VariationalTimeDifferenceOperator"]@schexp];
    schexp = EchoLabel["DiscreteConservedQ: schexp[exp]"]@PiecewiseMap[Lookup["exp"] (*/@ # &*), schexp];
    generators = PiecewiseExtractGeneratorsOperator[var][schexp];
    var = Append[var, "generators" -> generators];
    If[Lookup[var, "display result", False], Print[schexp]];
    EqualToZeroOperator[var][schexp]
    ]
   ];

PiecewiseExtractGeneratorsOperator[variables_Association][expression_] :=
  Which[
   Head[expression] === List,
   (PiecewiseExtractGeneratorsOperator[variables][#] & /@ 
      expression) // Flatten,
   Head[expression] === Piecewise,
   Module[
    {xp},
    (*TODO iuse PiecewiseLastCaseClean and not [[1]]. Later, DeleteCases[$Failed].*)
    xp = (List @@ expression)[[1]];
    xp = First /@ xp // Flatten;
    PiecewiseExtractGeneratorsOperator[variables][xp]
    ],
   True,
   Module[{exp = expression, list},
    list = 
     Complement[exp // Variables // Flatten, 
      Lookup[variables, "pars", {}]];
    If[
     list === {},
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
  Module[
   {var = variables, exp = expression},
   exp["exp"] = ParametricRefineOperator[var][exp["exp"]];
   If[
    ! KeyExistsQ[var, "sortoperator"],
    var = Append[var, "sortoperator" -> SortBy[Simplify`SimplifyCount]]
    ];
   Which[
    KeyExistsQ[exp, "rhs"],
    ExplicitVariationalTimeDifferenceOperator[var][exp],
    KeyExistsQ[exp, "scheme"],
    ImplicitVariationalTimeDifferenceOperator[var][exp],
    True,
    ImplicitVariationalTimeDifferenceOperator[var][
     Append[exp, "scheme" -> {0}]]
    ]
   ];

ExplicitVariationalTimeDifferenceOperator[variables_Association][rhsexpression_] := 
  HeaderOperator[ExplicitVariationalTimeDifference][variables][rhsexpression];

ExplicitVariationalTimeDifference[variables_Association][
   rhsexpression_Association] :=
  Module[
   {var = variables, rhsexp = rhsexpression},
   If[
    ! KeyExistsQ[var, "VarDOperator"],
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
  Module[
   {schexp = schemeexpression, var = variables,generators},
    If[! KeyExistsQ[var, "VarDOperator"] || var["VarDOperator"] === DVarDOperator,
       var = Append[var, "VarDOperator" -> PartialDVarDOperator]
       ];
   If[
    ! KeyExistsQ[var, "timeVars"],
    var = Append[var, "timeVars" -> {Lookup[var, "indVars"] // Last}]
    ];
   schexp = TimeDifferenceOperator[var][schexp];
   schexp = 
    PiecewiseAssociationOperator[ParametricRefineOperator][var, "exp", schexp];
   schexp = 
    PiecewiseAssociationOperator[var["VarDOperator"]][var, "exp", schexp];
   generators = PiecewiseExtractGeneratorsOperator[var][PiecewiseMap[Lookup["exp"], schexp]];
   schexp = 
    PiecewiseAssociationOperator[ParametricRefineOperator][Append[var, "generators"->generators], "exp", schexp];
   schexp = 
    ReduceModSchemeOperator[Append[var, "reduce Beautify" -> False]][
     schexp];
   generators = PiecewiseExtractGeneratorsOperator[var][PiecewiseMap[Lookup["exp"], schexp]]; 
   schexp = 
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
   Module[
    {schexp = schemeexpression},
    schexp = Association @@ KeyValueMap[
       Function[{ky, value}, If[
         ky === key,
         ky -> Op[variables][value],
         ky -> value]], schexp];
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
   Module[
    {schexp = schemeexpression},
    schexp = Association @@ KeyValueMap[
       Function[{ky, value}, If[
         ky === key,
         key -> Fun[value],
         ky -> value]], schexp];
    schexp // PiecewiseExpandAssociation
    ]
   ];

ReduceModSchemeOperator[variables_Association][expression_] := 
  HeaderOperator[ReduceModScheme][variables][expression];
  
ReduceModScheme[variables_Association][schemeexpression_Association] :=
  Module[
  {var = variables, schexp = schemeexpression, reducelist},
  If[
   ! KeyExistsQ[schexp, "scheme"],
   schexp = Append[schexp, "scheme" -> {0}]
   ];
   If[
   	!KeyExistsQ[var,"VarDOperator"],
   	If[
   		KeyExistsQ[var,"timeVars"],
   		var = Append[var,"VarDOperator"->PartialDVarDOperator],
   		var = Append[var,"VarDOperator"->DVarDOperator]
   	];
   ];
   If[
   Lookup[var, "reduce Beautify", True],
   If[
    ! KeyExistsQ[var, "sortoperator"],
    var = Append[var, "sortoperator" -> SortBy[Simplify`SimplifyCount]]
    ];
   schexp = PiecewiseAssociationOperator[IntegralEquivalenceClassOperator][var,"exp", schexp]
   ];
  reducelist = ReductionOperator[var][schexp];
  If[
   Lookup[var, "reduce Beautify", True],
   reducelist = PiecewiseAssociationOperator[IntegralEquivalenceClassOperator][var, "exp", reducelist]
   ];
   reducelist = PiecewiseMap[Association["exp"->(#["exp"]&/@#),"scheme"->(Lookup[#//First,"scheme"])]&,reducelist];
  schexp = PiecewiseAssociationOperator[TimeInstancesSmallestOperator][var,"exp",reducelist]
  ];

ReductionOperator[variables_Association][schemeexpression_]:=
	HeaderOperator[Reduction][variables][schemeexpression];

Reduction[variables_Association][schemeexpression_Association] :=
	Module[
	{var = variables, schexp = schemeexpression, masterstencil,
		stencil, transl, polylist, polyvars, scheme, normalred, eliminationlist, reducelist},
	masterstencil = StencilOperator[var][schexp["exp"]];
  stencil = StencilOperator[var][schexp["scheme"]];
  transl = 
   RangeSchemeTranslationsOperator[var][masterstencil, #] & /@ stencil;
  g[nscheme_, trans_List] := 
   If[
   	(trans // Flatten) =!= {}, 
    Map[MKF[var["indVars"], nscheme] @@ # &, 
     trans + Table[var["indVars"], Length[trans]]],
    {}];
  polylist =MapThread[g, {schexp["scheme"], transl}] // Flatten;
  If[polylist === {}, polylist = schexp["scheme"]];
  polyvars = 
   Complement[
    Union[polylist // Variables // Flatten, 
      schexp["exp"] // Variables // Flatten] // Flatten, 
    Lookup[var, "pars", {}]];
 polyvars = Sort[polyvars, TimeOrderedQOperator[Append[variables,"elimOrder"->"explicit"]]];
 
 (*from here *)
 
 (* Friedmann code *)
 (*
  scheme = 
   GroebnerBasis[polylist, polyvars, 
    CoefficientDomain -> RationalFunctions];
    
    *)
    
  (* DG code *)  
    (*
    Print["original scheme = ", schexp["scheme"]];
    Print["polylist = ",polylist];
    Print["polyvars = ",polyvars];
    *)
  scheme=GrobOp[Append[variables, "generators"->polyvars]][polylist];  
    
   (*
    Print["polyscheme = ", scheme]; 
    *)
    
  (* Friedmann code *)
 (*  
  normalred = 
   PolynomialReduce[schexp["exp"], scheme, polyvars, 
     CoefficientDomain -> RationalFunctions] // Last;
     
      *)
    
  (* DG code *)  
    
    
    normalred= PiecewisePolynomialRemainderOperator[Append[variables, "generators"->polyvars]][schexp["exp"],scheme];
     
     (*
    Print["original scheme = ", schexp["scheme"]];
    Print["polylist = ",polylist];
    Print["polyvars = ",polyvars];
    Print["polyscheme = ", scheme]; 
    Print["normalred = ", normalred]; 
     *)
     
     
   normalred = Association["exp"->normalred,"scheme"->scheme]//PiecewiseExpandAssociation;
   (* set up list of lists with elimination order, i.e. 
  order of variables in which they are eliminated , 
  default is permutations, 
  specify function that does that by function name*)
 
  eliminationlist = 
   Lookup[var, "EliminationListOperator", EliminationListOperator][
     Append[var, "scheme" -> polylist]][
    schexp["exp"]]; (*list of lists*)
  reducelist = VariableEliminationOperator[Append[var,"elimOrder"->Lookup[var,"elimOrder","explicit"]]][#, schexp] & /@ eliminationlist;
   Append[reducelist, normalred] // PiecewiseExpand // PiecewiseListClean
   
   (* to here there are some picewise objects *)
   
	];

drlMatrix[n_] := 
  Prepend[Table[-KroneckerDelta[j + k - (n + 1)], {j, n - 1}, {k, n}],
    Table[1, {n}]];
elimMatrix[n1_, n2_] := 
  Module[{row1, rest}, 
   row1 = Join[Table[1, {n1}], Table[0, {n2 - n1}]];
   rest = drlMatrix[n2];
   rest = Drop[rest, {-n1}];
   Prepend[rest, row1]];

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
   Module[{var = variables, schexp = schemeexpression, elimlist = eliminationlist, elem, 
     Gbasis, polyvars, n1, n2, ordermatrix, expvars},
    If[
     Length[elimlist] === 1 || elimlist === {},
     schexp,
     elem = elimlist[[1]];
     polyvars = schexp["scheme"]//Variables//Flatten;
     expvars = schexp["exp"]//Variables//Flatten;
     If[
      polyvars =!= {},
      If[
      	MemberQ[polyvars,elem],
      	If[
      		"elimOrder"==="permutations",
      		polyvars = Sort[Union[expvars,polyvars], TimeOrderedQOperator[variables]],
      		polyvars = Append[EliminationListOperator[variables][Plus@@expvars]//First, Complement[polyvars,expvars]]//Flatten
      	];
      	n1 = Position[polyvars,elem]//First//First;
      	n2 = Length[polyvars];
      	ordermatrix = elimMatrix[n1,n2];
      	
      (* from here *)	
      	(* Friedmann code *)
      (*Gbasis = GroebnerBasis[schexp["scheme"], polyvars, CoefficientDomain -> RationalFunctions, MonomialOrder -> ordermatrix];*)
      (*schexp["exp"] = 
       PolynomialReduce[schexp["exp"], Gbasis, polyvars, CoefficientDomain -> RationalFunctions, MonomialOrder -> ordermatrix] // Last;*)
       
       
        Gbasis=GrobOp[Append[variables, "generators"->polyvars]][schexp["scheme"]];  
        schexp["exp"] = PiecewisePolynomialRemainderOperator[Append[variables, "generators"->polyvars]][schexp["exp"], Gbasis];
  
  
       
       
      If[
       Lookup[var, "reduce Beautify", True],
       schexp = PiecewiseAssociationOperator[IntegralEquivalenceClassOperator][var, "exp", schexp]
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
   Module[
    {var = variables, exp = expression, 
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
    f[exp, elem_] := If[
      elem === 0 && exp === 0, -1, elem
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
   Module[
    {polyvars, list, helpvars1, helpvars2, firstlist, secondlist},
    polyvars = 
     Complement[expression // Variables // Flatten, 
       Lookup[variables, "pars", {}]] // DeleteDuplicates;
    Which[
     variables["elimOrder"] === "implicit",
     list = {Sort[polyvars, TimeOrderedQOperator[variables]]},
     variables["elimOrder"] === "permutations",
     list = Permutations[polyvars],
     variables["elimOrder"] === "explicitimplicit",
     helpvars1 =  Select[polyvars, Head[#] == First[variables["depVars"]]&];
     firstlist = Sort[helpvars1, 
        TimeOrderedQOperator[
         Append[variables, "elimOrder" -> "explicit"]]];
     helpvars2 = Complement[polyvars,helpvars1];
     secondlist = Sort[helpvars2, 
        TimeOrderedQOperator[
         Append[variables, "elimOrder" -> "implicit"]]];
     list = {Append[firstlist,secondlist]//Flatten},
     True,
     list = {Sort[polyvars, 
        TimeOrderedQOperator[
         Append[variables, "elimOrder" -> "explicit"]]]}
     ];
    list
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
   Module[
    {xlist, ylist, poslist},
    Which[
     (MemberQ[variables["depVars"], Head[x]] && 
        MemberQ[variables["depVars"], Head[y]]) ||
      (!MemberQ[variables["depVars"], Head[x]] && !MemberQ[variables["depVars"], Head[y]]),
     xlist = Cases[x, _ + #, All] & /@ variables["indVars"];
     poslist = Position[xlist, {}] // Flatten;
     xlist[[poslist]] = 
      Cases[x, #, All] & /@ (variables["indVars"][[poslist]]);
     poslist = Position[xlist, {}] // Flatten;
     xlist[[poslist]] = -Table[Infinity, Length[poslist]];
     ylist = Cases[y, _ + #, All] & /@ variables["indVars"];
     poslist = Position[ylist, {}] // Flatten;
     ylist[[poslist]] = 
      Cases[y, #, All] & /@ (variables["indVars"][[poslist]]);
     poslist = Position[ylist, {}] // Flatten;
     ylist[[poslist]] = -Table[Infinity, Length[poslist]];
     xlist = xlist // Flatten;
     ylist = ylist // Flatten;
     TimeOrderOperator[variables][xlist, ylist],
     MemberQ[variables["depVars"], Head[x]],
     True,
     MemberQ[variables["depVars"], Head[y]],
     False
     ]
    ]
   ];

TimeOrderOperator[variables_Association][xlist_List, ylist_List] :=
  Module[
   {},
   If[
    Lookup[variables, "elimOrder", "explicit"] === "implicit",
    Oper[x_] := Identity[x],
    Oper[x_] := Not[x]
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
  Module[
  {schexp = schemeexpression, var = variables, t},
  If[
  	KeyExistsQ[schexp,"rhs"],
  	If[
    ! KeyExistsQ[var, "VarDOperator"],
    var = Append[var, "VarDOperator" -> DVarDOperator]
    ],
   If[
    KeyExistsQ[var, "timeVars"],
    t = var["timeVars"] // Last,
    t = var["indVars"] // Last;
    var = Append[var, "timeVars" -> {t}]
    ];
   If[
      ! KeyExistsQ[var, "VarDOperator"] || var["VarDOperator"] === DVarDOperator,
      var = Append[var, "VarDOperator" -> PartialDVarDOperator]
     ]
   ];
  If[
   ! KeyExistsQ[var, "timederivativeorder"],
   var = Append[var, "timederivativeorder" -> 1]
   ];
  If[
   KeyExistsQ[schexp, "rhs"],
   replacementrule = 
    MapThread[#1 -> MKF[var["indVars"], #2] &, {var["depVars"], 
      schexp["rhs"]}];
   schexp["exp"] = (schexp["exp"] /. replacementrule) - 
     schexp["exp"],
     If[
     	KeyExistsQ[var,"timedifference"],
     	schexp["exp"] = var["timedifference"] @ schexp["exp"],
   schexp["exp"] = (schexp["exp"] /. t :> t + 1) - schexp["exp"]
     ];
   ];
  var["timederivativeorder"] = var["timederivativeorder"] - 1;
  If[
   var["timederivativeorder"] > 0,
   TimeDifferenceOperator[var][schexp],
   If[
    KeyExistsQ[schexp, "scheme"],
    If[
     Lookup[var, "Beautify", True],
     schexp = 
      PiecewiseAssociationOperator[IntegralEquivalenceClassOperator][
       var, "exp", schexp]
     ];
    schexp = ReduceModSchemeOperator[var][schexp];
    ];
   If[
    Lookup[var, "Beautify", True],
    schexp = 
     PiecewiseAssociationOperator[IntegralEquivalenceClassOperator][
      var, "exp", schexp]
    ];
   schexp=PiecewiseAssociationFunction[Expand]["exp", schexp]
   ]
  ]
  
  
expand := Expand[#] /. Power[x_, y_] :> Power[Expand[Power[x, -y]], -1] &;

FindDiscreteConservedQuantityOperator[variables_Association][problem_] := Which[
   problem === $Failed,
   $Failed,
   Head[problem] === Piecewise, 
   PiecewiseOperatorMap[FindDiscreteConservedQuantityOperator, 
    variables, problem], True, 
   Module[{monomials, basis, glc, conservationcondition, sol}, 
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
      If[#[[1]] === $Failed || #[[2]] === $Failed, $Failed, 
        SolveUndeterminedCoefficientsOperator[
          Append[variables, "coefficients" -> #[[1, 2]]]][#[[2]]]] &, 
      PiecewiseExpand[{glc, conservationcondition}]];
      PiecewiseMap[First, PiecewiseReplace[glc, sol]]
      ]
      ];

FindDiscreteConservedQuantityBasisOperator[variables_Association][problem_] := With[
   {conservationlaws = 
     FindDiscreteConservedQuantityOperator[variables][
      problem]},
   PiecewiseMap[
     With[{coefficients = 
         DeleteDuplicates[
          Cases[#, Subscript[\[FormalA], _], {0, Infinity}]]},
       Map[Function[coeff, conservationlaws /. coeff -> 1], 
         coefficients] /. (Function[c, Rule[c, 0]] /@ 
          coefficients)] &, conservationlaws] //PiecewiseExpand// PiecewiseBeautifyOperator[variables]]; 
          
End[] (* End Private Context *)
(*EndPackage[]*)