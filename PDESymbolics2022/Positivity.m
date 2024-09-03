(* Wolfram Language package *)
(*BeginPackage["PDESymbolics2020`Positivity`"]*)
PositivityOperator::usage = 
"Not ready";

SignedFactorsOperator::usage = 
"Extracts factors that have a definite sign";

SimplifyPositivityQEOperator::usage = 
"SimlifyPositivityQEOperator[variables][expression] Positivity quantifier elimination";

SimplifyPositivityOperator::usage =  
"SimplifyPositivityOperator[variables][expression] returns necessary conditions on the parameters for the expression to be non-negative";

PositivityConditionQEOperator::usage = 
"PositivityConditionQEOperator[variables][expression] ";

SimplifyPositivityOddStepOperator::usage = 
"internal routine used in SimplifyPositivityOperator";

SimplifyPositivityEvenStepOperator::usage = 
"internal routine used in SimplifyPositivityOperator";

SimplifyPositivityExtremeEvenCoefficientsOperator::usage = 
"internal routine used in SimplifyPositivityOperator";

Begin["`Private`"]
PositivityOperator[variables_Association] :=
    Print["Not ready"]

SignedFactorsOperator[variables_Association][xp_] :=
    Which[
     xp === $Failed,
     $Failed,
    
     Head[xp]===List, 
     SignedFactorsOperator[variables]/@ xp,
    
     Head[xp] === Piecewise,
     PiecewiseOperatorMap[SignedFactorsOperator, variables, xp],
     
     (* powers are handled as follows - even powers are positive, 
     all others have the sign of what is inside - 
     this has some issues though - 
     what happens if what is inside is negative but the power is generic... \
    *)
     
     Head[xp] === Power,
     Which[
      EvenQ[Last[xp]] === True,
      Association["positive" -> {xp}, "negative" -> {}],
      OddQ[Last[xp]] === True,
      With[ {power = Last[xp], 
        factor = SignedFactorsOperator[variables][First[xp] // Factor]},
          PiecewiseMap[
           Association["positive" -> #["positive"]^power, 
             "negative" -> #["negative"]^power] &, factor]
      ],
      True
      ,
      With[ {power = Last[xp], 
        factor = SignedFactorsOperator[variables][First[xp] // Factor]},
          PiecewiseMap[
           Association["positive" -> #["positive"]^power, 
             "negative" -> {}] &, factor]
      ]
      ]
     
     ,
     
     (* products are split and studied separately *)
     
     Head[xp] === Times,
     With[ {sps = 
        PiecewiseListClean@
         PiecewiseExpand[
          SignedFactorsOperator[variables] /@ (List @@ (xp))]},
         PiecewiseMap[
          Association["positive" -> Union @@ ((#["positive"] &) /@ #), 
            "negative" -> Union @@ ((#["negative"] &) /@ #)] &, sps]
     ],
     
     (* all other cases are handled by quantifier elimination *)
     
     True,
     With[ {xpp = Factor[xp]},
         If[ xpp =!= xp, 
          
          (* if expression can be factorized then we call the funnction \
      again *)
             SignedFactorsOperator[variables][xpp],
             
             (* otherwise just handle with quantifier eliminator *)
             Module[ {positivity, negativity, pc, nc, facts},
              
              (* check when expression is positive *)
                 positivity = PositivityConditionQEOperator[variables][xp];
                 
                 (* check when expression is negative *)
                 negativity = PositivityConditionQEOperator[variables][-xp];
                 pc = Which[
                   positivity === $Failed, 
                   False, 
                   Head[positivity] =!= Piecewise,
                   positivity,
                   True, 
                    positivity // First // First // Last];
                 nc = Simplify[! pc && Which[
                     negativity === $Failed, 
                     False, 
                     Head[negativity] =!= Piecewise,
                     negativity,
                     True, 
                      negativity // First // First // Last]];
                 facts = Lookup[variables, "facts", True];
                 Piecewise[
                  {{Association["positive" -> {xp}, "negative" -> {}], pc&&facts}, 
                   {Association["positive" -> {}, "negative" -> {xp}], nc&&facts},
                   {Association["positive" -> {}, "negative" -> {}], 
                    Simplify[(! pc) && (! nc) && facts ]}
                   }, $Failed]
             ]
         ]
     ]
     ]








SimplifyPositivityOperator[variables_Association][oproblem_] :=
    With[ {problem = If[ Head[oproblem]===Association,
                         PiecewiseExpandAssociation[oproblem],
                         oproblem
                     ]},
        Which[
         problem === $Failed,
         $Failed,
         Head[problem] === Piecewise,
         PiecewiseOperatorMap[SimplifyPositivityOperator, variables, 
          problem],
         Head[problem] =!= Association,
         SimplifyPositivityOperator[variables][
          Association[
              "expression" -> problem,
              "eliminator"->Lookup[variables,"eliminator",True]
              ]],
         True,
         Module[ {fproblem, coefficients},
             coefficients = Lookup[problem, "coefficients", 
               DeleteDuplicates@
                Cases[Lookup[problem, "expression", 0], 
                 Subscript[\[FormalA], _], {0, Infinity}]];
             fproblem = 
              FixedPoint[
               PiecewiseSimplifyOperator[variables]@
                 SimplifyPositivityEvenStepOperator[variables]@
                  PiecewiseSimplifyOperator[variables]@
                   SimplifyPositivityOddStepOperator[variables]@# &,
               Append[
                problem, {"eliminator" -> False, 
                 "coefficients" -> coefficients, 
                 "facts" -> Lookup[problem, "facts", True]}]];
             
             (*Print[fproblem];*)
             PiecewiseMap[KeyDrop["eliminator"],#]&@If[ Lookup[problem, "eliminator", True],
                                                        ConditionalPiecewiseMap[
                                                         With[ {extremevencoefficients = 
                                                             Lookup[SimplifyPositivityExtremeEvenCoefficientsOperator[
                                                                variables][#1], "extremecoefficients", {}]},
                                                           (*Print[#1];
                                                           Print[extremevencoefficients];
                                                           Print[And@@(Function[z,(z\[GreaterEqual]0)]/@
                                                           extremevencoefficients)];*)
                                                           
                                                           (*
                                                           Print[extremevencoefficients];
                                                   *)
                                                             Piecewise[{{#1, 
                                                                Reduce[#2 && (And @@ (Function[z, (z >= 0)] /@ 
                                                                      extremevencoefficients)),
                                                                 Lookup[variables, "domain", Reals]]}}, $Failed]
                                                         ] &, 
                                                         fproblem],
                                                        fproblem
                                                    ]
         ]
        ]
    ];




SimplifyPositivityOddStepOperator[variables_Association][problem_] :=
    Which[
    problem === $Failed,
    $Failed,
    Head[problem] === Piecewise,
    PiecewiseOperatorMap[SimplifyPositivityOddStepOperator, variables, 
    problem],
    True,
    Module[ {expr, expralt, vars, allvars, candidates, candidatessingle, candidateslow,candidateslowt, candidateshigh,
       candidateshight,  oddcandidateshigh,  oddcandidateslow, oddcandidatessingle,  
        oddcandidates, 
    (* candidatevariables,*)
     candidatevariableshigh,
     candidatevariableslow,
     candidatevariablessingle,
      freevariableshigh,
      freevariableslow,
      freevariablessingle,
     (* freevariables,
      reducedfree,*)
      reducedfreehigh,
      reducedfreelow,
      reducedfreesingle,
      (*freeoddcandidates,*)
      freeoddcandidateshigh,
      freeoddcandidateslow,
      freeoddcandidatessingle,
       sol,  facts, FA, 
     EE, freeoddcandidates},
        expr = Expand@problem["expression"];
        expralt = Select[{expr} // Flatten, # =!= 0 &];
        If[ expralt === {},
            problem,
            (*vars = getVars[expralt, Lookup[variables, "depVars", {}]];*)
            vars = GetVarsOperator[variables][expralt];
            allvars = Union[vars, Lookup[variables, "indVars", {}]];
            facts = Lookup[variables, "facts", True];
            candidateslowt = 
             Flatten[Map[
               Function[{xp}, 
                Union @@ 
                 Map[Part[CoefficientRules[xp, #], {-1}] /. 
                    Rule[{j_Integer}, coeff_] :> {j, #, coeff} &, allvars]], 
               expralt], 1];
            candidateshight = 
             Flatten[Map[
               Function[{xp}, 
                Union @@ 
                 Map[Part[CoefficientRules[xp, #], { 1}] /. 
                    Rule[{j_Integer}, coeff_] :> {j, #, coeff} &, allvars]], 
               expralt], 1];
            candidatessingle = Intersection[candidateslowt, candidateshight];
            candidateshigh = Complement[candidateshight,candidatessingle];
            candidateslow = Complement[candidateslowt,candidatessingle];
            candidates = Union[candidateslow, candidateshigh, candidatessingle];
            
          (*  Print["Odd step"];
            Print[expralt];*)
            (*Print[candidates];*)
           (* Print[candidateslow];*)
           (* Print[candidateshigh];*)
            (*Print[candidatessingle];*)
            If[ candidates =!= {},
                oddcandidateslow = Select[candidateslow, OddQ@First@# &];
                oddcandidateshigh = Select[candidateshigh, OddQ@First@# &];
                oddcandidatessingle = Select[candidatessingle, OddQ@First@# &],
                Return[problem]
            ];
            oddcandidates = Union[oddcandidateslow, oddcandidateshigh, oddcandidatessingle];
            If[ oddcandidates === {},
                Return[problem]
            ];
            
            (* the principle is the following: *)
            (* for high order candidates, if the corresponding variable can take values arbitrarily large close to  +infty and
            -infty then the corresponding coefficient mustbe zero *)
            (* for low order candidates, if the corresponding variable can take values arbitrarily close to  0 with positive and
            negative signs, then the corresponding coefficient mustbe zero *)
            (* for single candidates, if the corresponding variable can take positive and negative values
            , then the corresponding coefficient must be zero *)
            FA :=
                ForAll[#1, #2] &;
            EE :=
                Exists[#1, #2] &;
         
         
         (* high variables *)
            candidatevariableshigh = If[ oddcandidateshigh=!={},
                                         DeleteDuplicates[oddcandidateshigh[[All, 2]]],
                                         {}
                                     ];
            
         (* this is where the magic happens, checks if variables achieve \pm infinity *)
            reducedfreehigh = {#, 
                Reduce[facts && 
                  Reduce[FA[Complement[allvars, {#}], 
                    Implies[Reduce[EE[#, facts], Reals], 
                    Reduce[FA[\[FormalB],EE[# ,#<\[FormalB]&& facts]], Reals]&&
                    Reduce[FA[\[FormalB],EE[# ,#>\[FormalB]&& facts]], Reals]]], Reals], Reals]} & /@ 
              candidatevariableshigh;
            freevariableshigh = 
             Select[reducedfreehigh, 
               FullSimplify[Equivalent[#[[2]], facts]] === True &][[All, 
               1]];
            freeoddcandidateshigh = 
             Select[oddcandidateshigh, MemberQ[freevariableshigh, #[[2]]] &];
             
            (* Print[ freeoddcandidateshigh];
             Print["zob"];*)
        
         (* low variables *)
            candidatevariableslow = If[ oddcandidateslow=!={},
                                        DeleteDuplicates[oddcandidateslow[[All, 2]]],
                                        {}
                                    ];
            
         (* this is where the magic happens, checks if variables achieve \pm 0  *)
            reducedfreelow = {#, 
                Reduce[facts && 
                  Reduce[FA[Complement[allvars, {#}], 
                    Implies[Reduce[EE[#, facts], Reals], 
                    Reduce[FA[\[FormalB],EE[# , \[FormalB]<=0||( 0<#<\[FormalB]&& facts)]], Reals]&&
                    Reduce[FA[\[FormalB],EE[# , \[FormalB]<=0||( 0>#>-\[FormalB]&& facts)]], Reals]]], Reals], Reals]} & /@ 
              candidatevariableslow;
            freevariableslow = 
             Select[reducedfreelow, 
               FullSimplify[Equivalent[#[[2]], facts]] === True &][[All, 
               1]];
            freeoddcandidateslow = 
             Select[oddcandidateslow, MemberQ[freevariableslow, #[[2]]] &];
           
          
       (* single variables *)
            candidatevariablessingle =  If[ oddcandidatessingle=!={},
                                            DeleteDuplicates[oddcandidatessingle[[All, 2]]],
                                            {}
                                        ];
            
         (* this is where the magic happens, checks if variables achieve \pm infinity *)
            reducedfreesingle = {#, 
                Reduce[facts && 
                  Reduce[FA[Complement[allvars, {#}], 
                    Implies[Reduce[EE[#, facts], Reals], 
                    Reduce[EE[# ,#>0&& facts], Reals]&&
                    Reduce[EE[# ,#<0&& facts], Reals]]], Reals], Reals]} & /@ 
              candidatevariablessingle;
            freevariablessingle = 
             Select[reducedfreesingle, 
               FullSimplify[Equivalent[#[[2]], facts]] === True &][[All, 
               1]];
            freeoddcandidatessingle = 
             Select[oddcandidatessingle, MemberQ[freevariablessingle, #[[2]]] &];
           
           
           
          
            
            (* putting it all together *)
            freeoddcandidates = Union[freeoddcandidateshigh, freeoddcandidateslow, freeoddcandidatessingle];
            
           (* Print[freeoddcandidates];*)
            If[ freeoddcandidates === {},
                Return[problem]
            ];
            
            (* solve undetermined coefficients *)
            sol = SolveUndeterminedCoefficientsOperator[variables][
              Association[{
                "expression" -> freeoddcandidates[[All, 3]], 
                "coefficients" -> Lookup[problem, "coefficients", {}]
                }]];
            
            
            (* replace back in the expression and append rules *)
            PiecewiseMap[
             Function[{rule},
              Association[
               "expression" -> expr /. rule,
               "rules" -> Join[Lookup[problem, "rules", {}], rule],
               "coefficients" -> Select[
                 
                 Lookup[problem, 
                  "coefficients", {}], ! MemberQ[Keys@rule, #] &]
               ]
              ],
             sol]
        ]
    ]
    ];

SimplifyPositivityEvenStepOperator[variables_Association][problem_] :=
    Which[
    problem === $Failed,
    $Failed,
    Head[problem] === Piecewise,
    PiecewiseOperatorMap[SimplifyPositivityEvenStepOperator, variables,
     problem],
    True,
    Module[ {expr, expralt, vars, candidates,
       candidatessingle, candidateslow,candidateslowt, candidateshigh,
       candidateshight,
       oddcandidateshigh,  oddcandidateslow, oddcandidatessingle,  
       evencandidateshigh,  evencandidateslow, evencandidatessingle,  
         dependentcandidates,
        evencandidatevariableshigh,
    reducedfreeevenhigh,
     freevariablesevenhigh,
     freeevencandidateshigh,
     evencandidatevariableslow,
    reducedfreeevenlow,
    freevariablesevenlow,
    freeevencandidateslow,
    evencandidatevariablessingle,
    reducedfreeevensingle,
    freevariablesevensingle,  
    freeevencandidatessingle,      
     sol, allvars, FA, EE, 
     oddcandidatevariableshigh,
    reducedfreeoddhighpositive,
    reducedfreeoddhighnegative,
    freevariablesoddhighpositive,
    freevariablesoddhighnegative,
    common,
    freeoddcandidateshighpositive,
    freeoddcandidateshighnegative,
    oddcandidatevariableslow,
    reducedfreeoddlowpositive,
    reducedfreeoddlownegative,
    freevariablesoddlowpositive,
    freevariablesoddlownegative,
    freeoddcandidateslowpositive,
    freeoddcandidateslownegative,
    oddcandidatevariablessingle,
    reducedfreeoddsinglepositive,
    reducedfreeoddsinglenegative,
    freevariablesoddsinglepositive,
    freevariablesoddsinglenegative,
    freeoddcandidatessinglepositive,
    freeoddcandidatessinglenegative,
     freecandidates,
      facts},
        expr = Expand@problem["expression"];
        facts = Lookup[variables, "facts", True];
        expralt = Select[{expr} // Flatten, # =!= 0 &];
        If[ expralt === {},
            problem,
            (*vars = getVars[expr, Lookup[variables, "depVars", {}]];*)
            vars = GetVarsOperator[variables][expr];
            allvars = Union[vars, Lookup[variables, "indVars", {}]];
            candidateslowt = 
             Flatten[Map[
               Function[{xp}, 
                Union @@ 
                 Map[Part[CoefficientRules[xp, #], {-1}] /. 
                    Rule[{j_Integer}, coeff_] :> {j, #, coeff} &, allvars]], 
               expralt], 1];
            candidateshight = 
             Flatten[Map[
               Function[{xp}, 
                Union @@ 
                 Map[Part[CoefficientRules[xp, #], { 1}] /. 
                    Rule[{j_Integer}, coeff_] :> {j, #, coeff} &, allvars]], 
               expralt], 1];
            candidatessingle = Intersection[candidateslowt, candidateshight];
            candidateshigh = Complement[candidateshight,candidatessingle];
            candidateslow = Complement[candidateslowt,candidatessingle];
            candidates = Union[candidateslow, candidateshigh, candidatessingle];
            
         
         (* here we need to select both the even and the odd *)
         (* out of the even, the ones that take arbitarily large values for high or arbitrarily close
         to zero for low, must be non-negative, if single, the corresponding coefficient must be non-negative also
         *)
         (* out of the odd, the if the high-order takes arbitrarily large values (+infty) then the corresponding coeff
         must be >=0, if it takes arbitrarily small values (-infty) the  corresponding coeff
         must be <=0, similar argument for "low", for single odd -> if xp takes positive values then coeff positive if
         xp takes negative values then negative *)
        
        
       (* Print[candidatessingle];*)
        
        (* dependentcandidates is a function that selects the candidates that are
        dependent on at least one of the variables *)
            dependentcandidates = Function[candidts, Select[candidts, 
             ! FreeQ[#[[3]], Alternatives @@ allvars, {0, Infinity}] &]]; 
        
        (* here we split the candidates in the various categories *)
            If[ candidates =!= {},
                evencandidateshigh = 
                  dependentcandidates@Select[Select[candidateshigh, 
                    EvenQ@First@# &], ! MemberQ[expralt, #[[3]]] &];
                oddcandidateshigh = 
                 dependentcandidates@Select[candidateshigh, 
                   OddQ@First@# &];
                evencandidateslow = 
                 dependentcandidates@Select[Select[candidateslow, 
                   EvenQ@First@# &], ! MemberQ[expralt, #[[3]]] &];
                oddcandidateslow = 
                 dependentcandidates@Select[candidateslow, 
                   OddQ@First@# &];
                evencandidatessingle = 
                 dependentcandidates@Select[Select[candidatessingle, 
                   EvenQ@First@# &], ! MemberQ[expralt, #[[3]]] &];
                oddcandidatessingle = 
                 dependentcandidates@Select[candidatessingle, 
                   OddQ@First@# &];,
                Return[problem]
            ];


           (* Print[evencandidates];*)

       (*
           Print[evencandidateshigh];
           Print[evencandidateslow];
           Print[evencandidatessingle]; 
        *)
            If[ Union[evencandidateshigh,evencandidateslow, evencandidatessingle, oddcandidateshigh,oddcandidateslow, oddcandidatessingle] === {},
                Return[problem]
            ];
            FA :=
                ForAll[#1, #2] &;
            EE :=
                Exists[#1, #2] &;


        (* case by case analysis *)

        (* high even *)
        (* we select the variables that assume arbitrarily large values (when squared) *)
            evencandidatevariableshigh = If[ evencandidateshigh==={},
                                             {},
                                             DeleteDuplicates[evencandidateshigh[[All, 2]]]
                                         ];
            reducedfreeevenhigh = {#, 
                     Reduce[facts && 
                       Reduce[FA[Complement[allvars, {#}], 
                         Implies[Reduce[EE[#, facts], Reals], 
                          Reduce[FA[\[FormalB],EE[# ,#^2>\[FormalB]&& facts]], Reals]
                          ]], Reals], Reals]} & /@ 
                   evencandidatevariableshigh;
            freevariablesevenhigh = 
                  Select[reducedfreeevenhigh, 
                    FullSimplify[Equivalent[#[[2]], facts]] === True &][[All, 
                    1]];
            freeevencandidateshigh = 
                  Select[evencandidateshigh, MemberQ[freevariablesevenhigh , #[[2]]] &];

            (*Print["high"];
            Print[evencandidatevariableshigh];
            Print[freevariablesevenhigh];
            Print[freeevencandidateshigh];*)


            (* low even *)
            (* we select the variables that assume arbitrarily small values (when squared) *)
            evencandidatevariableslow = If[ evencandidateslow==={},
                                            {},
                                            DeleteDuplicates[evencandidateslow[[All, 2]]]
                                        ];
            reducedfreeevenlow = {#, 
                     Reduce[facts && 
                       Reduce[FA[Complement[allvars, {#}], 
                         Implies[Reduce[EE[#, facts], Reals], 
                          Reduce[FA[\[FormalB],EE[# ,\[FormalB]<=0||(#^2<\[FormalB]&& facts)]], Reals]
                          ]], Reals], Reals]} & /@ 
                   evencandidatevariableslow;
            freevariablesevenlow = 
                  Select[reducedfreeevenlow, 
                    FullSimplify[Equivalent[#[[2]], facts]] === True &][[All, 
                    1]];
            freeevencandidateslow = 
                  Select[evencandidateslow, MemberQ[freevariablesevenlow , #[[2]]] &];

            (*Print["low"];
            Print[reducedfreeevenlow];
            Print[evencandidatevariableslow];
            Print[freevariablesevenlow];
            Print[freeevencandidateslow];
            *)

            (* single even *)
            (* we select the variables that take a non-zero value *)
            evencandidatevariablessingle = If[ evencandidatessingle==={},
                                               {},
                                               DeleteDuplicates[evencandidatessingle[[All, 2]]]
                                           ];
            reducedfreeevensingle = {#, 
                     Reduce[facts && 
                       Reduce[FA[Complement[allvars, {#}], 
                         Implies[Reduce[EE[#, facts], Reals], 
                          Reduce[EE[# ,#!=0 && facts], Reals]
                          ]], Reals], Reals]} & /@ 
                   evencandidatevariablessingle;
            freevariablesevensingle = 
                  Select[reducedfreeevensingle, 
                    FullSimplify[Equivalent[#[[2]], facts]] === True &][[All, 
                    1]];
            freeevencandidatessingle = 
                  Select[evencandidatessingle, MemberQ[freevariablesevensingle , #[[2]]] &];


            (*Print["single"];
            Print[evencandidatevariablessingle];
            Print[freevariablesevensingle];
            Print[freeevencandidatessingle];*)



            (* ODD CASES *)

            (** odd high positive and odd high negative **)
            oddcandidatevariableshigh = If[ oddcandidateshigh==={},
                                            {},
                                            DeleteDuplicates[oddcandidateshigh[[All, 2]]]
                                        ];

            (*
            Print[oddcandidateshigh];*)
            reducedfreeoddhighpositive = {#, 
                     Reduce[facts && 
                       Reduce[FA[Complement[allvars, {#}], 
                         Implies[Reduce[EE[#, facts], Reals], 
                          Reduce[FA[\[FormalB],EE[# ,#>\[FormalB]&& facts]], Reals]
                          ]], Reals], Reals]} & /@ 
                   oddcandidatevariableshigh;
            reducedfreeoddhighnegative = {#, 
                     Reduce[facts && 
                       Reduce[FA[Complement[allvars, {#}], 
                         Implies[Reduce[EE[#, facts], Reals], 
                          Reduce[FA[\[FormalB],EE[# ,#<\[FormalB]&& facts]], Reals]
                          ]], Reals], Reals]} & /@ 
                   oddcandidatevariableshigh;
            freevariablesoddhighpositive = 
                  Select[reducedfreeoddhighpositive, 
                    FullSimplify[Equivalent[#[[2]], facts]] === True &][[All, 
                    1]];
            freevariablesoddhighnegative = 
                  Select[reducedfreeoddhighnegative, 
                    FullSimplify[Equivalent[#[[2]], facts]] === True &][[All, 
                    1]];        

            (* the variables that are common should be handled by the odd simplifier becuase their coefficients must vanish *)
            common = Intersection[freevariablesoddhighpositive, freevariablesoddhighnegative];   

            (*Print[common];
            Print[freevariablesoddhighnegative];*)
            freeoddcandidateshighpositive = 
                  Select[oddcandidateshigh, MemberQ[Complement[freevariablesoddhighpositive, common] , #[[2]]] &];

            (*Print[freeoddcandidateshighpositive];*)
            freeoddcandidateshighnegative = 
                  {#[[1]],#[[2]],-#[[3]]}&/@Select[oddcandidateshigh, MemberQ[Complement[freevariablesoddhighnegative, common]  , #[[2]]] &];

            (*Print[freeoddcandidateshighnegative];*)

            (** odd low positive and odd low negative **)
            oddcandidatevariableslow = If[ oddcandidateslow==={},
                                           {},
                                           DeleteDuplicates[oddcandidateslow[[All, 2]]]
                                       ];

            (*Print[oddcandidateslow];*)
            reducedfreeoddlowpositive = {#, 
                     Reduce[facts && 
                       Reduce[FA[Complement[allvars, {#}], 
                         Implies[Reduce[EE[#, facts], Reals], 
                          Reduce[FA[\[FormalB],EE[# ,\[FormalB]<=0||(0<#<\[FormalB]&& facts)]], Reals]
                          ]], Reals], Reals]} & /@ 
                   oddcandidatevariableslow;
            reducedfreeoddlownegative = {#, 
                     Reduce[facts && 
                       Reduce[FA[Complement[allvars, {#}], 
                         Implies[Reduce[EE[#, facts], Reals], 
                          Reduce[FA[\[FormalB],EE[# ,\[FormalB]<=0||(0>#>-\[FormalB]&& facts)]], Reals]
                          ]], Reals], Reals]} & /@ 
                   oddcandidatevariableslow;
            freevariablesoddlowpositive = 
                  Select[reducedfreeoddlowpositive, 
                    FullSimplify[Equivalent[#[[2]], facts]] === True &][[All, 
                    1]];
            freevariablesoddlownegative = 
                  Select[reducedfreeoddlownegative, 
                    FullSimplify[Equivalent[#[[2]], facts]] === True &][[All, 
                    1]];        

            (* the variables that are common should be handled by the odd simplifier becuase their coefficients must vanish *)
            common = Intersection[freevariablesoddlowpositive, freevariablesoddlownegative];   

            (*Print[common];
            Print[freevariablesoddhighnegative];*)
            freeoddcandidateslowpositive = 
                  Select[oddcandidateslow, MemberQ[Complement[freevariablesoddlowpositive, common] , #[[2]]] &];

            (*Print[freeoddcandidateshighpositive];*)
            freeoddcandidateslownegative = 
                  {#[[1]],#[[2]],-#[[3]]}&/@Select[oddcandidateslow, MemberQ[Complement[freevariablesoddlownegative, common]  , #[[2]]] &];

            (*Print[freeoddcandidateslownegative];*)



            (** odd single positive and single negative **)
            oddcandidatevariablessingle = If[ oddcandidatessingle==={},
                                              {},
                                              DeleteDuplicates[oddcandidatessingle[[All, 2]]]
                                          ];

            (*Print[oddcandidatessingle];*)
            reducedfreeoddsinglepositive = {#, 
                     Reduce[facts && 
                       Reduce[FA[Complement[allvars, {#}], 
                         Implies[Reduce[EE[#, facts], Reals], 
                          Reduce[EE[# ,#>0 && facts], Reals]
                          ]], Reals], Reals]} & /@ 
                   oddcandidatevariablessingle;
            reducedfreeoddsinglenegative = {#, 
                     Reduce[facts && 
                       Reduce[FA[Complement[allvars, {#}], 
                         Implies[Reduce[EE[#, facts], Reals], 
                          Reduce[EE[# ,#<0 && facts], Reals]
                          ]], Reals], Reals]} & /@ 
                   oddcandidatevariablessingle;
            freevariablesoddsinglepositive = 
                  Select[reducedfreeoddsinglepositive, 
                    FullSimplify[Equivalent[#[[2]], facts]] === True &][[All, 
                    1]];
                    
            (*Print[freevariablesoddsinglepositive];  *)
            freevariablesoddsinglenegative = 
                  Select[reducedfreeoddsinglenegative, 
                    FullSimplify[Equivalent[#[[2]], facts]] === True &][[All, 
                    1]];        

            (* the variables that are common should be handled by the odd simplifier becuase their coefficients must vanish *)
            common = Intersection[freevariablesoddsinglepositive, freevariablesoddsinglenegative];   

            (*Print[common];
            Print[freevariablesoddsinglepositive];*)
            freeoddcandidatessinglepositive = 
                  Select[oddcandidatessingle, MemberQ[Complement[freevariablesoddsinglepositive, common] , #[[2]]] &];

            (*Print[freeoddcandidateshighpositive];*)
            freeoddcandidatessinglenegative = 
                  {#[[1]],#[[2]],-#[[3]]}&/@Select[oddcandidatessingle, MemberQ[Complement[freevariablesoddsinglenegative, common]  , #[[2]]] &];

            (*Print[freeoddcandidatessinglenegative];*)





            (*****************)
            freecandidates = Union[freeevencandidateshigh, freeevencandidateslow, freeevencandidatessingle,freeoddcandidateshighpositive ,
                freeoddcandidateshighnegative,    freeoddcandidateslowpositive ,freeoddcandidateslownegative,
                    freeoddcandidatessinglepositive ,freeoddcandidatessinglenegative ];     


            (*Print[freecandidates];*)
            (*Return[problem];*)
            If[ freecandidates === {},
                Return[problem]
            ];    
               
               
               (* select the candidates that assumptions don't imply they have \
          a definite sign -for all values of the variables *)
               (* 
               TO BE DONE *)
            sol = SimplifyPositivityOperator[variables][
              Association[
               "expression" -> ((*dependentevencandidates*) freecandidates[[All, 3]]),
               "coefficients" -> Lookup[problem, "coefficients", {}],
               "eliminator" -> False,
               "rules" -> {}
               ]
              ];
            PiecewiseMap[
             Association[
               "eliminator" -> False,
               "expression" -> expr /. #["rules"],
               "rules" -> 
                Join[Lookup[problem, "rules", {}], Lookup[#, "rules", {}]],
               "coefficients" -> Select[
                 Lookup[problem, "coefficients", {}], 
                 Function[z, ! MemberQ[Keys@#["rules"], z]]]
               ] &, sol]
        ]
    ]
    ];

(* NEW VERSION *)

SimplifyPositivityExtremeEvenCoefficientsOperator[variables_Association][problem_] :=
    Which[
     problem === $Failed,
     $Failed,
     Head[problem] === Piecewise, 
     PiecewiseOperatorMap[
      SimplifyPositivityExtremeEvenCoefficientsOperator, variables, problem],
     True,
     Module[ {expr, expralt, vars, candidates, candidatessingle, 
       candidateslow, candidateslowt, candidateshigh, candidateshight, 
       oddcandidateshigh, oddcandidateslow, oddcandidatessingle, 
       evencandidateshigh, evencandidateslow, evencandidatessingle, 
       (*dependentcandidates,*) evencandidatevariableshigh, 
       reducedfreeevenhigh, freevariablesevenhigh, 
       freeevencandidateshigh, evencandidatevariableslow, 
       reducedfreeevenlow, freevariablesevenlow, freeevencandidateslow, 
       evencandidatevariablessingle, reducedfreeevensingle, 
       freevariablesevensingle, freeevencandidatessingle, allvars, 
       FA, EE, oddcandidatevariableshigh, reducedfreeoddhighpositive, 
       reducedfreeoddhighnegative, freevariablesoddhighpositive, 
       freevariablesoddhighnegative, common, 
       freeoddcandidateshighpositive, freeoddcandidateshighnegative, 
       oddcandidatevariableslow, reducedfreeoddlowpositive, 
       reducedfreeoddlownegative, freevariablesoddlowpositive, 
       freevariablesoddlownegative, freeoddcandidateslowpositive, 
       freeoddcandidateslownegative, oddcandidatevariablessingle, 
       reducedfreeoddsinglepositive, reducedfreeoddsinglenegative, 
       freevariablesoddsinglepositive, freevariablesoddsinglenegative, 
       freeoddcandidatessinglepositive, freeoddcandidatessinglenegative,
        freecandidates, facts,
       thedependentcandidates,
       theindependependentcandidates },
         expr = Expand@problem["expression"];
         facts = Lookup[variables, "facts", True];
         expralt = Select[{expr} // Flatten, # =!= 0 &];
         If[ expralt === {},
             problem,
             (*vars = getVars[expr, Lookup[variables, "depVars", {}]];*)
             vars = GetVarsOperator[variables][expr];
             allvars = Union[vars, Lookup[variables, "indVars", {}]];
             candidateslowt = 
              Flatten[Map[
                Function[{xp}, 
                 Union @@ 
                  Map[Part[CoefficientRules[xp, #], {-1}] /. 
                     Rule[{j_Integer}, coeff_] :> {j, #, coeff} &, allvars]], 
                expralt], 1];
             candidateshight = 
              Flatten[Map[
                Function[{xp}, 
                 Union @@ 
                  Map[Part[CoefficientRules[xp, #], { 1}] /. 
                     Rule[{j_Integer}, coeff_] :> {j, #, coeff} &, allvars]], 
                expralt], 1];
             candidatessingle = Intersection[candidateslowt, candidateshight];
             candidateshigh = Complement[candidateshight,candidatessingle];
             candidateslow = Complement[candidateslowt,candidatessingle];
             candidates = Union[candidateslow, candidateshigh, candidatessingle];
         (*    
             Print["candidates = ",candidates];
        *)     
          
          (* here we need to select both the even and the odd *)
          (* out of the even, the ones that take arbitarily large values for high or arbitrarily close
          to zero for low, must be non-negative, if single, the corresponding coefficient must be non-negative also
          *)
          (* out of the odd, the if the high-order takes arbitrarily large values (+infty) then the corresponding coeff
          must be >=0, if it takes arbitrarily small values (-infty) the  corresponding coeff
          must be <=0, similar argument for "low", for single odd -> if xp takes positive values then coeff positive if
          xp takes negative values then negative *)
         
         
        (* Print[candidatessingle];*)
         
         (* dependentcandidates is a function that selects the candidates that are
         dependent on at least one of the variables *)
          
        (*      dependentcandidates = Function[candidts, Select[candidts, 
               ! FreeQ[#[[3]], Alternatives @@ allvars, {0, Infinity}] &]]; *)
          
          (* here we split the candidates in the various categories *)
             If[ candidates =!= {},
                 evencandidateshigh = 
                   Select[Select[candidateshigh, 
                     EvenQ@First@# &], ! MemberQ[expralt, #[[3]]] &];
                 oddcandidateshigh = Select[candidateshigh, 
                    OddQ@First@# &];
                 evencandidateslow = Select[Select[candidateslow, 
                    EvenQ@First@# &], ! MemberQ[expralt, #[[3]]] &];
                 oddcandidateslow = 
                  Select[candidateslow, 
                    OddQ@First@# &];
                 evencandidatessingle = 
                  Select[Select[candidatessingle, 
                    EvenQ@First@# &], ! MemberQ[expralt, #[[3]]] &];
                 oddcandidatessingle = 
                  Select[candidatessingle, 
                    OddQ@First@# &];,
                 Return[problem]
             ];


            (* Print[evencandidates];*)

        (*
            Print[evencandidateshigh];
            Print[evencandidateslow];
            Print[evencandidatessingle]; 
         *)
        (*
        Print["selected candidates = ",Union[evencandidateshigh,evencandidateslow, evencandidatessingle, oddcandidateshigh,oddcandidateslow, oddcandidatessingle]];
        *)
             If[ Union[evencandidateshigh,evencandidateslow, evencandidatessingle, oddcandidateshigh,oddcandidateslow, oddcandidatessingle] === {},
                 Return[problem]
             ];
             FA :=
                 ForAll[#1, #2] &;
             EE :=
                 Exists[#1, #2] &;


         (* case by case analysis *)

         (* high even *)
         (* we select the variables that assume arbitrarily large values (when squared) *)
             evencandidatevariableshigh = If[ evencandidateshigh==={},
                                              {},
                                              DeleteDuplicates[evencandidateshigh[[All, 2]]]
                                          ];
             reducedfreeevenhigh = {#, 
                      Reduce[facts && 
                        Reduce[FA[Complement[allvars, {#}], 
                          Implies[Reduce[EE[#, facts], Reals], 
                           Reduce[FA[\[FormalB],EE[# ,#^2>\[FormalB]&& facts]], Reals]
                           ]], Reals], Reals]} & /@ 
                    evencandidatevariableshigh;
             freevariablesevenhigh = 
                   Select[reducedfreeevenhigh, 
                     FullSimplify[Equivalent[#[[2]], facts]] === True &][[All, 
                     1]];
             freeevencandidateshigh = 
                   Select[evencandidateshigh, MemberQ[freevariablesevenhigh , #[[2]]] &];

             (*Print["high"];
             Print[evencandidatevariableshigh];
             Print[freevariablesevenhigh];
             Print[freeevencandidateshigh];*)


             (* low even *)
             (* we select the variables that assume arbitrarily small values (when squared) *)
             evencandidatevariableslow = If[ evencandidateslow==={},
                                             {},
                                             DeleteDuplicates[evencandidateslow[[All, 2]]]
                                         ];
             reducedfreeevenlow = {#, 
                      Reduce[facts && 
                        Reduce[FA[Complement[allvars, {#}], 
                          Implies[Reduce[EE[#, facts], Reals], 
                           Reduce[FA[\[FormalB],EE[# ,\[FormalB]<=0||(#^2<\[FormalB]&& facts)]], Reals]
                           ]], Reals], Reals]} & /@ 
                    evencandidatevariableslow;
             freevariablesevenlow = 
                   Select[reducedfreeevenlow, 
                     FullSimplify[Equivalent[#[[2]], facts]] === True &][[All, 
                     1]];
             freeevencandidateslow = 
                   Select[evencandidateslow, MemberQ[freevariablesevenlow , #[[2]]] &];

             (*Print["low"];
             Print[reducedfreeevenlow];
             Print[evencandidatevariableslow];
             Print[freevariablesevenlow];
             Print[freeevencandidateslow];
             *)

             (* single even *)
             (* we select the variables that take a non-zero value *)
             evencandidatevariablessingle = If[ evencandidatessingle==={},
                                                {},
                                                DeleteDuplicates[evencandidatessingle[[All, 2]]]
                                            ];
             reducedfreeevensingle = {#, 
                      Reduce[facts && 
                        Reduce[FA[Complement[allvars, {#}], 
                          Implies[Reduce[EE[#, facts], Reals], 
                           Reduce[EE[# ,#!=0 && facts], Reals]
                           ]], Reals], Reals]} & /@ 
                    evencandidatevariablessingle;
             freevariablesevensingle = 
                   Select[reducedfreeevensingle, 
                     FullSimplify[Equivalent[#[[2]], facts]] === True &][[All, 
                     1]];
             freeevencandidatessingle = 
                   Select[evencandidatessingle, MemberQ[freevariablesevensingle , #[[2]]] &];


             (*Print["single"];
             Print[evencandidatevariablessingle];
             Print[freevariablesevensingle];
             Print[freeevencandidatessingle];*)



             (* ODD CASES *)

             (** odd high positive and odd high negative **)
             oddcandidatevariableshigh = If[ oddcandidateshigh==={},
                                             {},
                                             DeleteDuplicates[oddcandidateshigh[[All, 2]]]
                                         ];

             (*
             Print[oddcandidateshigh];*)
             reducedfreeoddhighpositive = {#, 
                      Reduce[facts && 
                        Reduce[FA[Complement[allvars, {#}], 
                          Implies[Reduce[EE[#, facts], Reals], 
                           Reduce[FA[\[FormalB],EE[# ,#>\[FormalB]&& facts]], Reals]
                           ]], Reals], Reals]} & /@ 
                    oddcandidatevariableshigh;
             reducedfreeoddhighnegative = {#, 
                      Reduce[facts && 
                        Reduce[FA[Complement[allvars, {#}], 
                          Implies[Reduce[EE[#, facts], Reals], 
                           Reduce[FA[\[FormalB],EE[# ,#<\[FormalB]&& facts]], Reals]
                           ]], Reals], Reals]} & /@ 
                    oddcandidatevariableshigh;
             freevariablesoddhighpositive = 
                   Select[reducedfreeoddhighpositive, 
                     FullSimplify[Equivalent[#[[2]], facts]] === True &][[All, 
                     1]];
             freevariablesoddhighnegative = 
                   Select[reducedfreeoddhighnegative, 
                     FullSimplify[Equivalent[#[[2]], facts]] === True &][[All, 
                     1]];        

             (* the variables that are common should be handled by the odd simplifier becuase their coefficients must vanish *)
             common = Intersection[freevariablesoddhighpositive, freevariablesoddhighnegative];   

             (*Print[common];
             Print[freevariablesoddhighnegative];*)
             freeoddcandidateshighpositive = 
                   Select[oddcandidateshigh, MemberQ[Complement[freevariablesoddhighpositive, common] , #[[2]]] &];

             (*Print[freeoddcandidateshighpositive];*)
             freeoddcandidateshighnegative = 
                   {#[[1]],#[[2]],-#[[3]]}&/@Select[oddcandidateshigh, MemberQ[Complement[freevariablesoddhighnegative, common]  , #[[2]]] &];

             (*Print[freeoddcandidateshighnegative];*)

             (** odd low positive and odd low negative **)
             oddcandidatevariableslow = If[ oddcandidateslow==={},
                                            {},
                                            DeleteDuplicates[oddcandidateslow[[All, 2]]]
                                        ];

             (*Print[oddcandidateslow];*)
             reducedfreeoddlowpositive = {#, 
                      Reduce[facts && 
                        Reduce[FA[Complement[allvars, {#}], 
                          Implies[Reduce[EE[#, facts], Reals], 
                           Reduce[FA[\[FormalB],EE[# ,\[FormalB]<=0||(0<#<\[FormalB]&& facts)]], Reals]
                           ]], Reals], Reals]} & /@ 
                    oddcandidatevariableslow;
             reducedfreeoddlownegative = {#, 
                      Reduce[facts && 
                        Reduce[FA[Complement[allvars, {#}], 
                          Implies[Reduce[EE[#, facts], Reals], 
                           Reduce[FA[\[FormalB],EE[# ,\[FormalB]<=0||(0>#>-\[FormalB]&& facts)]], Reals]
                           ]], Reals], Reals]} & /@ 
                    oddcandidatevariableslow;
             freevariablesoddlowpositive = 
                   Select[reducedfreeoddlowpositive, 
                     FullSimplify[Equivalent[#[[2]], facts]] === True &][[All, 
                     1]];
             freevariablesoddlownegative = 
                   Select[reducedfreeoddlownegative, 
                     FullSimplify[Equivalent[#[[2]], facts]] === True &][[All, 
                     1]];        

             (* the variables that are common should be handled by the odd simplifier becuase their coefficients must vanish *)
             common = Intersection[freevariablesoddlowpositive, freevariablesoddlownegative];   

             (*Print[common];
             Print[freevariablesoddhighnegative];*)
             freeoddcandidateslowpositive = 
                   Select[oddcandidateslow, MemberQ[Complement[freevariablesoddlowpositive, common] , #[[2]]] &];

             (*Print[freeoddcandidateshighpositive];*)
             freeoddcandidateslownegative = 
                   {#[[1]],#[[2]],-#[[3]]}&/@Select[oddcandidateslow, MemberQ[Complement[freevariablesoddlownegative, common]  , #[[2]]] &];

             (*Print[freeoddcandidateslownegative];*)



             (** odd single positive and single negative **)
             oddcandidatevariablessingle = If[ oddcandidatessingle==={},
                                               {},
                                               DeleteDuplicates[oddcandidatessingle[[All, 2]]]
                                           ];

             (*Print[oddcandidatessingle];*)
             reducedfreeoddsinglepositive = {#, 
                      Reduce[facts && 
                        Reduce[FA[Complement[allvars, {#}], 
                          Implies[Reduce[EE[#, facts], Reals], 
                           Reduce[EE[# ,#>0 && facts], Reals]
                           ]], Reals], Reals]} & /@ 
                    oddcandidatevariablessingle;
             reducedfreeoddsinglenegative = {#, 
                      Reduce[facts && 
                        Reduce[FA[Complement[allvars, {#}], 
                          Implies[Reduce[EE[#, facts], Reals], 
                           Reduce[EE[# ,#<0 && facts], Reals]
                           ]], Reals], Reals]} & /@ 
                    oddcandidatevariablessingle;
             freevariablesoddsinglepositive = 
                   Select[reducedfreeoddsinglepositive, 
                     FullSimplify[Equivalent[#[[2]], facts]] === True &][[All, 
                     1]];
                     
             (*Print[freevariablesoddsinglepositive];  *)
             freevariablesoddsinglenegative = 
                   Select[reducedfreeoddsinglenegative, 
                     FullSimplify[Equivalent[#[[2]], facts]] === True &][[All, 
                     1]];        

             (* the variables that are common should be handled by the odd simplifier becuase their coefficients must vanish *)
             common = Intersection[freevariablesoddsinglepositive, freevariablesoddsinglenegative];   

             (*Print[common];
             Print[freevariablesoddsinglepositive];*)
             freeoddcandidatessinglepositive = 
                   Select[oddcandidatessingle, MemberQ[Complement[freevariablesoddsinglepositive, common] , #[[2]]] &];

             (*Print[freeoddcandidateshighpositive];*)
             freeoddcandidatessinglenegative = 
                   {#[[1]],#[[2]],-#[[3]]}&/@Select[oddcandidatessingle, MemberQ[Complement[freevariablesoddsinglenegative, common]  , #[[2]]] &];

             (*Print[freeoddcandidatessinglenegative];*)





             (*****************)
             freecandidates = Union[freeevencandidateshigh, freeevencandidateslow, freeevencandidatessingle,freeoddcandidateshighpositive ,
                 freeoddcandidateshighnegative,    freeoddcandidateslowpositive ,freeoddcandidateslownegative,
                     freeoddcandidatessinglepositive ,freeoddcandidatessinglenegative ];     

             (*
             Print[freecandidates];*)
             (*Return[problem];*)
             If[ freecandidates === {},
                 Return[problem]
             ];
             thedependentcandidates =  Select[freecandidates, !FreeQ[#[[3]], Alternatives @@ allvars, {0, Infinity}] &];
             theindependependentcandidates = Select[freecandidates, FreeQ[#[[3]], Alternatives @@ allvars, {0, Infinity}] &];
             If[ thedependentcandidates === {},
                 Append[problem, 
                  "extremecoefficients" -> 
                   DeleteDuplicates@
                    Join[Lookup[problem, "extremecoefficients", {}], 
                     theindependependentcandidates[[All, 3]]]],
                 Append[problem, 
                  "extremecoefficients" -> 
                   DeleteDuplicates@
                    Join[Lookup[problem, "extremecoefficients", {}], 
                     theindependependentcandidates[[All, 3]], 
                     Lookup[SimplifyPositivityExtremeEvenCoefficientsOperator[
                        variables][
                       Association[
                        "expression" -> thedependentcandidates[[All, 3]]]], 
                      "extremecoefficients", {}]]]
             ]
         ]
     ]
     ];






getSymbols[expr_] :=
    With[ {symbols = 
       DeleteDuplicates@
        Flatten@Cases[expr, 
          f_Symbol | Derivative[__][f_Symbol][x__Symbol] | 
            Derivative[__][f_Symbol][__] | 
            f_Symbol[__] | _[x__Symbol] :> {f, x}, {0, 
           Infinity}]},(*there might be atomic expressions in symbols \
  that are not strictly symbols in this context,like Plus,Times,
     Power etc.*)(*those are symbols which should not be transford into \
  pattern,so we eliminate them by exact string match in the actual \
  expr.*)
        Select[
        symbols, ! (StringFreeQ[ToString[expr], ToString[#]] || 
         MemberQ[{True, False}, #]) &]
    ];


Options[findExtrema] = {Facts -> True, RandomSampleSize -> 10, 
   Type -> Min};
findExtrema[function_, vars_List, pars_List: {}, OptionsPattern[]] :=
    Module[ {randomSampleSize, type, facts, usedVars, usedPars, 
      parametricFacts, nonparametricFacts, directExtrema, 
      randomParValues, values, typeValue},
        randomSampleSize = OptionValue[RandomSampleSize];
        type = OptionValue[Type];
        usedVars = Select[vars, ! FreeQ[function, #] &];
        usedPars = Select[pars, ! FreeQ[function, #] &];
        facts = OptionValue[Facts];
        {parametricFacts, nonparametricFacts} = 
         GroupBy[If[ FreeQQ[facts, And],
                     List@facts,
                     List @@ facts
                 ], 
            And @@ FreeQQ[#, usedVars] &] /@ {True, False} /. 
          Missing[___] -> {};
        (*DPrint["parameters and variables = ",{usedPars,
        usedVars}];*)(*DPrint[
        "parametricFacts, nonparametricFacts = ",{parametricFacts,
        nonparametricFacts}];*)
        typeValue = If[ type === Min,
                        MinValue,
                        MaxValue
                    ];
        directExtrema = 
         typeValue[{function, And @@ nonparametricFacts}, usedVars];
        If[ Head@directExtrema =!= typeValue,
            Return@directExtrema
        ];
        randomParValues = 
         Through[Unevaluated@
            Union[RandomInteger, RandomReal][{-randomSampleSize, 
              randomSampleSize}, {randomSampleSize, Length@usedPars}]] // 
    Round[#, 10^(-2)] &;
        (*DPrint["randomParValues = ",randomParValues]*);
        randomParValues = 
         Select[randomParValues, ! (Simplify[
               And @@ parametricFacts /. Thread[usedPars -> #]] === 
              False) &];
        values = 
         Map[typeValue[{function, And @@ nonparametricFacts}, usedVars] /. 
            Thread[usedPars -> #] &, randomParValues];
        (*DPrint["min/max values = ",values];*)
        type@Select[values, NumericQ[#] || Head@# === DirectedInfinity &]
    ]


Options[AssociatedPolynomial] = {Facts -> True};
AssociatedPolynomial[exp_List, depVars_List, indVars_List, 
  pars_List: {}, OptionsPattern[]] :=
    Module[ {print, facts, expr, vars, functions, extraFunctions, 
      extraFacts},
        print = DebugPrint[False, "[assoc-pol]"];
        facts = OptionValue[Facts];
        print["facts = ", facts];
        expr = Together /@ exp;
        vars = getVars[expr, depVars];
        functions = 
         DeleteDuplicates@
          Select[FixedPoint[
            Map[If[ MemberQ[{Plus, Times}, Head@#],
                    Sequence @@ List @@ #,
                    #
                ] &], 
            expr], ! PolynomialQ[#, vars] && ! FreeQQ[#, vars] &];
        If[ functions == {},
            Return[{expr, {}, facts}]
        ];
        (*There are two problems here:*)(*1. functinos need to be cleaned,
        since some of them might be expressed by others in a polynomial \
      relation,like r[x]^b,r[x]^(2b),r[
        x]^(b-1)*)(*2. MinV and MaxV do not work for all cases,
        they need to be improved (NMinimize,Minimize,
        FindMinimum)*)(*It might be useful to apply this part also in \
      SimplifyPositivity to handle non-plynomial cases. 
        Maybe a function for this will be usefull:AssociatePolynomial.*)
        print["functions = ", functions];
        extraFunctions = 
         Table[Subscript[\[FormalCapitalY], k] @@ indVars, {k, 
           Length@functions}];
        print["extraFunctions = ", extraFunctions];
        print["functions = ", Thread[functions -> extraFunctions]];
        (*extraFacts=(MinV[{First@#,facts},
        vars]\[LessEqual]#[[2]]\[LessEqual]MaxV[{First@#,facts},vars])&/@
        Transpose[{functions,extraVars}];*)
        extraFacts = (findExtrema[First@#, vars, pars, Facts -> facts, 
              Type -> Min] <= #[[2]] <= 
             findExtrema[First@#, vars, pars, Facts -> facts, 
              Type -> Max]) & /@ Transpose[{functions, extraFunctions}];
        print["genFacts = ", extraFacts];
        {expr /. Thread[functions -> extraFunctions], extraFunctions, 
         And @@ extraFacts, functions}
    ]


SimplifyPositivityQEOperator[variables_Association][problem_] :=
    Which[
     problem === $Failed,
     $Failed,
     Head[problem] === Piecewise,
     PiecewiseOperatorMap[SimplifyPositivityQEOperator, variables, problem],
     Head[problem] =!= Association,
     SimplifyPositivityQEOperator[variables][
      Association["expression" -> problem]],
     Head[problem["expression"]]===Piecewise,  
     SimplifyPositivityQEOperator[variables][PiecewiseExpandAssociation[problem]],    
     True,
     Module[ {exp, depVars, indVars, pars,
       dom, facts, timeConstraint, (*type,*) expr, vars, factVars, allVars, 
       parametricFacts, nonparametricFacts, extraFunctions, extraFacts, 
       oldFunctions, (*formalCoeffs, *)print, cleanup,FA},
         exp = Lookup[problem, "expression", 0];
         depVars = Lookup[variables, "depVars", {}];
         indVars = Lookup[variables, "indVars", {}];
         pars = Lookup[variables, "pars", {}];
         dom = Lookup[variables, "domain", Reals];
         facts = Lookup[variables, "facts", True];
         timeConstraint = 
          Lookup[problem, "timeconstraint", 
           Lookup[variables, "timeconstraint", Infinity]];
      (*   type = Lookup[problem, "type", "ForAll"];*)
         expr = Together /@ ({exp} // Flatten);
         print = Null;
         cleanup :=
             If[ # === $Failed,
                 $Failed,
                 PiecewiseSimplifyOperator[variables][Piecewise[{{exp, #}}, $Failed]]
             ] &;
         vars = GetVarsOperator[variables][expr];
         
         (*I have added the independent variables that appear in the \
      expression*)
         (*vars = Union[getVars[expr, depVars], 
           Intersection[getSymbols[{exp, facts}], indVars]];*)
         vars = Union[vars, Intersection[getSymbols[{exp, facts}], indVars]];
       (*factVars = getVars[facts, depVars];*)
         factVars = GetVarsOperator[variables][facts];
         allVars = Union[vars, factVars];
         FA = ForAll[#1,#2,#3]&;
         
         (*If the given expression does not contain any variables,
         then it is a coefficient and hence the output should be expr\
      \[GreaterEqual]0*)
         If[ vars === {},
             Return[cleanup[And @@ (# >= 0 & /@ expr)]]
         ];
         print["vars = ", vars];
         print["allvars = ", allVars];
         {parametricFacts, nonparametricFacts} = 
          GroupBy[If[ FreeQQ[facts, And],
                      List@facts,
                      List @@ facts
                  ], 
             And @@ FreeQQ[#, Union[depVars, indVars]] &] /@ {True, 
             False} /. Missing[___] -> {};
         print["parametricFacts = ", parametricFacts, 
          ", nonparametricFacts = ", nonparametricFacts];
         
       (*  cleanup@If[type === Exists,
           
           formalCoeffs = 
            Union@Cases[expr, 
              Subscript[\[FormalA], _Integer], {0, Infinity}];
           print[formalCoeffs, " - ", type, " - ", 
            PolynomialQ[expr, vars]];
           If[formalCoeffs === {}, Return[$Failed]];
           If[And @@ (PolynomialQ[#, vars] & /@ expr), 
            print["Given expression seems to be a polynomial."];
            TimeConstrained[
             FullSimplify@
              Reduce[Exists[Evaluate@formalCoeffs, 
                ForAll[Evaluate@allVars, And @@ nonparametricFacts, 
                 And @@ parametricFacts && (And @@ (# >= 0 & /@ expr))]], 
               dom], timeConstraint, $Failed],(*If expr is not a \
      polynomial*){expr, extraFunctions, extraFacts, oldFunctions} = 
             AssociatedPolynomial[expr, depVars, indVars, pars, 
              Facts -> facts];
            print["expr = ", expr];
            print["extraFunctions, extraFacts = ", extraFunctions, " | ", 
             extraFacts];
            TimeConstrained[
             FullSimplify@
              Reduce[Exists[formalCoeffs, 
                ForAll[Evaluate@Union[allVars, extraFunctions], 
                 And @@ nonparametricFacts && extraFacts, 
                 And @@ parametricFacts && expr >= 0]], dom], 
             timeConstraint, $Failed]],
         *)  
           (*If type===ForAll*)
         cleanup@If[ And @@ (PolynomialQ[#, vars] & /@ expr),
                     print["Given expression seems to be a polynomial. zobzb 2"];
                     print[{FA[Evaluate@allVars, And @@ nonparametricFacts, 
                         And @@ parametricFacts && (And @@ (# >= 0 & /@ expr))], Evaluate[dom]}];
                     (*1. parametric facts should be placed with conditions where \
               the expr\[GreaterEqual]0,
                     while nonparametric ones should be as conditions on vars*)(*2. \
               FullSumplify is needed,
                     since sometimes Resolve gives complicated constraints which can \
               actually be simplified,e.g.x(a+bx+cx^2)\[GreaterEqual]0*)
                     TimeConstrained[
                      (*FullSimplify@*)
                       Resolve[FA[Evaluate@allVars, And @@ nonparametricFacts, 
                         And @@ parametricFacts && (And @@ (# >= 0 & /@ expr))], Evaluate[dom]], timeConstraint, $Failed],
                        
                        (*If expr is not a polynomial*)
                     {expr, extraFunctions, extraFacts, oldFunctions} = 
                      AssociatedPolynomial[expr, depVars, indVars, pars, 
                       Facts -> facts];
                     print["expr = ", expr];
                     print["extraFunctions, extraFacts = ", extraFunctions, " | ", 
                      extraFacts];
                     TimeConstrained[
                      FullSimplify@
                       Resolve[ForAll[Evaluate@Union[allVars, extraFunctions], 
                         And @@ nonparametricFacts && extraFacts, 
                         And @@ parametricFacts && (And @@ (# >= 0 & /@ expr))], 
                        dom], timeConstraint, $Failed]
                 ]
     ]
     ]


PositivityConditionQEOperator[variables_Association][problem_] :=
    Which[
     problem === $Failed, $Failed,  
     Head[problem] === Piecewise, 
     PiecewiseOperatorMap[PositivityConditionQEOperator,variables, 
      problem],
     
     Head[problem] =!= Association,
     PositivityConditionQEOperator[variables][
      Association["expression" -> problem]],
     
     Head[problem["expression"]] === Piecewise, 
     SimplifyPositivityQEOperator[variables][
      PiecewiseExpandAssociation[problem]],
     
     True,
     Module[ {exp, depVars, indVars, pars, dom, facts, timeConstraint, 
       type, expr, vars, factVars, allVars, parametricFacts, 
       nonparametricFacts, extraFunctions, extraFacts, oldFunctions, 
       formalCoeffs, print, cleanup},
         exp = Lookup[problem, "expression", 0];
         depVars = Lookup[variables, "depVars", {}];
         indVars = Lookup[variables, "indVars", {}];
         pars = Lookup[variables, "pars", {}];
         dom = Lookup[variables, "domain", Reals];
         facts = Lookup[variables, "facts", True];
         timeConstraint = 
          Lookup[problem, "timeconstraint", 
           Lookup[variables, "timeconstraint", Infinity]];
         type = Lookup[problem, "remove", True]; (** ??? document this ??? **)
         expr = Together /@ ({exp} // Flatten);
         print = Null;
         cleanup = Piecewise[{{True,#}}, $Failed]&;
         
         (*I have added the independent variables that appear in the \
      expression*)
         vars = Union[getVars[expr, depVars], 
           Intersection[getSymbols[{exp, facts}], indVars]];
         factVars = getVars[facts, depVars];
         allVars = Union[vars, factVars];
         (*If the given expression does not contain any variables,
         then it is a coefficient and hence the output should be expr\
      \[GreaterEqual]0*)
         If[ vars === {},
             Return[cleanup[And @@ (# >= 0 & /@ expr)]]
         ];
         print["vars = ", vars];
         {parametricFacts, nonparametricFacts} = 
          GroupBy[If[ FreeQQ[facts, And],
                      List@facts,
                      List @@ facts
                  ], 
             And @@ FreeQQ[#, Union[depVars, indVars]] &] /@ {True, 
             False} /. Missing[___] -> {};
         print["parametricFacts = ", parametricFacts, 
          ", nonparametricFacts = ", nonparametricFacts];
         cleanup@If[ type,
                     formalCoeffs = 
                      Union@Cases[expr, Subscript[\[FormalA], _Integer], {0, Infinity}];
                     print[formalCoeffs, " - ", type, " - ", PolynomialQ[expr, vars]];
                    (* If[formalCoeffs === {}, Return[$Failed]];*)
                     If[ And @@ (PolynomialQ[#, vars] & /@ expr),
                         print["Given expression seems to be a polynomial. zob!"];
                         print[Exists[Evaluate@formalCoeffs, 
                             ForAll[Evaluate@allVars, And @@ nonparametricFacts, 
                              And @@ parametricFacts && (And @@ (# >= 0 & /@ expr))]]];
                         TimeConstrained[
                          FullSimplify@
                           Reduce[Exists[Evaluate@formalCoeffs, 
                             ForAll[Evaluate@allVars, And @@ nonparametricFacts, 
                              And @@ parametricFacts && (And @@ (# >= 0 & /@ expr))]], 
                            dom], timeConstraint, $Failed],
                            (*If expr is not a polynomial*)
                         {expr, extraFunctions, extraFacts, oldFunctions} = 
                         AssociatedPolynomial[expr, depVars, indVars, pars, 
                         Facts -> facts];
                         print["expr = ", expr];
                         print["extraFunctions, extraFacts = ", extraFunctions, " | ", 
                          extraFacts];
                         TimeConstrained[
                          FullSimplify@
                           Reduce[Exists[formalCoeffs, 
                             ForAll[Evaluate@Union[allVars, extraFunctions], 
                              And @@ nonparametricFacts && extraFacts, 
                              And @@ parametricFacts && expr >= 0]], dom], 
                          timeConstraint, $Failed]
                     ],(*If type===ForAll*)
                     If[ And @@ (PolynomialQ[#, vars] & /@ expr),
                         print["Given expression seems to be a polynomial."];
                         (*1. parametric facts should be placed with conditions where the \
                    expr\[GreaterEqual]0,
                         while nonparametric ones should be as conditions on vars*)(*2. \
                    FullSumplify is needed,
                         since sometimes Resolve gives complicated constraints which can \
                    actually be simplified,e.g.x(a+bx+cx^2)\[GreaterEqual]0*)
                         print[ForAll[Evaluate@allVars, And @@ nonparametricFacts, 
                             And @@ parametricFacts && (And @@ (# >= 0 & /@ expr))]];
                         print["zobzob"];
                         TimeConstrained[
                          FullSimplify@
                           Reduce[ForAll[Evaluate@allVars, And @@ nonparametricFacts, 
                             And @@ parametricFacts && (And @@ (# >= 0 & /@ expr))], dom],
                           timeConstraint, $Failed],
                           
                           (*If expr is not a polynomial*)
                         {expr, 
                         extraFunctions, extraFacts, oldFunctions} = 
                         AssociatedPolynomial[expr, depVars, indVars, pars, 
                         Facts -> facts];
                         print["expr = ", expr];
                         print["extraFunctions, extraFacts = ", extraFunctions, " | ", 
                          extraFacts];
                         TimeConstrained[
                          FullSimplify@
                           Reduce[ForAll[Evaluate@Union[allVars, extraFunctions], 
                             And @@ nonparametricFacts && extraFacts, 
                             And @@ parametricFacts && (And @@ (# >= 0 & /@ expr))], dom],
                           timeConstraint, $Failed]
                     ]
                 ]
     ]]
 


        
End[]
(*EndPackage[]*)