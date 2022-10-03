(* Wolfram Language package *)
(*BeginPackage["PDESymbolics2020`Monomials`"]*)
MonomialsOperator::usage = "generates monomials in dependent, independent variables, or generators";


Begin["`Private`"] (* Begin Private Context *) 

DegM :=
    Exponent[# /. Thread[Variables[#] -> \[FormalX]], \[FormalX]] &; 
  
GenerateIndices[deg_, len_] :=
    Join @@ Table[
    Flatten[DeleteDuplicates@(Permutations /@ 
    IntegerPartitions[k, {len}, Range[0, deg]]), 1], {k, 0, deg}];
     
GenerateMonomials[generators_, indices_] :=
    DeleteDuplicates@(Map[Times @@ (generators^#) &, indices]);

MyHead[Derivative[__][z_][___]] :=
    z
MyHead[z_] :=
    Head[z]

FrobeniusSystemSolve[M_, b_] :=
    With[ {candidates = FrobeniusSolve[Total /@ Transpose[M], Total[b]]},
        Select[candidates, M.# == b &]
    ];

FrobeniusSystemSolve[M_, b_, w_] :=
    With[ {candidates = FrobeniusSolve[w.M, w.b]},
        Select[candidates, M.# == b &]
    ];

Options[Monomials] = {"Generators" -> {}, "Type" -> "All", "Weights" -> {}, 
   "HomogeneousDeg" -> False, "HomogeneousDer" -> False, 
   "IndVariables" -> False, "depth"->0};

Monomials[DepVars_List, IndVars_List, der_Integer?NonNegative, deg_, 
    OptionsPattern[]] /; ((IntegerQ[deg] && 
        NonNegative[deg]) || (ListQ[deg])) && Length@DepVars != 0 :=
    Module[ {FirstDepVar, Ders, AllDers, generators, type, Monoms, 
      weights, hdeg, hder, mdeg, mder, a, fgenerators, ivrs,  
      fullweights, deg2,depthm},
        generators = OptionValue["Generators"];
        type = OptionValue["Type"];
        weights = OptionValue["Weights"];
        FirstDepVar = DepVars[[1]];
        hdeg = OptionValue["HomogeneousDeg"];
        hder = OptionValue["HomogeneousDer"];
        ivrs = OptionValue["IndVariables"];
        depthm = OptionValue["depth"];
        If[ hdeg,
            mdeg = deg,
            mdeg = 0
        ];
        If[ hder,
            mder = der,
            mder = 0
        ];
           (*Derivatives of the first dependent variable*)
        If[ generators == {},
            Ders = DeleteDuplicates@Flatten@
               Table[D[FirstDepVar @@ IndVars, {IndVars, k}], {k, mder, der}],
            Ders = MKF[FirstDepVar, #] & /@ DeleteDuplicates@Flatten@Table[
                 D[FirstDepVar @@ IndVars, {IndVars, k}], {k, mder, der}];
        ];
                (*All derivatives of the all dependent variables or \
     generator funtions*)
        AllDers = Select[If[ generators == {},
                             Union @@ Map[(Ders /. {FirstDepVar -> #}) &, DepVars],
                             fgenerators = Map[MKF[IndVars, #] &, generators];
                             DeleteDuplicates@Flatten@Outer[#1[#2] &, Ders, fgenerators]
                         ], # =!= 0 &];
        If[ ! ListQ[deg] && weights =!= {} && generators == {},
            weights = {weights};
            deg2 = {deg},
            deg2 = deg
        ];
        If[ weights =!= {} && generators == {},
            fullweights = 
             With[ {baseweight = 
                  Association[MapThread[Rule, {DepVars, #[[1]]}]], 
                 nqz = Function[x, If[ NumberQ[x],
                                       x,
                                       0
                                   ]]},
                 (nqz /@ (AllDers /. 
                 Derivative[k___][
                 z_][___] :> ((List@k).#[[2]]))) + 
                 (baseweight /@ MyHead /@ AllDers)
             ] & /@ weights
        ];
        If[ ivrs,
            AllDers = Join[IndVars, AllDers]
        ];
        If[ generators == {} && weights == {},
            If[ hdeg,
                Monoms = 
                 Select[List @@(If[ Head[#] === Plus,
                                    #,
                                    {#}
                                ] &@((Expand[a^deg (1 + 1/a Total[AllDers])^deg2] /. 
                         j_Integer*expr : _ :> expr) /. a -> 0)), # =!= 0 &],
                Monoms = -List @@ Expand[(1 + Total[AllDers])^deg2] /. 
                  j_Integer*expr : _ :> expr
            ];
            If[ IntegerQ@Monoms[[1]],
                Monoms[[1]] = 1
            ];
            If[ mder>0&& Monoms[[1]]==1,
                Monoms = Rest[Monoms]
            ];
        ];
        Which[
            ivrs && weights =!= {}&& depthm==0,
        Monomials[DepVars, IndVars, der, deg, "Generators" -> generators, "Type" -> type, "Weights" -> OptionValue["Weights"], "HomogeneousDeg" -> hdeg, "HomogeneousDer" -> hder, "IndVariables" -> False, "depth"->0],
            ivrs && weights =!= {}&& depthm>0,
        Union[Monomials[DepVars, IndVars, der, deg,
        "Generators" -> generators, "Type" -> type, "Weights" -> OptionValue["Weights"], "HomogeneousDeg" -> hdeg, "HomogeneousDer" -> hder, "IndVariables" -> False, "depth"->depthm],     
        Flatten[Table[ IndVars[[k]] Monomials[DepVars, IndVars, der, 
        If[ Head[deg]===List,
            deg+OptionValue["Weights"][[All,2,k]],
            deg+OptionValue["Weights"][[2,k]]
        ],
        "Generators" -> generators, "Type" -> type, "Weights" -> OptionValue["Weights"], "HomogeneousDeg" -> hdeg, "HomogeneousDer" -> hder, "IndVariables" -> True, "depth"->depthm-1],{k,1,Length[IndVars]}]]   
        ],     
        hdeg && weights =!= {},            
        Return["Incompatible options: homogeneous degree and weights"], 
        weights != {} && generators == {},
        GenerateMonomials[AllDers, 
        FrobeniusSystemSolve[fullweights, deg2]], 
         weights != {} && Length@weights < 2,
        Return["Weights should be a list of at least two positive \
integers"],
        weights != {} && generators != {} && 
        Length@weights != Length@generators,
        Return["Weights and Generators should be a lists of equal length"],
         weights != {} && generators != {},
         GenerateMonomials[generators, FrobeniusSolve[weights, deg]],
         type == "All" && generators == {},
         Monoms,
         type == "All" && generators != {},
        GenerateMonomials[AllDers, 
        Select[GenerateIndices[deg, Length@AllDers], 
        mdeg <= Total[#] <= deg &]],
         type == "Even" && generators == {},
         Select[Monoms, EvenQ[DegM@#] &],
         type == "Even" && generators != {},
        GenerateMonomials[AllDers, 
        Select[2*GenerateIndices[Floor[deg/2], Length@AllDers], 
        mdeg <= Total[#] <= deg &]],
         type == "Odd" && generators == {},
         Select[Monoms, OddQ[DegM@#] &],
         type == "Odd" && generators != {},         
        GenerateMonomials[AllDers, 
        Select[GenerateIndices[deg, Length@AllDers], 
        OddQ@Total[#] && mdeg <= Total[#] <= deg &]],
         True,
        Print["Oops!, uncovered input of arguments, how did you do that ?"]
         ]
    ];
    
Monomials::BadArgs = "Incorrect input of arguments";
Monomials[___] :=
    "nothing" /; Message[Monomials::BadArgs]

MonomialsOperator[variables_Association][xp_] :=
    Which[
     xp === $Failed,
     $Failed,
     Head[xp] === Piecewise,
     PiecewiseOperatorMap[MonomialsOperator, variables, xp],   
     Head[xp] === List,
     Map[MonomialsOperator[variables],xp],
     Lookup[xp, "generators", {}]=!={},   
     Module[ {generators, indvars,LMKF,tempdepvars,tempvariables,tempmonomials},
         generators = Lookup[xp, "generators", {}];
         indvars = Lookup[variables, "indVars", {}];
         LMKF :=
             Function[Evaluate[indvars],#]&;
         tempdepvars = Unique["u"] & /@ generators;
         tempvariables = Append[variables, "depVars" -> tempdepvars];
         tempmonomials = MonomialsOperator[tempvariables][Append[xp,"generators"->{}]];
         tempmonomials /. MapThread[Rule, {tempdepvars, LMKF /@ generators}]
     ],
     Head[Lookup[xp, "stencil", $Failed]] === List, 
     MonomialsOperator[variables][
         Append[xp, "stencil" -> Association[# -> xp["stencil"] & /@ 
       If[ !Lookup[xp, "genFuns", False],
           Lookup[variables, "depVars", {}],
           Union[Lookup[variables, "depVars", {}], Lookup[variables, "genFuns", {}]]
       ]
      ]
         ]
     ],
     Head[Lookup[xp, "stencil", $Failed]] === Association,
     Module[ {tempgenerators, iv, dv},
         iv = Lookup[variables, "indVars", {}];
         dv = Union[Lookup[variables, "depVars", {}], Lookup[variables, "genFuns", {}]];
         tempgenerators = MapThread[#1 @@@ #2 &, {dv, 
         Map[(# + iv) & /@ # &, (Lookup[xp["stencil"], #, {}] & /@ 
            dv)]}] // Flatten;
         MonomialsOperator[variables][
             KeyDrop[Append[xp,"generators"-> tempgenerators],"stencil"]
         ]
     ],
     True,
     Monomials[
      If[ !Lookup[xp, "genFuns", False],
          Lookup[variables, "depVars", {}],
          Union[Lookup[variables, "depVars", {}], Lookup[variables, "genFuns", {}]]
      ],
      Lookup[variables, "indVars", {}],
      Lookup[xp, "derivatives", 0],
      Lookup[xp, "degree", 2],      
      (* we put the generators as empty because we are handling them differently 
      in the previous case *)
      "Generators" -> {},
      "Type" -> Lookup[xp, "type", "All"],
      "Weights" -> Lookup[xp, "weights", {}],
      "HomogeneousDeg" -> Lookup[xp, "homogeneousdegree", False],
      "HomogeneousDer" -> Lookup[xp, "homogeneousderivatives", False],
      "IndVariables" -> Lookup[xp, "indVars", False],
      "depth"->Lookup[xp, "depth", False]
      ]
     ];

End[] (* End Private Context *)

(*EndPackage[]*)