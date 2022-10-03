(* Wolfram Language Test file *)
(*Test[
		With[{result = system["result"]},
		With[{computation=GaussianEliminationOperator[field][system]},
		Print[field];
		Print[system];
		Print[result];
		Print[computation];	
		Print["*****"];
		Print[result===computation];
		Print[label];
    	Which[
    		result===computation,
    		True, 
    		PiecewiseEqualOperator[field][result, computation]===True,
    		True,
    		True,
    		False
    	]
		]
    	
	]
    ,
    True

    ,
    TestID -> "GaussianEliminationOperator-20200420-F6MHN8_" <> label
]*)



Test[
	With[{sol = GaussianEliminationOperator[field][system]},		
		sol
	]
    ,
    Lookup[system, "result", result]
    ,
    TestID -> "GaussianEliminationOperator-20200420-F6MHN8_" <> label
]
