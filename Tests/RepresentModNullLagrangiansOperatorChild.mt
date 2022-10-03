(* Wolfram Language Test file *)

Test[
	With[{expression = variables["expression"],result = variables["result"]},
		With[{computation=RepresentModNullLagrangiansOperator[variables][expression]},
    	Which[
    		result===computation,
    		True, 
    		PiecewiseEqualOperator[variables][result, computation]===True,
    		True,
    		True,
    		{computation, variables}
    	]
		]
    	
	]
    ,
    True
    ,
    TestID -> "RepresentModNullLagrangiansOperator-20200423-M7B7R8_" <> label
]