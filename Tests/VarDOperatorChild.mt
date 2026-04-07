(* Wolfram Language Test file *)

Test[
	With[{expression = variables["expression"], result = variables["result"]},
    	With[{computation = VarDOperator[variables][expression]},
    		Which[
    			result === computation,
    				result,
    			PiecewiseEqualOperator[variables][result, computation] === True,
    				result,
    			Simplify[result == computation] === True,
    				result,
    			True,
    				{computation, variables}
    		]
    	]
	]
    ,
    With[{result = variables["result"]},
    	result
    ]
    ,
    TestID -> "VarDOperator-20200420-F6MHN8_" <> label
]
