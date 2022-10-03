(* Wolfram Language Test file *)

Test[
	With[{expression = variables["expression"], result = variables["result"]},
		With[{computation = TimeOrderedQOperator[variables][expression]},
			Print[computation];
			Which[
    		result === computation,
    			result,
    		PiecewiseEqualOperator[variables][result, computation] === True,
    			result,
    		True,
    			computation
    		]
    	]	
	]
    ,
    With[{result = variables["result"]},
    	result
    ]
    ,
    TestID -> "TimeOrderedQOperator-20211118-38WERN_" <> label
]
