(* Wolfram Language Test file *)

Test[
	With[{expression = template["expression"], result = template["result"]},
		With[{computation = template["operator"][template["variables"]][expression]},
			Which[
    		result === computation,
    			result,
    		PiecewiseEqualOperator[template["variables"]][result, computation] === True,
    			result,
    		True,
    			computation
    		]
    	]	
	]
    ,
    With[{result = template["result"]},
    	result
    ]
    ,
    TestID -> "InferGeneratorsOperator-20230309-9D8PMC_" <> label
]
