(* Wolfram Language Test file *)

Test[
	With[{expression = template["expression"], result = template["result"]},
		With[{computation = template["operator"][template["variables"]][expression]//Quiet},
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
    TestID -> "AutoReduceOperator-20210316-8DX9MA_" <> label
]