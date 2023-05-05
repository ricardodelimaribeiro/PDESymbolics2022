(* Wolfram Language Test file *)

Test[
	With[{expression = template["expression"], result = template["result"]},
		With[{computation = template["operator"][template["variables"]][expression]},
			Which[
    		result === computation,
    			result,
    		PiecewiseEqualOperator[template["variables"]][result, computation //
    			ComprehensiveGroebnerSystemOperator[Append["reduce" -> Reduce]@variables] // 
 PiecewiseApplyConditionOperator[Append["reduce" -> Reduce]@variables]] === True,
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
    TestID -> "GrobOp-20210218-8DX9MA_" <> label
]
