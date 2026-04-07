(* Wolfram Language Test file *)

Test[
	With[{expression = template["expression"], result = template["result"], variables = template["variables"]},
    	With[{computation = MatrixInverseOperator[variables][expression]},
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
    With[{result = template["result"]},
    	result
    ]
    ,
    TestID -> "MatrixInverseOperator-20210131-8DB2MA_" <> label
]
