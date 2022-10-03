(* Wolfram Language Test file *)

Test[
	With[{expression = variables["expression"], result = variables["result"]},
		With[{computation = TimeDifferenceOperator[variables][expression]},
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
    TestID -> "TimeDifferenceOperator-20211118-NTER22_" <> label
]
