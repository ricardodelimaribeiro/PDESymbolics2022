(* Wolfram Language Test file *)

Test[
	With[{expression = variables["expression"], result = variables["result"]},
		With[{computation = DiscreteConservedQOperator[KeyDrop["result"][variables]][expression]//Quiet},
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
    TestID -> "DiscreteConservedQOperator-20211118-FAFD67_" <> label
]
