(* Wolfram Language Test file *)

Test[
	With[{expression = variables["expression"], result = variables["result"]},
		With[{computation = (*PDESymbolics2020`*)EliminationListOperator[variables][expression]},
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
    TestID -> "EliminationListOperator-20211118-YNA3R5_" <> label
]
