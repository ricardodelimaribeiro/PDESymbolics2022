(* Wolfram Language Test file *)

Test[
	With[{expression = variables["expression"], result = variables["result"]},
		With[{computation = FindDiscreteConservedQuantityBasisOperator[KeyDrop[{"result","expression"}][variables]][expression]//Quiet},
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
    TestID -> "FindDiscreteConservedQuantityBasisOperator-20220201-MNT345_" <> label
]