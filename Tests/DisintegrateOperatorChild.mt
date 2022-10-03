(* Wolfram Language Test file *)

Test[
	With[{expression = variables["expression"],result = variables["result"]},
		With[{computation=DisintegrateOperator[variables][expression]},
    	Which[
    		result===computation,
    		True, 
    		PiecewiseEqualOperator[variables][result, computation]===True,
    		True,
    		True,
    		False
    	]
		]
    	
	]
    ,
    True

(*

	With[{expression = variables["expression"]},
    	DisintegrateOperator[variables][expression]
	]
    ,
    With[{result = variables["result"]},
    	result
    ]*)
    ,
    TestID -> "DisintegrateOperator-20201104-L72GR8_" <> label
]

