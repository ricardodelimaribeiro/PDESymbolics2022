(* Wolfram Language Test file *)

Test[
	
(* OLD CODE *)	
	
	With[{expression = variables["expression"]},
    	PiecewiseBeautify[expression]
	]
    ,
    With[{result = variables["result"]},
    	result
    ]
    
(* NEW CODE *)    
    
(*	With[{expression = variables["expression"],result = variables["result"]},
		With[{computation=ParametricRefineOperator[variables][expression]},
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
    True    *)
    
    ,
    TestID -> "PiecewiseBeautify-20210121-K6RH82_" <> label
]
