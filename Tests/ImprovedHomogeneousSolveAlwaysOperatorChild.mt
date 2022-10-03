(* Wolfram Language Test file *)

Test[
(*	With[{expression = variables["expression"]},
    	ImprovedHomogeneousSolveAlwaysOperator[variables][expression]
	]
    ,
    With[{result = variables["result"]},
    	result
    ]*)

	With[{expression = variables["expression"],result = variables["result"]},
		With[{computation=ImprovedHomogeneousSolveAlwaysOperator[variables][expression]},
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
    ,
    TestID -> "ImprovedHomogeneousSolveAlwaysOperator-20200624-LMBH99_" <> label
]
