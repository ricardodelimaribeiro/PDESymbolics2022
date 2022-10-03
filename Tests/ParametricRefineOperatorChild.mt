(* Wolfram Language Test file *)

Test[
	
(* OLD CODE *)	
(*	
	With[{expression = variables["expression"]},
    	ParametricRefineOperator[variables][expression]//PiecewiseExpand
	]
    ,
    With[{result = variables["result"]},
    	result
    ]
*)    
(* NEW CODE *)    

    	With[{expression = variables["expression"],result = variables["result"]},
		With[{computation=ParametricRefineOperator[variables][expression]},
    	Which[
    		Expand[result]===Expand[computation],
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
    TestID -> "ParametricRefineOperator-20200812-LRRH82_" <> label
]
