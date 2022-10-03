(* Wolfram Language Test file *)

Test[
		With[{expression = variables["expression"],result = variables["result"]},
		With[{computation=TimeDerOperator[variables][expression]},
    	Which[
    		result===computation,
    		True, 
    		PiecewiseEqualOperator[variables][result, computation]===True,
    		True,
    		True,
    		Print["Expected output:\n",result, "Actual output\n",computation];
    		False
    	]
		]
    	
	]
    ,
    True

    ,
    TestID -> "TimeDerOperator-20200629-PPG7N8_" <> label
]

(*


Test[
	With[{expression = variables["expression"]},
    	TimeDerOperator[variables][expression]
	]
    ,
    With[{result = variables["result"]},
    	result
    ]
    ,
    TestID -> "TimeDerOperator-20200629-PPG7N8_" <> label
]
*)