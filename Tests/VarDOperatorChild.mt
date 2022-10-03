(* Wolfram Language Test file *)

Test[
	With[{expression = variables["expression"]},
    	VarDOperator[variables][expression]
	]
    ,
    With[{result = variables["result"]},
    	result
    ]
    ,
    TestID -> "VarDOperator-20200420-F6MHN8_" <> label
]
