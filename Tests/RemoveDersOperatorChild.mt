(* Wolfram Language Test file *)

Test[
	With[{expression = variables["expression"]},
    	RemoveDersOperator[variables][expression]
	]
    ,
    With[{result = variables["result"]},
    	result
    ]
    ,
    TestID -> "RemoveDersOperator-20200614-M7B7R8_" <> label
]

