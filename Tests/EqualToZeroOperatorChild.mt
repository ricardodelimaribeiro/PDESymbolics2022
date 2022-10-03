(* Wolfram Language Test file *)

Test[
	With[{expression = variables["expression"]},
    	EqualToZeroOperator[variables][expression]
	]
    ,
    With[{result = variables["result"]},
    	result
    ]
    ,
    TestID -> "EqualToZeroOperator-20200624-G6MH79_" <> label
]
