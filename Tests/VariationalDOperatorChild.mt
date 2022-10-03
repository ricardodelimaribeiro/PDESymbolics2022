(* Wolfram Language Test file *)

Test[
	With[{expression = variables["expression"]},
    	VariationalDOperator[variables][expression]
	]
    ,
    With[{result = variables["result"]},
    	result
    ]
    ,
    TestID -> "VariationalDOperator-20200422-F6MH99_" <> label
]
