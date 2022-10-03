(* Wolfram Language Test file *)

Test[
	With[{expression = variables["expression"]},
    	DVarDOperator[variables][expression]
	]
    ,
    With[{result = variables["result"]},
    	result
    ]
    ,
    TestID -> "DVarDOperator-20200430-PP8HN8_" <> label
]
