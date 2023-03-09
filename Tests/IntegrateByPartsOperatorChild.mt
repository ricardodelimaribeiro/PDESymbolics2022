(* Wolfram Language Test file *)

Test[
	With[{expression = variables["expression"]},
    	IntegrateByPartsOperator[variables][expression]//Quiet
	]
    ,
    With[{result = variables["result"]},
    	result
    ]
    ,
    TestID -> "IntegrateByPartsOperator-20200614-M7B7R8_" <> label
]

