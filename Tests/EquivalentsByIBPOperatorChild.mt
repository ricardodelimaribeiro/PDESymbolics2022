(* Wolfram Language Test file *)

Test[
	With[{expression = variables["expression"]},
    	EquivalentsByIBPOperator[variables][expression]
	]
    ,
    With[{result = variables["result"]},
    	result
    ]
    ,
    TestID -> "EquivalentsByIBPOperator-20201020-P7B7R8_" <> label
]

