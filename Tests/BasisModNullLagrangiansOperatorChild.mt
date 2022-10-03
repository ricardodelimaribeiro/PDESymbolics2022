(* Wolfram Language Test file *)

Test[
	With[{MonList = variables["MonList"]},
    	BasisModNullLagrangiansOperator[variables][MonList]
	]
    ,
    With[{result = variables["result"]},
    	result
    ]
    ,
    TestID -> "BasisModNullLagrangiansOperator-20200423-M7B7R8_" <> label
]
