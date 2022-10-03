(* Wolfram Language Test file *)

Test[
	With[{MonList = variables["MonList"]},
    	CleanNullLagrangiansOperator[variables][MonList]
	]
    ,
    With[{result = variables["result"]},
    	result
    ]
    ,
    TestID -> "CleanNullLagrangiansOperator-20200423-K9MHN8_" <> label
]
