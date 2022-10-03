(* Wolfram Language Test file *)

Test[
	With[{MonList = variables["MonList"]},
    	BasisOperator[variables][MonList]
	]
    ,
    With[{result = variables["result"]},
    	result
    ]
    ,
    TestID -> "BasisOperator-20201202-M7B7R1_" <> label
]
