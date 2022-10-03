(* Wolfram Language Test file *)

Test[
	With[{expression = variables["expression"]},
    	EquivalentsByIntegrationByPartsOperator[variables][expression]
	]
    ,
    With[{result = variables["result"]},
    	result
    ]
    ,
    TestID -> "EquivalentsByIntegrationByPartsOperator-20201103-P7BGR8_" <> label
]

