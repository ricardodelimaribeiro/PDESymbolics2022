(* Wolfram Language Test file *)

Test[
	With[{MonList = variables["MonList"],result = variables["result"]},
		With[{computation = BasisModNullLagrangiansOperator[variables][MonList]},
			Which[
				result === computation,
				result,
				PiecewiseEqualOperator[variables][result, computation] ===True,
				result,
				True,
				computation
			]
		]
	]
    ,
    With[{result = variables["result"]},
    	result
    ]
    ,
    TestID -> "BasisModNullLagrangiansOperator-20200423-M7B7R8_" <> label
]
