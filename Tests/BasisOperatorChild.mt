(* Wolfram Language Test file *)

Test[
	With[{MonList = variables["MonList"]},
		With[{result = variables["result"],computation = BasisOperator[variables][MonList]},
			Which[
				result === computation,
				result,
				PiecewiseEqualOperator[variables][result,computation]===True,
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
    TestID -> "BasisOperator-20201202-M7B7R1_" <> label
]
