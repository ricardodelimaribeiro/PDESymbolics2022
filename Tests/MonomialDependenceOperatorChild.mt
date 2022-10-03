(* Wolfram Language Test file *)

Test[
	With[{expression = variables["expression"]},
    	MonomialDependenceOperator[variables][expression]
	]
    ,
    With[{result = variables["result"]},
    	result
    ]
    ,
    TestID -> "MonomialDependenceOperator-20200624-FKFG99_" <> label
]
