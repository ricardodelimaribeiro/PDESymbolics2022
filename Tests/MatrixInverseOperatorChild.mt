(* Wolfram Language Test file *)

Test[
	With[{expression = template["expression"]},
    	MatrixInverseOperator[template["variables"]][expression]
	]
    ,
    With[{result = template["result"]},
    	result
    ]
    ,
    TestID -> "MatrixInverseOperator-20210131-8DB2MA_" <> label
]
