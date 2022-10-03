(* Wolfram Language Test file *)

Test[
	With[{expression = variables["expression"]},
		result = Distribute/@VariationalDOperator[variables][expression];
    	VarDOperator[variables][expression]
	]
    ,
    result
    ,
    TestID -> "VarDOperator-20200420-F6M7R8_" <> label
]
